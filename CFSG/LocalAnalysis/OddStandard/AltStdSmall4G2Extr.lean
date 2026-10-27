module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Term
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup

theorem natCard_centralizer_conj' {G : Type} [Group G] (g u : G) :
    Nat.card (centralizer ({g⁻¹ * u * g} : Set G)) = Nat.card (centralizer ({u} : Set G)) := by
  refine Nat.card_congr ⟨fun y => ⟨g * y * g⁻¹, ?_⟩, fun y => ⟨g⁻¹ * y * g, ?_⟩, fun y => ?_,
    fun y => ?_⟩
  · have hy := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc g * ↑y * g⁻¹ * u = g * (↑y * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * u * g * ↑y) * g⁻¹ := by rw [hy]
      _ = u * (g * ↑y * g⁻¹) := by group
  · have hy := mem_centralizer_singleton_iff.1 y.2
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * ↑y * g * (g⁻¹ * u * g) = g⁻¹ * (↑y * u) * g := by group
      _ = g⁻¹ * (u * ↑y) * g := by rw [hy]
      _ = g⁻¹ * u * g * (g⁻¹ * ↑y * g) := by group
  · exact Subtype.ext (by group)
  · exact Subtype.ext (by group)

namespace TermData

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A D : Subgroup G}
  (c : Config G L Q n θ z) (h : TermData θ c.hn8 z m A D)
include c h

theorem exists_extremal (hsyl : ¬ 2 ∣ (Tm A z D).index) :
    ∃ x ∈ Mm A D, x ∉ A ∧ (∃ g : G, x = g⁻¹ * z * g) ∧
      Nat.card (Tm A z D ⊓ centralizer ({x} : Set G) : Subgroup G) = cardN L n z ∧
      (∀ h ∈ Tm A z D, h * x * h⁻¹ ∉ centralizer ({z} : Set G)) ∧
      ∀ y ∈ Tm A z D ⊓ centralizer ({x} : Set G), y ^ expo L n z = 1 := by
  have : IsSimpleGroup G := c.ot.std.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by rw [sq, z_mul_self c]
  obtain ⟨g, hgM, hext, -⟩ :=
    CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two
      c.ot.std.nonab (h.isPGroup_Tm c) hsyl Mm_le_Tm (h.index_Mm c) z_mem_Tm (h.z_not_mem_Mm c)
      hz2
  have hxL : g⁻¹ * z * g ∉ L := by
    have := N0.conj_z_not_mem_L c g⁻¹
    rwa [inv_inv] at this
  refine ⟨g⁻¹ * z * g, hgM, fun hxA => ?_, ⟨g, rfl⟩, ?_, fun k hk hkx => ?_, ?_⟩
  · have hx2 : (g⁻¹ * z * g) ^ 2 = 1 := by
      rw [sq, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, z_mul_self c]
      group
    exact hxL (ModIso.E_le_L c.hn8 ((h.datum.mem_E_iff_sq_eq_one hxA).2 hx2))
  · obtain ⟨hle, hp, hidx⟩ := hext
    set S := Tm A z D ⊓ centralizer ({g⁻¹ * z * g} : Set G) with hS
    set H := centralizer ({g⁻¹ * z * g} : Set G) with hH
    have hS' : IsPGroup 2 (S.subgroupOf H) := hp.of_equiv (subgroupOfEquivOfLe hle).symm
    have h1 : Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
      exact Sylow.card_eq_multiplicity (hS'.toSylow hidx)
    obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer ({z} : Set G))) := inferInstance
    have h2 := Sylow.card_eq_multiplicity P
    rw [h1, hH, natCard_centralizer_conj', ← h2, card_sylow_eq_cardN c P]
  · have hkM : k * (g⁻¹ * z * g) * k⁻¹ ∈ Mm A D :=
      (mem_normalizer_iff.1 (h.Tm_le_normalizer_Mm c hk) _).1 hgM
    apply N0.conj_z_not_mem_L c (k * g⁻¹)
    rw [show k * g⁻¹ * z * (k * g⁻¹)⁻¹ = k * (g⁻¹ * z * g) * k⁻¹ by group]
    exact h.Mm_inf_cent_le_L c ⟨hkM, hkx⟩
  · rintro y ⟨hyT, hyx⟩
    obtain ⟨j, hj⟩ := (h.isPGroup_Tm c) ⟨y, hyT⟩
    have hj' : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hgy : g * y * g⁻¹ ∈ centralizer ({z} : Set G) := by
      have hyx' := mem_centralizer_singleton_iff.1 hyx
      rw [mem_centralizer_singleton_iff]
      calc g * y * g⁻¹ * z = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g * y) * g⁻¹ := by rw [hyx']
        _ = z * (g * y * g⁻¹) := by group
    have h1 := pow_expo_eq_one c hgy (k := j) (by rw [conj_pow, hj']; group)
    rw [conj_pow] at h1
    calc y ^ expo L n z = g⁻¹ * (g * y ^ expo L n z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem expo_dvd_of_lt (hlt : expo L n z < 2 ^ m) : expo L n z ∣ 2 ^ (m - 1) := by
  rcases expo_eq_four_or_eight L n z with he | he <;> rw [he] at hlt ⊢
  · have hm : 3 ≤ m := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show m ≤ 2 by omega)
      norm_num at this
      omega
    exact (pow_dvd_pow 2 (show 2 ≤ m - 1 by omega) : 2 ^ 2 ∣ 2 ^ (m - 1))
  · have hm : 4 ≤ m := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show m ≤ 3 by omega)
      norm_num at this
      omega
    exact (pow_dvd_pow 2 (show 3 ≤ m - 1 by omega) : 2 ^ 3 ∣ 2 ^ (m - 1))

theorem false_of_lt (hsyl : ¬ 2 ∣ (Tm A z D).index) (hlt : expo L n z < 2 ^ m) : False := by
  obtain ⟨x, hxM, hxA, ⟨g, hxg⟩, -, -, hexp⟩ := h.exists_extremal c hsyl
  obtain ⟨a, ha, d, hd, rfl⟩ := (h.mem_Mm_iff c).1 hxM
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxA
    exact hxA ha
  obtain ⟨e, he, hde⟩ : ∃ e ∈ E θ c.hn8, d * e * d⁻¹ ≠ e := by
    by_contra hcon
    push Not at hcon
    exact hd1 (h.D_faith d hd hcon)
  obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ c.hn8 e).1 he
  obtain ⟨b, hb, hbv⟩ := h.datum.exists_pow_eq_eps v
  have hxN : a * d ∈ normalizer (A : Set G) := mul_mem (le_normalizer ha) (h.D_norm hd)
  have hx2 : a * d * (a * d) = 1 := by
    rw [hxg, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, z_mul_self c]
    group
  have hxi : (a * d)⁻¹ = a * d := inv_eq_of_mul_eq_one_right hx2
  have hb' : a * d * b * (a * d)⁻¹ ∈ A := (mem_normalizer_iff.1 hxN b).1 hb
  have hyA : b * (a * d * b * (a * d)⁻¹) ∈ A := mul_mem hb hb'
  have hyx : b * (a * d * b * (a * d)⁻¹) ∈ centralizer ({a * d} : Set G) := by
    have hc := h.datum.comm hb hb'
    have hconj : a * d * (b * (a * d * b * (a * d)⁻¹)) * (a * d)⁻¹ =
        b * (a * d * b * (a * d)⁻¹) := by
      calc a * d * (b * (a * d * b * (a * d)⁻¹)) * (a * d)⁻¹ =
          a * d * b * (a * d)⁻¹ * (a * d * (a * d) * b * (a * d * (a * d))⁻¹) := by group
        _ = a * d * b * (a * d)⁻¹ * b := by rw [hx2, one_mul, inv_one, mul_one]
        _ = b * (a * d * b * (a * d)⁻¹) := hc.symm
    rw [mem_centralizer_singleton_iff]
    calc b * (a * d * b * (a * d)⁻¹) * (a * d) =
        a * d * (b * (a * d * b * (a * d)⁻¹)) * (a * d)⁻¹ * (a * d) := by rw [hconj]
      _ = a * d * (b * (a * d * b * (a * d)⁻¹)) := by group
  have hy := hexp _ ⟨A_le_Tm hyA, hyx⟩
  have hdE : d * epsV θ c.hn8 v * d⁻¹ ∈ A :=
    (mem_normalizer_iff.1 (h.D_norm hd) _).1 (h.datum.E_le he)
  have hpow : (b * (a * d * b * (a * d)⁻¹)) ^ 2 ^ (m - 1) =
      epsV θ c.hn8 v * (d * epsV θ c.hn8 v * d⁻¹) := by
    have hcomm : Commute b (a * d * b * (a * d)⁻¹) := h.datum.comm hb hb'
    rw [hcomm.mul_pow, conj_pow, hbv,
      show a * d * epsV θ c.hn8 v * (a * d)⁻¹ = a * (d * epsV θ c.hn8 v * d⁻¹) * a⁻¹ by group,
      h.datum.comm ha hdE, mul_inv_cancel_right]
  have hne : (b * (a * d * b * (a * d)⁻¹)) ^ 2 ^ (m - 1) ≠ 1 := by
    rw [hpow]
    intro h1
    apply hde
    calc d * epsV θ c.hn8 v * d⁻¹ = (epsV θ c.hn8 v)⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = epsV θ c.hn8 v := epsV_inv θ c.hn8 v
  obtain ⟨q, hq⟩ := h.expo_dvd_of_lt c hlt
  exact hne (by rw [hq, pow_mul, hy, one_pow])

end TermData

end CFSG.OddStandard.AltStdSmall4.G2

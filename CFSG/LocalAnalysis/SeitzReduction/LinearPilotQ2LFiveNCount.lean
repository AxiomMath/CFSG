module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveDTransfer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

theorem card_comap_mk_eq_mul {H : Type*} [Group H] (J : Subgroup H) [J.Normal]
    (O : Subgroup (H ⧸ J)) :
    Nat.card (O.comap (QuotientGroup.mk' J)) = Nat.card J * Nat.card O := by
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hJF : J ≤ O.comap π := fun x hx => by
    have h1 : (x : H ⧸ J) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show (x : H ⧸ J) ∈ O
    rw [h1]
    exact one_mem _
  have h := card_ker_mul_card_range (π.comp (O.comap π).subtype)
  have hker : (π.comp (O.comap π).subtype).ker = J.subgroupOf (O.comap π) := by
    ext x
    simp [hπ, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hrange : (π.comp (O.comap π).subtype).range = O := by
    rw [MonoidHom.range_comp, range_subtype, map_comap_eq_self_of_surjective hπs]
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hJF).toEquiv] at h
  exact h.symm

variable {G : Type*} [Group G] [Finite G]

theorem false_of_conj_of_card_le {W P : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {t x g : G}
    (hxg : x = g⁻¹ * t * g) (hx : x * x = 1) (hP : IsPGroup 2 P)
    (hPW : ∀ y ∈ P, y * x * y⁻¹ * x⁻¹ ∈ W) {a : ℕ}
    (hcard : 2 ^ (a + 1) * Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ Nat.card P)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer ({t} : Set G) →
      Nat.card Q ≤ 2 ^ a) : False := by
  have h := card_le_card_inf_centralizer_mul_card_of_exponent_two hW2 hx hPW
  have hpos : 0 < Nat.card (W ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
  have h1 : 2 ^ (a + 1) ≤ Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    le_of_mul_le_mul_right (hcard.trans h) hpos
  set Q := (P ⊓ centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom with hQ
  have hQt : Q ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2
    rw [mem_centralizer_singleton_iff]
    change g * y * g⁻¹ * t = t * (g * y * g⁻¹)
    have ht : t = g * x * g⁻¹ := by rw [hxg]; group
    rw [ht]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  have hQp : IsPGroup 2 Q := (hP.to_le inf_le_left).map _
  have hQc : Nat.card Q = Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_map_of_injective (MulAut.conj g).injective
  have h2 := hmax Q hQp hQt
  rw [hQc] at h2
  have h3 : 2 ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem card_inf_centralizer_le_sq_of_exponent_two {W : Subgroup G}
    (hW2 : ∀ w ∈ W, w * w = 1) {t l : G} (ht : t * t = 1) (htW : t ∈ normalizer (W : Set G))
    (hlt : l * t = t * l) :
    Nat.card (W ⊓ centralizer ({l} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({l} : Set G) : Subgroup G) ^ 2 := by
  set V := W ⊓ centralizer ({t} : Set G) ⊓ centralizer ({l} : Set G) with hV
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hV2 : ∀ w ∈ V, w * w = 1 := fun w hw => hW2 w (mem_inf.1 (mem_inf.1 hw).1).1
  have hcomm : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v := fun v hv w hw => by
    have h1 := hW2 (v * w) (mul_mem hv hw)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hW2 v hv)
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW2 w hw)
    calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = w * v := by rw [mul_inv_rev, hvi, hwi]
  have htl : t ∈ centralizer ({l} : Set G) := mem_centralizer_singleton_iff.2 hlt.symm
  have hP : ∀ y ∈ W ⊓ centralizer ({l} : Set G), y * t * y⁻¹ * t⁻¹ ∈ V := by
    intro y hy
    obtain ⟨hyW, hyl⟩ := mem_inf.1 hy
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hW2 y hyW)
    have hy' : t * y * t⁻¹ ∈ W := (mem_normalizer_iff.1 htW y).1 hyW
    have hz : y * t * y⁻¹ * t⁻¹ = y * (t * y * t⁻¹) := by rw [hyi, hti]; group
    refine mem_inf.2 ⟨mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · rw [hz]
      exact mul_mem hyW hy'
    · rw [mem_centralizer_singleton_iff, hz]
      have hc := hcomm y hyW _ hy'
      have key : t * (y * (t * y * t⁻¹)) * t⁻¹ = y * (t * y * t⁻¹) := by
        calc t * (y * (t * y * t⁻¹)) * t⁻¹ = (t * y * t⁻¹) * ((t * t) * y * (t * t)⁻¹) := by
              group
          _ = (t * y * t⁻¹) * y := by rw [ht]; group
          _ = y * (t * y * t⁻¹) := hc.symm
      calc y * (t * y * t⁻¹) * t = t * (y * (t * y * t⁻¹)) * t⁻¹ * t := by rw [key]
        _ = t * (y * (t * y * t⁻¹)) := by group
    · rw [hz]
      exact mul_mem hyl (mul_mem (mul_mem htl hyl) (inv_mem htl))
  have h := card_le_card_inf_centralizer_mul_card_of_exponent_two hV2 ht hP
  have h1 : Nat.card (W ⊓ centralizer ({l} : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card V :=
    Subgroup.card_le_of_le fun z hz => by
      obtain ⟨⟨hzW, hzl⟩, hzt⟩ := mem_inf.1 hz |>.imp_left mem_inf.1
      exact mem_inf.2 ⟨mem_inf.2 ⟨hzW, hzt⟩, hzl⟩
  have h2 : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) ≤ Nat.card V :=
    Subgroup.card_le_of_le inf_le_left
  calc Nat.card (W ⊓ centralizer ({l} : Set G) : Subgroup G) ≤ Nat.card V * Nat.card V :=
        h.trans (Nat.mul_le_mul h1 h2)
    _ = Nat.card V ^ 2 := (sq _).symm

theorem card_le_of_le_of_ne_of_card_eq_two_pow {V H : Subgroup G} (hHV : H ≤ V) (hne : H ≠ V)
    {m : ℕ} (hV : Nat.card V = 2 ^ (m + 1)) : Nat.card H ≤ 2 ^ m := by
  have hdvd : Nat.card H ∣ 2 ^ (m + 1) := hV ▸ Subgroup.card_dvd_of_le hHV
  obtain ⟨k, hk, hHk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hHk]
  rcases Nat.lt_or_ge k (m + 1) with h | h
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    apply hne
    refine eq_of_le_of_card_ge hHV ?_
    rw [hV, hHk, show k = m + 1 by omega]

end CFSG.SeitzReduction.LinearPilot

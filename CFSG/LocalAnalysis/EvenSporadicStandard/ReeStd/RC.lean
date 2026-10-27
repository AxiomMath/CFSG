module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.CosetPow
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Step

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

theorem conj_coset_fixed_pow {R Y : Subgroup G} (hidx : Y.relIndex R ≤ 6) {σ : G} {a : ℕ}
    (hσ7 : σ ^ 7 ^ a = 1) (hσR : σ ∈ normalizer (R : Set G)) (hσY : σ ∈ normalizer (Y : Set G))
    {r : G} (hr : r ∈ R) : σ * r * σ⁻¹ * r⁻¹ ∈ Y := by
  have hσ'7 : R.normalizerMonoidHom ⟨σ, hσR⟩ ^ 7 ^ a = 1 := by
    ext b
    have := J1Std.normalizerMonoidHom_pow_apply hσR (7 ^ a) b
    rw [hσ7] at this
    simpa using this
  have hS' : (Y.subgroupOf R).map (R.normalizerMonoidHom ⟨σ, hσR⟩).toMonoidHom =
      Y.subgroupOf R := by
    refine Subgroup.ext fun x => ?_
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      exact (mem_normalizer_iff.1 hσY (y : G)).1 hy
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hσR' : σ⁻¹ ∈ normalizer (R : Set G) := inv_mem hσR
      have hσY' : σ⁻¹ ∈ normalizer (Y : Set G) := inv_mem hσY
      have hmemR : σ⁻¹ * x * σ ∈ R := by
        have := (mem_normalizer_iff.1 hσR' (x : G)).1 x.2
        simpa using this
      refine ⟨⟨σ⁻¹ * x * σ, hmemR⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have := (mem_normalizer_iff.1 hσY' (x : G)).1 hx
        simpa using this
      · apply Subtype.ext
        show σ * (σ⁻¹ * x * σ) * σ⁻¹ = x
        group
  exact coset_fixed_of_small_index_pow (S := Y.subgroupOf R) hidx
    (R.normalizerMonoidHom ⟨σ, hσR⟩) hσ'7 hS' ⟨r, hr⟩

namespace Stage

variable {H : LocalSetting G} {S Λ : Subgroup G} (h : Stage H S Λ)

include h in
theorem N_conj_E {n e : G} (hn : n ∈ normalizer (S : Set G)) (he : e ∈ H.E) :
    n * e * n⁻¹ ∈ H.E := by
  refine h.mem_E_of_sq (h.N_normalizes_Λ hn (h.E_le he)) ?_
  calc n * e * n⁻¹ * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
    _ = 1 := by rw [H.sq_E e he]; group

include h in
theorem N_conj_RC {n r : G} (hn : n ∈ normalizer (S : Set G)) (hr : r ∈ H.RC S) :
    n * r * n⁻¹ ∈ H.RC S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun e he => ?_, ?_⟩
  · have h1 : n⁻¹ * e * n ∈ H.E := by
      have := h.N_conj_E (inv_mem hn) he
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).1 _ h1
    calc e * (n * r * n⁻¹) = n * ((n⁻¹ * e * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * e * n)) * n⁻¹ := by rw [h2]
      _ = n * r * n⁻¹ * e := by group
  · exact mul_mem (mul_mem hn (Subgroup.mem_inf.1 hr).2) (inv_mem hn)

include h in
theorem N_le_normalizer_RC :
    normalizer (S : Set G) ≤ normalizer ((H.RC S : Subgroup G) : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun r => ⟨fun hr => h.N_conj_RC hn hr, fun hr => ?_⟩
  have := h.N_conj_RC (inv_mem hn) hr
  simpa [mul_assoc] using this

include h in
theorem CZ_le_normalizer_DC : H.CZ S ≤ normalizer ((H.DC S : Subgroup G) : Set G) := by
  have key : ∀ c ∈ H.CZ S, ∀ d ∈ H.DC S, c * d * c⁻¹ ∈ H.DC S := by
    intro c hc d hd
    have hcB : c ∈ H.B := h.CZ_le_B hc
    have hcV := mem_normalizer_iff.1 (H.mem_B_def.1 hcB).1
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_,
      mul_mem (mul_mem hc.2 hd.2) (inv_mem hc.2)⟩
    have h1 : c⁻¹ * v * c ∈ H.V := by
      have := (hcV (c⁻¹ * v * c)).2 (by simpa [mul_assoc] using hv)
      simpa [mul_assoc] using this
    have h2 := Subgroup.mem_centralizer_iff.1 hd.1 _ h1
    calc v * (c * d * c⁻¹) = c * ((c⁻¹ * v * c) * d) * c⁻¹ := by group
      _ = c * (d * (c⁻¹ * v * c)) * c⁻¹ := by rw [h2]
      _ = c * d * c⁻¹ * v := by group
  intro c hc
  exact mem_normalizer_iff.2 fun d => ⟨fun hd => key c hc d hd, fun hd => by
    have := key c⁻¹ (inv_mem hc) _ hd
    simpa [mul_assoc] using this⟩

include h in
theorem DC_conj_eq {d s : G} (hd : d ∈ H.DC S) (hs : s ∈ S) :
    ∃ v ∈ H.V, d * s * d⁻¹ = v * s * v⁻¹ := by
  obtain ⟨j, ⟨k, hk⟩, o, ho, hdo⟩ := exists_two_part d
  have hdj : d ^ j ∈ H.DC S := pow_mem hd j
  have hd' : d * (d ^ j)⁻¹ ∈ H.DC S := mul_mem hd (inv_mem hdj)
  have hV : d ^ j ∈ H.V :=
    H.le_V_of_isPGroup_of_le_centralizer_V (isPGroup_zpowers hk)
      ((Subgroup.zpowers_le.2 hdj).trans inf_le_left) (mem_zpowers _)
  have hVS : d ^ j ∈ S := h.V_le hV
  have hE : ∀ e ∈ H.E, (d * (d ^ j)⁻¹) * e * (d * (d ^ j)⁻¹)⁻¹ = e := fun e he => by
    have := Subgroup.mem_centralizer_iff.1 hd'.1 e (H.E_le_V he)
    rw [← this]
    group
  have hz : (d * (d ^ j)⁻¹) * H.z = H.z * (d * (d ^ j)⁻¹) :=
    (Subgroup.mem_centralizer_iff.1 hd'.1 H.z H.z_mem_V).symm
  have hc := h.centralizes_S_of_odd_pow hd'.2 ho hdo hE hz
  have h1 := hc (d ^ j * s * (d ^ j)⁻¹) (mul_mem (mul_mem hVS hs) (inv_mem hVS))
  have key : ∀ x : G, d * s * d⁻¹ = (d * x⁻¹) * (x * s * x⁻¹) * (d * x⁻¹)⁻¹ := fun x => by group
  exact ⟨d ^ j, hV, (key (d ^ j)).trans h1⟩

include h in
theorem mem_SD_of_sigma_coset {σ r : G} (hσ : H.IsSigma σ) (hσN : σ ∈ normalizer (S : Set G))
    (hr : r ∈ H.RC S) (hcoset : σ * r * σ⁻¹ * r⁻¹ ∈ H.DC S ⊔ S) : r ∈ H.DC S ⊔ S := by
  have hrN : r ∈ normalizer (S : Set G) := (Subgroup.mem_inf.1 hr).2
  obtain ⟨φ, hφ7, hφfree, hφpow⟩ := h.exists_sigma_aut hσ hσN
  have hσz : σ * H.z = H.z * σ := hσ.comm_z
  have hσz' : σ * H.z * σ⁻¹ = H.z := by rw [hσz]; group
  have hσz'' : σ⁻¹ * H.z * σ = H.z := by
    calc σ⁻¹ * H.z * σ = σ⁻¹ * (H.z * σ) := by group
      _ = σ⁻¹ * (σ * H.z) := by rw [hσz]
      _ = H.z := by group
  obtain ⟨hxS, hxΛ⟩ := h.N_conj_z_mem hrN
  have hlΛ : H.z * (r * H.z * r⁻¹) ∈ Λ := h.z_mul_mem_Λ hxS hxΛ
  obtain ⟨l, hl⟩ : ∃ l : G, l = H.z * (r * H.z * r⁻¹) := ⟨_, rfl⟩
  have hxl : r * H.z * r⁻¹ = H.z * l := by
    rw [hl, ← mul_assoc, H.z_mul_self, one_mul]
  rw [← hl] at hlΛ
  obtain ⟨d, hd, s₁, hs₁, hds⟩ : ∃ d ∈ H.DC S, ∃ s ∈ S, d * s = σ * r * σ⁻¹ * r⁻¹ := by
    have hmem : σ * r * σ⁻¹ * r⁻¹ ∈ ((H.DC S ⊔ S : Subgroup G) : Set G) := hcoset
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (H.DC S) S inf_le_right] at hmem
    obtain ⟨d, hd, s, hs, e⟩ := hmem
    exact ⟨d, hd, s, hs, e⟩
  have hy : s₁ * (H.z * l) * s₁⁻¹ ∈ S := by
    rw [← hxl]
    exact mul_mem (mul_mem hs₁ hxS) (inv_mem hs₁)
  obtain ⟨v, hv, hdv⟩ := h.DC_conj_eq hd hy
  have hs₂ : v * s₁ ∈ S := mul_mem (h.V_le hv) hs₁
  have h1 : σ * (H.z * l) * σ⁻¹ = (v * s₁) * (H.z * l) * (v * s₁)⁻¹ := by
    calc σ * (H.z * l) * σ⁻¹ = σ * (r * H.z * r⁻¹) * σ⁻¹ := by rw [hxl]
      _ = (σ * r * σ⁻¹ * r⁻¹) * (r * H.z * r⁻¹) * (σ * r * σ⁻¹ * r⁻¹)⁻¹ := by
          calc σ * (r * H.z * r⁻¹) * σ⁻¹ = σ * r * (σ⁻¹ * H.z * σ) * r⁻¹ * σ⁻¹ := by
                rw [hσz'']; group
            _ = _ := by group
      _ = (d * s₁) * (r * H.z * r⁻¹) * (d * s₁)⁻¹ := by rw [hds]
      _ = (d * s₁) * (H.z * l) * (d * s₁)⁻¹ := by rw [hxl]
      _ = d * (s₁ * (H.z * l) * s₁⁻¹) * d⁻¹ := by group
      _ = v * (s₁ * (H.z * l) * s₁⁻¹) * v⁻¹ := hdv
      _ = (v * s₁) * (H.z * l) * (v * s₁)⁻¹ := by group
  obtain ⟨m, hmΛ, hm⟩ := h.conj_zl hs₂ hlΛ
  have h2 : σ * (H.z * l) * σ⁻¹ = H.z * (σ * l * σ⁻¹) := by
    calc σ * (H.z * l) * σ⁻¹ = (σ * H.z * σ⁻¹) * (σ * l * σ⁻¹) := by group
      _ = H.z * (σ * l * σ⁻¹) := by rw [hσz']
  have h3 : σ * l * σ⁻¹ = l * (m * m) :=
    mul_left_cancel (a := H.z) ((h2.symm.trans (h1.trans hm)).trans (mul_assoc _ _ _))
  have hφ1 : ∀ a : Λ, (φ a : G) = σ * a * σ⁻¹ := fun a => by simpa using hφpow 1 a
  have hsq : ∃ b : Λ, φ ⟨l, hlΛ⟩ * ⟨l, hlΛ⟩⁻¹ = b * b := by
    refine ⟨⟨m, hmΛ⟩, Subtype.ext ?_⟩
    show (φ ⟨l, hlΛ⟩ : G) * l⁻¹ = m * m
    rw [hφ1]
    show σ * l * σ⁻¹ * l⁻¹ = m * m
    rw [h3]
    calc l * (m * m) * l⁻¹ = (m * m) * l * l⁻¹ := by rw [h.comm hlΛ (mul_mem hmΛ hmΛ)]
      _ = m * m := by group
  obtain ⟨c, hc⟩ := J1Std.mem_sq_of_sigma_fixed (fun a b => Subtype.ext (h.comm a.2 b.2)) φ hφ7
    hφfree hsq
  have hlc : l = c.1 * c.1 := congrArg Subtype.val hc
  obtain ⟨s, hs, hseq⟩ := h.sq_conj_zl (one_mem Λ) c.2
  have hxs : r * H.z * r⁻¹ = s * H.z * s⁻¹ := by
    rw [hxl, hlc]
    simpa using hseq.symm
  have hu : s⁻¹ * r ∈ centralizer ({H.z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc s⁻¹ * r * H.z = s⁻¹ * (r * H.z * r⁻¹) * r := by group
      _ = s⁻¹ * (s * H.z * s⁻¹) * r := by rw [hxs]
      _ = H.z * (s⁻¹ * r) := by group
  have huN : s⁻¹ * r ∈ normalizer (S : Set G) := mul_mem (inv_mem (le_normalizer hs)) hrN
  have huR : s⁻¹ * r ∈ H.RC S := mul_mem (inv_mem (h.S_le_RC hs)) hr
  have huD : s⁻¹ * r ∈ H.DC S := LocalSetting.mem_DC_of_mem_CZ_of_mem_RC ⟨hu, huN⟩ huR
  have hsY : s ∈ H.DC S ⊔ S := Subgroup.mem_sup_right hs
  have huY : s⁻¹ * r ∈ H.DC S ⊔ S := Subgroup.mem_sup_left huD
  have := mul_mem hsY huY
  simpa using this

end Stage

end CFSG.EvenSporadicStandard.ReeStd

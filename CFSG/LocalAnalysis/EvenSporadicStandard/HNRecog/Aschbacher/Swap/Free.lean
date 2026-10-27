module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.FreePreserve

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {c : ℕ} {Fp Fm : Submodule (ZMod 2) V}

theorem finrank_range_add_one_le_two (h8 : finrank (ZMod 2) V = 8) (hc : IsCompl Fp Fm)
    (h4 : finrank (ZMod 2) Fp = 4) (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1)
    (hFm : ∀ v ∈ Fm, b v ∈ Fm) (hid : ∀ v ∈ Fp, b v = v) :
    finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)) ≤ 2 := by
  let bL : V →ₗ[ZMod 2] V := (b : V →ₗ[ZMod 2] V)
  let D : V →ₗ[ZMod 2] V := bL + 1
  change finrank (ZMod 2) (LinearMap.range D) ≤ 2
  have htwo : ∀ v : V, v + v = 0 := by
    intro v
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) v, h2, zero_smul]
  have hbL_apply : ∀ v : V, bL (bL v) = v := by
    intro v
    change (b : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) v) = v
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) hb
    simpa using h
  have hD2 : D * D = 0 := by
    ext v
    change ((bL + 1) * (bL + 1)) v = 0
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, map_add]
    rw [hbL_apply v, add_comm (bL v) v]
    exact htwo (v + bL v)
  have hker : LinearMap.range D ≤ LinearMap.ker D :=
    LinearMap.range_le_ker_iff.mpr hD2
  have hFp_ker : Fp ≤ LinearMap.ker D := by
    intro v hv
    rw [LinearMap.mem_ker]
    change bL v + v = 0
    rw [show bL v = v from hid v hv]
    exact htwo v
  have hrange_le_Fm : LinearMap.range D ≤ Fm := by
    rintro w ⟨v, rfl⟩
    have hv : v ∈ Fp ⊔ Fm := by rw [hc.codisjoint.eq_top]; trivial
    obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hv
    have hDp : D p = 0 := LinearMap.mem_ker.mp (hFp_ker hp)
    have hDv : D v = D m := by rw [← hpm, map_add, hDp, zero_add]
    rw [hDv]
    change bL m + m ∈ Fm
    exact Fm.add_mem (hFm m hm) hm
  have hdisj : Disjoint (LinearMap.range D) Fp := by
    rw [disjoint_iff_inf_le]
    intro v hv
    rw [Submodule.mem_bot]
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvr, hvp⟩ := hv
    have hvFm : v ∈ Fm := hrange_le_Fm hvr
    have : v ∈ Fp ⊓ Fm := Submodule.mem_inf.mpr ⟨hvp, hvFm⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    exact this
  have hsup_finrank :
      finrank (ZMod 2) ↥(LinearMap.range D ⊔ Fp) =
        finrank (ZMod 2) (LinearMap.range D) + finrank (ZMod 2) Fp := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range D) Fp
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h
  have hsup_le_ker : LinearMap.range D ⊔ Fp ≤ LinearMap.ker D := sup_le hker hFp_ker
  have hstep : finrank (ZMod 2) ↥(LinearMap.range D ⊔ Fp) =
      finrank (ZMod 2) (LinearMap.range D) + 4 := by
    rw [hsup_finrank, h4]
  have hrank : finrank (ZMod 2) (LinearMap.range D) + 4 ≤
      finrank (ZMod 2) (LinearMap.ker D) := by
    rw [← hstep]
    exact Submodule.finrank_mono hsup_le_ker
  have hrk : finrank (ZMod 2) (LinearMap.range D) +
      finrank (ZMod 2) (LinearMap.ker D) = 8 := by
    rw [LinearMap.finrank_range_add_finrank_ker, h8]
  omega

theorem EigenData.mul_mod_five_of_free (hS : StdHyp σ) (hE : EigenData σ c Fp Fm)
    (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1) {k k' : ℕ} (hkk' : (k * k') % 5 = 1)
    (hα : b * σ (a₀, 1) * b⁻¹ = σ (1, a₀ ^ k))
    (hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1))) :
    (k * c) % 5 = 2 ∨ (k * c) % 5 = 3 := by
  have hk5 : ¬ 5 ∣ k := by
    intro h
    have hmod : (k * k') % 5 = 0 := by
      rw [Nat.mul_mod, Nat.mod_eq_zero_of_dvd h, Nat.zero_mul, Nat.zero_mod]
    omega
  have hc5 : ¬ 5 ∣ c := by
    intro h
    have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt h (Nat.lt_succ_of_le hE.le_four)
    have hone : 1 ≤ c := hE.one_le
    omega
  have hkc5 : ¬ 5 ∣ k * c := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with hk | hc
    · exact hk5 hk
    · exact hc5 hc
  have hrne : (k * c) % 5 ≠ 0 := fun h => hkc5 (Nat.dvd_of_mod_eq_zero h)
  have hrlt : (k * c) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : (k * c) % 5 = 1
  · have hmem := EigenData.map_mem_of_mul_mod hS hE b hb hkk' hα (Or.inl h1)
    have hid := EigenData.eq_of_mul_mod_one hS hE b hb hkk' hα h1
    have hle :=
      finrank_range_add_one_le_two hS.finrank_eq hE.isCompl hE.finrank_plus b hb hmem.2 hid
    omega
  · by_cases h4 : (k * c) % 5 = 4
    · have hmem := EigenData.map_mem_of_mul_mod hS hE b hb hkk' hα (Or.inr h4)
      have hid := EigenData.eq_of_mul_mod_four hS hE b hb hkk' hα h4
      have hle :=
        finrank_range_add_one_le_two hS.finrank_eq hE.isCompl.symm hE.finrank_minus b hb hmem.1 hid
      omega
    · omega

end CFSG.EvenSporadicStandard.HNRecog.Swap

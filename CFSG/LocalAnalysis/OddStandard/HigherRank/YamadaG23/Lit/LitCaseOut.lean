module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitFixPt
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitPerfAct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitSolvP
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitCore
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three

variable {X G : Type} [Group X] [Finite X] [Group G] [Finite G] {π : X →* G} {Z : Subgroup X}
  [Z.Normal] {τ : X ≃* X} {σ : G ≃* G}

theorem lit_sigma_nontriv (d : LitTData π Z τ σ) {H : Subgroup X} (hH : ⁅H, H⁆ = H)
    (hτH : ∀ x ∈ H, τ x ∈ H) (hcent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x) {z : X}
    (hzH : z ∈ H) (hz : τ z ≠ z) : ∃ x, σ x ≠ x := by
  by_contra h
  push Not at h
  have hmem : ∀ x ∈ H, τ x * x⁻¹ ∈ H := fun x hx => H.mul_mem (hτH x hx) (H.inv_mem hx)
  have hcent' : ∀ x ∈ H, ∀ y ∈ H, (τ x * x⁻¹) * y = y * (τ x * x⁻¹) := by
    intro x hx y hy
    have hker : τ x * x⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : π (τ x) = π x := by rw [← d.comm x, h (π x)]
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (hcent y hy (τ x * x⁻¹) hker).symm
  exact hz (lit_perfect_central_action τ hH hmem hcent' z hzH)

theorem lit_caseM22 (hM : GomiOuterM22) (d : LitTData π Z τ σ) {M : Subgroup G} [M.Normal]
    (hM22 : CFSG.Blueprint.NativeSporadic.IsSporadic ↥M .M22)
    (hC : centralizer (M : Set G) = ⊥) (h72 : 72 ∣ Nat.card ↥((litTSub τ Z).map π))
    (hσ : ∃ x, σ x ≠ x) : False := by
  have hle : (litTSub τ Z).map π ≤ litFixSub σ := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact d.fix_of_mem_tsub hx
  have h9 : 9 ∣ Nat.card ↥(litFixSub σ) :=
    dvd_trans (dvd_trans (by norm_num : 9 ∣ 72) h72) (Subgroup.card_dvd_of_le hle)
  exact (hM G M σ inferInstance hM22 hC d.invol_G hσ) h9

theorem lit_solv_centPre (d : LitTData π Z τ σ) (hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z)
    (hTs : Group.IsSolvable ↥(litTSub τ Z)) {H : Subgroup X} (hτH : ∀ x, x ∈ H ↔ τ x ∈ H)
    (hcen : ∀ x ∈ center ↥H, (x : X) ∈ π.ker) :
    Group.IsSolvable ↥(litTSub (litRestrict τ H hτH) (center ↥H)) := by
  haveI hPnorm : (litP Z).Normal := by rw [← d.ker]; infer_instance
  have hsup : Group.IsSolvable ↥(litTSub τ Z ⊔ litP Z) :=
    lit_solvable_sup hTs (lit_solvable_litP hZc)
  let S : Subgroup ↥H := litTSub (litRestrict τ H hτH) (center ↥H)
  have hmem : ∀ x : ↥S, (((x : ↥H) : X)) ∈ litTSub τ Z ⊔ litP Z := by
    intro x
    have hcenter : (litRestrict τ H hτH (x : ↥H) * (x : ↥H)⁻¹) ∈ center ↥H := x.2
    have hker : (((litRestrict τ H hτH (x : ↥H) * (x : ↥H)⁻¹ : ↥H)) : X) ∈ π.ker :=
      hcen _ hcenter
    rw [Subgroup.coe_mul, Subgroup.coe_inv, litRestrict_coe] at hker
    have hπ1 : π (τ ((x : ↥H) : X) * ((x : ↥H) : X)⁻¹) = 1 := MonoidHom.mem_ker.mp hker
    have hπτ : π (τ ((x : ↥H) : X)) = π ((x : ↥H) : X) := by
      rw [map_mul, map_inv, mul_inv_eq_one] at hπ1
      exact hπ1
    have hfix : π ((x : ↥H) : X) ∈ litFixSub σ := by
      show σ (π ((x : ↥H) : X)) = π ((x : ↥H) : X)
      rw [d.comm, hπτ]
    obtain ⟨w, hw, hwπ⟩ := Subgroup.mem_map.mp (lit_fix_le d hfix)
    have hk : w⁻¹ * ((x : ↥H) : X) ∈ litP Z := by
      rw [← d.ker, MonoidHom.mem_ker, map_mul, map_inv, hwπ, inv_mul_cancel]
    have hsupmem := Subgroup.mul_mem_sup hw hk
    simpa [mul_inv_cancel_left] using hsupmem
  let f : ↥S →* X := H.subtype.comp S.subtype
  let g : ↥S →* ↥(litTSub τ Z ⊔ litP Z) := f.codRestrict _ hmem
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : f a = f b :=
      congrArg (fun w : ↥(litTSub τ Z ⊔ litP Z) => (w : X)) hab
    exact (H.subtype_injective.comp S.subtype_injective) h1
  haveI : Group.IsSolvable ↥(litTSub τ Z ⊔ litP Z) := hsup
  change Group.IsSolvable ↥S
  exact Group.isSolvable_of_isSolvable_injective (f := g) hginj

theorem lit_casePSLU (hI : GomiOuterPSLU4) (d : LitTData π Z τ σ)
    (hZc : ∀ z ∈ Z, ∀ x : X, z * x = x * z) (hTs : Group.IsSolvable ↥(litTSub τ Z))
    {M : Subgroup G} (hMs : IsSimpleGroup ↥M) (hMn : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hMt : LitPSLU4All ↥M) {H : Subgroup X} (hq : CFSG.IsQuasisimple ↥H) (hHM : H.map π = M)
    (hcent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x) (hτH : ∀ x, x ∈ H ↔ τ x ∈ H) {z : X}
    (hzZ : z ∈ Z) (hzH : z ∈ H) (hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1) (hz : τ z ≠ z) :
    IsSU43 (↥H ⧸ CFSG.oddCore ↥H) := by
  obtain ⟨ρ, hρsurj, hρcoe, hρker⟩ := lit_H_hom hMs hMn hHM hcent
  let e₁ : ↥H ⧸ ρ.ker ≃* ↥M := QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj
  let e : ↥H ⧸ center ↥H ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hρker.symm).trans e₁
  have hpslu : LitPSLU4All (↥H ⧸ center ↥H) := lit_psl4_of_mulEquiv e.symm hMt
  have h_invol : ∀ x : ↥H, litRestrict τ H hτH (litRestrict τ H hτH x) = x := by
    intro x
    apply Subtype.ext
    rw [litRestrict_coe, litRestrict_coe]
    exact d.invol (x : X)
  have hmoved : ∃ z ∈ center ↥H, (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
      litRestrict τ H hτH z ≠ z := by
    refine ⟨⟨z, hzH⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hZc z hzZ (y : X)).symm
    · obtain ⟨k, hk⟩ := hz2
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])⟩
    · intro h
      exact hz (by
        have := congrArg (fun w : ↥H => (w : X)) h
        simpa [litRestrict_coe] using this)
  have hcen' : ∀ x ∈ center ↥H, (x : X) ∈ π.ker := by
    intro x hx
    have hxker : x ∈ ρ.ker := by rw [hρker]; exact hx
    have hρx : ρ x = 1 := MonoidHom.mem_ker.mp hxker
    rw [MonoidHom.mem_ker, ← hρcoe x, hρx]
    simp
  exact hI ↥H (litRestrict τ H hτH) hq hpslu h_invol hmoved
    (lit_solv_centPre d hZc hTs hτH hcen')

end CFSG.OddStandard.HigherRank.YamadaG23

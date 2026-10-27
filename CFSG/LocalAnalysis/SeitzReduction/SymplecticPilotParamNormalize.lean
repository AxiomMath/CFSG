module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective spProjEquiv)

section Entrywise

variable {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}

theorem spFieldMap_eq_statedSpMap (ι : K →+* F) : spFieldMap n ι = statedSpMap ι n :=
  MonoidHom.ext fun _ => rfl

theorem fieldSp_statedSpMap_of_fix {k : Type} [Field k] (ι : k →+* K) {σ : K ≃+* K}
    (hσι : ∀ c, σ (ι c) = ι c) (g : StatedSp n k) :
    fieldSp n K σ (statedSpMap ι n g) = statedSpMap ι n g := by
  rw [F4Pilot.fieldSp_eq_statedSpMap, F4Pilot.statedSpMap_comp,
    show (σ : K →+* K).comp ι = ι from RingHom.ext hσι]

theorem coe_fieldBlockSp_eq_fieldSp (σ : F ≃+* F) (N : Finset (Fin n)) (x : spBlock F N) :
    ((fieldBlockSp σ N x : spBlock F N) : StatedSp n F) = fieldSp n F σ x := by
  rw [coe_fieldBlockSp_apply, F4Pilot.fieldSp_eq_statedSpMap, spFieldMap_eq_statedSpMap]
  rfl

end Entrywise

section Extension

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulAut_statedSpMap_comm_fieldSp {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (hr : 3 ≤ r) {σ : K ≃+* K} (hσι : ∀ c, σ (ι c) = ι c)
    (δ : MulAut (StatedSp r k)) :
    ∃ δ' : MulAut (StatedSp r K), (∀ g, δ' (statedSpMap ι r g) = statedSpMap ι r (δ g)) ∧
      ∀ x, δ' (fieldSp r K σ x) = fieldSp r K σ (δ' x) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨A, ρ, hA⟩ := (automorphism_generation (K := k) hr).2 (MulAut.congr (spProjEquiv r k) δ)
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  have hδ : δ = MulAut.conj s * fieldSp r k ρ := by
    apply (MulAut.congr (spProjEquiv r k)).injective
    rw [hA, hs, map_mul, F4Pilot.mulAutCongr_spProjEquiv_conj,
      F4Pilot.mulAutCongr_spProjEquiv_fieldSp]
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq ι ρ
  refine ⟨MulAut.conj (statedSpMap ι r s) * fieldSp r K ρ', fun g => ?_, fun x => ?_⟩
  · rw [hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      F4Pilot.fieldSp_statedSpMap ι hρ', map_mul, map_mul, map_inv]
  · have hσρ : fieldSp r K σ (fieldSp r K ρ' x) = fieldSp r K ρ' (fieldSp r K σ x) := by
      rw [← MulAut.mul_apply, ← map_mul, ringAut_mul_comm K σ ρ', map_mul, MulAut.mul_apply]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
      map_inv, fieldSp_statedSpMap_of_fix ι hσι, hσρ]

end Extension

section Normalize

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_mulEquiv_statedSpMap_eq_comm_of_descent {k : Type} [Field k] [Finite k]
    (hk : 4 ≤ Nat.card k) (ι : k →+* K) {σ : K ≃+* K}
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι)
    (hdesc : ∀ β : MulAut (StatedSp r K), β * β = 1 →
      β ∉ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range →
        ∃ h : StatedSp r K, β = MulAut.conj h * fieldSp r K σ * (MulAut.conj h)⁻¹)
    (hext : ∀ δ : MulAut (StatedSp r k), ∃ δ' : MulAut (StatedSp r K),
      (∀ g, δ' (statedSpMap ι r g) = statedSpMap ι r (δ g)) ∧
        ∀ x, δ' (fieldSp r K σ x) = fieldSp r K σ (δ' x))
    {M : Type*} [Group M] (ψ : StatedSp r K ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (hθi : θ ∉ (MulAut.conj : M →* MulAut M).range) (ε : StatedSp r k →* M)
    (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp r K ≃* M, (∀ g, ψ' (statedSpMap ι r g) = ε g) ∧
      ∀ x, θ (ψ' x) = ψ' (fieldSp r K σ x) := by
  set β := MulAut.congr ψ.symm θ with hβdef
  have hβapp : ∀ y, β y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  have hβi : β ∉ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range := by
    rintro ⟨s, hs⟩
    apply hθi
    refine ⟨ψ s, MulEquiv.ext fun x => ?_⟩
    have h1 := hβapp (ψ.symm x)
    rw [← hs, MulAut.conj_apply, ψ.apply_symm_apply] at h1
    rw [MulAut.conj_apply, ← ψ.apply_symm_apply (θ x), ← h1, map_mul, map_mul, map_inv,
      ψ.apply_symm_apply]
  obtain ⟨h, hh⟩ := hdesc β hβ hβi
  set ψ₁ : StatedSp r K ≃* M := (MulAut.conj h).trans ψ with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (h * x * h⁻¹) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (fieldSp r K σ x) := by
    intro x
    have h1 := hβapp (h * x * h⁻¹)
    rw [hh, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
      show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h1
    rw [hψ₁app, hψ₁app, ← ψ.apply_symm_apply (θ (ψ (h * x * h⁻¹))), ← h1]
  have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M) =
      (statedSpMap ι r).range.map ψ₁.toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply, ← F4Pilot.eqLocus_fieldSp_eq_range ι hfix]
    change θ (ψ₁ x) = ψ₁ x ↔ fieldSp r K σ x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have htop : ⁅(⊤ : Subgroup (StatedSp r k)), (⊤ : Subgroup (StatedSp r k))⁆ = ⊤ := by
    have := isPerfect_statedSp_of_four_le hk r
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hperf : ⁅(statedSpMap ι r).range.map ψ₁.toMonoidHom,
      (statedSpMap ι r).range.map ψ₁.toMonoidHom⁆ =
        (statedSpMap ι r).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp (statedSpMap ι r)).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp (statedSpMap ι r)) :=
    ψ₁.injective.comp (statedSpMap_injective ι r)
  set δ : MulAut (StatedSp r k) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδdef
  have hδ : ∀ g, ψ₁ (statedSpMap ι r (δ g)) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ', hδσ⟩ := hext δ
  refine ⟨δ'.trans ψ₁, fun g => ?_, fun x => ?_⟩
  · change ψ₁ (δ' (statedSpMap ι r g)) = ε g
    rw [hδ', hδ]
  · change θ (ψ₁ (δ' x)) = ψ₁ (δ' (fieldSp r K σ x))
    rw [hθψ₁, hδσ]

theorem exists_mulEquiv_statedSpMap_eq_comm (hr : 3 ≤ r) {k : Type} [Field k] [Finite k]
    [CharP k 2] (hk : 4 ≤ Nat.card k) (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M] (ψ : StatedSp r K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (hθi : θ ∉ (MulAut.conj : M →* MulAut M).range)
    (ε : StatedSp r k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp r K ≃* M, (∀ g, ψ' (statedSpMap ι r g) = ε g) ∧
      ∀ x, θ (ψ' x) = ψ' (fieldSp r K σ x) :=
  exists_mulEquiv_statedSpMap_eq_comm_of_descent hk ι hfix
    (fun _ hβ hβi => F4Pilot.exists_eq_conj_mul_fieldSp_mul_conj_inv hr hσ hβ hβi)
    (exists_mulAut_statedSpMap_comm_fieldSp ι hr fun c => (hfix (ι c)).2 ⟨c, rfl⟩)
    ψ hθ hθi ε hε hεr

end Normalize

end CFSG.SeitzReduction.SymplecticPilot

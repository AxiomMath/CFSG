module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamNormalize
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective spProjEquiv)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauMat_apply tauEquiv tauAut tauAut_proj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Tau

variable {K F : Type} [Field K] [CharP K 2] [Field F] [CharP F 2]

theorem tauSp_statedSpMap (ι : K →+* F) (g : StatedSp 2 K) :
    tauSp (statedSpMap ι 2 g) = statedSpMap ι 2 (tauSp g) := by
  apply SymplecticTorusWeyl.statedSp_ext
  simp only [coe_tauSp, F4Pilot.coe_statedSpMap, F4Pilot.coe_map_GL]
  ext r c
  simp only [tauMat_apply, Matrix.map_apply, map_sub, map_mul]

variable [Finite K] [Finite F]

theorem tauEquiv_statedSpMap (ι : K →+* F) (g : StatedSp 2 K) :
    tauEquiv (statedSpMap ι 2 g) = statedSpMap ι 2 (tauEquiv g) :=
  tauSp_statedSpMap ι g

theorem tauEquiv_fieldSp (σ : F ≃+* F) (x : StatedSp 2 F) :
    tauEquiv (fieldSp 2 F σ x) = fieldSp 2 F σ (tauEquiv x) :=
  CFSG.RankThree.PartTwo.KFacts.tauSp_fieldSp σ x

theorem mulAutCongr_spProjEquiv_tauEquiv :
    MulAut.congr (spProjEquiv 2 F) tauEquiv = tauAut := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  change spProjEquiv 2 F (tauEquiv ((spProjEquiv 2 F).symm (proj 2 F g))) = _
  rw [F4Pilot.spProjEquiv_symm_proj, tauAut_proj]
  rfl

end Tau

section Descent

theorem eq_of_mul_self_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {a b : C} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite C
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sq]
    rcases hx with rfl | rfl | rfl
    · exact mul_one 1
    · exact ha
    · exact hb
  have h1 : (1 : C) ∉ ({a, b} : Finset C) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have hcard : ({1, a, b} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair hab]
  have h3 := (Finset.card_le_card hsub).trans hle
  rw [hcard] at h3
  omega

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_eq_conj_mul_fieldSp_mul_conj_inv_sp4 {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {β : MulAut (StatedSp 2 F)} (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : StatedSp 2 F →* MulAut (StatedSp 2 F)).range) :
    ∃ h : StatedSp 2 F, β = MulAut.conj h * fieldSp 2 F σ * (MulAut.conj h)⁻¹ := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨e, he, hF⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hFc : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hF]
  obtain ⟨hcyc, hcard⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic F e hFc he
  have : Finite (Outer (StatedProj (StatedSp 2 F))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  set a := MulAut.congr (spProjEquiv 2 F) β with ha_def
  have ha : a * a = 1 := by rw [ha_def, ← map_mul, hβ, map_one]
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  set φ := fieldAut 2 F σ with hφ_def
  have hφφ : φ * φ = 1 := by rw [hφ_def, ← map_mul, hσσ, map_one]
  have haout : a ∉ inner (StatedProj (StatedSp 2 F)) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    apply hβi
    refine ⟨g, (MulAut.congr (spProjEquiv 2 F)).injective ?_⟩
    rw [F4Pilot.mulAutCongr_spProjEquiv_conj, conjAut_statedSp, hx]
  have hφout : φ ∉ inner (StatedProj (StatedSp 2 F)) := fun h =>
    hσ1 (CFSG.QuasithinUnique.Lin2.Five.fieldAut_eq_one_of_mem_inner h)
  have hπ : ((a : MulAut (StatedProj (StatedSp 2 F))) : Outer (StatedProj (StatedSp 2 F))) =
      (φ : Outer (StatedProj (StatedSp 2 F))) := by
    refine eq_of_mul_self_eq_one_of_isCyclic ?_ ?_ ?_ ?_
    · rw [← QuotientGroup.mk_mul, ha, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_mul, hφφ, QuotientGroup.mk_one]
    · exact fun h => haout ((QuotientGroup.eq_one_iff a).1 h)
    · exact fun h => hφout ((QuotientGroup.eq_one_iff φ).1 h)
  have hmem : a * φ⁻¹ ∈ inner (StatedProj (StatedSp 2 F)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπ,
      mul_inv_cancel]
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨g, rfl⟩ := proj_surjective x
  have hag : a = conjAut 2 F ⟨g, statedSp_le_gsp g.2⟩ * fieldAut 2 F σ := by
    rw [conjAut_statedSp, hx, inv_mul_cancel_right]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, hh⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_symplectic_quadratic_involution_descent
      (r := 2) (by norm_num) he hF ha g σ hag hσ1
  refine ⟨h, (MulAut.congr (spProjEquiv 2 F)).injective ?_⟩
  rw [← ha_def, hh, map_mul, map_mul, map_inv, F4Pilot.mulAutCongr_spProjEquiv_conj,
    F4Pilot.mulAutCongr_spProjEquiv_fieldSp]

end Descent

section Extension

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_mulAut_statedSpMap_comm_fieldSp_sp4 (ι : K →+* F) {σ : F ≃+* F}
    (hσι : ∀ c, σ (ι c) = ι c) (δ : MulAut (StatedSp 2 K)) :
    ∃ δ' : MulAut (StatedSp 2 F), (∀ g, δ' (statedSpMap ι 2 g) = statedSpMap ι 2 (δ g)) ∧
      ∀ x, δ' (fieldSp 2 F σ x) = fieldSp 2 F σ (δ' x) := by
  obtain ⟨A, ρ, ε, -, hA⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow
      (MulAut.congr (spProjEquiv 2 K) δ)
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  have hδ : δ = MulAut.conj s * fieldSp 2 K ρ * tauEquiv ^ ε := by
    apply (MulAut.congr (spProjEquiv 2 K)).injective
    rw [hA, hs, map_mul, map_mul, map_pow, F4Pilot.mulAutCongr_spProjEquiv_conj,
      F4Pilot.mulAutCongr_spProjEquiv_fieldSp, mulAutCongr_spProjEquiv_tauEquiv]
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq ι ρ
  have hτpow : ∀ (j : ℕ) (g : StatedSp 2 K),
      (tauEquiv ^ j : MulAut (StatedSp 2 F)) (statedSpMap ι 2 g) =
        statedSpMap ι 2 ((tauEquiv ^ j : MulAut (StatedSp 2 K)) g) := by
    intro j
    induction j with
    | zero => intro g; rfl
    | succ j ih =>
      intro g
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, tauEquiv_statedSpMap, ih]
  have hτσ : ∀ (j : ℕ) (x : StatedSp 2 F),
      (tauEquiv ^ j : MulAut (StatedSp 2 F)) (fieldSp 2 F σ x) =
        fieldSp 2 F σ ((tauEquiv ^ j : MulAut (StatedSp 2 F)) x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, tauEquiv_fieldSp, ih]
  have hσρ : ∀ y : StatedSp 2 F,
      fieldSp 2 F σ (fieldSp 2 F ρ' y) = fieldSp 2 F ρ' (fieldSp 2 F σ y) := fun y => by
    rw [← MulAut.mul_apply, ← map_mul, ringAut_mul_comm F σ ρ', map_mul, MulAut.mul_apply]
  refine ⟨MulAut.conj (statedSpMap ι 2 s) * fieldSp 2 F ρ' * tauEquiv ^ ε, fun g => ?_,
    fun x => ?_⟩
  · rw [hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hτpow,
      F4Pilot.fieldSp_statedSpMap ι hρ', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
      map_inv]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hτσ,
      MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      fieldSp_statedSpMap_of_fix ι hσι, hσρ]

end Extension

section Normalize

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulEquiv_statedSpMap_eq_comm_of_two_le (hr : 2 ≤ r) {k : Type} [Field k]
    [Finite k] [CharP k 2] (hk : 4 ≤ Nat.card k) (ι : k →+* K) {σ : K ≃+* K}
    (hσ : orderOf σ = 2) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M]
    (ψ : StatedSp r K ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (hθi : θ ∉ (MulAut.conj : M →* MulAut M).range) (ε : StatedSp r k →* M)
    (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp r K ≃* M, (∀ g, ψ' (statedSpMap ι r g) = ε g) ∧
      ∀ x, θ (ψ' x) = ψ' (fieldSp r K σ x) := by
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact exists_mulEquiv_statedSpMap_eq_comm_of_descent hk ι hfix
      (fun _ hβ hβi => exists_eq_conj_mul_fieldSp_mul_conj_inv_sp4 hσ hβ hβi)
      (exists_mulAut_statedSpMap_comm_fieldSp_sp4 ι fun c => (hfix (ι c)).2 ⟨c, rfl⟩)
      ψ hθ hθi ε hε hεr
  · exact exists_mulEquiv_statedSpMap_eq_comm hr3 hk ι hσ hfix ψ hθ hθi ε hε hεr

end Normalize

end CFSG.SeitzReduction.SymplecticPilot

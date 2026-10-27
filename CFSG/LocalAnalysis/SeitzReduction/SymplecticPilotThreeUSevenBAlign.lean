module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenBOrth

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open scoped MatrixGroups

section Rigid

variable {F : Type} [Field F] [CharP F 2] {K : Type} [Field K]

theorem usa_eq_one_or_eq_of_fix {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) {ι : K →+* F}
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {ω : F} (hω : σ ω = ω + 1) {ρ : F ≃+* F}
    (hρ : ∀ c, ρ (ι c) = ι c) : (∀ a, ρ a = a) ∨ ∀ a, ρ a = σ a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hdec : ∀ a : F, ∃ s₁ s₂ : F, σ s₁ = s₁ ∧ σ s₂ = s₂ ∧ a = s₁ + s₂ * ω := by
    intro a
    refine ⟨a + (a + σ a) * ω, a + σ a, ?_, ?_, ?_⟩
    · rw [map_add, map_mul, map_add, hσσ, hω]
      linear_combination (σ a) * h2
    · rw [map_add, hσσ, add_comm]
    · linear_combination (-(a + σ a) * ω) * h2
  have hfixρ : ∀ s : F, σ s = s → ρ s = s := fun s hs => by
    obtain ⟨c, rfl⟩ := (hfix s).1 hs
    exact hρ c
  have hn : σ (ω * (ω + 1)) = ω * (ω + 1) := by
    rw [map_mul, map_add, map_one, hω]
    linear_combination (ω + 1) * h2
  have hroot : ρ ω * ρ ω + ρ ω + ω * (ω + 1) = 0 := by
    have h1 : ρ (ω * ω + ω + ω * (ω + 1)) = 0 := by
      rw [show ω * ω + ω + ω * (ω + 1) = 0 by linear_combination (ω * ω + ω) * h2, map_zero]
    rw [map_add, map_add, map_mul, hfixρ _ hn] at h1
    exact h1
  have hcases : ρ ω = ω ∨ ρ ω = ω + 1 := by
    have h1 : (ρ ω - ω) * (ρ ω - (ω + 1)) = 0 := by
      linear_combination hroot - (ρ ω * (ω + 1)) * h2
    rcases mul_eq_zero.1 h1 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hcases with h | h
  · left
    intro a
    obtain ⟨s₁, s₂, h1, h2', rfl⟩ := hdec a
    rw [map_add, map_mul, hfixρ _ h1, hfixρ _ h2', h]
  · right
    intro a
    obtain ⟨s₁, s₂, h1, h2', rfl⟩ := hdec a
    rw [map_add, map_mul, hfixρ _ h1, hfixρ _ h2', h, map_add, map_mul, h1, h2', hω]

variable [Finite F]

omit [CharP F 2] [Finite F] in
theorem usa_hom_ext_sl2 {G : Type*} [Group G] {α β : SL(2, F) →* G}
    (hU : ∀ a, α (sl2Upper a) = β (sl2Upper a)) (hL : ∀ a, α (sl2Lower a) = β (sl2Lower a)) :
    α = β := by
  ext A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus α β := by
    rw [Subgroup.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact hU a
    · exact hL a
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A)

theorem usa_rigid {G : Type*} [Group G] {σ : F ≃+* F} (hσσ : ∀ c, σ (σ c) = c) (ι : K →+* F)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1) {ω : F}
    (hω : σ ω = ω + 1) {α β : SL(2, F) →* G} (hα : Function.Injective α)
    (hβ : Function.Injective β) (hr : α.range = β.range)
    (hU : ∀ c : K, α (sl2Upper (ι c)) = β (sl2Upper (ι c)))
    (hL : ∀ c : K, α (sl2Lower (ι c)) = β (sl2Lower (ι c))) :
    (∀ a, α (sl2Upper a) = β (sl2Upper a) ∧ α (sl2Lower a) = β (sl2Lower a)) ∨
      ∀ a, α (sl2Upper a) = β (sl2Upper (σ a)) ∧ α (sl2Lower a) = β (sl2Lower (σ a)) := by
  set eα := MonoidHom.ofInjective hα with heα
  set eβ := MonoidHom.ofInjective hβ with heβ
  set θ : MulAut SL(2, F) := (eα.trans (MulEquiv.subgroupCongr hr)).trans eβ.symm with hθdef
  have hθ : ∀ A, β (θ A) = α A := by
    intro A
    have h1 : eβ (θ A) = MulEquiv.subgroupCongr hr (eα A) := by
      rw [hθdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    rw [h2]
    exact MonoidHom.ofInjective_apply hα
  have hfixθ : ∀ x, α x = β x → θ x = x := fun x hx => hβ (by rw [hθ, hx])
  obtain ⟨ρ, hρ, hθρ⟩ := CFSG.SeitzReduction.E8Pilot.exists_ringEquiv_of_forall_sl2 ι hK θ
    (fun c => hfixθ _ (hU c)) (fun c => hfixθ _ (hL c))
  rcases usa_eq_one_or_eq_of_fix hσσ hfix hω hρ with h | h
  · left
    intro a
    rw [← hθ (sl2Upper a), (hθρ a).1, h a, ← hθ (sl2Lower a), (hθρ a).2, h a]
    exact ⟨rfl, rfl⟩
  · right
    intro a
    rw [← hθ (sl2Upper a), (hθρ a).1, h a, ← hθ (sl2Lower a), (hθρ a).2, h a]
    exact ⟨rfl, rfl⟩

end Rigid

section Rank

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {j : Fin (n / 2)}
  (hj : j.val + 1 < n / 2)

@[expose] noncomputable def usaU (c : F) : SU σ n :=
  rootHom σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c)

@[expose] noncomputable def usaL (c : F) : SU σ n :=
  rootHom σ hσ (lowIdx_ne_succ hj).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev j j)
    (Multiplicative.ofAdd c)

theorem usaU_mem_rootGroup (c : F) : usaU hσ hj c ∈ rootGroup σ hσ n (Pi.single j 1) :=
  rootHom_mem hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev _ _) (toStd_short hj).symm _

theorem usaL_mem_rootGroup (c : F) : usaL hσ hj c ∈ rootGroup σ hσ n (-Pi.single j 1) :=
  rootHom_mem hσ (lowIdx_ne_succ hj).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev j j)
    (lowIdx_ne_rev _ _) (toStd_short_neg hj).symm _

theorem usaU_mem (c : F) : usaU hσ hj c ∈ rankOne (rootGroup σ hσ n) j :=
  Subgroup.mem_sup_left (usaU_mem_rootGroup hσ hj c)

theorem usaL_mem (c : F) : usaL hσ hj c ∈ rankOne (rootGroup σ hσ n) j :=
  Subgroup.mem_sup_right (usaL_mem_rootGroup hσ hj c)

theorem ctuaBarAut_usaU (c : F) : ctuaBarAut σ hσ n (usaU hσ hj c) = usaU hσ hj (σ c) := by
  rw [usaU, ctuaBarAut_rootHom, toAdd_ofAdd]
  rfl

theorem ctuaBarAut_usaL (c : F) : ctuaBarAut σ hσ n (usaL hσ hj c) = usaL hσ hj (σ c) := by
  rw [usaL, ctuaBarAut_rootHom, toAdd_ofAdd]
  rfl

variable {hσ}

theorem rankOneShortEquiv_usaU (c : F) :
    CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj ⟨usaU hσ hj c, usaU_mem hσ hj c⟩ =
      sl2Upper c := by
  apply Subtype.ext
  change SUExtras.toBlock (lowIdx _) (lowIdx _) (mat σ n (usaU hσ hj c)) = _
  rw [toBlock_of_mem_pos hj (usaU_mem_rootGroup hσ hj c), CFSG.LieType.Steinberg.coe_sl2Upper,
    mat_apply, usaU, coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq (lowIdx_ne_succ hj) (lowIdx_ne_rev _ _)]

theorem rankOneShortEquiv_usaL (c : F) :
    CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj ⟨usaL hσ hj c, usaL_mem hσ hj c⟩ =
      sl2Lower c := by
  apply Subtype.ext
  change SUExtras.toBlock (lowIdx _) (lowIdx _) (mat σ n (usaL hσ hj c)) = _
  rw [toBlock_of_mem_neg hj (usaL_mem_rootGroup hσ hj c), CFSG.LieType.Steinberg.coe_sl2Lower,
    mat_apply, usaL, coe_rootHom, toAdd_ofAdd,
    rootMatrix_apply_pq (lowIdx_ne_succ hj).symm (lowIdx_ne_rev _ _)]

theorem rankOneShortEquiv_symm_sl2Upper (c : F) :
    (CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj).symm (sl2Upper c) =
      ⟨usaU hσ hj c, usaU_mem hσ hj c⟩ := by
  rw [MulEquiv.symm_apply_eq, rankOneShortEquiv_usaU]

theorem rankOneShortEquiv_symm_sl2Lower (c : F) :
    (CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj).symm (sl2Lower c) =
      ⟨usaL hσ hj c, usaL_mem hσ hj c⟩ := by
  rw [MulEquiv.symm_apply_eq, rankOneShortEquiv_usaL]

end Rank

section Siegel

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {N ε : ℕ}
  {hε : ε ≤ 1}

theorem ctufSiegel_transvection {p q : Fin N} (hpq : p ≠ q) (a : F) {i j : Fin (2 * N + ε)}
    (hi : ctuCoord N ε (Sum.inl (Sum.inl p)) = i) (hj : ctuCoord N ε (Sum.inl (Sum.inl q)) = j)
    (hij : i ≠ j) (hii : i ≠ Fin.rev i) (hjj : j ≠ Fin.rev j) :
    ctufSiegel σ hσ ε hε (SpecialLinearGroup.transvection hpq a) =
      rootHom σ hσ hij hii hjj (Multiplicative.ofAdd a) := by
  subst hi hj
  apply Subtype.ext
  apply Units.ext
  rw [coe_rootHom, toAdd_ofAdd, rootMatrix, ctuCoord_rev hε, ctuCoord_rev hε, ctuPar_inl,
    ctuPar_inl, par_inl, par_inl]
  ext a' b'
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a'
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b'
  rw [ctufSiegel_apply_ctuCoord, Matrix.sub_apply, Matrix.add_apply, single_apply, single_apply,
    one_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with (u | u) | k <;> rcases w' with (v | v) | k'
  · simp only [fromBlocks_apply₁₁, ctufSiegelMat, SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply, single_apply, Sum.inl.injEq, reduceCtorEq, and_false,
      ite_false, sub_zero]
  · simp [fromBlocks_apply₁₁, ctufSiegelMat]
  · simp [fromBlocks_apply₁₂]
  · simp [fromBlocks_apply₁₁, ctufSiegelMat]
  · simp only [fromBlocks_apply₁₁, ctufSiegelMat, fromBlocks_apply₂₂, transpose_apply, map_apply,
      Matrix.SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply, single_apply, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, ite_false, add_zero]
    by_cases h2 : q = u ∧ p = v
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hpq, Ne.symm hpq, map_neg, sub_eq_add_neg]
    · have h2' : ¬(p = v ∧ q = u) := fun h => h2 ⟨h.2, h.1⟩
      simp only [h2', h2, ite_false, add_zero, sub_zero]
      by_cases h1 : u = v
      · subst h1
        simp
      · simp [h1, Ne.symm h1]
  · simp [fromBlocks_apply₁₂]
  · simp [fromBlocks_apply₂₁]
  · simp [fromBlocks_apply₂₁]
  · simp [fromBlocks_apply₂₂, Matrix.one_apply]

theorem ctufSiegel_eq_usaU {j : Fin ((2 * N + ε) / 2)} (hj : j.val + 1 < (2 * N + ε) / 2)
    (hjN : j.val + 1 < N) (a : F) :
    ctufSiegel σ hσ ε hε (SpecialLinearGroup.transvection
      (show (⟨j.val, by omega⟩ : Fin N) ≠ ⟨j.val + 1, hjN⟩ from fun h => by
        simp [Fin.ext_iff] at h) a) = usaU hσ hj a :=
  ctufSiegel_transvection hσ _ a (lowIdx_eq_ctuCoord (by omega)).symm
    (lowIdx_eq_ctuCoord hjN).symm (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)

theorem ctufSiegel_eq_usaL {j : Fin ((2 * N + ε) / 2)} (hj : j.val + 1 < (2 * N + ε) / 2)
    (hjN : j.val + 1 < N) (a : F) :
    ctufSiegel σ hσ ε hε (SpecialLinearGroup.transvection
      (show (⟨j.val + 1, hjN⟩ : Fin N) ≠ ⟨j.val, by omega⟩ from fun h => by
        simp [Fin.ext_iff] at h) a) = usaL hσ hj a :=
  ctufSiegel_transvection hσ _ a (lowIdx_eq_ctuCoord hjN).symm
    (lowIdx_eq_ctuCoord (by omega)).symm (lowIdx_ne_succ hj).symm (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev j j)

theorem rankOne_le_range_ctufSiegel {j : Fin ((2 * N + ε) / 2)}
    (hj : j.val + 1 < (2 * N + ε) / 2) :
    rankOne (rootGroup σ hσ (2 * N + ε)) j ≤ (ctufSiegel σ hσ ε hε).range := by
  have hjN : j.val + 1 < N := by omega
  intro x hx
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj with heR
  set φ : SL(2, F) →* SU σ (2 * N + ε) :=
    (rankOne (rootGroup σ hσ (2 * N + ε)) j).subtype.comp eR.symm.toMonoidHom with hφ
  have hU : ∀ a, φ (sl2Upper a) = usaU hσ hj a := fun a => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, rankOneShortEquiv_symm_sl2Upper]
    rfl
  have hL : ∀ a, φ (sl2Lower a) = usaL hσ hj a := fun a => by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, rankOneShortEquiv_symm_sl2Lower]
    rfl
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      (ctufSiegel σ hσ ε hε).range.comap φ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hU]
      exact ⟨_, ctufSiegel_eq_usaU hσ hj hjN a⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, hL]
      exact ⟨_, ctufSiegel_eq_usaL hσ hj hjN a⟩
  have hx' : x = φ (eR ⟨x, hx⟩) := by
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  rw [hx']
  exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 _)

end Siegel

section Bar

variable {N ε : ℕ} {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {hε : ε ≤ 1}

theorem usa_hν : σ ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by simp

theorem usa_ctuaTwist_one_apply (b : Bool) (x : SU σ (2 * N + ε)) :
    ctuaTwist hε σ hσ 1 usa_hν b x = bif b then ctuaBarAut σ hσ (2 * N + ε) x else x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [ctuaTwist_apply_apply]
  have h1 : ∀ a : Fin (2 * N + ε), ctuaTorEntry (N := N) (ε := ε) ((1 : Fˣ) : F) a = 1 := by
    intro a
    obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
    rcases w with u | k
    · exact ctuaTorEntry_inl _ u
    · rw [ctuaTorEntry_inr, Units.val_one]
  have h2 : ∀ a : Fin (2 * N + ε), ctuaTorEntry (N := N) (ε := ε) (((1 : Fˣ)⁻¹ : Fˣ) : F) a = 1 :=
    fun a => by rw [inv_one]; exact h1 a
  rw [h1, h2, one_mul, mul_one]
  cases b
  · rfl
  · simp only [Bool.cond_true]
    rw [coe_ctuaBarAut, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
    rfl

end Bar

section Align

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

omit [Finite K] in
theorem exists_twist_eq_on_rankOne (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
    {e : L ≃* StatedSp 3 K} {k : Fin 3}
    (P : CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k)
    {j : Fin ((2 * 3 + 1) / 2)} (hj : j.val + 1 < (2 * 3 + 1) / 2) (hkj : k.val ≠ j.val)
    (hkj' : k.val ≠ j.val + 1) (β : SL(2, F) →* G) (hβ : Function.Injective β)
    (hβr : β.range = pieceCore e ({⟨j.val, by omega⟩} : Finset (Fin 3)))
    (hβU : ∀ c : K, β (sl2Upper (ι c)) =
      ((e.symm (simpleRootHom K (⟨j.val, by omega⟩ : Fin 3) (sl2Upper c)) : L) : G))
    (hβL : ∀ c : K, β (sl2Lower (ι c)) =
      ((e.symm (simpleRootHom K (⟨j.val, by omega⟩ : Fin 3) (sl2Lower c)) : L) : G)) :
    ∃ b : Bool, ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + 1))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
        (2 * 3 + 1)) j),
      (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := unitaryInvolution_involutive hF)
        usa_hν b)).Φ ⟨x, rankOne_le_ctuBlock le_rfl j hkj hkj' hx⟩ =
          β (CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := unitaryInvolution_involutive hF)
            hj ⟨x, hx⟩) := by
  classical
  have hσ := unitaryInvolution_involutive hF
  have hjN : j.val + 1 < 3 := by omega
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj with heR
  have hRle : rankOne (rootGroup (unitaryInvolution F 2 f) hσ (2 * 3 + 1)) j ≤
      ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin 3)) := fun x hx =>
    rankOne_le_ctuBlock le_rfl j hkj hkj' hx
  have htw : ∀ (b : Bool) (y : SU (unitaryInvolution F 2 f) (2 * 3 + 1))
      (hy : y ∈ ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin 3)))
      (hy' : (bif b then ctuaBarAut _ hσ (2 * 3 + 1) y else y) ∈
        ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin 3))),
      (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν b)).Φ ⟨y, hy⟩ =
        P.Φ ⟨_, hy'⟩ := by
    intro b y hy hy'
    rw [CtuParam.twistBy_Φ_apply]
    congr 1
    apply Subtype.ext
    rw [CtuaAdmissible.coe_restrict]
    exact usa_ctuaTwist_one_apply b y
  set αb : Bool → SL(2, F) →* G := fun b =>
    (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν b)).Φ.comp
      ((Subgroup.inclusion hRle).comp eR.symm.toMonoidHom) with hαbdef
  have hαU : ∀ (b : Bool) (a : F), αb b (sl2Upper a) =
      P.Φ ⟨usaU hσ hj (bif b then unitaryInvolution F 2 f a else a),
        hRle (usaU_mem hσ hj _)⟩ := by
    intro b a
    change (P.twistBy _).Φ (Subgroup.inclusion hRle (eR.symm (sl2Upper a))) = _
    rw [rankOneShortEquiv_symm_sl2Upper]
    refine (htw b _ _ ?_).trans ?_
    · cases b
      · exact hRle (usaU_mem hσ hj a)
      · rw [Bool.cond_true, ctuaBarAut_usaU]
        exact hRle (usaU_mem hσ hj _)
    · congr 2
      cases b
      · rfl
      · exact ctuaBarAut_usaU hσ hj a
  have hαL : ∀ (b : Bool) (a : F), αb b (sl2Lower a) =
      P.Φ ⟨usaL hσ hj (bif b then unitaryInvolution F 2 f a else a),
        hRle (usaL_mem hσ hj _)⟩ := by
    intro b a
    change (P.twistBy _).Φ (Subgroup.inclusion hRle (eR.symm (sl2Lower a))) = _
    rw [rankOneShortEquiv_symm_sl2Lower]
    refine (htw b _ _ ?_).trans ?_
    · cases b
      · exact hRle (usaL_mem hσ hj a)
      · rw [Bool.cond_true, ctuaBarAut_usaL]
        exact hRle (usaL_mem hσ hj _)
    · congr 2
      cases b
      · rfl
      · exact ctuaBarAut_usaL hσ hj a
  have hinj : ∀ b, Function.Injective (αb b) := by
    intro b
    rw [injective_iff_map_eq_one]
    intro A hA
    have hz := (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν b)).ker_le hA
    have hc : eR.symm A ∈ center (rankOne (rootGroup (unitaryInvolution F 2 f) hσ
        (2 * 3 + 1)) j) := by
      rw [mem_center_iff]
      intro g
      have h1 := mem_center_iff.1 hz (Subgroup.inclusion hRle g)
      have h2 : ((Subgroup.inclusion hRle g * Subgroup.inclusion hRle (eR.symm A) :
          ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin 3))) :
            SU (unitaryInvolution F 2 f) (2 * 3 + 1)) =
          ((Subgroup.inclusion hRle (eR.symm A) * Subgroup.inclusion hRle g :
            ctuBlock (unitaryInvolution F 2 f) 1 ({k} : Finset (Fin 3))) :
              SU (unitaryInvolution F 2 f) (2 * 3 + 1)) :=
        congrArg Subtype.val h1
      exact Subtype.ext h2
    have hc' : A ∈ center SL(2, F) := by
      rw [mem_center_iff]
      intro B
      apply eR.symm.injective
      rw [map_mul, map_mul]
      exact mem_center_iff.1 hc (eR.symm B)
    rw [center_SL_two_eq_bot_of_charTwo, mem_bot] at hc'
    exact hc'
  have hrange : (αb false).range = β.range := by
    have hle : (αb false).range ≤ β.range := by
      rw [hβr]
      rintro _ ⟨A, rfl⟩
      exact (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν false)).mem_pieceCore
        hF hf (by norm_num) j hkj hkj' (eR.symm A).2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hβ).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective (hinj false)).toEquiv]
  have hy : ∀ A : SL(2, K), simpleRootHom K (⟨j.val, by omega⟩ : Fin 3) A ∈
      spBlock K ({k} : Finset (Fin 3))ᶜ := fun A =>
    simpleRootSL2_le_spBlock_compl (fun h => hkj (by rw [h])) (fun _ h => hkj' (by rw [h]))
      ⟨A, rfl⟩
  have hU0 : ∀ c : K, usaU hσ hj (ι c) = ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
      (simpleRootHom K (⟨j.val, by omega⟩ : Fin 3) (sl2Upper c)) := by
    intro c
    rw [simpleRootHom_of_lt (by simp only; omega), shortBlock_sl2Upper,
      usb_ctuEmbed_elt_difference_eq_rootHom hσ _ (lowIdx_eq_ctuCoord (by omega)).symm
        (lowIdx_eq_ctuCoord hjN).symm (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)]
    rfl
  have hL0 : ∀ c : K, usaL hσ hj (ι c) = ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
      (simpleRootHom K (⟨j.val, by omega⟩ : Fin 3) (sl2Lower c)) := by
    intro c
    rw [simpleRootHom_of_lt (by simp only; omega), shortBlock_sl2Lower,
      usb_ctuEmbed_elt_difference_eq_rootHom hσ _ (lowIdx_eq_ctuCoord hjN).symm
        (lowIdx_eq_ctuCoord (by omega)).symm (lowIdx_ne_succ hj).symm (lowIdx_ne_rev _ _)
          (lowIdx_ne_rev j j)]
    rfl
  have hU : ∀ c : K, αb false (sl2Upper (ι c)) = β (sl2Upper (ι c)) := by
    intro c
    rw [hαU false, hβU c]
    exact P.N1' (hy _) _ (hU0 c)
  have hL : ∀ c : K, αb false (sl2Lower (ι c)) = β (sl2Lower (ι c)) := by
    intro c
    rw [hαL false, hβL c]
    exact P.N1' (hy _) _ (hL0 c)
  have hfix := ctuf_fix_iff hKc hF (by omega) hι
  have hK3 : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le (hKc ▸ four_le_two_pow hf)
    exact ⟨κ, κ.ne_zero, fun h => hκ (by rw [show κ = 1 from Units.ext h, one_mul])⟩
  have hσσ : unitaryInvolution F 2 f * unitaryInvolution F 2 f = 1 :=
    RingEquiv.ext fun c => hσ c
  obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution
    (usb_unitaryInvolution_ne_one hF) hσσ
  have hconc : ∀ b, αb b = β → ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + 1))
      (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) hσ (2 * 3 + 1)) j),
      (P.twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν b)).Φ
        ⟨x, rankOne_le_ctuBlock le_rfl j hkj hkj' hx⟩ = β (eR ⟨x, hx⟩) := by
    intro b hb x hx
    rw [← hb]
    change _ = (P.twistBy _).Φ (Subgroup.inclusion hRle (eR.symm (eR ⟨x, hx⟩)))
    rw [MulEquiv.symm_apply_apply]
    rfl
  rcases usa_rigid hσ ι hfix hK3 hω (hinj false) hβ hrange hU hL with h | h
  · exact ⟨false, hconc false (usa_hom_ext_sl2 (fun a => (h a).1) (fun a => (h a).2))⟩
  · refine ⟨true, hconc true (usa_hom_ext_sl2 (fun a => ?_) (fun a => ?_))⟩
    · rw [hαU true, Bool.cond_true]
      have h1 := (h (unitaryInvolution F 2 f a)).1
      rw [hαU false, Bool.cond_false, hσ] at h1
      exact h1
    · rw [hαL true, Bool.cond_true]
      have h1 := (h (unitaryInvolution F 2 f a)).2
      rw [hαL false, Bool.cond_false, hσ] at h1
      exact h1

end Align

section RhoS

open CFSG.LieType.Universal.Symplectic.SpExtras (elt)

theorem usa_leviEmbedSL_transvection {F : Type} [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (c : F) : leviEmbedSL F n (SpecialLinearGroup.transvection hij c) =
      elt (.difference i j hij) c := by
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.elt_difference_eq_leviHom,
    ← TauCeti.toGL_transvection_eq_transvectionUnit]
  rfl

theorem usa_map_sl2Upper {F F' : Type} [Field F] [Field F'] (θ : F →+* F') (a : F) :
    SpecialLinearGroup.map θ (sl2Upper a) = sl2Upper (θ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.SpecialLinearGroup.map_apply_coe]

theorem usa_map_sl2Lower {F F' : Type} [Field F] [Field F'] (θ : F →+* F') (a : F) :
    SpecialLinearGroup.map θ (sl2Lower a) = sl2Lower (θ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.SpecialLinearGroup.map_apply_coe]

theorem usa_map_transvection {F F' : Type} [Field F] [Field F'] (θ : F →+* F') {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (a : F) :
    SpecialLinearGroup.map θ (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij (θ a) := by
  ext p q
  simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]

abbrev usaJ : Finset (Fin ((2 * 3 + 1) / 2)) := {⟨0, by norm_num⟩, ⟨1, by norm_num⟩}

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {F : Type}
  [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {F' : Type} [Field F']
  {e : L ≃* StatedSp 3 K} {t : G} {ι' : K →+* F'} {σ' : F' ≃+* F'}

theorem usa_levi_le_range :
    levi (rootGroup σ hσ (2 * 3 + 1)) usaJ ≤
        (ctufSiegel σ hσ 1 le_rfl : SL(3, F) →* SU σ (2 * 3 + 1)).range := by
  refine iSup₂_le fun j hj => ?_
  have hj3 : j.val + 1 < (2 * 3 + 1) / 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> norm_num
  exact rankOne_le_range_ctufSiegel hσ hj3

@[expose] noncomputable def usaSiegelEquiv :
    SL(3, F) ≃* (ctufSiegel σ hσ 1 le_rfl : SL(3, F) →* SU σ (2 * 3 + 1)).range :=
  MonoidHom.ofInjective (ctufSiegel_injective (N := 3) (σ := σ) (hσ := hσ) (ε := 1)
    (hε := le_rfl))

theorem usaSiegelEquiv_symm_apply {z : (ctufSiegel σ hσ 1 le_rfl :
    SL(3, F) →* SU σ (2 * 3 + 1)).range} {A : SL(3, F)}
    (hA : (z : SU σ (2 * 3 + 1)) = (ctufSiegel σ hσ 1 le_rfl : SL(3, F) →* SU σ (2 * 3 + 1)) A) :
    (usaSiegelEquiv hσ).symm z = A := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [hA]
  exact (MonoidHom.ofInjective_apply _).symm

variable (S : SiegelFieldParam e t ι' σ') (θ : F ≃+* F')

@[expose] noncomputable def usaRho : levi (rootGroup σ hσ (2 * 3 + 1)) usaJ →* G :=
  (S.Φ.comp ((siegelLeviEquiv (K := F') (n := 3)).toMonoidHom.comp
    (SpecialLinearGroup.map (θ : F →+* F')))).comp
      ((usaSiegelEquiv hσ).symm.toMonoidHom.comp (Subgroup.inclusion (usa_levi_le_range hσ)))

omit [CharP K 2] in
theorem usaRho_apply_of_eq (y : levi (rootGroup σ hσ (2 * 3 + 1)) usaJ) (A : SL(3, F))
    (hA : (y : SU σ (2 * 3 + 1)) =
      (ctufSiegel σ hσ 1 le_rfl : SL(3, F) →* SU σ (2 * 3 + 1)) A) :
    usaRho hσ S θ y = S.Φ (siegelLeviEquiv (SpecialLinearGroup.map (θ : F →+* F') A)) := by
  have h1 : (usaSiegelEquiv hσ).symm (Subgroup.inclusion (usa_levi_le_range hσ) y) = A :=
    usaSiegelEquiv_symm_apply hσ hA
  change S.Φ (siegelLeviEquiv (SpecialLinearGroup.map (θ : F →+* F')
    ((usaSiegelEquiv hσ).symm (Subgroup.inclusion (usa_levi_le_range hσ) y)))) = _
  rw [h1]

omit [CharP K 2] in
theorem usaRho_eq_on_rankOne {j : Fin ((2 * 3 + 1) / 2)} (hj : j.val + 1 < (2 * 3 + 1) / 2)
    (hjJ : j ∈ usaJ)
    (x : SU σ (2 * 3 + 1)) (hx : x ∈ rankOne (rootGroup σ hσ (2 * 3 + 1)) j) :
    usaRho hσ S θ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ hjJ hx⟩ =
      ((S.rootHom (j := (⟨j.val, by omega⟩ : Fin 3)) (by simp only; omega)).comp
        (SpecialLinearGroup.map (θ : F →+* F')))
          (CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj ⟨x, hx⟩) := by
  have hjN : j.val + 1 < 3 := by omega
  set eR := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hj with heR
  set γ : SL(2, F) →* G := (usaRho hσ S θ).comp
    ((Subgroup.inclusion (CFSG.LieType.CurtisTits.rankOne_le_levi
      (rootGroup σ hσ (2 * 3 + 1)) hjJ)).comp eR.symm.toMonoidHom) with hγ
  have hγβ : γ = (S.rootHom (j := (⟨j.val, by omega⟩ : Fin 3)) (by simp only; omega)).comp
      (SpecialLinearGroup.map (θ : F →+* F')) := by
    refine usa_hom_ext_sl2 (fun a => ?_) (fun a => ?_)
    · change usaRho hσ S θ (Subgroup.inclusion (CFSG.LieType.CurtisTits.rankOne_le_levi
        (rootGroup σ hσ (2 * 3 + 1)) hjJ) (eR.symm (sl2Upper a))) = _
      rw [rankOneShortEquiv_symm_sl2Upper, MonoidHom.comp_apply, usa_map_sl2Upper,
        SiegelFieldParam.rootHom_apply]
      rw [usaRho_apply_of_eq hσ S θ _ _ (ctufSiegel_eq_usaU hσ hj hjN a).symm]
      congr 1
      apply Subtype.ext
      rw [coe_siegelLeviEquiv_apply, usa_map_transvection, usa_leviEmbedSL_transvection]
      change _ = simpleRootHom F' (⟨j.val, by omega⟩ : Fin 3) (sl2Upper (θ a))
      rw [simpleRootHom_of_lt (by simp only; omega), shortBlock_sl2Upper]
      rfl
    · change usaRho hσ S θ (Subgroup.inclusion (CFSG.LieType.CurtisTits.rankOne_le_levi
        (rootGroup σ hσ (2 * 3 + 1)) hjJ) (eR.symm (sl2Lower a))) = _
      rw [rankOneShortEquiv_symm_sl2Lower, MonoidHom.comp_apply, usa_map_sl2Lower,
        SiegelFieldParam.rootHom_apply]
      rw [usaRho_apply_of_eq hσ S θ _ _ (ctufSiegel_eq_usaL hσ hj hjN a).symm]
      congr 1
      apply Subtype.ext
      rw [coe_siegelLeviEquiv_apply, usa_map_transvection, usa_leviEmbedSL_transvection]
      change _ = simpleRootHom F' (⟨j.val, by omega⟩ : Fin 3) (sl2Lower (θ a))
      rw [simpleRootHom_of_lt (by simp only; omega), shortBlock_sl2Lower]
      rfl
  rw [← hγβ]
  change _ = usaRho hσ S θ (Subgroup.inclusion (CFSG.LieType.CurtisTits.rankOne_le_levi
    (rootGroup σ hσ (2 * 3 + 1)) hjJ) (eR.symm (eR ⟨x, hx⟩)))
  rw [MulEquiv.symm_apply_apply]
  rfl

end RhoS

theorem spThreeUnitaryOddSiegelAlignInput_holds : SpThreeUnitaryOddSiegelAlignInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot hstd F _ _ _ hF ι hι hP F' _ _ ι' σ'
    hσ1 hσσ hfix hS
  obtain ⟨S⟩ := hS
  have hσ := unitaryInvolution_involutive hF
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have : CharP F' 2 := charP_of_injective_ringHom ι'.injective 2
  have hF' : Nat.card F' = (2 ^ f) ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι' hσ1 hσσ hfix, ← pow_mul, mul_comm]
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι ι' (hF.trans hF'.symm)
  set P : ∀ k : Fin 3, CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k :=
    fun k => (hP k).some with hPdef
  set β : ∀ (j : Fin 3) (hj : j.val + 1 < 3), SL(2, F) →* G := fun j hj =>
    (S.rootHom hj).comp (SpecialLinearGroup.map (θ : F →+* F')) with hβdef
  have hmapθ : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (θ : F →+* F')) := by
    intro A B hAB
    ext i j
    have h := congrArg (fun X : SL(2, F') => (X : Matrix (Fin 2) (Fin 2) F') i j) hAB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply] at h
    exact θ.injective h
  have hmapθs : Function.Surjective (SpecialLinearGroup.map (n := Fin 2) (θ : F →+* F')) := by
    intro B
    refine ⟨SpecialLinearGroup.map (θ.symm : F' →+* F) B, ?_⟩
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have hβinj : ∀ j hj, Function.Injective (β j hj) := fun j hj =>
    (S.injective_rootHom hj le_rfl).comp hmapθ
  have hβr : ∀ j hj, (β j hj).range = pieceCore e ({j} : Finset (Fin 3)) := by
    intro j hj
    rw [hβdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hmapθs, ← MonoidHom.range_eq_map,
      S.range_rootHom hj hK4]
  have hβU : ∀ j hj (c : K), β j hj (sl2Upper (ι c)) =
      ((e.symm (simpleRootHom K j (sl2Upper c)) : L) : G) := by
    intro j hj c
    change S.rootHom hj (SpecialLinearGroup.map (θ : F →+* F') (sl2Upper (ι c))) = _
    rw [usa_map_sl2Upper, RingEquiv.coe_toRingHom, hθ, ← usa_map_sl2Upper, S.rootHom_map hj]
  have hβL : ∀ j hj (c : K), β j hj (sl2Lower (ι c)) =
      ((e.symm (simpleRootHom K j (sl2Lower c)) : L) : G) := by
    intro j hj c
    change S.rootHom hj (SpecialLinearGroup.map (θ : F →+* F') (sl2Lower (ι c))) = _
    rw [usa_map_sl2Lower, RingEquiv.coe_toRingHom, hθ, ← usa_map_sl2Lower, S.rootHom_map hj]
  have h0 : (⟨0, by norm_num⟩ : Fin ((2 * 3 + 1) / 2)).val + 1 < (2 * 3 + 1) / 2 := by norm_num
  have h1 : (⟨1, by norm_num⟩ : Fin ((2 * 3 + 1) / 2)).val + 1 < (2 * 3 + 1) / 2 := by norm_num
  obtain ⟨b₂, hb₂⟩ := exists_twist_eq_on_rankOne hKc hf hF (P 2) h0 (by decide) (by decide)
    (β ⟨0, by norm_num⟩ (by norm_num)) (hβinj _ _) (hβr _ _) (hβU _ _) (hβL _ _)
  obtain ⟨b₀, hb₀⟩ := exists_twist_eq_on_rankOne hKc hf hF (P 0) h1 (by decide) (by decide)
    (β ⟨1, by norm_num⟩ (by norm_num)) (hβinj _ _) (hβr _ _) (hβU _ _) (hβL _ _)
  refine ⟨fun k => (P k).twistBy (ctuaTwist_admissible (hε := le_rfl) (hσ := hσ) usa_hν
    (![b₀, false, b₂] k)), usaRho hσ S θ, fun x hx => ?_, fun x hx => ?_⟩
  · rw [usaRho_eq_on_rankOne hσ S θ h0 (by simp) x hx]
    exact (hb₂ x hx).symm
  · rw [usaRho_eq_on_rankOne hσ S θ h1 (by simp) x hx]
    exact (hb₀ x hx).symm

end CFSG.SeitzReduction.SymplecticPilot

module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Final
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.FixDim

public section

open Matrix CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
  CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.HardMathSupport.GuralnickMalle
open CFSG.Open
open Module

namespace CFSG.LieType.SpecialLinear

theorem fixF_comp_of_surjective {F : Type*} [Field F] {Idx ι ι' : Type*} [Fintype Idx]
    {f : ι → ι'} (hf : Function.Surjective f) (T : ι' → Matrix Idx Idx F) :
    fixF (fun i => T (f i)) = fixF T := by
  ext v
  change (∀ i : ι, T (f i) *ᵥ v = v) ↔ (∀ i : ι', T i *ᵥ v = v)
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := hf i
    exact h j
  · exact fun h i => h (f i)

theorem finrank_fixSubGen_sl6Exterior3Rep_eq_finrank_fixF
    {K : Type} [Field K] (A : Subgroup (StatedSL 6 K)) [Finite A] :
    Module.finrank K (fixSubGen (sl6Exterior3Rep K) A) =
      Module.finrank K (fixF (fun a : A =>
        minorMatrix 3 (((a : StatedSL 6 K) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K))) := by
  classical
  let B : Basis (Set.powersetCard (Fin 6) 3) K (⋀[K]^3 (Fin 6 → K)) :=
    (Pi.basisFun K (Fin 6)).exteriorPower 3
  have hmul (a : A) (v : ⋀[K]^3 (Fin 6 → K)) :
      (minorMatrix 3 (((a : StatedSL 6 K) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)).mulVec (B.equivFun v) =
        B.equivFun ((sl6Exterior3Rep K) (a : StatedSL 6 K) v) := by
    have h := LinearMap.toMatrix_mulVec_repr B B
      (exteriorPower.map 3
        (Matrix.toLin' (((a : StatedSL 6 K) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K))) v
    rw [toMatrix_exteriorPower_map] at h
    rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_apply] at h
    simpa [sl6Exterior3Rep_apply, slNaturalRep_eq_toLin] using h
  have hmap : (fixSubGen (sl6Exterior3Rep K) A).map B.equivFun.toLinearMap =
      fixF (fun a : A =>
        minorMatrix 3 (((a : StatedSL 6 K) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) := by
    ext x
    rw [Submodule.mem_map, mem_fixF]
    constructor
    · rintro ⟨v, hv, rfl⟩ a
      simpa using (hmul a v).trans
        (congrArg B.equivFun ((mem_fixSubGen.mp hv) a a.2))
    · intro hx
      refine ⟨B.equivFun.symm x, ?_, B.equivFun.apply_symm_apply x⟩
      rw [mem_fixSubGen]
      intro a ha
      apply B.equivFun.injective
      have h := hmul ⟨a, ha⟩ (B.equivFun.symm x)
      rw [B.equivFun.apply_symm_apply] at h ⊢
      rw [← h]
      exact hx ⟨a, ha⟩
  calc Module.finrank K (fixSubGen (sl6Exterior3Rep K) A)
      = Module.finrank K ((fixSubGen (sl6Exterior3Rep K) A).map
          B.equivFun.toLinearMap) :=
        (LinearEquiv.finrank_map_eq B.equivFun _).symm
    _ = Module.finrank K (fixF (fun a : A =>
          minorMatrix 3 (((a : StatedSL 6 K) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K))) := by
        rw [hmap]

theorem mul_card_mul_pow_finrank_fixK_minorMatrix_lt {K : Type} [Field K] [Fintype K]
    [CharP K 2] {m : ℕ} (hm : m < Fintype.card K) {k : Type} [Field k] [Algebra K k]
    (τ : K ≃+* K) (A : Subgroup (SpecialLinearGroup (Fin 6) K)) (hA : A ≠ ⊥)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) :
    m * Nat.card A * Fintype.card K ^ Module.finrank k (fixK (k := k)
        (fun a : A => minorMatrix 3
          (((a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map τ))) <
      Fintype.card K ^ 20 := by
  classical
  have hmNat : m < Nat.card K := by
    rwa [Nat.card_eq_fintype_card]
  let eSL : SpecialLinearGroup (Fin 6) K ≃* StatedSL 6 K :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 6 K
  let φτ : SpecialLinearGroup (Fin 6) K →* StatedSL 6 K :=
    eSL.toMonoidHom.comp (SpecialLinearGroup.map τ.toRingHom)
  have hφτ_inj : Function.Injective φτ := by
    intro a b hab
    have h' := congrArg (fun x : StatedSL 6 K =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hab
    have hmap : (a : Matrix (Fin 6) (Fin 6) K).map τ =
        (b : Matrix (Fin 6) (Fin 6) K).map τ := by
      simpa [φτ, eSL, Matrix.SpecialLinearGroup.map_apply_coe,
        CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] using h'
    exact Subtype.ext (Matrix.map_injective τ.injective hmap)
  let Aτ : Subgroup (StatedSL 6 K) := A.map φτ
  have hAτ : Aτ ≠ ⊥ := by
    change A.map φτ ≠ ⊥
    intro hbot
    exact hA ((Subgroup.map_eq_bot_iff_of_injective (H := A) (f := φτ) hφτ_inj).mp
      hbot)
  have hAelτ : CFSG.IsElementaryAbelian 2 ↥Aτ := by
    change CFSG.IsElementaryAbelian 2 ↥(A.map φτ)
    exact hAel.subgroup_map φτ
  have hcardA : Nat.card Aτ = Nat.card A := by
    change Nat.card ↥(A.map φτ) = Nat.card ↥A
    exact Subgroup.card_map_of_injective hφτ_inj
  let T : A → Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K :=
    fun a => minorMatrix 3
      (((a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map τ)
  let Tτ : Aτ → Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K :=
    fun a => minorMatrix 3
      (((a : StatedSL 6 K) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  let φ : A → Aτ := fun a => ⟨φτ (a : SpecialLinearGroup (Fin 6) K),
    Subgroup.mem_map_of_mem φτ a.2⟩
  have hφsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, ha, hb⟩ := Subgroup.mem_map.mp b.2
    exact ⟨⟨a, ha⟩, Subtype.ext hb⟩
  have hTcomm (a : A) : Tτ (φ a) = T a := by
    simp [T, Tτ, φ, φτ, eSL, Matrix.SpecialLinearGroup.map_apply_coe,
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  have hfixF : Module.finrank K (fixF Tτ) = Module.finrank K (fixF T) := by
    rw [← fixF_comp_of_surjective hφsurj Tτ, funext hTcomm]
  have hfixSub : Module.finrank K (fixSubGen (sl6Exterior3Rep K) Aτ) =
      Module.finrank K (fixF Tτ) := by
    simpa [Tτ] using finrank_fixSubGen_sl6Exterior3Rep_eq_finrank_fixF Aτ
  have hfixK : Module.finrank k (fixK (k := k) T) =
      Module.finrank K (fixSubGen (sl6Exterior3Rep K) Aτ) := by
    rw [finrank_fixK T, ← hfixF]
    exact hfixSub.symm
  have hmain' : m * (Nat.card A * Fintype.card K ^
      Module.finrank K (fixSubGen (sl6Exterior3Rep K) Aτ)) <
      Fintype.card K ^ 20 := by
    have h := sl6Exterior3_mul_weight1Gen_lt (K := K) (m := m) hmNat Aτ hAτ hAelτ
    rw [weight1Gen] at h
    have hfixcard : Nat.card (fixSubGen (sl6Exterior3Rep K) Aτ) =
        Nat.card K ^ Module.finrank K (fixSubGen (sl6Exterior3Rep K) Aτ) :=
      @Module.natCard_eq_pow_finrank K ↥(fixSubGen (sl6Exterior3Rep K) Aτ) _ _ _
        (FiniteDimensional.finiteDimensional_submodule _)
    have hKcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
    rw [hcardA, hfixcard, card_sl6Exterior3, hKcard] at h
    exact h
  rw [← hfixK] at hmain'
  simpa [T, mul_assoc] using hmain'

theorem two_mul_card_mul_pow_finrank_fixK_minorMatrix_lt {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : 2 < Fintype.card K) {k : Type} [Field k] [Algebra K k] (τ : K ≃+* K)
    (A : Subgroup (SpecialLinearGroup (Fin 6) K)) (hA : A ≠ ⊥)
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) :
    2 * Nat.card A * Fintype.card K ^ Module.finrank k (fixK (k := k)
        (fun a : A => minorMatrix 3
          (((a : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map τ))) <
      Fintype.card K ^ 20 :=
  mul_card_mul_pow_finrank_fixK_minorMatrix_lt (m := 2) hK τ A hA hAel

end CFSG.LieType.SpecialLinear

module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits

variable {K : Type} [Field K]

noncomputable abbrev rankOneTwo
    (K : Type) [Field K] : Subgroup (adjointGroup d4 K) :=
  CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K) (nd 2)

noncomputable abbrev restrictTwo
    (K : Type) [Field K] :
    rankOneTwo K →* Matrix.SpecialLinearGroup (Fin 2) K :=
  restrictHom (K := K) (rootOperatorFamily d4) cartan_two_zero

theorem twistC_mem_rankOneTwo
    (σ : K →+* K) {y : adjointGroup d4 K} (hy : y ∈ rankOneTwo K) :
    twistC .D4 K σ y ∈ rankOneTwo K := by
  have h := twistC_mem_rankOne σ hy
  rwa [rhoPerm_two] at h

noncomputable abbrev twistTwo
    (σ : K →+* K) : rankOneTwo K →* rankOneTwo K :=
  ((twistC .D4 K σ).comp (rankOneTwo K).subtype).codRestrict _
    fun y => twistC_mem_rankOneTwo σ y.2

theorem restrictHom_twistC
    (σ : K →+* K) (y : rankOneTwo K) :
    restrictTwo K (twistTwo σ y) =
      Matrix.SpecialLinearGroup.map σ (restrictTwo K y) := by
  set f := ((restrictTwo K).comp (twistTwo σ)).prod
    ((Matrix.SpecialLinearGroup.map σ).comp (restrictTwo K)) with hf
  have h := forall_mem_of_rankOne (nd 2) f (MonoidHom.eqLocus (MonoidHom.fst _ _)
    (MonoidHom.snd _ _)) (fun s hs c => ?_) y
  · exact h
  · change restrictTwo K (twistTwo σ ⟨_, xPar_single_mem_rankOne' (nd 2) hs c⟩) =
      Matrix.SpecialLinearGroup.map σ (restrictTwo K ⟨_, xPar_single_mem_rankOne' (nd 2) hs c⟩)
    have e : twistTwo σ ⟨_, xPar_single_mem_rankOne' (nd 2) hs c⟩ =
        ⟨_, xPar_single_mem_rankOne' (nd 2) hs (σ c)⟩ := by
      refine Subtype.ext ?_
      change twistC .D4 K σ (xPar (rootOperatorFamily d4) (s • Pi.single (nd 2) 1) c) = _
      rw [twistC_xPar_smul_single σ hs, rhoPerm_two]
    rw [e]
    rcases hs with rfl | rfl
    · have e1 : ∀ d : K, (⟨_, xPar_single_mem_rankOne' (nd 2) (Or.inl rfl) d⟩ : rankOneTwo K) =
          ⟨xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) d,
            xPar_single_mem_rankOne (F := rootOperatorFamily d4) _ d⟩ := fun d =>
        Subtype.ext (by simp only [one_smul])
      rw [e1, e1, restrictHom_upper cartan_two_zero, restrictHom_upper cartan_two_zero]
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Upper]
    · have e1 : ∀ d : K, (⟨_, xPar_single_mem_rankOne' (nd 2) (Or.inr rfl) d⟩ : rankOneTwo K) =
          ⟨xPar (rootOperatorFamily d4) (-Pi.single (nd 2) 1) d,
            xPar_neg_single_mem_rankOne (F := rootOperatorFamily d4) _ d⟩ := fun d =>
        Subtype.ext (by simp only [neg_one_smul])
      rw [e1, e1, restrictHom_lower cartan_two_zero, restrictHom_lower cartan_two_zero]
      ext p q
      fin_cases p <;> fin_cases q <;> simp [coe_sl2Lower]

variable {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem slLong_mem_rankOne
    (M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    slLong σ hσ M ∈ rankOne (twistedRootGroup σ) (ng 0) := by
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod M
  have hx : ∀ d : fixedField σ, slLong σ hσ (sl2Upper d) ∈ rankOne (twistedRootGroup σ) (ng 0) :=
    fun d => by
      refine Subgroup.mem_sup_left ((mem_twistedRootGroup σ).2 ?_)
      rw [slLong_val, slLongE_upper]
      exact xPar_single_two_mem_twisted hσ d.2
  have hy : ∀ d : fixedField σ, slLong σ hσ (sl2Lower d) ∈ rankOne (twistedRootGroup σ) (ng 0) :=
    fun d => by
      refine Subgroup.mem_sup_right ((mem_twistedRootGroup σ).2 ?_)
      rw [slLong_val, slLongE_lower]
      exact xPar_neg_single_two_mem_twisted hσ d.2
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (hy e) (hx a)) (hy b)) (hx c)

theorem exists_slLong_eq_of_twistC_eq
    {y : adjointGroup d4 K} (hy : y ∈ rankOneTwo K)
    (hF : twistC .D4 K σ y = y) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ),
      ((slLong σ hσ M : twistedGroup σ) : adjointGroup d4 K) = y := by
  have hfix : restrictTwo K ⟨y, hy⟩ ∈ TwistedE6.slFixed K σ := by
    have h := restrictHom_twistC σ ⟨y, hy⟩
    have e : twistTwo σ ⟨y, hy⟩ = ⟨y, hy⟩ := Subtype.ext hF
    rw [e] at h
    exact h.symm
  rw [TwistedE6.mem_slFixed] at hfix
  set N := restrictTwo K ⟨y, hy⟩ with hN
  let M' : Matrix (Fin 2) (Fin 2) (fixedField σ) := fun p q =>
    ⟨(N : Matrix (Fin 2) (Fin 2) K) p q, hfix p q⟩
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : ((M'.det : fixedField σ) : K) = (N : Matrix (Fin 2) (Fin 2) K).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      rfl
    rw [h1, N.2]
    rfl
  set M'' : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) := ⟨M', hdet⟩ with hM''
  refine ⟨M'', ?_⟩
  rw [slLong_val, slLongE]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  have e : Matrix.SpecialLinearGroup.map (fixedField σ).subtype M'' = N := by
    ext p q
    rfl
  rw [e, hN]
  have h2 : (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm
      (restrictHom (rootOperatorFamily d4) cartan_two_zero ⟨y, hy⟩) = ⟨y, hy⟩ :=
    (restrictEquiv (rootOperatorFamily d4) cartan_two_zero).symm_apply_apply ⟨y, hy⟩
  rw [h2]

theorem mem_rankOne_long_of_mem_rankOneTwo
    {g : twistedGroup σ}
    (hg : (g : adjointGroup d4 K) ∈ rankOneTwo K) :
    g ∈ rankOne (twistedRootGroup σ) (ng 0) := by
  obtain ⟨M, hM⟩ := exists_slLong_eq_of_twistC_eq hσ hg
    (twistedGroup_le_twistFixed σ g.2)
  have e : slLong σ hσ M = g := Subtype.ext hM
  rw [← e]
  exact slLong_mem_rankOne hσ M

theorem card_rankOne_long_le
    [Finite K] :
    Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hle : rankOne (twistedRootGroup σ) (ng 0) ≤ (slLong σ hσ).range := by
    intro g hg
    obtain ⟨M, hM⟩ := exists_slLong_eq_of_twistC_eq hσ (val_mem_rankOne_two σ hg)
      (twistedGroup_le_twistFixed σ g.2)
    exact ⟨M, Subtype.ext hM⟩
  calc Nat.card (rankOne (twistedRootGroup σ) (ng 0)) ≤ Nat.card (slLong σ hσ).range :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :=
        Nat.card_congr (MonoidHom.ofInjective (slLong_injective hσ)).toEquiv.symm

omit hσ in
theorem card_fixedField_eq_three (hK : ringChar K ≠ 2) (hσ3 : ∀ c, σ c = c ^ 3) :
    Nat.card (fixedField σ) = 3 := by
  classical
  have h1 : (1 : K) ≠ -1 := fun h => Ring.neg_one_ne_one_of_char_ne_two hK h.symm
  have hmem : ∀ c : K, c ∈ fixedField σ ↔ c ∈ ({0, 1, -1} : Finset K) := by
    intro c
    change σ c = c ↔ _
    rw [hσ3]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h' : c * (c - 1) * (c + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl (sub_eq_zero.1 h3))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h2))
    · rintro (rfl | rfl | rfl) <;> ring
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  exact Finset.card_eq_three.2 ⟨0, 1, -1, zero_ne_one, by simp, h1, rfl⟩

end CFSG.LieType.HighestRoot

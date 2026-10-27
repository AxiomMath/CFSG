module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique.Bridge.Alt57Model

open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.PresentationLocal

@[expose] noncomputable def glSympRingEquiv {K F : Type} [Field K] [Field F] (n : ℕ) (e : K ≃+* F) :
    TauCeti.GLSymplectic (Fin n) K ≃* TauCeti.GLSymplectic (Fin n) F where
  toFun := TauCeti.GLSymplectic.map (Fin n) e.toRingHom
  invFun := TauCeti.GLSymplectic.map (Fin n) e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  right_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  map_mul' := (TauCeti.GLSymplectic.map (Fin n) e.toRingHom).map_mul

@[expose] def fourIdx : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun i := if i = 0 then Sum.inl 0 else if i = 1 then Sum.inl 1 else if i = 2 then Sum.inr 1
    else Sum.inr 0
  invFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 1
    | Sum.inr 1 => 2
    | Sum.inr 0 => 3
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def glFourEquiv : GL (Fin 4) (ZMod 2) ≃* GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).toMulEquiv

theorem glFourEquiv_apply (g : GL (Fin 4) (ZMod 2)) :
    ((glFourEquiv g : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix _ _ (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  rfl

theorem reindex_antidiagGram :
    Matrix.reindex fourIdx fourIdx antidiagGram = Matrix.J (Fin 2) (ZMod 2) := by
  ext a c
  rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;> decide

theorem map_sympFour :
    sympFour.map glFourEquiv.toMonoidHom = TauCeti.GLSymplectic (Fin 2) (ZMod 2) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_sympFour_iff, TauCeti.GLSymplectic.mem_iff']
  set M := ((glFourEquiv.symm g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hg : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx M := by
    rw [← glFourEquiv_apply, MulEquiv.apply_symm_apply]
  have e : ∀ X : Matrix (Fin 4) (Fin 4) (ZMod 2), Matrix.reindex fourIdx fourIdx X =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx X := fun X =>
    (congrFun (Matrix.coe_reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx) X).symm
  rw [hg, ← reindex_antidiagGram, Matrix.transpose_reindex, e, e, e, ← map_mul, ← map_mul]
  exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) fourIdx).injective.eq_iff.symm

@[expose] noncomputable def spTwoEquivPerm :
    TauCeti.GLSymplectic (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 6) :=
  ((glFourEquiv.subgroupMap sympFour).trans (MulEquiv.subgroupCongr map_sympFour)).symm.trans
    (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩)

@[expose] noncomputable def spEquivPerm (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    ↥(StatedSp 2 K) ≃* Equiv.Perm (Fin 6) :=
  (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic).trans
    ((glSympRingEquiv 2 (ZMod.ringEquivOfPrime K Nat.prime_two hK)).symm.trans spTwoEquivPerm)

theorem alt57_sp4 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoAlt57Image ↥(StatedSp 2 K) := by
  obtain ⟨n, hn⟩ := hK
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have : Nontrivial K := inferInstance
      have := Fintype.one_lt_card (α := K)
      omega
    · exact h0
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hcard
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn' : n = 1 := by omega
    have hK2 : Fintype.card K = 2 := by rw [hcard, hn']; norm_num
    exact noAlt57Image_of_mulEquiv (spEquivPerm K hK2) noAlt57Image_perm_six
  · have h4 : 4 ≤ Nat.card K := by
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have hbij : Function.Bijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K) :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    have hsimple' : IsSimpleGroup ↥(StatedSp 2 K) :=
      (MulEquiv.ofBijective _ hbij).isSimpleGroup
    have hdvd : 256 ∣ Nat.card ↥(StatedSp 2 K) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2]
      have h22 : 4 ∣ Nat.card K := by
        rw [hn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ n := pow_dvd_pow 2 h2
      have : 4 ^ 4 ∣ Nat.card K ^ (2 ^ 2) := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact pow_dvd_pow_of_dvd h22 4
      exact (show (256 : ℕ) = 4 ^ 4 by norm_num) ▸ this.trans (dvd_mul_right _ _)
    exact noAlt57Image_of_simple (by omega) (by omega)

end CFSG.QuasithinUnique.Bridge.Alt57Model

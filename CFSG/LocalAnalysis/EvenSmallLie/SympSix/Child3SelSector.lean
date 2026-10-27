module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrdersData
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs

public section

namespace CFSG.EvenSmallLie.Child3

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem statedClassicalModel_of_lieModel {T : Type} [Group T] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (hm : LieModel T t n p f) : StatedClassicalModel T t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel hm ht

theorem sector_of_sectorTuple {T : Type} [Group T] {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hs : sectorTuple t n p f = true) (hm : LieModel T t n p f) : Sector T := by
  cases t
  case PSL =>
    have hcl := statedClassicalModel_of_lieModel (by decide) hm
    obtain ⟨-, hf, hn, -⟩ := hcl.1
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨K, hK, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
      exact Or.inl ⟨n, f, hn, hf, K, hK, hcard, ⟨e⟩⟩
    · simp only [sectorTuple, Bool.or_eq_true, beq_iff_eq] at hs
      obtain rfl := hs.resolve_left hp2
      exact Or.inr (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hm⟩)
  case PSU =>
    simp only [sectorTuple, beq_iff_eq] at hs
    subst hs
    obtain ⟨-, hf, hn, -⟩ := (statedClassicalModel_of_lieModel (by decide) hm).1
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, f, hn, hf, hm⟩)))
  case PSp =>
    simp only [sectorTuple, beq_iff_eq] at hs
    subst hs
    obtain ⟨-, hf, hn, -⟩ := (statedClassicalModel_of_lieModel (by decide) hm).1
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, f, hn, hf, hm⟩))))
  case POmegaOdd =>
    simp only [sectorTuple, beq_iff_eq] at hs
    exact absurd hs (statedClassicalModel_of_lieModel (by decide) hm).1.2.2.2
  case G2 =>
    simp only [sectorTuple, decide_eq_true_eq] at hs
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd h.1.2.2.2 (by omega)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  case twistedB2 =>
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, h⟩))
  case twistedG2 =>
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨rfl, ht, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, f, Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩))⟩)))))
    · exact absurd ht (by decide)
  all_goals simp [sectorTuple] at hs

theorem sector_of_alternating {T : Type} [Group T]
    (h : ∃ n : ℕ, 5 ≤ n ∧ Nonempty (T ≃* alternatingGroup (Fin n))) : Sector T :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

open scoped IsMulCommutative

theorem card_mulAut_eq_card_GL {C : Type} [Group C] [Finite C] [CFSG.IsElementaryAbelian 2 C]
    {n : ℕ} (hC : Nat.card C = 2 ^ n) :
    Nat.card (MulAut C) = Nat.card (GL (Fin n) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive C) := CFSG.IsElementaryAbelian.isVectorSpace 2
  let e₁ : MulAut C ≃ (Additive C ≃ₗ[ZMod 2] Additive C) :=
    { toFun := fun a => (MulEquiv.toAdditive a).toLinearEquiv fun c x =>
        ZMod.map_smul (MulEquiv.toAdditive a).toAddMonoidHom c x
      invFun := fun g => MulEquiv.toAdditive.symm g.toAddEquiv
      left_inv := fun a => by ext; rfl
      right_inv := fun g => by ext; rfl }
  have hfin : Module.finrank (ZMod 2) (Additive C) = n := by
    have h := FiniteField.pow_finrank_eq_natCard 2 (Additive C)
    rw [show Nat.card (Additive C) = Nat.card C from rfl, hC] at h
    exact Nat.pow_right_injective le_rfl h
  have : FiniteDimensional (ZMod 2) (Additive C) := Module.Finite.of_finite
  let ℓ : Additive C ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_fin_fun])
  let e₂ : (Additive C ≃ₗ[ZMod 2] Additive C) ≃
      ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun g => (ℓ.symm.trans g).trans ℓ
      invFun := fun g => (ℓ.trans g).trans ℓ.symm
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }
  let e₃ : GL (Fin n) (ZMod 2) ≃* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  exact Nat.card_congr ((e₁.trans e₂).trans e₃.toEquiv.symm)

end CFSG.EvenSmallLie.Child3

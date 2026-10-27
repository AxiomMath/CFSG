module

public import CFSG.ClassicalInvolution.Q3.Q3T6FaLin
public import CFSG.ClassicalInvolution.Q3.Q3T6FaUni
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.ClassicalInvolution.AschTight.S19KFL
public import CFSG.ClassicalInvolution.AschTight.S19KFG2
public import CFSG.ClassicalInvolution.AschTight.S19TBr2
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Cards

private theorem card_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

private theorem card_gf9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
  rw [GaloisField.card 3 (2 * 1) (by norm_num)]
  norm_num

end Cards

section Facts

theorem factFL3 :
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ),
        ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → Nonempty (Ih8Model 3 1 Ω t k e') →
        ∀ L ∈ Ω, ∀ φ : MulAut E,
          (∃ (ι : ↥L ≃* SL(2, GaloisField 3 1))
              (g : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 3 1)),
            ∀ x : ↥L,
              ((ι.symm (AscL62.semilinHom g (RingEquiv.refl _) (ι x)) : ↥L) : E) = φ x) →
          ((∀ c ∈ Subgroup.centralizer (L : Set E), φ c = c) ∨
              (∀ c ∈ Subgroup.centralizer (L : Set E), φ c = c⁻¹)) ∧
            (φ * φ = 1 → (∃ c ∈ Subgroup.centralizer (L : Set E), φ c = c ∧ c * c ≠ 1) →
              ∃ y : E, φ = MulAut.conj y) := by
  intro E _ _ _ Ω t k e' ht hM L hL φ hφ
  obtain ⟨M⟩ := hM
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain rfl : e' = 1 := M.exp_eq_f hD4
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨θ, hθ, hker, rfl⟩ := S19K.exists_theta_psl M hL
    exact flLin_three card_gf3 (Q3W.linearAutClassification3 (by norm_num)) θ hθ hker φ hφ
  · obtain ⟨θ, hθ, hker, rfl⟩ := S19K.exists_theta_psu (by norm_num) M hL
    exact flUni_three card_gf9 (by norm_num) (by norm_num) (card_gf3.trans (pow_one 3).symm) θ hθ
      hker φ hφ

theorem exists_conj_of_fixes_three {E : Type} [Group E] [Finite E] [IsSimpleGroup E]
    {Ω : Set (Subgroup E)} {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (ht : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) (M : Ih8Model 3 1 Ω t k e) {L : Subgroup E}
    (hL : L ∈ Ω) (φ : MulAut E) (hφ2 : φ * φ = 1) (hφL : L.map φ.toMonoidHom = L)
    (hc : ∃ c ∈ Subgroup.centralizer (L : Set E), φ c = c ∧ c * c ≠ 1) :
    ∃ y : E, φ = MulAut.conj y := by
  obtain ⟨ι⟩ := S19T.nonempty_equiv_sl2_of_mem (by norm_num : (3 : ℕ) ≠ 2) M ht hL
  let φL : ↥L ≃* ↥L := (φ.subgroupMap L).trans (MulEquiv.subgroupCongr hφL)
  have hφL' : ∀ x : ↥L, ((φL x : ↥L) : E) = φ x := fun _ => rfl
  let β : MulAut SL(2, GaloisField 3 1) := (ι.symm.trans φL).trans ι
  have hβ : ∀ b, β b = ι (φL (ι.symm b)) := fun _ => rfl
  obtain ⟨G, hG⟩ := exists_eq_semilinHom_three card_gf3 β
  have hyp : ∀ x : ↥L,
      ((ι.symm (AscL62.semilinHom G (RingEquiv.refl _) (ι x)) : ↥L) : E) = φ x := by
    intro x
    rw [← hG, hβ, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, hφL']
  exact (factFL3 E Ω t k e ht ⟨M⟩ L hL φ ⟨ι, G, hyp⟩).2 hφ2 hc

end Facts

end CFSG.ClassicalInvolution.Q3.Q3T6

module

public import CFSG.ClassicalInvolution.Q3.TL4LieZ2M11Gen
public import CFSG.ClassicalInvolution.Q3.TL4LieZ2Ck
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Exit
public import Certificates.Certificate55123

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LieZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.Sporadic.Mathieu CFSG.GH74.KGroups CFSG.ClassicalInvolution.Q3.TA3.Check

theorem linkZ2Model_m11 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hsec : LieLinkSection Φ) (hshape : SecIdQ8Shape CompData.m11 Φ) : LinkZ2Model X Φ := by
  obtain ⟨ψ, hψ, hker, -⟩ := hshape
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (le_of_eq Q3W.center_m11_eq_bot)
  let e : X ≃* ↥NativeSporadic.M11 := (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).symm
  have : IsSimpleGroup ↥NativeSporadic.M11 := Q3.isSimpleGroup_m11_kernel
  have hs : IsSimpleGroup X := e.isSimpleGroup
  have hab : m11a * m11b ≠ m11b * m11a := by decide +kernel
  have hnab : ∃ a b : X, a * b ≠ b * a :=
    ⟨e.symm m11a, e.symm m11b, fun h => hab (by simpa using congrArg e h)⟩
  have hF : genFittingFStar X = ⊤ :=
    ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (f := (eF.trans e).toMonoidHom)
      (eF.trans e).injective, show (Subgroup.center ↥(genFittingFStar X)).map
        (eF.trans e).toMonoidHom = Subgroup.center ↥NativeSporadic.M11 from
          Subgroup.map_center_eq (eF.trans e), Q3W.center_m11_eq_bot]
  have hα : AutAlphaPairs ↥(genFittingFStar X) :=
    autAlphaPairs_of_model165Aut model165Aut_proved
      (Or.inl ⟨eF.isSimpleGroup, Or.inr ⟨eF.trans e⟩⟩) hZ
  obtain ⟨Mo, hMP, hMA⟩ := M11.autModel (K := X) ⟨e⟩
  have h163 := concl163_of_autModel Mo (LP := elemsT M11.Q) (LA := elemsT M11.Q)
    (reps := pickReps (elemsT M11.Q)) (fun g => by rw [hMP]; exact mem_elemsT _ M11.Q_ok g)
    (fun g hg => (mem_elemsT _ M11.Q_ok g).2 (hMA ▸ hg)) (hMP.le.trans hMA.ge)
    Certificates.certificate55123.2 hsec.1
  have hinv : ∀ w : ↥NativeSporadic.M11, orderOf w = 2 → w * w = 1 ∧ w ≠ 1 := fun w hw =>
    ⟨by rw [← sq, ← hw, pow_orderOf_eq_one], fun h => by rw [h, orderOf_one] at hw; omega⟩
  refine Z2Exit.linkZ2Model_of_mulEquiv hs hnab e hα (fun a b ha hb => ?_)
    (fun a b ha hb hab hne => sup_centralizer_eq_top_m11 ha hb hab hne) h163
  exact Q3T8.Asc77.exists_conj_of_involutions_m11 (hinv a ha).1 (hinv a ha).2 (hinv b hb).1
    (hinv b hb).2

end CFSG.ClassicalInvolution.Q3.TL4.LieZ2

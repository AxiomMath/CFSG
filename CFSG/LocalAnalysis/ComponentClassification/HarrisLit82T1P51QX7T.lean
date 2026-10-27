module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CentData
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXInv

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {p : ℕ} [Fact p.Prime]

theorem eq_rootDiagUnit_of_commute_orbitGroup_two
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) (hq : 3 ≤ D.q)
    (hχ : D.χ = signMaskChar .E7 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    [Subsingleton (KernelComponent D.χ)] {z : ModGL .E7 k} (hzG : z ∈ adjointGroup .E7 k)
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) :
    ∃ b : Fin (Tag.rank .E7) → kˣ, z = rootDiagUnit .E7 b ∧
      ∀ j : Fin 7, j ≠ 1 → b (CatLeafProof.e7Node j) = 1 := by
  have hcard := TwE7.orbitCard_of_e7Word D (Or.inl rfl) hχ hθ
  have hΔ : D.simpleRootsJ = Set.range e7A7Root := by
    rw [TwE7.simpleRootsJ_eq_simpleUnion, hχ, simpleUnion_e7_two]
  have hmem : ∀ β ∈ Set.range e7A7Root, ∀ A : SL2 k,
      z * rootSL2 .E7 k β A = rootSL2 .E7 k β A * z := fun β hβ A =>
    TwE7.commute_rootSL2_of_commute_orbitGroup D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ y ∈ TwE7.e7Gamma2, IsRoot .E7 y.1 := fun y hy => by
    obtain ⟨i, hi⟩ := TwE7.e7Gamma2_mem y hy
    rw [← hi]
    exact TwE7.e7A7Root_isRoot i
  have hT := TwE7.mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hzG
    TwE7.e7Gamma2 hroot (fun y hy s => hmem y.1 (TwE7.e7Gamma2_mem y hy) (HSL s)) 19
    (fun α hα => TwE7.e7Gamma2_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ β ∈ Set.range e7A7Root, rootChar b β = 1 := fun β hβ => by
    obtain ⟨i, rfl⟩ := hβ
    exact TwE7.rootChar_eq_one_of_commute (TwE7.e7A7Root_isRoot i) (hmem _ ⟨i, rfl⟩ (uSL 1))
  refine ⟨b, rfl, fun j hj => ?_⟩
  have hj' : ∃ i : Fin 7, e7A7Root i = Pi.single (CatLeafProof.e7Node j) 1 := by
    fin_cases j
    · exact ⟨6, by funext i; fin_cases i <;> rfl⟩
    · exact absurd rfl hj
    · exact ⟨5, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
    · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨i, hi⟩ := hj'
  have h := hχb _ ⟨i, hi⟩
  rwa [rootChar_piSingle_eq_coord] at h

theorem rootDiagUnit_eq_of_pair_e7
    {M : Type} [Field M] {b b' : Fin (Tag.rank .E7) → Mˣ}
    (hb : ∀ j : Fin 7, 2 ≤ j.val → b (CatLeafProof.e7Node j) = 1)
    (hb01 : b (CatLeafProof.e7Node 0) * b (CatLeafProof.e7Node 1) = 1)
    (hb' : ∀ j : Fin 7, 2 ≤ j.val → b' (CatLeafProof.e7Node j) = 1)
    (hb01' : b' (CatLeafProof.e7Node 0) * b' (CatLeafProof.e7Node 1) = 1)
    (h2 : rootDiagUnit .E7 b * rootDiagUnit .E7 b = 1)
    (h2' : rootDiagUnit .E7 b' * rootDiagUnit .E7 b' = 1) (h1 : rootDiagUnit .E7 b ≠ 1)
    (h1' : rootDiagUnit .E7 b' ≠ 1) : rootDiagUnit .E7 b = rootDiagUnit .E7 b' := by
  classical
  have key : ∀ m : Fin (Tag.rank .E7) → Mˣ,
      (∀ j : Fin 7, 2 ≤ j.val → m (CatLeafProof.e7Node j) = 1) →
      m (CatLeafProof.e7Node 0) * m (CatLeafProof.e7Node 1) = 1 →
      rootDiagUnit .E7 m * rootDiagUnit .E7 m = 1 → rootDiagUnit .E7 m ≠ 1 →
        ∀ j : Fin 7, m (CatLeafProof.e7Node j) = if j.val < 2 then -1 else 1 := by
    intro m hm hm01 hm2 hm1
    have hmm : m * m = 1 := eq_one_of_rootDiagUnit_eq_one (by rw [rootDiagUnit_mul]; exact hm2)
    have hm0 : m (CatLeafProof.e7Node 0) * m (CatLeafProof.e7Node 0) = 1 := congrFun hmm _
    have hm10 : m (CatLeafProof.e7Node 1) = m (CatLeafProof.e7Node 0) :=
      (eq_inv_of_mul_eq_one_right hm01).trans (eq_inv_of_mul_eq_one_left hm0).symm
    have hm0' : (m (CatLeafProof.e7Node 0) : M) * m (CatLeafProof.e7Node 0) = 1 := by
      have h3 := congrArg Units.val hm0
      simpa using h3
    rcases mul_self_eq_one_iff.1 hm0' with h | h
    · refine absurd ?_ hm1
      have hm' : m = 1 := funext fun j => by
        obtain ⟨j', rfl⟩ : ∃ j' : Fin 7, CatLeafProof.e7Node j' = j := ⟨j, rfl⟩
        by_cases hj : 2 ≤ j'.val
        · exact hm j' hj
        · have hj01 : j' = 0 ∨ j' = 1 := by omega
          rcases hj01 with rfl | rfl
          · exact Units.ext h
          · rw [hm10]
            exact Units.ext h
      rw [hm', rootDiagUnit_one]
    · intro j
      by_cases hj : 2 ≤ j.val
      · simp only [show ¬ (j.val < 2) by omega, ↓reduceIte]
        exact hm j hj
      · simp only [show j.val < 2 by omega, ↓reduceIte]
        have hj01 : j = 0 ∨ j = 1 := by omega
        rcases hj01 with rfl | rfl
        · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
        · rw [hm10]
          exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have e := key b hb hb01 h2 h1
  have e' := key b' hb' hb01' h2' h1'
  congr 1
  funext j
  obtain ⟨j', rfl⟩ : ∃ j' : Fin 7, CatLeafProof.e7Node j' = j := ⟨j, rfl⟩
  rw [e j', e' j']

end CFSG.ComponentClassification.HarrisLit.T1.P51Q

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHeThird
public import CFSG.RankThree.PartOne.K133.Count

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeNT

variable {X : Type} [Group X] [Finite X]

theorem exists_eight_of_pair (hIC : L34InvolutionCentralizerFact) {L : Subgroup X}
    (hset : HeldEndSetting X L) {a u : X} {M : Subgroup X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) {w : X}
    (hw2 : orderOf w = 2) (hMw : M ≤ centralizer ({w} : Set X)) :
    ∃ B : Subgroup X, B ≤ M ∧ IsElemTwo B ∧ Nat.card B = 8 ∧ wGroup B = ⊥ ∧
      ∃ V : Subgroup X, V ≤ B ∧ Nat.card V = 4 ∧
        V ≤ (Open.fusionZStar ↥M).map M.subtype := by
  obtain ⟨hHS, -, -, -, -⟩ := id hset
  obtain ⟨-, -, -, -, hLB, -, -⟩ := id hHS
  obtain ⟨-, -, -, hMq, -⟩ := diag_data ha hLa hu hMu hMp hne hfix hc
  obtain ⟨htype, z₁, hz₁, z₂, hz₂, hs₁, hs₂, hn₁, hn₂, hz, hcz⟩ :=
    HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  have hMperf : ⁅M, M⁆ = M := GSThmB.commutator_eq_self_of_isPComponent hMu hMp
  obtain ⟨r, hrM, hr2, -, hrZ, -⟩ := hIC X M 1 hMperf htype (mul_one 1) (one_mem _)
  have hOM : pPrimeCore 2 ↥M ≤ center ↥M := fun y hy => mem_center_iff.mpr fun g =>
    Subtype.ext (hc _ (mem_map_of_mem _ hy) g g.2).symm
  have hZM : Open.fusionZStar ↥M = center ↥M :=
    GrS5.fusionZStar_eq_center_of_le hMq.1.commutator_eq_top hOM
  have hzC : ∀ z ∈ (Open.fusionZStar ↥M).map M.subtype, ∀ m ∈ M, z * m = m * z := by
    rw [hZM]
    rintro _ ⟨y, hy, rfl⟩ m hm
    exact (congrArg Subtype.val (mem_center_iff.mp hy ⟨m, hm⟩)).symm
  have hz₁M : z₁ ∈ M := map_subtype_le _ hz₁
  have hz₂M : z₂ ∈ M := map_subtype_le _ hz₂
  set V := zpowers z₁ ⊔ zpowers z₂ with hVdef
  set B := V ⊔ zpowers r with hBdef
  have hVZ : V ≤ (Open.fusionZStar ↥M).map M.subtype :=
    sup_le (zpowers_le.mpr hz₁) (zpowers_le.mpr hz₂)
  have hVM : V ≤ M := hVZ.trans (map_subtype_le _)
  have hBM : B ≤ M := sup_le hVM (zpowers_le.mpr hrM)
  have hVe : IsElemTwo V := (isElemTwo_zpowers hs₁).sup (isElemTwo_zpowers hs₂) (by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute z₁ z₂ from hcz) i j).eq)
  have hBe : IsElemTwo B := hVe.sup (isElemTwo_zpowers hr2) (by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x r from hzC x (hVZ hx) r hrM) j).eq)
  have hz₁2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs₁) hn₁
  have hz₂2 : orderOf z₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs₂) hn₂
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hrZ (one_mem _)
  have hr2' : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hz₂n : z₂ ∉ zpowers z₁ := by
    rw [LocalB.mem_zpowers_iff_of_involution z₁ z₂ hz₁2]
    rintro (h | h)
    · exact hn₂ h
    · exact hz h.symm
  have hV4 : Nat.card V = 4 := by
    rw [hVdef, RankThree.PartOne.K133.card_sup_zpowers Nat.prime_two hz₂2 (fun y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute z₁ z₂ from hcz) i).eq) hz₂n,
      Nat.card_zpowers, hz₁2]
  have hB8 : Nat.card B = 8 := by
    rw [hBdef, RankThree.PartOne.K133.card_sup_zpowers Nat.prime_two hr2'
      (fun y hy => hzC y (hVZ hy) r hrM) (fun h => hrZ (hVZ h)), hV4]
  obtain ⟨E, -, hEM, hEe, hE8, hWE⟩ :=
    HeKMU.exists_elem_eight_wGroup hset ha hLa hLc hu hMu hMp hne hfix hc hw2 hMw
  have hGW : GWTwoBalanced X := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hWB : wGroup B = ⊥ := by
    rw [wGroup_eq_of_commute hGW (hBe.isAbelianTwoOfRank (by rw [hB8]))
      (hEe.isAbelianTwoOfRank hE8) (fun x hx y hy => (hEM y hy x (hBM hx)).symm), hWE]
  exact ⟨B, hBM, hBe, hB8, hWB, V, le_sup_left, hV4, hVZ⟩

end HeNT

end CFSG.ComponentClassification.GrSLit

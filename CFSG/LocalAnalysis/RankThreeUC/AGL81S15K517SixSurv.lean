module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixFam
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixLeviK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixSL3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LocalAnalysis.RankThreeUC.S15.KFactsPair
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.Assembly.LowTwoRank

section Generic

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L}

theorem exists_class_of_two_bad (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (hbq : BorelQuotient D n H π M) (hdiv : D.divisible = ∅)
    (hodd : ∀ i, OddNode (rankOne D.rootGroup i) 3) (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1) {a b c : Fin D.rank}
    (hac : BadPair D a c) (hbc : BadPair D b c) :
    ∃ π' : K →* ↥L ⧸ Subgroup.center ↥L, BorelQuotient D n H π' M ∧
      (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
        (posUnipotent D).map π' ∧
      ∃ A : Subgroup W, (A = A₁ ∨ A = A₂) ∧ NodeIn (D := D) L A π' a ∧ NodeIn (D := D) L A π' b ∧
        ¬ NodeIn (D := D) L A π' c := by
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS hbq
  have hcl : ∀ i, NodeIn (D := D) L A₁ π' i ∨ NodeIn (D := D) L A₂ π' i := fun i =>
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.cover_of_borelQuotient hS hcov hπ' hT i
  have key : ∀ {A : Subgroup W}, A ≤ L → CFSG.Open.pRank 3 A ≤ 1 → ∀ {i j : Fin D.rank},
      BadPair D i j → NodeIn (D := D) L A π' i → ¬ NodeIn (D := D) L A π' j := by
    intro A hA hr i j hb hi hj
    have := two_le_pRank_of_badPair hπ' hdiv hodd hA hb hi hj
    omega
  refine ⟨π', hπ', hT, ?_⟩
  by_cases hc1 : NodeIn (D := D) L A₁ π' c
  · have ha : ¬ NodeIn (D := D) L A₁ π' a := fun h => key hA₁ h₁ hac h hc1
    have hb : ¬ NodeIn (D := D) L A₁ π' b := fun h => key hA₁ h₁ hbc h hc1
    have ha2 := (hcl a).resolve_left ha
    have hb2 := (hcl b).resolve_left hb
    exact ⟨A₂, Or.inr rfl, ha2, hb2, fun h => key hA₂ h₂ hac ha2 h⟩
  · have hc2 := (hcl c).resolve_left hc1
    have ha : ¬ NodeIn (D := D) L A₂ π' a := fun h => key hA₂ h₂ hac h hc2
    have hb : ¬ NodeIn (D := D) L A₂ π' b := fun h => key hA₂ h₂ hbc h hc2
    have ha1 := (hcl a).resolve_right ha
    have hb1 := (hcl b).resolve_right hb
    exact ⟨A₁, Or.inl rfl, ha1, hb1, hc1⟩

theorem leviM_nonabelian_of_oddNode {J : Set (Fin D.rank)} {i : Fin D.rank} (hi : i ∈ J)
    (hodd : OddNode (rankOne D.rootGroup i) 3) :
    ¬ IsMulCommutative ↥(leviM D J) ∧ ¬ IsPGroup 2 ↥(leviM D J) := by
  obtain ⟨w, hw, m, hm, hw3, hw1, hmw⟩ := hodd
  have hwM : w ∈ leviM D J := rankOne_le_leviM hi hw
  have hmM : m ∈ leviM D J := rankOne_le_leviM hi hm
  refine ⟨fun hc => ?_, fun h2 => ?_⟩
  · refine not_mem_center_of_inverted (p := 3) (by decide) (w := (⟨w, hwM⟩ : ↥(leviM D J)))
      (m := ⟨m, hmM⟩) (Subtype.ext hw3) (fun h => hw1 (congrArg Subtype.val h))
      (Subtype.ext hmw) ?_
    rw [Subgroup.mem_center_iff]
    intro g
    exact hc.is_comm.comm g _
  · obtain ⟨k, hk⟩ := h2 ⟨w, hwM⟩
    have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    have hcop : Nat.Coprime (2 ^ k) 3 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
    exact hw1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2))

theorem hasLThreeCore_of_nodes {A : Subgroup W} (hA : A ≤ L) (hSA : S₀ ≤ A)
    (hZ : Subgroup.center ↥L = ⊥) (hbq : BorelQuotient D n H π M)
    (hT : (S₀.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) =
      (posUnipotent D).map π)
    {a b c : Fin D.rank} (hall : ∀ i, i = a ∨ i = b ∨ i = c) (ha : NodeIn (D := D) L A π a)
    (hb : NodeIn (D := D) L A π b) (hc : ¬ NodeIn (D := D) L A π c) (hac : a ≠ c)
    (hodd : OddNode (rankOne D.rootGroup a) 3) (hLevi : IsLThreeOdd ↥(leviM D {i | i ≠ c})) :
    HasLThreeCore A := by
  classical
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  set Ā : Subgroup (↥L ⧸ Subgroup.center ↥L) := (A.subgroupOf L).map q with hĀ
  set Xt : Subgroup K := Ā.comap π with hXt
  have hU : posUnipotent D ≤ Xt := by
    intro x hx
    have h1 : π x ∈ (posUnipotent D).map π := ⟨x, hx, rfl⟩
    rw [← hT] at h1
    exact Subgroup.map_mono (show S₀.subgroupOf L ≤ A.subgroupOf L from fun y hy => hSA hy) h1
  have hrank : ∀ i, rankOne D.rootGroup i ≤ Xt ↔ NodeIn (D := D) L A π i := fun i =>
    (Subgroup.map_le_iff_le_comap).symm
  have hJ : {i | rankOne D.rootGroup i ≤ Xt} = {i | i ≠ c} := by
    ext i
    simp only [Set.mem_setOf_eq, hrank]
    constructor
    · rintro h rfl
      exact hc h
    · intro hi
      rcases hall i with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact absurd rfl hi
  have hP : Xt ≤ parJ D H {i | i ≠ c} := by
    have := le_parJ_of_posUnipotent_le hbq.ct hbq.extras hU
    rwa [hJ] at this
  have hUJ : unipJ D {i | i ≠ c} ≤ Xt := by
    refine sup_le hU (iSup₂_le fun i hi => ?_)
    have : i ∈ {i | rankOne D.rootGroup i ≤ Xt} := by rw [hJ]; exact hi
    exact this
  have hmap : Xt.map π = Ā := Subgroup.map_comap_eq_self_of_surjective hbq.surj Ā
  have hMs : IsSimpleGroup ↥(leviM D {i | i ≠ c}) :=
    R1511C.isSimpleGroup_of_isLThreeTwoPow (R1511C.isLThreeTwoPow_of_isLThreeOdd hLevi)
  obtain ⟨hMnc, hM2⟩ := leviM_nonabelian_of_oddNode (J := {i | i ≠ c}) hac hodd
  obtain ⟨e⟩ := exists_mulEquiv_leviM hbq hUJ hP π (fun x hx => hbq.ker_central x hx) hmap hMs hMnc
    hM2
  have h1 : HasLThreeCore Ā := R1511C.isLThreeOdd_of_equiv e hLevi
  have hinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, hq, QuotientGroup.ker_mk', hZ]
  let eA : ↥A ≃* ↥Ā :=
    (Subgroup.subgroupOfEquivOfLe hA).symm.trans (Subgroup.equivMapOfInjective _ q hinj)
  exact R1511C.hasLThreeCore_of_equiv eA h1

end Generic


section Families

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}

section Sp

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem hasLThreeCore_sp_three (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L) (hS₁ : S₀ ≤ A₁) (hS₂ : S₀ ≤ A₂)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1) {k : ℕ}
    (hk : Nat.card F = 2 ^ k) (hkodd : Odd k) (hZ : Subgroup.center ↥L = ⊥)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedSp 3 F)) :
    HasLThreeCore A₁ ∨ HasLThreeCore A₂ := by
  have hbq := borelQuotient_sp e
  have hodd : ∀ i : Fin (Symplectic.rootDatum 3 F).rank,
      OddNode (rankOne (Symplectic.rootDatum 3 F).rootGroup i) 3 := fun i => oddNode_sp_three 3 i
  have hac : BadPair (Symplectic.rootDatum 3 F) (0 : Fin 3) (2 : Fin 3) := by
    show BadPairMat (Symplectic.cartanC 3) 0 2
    decide +kernel
  have hbc : BadPair (Symplectic.rootDatum 3 F) (1 : Fin 3) (2 : Fin 3) := by
    show BadPairMat (Symplectic.cartanC 3) 1 2
    decide +kernel
  obtain ⟨π', hπ', hT, A, hA, ha, hb, hc⟩ :=
    exists_class_of_two_bad hS hcov hbq rfl hodd hA₁ hA₂ h₁ h₂ hac hbc
  have hall : ∀ i : Fin (Symplectic.rootDatum 3 F).rank,
      i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
    intro i
    have h3 : i.val < 3 := i.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have hLevi : IsLThreeOdd ↥(leviM (Symplectic.rootDatum 3 F) {i : Fin 3 | i ≠ 2}) :=
    isLThreeOdd_of_equiv_sl3 hkodd hk rfl (leviM_sp_three_equiv (F := F)).some
  rcases hA with rfl | rfl
  · exact Or.inl (hasLThreeCore_of_nodes hA₁ hS₁ hZ hπ' hT hall ha hb hc hac.1 (hodd _) hLevi)
  · exact Or.inr (hasLThreeCore_of_nodes hA₂ hS₂ hZ hπ' hT hall ha hb hc hac.1 (hodd _) hLevi)

end Sp

section SpinMinus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt

set_option linter.unusedSectionVars false


variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem hasLThreeCore_spinMinus_four (hS : IsSylowTwoOf S₀ L) (hcov : CoveredByTwo L S₀ A₁ A₂)
    (hA₁ : A₁ ≤ L) (hA₂ : A₂ ≤ L) (hS₁ : S₀ ≤ A₁) (hS₂ : S₀ ≤ A₂)
    (h₁ : CFSG.Open.pRank 3 A₁ ≤ 1) (h₂ : CFSG.Open.pRank 3 A₂ ≤ 1) {k : ℕ}
    (hk : Nat.card F = 2 ^ k) (hkodd : Odd k) (hZ : Subgroup.center ↥L = ⊥)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* StatedProj (StatedOmega (StatedQuadMinus 4 F b c))) :
    HasLThreeCore A₁ ∨ HasLThreeCore A₂ := by
  haveI : Finite (spinGroup (quadMinus 4 F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hbq := borelQuotient_spinMinus hirr (le_refl 4) e
  have hodd : ∀ i : Fin (minusDatum 4 hirr).rank,
      OddNode (rankOne (minusDatum 4 hirr).rootGroup i) 3 := fun i =>
    oddNode_spinMinus_three (n := 4) hirr (le_refl 4) i
  have hac : BadPair (minusDatum 4 hirr) (0 : Fin 3) (2 : Fin 3) := by
    show BadPairMat (cartanB (4 - 1)) 0 2
    decide +kernel
  have hbc : BadPair (minusDatum 4 hirr) (1 : Fin 3) (2 : Fin 3) := by
    show BadPairMat (cartanB (4 - 1)) 1 2
    decide +kernel
  obtain ⟨π', hπ', hT, A, hA, ha, hb, hc⟩ :=
    exists_class_of_two_bad hS hcov hbq rfl hodd hA₁ hA₂ h₁ h₂ hac hbc
  have hall : ∀ i : Fin (minusDatum 4 hirr).rank,
      i = (0 : Fin 3) ∨ i = (1 : Fin 3) ∨ i = (2 : Fin 3) := by
    intro i
    have h3 : i.val < 3 := i.isLt
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have hLevi : IsLThreeOdd ↥(leviM (minusDatum 4 hirr)
      {i : Fin (minusDatum 4 hirr).rank | i ≠ ⟨2, show 2 < 4 - 1 by norm_num⟩}) :=
    isLThreeOdd_of_equiv_sl3 hkodd hk rfl (leviM_spinMinus_four_equiv hirr).some
  rcases hA with rfl | rfl
  · exact Or.inl (hasLThreeCore_of_nodes hA₁ hS₁ hZ hπ' hT hall ha hb hc hac.1 (hodd _) hLevi)
  · exact Or.inr (hasLThreeCore_of_nodes hA₂ hS₂ hZ hπ' hT hall ha hb hc hac.1 (hodd _) hLevi)

end SpinMinus

end Families

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

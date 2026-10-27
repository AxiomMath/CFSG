module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusFamily
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusModel

public section

namespace CFSG.GroupTheory

open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.AGLEmbeddingD2.ParabLevi

private theorem dAdj_of_cartanD_ne_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hc : cartanD n i j ≠ 0) : DAdj n i j := by
  have hcond : (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n) := by
    by_contra h
    apply hc
    unfold cartanD
    simp only [Matrix.of_apply]
    rw [if_neg hij, if_neg h]
  unfold DAdj
  omega

private theorem dAdj_of_nodeAdj {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    {C : Set (Fin n)} {i j : Fin n}
    (h : NodeAdj (plusDatum n F hn) C i j) : DAdj n i j := by
  obtain ⟨-, -, hadj⟩ := h
  have h' := (plusDatum n F hn).isFiniteType.diagramGraph_adj_iff.mp hadj
  exact dAdj_of_cartanD_ne_zero h'.1 h'.2

private theorem nodeAdj_last {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    {C : Set (Fin n)} {a b : Fin n}
    (h : Relation.ReflTransGen (NodeAdj (plusDatum n F hn) C) a b) (hab : a ≠ b) :
    ∃ d, d ∈ C ∧ d ≠ b ∧ cartanD n d b ≠ 0 := by
  revert hab
  induction h with
  | refl => intro hab; exact absurd rfl hab
  | tail _ hcb _ =>
    intro _
    obtain ⟨hd, -, hadj⟩ := hcb
    have h' := (plusDatum n F hn).isFiniteType.diagramGraph_adj_iff.mp hadj
    exact ⟨_, hd, h'.1, h'.2⟩

private theorem three_le_card_of_two_le_ncard {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ch : DBlk n ι) (h2 : 2 ≤ ch.nodes.ncard) : 3 ≤ Fintype.card ι := by
  classical
  by_contra hlt
  push Not at hlt
  have huniv : ∀ {a b : ι}, a ≠ b → ({a, b} : Finset ι) = Finset.univ := by
    intro a b hab
    have hcard2 : Fintype.card ι = 2 := by
      have hsub : ({a, b} : Finset ι) ⊆ (Finset.univ : Finset ι) := Finset.subset_univ _
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair_eq_two_iff.mpr hab, Finset.card_univ] at hle
      omega
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair_eq_two_iff.mpr hab, hcard2]
  have hle1 : ch.nodes.ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff]
    intro i j hi hj
    obtain ⟨u₁, v₁, huv₁, hd₁⟩ := ch.gen i hi
    obtain ⟨u₂, v₂, huv₂, hd₂⟩ := ch.gen j hj
    have hpair : (u₂ = u₁ ∧ v₂ = v₁) ∨ (u₂ = v₁ ∧ v₂ = u₁) := by
      have hsetu : u₂ ∈ ({u₁, v₁} : Finset ι) := by rw [huniv huv₁]; exact Finset.mem_univ u₂
      have hsetv : v₂ ∈ ({u₁, v₁} : Finset ι) := by rw [huniv huv₁]; exact Finset.mem_univ v₂
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsetu hsetv
      rcases hsetu with rfl | rfl <;> rcases hsetv with rfl | rfl
      · exact absurd rfl huv₂
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl huv₂
    have hsingle : (Pi.single j 1 : Fin n → ℤ) = Pi.single i 1 ∨
        (Pi.single j 1 : Fin n → ℤ) = - Pi.single i 1 := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (hd₂.symm.trans hd₁)
      · exact Or.inr (hd₂.symm.trans ((Dgamma_neg _ _).trans (congrArg Neg.neg hd₁)))
    rcases hsingle with hsingle | hsingle
    · by_contra hji
      have h := congrFun hsingle j
      simp only [Pi.single_apply] at h
      rw [if_neg (Ne.symm hji)] at h
      norm_num at h
    · by_contra hji
      have h := congrFun hsingle j
      simp only [Pi.single_apply, Pi.neg_apply] at h
      rw [if_neg (Ne.symm hji)] at h
      norm_num at h
  omega

private theorem exists_goodBlock_eq {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    {β : Type} [Fintype β] {C : Set (Fin n)} {J : β → Set (Fin n)}
    (hsub : ∀ b, J b ⊆ C) (hcov : ∀ i ∈ C, ∃ b, i ∈ J b)
    (hnonadj : ∀ b b', b ≠ b' → ∀ i ∈ J b, ∀ j ∈ J b', i ≠ j ∧ ¬ DAdj n i j)
    (hC : IsNodeConnected (plusDatum n F hn) C) : ∃ b, C = J b := by
  obtain ⟨i0, hi0⟩ := hC.1
  obtain ⟨b0, hb0⟩ := hcov i0 hi0
  refine ⟨b0, le_antisymm ?_ (hsub b0)⟩
  intro j hj
  have key : ∀ a ∈ J b0, ∀ k, NodeAdj (plusDatum n F hn) C a k → k ∈ J b0 := by
    intro a ha k hak
    have hkC : k ∈ C := hak.2.1
    obtain ⟨b, hb⟩ := hcov k hkC
    by_cases hbb : b = b0
    · rwa [hbb] at hb
    · exact absurd (dAdj_of_nodeAdj hn hak) (hnonadj b0 b (Ne.symm hbb) a ha k hb).2
  have : ∀ k, Relation.ReflTransGen (NodeAdj (plusDatum n F hn) C) i0 k → k ∈ J b0 := by
    intro k hk
    induction hk with
    | refl => exact hb0
    | tail _ hbc ih => exact key _ ih _ hbc
  exact this j (hC.2 i0 hi0 j hj)

private theorem finite_spinGroup_quadPlus' {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] :
    Finite (spinGroup (quadPlus n F)) := by
  have hfin : Finite ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) :=
    Finite.of_injective
      (fun e : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) =>
        (e : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F)))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  exact Finite.of_injective _
    (CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective (K := F))

private theorem isGomiChevTwo_of_center_eq_bot {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    (hC : CFSG.AGLEmbedding.IsClassicalTwoOrG2 (X ⧸ Subgroup.center X)) : IsGomiChevTwo X := by
  refine ⟨hq, ?_,
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isChevTwo_of_classicalTwoOrG2 hC⟩
  have hqO : CFSG.Open.IsQuasisimple X := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqO
      (CFSG.pCore 2 X) with hle | htop
  · rw [hZ] at hle
    exact le_bot_iff.mp hle
  · exfalso
    have : Nontrivial X := CFSG.ComponentClassification.Quasisimple.nontrivial hqO
    have : Group.IsPerfect X := hq.1
    have hpg : IsPGroup 2 (⊤ : Subgroup X) := htop ▸ (CFSG.pCore_isPGroup (p := 2) (G := X))
    have : Group.IsNilpotent X := (hpg.of_equiv Subgroup.topEquiv).isNilpotent
    exact Group.IsPerfect.not_isSolvable X inferInstance

private theorem gomiLeviFactor_of_trivialCenter {X M : Type} [Group X] [Finite X] [Group M]
    (e : X ≃* M) (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥)
    (hC : CFSG.AGLEmbedding.IsClassicalTwoOrG2 (X ⧸ Subgroup.center X)) : GomiLeviFactor M :=
  GomiLeviFactor.of_mulEquiv e (Or.inl (isGomiChevTwo_of_center_eq_bot hq hZ hC))

private theorem gomiLeviFactor_of_chevEquiv {X M : Type} [Group X] [Finite X] [Group M]
    (e : X ≃* M) (hq : CFSG.IsQuasisimple X) (hZ : Odd (Nat.card (Subgroup.center X)))
    (hC : CFSG.AGLEmbedding.IsClassicalTwoOrG2 (X ⧸ Subgroup.center X)) : GomiLeviFactor M :=
  GomiLeviFactor.of_mulEquiv e (Or.inl (IsGomiChevTwo.of_isQuasisimple hq hZ
    (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isChevTwo_of_classicalTwoOrG2 hC)))

private theorem gomiLeviFactor_of_isABlock {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) {C : Set (Fin n)} (hAB : IsABlock C) (h2 : 2 ≤ C.ncard)
    (hcert : ∀ k, 3 ≤ k → CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) F) ∧
      CFSG.AGLEmbedding.IsClassicalTwoOrG2 (Matrix.SpecialLinearGroup (Fin k) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin k) F))) :
    GomiLeviFactor ↥(leviM (plusDatum n F hn) C) := by
  obtain ⟨ι, _, _, ch, hch, _⟩ := hAB
  rw [← hch]
  have h3 : 3 ≤ Fintype.card ι := three_le_card_of_two_le_ncard ch (by rw [hch]; exact h2)
  refine gomiLeviFactor_of_chevEquiv
    ((slReindexEquiv (Fintype.equivFin ι)).symm.trans (chEquiv (F := F) hn ch)) ?_ ?_ ?_
  · exact (hcert (Fintype.card ι) h3).1
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup)
  · exact (hcert (Fintype.card ι) h3).2

private theorem gomiLeviFactor_of_blkNodes {n a k : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (h : a + k = n) (hk : 3 ≤ k)
    (hcert : CFSG.IsQuasisimple (spinGroup (quadPlus k F)) ∧
      CFSG.AGLEmbedding.IsClassicalTwoOrG2 (spinGroup (quadPlus k F) ⧸
        Subgroup.center (spinGroup (quadPlus k F)))) :
    GomiLeviFactor ↥(leviM (plusDatum n F hn) (blkNodes n a)) := by
  have : Finite (spinGroup (quadPlus k F)) := finite_spinGroup_quadPlus'
  refine gomiLeviFactor_of_trivialCenter (blkEquiv (F := F) h hn hk) hcert.1 ?_ hcert.2
  exact CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := k) (K := F)
    (by omega)

private theorem isABlock_of_goodFamily_three {F : Type} [Field F] {hn : 3 ≤ 3}
    {β : Type} [Fintype β] {C : Set (Fin 3)} {J : β → Set (Fin 3)}
    (hGood : GoodFamily 3 C J) (hC : IsNodeConnected (plusDatum 3 F hn) C)
    (hne : C ≠ Set.univ) : IsABlock C := by
  obtain ⟨hsub, hcov, hnonadj, hty⟩ := hGood
  obtain ⟨b, hbC⟩ := exists_goodBlock_eq (F := F) hn hsub hcov hnonadj hC
  rcases hty b with h | ⟨a, ha, hba⟩
  · rw [hbC]; exact h
  · exfalso
    have ha0 : a = 0 := by omega
    subst ha0
    have hJ : J b = Set.univ := by rw [hba]; ext x; simp [blkNodes]
    exact hne (hbC.trans hJ)

private theorem isABlock_of_isNodeConnected_three {F : Type} [Field F] {hn : 3 ≤ 3}
    {C : Set (Fin 3)} (hC : IsNodeConnected (plusDatum 3 F hn) C)
    (h2 : 2 ≤ C.ncard) (hne : C ≠ Set.univ) : IsABlock C := by
  have hcardC : C.ncard = 2 := by
    have hle : C.ncard ≤ 3 := by
      calc C.ncard ≤ (Set.univ : Set (Fin 3)).ncard := Set.ncard_le_ncard (Set.subset_univ C)
        _ = 3 := by simp
    by_contra hcon
    have h3 : C.ncard = 3 := by omega
    exact hne (Set.eq_of_subset_of_ncard_le (Set.subset_univ C)
      (by rw [h3, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]))
  by_cases h1 : (1 : Fin 3) ∈ C
  · have h2not : (2 : Fin 3) ∉ C := by
      intro h2C
      obtain ⟨d, hd, hdb, hcart⟩ := nodeAdj_last (F := F) hn
        (hC.2 (1 : Fin 3) h1 (2 : Fin 3) h2C) (by norm_num)
      have hCeq : C = ({1, 2} : Set (Fin 3)) := by
        symm
        refine Set.eq_of_subset_of_ncard_le ?_ ?_
        · intro x hx; rcases hx with rfl | rfl <;> assumption
        · simp [hcardC, Set.ncard_pair (by decide : (1 : Fin 3) ≠ 2)]
      rw [hCeq] at hd
      rcases hd with rfl | rfl
      · exact hcart (by decide)
      · exact absurd rfl hdb
    have hI : C ⊆ Set.range (frameId 2).ν := by
      intro x hx
      fin_cases x
      · exact ⟨0, by simp [frameId]⟩
      · exact ⟨1, by simp [frameId]⟩
      · exact absurd hx h2not
    obtain ⟨β, _, J, hGood⟩ := family_of_frame (frameId 2)
      (frameId_inj 2) (frameId_adj 2) C hI
    exact isABlock_of_goodFamily_three hGood hC hne
  · have hI : C ⊆ Set.range (frameTau 2 (by norm_num)).ν := by
      intro x hx
      fin_cases x
      · exact ⟨0, by simp [frameTau]⟩
      · exact absurd hx h1
      · exact ⟨1, by simp [frameTau]⟩
    obtain ⟨β, _, J, hGood⟩ := family_of_frame (frameTau 2 (by norm_num))
      (frameTau_inj 2 (by norm_num)) (frameTau_adj 2 (by norm_num)) C hI
    exact isABlock_of_goodFamily_three hGood hC hne

theorem gomiLeviFactorsSpinPlus_holds : GomiLeviFactorsSpinPlus := by
  intro n F _ _ _ hn C hC h2C hCne
  have hcertA : ∀ k, 3 ≤ k → CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) F) ∧
      CFSG.AGLEmbedding.IsClassicalTwoOrG2 (Matrix.SpecialLinearGroup (Fin k) F ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin k) F)) :=
    fun k hk => isChevComponent_sl (F := F) (Or.inl hk)
  have hcertD : ∀ k, 3 ≤ k → CFSG.IsQuasisimple (spinGroup (quadPlus k F)) ∧
      CFSG.AGLEmbedding.IsClassicalTwoOrG2 (spinGroup (quadPlus k F) ⧸
        Subgroup.center (spinGroup (quadPlus k F))) := by
    intro k hk
    by_cases hk4 : 4 ≤ k
    · exact isChevComponent_spinPlus (F := F) hk4
    · have hk3 : k = 3 := by omega
      subst hk3
      exact chev_spinPlus_three (F := F)
  by_cases hn4 : 4 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨β, _, J, hGood⟩ := comb m (by omega) C
    obtain ⟨hsub, hcov, hnonadj, hty⟩ := hGood
    obtain ⟨b, hbC⟩ := exists_goodBlock_eq hn hsub hcov hnonadj hC
    rw [hbC]
    rcases hty b with hAB | ⟨a, ha, hba⟩
    · exact gomiLeviFactor_of_isABlock hn hAB (by rw [← hbC]; exact h2C) hcertA
    · rw [hba]
      obtain ⟨k, hk⟩ : ∃ k, a + k = m + 1 := ⟨m + 1 - a, by omega⟩
      have hk3 : 3 ≤ k := by omega
      exact gomiLeviFactor_of_blkNodes hn hk hk3 (hcertD k hk3)
  · have hn3 : n = 3 := by omega
    subst hn3
    exact gomiLeviFactor_of_isABlock hn (isABlock_of_isNodeConnected_three hC h2C hCne)
      h2C hcertA

end CFSG.GroupTheory

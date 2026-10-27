module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualShared
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeLie
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section BlockClosure

variable {G : Type} [Group G] [Finite G]

theorem D1L2Data.le_blockClosure_of_three {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (hp3 : p = 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hB : BlockHasThree M (pCoreOf 2 H) L) :
    X ≤ blockClosure M (H ⊓ M) L :=
  h.ph3.toD1Escape.toTwoLocalPair.le_blockClosure_of_dichotomy hp3 h.normal_dichotomy hL hB

theorem stmtXNormalizesBlockThree : StmtXNormalizesBlockThree := by
  intro G _ _ p n _ P M H R X h hp3 L hL hB
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hT : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) ≤
      Subgroup.normalizer (barM M L : Set _) := by
    intro k hk z hz
    have hLk := hL.toIsTwoPrimeComponent.map_conj (hKM hk)
    by_cases he : barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L
    · rw [he] at hz
      exact Subgroup.le_normalizer hz
    · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLk.component
        hL.component he
      exact Subgroup.centralizer_le_normalizer _
        ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hz)
  have hXN := barM_le_of_le_preimage ((h.le_blockClosure_of_three hp3 hL hB).trans
    (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent hT))
  exact hL.toIsTwoPrimeComponent.le_normalizer hXN (h.le_R.trans h.ph3.le_M)

end BlockClosure

theorem stmtNormalizeBlocks : StmtNormalizeBlocks :=
  stmtNormalizeBlocks_of stmtXNormalizesBlockThree stmtComponentRank stmtBarPRankLift

section LayerCore

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem glbLayer_top_normal : (GLBLayer (⊤ : Subgroup Y)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hle : GLBLayer (⊤ : Subgroup Y) ≤
      (GLBLayer (⊤ : Subgroup Y)).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun L' hL' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g)
      L').mpr hL')
  simpa [MulAut.conj_apply] using hle hx

omit [Finite Y] in
theorem le_pCore_of_le_normal_comm {p : ℕ} {A Z : Subgroup Y} (hZn : Z.Normal)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hAZ : A ≤ Z) (hA : IsPGroup p A) :
    A ≤ CFSG.pCore p Y := by
  set W := Subgroup.normalClosure (A : Set Y) with hW
  have hWZ : W ≤ Z := Subgroup.normalClosure_le_normal hAZ
  have hWp : ∀ w ∈ W, ∃ k : ℕ, w ^ p ^ k = 1 := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
      refine ⟨k, ?_⟩
      rw [conj_pow]
      have : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      group
    | one => exact ⟨0, by simp⟩
    | mul x z hx hz ihx ihz =>
      obtain ⟨k₁, hk₁⟩ := ihx
      obtain ⟨k₂, hk₂⟩ := ihz
      refine ⟨k₁ + k₂, ?_⟩
      rw [Commute.mul_pow (hZ x (hWZ hx) z (hWZ hz)), pow_add, pow_mul, hk₁, one_pow,
        one_mul, mul_comm, pow_mul, hk₂, one_pow]
    | inv x hx ihx =>
      obtain ⟨k, hk⟩ := ihx
      exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
  have hWpg : IsPGroup p W := fun w => by
    obtain ⟨k, hk⟩ := hWp w w.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact Subgroup.subset_normalClosure.trans
    (le_sSup (s := {K : Subgroup Y | K.Normal ∧ IsPGroup p K}) ⟨inferInstance, hWpg⟩)

end LayerCore

section PCoreThree

variable {G : Type} [Group G] [Finite G]

theorem stmtLePCoreThree_of (hROne : StmtROne) (hB3 : StmtBlockThree)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : StmtLePCoreThree := by
  intro G _ _ p n _ P M H R X h hp3
  obtain ⟨L, hL⟩ := h.ph3.exists_weakSBlock h84 hD2
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hXE := h.le_blockClosure_of_three hp3 hL (hB3 h.ph3 hL)
  set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := GLBLayer ⊤ with hEdef
  have hXbarE : barM M X ≤ E := barM_le_of_le_preimage (hXE.trans
    (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent (fun k hk =>
      le_sSup (hL.toIsTwoPrimeComponent.map_conj (hKM hk)).component)))
  have hXcent : ∀ L' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L' ⊤ →
      barM M X ≤ Subgroup.centralizer (L' : Set _) := by
    intro L' hL'
    by_cases hex : ∃ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = L'
    · obtain ⟨k, hk, rfl⟩ := hex
      exact hROne h (Or.inl hp3) _ (hL.map_conj (hKM hk) (hKeq ▸ hk).2)
    · push Not at hex
      refine barM_le_of_le_preimage (hXE.trans
        (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent (fun k hk => ?_)))
      have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hL.toIsTwoPrimeComponent.map_conj (hKM hk)).component hL' (hex k hk)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  have hXC : barM M X ≤ Subgroup.centralizer (E : Set _) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun L' hL' => Subgroup.le_centralizer_iff.mp (hXcent L' hL')
  have hEn : E.Normal := glbLayer_top_normal
  have hZn : (E ⊓ Subgroup.centralizer (E : Set _)).Normal := inferInstance
  have hZ : ∀ a ∈ E ⊓ Subgroup.centralizer (E : Set _),
      ∀ b ∈ E ⊓ Subgroup.centralizer (E : Set _), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  have hXp : IsPGroup p (barM M X) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hxp : (x : G) ^ p = 1 := h.isElemAbelian.2 x (Subgroup.mem_subgroupOf.mp hx)
    have : x ^ p = 1 := Subtype.ext (by simpa using hxp)
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, this, map_one]
  exact le_pCore_of_le_normal_comm hZn hZ (le_inf hXbarE hXC) hXp

end PCoreThree

theorem stmtP3OfData_of (hLe : StmtLePCoreThree)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) : StmtP3OfData :=
  have hN := @stmtNormalSupOfLePCore
  fun h hp3 => hN h h84 hD2 (hLe h hp3)

theorem stmtP3OfData_of_inputs (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaB) (hT1 : StmtPPDElement) :
    StmtP3OfData :=
  stmtP3OfData_of (stmtLePCoreThree_of (stmtROne_of hB3 hLB hT1 stmtNormalizeBlocks h85 hD2)
    hB3 h84 hD2) h84 hD2

theorem lemmaP3LinTwo_of (hD : StmtL2Data) (h3 : StmtP3OfData) : StmtLemmaP3LinTwo := by
  intro G _ _ p _ P M H R Rbar hcfg hp3 K hK huniq _ hcent _ d hd e
  obtain ⟨n, hd⟩ := hd
  exact h3 (hD G p P M H R Rbar hcfg K hK huniq hcent n d hd e) hp3

theorem lemmaP3LinTwo_of_inputs (hD : StmtL2Data) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (hT1 : StmtPPDElement) : StmtLemmaP3LinTwo :=
  lemmaP3LinTwo_of hD (stmtP3OfData_of_inputs h84 h85 hD2 hB3 hLB hT1)

end CFSG.AGLEmbedding

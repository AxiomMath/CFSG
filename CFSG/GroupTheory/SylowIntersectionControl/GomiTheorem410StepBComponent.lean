module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBSetting
import CFSG.GroupTheory.AutOnPCoreQuotient
import CFSG.LocalAnalysis.UniquenessCase.UC22CmpX
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

omit [Finite Ω] in
private lemma gomiV_le_pCoreOf_bcomp (G : Subgroup Ω) : gomiV G ≤ pCoreOf 2 G := by
  rw [gomiV, omegaOneCenterOf, omegaOneOf]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact hx.1.1

private lemma oResidualTwo_eq_top_of_twoResidual_eq_self_bcomp {B : Subgroup Ω}
    (hB : twoResidual B = B) : oResidualTwo ↥B = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : Ω) ∈ twoResidual B := by rw [hB]; exact x.2
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.twoResidual_eq_map_oResidualTwo] at hx
  exact (Subgroup.mem_map_iff_mem B.subtype_injective).mp hx

omit [Finite Ω] in
private lemma inf_centralizer_le_pCoreOf_bcomp {B W : Subgroup Ω}
    (hBW : B ≤ normalizer (W : Set Ω)) (hNQ : B ⊓ centralizer (W : Set Ω) ≤ pCoreOf 2 G)
    (hQ2 : IsPGroup 2 (pCoreOf 2 G)) :
    B ⊓ centralizer (W : Set Ω) ≤ pCoreOf 2 B := by
  have hNC : normalizer (W : Set Ω) ≤ normalizer (centralizer (W : Set Ω) : Set Ω) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer (W : Set Ω))
  have hnorm : B ≤ normalizer ((B ⊓ centralizer (W : Set Ω)) : Set Ω) :=
    (le_inf Subgroup.le_normalizer (hBW.trans hNC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm (hQ2.to_le hNQ)

private lemma pCoreOf_le_inf_centralizer_bcomp {B W : Subgroup Ω} {M : Subgroup (MulAut ↥W)}
    (hBW : B ≤ normalizer (W : Set Ω)) (hBM : autOn B W = M) (hM2 : CFSG.pCore 2 ↥M = ⊥) :
    pCoreOf 2 B ≤ B ⊓ centralizer (W : Set Ω) := by
  have hbotM : pCoreOf 2 M = ⊥ := by
    unfold pCoreOf
    rw [hM2, Subgroup.map_bot]
  refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 B) ?_
  have hR2 : IsPGroup 2 (pCoreOf 2 B) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  have hauto2 : IsPGroup 2 (autOn (pCoreOf 2 B) W) :=
    CFSG.Quasithin.AutOn.isPGroup_autOn hR2
  have hautoM : autOn (pCoreOf 2 B) W ≤ M := by
    rw [← hBM]
    exact CFSG.Quasithin.AutOn.autOn_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 B)
  have hnormM : M ≤ normalizer (autOn (pCoreOf 2 B) W : Set (MulAut ↥W)) := by
    rw [← hBM]
    exact CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B)
  have hbot : autOn (pCoreOf 2 B) W = ⊥ :=
    eq_bot_iff.mpr ((CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      hautoM hnormM hauto2).trans hbotM.le)
  intro r hr
  have hmem : conjAct W ⟨r, hBW (CFSG.LieType.BorelTits.pCoreOf_le 2 B hr)⟩ ∈
      autOn (pCoreOf 2 B) W :=
    CFSG.Quasithin.AutOn.conjAct_mem_autOn _ hr
  rw [hbot, Subgroup.mem_bot] at hmem
  simpa using (CFSG.Quasithin.AutOn.conjAct_eq_one_iff
    (⟨r, hBW (CFSG.LieType.BorelTits.pCoreOf_le 2 B hr)⟩ :
      normalizer (W : Set Ω))).mp hmem

private lemma commutator_pCoreOf_eq_commutator_bcomp {G B W : Subgroup Ω}
    (hBLG : B ≤ G) (hBtop : oResidualTwo ↥B = ⊤)
    (hQBleW : ⁅pCoreOf 2 G, B⁆ ≤ W) (hWQ : W ≤ pCoreOf 2 G) :
    ⁅pCoreOf 2 G, B⁆ = ⁅W, B⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono hWQ le_rfl)
  have hJ : ∀ (N : Subgroup ↥B) [N.Normal], IsPGroup 2 (↥B ⧸ N) → N = ⊤ := by
    intro N hN hN2
    rw [eq_top_iff, ← hBtop]
    exact sInf_le ⟨hN, hN2⟩
  have hJP : B ≤ normalizer ((pCoreOf 2 G : Subgroup Ω) : Set Ω) :=
    hBLG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  calc ⁅pCoreOf 2 G, B⁆ = ⁅⁅pCoreOf 2 G, B⁆, B⁆ :=
        (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
          hJ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G) hJP).symm
    _ ≤ ⁅W, B⁆ := Subgroup.commutator_mono hQBleW le_rfl

structure IsGomi410bComponent (G W B : Subgroup Ω) (M : Subgroup (MulAut ↥W)) : Prop where
  twoComponent : IsGomiTwoComponent G B
  autOn_eq : autOn B W = M
  quotient_equiv : Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥M)
  commutator_pCoreOf_le : ⁅pCoreOf 2 G, B⁆ ≤ gomiV G
  commutator_gomiV_eq : ⁅gomiV G, B⁆ = ⁅W, B⁆
  le_normalizer : B ≤ normalizer (W : Set Ω)
  inf_centralizer_eq : B ⊓ centralizer (W : Set Ω) = pCoreOf 2 B
  commutator_eq : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆

theorem IsGomi410bSetting.isGomi410bComponent {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) {B : Subgroup Ω} (hBL : B ≤ L)
    (hBsub : (B.subgroupOf G).IsSubnormal) (hBres : twoResidual B = B)
    {M : Subgroup (MulAut ↥W)} (hBM : autOn B W = M) (hM2 : CFSG.pCore 2 ↥M = ⊥)
    (hMq : CFSG.IsQuasisimple ↥M ∨ ((Nat.card ↥M).Prime ∧ Odd (Nat.card ↥M))) :
    IsGomi410bComponent G W B M := by
  have hBLG : B ≤ G := hBL.trans hset.le
  have hLH : L ≤ H := by rw [hset.eq_sup]; exact le_sup_left.trans le_sup_left
  have hBW : B ≤ normalizer (W : Set Ω) := hBL.trans (hLH.trans hset.le_normalizer_W)
  have hBtop : oResidualTwo ↥B = ⊤ := oResidualTwo_eq_top_of_twoResidual_eq_self_bcomp hBres
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hWQ : W ≤ pCoreOf 2 G := hset.le_gomiV.trans (gomiV_le_pCoreOf_bcomp G)
  have hQBleW : ⁅pCoreOf 2 G, B⁆ ≤ W :=
    (Subgroup.commutator_mono le_rfl hBL).trans hset.commutator_le
  have hQW : ⁅pCoreOf 2 G, B⁆ = ⁅W, B⁆ :=
    commutator_pCoreOf_eq_commutator_bcomp hBLG hBtop hQBleW hWQ
  have hWBR : ⁅pCoreOf 2 B, B⁆ = ⁅W, B⁆ :=
    (commutator_pCoreOf_eq_of_isSubnormal hBLG hBsub hBtop).symm.trans hQW
  have hVB : ⁅gomiV G, B⁆ = ⁅W, B⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono hset.le_gomiV le_rfl)
    calc ⁅gomiV G, B⁆ ≤ ⁅pCoreOf 2 G, B⁆ :=
          Subgroup.commutator_mono (gomiV_le_pCoreOf_bcomp G) le_rfl
      _ = ⁅W, B⁆ := hQW
  have hNQ : B ⊓ centralizer (W : Set Ω) ≤ pCoreOf 2 G :=
    (inf_le_inf hBL le_rfl).trans hset.inf_centralizer_le
  have hker : B ⊓ centralizer (W : Set Ω) = pCoreOf 2 B :=
    le_antisymm (inf_centralizer_le_pCoreOf_bcomp hBW hNQ hQ2)
      (pCoreOf_le_inf_centralizer_bcomp hBW hBM hM2)
  obtain ⟨φ, _⟩ := exists_quotient_pCore_mulEquiv_autOn hBW hker
  let e : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥M := φ.trans (MulEquiv.subgroupCongr hBM)
  refine ⟨⟨hBLG, hBsub, hBtop, ?_⟩, hBM, ⟨e⟩, hQBleW.trans hset.le_gomiV,
    hVB, hBW, hker, hWBR⟩
  rcases hMq with hq | ⟨hp, ho⟩
  · exact Or.inl (CFSG.IsQuasisimple.of_mulEquiv e hq)
  · exact Or.inr ⟨by rw [Nat.card_congr e.toEquiv]; exact hp,
      by rw [Nat.card_congr e.toEquiv]; exact ho⟩

end CFSG.GroupTheory

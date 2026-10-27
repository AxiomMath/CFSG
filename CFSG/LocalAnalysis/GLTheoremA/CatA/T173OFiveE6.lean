module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Rank2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Toral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Weyl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three


private theorem exists_diagonal_model_famFive_E6 {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel}
    (hlab : GLAInLambda2 lab) (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      4 ≤ Nat.card F ∧ 3 ∣ Nat.card F - 1 ∧ Nat.card (Subgroup.center ↥S) ∣ 3 ∧
      ∃ M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F),
        ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
          a = rootDiagUnit Tag.E6 c := by
  classical
  obtain ⟨F, hFld, hFinF, hCharF, hFcard, hZ, ⟨M⟩⟩ :=
    exists_dmodel_E6 hcfg hlab htag h3 hmark
  letI : Field F := hFld
  letI : Finite F := hFinF
  letI : CharP F 2 := hCharF
  have hn2 : 2 ≤ lab.n := by
    by_cases h : lab.n < 2
    · have hn1 : lab.n = 1 := le_antisymm (Nat.lt_succ_iff.mp h) hlab.1
      rw [hn1] at h3
      norm_num at h3
    · omega
  have hq : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2
  have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact h3
  have hB6 := three_pow_six_le_card_B hcfg hq h3F M hZ
  have hcard := S172DModel.card_eq_mul_card_barB hcfg M
  have hbar5 : 3 ^ 5 ≤ Nat.card M.barB := by
    rw [hcard] at hB6
    have h729 : 3 ^ 6 = 3 * 3 ^ 5 := by norm_num
    rw [h729] at hB6
    exact Nat.le_of_mul_le_mul_left hB6 (by norm_num)
  have hEel : IsElemAbelian 3 M.barB := S172DModel.isElemAbelian_barB hcfg M
  have hEH : M.barB ≤ hatGroup Tag.E6 F := Subgroup.map_subtype_le _
  obtain ⟨g, hgH, hconj⟩ := exists_conj_rootDiag_of_le_hatGroup h3F hEel hEH hbar5
  have hgN : g ∈ Subgroup.normalizer (adjointGroup Tag.E6 F : Set (ModGL Tag.E6 F)) :=
    hatGroup_le_normalizer hgH
  obtain ⟨M', hbar, -, -⟩ := S172DModel.exists_conj M hgH hgN
  refine ⟨F, hFld, hFinF, hCharF, hq, h3F, hZ, M', ?_⟩
  intro a ha
  rw [hbar, Subgroup.mem_map] at ha
  obtain ⟨e, he, rfl⟩ := ha
  obtain ⟨c, hc3, hgc⟩ := hconj e he
  exact ⟨c, hc3, by simpa [MulAut.conj_apply] using hgc⟩

private theorem exists_rootCharKernel_famFive_E6 {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 3 S B N D K x) {F : Type}
    [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) (h3F : 3 ∣ Nat.card F - 1)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c) :
    ∃ (c : Fin Tag.E6.rank → Fˣ) (α : Fin Tag.E6.rank → ℤ),
      (∀ i, c i ^ 3 = 1) ∧ rootDiagUnit Tag.E6 c ≠ 1 ∧ IsRoot Tag.E6 α ∧
      rootSubgroup Tag.E6 F α ≤ M.piImg K := by
  classical
  obtain ⟨d, hdbar, hd1, -, -, hK, hcomp, hcent⟩ := S172DModel.exists_stdD hcfg M
  obtain ⟨c, hc3, hdc⟩ := hdiag d hdbar
  have hcd1 : rootDiagUnit Tag.E6 c ≠ 1 := by rw [← hdc]; exact hd1
  have hcomp' : IsComponentOf (stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c))
      (adjointGroup Tag.E6 F ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E6 c} : Set (ModGL Tag.E6 F))) := by
    rw [hdc] at hcomp
    exact hcomp
  have hcent' : M.barB ⊓ Subgroup.centralizer
      (stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c) : Set (ModGL Tag.E6 F)) =
      Subgroup.zpowers (rootDiagUnit Tag.E6 c) := by
    rw [hK, hdc] at hcent
    exact hcent
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) (p := 3) h3F
  have hA : e6TorusThree F ζ ≤ M.barB := e6TorusThree_le_barB hcfg hq M hZ hdiag hζ
  obtain ⟨α, hαker⟩ := rootCharKernel_nonempty_of_torusThree_le (F := F) hζ hA hcomp' hcent'
  have hU : rootSubgroup Tag.E6 F α ≤
      stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c) :=
    rootSubgroup_le_stdLayerD (F := F) hq hc3 hcd1 hαker
  refine ⟨c, α, hc3, hcd1, hαker.1, ?_⟩
  rw [hK, hdc]
  exact hU

private theorem weylElt_mem_normalizer_piImg_closureIn_famFive_E6 {Ω : Type} [Group Ω] [Finite Ω]
    {S B N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 3 S B N D K x) {F : Type}
    [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (M : S172DModel S B (adjointGroup Tag.E6 F) (hatGroup Tag.E6 F))
    (hZ : Nat.card (Subgroup.center ↥S) ∣ 3)
    (hdiag : ∀ a ∈ M.barB, ∃ c : Fin Tag.E6.rank → Fˣ, (∀ i, c i ^ 3 = 1) ∧
      a = rootDiagUnit Tag.E6 c) :
    ∀ i, weylElt Tag.E6 F i 1 ∈
      Subgroup.normalizer (M.piImg (closureIn K N) : Set (ModGL Tag.E6 F)) := by
  classical
  choose ψ hψ using fun i : Fin Tag.E6.rank => exists_rootSL2_lift (F := F) hq M hZ i
  have hE : ∀ i (g : Matrix.SpecialLinearGroup (Fin 2) F), (∃ γ : Fˣ, γ ^ 3 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(γ : F), ((γ⁻¹ : Fˣ) : F)]) →
      ((ψ i g : ↥S) : Ω) ∈ B := by
    intro i g hg
    exact lift_diag_mem_B hcfg hq M ψ hψ hdiag i g hg
  have hNle : M.piImg N ≤
      Subgroup.normalizer (M.piImg (closureIn K N) : Set (ModGL Tag.E6 F)) :=
    S172DModel.piImg_le_normalizer_piImg_closureIn hcfg M
  intro i
  exact hNle (weylElt_mem_piImg_N hcfg M hZ ψ hψ hdiag hE i)

theorem false_of_famFive_E6 {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .E6) (h3 : 3 ∣ 2 ^ lab.n - 1)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    False := by
  classical
  obtain ⟨F, hFld, hFinF, hCharF, hq, h3F, hZ, ⟨M, hdiag⟩⟩ :=
    exists_diagonal_model_famFive_E6 hcfg hlab htag h3 hmark
  letI : Field F := hFld
  letI : Finite F := hFinF
  letI : CharP F 2 := hCharF
  obtain ⟨-, α, -, -, hαroot, hαUK⟩ :=
    exists_rootCharKernel_famFive_E6 hcfg hq h3F M hZ hdiag
  have hW := weylElt_mem_normalizer_piImg_closureIn_famFive_E6 hcfg hq M hZ hdiag
  have hKle : K ≤ closureIn K N := le_closureIn_self K N
  have hαX : rootSubgroup Tag.E6 F α ≤ M.piImg (closureIn K N) := by
    intro y hy
    exact Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono S hKle)) (hαUK hy)
  have hXG : M.piImg (closureIn K N) ≤ adjointGroup Tag.E6 F := Subgroup.map_subtype_le _
  have hXtop : M.piImg (closureIn K N) = adjointGroup Tag.E6 F :=
    eq_of_rootSubgroup_le_of_weylElt_mem_normalizer hXG hW hαroot hαX
  obtain ⟨R, hRne, hR2, hRle, hRnorm⟩ :=
    S172DModel.exists_twoGroup_normalized_by_piImg_sup_barB hcfg M
  have hnormG : adjointGroup Tag.E6 F ≤ Subgroup.normalizer (R : Set (ModGL Tag.E6 F)) := by
    rw [← hXtop]
    exact le_trans le_sup_left hRnorm
  haveI : Finite ↥(adjointGroup Tag.E6 F) := Subtype.finite
  haveI hsimple : IsSimpleGroup ↥(adjointGroup Tag.E6 F) :=
    CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 F)
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E6 F)).trans
        QuotientGroup.quotientBot).symm
  haveI hNrm : (R.subgroupOf (adjointGroup Tag.E6 F)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRle).2 hnormG
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (R.subgroupOf (adjointGroup Tag.E6 F)) with hbot | htop
  · have hdis : Disjoint R (adjointGroup Tag.E6 F) := Subgroup.subgroupOf_eq_bot.1 hbot
    exact hRne (by rw [← inf_eq_left.2 hRle, hdis.eq_bot])
  · have hReq : R = adjointGroup Tag.E6 F :=
      le_antisymm hRle (Subgroup.subgroupOf_eq_top.1 htop)
    rw [hReq] at hR2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial ↥(adjointGroup Tag.E6 F) := hsimple.toNontrivial
    have hZnt : Nontrivial ↥(Subgroup.center ↥(adjointGroup Tag.E6 F)) := hR2.center_nontrivial
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E6 F] at hZnt
    exact (Subgroup.nontrivial_iff_ne_bot (⊥ : Subgroup ↥(adjointGroup Tag.E6 F))).1 hZnt rfl

end CFSG.LocalAnalysis.GLTheoremA.T173O

end

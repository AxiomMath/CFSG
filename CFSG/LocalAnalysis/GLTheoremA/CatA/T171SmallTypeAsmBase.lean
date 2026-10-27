module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma6364AutAux
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLeviAbstract
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTypes
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem centModSubgroup_le_centralizer_of_primeCore_le_center {Ω : Type} [Group Ω]
    {L : Subgroup Ω} (hL : commutator ↥L = ⊤)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    centModSubgroup 3 L ≤ Subgroup.centralizer (L : Set Ω) := by
  intro g hg
  obtain ⟨hgN, hgC⟩ := hg
  let α : MulAut ↥L := L.normalizerMonoidHom ⟨g, hgN⟩
  have hαcoe : ∀ l : ↥L, ((α l : ↥L) : Ω) = g * (l : Ω) * g⁻¹ := fun l => rfl
  have hα : ∀ l : ↥L, l⁻¹ * α l ∈ Subgroup.center ↥L := by
    intro l
    obtain ⟨c, hcO, hcΩ⟩ := (Subgroup.mem_map (f := L.subtype)).1 (hgC l l.2)
    have hcZ : c ∈ Subgroup.center ↥L := hO hcO
    have hcΩ' : (c : Ω) = ⁅(l : Ω), g⁆ := hcΩ
    have hgl : g * (l : Ω) * g⁻¹ = (c : Ω)⁻¹ * (l : Ω) := by
      rw [hcΩ']
      rw [commutatorElement_def]
      group
    have hcomm : (c : Ω)⁻¹ * (l : Ω) = (l : Ω) * (c : Ω)⁻¹ := by
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hcZ) l)).symm
    have hkey : ((l⁻¹ * α l : ↥L) : Ω) = ((c⁻¹ : ↥L) : Ω) := by
      have hcoe : ((l⁻¹ * α l : ↥L) : Ω) = (l : Ω)⁻¹ * (g * (l : Ω) * g⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαcoe]
      rw [hcoe, hgl, hcomm]
      simp
    have : l⁻¹ * α l = c⁻¹ := Subtype.ext hkey
    rw [this]
    exact Subgroup.inv_mem _ hcZ
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    simpa [commutator, Subgroup.commutator_def] using hL
  have hα1 : α = 1 :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.eq_one_of_inv_mul_mem_center hperf α hα
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : α ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hα1]; rfl
  have h2 := congrArg (fun x : ↥L => (x : Ω)) h1
  have h3 : g * l * g⁻¹ = l := by
    rw [← hαcoe ⟨l, hl⟩]
    exact h2
  have h4 : g⁻¹ * l * g = l := by
    calc g⁻¹ * l * g = g⁻¹ * (g * l * g⁻¹) * g := by rw [h3]
      _ = l := by group
  calc l * g = g * (g⁻¹ * l * g) := by group
    _ = g * l := by rw [h4]

theorem inf_centModSubgroup_eq_zpowers {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    B ⊓ centModSubgroup 3 L = Subgroup.zpowers x := by
  have hle : B ⊓ centModSubgroup 3 L ≤ B ⊓ Subgroup.centralizer (L : Set Ω) :=
    inf_le_inf_left _ (centModSubgroup_le_centralizer_of_primeCore_le_center hcfg.qs.1 hO)
  have hxCL : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  refine le_antisymm ?_ ?_
  · intro b hb
    exact (hcfg.cent b hb.1).1 (hle hb).2
  · intro b hb
    have hbB : b ∈ B := (Subgroup.zpowers_le.2 hcfg.mem) hb
    exact ⟨hbB, centMod_iff.1 (centMod_of_mem_centralizer ((Subgroup.zpowers_le.2 hxCL) hb))⟩

theorem exists_elemAbelian_aut_pquot {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    ∃ A : Subgroup (MulAut (PQuot 3 L)), IsElemAbelian 3 A ∧ 3 ^ 3 ≤ Nat.card A := by
  have hD := inf_centModSubgroup_eq_zpowers hcfg hO
  have hx3 : x ^ 3 = 1 := hcfg.elem.2 x hcfg.mem
  have hx1 : x ≠ 1 := hcfg.ne_one
  have hDcard : Nat.card ↥(B ⊓ centModSubgroup 3 L) = 3 := by
    rw [hD, Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hk : 3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) ≤ Nat.card B := by
    rw [hDcard]
    calc 3 ^ 3 * 3 = 3 ^ 4 := by norm_num
      _ ≤ Nat.card B := hcfg.card_ge
  exact CFSG.LocalAnalysis.GLTheoremA.L6364.exists_elemAbelian_aut (p := 3) hcfg.elem
    hcfg.norm hk

theorem three_le_pRank_mulAut_pquot {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PQuot 3 L))) := by
  obtain ⟨A, hAel, hAcard⟩ := exists_elemAbelian_aut_pquot hcfg hO
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA3
  have hk3 : 3 ≤ k := by
    have hpow : 3 ^ 3 ≤ 3 ^ k := by simpa [hk] using hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hpow
  have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_top : A ≤ ⊤)
    hAel hk
  exact hk3.trans hle

theorem three_le_pRank_mulAut_pSimple {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hO : GLAPPrimeCore 3 ↥L ≤ Subgroup.center ↥L) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PSimple 3 L))) := by
  have hperf : commutator (PQuot 3 L) = ⊤ := by
    haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hcfg.qs.1
    haveI : Group.IsPerfect (PQuot 3 L) := inferInstance
    exact Group.IsPerfect.commutator_eq_top (G := PQuot 3 L)
  have h := (three_le_pRank_mulAut_pquot hcfg hO).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_le_quot hperf)
  simpa [PSimple] using h

theorem four_le_of_typeA_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.A r q) = 2) : 4 ≤ r := by
  have h4 := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, KD264Lie.fieldSize] at h4 hfs
  omega

theorem three_le_of_twistedA_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.twistedA r q) = 2) : 3 ≤ r := by
  have h4 := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, KD264Lie.fieldSize] at h4 hfs
  omega

theorem three_le_of_typeB_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.B r q) = 2) : 3 ≤ r := by
  have h4 := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, KD264Lie.fieldSize] at h4 hfs
  omega

theorem four_le_of_typeD_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.D r q) = 2) : 4 ≤ r := by
  have h4 := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, KD264Lie.fieldSize] at h4 hfs
  omega

theorem four_le_of_twistedD_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid)
    (hfs : KD264Lie.fieldSize (TauCeti.LieTypeIndex.twistedD r q) = 2) : 4 ≤ r := by
  have h4 := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  simp only [TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, KD264Lie.fieldSize] at h4 hfs
  omega

theorem pRank_mulAut_alt_five_le_one :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (alternatingGroup (Fin 5)))) ≤ 1 := by
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThree.PartTwo.Sec4.pRank_three_mulAut_alternatingGroup_five_le_one

theorem pRank_mulAut_alt_six_le_two :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (alternatingGroup (Fin 6)))) ≤ 2 := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i112f_pRank_mulAut_alt
    (K := alternatingGroup (Fin 6)) (n := 6) (Or.inl rfl)
    CFSG.HardMathSupport.Solomon.Coordinator.center_alt_six (MulEquiv.refl _)
  simpa using h

theorem pRank_mulAut_alt_eight_le_two :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (alternatingGroup (Fin 8)))) ≤ 2 := by
  have hZ : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    CFSG.Quasithin.H13.Lem8.center_alternatingGroup_eq_bot (by norm_num)
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 8))) ≤ 2 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 2 ?_
    have hcard : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [hcard]
    norm_num
  have h2 : CFSG.Open.pRank 3
      (⊤ : Subgroup (Outer (alternatingGroup (Fin 8)))) ≤ 0 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0 ?_
    have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four 8 (by norm_num)
    intro h3
    have h31 : 3 ^ (0 + 1) ∣ Nat.card (Outer (alternatingGroup (Fin 8))) := h3
    norm_num at h31
    exact absurd (h31.trans h4) (by norm_num)
  have h := CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer
    (K := alternatingGroup (Fin 8)) (p := 3) Nat.prime_three hZ
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171S

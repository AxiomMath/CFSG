module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWitCheck
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tabArr_mul (g h : Γ) :
    (tab n (g * h)).toArray = compArr (tab n g).toArray (tab n h).toArray := by
  apply Array.ext'
  rw [compArr_toList]
  simp [tab_mul]

theorem eq_of_tabArr_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {x y : Γ}
    (h : (tab n x).toArray = (tab n y).toArray) : x = y := by
  have h' : tab n x = tab n y := by simpa using h
  refine eq_of_act_eq_base hB hbase fun b _ => ?_
  unfold act
  rw [h']

@[expose] def quotElt (E : List Γ) (x : QuotGen) : Γ := (evalElt E.toArray x.w) ^ x.k

theorem quotGt_eq (E : List Γ) (x : QuotGen) (hw : ∀ l ∈ x.w, l < E.length) :
    quotGt n (genTabs n E) x = (tab n (quotElt E x)).toArray := by
  unfold quotGt quotElt
  rw [tab_pow, wordTabA_eq E.toArray (genTabs n E).toArray (genTabs_hel E) x.w (by simpa using hw)]

theorem quotGi_eq {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (E : List Γ) (x : QuotGen)
    (hw : ∀ l ∈ x.w, l < E.length) (hm : 0 < x.m)
    (hpow : powTab n (quotGt n (genTabs n E) x) x.m = idTab n) :
    quotElt E x ^ x.m = 1 ∧ quotGi n (genTabs n E) x = (tab n (quotElt E x)⁻¹).toArray := by
  have hg : quotElt E x ^ x.m = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← quotGt_eq (n := n) E x hw]
    exact hpow
  refine ⟨hg, ?_⟩
  have hinv : (quotElt E x)⁻¹ = quotElt E x ^ (x.m - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hm]
    exact hg
  unfold quotGi
  rw [hinv, tab_pow, quotGt_eq (n := n) E x hw]

theorem tabArr_comm (g h gi hi : Γ) :
    (tab n (g * h * gi * hi)).toArray =
      commTab (tab n g).toArray (tab n h).toArray (tab n gi).toArray (tab n hi).toArray := by
  unfold commTab
  rw [tabArr_mul, tabArr_mul, tabArr_mul]

end Tables

end CFSG.QuasithinUnique.Vol2Native.L239

namespace CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem quotElt_mem {j : ℕ} (x : QuotGen) (hw : ∀ l ∈ x.w, l < (C.sg ++ C.gens j).length) :
    quotElt (C.sg ++ C.gens j) x ∈ C.Y j := by
  have hels : ∀ l < (C.sg ++ C.gens j).toArray.size,
      (C.sg ++ C.gens j).toArray.getD l 1 ∈ C.Y j := by
    intro l hl
    have := evalElt_getD_mem_closure (C.sg ++ C.gens j).toArray hl
    rw [toList_toArray_set] at this
    exact this
  exact Subgroup.pow_mem _ (evalElt_mem (C.sg ++ C.gens j).toArray hels x.w (by simpa using hw)) _

theorem mem_pCoreOf_of_fix {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) {z : Γ}
    (h : ∀ x ∈ C.Λ j, C.A.act (tab n z).toArray x = x) : z ∈ pCoreOf 2 (C.Y j) := by
  rw [C.core_eq hj hodd, C.mem_tupStab hj]
  exact h

theorem wit3_sound {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) {B : List ℕ}
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {b q₁ q₂ : QuotGen}
    (h : Wit3Ok n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) b q₁ q₂) :
    ∃ b' ∈ C.Y j, orderOf b' = 3 ∧ ∃ x ∈ ⁅pCoreOf 2 (C.Y j), Subgroup.zpowers b'⁆,
      ∃ y ∈ ⁅pCoreOf 2 (C.Y j), Subgroup.zpowers b'⁆, x * y ≠ y * x ∨ x * x ≠ 1 := by
  obtain ⟨hlet, hbm, hb1, hb3, hq, hne⟩ := h
  rw [← C.Y_letters hj] at hlet hb1 hb3 hq hne
  have hwb : ∀ l ∈ b.w, l < (C.sg ++ C.gens j).length := by
    intro l hl
    have := (hlet b (by simp)).1 l hl
    simpa [genTabs_length] using this
  have hw1 : ∀ l ∈ q₁.w, l < (C.sg ++ C.gens j).length := by
    intro l hl
    have := (hlet q₁ (by simp)).1 l hl
    simpa [genTabs_length] using this
  have hw2 : ∀ l ∈ q₂.w, l < (C.sg ++ C.gens j).length := by
    intro l hl
    have := (hlet q₂ (by simp)).1 l hl
    simpa [genTabs_length] using this
  have hm1 : 0 < q₁.m := (hlet q₁ (by simp)).2
  have hm2 : 0 < q₂.m := (hlet q₂ (by simp)).2
  set E : List Γ := C.sg ++ C.gens j with hE
  have hTb := quotGt_eq (n := n) E b hwb
  have hb1' : quotElt E b ≠ 1 := by
    intro h1
    apply hb1
    rw [hTb, h1, tab_one_toArray]
  have hb3' : quotElt E b ^ 3 = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hTb]
    exact hb3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (quotElt E b) = 3 := orderOf_eq_prime hb3' hb1'
  obtain ⟨hpow1, hinv1⟩ := quotGi_eq (n := n) hB hbase E q₁ hw1 hm1 (hq q₁ (by simp)).1
  obtain ⟨hpow2, hinv2⟩ := quotGi_eq (n := n) hB hbase E q₂ hw2 hm2 (hq q₂ (by simp)).1
  obtain ⟨hpowb, hinvb⟩ := quotGi_eq (n := n) hB hbase E b hwb (by omega)
    (by rw [hbm]; exact hb3)
  have hcomm : ∀ (q : QuotGen), (∀ l ∈ q.w, l < E.length) → quotGi n (genTabs n E) q =
      (tab n (quotElt E q)⁻¹).toArray →
      (tab n (⁅quotElt E q, quotElt E b⁆)).toArray = commOf n (genTabs n E) q b := by
    intro q hwq hinvq
    rw [commutatorElement_def, tabArr_comm]
    unfold commOf
    rw [hinvq, hinvb, quotGt_eq (n := n) E q hwq, hTb]
  have hmem : ∀ q : QuotGen, (∀ l ∈ q.w, l < E.length) →
      (∀ x ∈ C.Λ j, C.A.act (quotGt n (genTabs n E) q) x = x) →
      ⁅quotElt E q, quotElt E b⁆ ∈ ⁅pCoreOf 2 (C.Y j), Subgroup.zpowers (quotElt E b)⁆ := by
    intro q hwq hfix
    refine Subgroup.commutator_mem_commutator ?_ (Subgroup.mem_zpowers _)
    apply C.mem_pCoreOf_of_fix hj hodd
    rw [← quotGt_eq (n := n) E q hwq]
    exact hfix
  refine ⟨quotElt E b, C.quotElt_mem b hwb, hord, ⁅quotElt E q₁, quotElt E b⁆,
    hmem q₁ hw1 (hq q₁ (by simp)).2, ⁅quotElt E q₂, quotElt E b⁆,
    hmem q₂ hw2 (hq q₂ (by simp)).2, ?_⟩
  have h1 := hcomm q₁ hw1 hinv1
  have h2 := hcomm q₂ hw2 hinv2
  rcases hne with hne | hne
  · left
    intro hxy
    apply hne
    rw [← h1, ← h2, ← tabArr_mul, ← tabArr_mul, hxy]
  · right
    intro hxx
    apply hne
    rw [← h1, ← tabArr_mul, hxx, tab_one_toArray]

theorem witP_sound {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) {B : List ℕ}
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) {p : ℕ}
    (hp : p.Prime) {b q : QuotGen}
    (h : WitPOk n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) p b q) :
    ∃ b' ∈ C.Y j, orderOf b' = p ∧ ∃ q' ∈ pCoreOf 2 (C.Y j), q' * b' ≠ b' * q' := by
  obtain ⟨hlet, hb1, hbp, hq, hne⟩ := h
  rw [← C.Y_letters hj] at hlet hb1 hbp hq hne
  have hwb : ∀ l ∈ b.w, l < (C.sg ++ C.gens j).length := by
    intro l hl
    have := hlet b (by simp) l hl
    simpa [genTabs_length] using this
  have hwq : ∀ l ∈ q.w, l < (C.sg ++ C.gens j).length := by
    intro l hl
    have := hlet q (by simp) l hl
    simpa [genTabs_length] using this
  set E : List Γ := C.sg ++ C.gens j with hE
  have hTb := quotGt_eq (n := n) E b hwb
  have hTq := quotGt_eq (n := n) E q hwq
  have hb1' : quotElt E b ≠ 1 := by
    intro h1
    apply hb1
    rw [hTb, h1, tab_one_toArray]
  have hbp' : quotElt E b ^ p = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hTb]
    exact hbp
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (quotElt E b) = p := orderOf_eq_prime hbp' hb1'
  refine ⟨quotElt E b, C.quotElt_mem b hwb, hord, quotElt E q, ?_, ?_⟩
  · apply C.mem_pCoreOf_of_fix hj hodd
    rw [← hTq]
    exact hq
  · intro heq
    apply hne
    rw [hTq, hTb, ← tabArr_mul, ← tabArr_mul, heq]

theorem goodLocal_of_wit {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1)
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hcard : C.D.Om[j]!.lbl.size = 3 * p)
    {b q₁ q₂ b' q' : QuotGen}
    (h3 : Wit3Ok n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) b q₁ q₂)
    (hP : WitPOk n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) p b' q') : GoodLocal (C.Y j) := by
  have hcard' : Nat.card (C.Y j) = 2 ^ C.k * 3 * p := by
    rw [C.Y_card hj, hcard]
    ring
  exact goodLocal_of_witnesses (C.Y j) hp h5 hcard' (C.wit3_sound hj hodd hB hbase h3)
    (C.witP_sound hj hodd hB hbase hp hP)

end CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2711c
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveRed
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.HN
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Leaf
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416TConv
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Quasithin.Background.F918V3S1
public import CFSG.HardMathSupport.Dickson.BMRows.Defs
public import CFSG.HardMathSupport.Dickson.BMRows.Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PCompJoin
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLy
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Shape
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import Certificates.Certificate41501
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Closure

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def IsoInv (P : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → P T → P T'

@[expose] def DownClosed (p : ℕ) (P : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → P S →
    ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I → P (PSimple p I)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem typeQ_step (hp : p.Prime) {P : ∀ (T : Type) [Group T], Prop} (hD : DownClosed p P)
    (hinv : IsoInv P) {X K : Subgroup G} (hK : GLAPComponent p X K) (hP : P (PSimple p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (hap : a ^ p = 1) {L : Subgroup G}
    (hL : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set G)) L) :
    P (PSimple p L) := by
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  have hap' : IsPGroup p (Subgroup.zpowers a) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hap
  have hα : chevAut p K ⟨a, ha⟩ ^ p = 1 := chevAut_pow_eq_one p K ha hap
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer hp ha hap' hL
  exact hinv _ _ e.symm
    (hD (PSimple p K) hsimple hnonab hP _ hα _ (glaPComponent_chevTransfer hp ha hap' hL))

theorem exists_hyperplane' (hp : p.Prime) {B : Subgroup G} (hB : IsElemAbelian p B) (hB1 : B ≠ ⊥) :
    ∃ B₁ : Subgroup G, B₁ ≤ B ∧ (B₁.subgroupOf B).index = p ∧ ∃ d ∈ B, d ∉ B₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  haveI : Group.IsNilpotent B := hBp.isNilpotent
  haveI : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).2 hB1
  have hnt : (⊥ : Subgroup ↥B) ≠ ⊤ := bot_ne_top
  obtain ⟨H, hH, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup ↥B)).resolve_left hnt
  have hidx : H.index = p := hBp.isCoatom_iff_index_eq_prime.1 hH
  have hHB : (H.map B.subtype).subgroupOf B = H :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective H
  refine ⟨H.map B.subtype, Subgroup.map_subtype_le H, by rw [hHB]; exact hidx, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hH.1
  rw [Subgroup.eq_top_iff']
  intro x
  have : (x : G) ∈ H.map B.subtype := hcon x x.2
  obtain ⟨y, hy, hyx⟩ := this
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem eq_sup_zpowers' (hp : p.Prime) {B₁ B : Subgroup G} (hB₁B : B₁ ≤ B)
    (hidx : (B₁.subgroupOf B).index = p) {d : G} (hdB : d ∈ B) (hdB₁ : d ∉ B₁) :
    B₁ ⊔ Subgroup.zpowers d = B := by
  have hMD : B₁ ⊔ Subgroup.zpowers d ≤ B := sup_le hB₁B (Subgroup.zpowers_le.2 hdB)
  have hAM : B₁ ≤ B₁ ⊔ Subgroup.zpowers d := le_sup_left
  have hmul := Subgroup.relIndex_mul_relIndex B₁ (B₁ ⊔ Subgroup.zpowers d) B hAM hMD
  have hAD' : B₁.relIndex B = p := hidx
  rw [hAD'] at hmul
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hmul) with h1 | h1
  · exfalso
    have : B₁ ⊔ Subgroup.zpowers d ≤ B₁ := (Subgroup.relIndex_eq_one.1 h1)
    exact hdB₁ (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  · rw [h1] at hmul
    have h2 : (B₁ ⊔ Subgroup.zpowers d).relIndex B = 1 :=
      Nat.eq_of_mul_eq_mul_left hp.pos (hmul.trans (mul_one p).symm)
    exact le_antisymm hMD (Subgroup.relIndex_eq_one.1 h2)

theorem le_centralizer_of_elem {A B : Subgroup G} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
  Subgroup.mem_centralizer_iff.2 fun b hb => isElemAbelian_commute hA (hBA hb) ha

theorem mem_sup_mul' {A N : Subgroup G} (h : A ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ A ⊔ N) : ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  have hx' : x ∈ ((A ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A N h] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, n, hn, rfl⟩

theorem centralizer_facts' {K A B : Subgroup G} (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKA : K ⊔ A = ⊤) (hBA : B ≤ A) :
    A ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) ∧
    Subgroup.centralizer (B : Set G) ≤ (K ⊓ Subgroup.centralizer (B : Set G)) ⊔ A ∧
    IsSubnormal (K ⊓ Subgroup.centralizer (B : Set G)) (Subgroup.centralizer (B : Set G)) := by
  have hAC := le_centralizer_of_elem hA hBA
  have h1 : A ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    fun a ha => chev_inf_centralizer_le_normalizer hAK B ⟨ha, hAC ha⟩
  have h2 : Subgroup.centralizer (B : Set G) ≤ (K ⊓ Subgroup.centralizer (B : Set G)) ⊔ A := by
    intro y hy
    have hy' : y ∈ A ⊔ K := by rw [sup_comm, hKA]; exact Subgroup.mem_top y
    obtain ⟨a, ha, k, hk, rfl⟩ := mem_sup_mul' hAK hy'
    have hkC : k ∈ Subgroup.centralizer (B : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAC ha)) hy
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left ⟨hk, hkC⟩)
  have h3 : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) :=
    h2.trans (sup_le Subgroup.le_normalizer h1)
  refine ⟨h1, h2, IsSubnormal.step inf_le_right ?_ (IsSubnormal.refl _)⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 h3

theorem pcomp_of_centralizer' (hp : p.Prime) {K A B₁ L : Subgroup G}
    (hA : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKA : K ⊔ A = ⊤)
    (hB₁A : B₁ ≤ A) (hL : GLAPComponent p (Subgroup.centralizer (B₁ : Set G)) L) :
    GLAPComponent p (K ⊓ Subgroup.centralizer (B₁ : Set G)) L := by
  obtain ⟨hAn, hle, -⟩ := centralizer_facts' hA hAK hKA hB₁A
  have hLK : L ≤ K ⊓ Subgroup.centralizer (B₁ : Set G) :=
    chevTools_perfect_le_of_sup hp hAn (isPGroup_of_isElemAbelian hA) (hL.1.trans hle)
      (glaPComponent_perfect hL)
  exact glaPComponent_of_le hp hL hLK inf_le_right

theorem typeQ_core (hp : p.Prime) (hp2 : p ≠ 2) {P : ∀ (T : Type) [Group T], Prop}
    (hD : DownClosed p P) (hinv : IsoInv P) (h183 : Input18_3_4)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y) {K A : Subgroup Y}
    (hK : GLAPComponent p K K) (hP : P (PSimple p K))
    (hA : IsElemAbelian p A) (hAK : A ≤ Subgroup.normalizer (K : Set Y)) (hKA : K ⊔ A = ⊤) :
    ∀ (B : Subgroup Y), B ≤ A → ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer (B : Set Y)) J → P (PSimple p J) := by
  suffices h : ∀ n : ℕ, ∀ B : Subgroup Y, Nat.card B = n → B ≤ A → ∀ J : Subgroup Y,
      GLAPComponent p (K ⊓ Subgroup.centralizer (B : Set Y)) J → P (PSimple p J) from
    fun B hBA J hJ => h _ B rfl hBA J hJ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn hBA J hJ
  by_cases hB1 : B = ⊥
  · subst hB1
    have e : K ⊓ Subgroup.centralizer (((⊥ : Subgroup Y) : Subgroup Y) : Set Y) = K := by
      refine inf_eq_left.2 fun k _ => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have : c = 1 := by simpa using hc
      rw [this, one_mul, mul_one]
    rw [e] at hJ
    have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
    obtain ⟨-, hall, -⟩ := glaPLayer_of_isQuasisimple (Y := K) hq
    have hJK : J = K := (hall J hJ).trans (hall K hK).symm
    exact hJK ▸ hP
  · obtain ⟨B₁, hB₁B, hidx, d, hdB, hdB₁⟩ := exists_hyperplane' hp (isElemAbelian_mono hA hBA) hB1
    have hBel : IsElemAbelian p B := isElemAbelian_mono hA hBA
    have hB₁A : B₁ ≤ A := hB₁B.trans hBA
    have hcard : Nat.card B₁ < n := by
      rw [← hn]
      exact card_lt_of_lt' (lt_of_le_of_ne hB₁B fun h => hdB₁ (h ▸ hdB))
    have hX₁K : CFSG.Open.IsKGroup ↥(Subgroup.centralizer (B₁ : Set Y)) :=
      hY.of_injective _ (Subgroup.centralizer (B₁ : Set Y)).subtype_injective
    have hBX₁ : B ≤ Subgroup.centralizer (B₁ : Set Y) := le_centralizer_of_elem hBel hB₁B
    have hCB : Subgroup.centralizer (B : Set Y) ≤ Subgroup.centralizer (B₁ : Set Y) :=
      Subgroup.centralizer_le hB₁B
    have hJC : GLAPComponent p (Subgroup.centralizer (B : Set Y)) J :=
      glaPComponent_of_isSubnormal' hp (centralizer_facts' hA hAK hKA hBA).2.2 hJ
    have hJ' : GLAPComponent p (Subgroup.centralizer (B₁ : Set Y) ⊓
        Subgroup.centralizer (B : Set Y)) J := by
      rwa [inf_eq_right.2 hCB]
    obtain ⟨𝒞, hcomp, hsup, hinv', htrans⟩ := h183 Y _ hX₁K p hp B hBX₁ hBel J hJ'
    have hCP : ∀ C ∈ 𝒞, P (PSimple p C) := fun C hC =>
      ih _ hcard B₁ rfl hB₁A C (pcomp_of_centralizer' hp hA hAK hKA hB₁A (hcomp C hC))
    have hJle : J ≤ ⨆ C ∈ 𝒞, C := by
      rw [hsup]
      exact (gLBConj_one J).symm.le.trans (le_iSup₂
        (f := fun g (_ : g ∈ GLAPLayer p (Subgroup.centralizer (B₁ : Set Y))) => GLBConj g J)
        (1 : Y) (Subgroup.one_mem _))
    by_cases hdiag : ∃ C₁ ∈ 𝒞, ∃ C₂ ∈ 𝒞, C₁ ≠ C₂
    · have hcov := i183DiagAt_holds Y p hp hp2 B₁ B J 𝒞 hBel hB₁B hidx hX₁K hJC hcomp hsup hinv'
        htrans hdiag
      obtain ⟨C₁, hC₁, -⟩ := hdiag
      have hJC' : J ≤ C₁ ⊔ centModSubgroup p C₁ := hJle.trans (iSup₂_le fun C hC => by
        by_cases hCC : C = C₁
        · exact hCC ▸ le_sup_left
        · exact (le_centModSubgroup_of_ne hp (hcomp C hC) (hcomp C₁ hC₁) hCC).trans le_sup_right)
      obtain ⟨e⟩ := pSimple_equiv_of_diag hp (hcomp C₁ hC₁) hJC hJC' (hcov C₁ hC₁)
      exact hinv _ _ e.symm (hCP C₁ hC₁)
    · push Not at hdiag
      obtain ⟨C, hC⟩ : ∃ C, C ∈ 𝒞 := by
        by_contra h
        push Not at h
        have h0 : (⨆ C ∈ 𝒞, C) = ⊥ := by simp [h]
        rw [h0, le_bot_iff] at hJle
        exact glaPComponent_ne_bot' hJC hJle
      have hall : ∀ C' ∈ 𝒞, C' = C := fun C' hC' => hdiag C' hC' C hC
      have hJCC : J ≤ C := hJle.trans (iSup₂_le fun C' hC' => (hall C' hC').le)
      have hdN : d ∈ Subgroup.normalizer (C : Set Y) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        exact hall _ (hinv' C hC d hdB)
      have hBeq := eq_sup_zpowers' hp hB₁B hidx hdB hdB₁
      have hCeq : C ⊓ Subgroup.centralizer (B : Set Y) =
          C ⊓ Subgroup.centralizer ({d} : Set Y) := by
        refine le_antisymm (inf_le_inf_left C (Subgroup.centralizer_le (by simpa using hdB))) ?_
        intro y hy
        refine ⟨hy.1, ?_⟩
        have hyB₁ : y ∈ Subgroup.centralizer (B₁ : Set Y) := (hcomp C hC).1 hy.1
        have hle : B ≤ Subgroup.centralizer ({y} : Set Y) := by
          rw [← hBeq]
          refine sup_le (fun b hb => ?_) ?_
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hyB₁ b hb
          · rw [Subgroup.zpowers_le]
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_singleton_iff.1 hy.2).symm
        show y ∈ Subgroup.centralizer (B : Set Y)
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hb)
      have hJd : GLAPComponent p (C ⊓ Subgroup.centralizer ({d} : Set Y)) J := by
        have h1 : GLAPComponent p (C ⊓ Subgroup.centralizer (B : Set Y)) J :=
          glaPComponent_of_le hp hJC (le_inf hJCC hJC.1) inf_le_right
        rwa [hCeq] at h1
      exact typeQ_step hp hD hinv (hcomp C hC) (hCP C hC) hdN (hBel.2 d hdB) hJd

theorem pSimple_equiv_subgroupOf' (p : ℕ) {H L : Subgroup G} (hLH : L ≤ H) :
    Nonempty (PSimple p L ≃* PSimple p (L.subgroupOf H)) := by
  obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf p hLH
  exact ⟨QuotientGroup.congr _ _ g.symm (Subgroup.map_center_eq g.symm)⟩

theorem typeClosure (hp : p.Prime) (hp2 : p ≠ 2) {P : ∀ (T : Type) [Group T], Prop}
    (hD : DownClosed p P) (hinv : IsoInv P) (h183 : Input18_3_4) {X K A : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hK : GLAPComponent p X K) (hP : P (PSimple p K)) (hA : IsElemAbelian p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {J : Subgroup G}
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer (A : Set G)) J) : P (PSimple p J) := by
  classical
  set H : Subgroup G := K ⊔ A with hH
  have hKH : K ≤ H := le_sup_left
  have hAH : A ≤ H := le_sup_right
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hHK : CFSG.Open.IsKGroup ↥H :=
    chevTools_isKGroup_sup hp hKX hAK (isPGroup_of_isElemAbelian hA)
  have hKK : GLAPComponent p K K := glaPComponent_of_le hp hK le_rfl hK.1
  have hK' : GLAPComponent p (K.subgroupOf H) (K.subgroupOf H) :=
    glaPComponent_subgroupOf hp hKH hKK
  obtain ⟨eK⟩ := pSimple_equiv_subgroupOf' p hKH
  have hP' : P (PSimple p (K.subgroupOf H)) := hinv _ _ eK hP
  have hA' : IsElemAbelian p (A.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact Subtype.ext (Subtype.ext (isElemAbelian_commute hA a.2 b.2))
    · exact Subtype.ext (by simpa using hA.2 (x : G) hx)
  have hAK' : A.subgroupOf H ≤ Subgroup.normalizer ((K.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 (hAK hx) (h : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hKA' : K.subgroupOf H ⊔ A.subgroupOf H = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup K A)
  have hJle : K ⊓ Subgroup.centralizer (A : Set G) ≤ H := inf_le_left.trans hKH
  have hJ1 := glaPComponent_subgroupOf hp hJle hJ
  have hcen : (Subgroup.centralizer (A : Set G)).subgroupOf H =
      Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_subgroupOf_inf_centralizer hAH,
      Subgroup.inf_subgroupOf_left]
  have hinf : (K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H =
      K.subgroupOf H ⊓ Subgroup.centralizer ((A.subgroupOf H : Subgroup H) : Set H) := by
    rw [← hcen]
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hinf] at hJ1
  have hres := typeQ_core hp hp2 hD hinv h183 (Y := ↥H) hHK hK' hP' hA' hAK' hKA'
    (A.subgroupOf H) le_rfl (J.subgroupOf H) hJ1
  obtain ⟨eJ⟩ := pSimple_equiv_subgroupOf' p (hJ.1.trans hJle)
  exact hinv _ _ eJ.symm hres

end Closure

section JZero

@[expose] def J0Type (p : ℕ) (Y : Type) [Group Y] : Prop :=
  (∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) Y) ∨ (∃ k : ℕ, IsAltType (k * p + 2) Y) ∨
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
      Nonempty (Y ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
        (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
    (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) Y ∧ HasFixedPointFreeOrder ε n p)

@[expose] def J0Free (p N M : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → J0Type p Y → N ∣ Nat.card Y →
    Nat.card Y ∣ M → False

@[expose] def spTwoOrd (n : ℕ) : ℕ := 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1)

theorem card_statedSp_two (n : ℕ) : Nat.card ↥(StatedSp n (ZMod 2)) = spTwoOrd n := by
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := ZMod 2) n
  rw [Nat.card_zmod] at h
  exact h

theorem factorial_half_dvd {m₀ m : ℕ} (h2 : 2 ≤ m₀) (h : m₀ ≤ m) :
    m₀.factorial / 2 ∣ m.factorial / 2 := by
  have h2f : 2 ∣ m₀.factorial := Nat.dvd_factorial (by norm_num) h2
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial h
  obtain ⟨d, hd⟩ := h2f
  refine ⟨c, ?_⟩
  rw [hc, hd, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem card_altType {m : ℕ} {Y : Type} [Group Y] (h : IsAltType m Y) :
    Nat.card Y = 1 ∨ (2 ≤ m ∧ Nat.card Y = m.factorial / 2) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · left
    haveI : Subsingleton (Fin m) := by
      rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> infer_instance
    haveI : Subsingleton (alternatingGroup (Fin m)) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      exact Subsingleton.elim _ _
    exact Nat.card_unique
  · right
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
    exact ⟨hm, by rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]⟩

theorem commutator_self_eq_of_perfect {G : Type*} [Group G] {H : Subgroup G}
    (h : Group.IsPerfect ↥H) : ⁅H, H⁆ = H := by
  have h1 : commutator ↥H = ⊤ := h.commutator_eq_top
  have h2 : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem card_spTwo {n : ℕ} {Y : Type} [Group Y]
    (e : Y ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2)))) :
    (3 ≤ n ∧ Nat.card Y = spTwoOrd n) ∨ (n ≤ 2 ∧ Nat.card Y ∣ 720) := by
  rw [Nat.card_congr e.toEquiv]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · right
    refine ⟨by omega, ?_⟩
    have hle : ⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ ≤ StatedSp n (ZMod 2) := by
      set H := StatedSp n (ZMod 2)
      refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [card_statedSp_two] at h1
    refine h1.trans ?_
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> decide
  · left
    refine ⟨hn, ?_⟩
    have hperf : Group.IsPerfect ↥(StatedSp n (ZMod 2)) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n := n) (K := ZMod 2)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn⟩))
    rw [commutator_self_eq_of_perfect hperf, card_statedSp_two]

theorem not_isSolvable_of_isQuasisimple' {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    ¬ Group.IsSolvable Y := by
  intro hs
  have : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.toNontrivial
  have : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Y
  rw [hq.1] at h
  exact lt_irrefl _ h

theorem le_of_two_pow_dvd {a b c : ℕ} (hb : ¬ 2 ^ (c + 1) ∣ b) (h : 2 ^ a ∣ b) : a ≤ c := by
  by_contra hac
  exact hb ((Nat.pow_dvd_pow 2 (by omega)).trans h)

theorem j0Free_of_checks {p N M m₀ b : ℕ} (hN60 : ¬ N ∣ 60) (hN720 : ¬ N ∣ 720) (hm₀ : 2 ≤ m₀)
    (hM : ¬ m₀.factorial / 2 ∣ M) (hA : ∀ m < m₀, 2 ≤ m → ¬ N ∣ m.factorial / 2) (hb : ¬ 2 ^ (b + 1) ∣ M)
    (hSp : ∀ n, 3 ≤ n → n ^ 2 ≤ b → ¬ N ∣ spTwoOrd n)
    (hOm : ∀ (ε : Bool) (m : ℕ), 3 ≤ m → m * (m - 1) ≤ b → ¬ N ∣ OmegaFacts.omegaOrd ε m) :
    J0Free p N M := by
  intro Y _ _ hq hT hNY hYM
  have hN1 : N ≠ 1 := fun h => hN60 (h ▸ one_dvd _)
  have halt : ∀ m, IsAltType m Y → False := by
    intro m hm
    rcases card_altType hm with h1 | ⟨h2m, h2⟩
    · rw [h1, Nat.dvd_one] at hNY
      exact hN1 hNY
    · rw [h2] at hNY hYM
      rcases Nat.lt_or_ge m m₀ with hlt | hge
      · exact hA m hlt h2m hNY
      · exact hM ((factorial_half_dvd hm₀ hge).trans hYM)
  rcases hT with ⟨k, -, hk⟩ | ⟨k, hk⟩ | ⟨ε, n, -, -, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, -⟩
  · exact halt _ hk
  · exact halt _ hk
  · rcases card_spTwo e with ⟨hn3, hc⟩ | ⟨-, hc⟩
    · rw [hc] at hNY hYM
      have h2 : 2 ^ (n ^ 2) ∣ M := (Dvd.intro _ rfl).trans hYM
      exact hSp n hn3 (le_of_two_pow_dvd hb h2) hNY
    · exact hN720 (hNY.trans hc)
  · rcases OmegaFacts.omega_data hΩ with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, hsol, -⟩ | ⟨-, -, h60, -⟩ |
        ⟨hn2, hc, -, -⟩
    · omega
    · omega
    · exact not_isSolvable_of_isQuasisimple' hq hsol
    · rw [h60] at hNY
      exact hN60 hNY
    · rw [hc] at hNY hYM
      have h2 : 2 ^ ((n + 1) * (n + 1 - 1)) ∣ M := by
        refine dvd_trans ?_ hYM
        unfold OmegaFacts.omegaOrd
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      exact hOm ε (n + 1) (by omega) (le_of_two_pow_dvd hb h2) hNY

theorem spTwoOrd_three : spTwoOrd 3 = 1451520 := by
  simp [spTwoOrd, Finset.prod_Icc_succ_top]

theorem omegaOrd_three (ε : Bool) : OmegaFacts.omegaOrd ε 3 = if ε then 20160 else 25920 := by
  have h : CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd 2 = 45 := by
    rw [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ]
    simp [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd]
  cases ε <;> simp [OmegaFacts.omegaOrd, h]

theorem spTwoOrd_four : spTwoOrd 4 = 47377612800 := by
  simp [spTwoOrd, Finset.prod_Icc_succ_top]

theorem omegaOrd_four (ε : Bool) :
    OmegaFacts.omegaOrd ε 4 = if ε then 174182400 else 197406720 := by
  have h : CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd 3 = 2835 := by
    rw [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ]
    simp [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd]
  cases ε <;> simp [OmegaFacts.omegaOrd, h]

theorem omegaOrd_five (ε : Bool) :
    OmegaFacts.omegaOrd ε 5 = if ε then 23499295948800 else 25015379558400 := by
  have h : CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd 4 = 722925 := by
    rw [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ,
      CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ]
    simp [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd]
  cases ε <;> simp [OmegaFacts.omegaOrd, h]

end JZero

section Sieve

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicOnePair)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)

@[expose] def SporPairCase (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    (¬ ∃ n : ℕ, IsAltType n (↥L ⧸ Subgroup.center ↥L)) →
    (¬ ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥L ⧸ Subgroup.center ↥L)) →
    (∃ A : Subgroup (MulAut ↥L), IsElemAbelian p A ∧ 3 ≤ CFSG.Open.pRank p A) →
    CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1 →
    IsSporType name (↥L ⧸ Subgroup.center ↥L) →
    (∀ b ∈ B, ∃ k ∈ L, k⁻¹ * b ∈ Subgroup.centralizer (L : Set X)) →
    ∀ J0 : Subgroup X,
      CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      J0Type p ↥J0 → ¬ (p = 3 ∧ IsAltType 5 J0) →
    ∀ E : Subgroup X, E ≤ B → B ⊓ Subgroup.centralizer (L : Set X) ≤ E →
      Nat.card B ≤ p ^ 2 * Nat.card E →
      GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      2 ≤ CFSG.Open.pRank p E →
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥ →
      (∀ e ∈ E, GLAPLayer p (L ⊓ Subgroup.centralizer ({e} : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

theorem inputI2711SporPairs_of_cases
    (h : ∀ name p, SporadicOnePair name p → ¬ (name = .McL ∧ p = 3) → ¬ (name = .Ly ∧ p = 5) →
      SporPairCase name p) : Inputs2711b.InputI2711SporPairs := by
  intro X _ _ p hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 name hname hpair hMcL hLy hin J0 hJ0 hJt
    hJ5 E hEB hEC hEi hEl hE2 hlE hle
  exact h name p hpair hMcL hLy X hp hp2 L B hLK hLq hB hBN hmax hB4 hnA hnC hA hC1 hname hin J0 hJ0 hJt hJ5
    E hEB hEC hEi hEl hE2 hlE hle

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem glaPPrimeCore_eq_bot_of_simple {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hp : p.Prime) (hpT : p ∣ Nat.card T) : GLAPPrimeCore p T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p T) with h | h
  · exact h
  · exfalso
    haveI : Fact p.Prime := ⟨hp⟩
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p T)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hcop
    exact (hp.coprime_iff_not_dvd).1 hcop hpT

theorem card_pSimple_dvd (p : ℕ) (J : Subgroup X) : Nat.card (PSimple p J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem false_of_sieve (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) {P : ∀ (T : Type) [Group T], Prop} (hD : DownClosed p P)
    (hinv : IsoInv P) {N : ℕ} (hPN : ∀ (T : Type) [Group T] [Finite T], P T → N ∣ Nat.card T)
    {name : TauCeti.SporadicName} (hPS : P (TauCeti.CFSGIndex.sporadic name).Group)
    (hpS : p ∣ sporOrd name) (hJ0F : J0Free p N (12 * sporOrd name))
    {L B J0 E : Subgroup X} (hLK : CFSG.IsKGroup ↥L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L))
    (hJ0 : CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X))) (hJt : J0Type p ↥J0) (hEB : E ≤ B)
    (hEl : GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    False := by
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    L ⊓ Subgroup.normalizer (U : Set X) with hΓ
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hEl
  have hΓL : Γ ≤ L := iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hJ0L : J0 ≤ L := hJ0.1.trans hΓL
  have hLE : L ⊓ Subgroup.centralizer (E : Set X) ≤ Γ :=
    le_iSup_of_le E (le_iSup_of_le hEB (le_iSup_of_le hE2
      (inf_le_inf_left L (Subgroup.centralizer_le_normalizer _))))
  have hsn : IsSubnormal (J0 ⊓ Subgroup.centralizer (E : Set X))
      (L ⊓ Subgroup.centralizer (E : Set X)) := by
    have h1 := hJ0.2.1.inf (L ⊓ Subgroup.centralizer (E : Set X))
    rwa [inf_eq_right.2 hLE, ← inf_assoc, inf_eq_left.2 hJ0L] at h1
  have hJL : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set X)) J :=
    glaPComponent_of_isSubnormal' hp hsn hJ
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  obtain ⟨eS⟩ := hname
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  have hcardS : Nat.card (↥L ⧸ Subgroup.center ↥L) = sporOrd name :=
    (Nat.card_congr eS.toEquiv).trans (hOrd name)
  have hpLZ : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := hcardS ▸ hpS
  have hLL : GLAPComponent p L L := S10.glaPComponent_of_quasisimple hp (IsSubnormal.refl L) hLq hpLZ
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq
  obtain ⟨ePL⟩ := pSimple_equiv_of_surjective_simple hp hLL hnab
    (glaPPrimeCore_eq_bot_of_simple hp hpLZ) (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _)
  have hPL : P (PSimple p L) := hinv _ _ (ePL.trans eS).symm hPS
  have hEel : IsElemAbelian p E := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB hEB
  have hPJ : P (PSimple p J) :=
    typeClosure hp hp2 hD hinv h183 hLK' hLL hPL hEel (hEB.trans hBN) hJL
  have hN : N ∣ Nat.card J0 := by
    have hJJ0 : J ≤ J0 := hJ.1.trans inf_le_left
    exact (hPN _ hPJ).trans ((card_pSimple_dvd p J).trans (Subgroup.card_dvd_of_le hJJ0))
  have hL12 : Nat.card L ∣ 12 * sporOrd name := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hLq name eS
    rw [← Subgroup.card_mul_index (Subgroup.center ↥L), Subgroup.index_eq_card, hcardS] at *
    exact Nat.mul_dvd_mul_right h1 _
  have hJ0M : Nat.card J0 ∣ 12 * sporOrd name := (Subgroup.card_dvd_of_le hJ0L).trans hL12
  exact hJ0F ↥J0 hJ0.2.2 hJt hN hJ0M

end Sieve

section SporDown

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (PConstrainedShape)

theorem fixSubgroup_one_eq_top' {S : Type} [Group S] : fixSubgroup (1 : MulAut S) = ⊤ := by
  ext x
  simp [mem_fixSubgroup]

theorem fixSubgroup_conj_eq' {S : Type} [Group S] (s : S) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    calc s * x * s⁻¹ = x * s * s⁻¹ := by rw [h]
      _ = x := by group

theorem pSimple_of_sporShape {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (htab : CentShapeRk p Good Rk Q) {P : ∀ (T : Type) [Group T], Prop} (hinv : IsoInv P)
    (hPS : P (TauCeti.CFSGIndex.sporadic s).Group) (hGP : ∀ (T : Type) [Group T], Good T → P T)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hT : Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (α : MulAut T) (hα : α ^ p = 1)
    (I : Subgroup T) (hI : GLAPComponent p (fixSubgroup α) I) : P (PSimple p I) := by
  obtain ⟨e⟩ := hT
  have hcen : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut T inferInstance hnab s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout α hα
  by_cases hx1 : x = 1
  · subst hx1
    rw [map_one, fixSubgroup_one_eq_top'] at hI
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv hp hnab hI
    exact hinv _ _ (f.trans e).symm hPS
  · haveI : Fact p.Prime := ⟨hp⟩
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    rw [fixSubgroup_conj_eq'] at hI
    let φ : T ≃* Q := e.trans b.symm
    have hφ1 : φ x ≠ 1 := fun h => hx1 (φ.injective (h.trans (map_one φ).symm))
    have hφp : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hsh := ShapeRkAt.of_equiv hp hGood hRk φ.symm (htab (φ x) hφ1 hφp)
    rw [MulEquiv.symm_apply_apply] at hsh
    rcases hsh with hc | ⟨J, -, huniq, hG, -⟩
    · exact (no_glaPComponent_of_pConstrainedShape hp hc hI).elim
    · rw [huniq I hI]
      exact hGP _ hG

theorem pSimple_of_sporShape' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (htab : CentShapeRk' p Good Rk Q) {P : ∀ (T : Type) [Group T], Prop} (hinv : IsoInv P)
    (hPS : P (TauCeti.CFSGIndex.sporadic s).Group) (hGP : ∀ (T : Type) [Group T], Good T → P T)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hT : Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (α : MulAut T) (hα : α ^ p = 1)
    (I : Subgroup T) (hI : GLAPComponent p (fixSubgroup α) I) : P (PSimple p I) := by
  obtain ⟨e⟩ := hT
  have hcen : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut T inferInstance hnab s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout α hα
  by_cases hx1 : x = 1
  · subst hx1
    rw [map_one, fixSubgroup_one_eq_top'] at hI
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv hp hnab hI
    exact hinv _ _ (f.trans e).symm hPS
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [fixSubgroup_conj_eq'] at hI
    let φ : T ≃* Q := e.trans b.symm
    have hφ1 : φ x ≠ 1 := fun h => hx1 (φ.injective (h.trans (map_one φ).symm))
    have hφp : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hsh := ShapeRkAt'.of_equiv hp hGood hRk φ.symm (htab (φ x) hφ1 hφp)
    rw [MulEquiv.symm_apply_apply] at hsh
    rcases hsh with hc | ⟨J, -, huniq, hG, -⟩
    · exact (hc I hI).elim
    · rw [huniq I hI]
      exact hGP _ hG

theorem centShapeRk_of_constrained {name : TauCeti.SporadicName} {p : ℕ}
    (h : ConstrainedShape name p) :
    CentShapeRk p (fun _ _ => False) (fun _ _ => True) (NativeSporadic.Carrier name) :=
  fun k hk1 hkp => Or.inl (h k hk1 hkp)

end SporDown

section PairLy

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Recognition.LyonsSims
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)


theorem lyShape_three :
    CentShapeRk 3 (fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (fun _ _ => True)
      (NativeSporadic.Carrier .Ly) := by
  haveI : Finite (NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (NativeSporadic.Carrier .Ly ≃* NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' →
      Nonempty (T ≃* NativeSporadic.McL) → Nonempty (T' ≃* NativeSporadic.McL) :=
    fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hA : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (fun _ _ => True)
      (x₁ : NativeSporadic.Carrier .Ly) := by
    obtain ⟨eP⟩ := tabLy_pSimple D St
    exact shapeRkAt_of_normal_quasisimple Nat.prime_three le_rfl
      (fun g hg l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg))
      (tabLy_quasisimple D St) (tabLy_three_dvd St) (tabLy_isPGroup_cent D St) ⟨eP⟩ trivial
  have hB : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (fun _ _ => True)
      ((x₁ : NativeSporadic.Carrier .Ly) * (x₂ : NativeSporadic.Carrier .Ly)) :=
    Or.inl (tabLy_threeB D St (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
      (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St)))
  have htr : ∀ {a b : NativeSporadic.Carrier .Ly}, IsConj a b →
      ShapeRkAt 3 (fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (fun _ _ => True) a →
        ShapeRkAt 3 (fun T _ => Nonempty (T ≃* NativeSporadic.McL)) (fun _ _ => True) b := by
    intro a b hab ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hab
    have := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj c) ha
    rwa [MulAut.conj_apply, hc] at this
  intro k hk1 hk3
  have hk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact htr h.symm hA
  · exact htr h.symm hB

end PairLy

section PairLyAssembly

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PLy (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Ly).Group) ∨
    Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .McL).Group)

theorem isoInv_PLy : IsoInv PLy := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

theorem dvd_card_of_PLy (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T] (h : PLy T) :
    898128000 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .Ly]
    simp only [sporOrd, CFSG.Open.orderLy]
    norm_num
  · rw [Nat.card_congr f.toEquiv, hOrd .McL]
    exact dvd_refl _

theorem j0Free_Ly : J0Free 3 898128000 (12 * sporOrd .Ly) := by
  refine j0Free_of_checks (m₀ := 13) (b := 10) (by decide) (by decide) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp only [sporOrd, CFSG.Open.orderLy]
    decide
  · decide
  · simp only [sporOrd, CFSG.Open.orderLy]
    decide
  · intro n hn3 hn
    have : n = 3 := by nlinarith
    subst this
    rw [spTwoOrd_three]
    decide
  · intro ε m hm3 hm
    have : m = 3 := by
      rcases Nat.lt_or_ge m 4 with h | h
      · omega
      · have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
        omega
    subst this
    rw [omegaOrd_three]
    cases ε <;> decide

theorem downClosed_PLy
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hMcL : ConstrainedShape .McL 3) :
    DownClosed 3 PLy := by
  intro T _ _ hs hnab hP α hα I hI
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  rcases hP with hT | hT
  · obtain ⟨bL⟩ := hBr .Ly
    haveI : Finite (NativeSporadic.Carrier .Ly) := Finite.of_equiv _ (hT.some.trans bL.symm).toEquiv
    exact pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bL
      (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) hRk lyShape_three isoInv_PLy
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ ⟨f⟩ => Or.inr ⟨f.trans (hBr .McL).some⟩) hnab hT α hα I hI
  · obtain ⟨bM⟩ := hBr .McL
    haveI : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv _ (hT.some.trans bM.symm).toEquiv
    exact pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bM (fun _ _ _ _ _ h => h) hRk
      (centShapeRk_of_constrained hMcL) isoInv_PLy (Or.inr ⟨MulEquiv.refl _⟩) (fun _ _ h => h.elim)
      hnab hT α hα I hI

theorem sporPairCase_Ly_three
    (h183 : Input18_3_4) (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hMcL : ConstrainedShape .McL 3) : SporPairCase .Ly 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ _ hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exact (false_of_sieve hp hp2 h183 hSpM hOrd (downClosed_PLy hOut hBr hMcL) isoInv_PLy
    (fun _ _ _ h => dvd_card_of_PLy hOrd h) (Or.inl ⟨MulEquiv.refl _⟩)
    (by simp only [sporOrd, CFSG.Open.orderLy]; norm_num) j0Free_Ly hLK hLq hB hBN hname hJ0 hJt hEB
    hEl hE2).elim

end PairLyAssembly

section Terminal

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem mem_inner_of_card {T : Type} [Group T] [Finite T] (hz : Subgroup.center T = ⊥) {m p : ℕ}
    (hp : p.Prime) (hcard : Nat.card (MulAut T) = m * Nat.card T) (hm : ¬ p ∣ m) (α : MulAut T)
    (hα : α ^ p = 1) : α ∈ inner T := by
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut T => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hz, Subgroup.mem_bot] at hc
    exact hc
  have hinner : Nat.card (inner T) = Nat.card T := Nat.card_range_of_injective hinj
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hidx : (inner T).index = m := by
    have h := (inner T).card_mul_index
    rw [hinner, hcard, mul_comm m] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  haveI : Finite (MulAut T) := inferInstance
  let π : MulAut T →* Outer T := QuotientGroup.mk' (inner T)
  have hp' : π α ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ p := orderOf_dvd_of_pow_eq_one hp'
  have hdvd : orderOf (π α) ∣ m := by
    have := orderOf_dvd_natCard (π α)
    rwa [show Nat.card (Outer T) = (inner T).index from rfl, hidx] at this
  rcases (Nat.dvd_prime hp).1 hord with h1 | h1
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)
  · rw [h1] at hdvd
    exact absurd hdvd hm

theorem pSimple_equiv_of_terminal {p : ℕ} (hp : p.Prime) (hKD : KDChevInner p) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hC : IsChevSimple p T)
    (hin : ∀ α : MulAut T, α ^ p = 1 → α ∈ inner T) (α : MulAut T) (hα : α ^ p = 1)
    (I : Subgroup T) (hI : GLAPComponent p (fixSubgroup α) I) : Nonempty (PSimple p I ≃* T) := by
  by_cases h1 : α = 1
  · subst h1
    rw [fixSubgroup_one_eq_top'] at hI
    exact chevQ_pSimple_top_equiv hp hnab hI
  · exfalso
    have hL := hKD T inferInstance hnab hC α hα h1 (hin α hα)
    have hIle : I ≤ GLAPLayer p (fixSubgroup α) := le_sSup hI
    rw [hL, le_bot_iff] at hIle
    exact glaPComponent_ne_bot' hI hIle

end Terminal

section PairFi22Table

open CFSG.Open CFSG.Certificates CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent CFSG.HardMathSupport.Dickson.I271
open CFSG.LieType.Multipliers.U43 (X₀)

section ClassA


theorem fi22ShapeRkAt_xP
    (hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥) :
    ShapeRkAt 3 (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) xP := by
  refine shapeRkAt_of_subgroup_data_solvable Nat.prime_three
    (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) (fun _ _ _ _ _ h => h) fi22P xP lSub ?_
    lSub_normalized_cent isSimpleGroup_lSub nonabelian_lSub ?_ hcore (m := 6) ?_ (by norm_num)
    nonempty_lSub_equiv trivial
  · intro l hl
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (lSub_comm_x l hl),
      ((mem_lev2_iff _).1 (lSub_le_lev2 hl)).1⟩
  · rw [card_lSub]; norm_num
  · refine card_cent_eq.trans ?_
    rw [card_lSub]

end ClassA

section ClassAJ

open CFSG.Sporadic.Fi22 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump
  CFSG.HardMathSupport.Dickson.I271.TabFi22Small


theorem fi22ShapeRkAt_xRep_three :
    ShapeRkAt 3 (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) (xRep 3) := by
  haveI := finite_J_tab
  have hOP : OPrimeCoreTrivialAt 3 ↥fi22P :=
    @OPrimeCoreTrivialAt.of_mulEquiv 3 ↥fi22P _ ↥CFSG.Sporadic.Fi22.J inferInstance eJP.symm oPrimeCoreTrivialAt_Fi22J
  have hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥ :=
    (glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore 3 _).1 (hOP xP orderOf_xP)
  have hshape := fi22ShapeRkAt_xP hcore
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* X₀) →
      Nonempty (T' ≃* X₀) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hJ := @ShapeRkAt.of_equiv ↥fi22P ↥CFSG.Sporadic.Fi22.J _ _ inferInstance 3 Nat.prime_three
    (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) hGood hRk finite_J_tab eJP.symm xP hshape
  set t : CFSG.Sporadic.Fi22.J := eJP.symm xP with ht
  have hord : orderOf t = 3 := by rw [MulEquiv.orderOf_eq]; exact orderOf_xP
  have hiota : Fi22Copy.iotaJ t = xPerm := by
    have h1 := eJP_apply t
    rw [ht, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨k, hk4, hconj⟩ := fi22_classify t hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hfix : fixCard (Fi22Copy.iotaJ (xRep k)) = 126 := by
    rw [← hc, map_mul, map_mul, map_inv, hiota, fixCard_conj]
    exact fixCard_xPerm
  have hk3 : k = 3 := by
    have hf := Fi22Copy.fixN_xRep
    simp only [fixN_eq_card] at hf
    interval_cases k <;> omega
  subst hk3
  have h2 := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) hGood hRk finite_J_tab (MulAut.conj c) t hJ
  rw [MulAut.conj_apply, hc] at h2
  exact h2

theorem fi22CentShapeRk : CentShapeRk 3 (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) CFSG.Sporadic.Fi22.J := by
  haveI := finite_J_tab
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* X₀) →
      Nonempty (T' ≃* X₀) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨j, hj4, hconj⟩ := fi22_classify k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hsh : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) (xRep j) := by
    by_cases h3 : j = 3
    · subst h3
      exact fi22ShapeRkAt_xRep_three
    · exact Or.inl (tabFi22_pConstrained_xRep (by omega))
  have h := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True) hGood hRk finite_J_tab (MulAut.conj c⁻¹)
    (xRep j) hsh
  have hk : (MulAut.conj c⁻¹) (xRep j) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

theorem fi22CentShapeRk_native :
    CentShapeRk 3 (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True)
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := by
  haveI := finite_J_tab
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi22 :=
    Finite.of_equiv CFSG.Sporadic.Fi22.J (CFSG.Sporadic.Fi22.fi22EquivJ.symm.toEquiv)
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* X₀) →
      Nonempty (T' ≃* X₀) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  exact @CentShapeRk.of_equiv ↥CFSG.Sporadic.Fi22.J CFSG.Blueprint.NativeSporadic.Fi22 inferInstance finite_J_tab
    inferInstance 3 Nat.prime_three (fun T _ => Nonempty (T ≃* X₀)) (fun _ _ => True)
    hGood hRk inferInstance CFSG.Sporadic.Fi22.fi22EquivJ.symm fi22CentShapeRk

end ClassAJ

end PairFi22Table

section PairFi22Assembly

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PFi22 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) ∨ Nonempty (T ≃* X₀)

theorem isoInv_PFi22 : IsoInv PFi22 := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

theorem dvd_card_of_PFi22 (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PFi22 T) : 3265920 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .Fi22]
    simp only [sporOrd]
    norm_num
  · rw [Nat.card_congr f.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]

theorem j0Free_Fi22 : J0Free 3 3265920 (12 * sporOrd .Fi22) := by
  refine j0Free_of_checks (m₀ := 14) (b := 19) (by decide) (by decide) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp only [sporOrd]
    decide
  · decide
  · simp only [sporOrd]
    decide
  · intro n hn3 hn
    have : n = 3 ∨ n = 4 := by
      rcases Nat.lt_or_ge n 5 with h | h
      · omega
      · have : 5 * 5 ≤ n ^ 2 := by nlinarith
        omega
    rcases this with rfl | rfl
    · rw [spTwoOrd_three]; decide
    · rw [spTwoOrd_four]; decide
  · intro ε m hm3 hm
    have : m = 3 ∨ m = 4 := by
      rcases Nat.lt_or_ge m 5 with h | h
      · omega
      · have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
        omega
    rcases this with rfl | rfl
    · rw [omegaOrd_three]; cases ε <;> decide
    · rw [omegaOrd_four]; cases ε <;> decide


theorem mem_inner_of_X₀ {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (e : T ≃* X₀) (α : MulAut T) (hα : α ^ 3 = 1) :
    α ∈ inner T := by
  obtain ⟨eA, -⟩ := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut.autModel
  have hA : Nat.card (MulAut X₀) = 26127360 :=
    (Nat.card_congr eA.toEquiv).symm.trans CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut.card_Nrm
  have hcard : Nat.card (MulAut T) = 8 * Nat.card T := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, hA, Nat.card_congr e.toEquiv,
      CFSG.LieType.Multipliers.U43.card_X₀]
  exact mem_inner_of_card
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab)
    Nat.prime_three hcard (by decide) α hα

theorem downClosed_PFi22 (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : DownClosed 3 PFi22 := by
  intro T _ _ hs hnab hP α hα I hI
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  rcases hP with hT | ⟨⟨e⟩⟩
  · obtain ⟨bF⟩ := hBr .Fi22
    haveI : Finite (NativeSporadic.Carrier .Fi22) := Finite.of_equiv _ (hT.some.trans bF.symm).toEquiv
    exact pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bF
      (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) hRk fi22CentShapeRk_native isoInv_PFi22
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ h => Or.inr h) hnab hT α hα I hI
  · have hC : IsChevSimple 3 T := isChevSimple_of_mulEquiv e.symm isChevSimple_three_X₀
    obtain ⟨f⟩ := pSimple_equiv_of_terminal Nat.prime_three hKD hnab hC
      (mem_inner_of_X₀ hnab e) α hα I hI
    exact Or.inr ⟨f.trans e⟩

theorem sporPairCase_Fi22_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : SporPairCase .Fi22 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ _ hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exact (false_of_sieve hp hp2 h183 hSpM hOrd (downClosed_PFi22 hOut hBr hKD) isoInv_PFi22
    (fun _ _ _ h => dvd_card_of_PFi22 hOrd h) (Or.inl ⟨MulEquiv.refl _⟩)
    (by simp only [sporOrd]; norm_num) j0Free_Fi22 hLK hLq hB hBN hname hJ0 hJt hEB hEl hE2).elim

end PairFi22Assembly

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem dvd_of_outer_statedPSU {S : Type} [Group S] [Finite S] {n p f : ℕ}
    (hM : StatedClassicalModel S .PSU n p f) (hn3 : 3 ≤ n) (hp2 : p ≠ 2)
    (hg : ¬ p ∣ Nat.gcd n (p ^ f + 1)) {ψ : MulAut S} (hψp : ψ ^ p = 1)
    (hψo : ψ ∉ (MulAut.conj : S →* MulAut S).range) : p ∣ f := by
  obtain ⟨⟨hℓ, hf, -, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hM
  haveI : Fact p.Prime := ⟨hℓ⟩
  have h : UnitaryFieldData p f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := n) (K := K))
  let e' : S ≃* primeFormP h (idGram K n) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  set β := MulAut.congr e' ψ with hβdef
  have hβ : β ^ p = 1 := congr_pow_eq_one e' hψp
  have hβo : β ∉ (MulAut.conj : primeFormP h (idGram K n) →* _).range := congr_not_inner e' hψo
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' β = 1
  · exfalso
    have hβD : β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD] at hβD
    exact hβo (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn3 hq' hℓ hg hβD hβ)
  · have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' β) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    have hK2 : Nat.card K = p ^ (2 * f) := h.card
    exact dvd_of_dvd_two_mul hℓ hp2 (dvd_of_orderOf_ringAut hℓ hK2 hσp)

theorem statedPSU_of_mulEquiv {G G' : Type} [Group G] [Group G'] {n p f : ℕ} (e : G' ≃* G)
    (h : StatedClassicalModel G .PSU n p f) : StatedClassicalModel G' .PSU n p f := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨φ⟩⟩ := h
  exact ⟨hadm, K, hF, hfin, hK, ⟨e.trans φ⟩⟩

end Unitary

section PairHNTable

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.HNSchreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Dickson.I271

abbrev IsU35 (T : Type) [Group T] : Prop := StatedClassicalModel T .PSU 3 5 1

theorem isU35_of_mulEquiv : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → IsU35 T → IsU35 T' :=
  fun _ _ _ _ e h => statedPSU_of_mulEquiv e.symm h

section Five

open CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNB


theorem hnShape_f : ShapeRkAt 5 IsU35 (fun _ _ => True) fJ := by
  obtain ⟨hcomm, -, -, -, hC, hcardI, -, hder, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  haveI hsimple : IsSimpleGroup ↥IJ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1 model_IJ).2
  have hLC : IJ ≤ Subgroup.centralizer ({fJ} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm fJ (Subgroup.mem_zpowers _) x hx).symm
  have hnp : ¬ (Nat.card ↥IJ).Prime := by
    rw [hcardI]
    norm_num
  have hnab : ∃ a b : ↥IJ, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥IJ) hnp
  have h5 : 5 ∣ Nat.card ↥IJ := by
    rw [hcardI]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({fJ} : Set ↥JH)) = Nat.card ↥IJ * 5 ^ 1 := by
    rw [hC, hcardI]
    norm_num
  refine shapeRkAt_of_data Nat.prime_five isU35_of_mulEquiv
    (fun _ _ _ _ _ h => h) fJ IJ hLC ?_ hsimple hnab h5 hk model_IJ trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈
      ⁅Subgroup.centralizer ({fJ} : Set ↥JH), Subgroup.centralizer ({fJ} : Set ↥JH)⁆ :=
    Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact IJ.mul_mem h1 hl

end Five

section Table


theorem hnCentShapeRk' : CentShapeRk' 5 IsU35 (fun _ _ => True) ↥JH := by
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  intro k hk1 hkp
  have hk5 : orderOf k = 5 := orderOf_eq_prime hkp hk1
  by_cases h5A : ∃ e : ℕ, IsConj k (fJ ^ e)
  · obtain ⟨e, he⟩ := h5A
    obtain ⟨c, hc⟩ := isConj_iff.1 he
    have hko : orderOf (fJ ^ e) = 5 := by
      rw [← hc]
      exact (orderOf_conj_eq c k).trans hk5
    have hcent : Subgroup.centralizer ({fJ ^ e} : Set JH) = Subgroup.centralizer ({fJ} : Set JH) :=
      centralizer_pow_eq (by rw [hko, orderOf_fJ]) (by rw [orderOf_fJ]; norm_num)
    have hshape : ShapeRkAt 5 IsU35 (fun _ _ => True) (fJ ^ e) :=
      ShapeRkAt.of_centralizer_eq hcent.symm hnShape_f
    have := ShapeRkAt.of_equiv Nat.prime_five isU35_of_mulEquiv hRk (MulAut.conj c⁻¹) hshape
    rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
    exact this.toWeak Nat.prime_five
  · push Not at h5A
    have hord : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
      hnFiveOrders_holds k hk5 h5A
    have hO := hnFiveRest_of_orders hnFiveOrders_holds k hk5 h5A
    by_cases h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH))
    · have h9 : ¬ 3 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) := fun h => by
        have := h.trans hord
        norm_num at this
      obtain ⟨Q, hQC, hQn, hQs, s, hsC, hso, hq⟩ := hnFiveMoved_holds k hk5 h5A h3
      exact Or.inl (hnNoComp_of_normal_solvable hQC hQn hQs hO hord
        (hnMoved_of_sylow hQC hQn h9 hsC hso hq))
    · have hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({k} : Set JH))) 3 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
      have hd : Nat.card ↥(Subgroup.centralizer ({k} : Set JH)) ∣ 2 ^ 14 * 5 ^ 6 := by
        have e : 2 ^ 14 * 3 * 5 ^ 6 = 3 * (2 ^ 14 * 5 ^ 6) := by ring
        rw [e] at hord
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop hord
      have hsh : ShapeRkAt 5 IsU35 (fun _ _ => True) k := Or.inl (pConstrainedShape_of_solvable
        Nat.prime_five (isSolvable_of_card_dvd_two_five hd) hO)
      exact hsh.toWeak Nat.prime_five

end Table

end PairHNTable

section PairHNAssembly

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PHN (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) ∨ IsU35 T

theorem isoInv_PHN : IsoInv PHN := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | h
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (isU35_of_mulEquiv T T' e h)

theorem dvd_card_of_PHN (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T] (h : PHN T) :
    126000 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | h
  · rw [Nat.card_congr f.toEquiv, hOrd .HN]
    simp only [sporOrd, CFSG.Open.orderHN]
    norm_num
  · rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h]

theorem j0Free_HN : J0Free 5 126000 (12 * sporOrd .HN) := by
  refine j0Free_of_checks (m₀ := 13) (b := 16) (by decide) (by decide) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp only [sporOrd, CFSG.Open.orderHN]
    decide
  · decide
  · simp only [sporOrd, CFSG.Open.orderHN]
    decide
  · intro n hn3 hn
    have : n = 3 ∨ n = 4 := by
      rcases Nat.lt_or_ge n 5 with h | h
      · omega
      · have : 5 * 5 ≤ n ^ 2 := by nlinarith
        omega
    rcases this with rfl | rfl
    · rw [spTwoOrd_three]; decide
    · rw [spTwoOrd_four]; decide
  · intro ε m hm3 hm
    have : m = 3 ∨ m = 4 := by
      rcases Nat.lt_or_ge m 5 with h | h
      · omega
      · have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
        omega
    rcases this with rfl | rfl
    · rw [omegaOrd_three]; cases ε <;> decide
    · rw [omegaOrd_four]; cases ε <;> decide

theorem mem_inner_of_U35 {T : Type} [Group T] [Finite T] (h : IsU35 T) (α : MulAut T)
    (hα : α ^ 5 = 1) : α ∈ inner T := by
  by_contra hout
  have := dvd_of_outer_statedPSU h (by norm_num) (by norm_num) (by decide) hα hout
  omega


theorem downClosed_PHN (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5) : DownClosed 5 PHN := by
  intro T _ _ hs hnab hP α hα I hI
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  rcases hP with hT | hU
  · have hfJ : Finite ↥CFSG.Sporadic.HNSchreier.JH := by
      have : Nat.card ↥CFSG.Sporadic.HNSchreier.JH ≠ 0 := by
        rw [CFSG.Sporadic.HNSchreier.card_JH]; norm_num
      exact Nat.finite_of_card_ne_zero this
    obtain ⟨b⟩ := CFSG.HardMathSupport.Solomon.Coordinator.YS08.nonempty_jh_equiv hBr
    have htab := hnCentShapeRk'
    exact @pSimple_of_sporShape' 5 Nat.prime_five (by norm_num) hOut .HN
      ↥CFSG.Sporadic.HNSchreier.JH inferInstance hfJ b IsU35 (fun _ _ => True)
      isU35_of_mulEquiv hRk htab PHN isoInv_PHN
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ h => Or.inr h) T _ _ hs hnab hT α hα I hI
  · have hC : IsChevSimple 5 T := isChevSimple_of_statedPSU hU
    obtain ⟨f⟩ := pSimple_equiv_of_terminal Nat.prime_five hKD hnab hC (mem_inner_of_U35 hU) α hα I hI
    exact Or.inr (isU35_of_mulEquiv T _ f.symm hU)

theorem sporPairCase_HN_five (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5) : SporPairCase .HN 5 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ _ hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exact (false_of_sieve hp hp2 h183 hSpM hOrd (downClosed_PHN hOut hBr hKD) isoInv_PHN
    (fun _ _ _ h => dvd_card_of_PHN hOrd h) (Or.inl ⟨MulEquiv.refl _⟩)
    (by simp only [sporOrd, CFSG.Open.orderHN]; norm_num) j0Free_HN hLK hLq hB hBN hname hJ0 hJt hEB
    hEl hE2).elim

end PairHNAssembly

section PairFi23Table

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native
  CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.HardMathSupport.Dickson.I271.TabFi23Y CFSG.YGroups CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.TabFi23
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.RankThree.PartOne.N143.O7 (Om)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi23ShapeRkAt_of_om {G : Type} [Group G] [Finite G] (x : G)
    (hcore : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) = ⊥) (L : Subgroup G)
    (e : ↥L ≃* ↥Om) (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hk : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Nat.card ↥L * 3) :
    ShapeRkAt 3 (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True) x := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* ↥Om) →
      Nonempty (T' ≃* ↥Om) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True :=
    fun _ _ _ _ _ h => h
  have hs : IsSimpleGroup ↥L := tabFi23_isSimpleGroup_of_equiv_om e
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := tabFi23_nonabelian_of_equiv_om e
  have hpL : 3 ∣ Nat.card ↥L := by
    rw [tabFi23_card_of_equiv_om e]
    norm_num
  exact shapeRkAt_of_data_solvable Nat.prime_three hGood hRk x L hLC hLn hs hnab hpL hcore
    (m := 3) hk (by norm_num) ⟨e⟩ trivial


theorem fi23ShapeRkAt_t3_zero : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True) (t3 0) := by
  haveI := finite_J23
  have hcl := t3_classData.1
  have hz : orderOf (t3 0) = 3 := hcl.1
  have hcardC := card_cent_t3_zero
  have h17339 : yCheck orb (dTable orb) (genTables orb (-2)) (t3Tabs orb letters)[0]! y322Ks =
      true := Certificates.certificate17339
  obtain ⟨s, hrel, hnc, hzc⟩ := y322_of_check (rep_t3Tabs 0) h17339
  have hcl' : Subgroup.closure (Set.range s ∪ {t3 0}) ≤
      Subgroup.centralizer ({t3 0} : Set J) := by
    rw [Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | hg)
    · exact cen_iff' (hzc i)
    · rw [Set.mem_singleton_iff.1 hg]
      exact cen_iff' rfl
  have hcard : Nat.card ↥(Subgroup.closure (Set.range s ∪ {t3 0})) ≤ 3 * 4585351680 := by
    have h1 := Subgroup.card_le_of_le hcl'
    rw [hcardC] at h1
    omega
  obtain ⟨⟨e⟩, hLcard, hzL⟩ := tabFi23_y322_recognition s hrel hnc (t3 0) hz hzc hcard
  set L : Subgroup J := Subgroup.closure (Set.range s) with hL
  set N : Subgroup J := Subgroup.closure (Set.range s ∪ {t3 0}) with hN
  set C : Subgroup J := Subgroup.centralizer ({t3 0} : Set J) with hC
  have hLN : L ≤ N := Subgroup.closure_mono Set.subset_union_left
  have hLC : L ≤ C := hLN.trans hcl'
  have hCL : Nat.card C = Nat.card L * 3 := by
    rw [hC, hcardC, hLcard]
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hNC : N = C := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hLN
    have hNd : Nat.card N ∣ Nat.card C := Subgroup.card_dvd_of_le hcl'
    rw [hc, hCL] at hNd
    have hc3 : c ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hLpos hNd
    rcases (Nat.dvd_prime Nat.prime_three).1 hc3 with h1 | h3
    · exfalso
      have hEq : L = N := Subgroup.eq_of_le_of_card_ge hLN (by rw [hc, h1, mul_one])
      apply hzL
      rw [hEq]
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
    · exact Subgroup.eq_of_le_of_card_ge hcl' (by rw [hCL, hc, h3])
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    have hNn : N ≤ Subgroup.normalizer L := by
      rw [hN, Subgroup.closure_le]
      rintro g (⟨i, rfl⟩ | hg)
      · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨i, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hg]
        refine Subgroup.mem_normalizer_iff.2 fun h => ?_
        have hcomm : ∀ l ∈ L, t3 0 * l * (t3 0)⁻¹ = l := fun l hl => by
          have h1 := cen_iff (hLC hl)
          calc t3 0 * l * (t3 0)⁻¹ = (l * t3 0) * (t3 0)⁻¹ := by rw [h1]
            _ = l := by group
        constructor
        · intro hh
          rw [hcomm h hh]
          exact hh
        · intro hh
          have hh' := hcomm _ hh
          have h3 : t3 0 * h * (t3 0)⁻¹ = h := by
            calc t3 0 * h * (t3 0)⁻¹
                = (t3 0)⁻¹ * (t3 0 * (t3 0 * h * (t3 0)⁻¹) * (t3 0)⁻¹) * t3 0 := by group
              _ = (t3 0)⁻¹ * (t3 0 * h * (t3 0)⁻¹) * t3 0 := by rw [hh']
              _ = h := by group
          rw [h3] at hh
          exact hh
    intro g hg l hl
    rw [← hNC] at hg
    exact (Subgroup.mem_normalizer_iff.1 (hNn hg) l).1 hl
  exact fi23ShapeRkAt_of_om (t3 0) (classData_core t3_classData.1) L e hLC hLn hCL


theorem fi23CentShapeRk : CentShapeRk 3 (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True) CFSG.Sporadic.Fi23.J := by
  haveI := finite_J23
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* ↥Om) →
      Nonempty (T' ≃* ↥Om) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hsh : ∀ i : Fin 4, ShapeRkAt 3 (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True) (t3 i) := by
    intro i
    fin_cases i
    · exact fi23ShapeRkAt_t3_zero
    · exact Or.inl pConstrained_t3_one
    · exact Or.inl pConstrained_t3_two
    · exact Or.inl pConstrained_t3_three
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨i, hconj⟩ := fi23_three_classes k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := @ShapeRkAt.of_equiv ↥J ↥J _ finite_J23 inferInstance 3 Nat.prime_three
    (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True) hGood hRk finite_J23 (MulAut.conj c⁻¹) (t3 i)
    (hsh i)
  have hk : (MulAut.conj c⁻¹) (t3 i) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

theorem fi23CentShapeRk_native :
    CentShapeRk 3 (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True)
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) := by
  haveI := finite_J23
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi23 := Finite.of_equiv J (fi23EquivJ.symm.toEquiv)
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* ↥Om) →
      Nonempty (T' ≃* ↥Om) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  exact @CentShapeRk.of_equiv ↥J CFSG.Blueprint.NativeSporadic.Fi23 inferInstance finite_J23
    inferInstance 3 Nat.prime_three (fun T _ => Nonempty (T ≃* ↥Om)) (fun _ _ => True)
    hGood hRk inferInstance fi23EquivJ.symm fi23CentShapeRk

end PairFi23Table

section PairFi23Assembly

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartOne.N143.O7 (Om modelEquiv)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PFi23 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group) ∨ Nonempty (T ≃* ↥Om)

theorem isoInv_PFi23 : IsoInv PFi23 := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

theorem dvd_card_of_PFi23 (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T]
    (h : PFi23 T) : 4585351680 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .Fi23]
    simp only [sporOrd, CFSG.Open.orderFi23]
    norm_num
  · rw [tabFi23_card_of_equiv_om f]

theorem j0Free_Fi23 : J0Free 3 4585351680 (12 * sporOrd .Fi23) := by
  refine j0Free_of_checks (m₀ := 14) (b := 20) (by decide) (by decide) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp only [sporOrd, CFSG.Open.orderFi23]
    decide
  · decide
  · simp only [sporOrd, CFSG.Open.orderFi23]
    decide
  · intro n hn3 hn
    have : n = 3 ∨ n = 4 := by
      rcases Nat.lt_or_ge n 5 with h | h
      · omega
      · have : 5 * 5 ≤ n ^ 2 := by nlinarith
        omega
    rcases this with rfl | rfl
    · rw [spTwoOrd_three]; decide
    · rw [spTwoOrd_four]; decide
  · intro ε m hm3 hm
    have : m = 3 ∨ m = 4 ∨ m = 5 := by
      rcases Nat.lt_or_ge m 6 with h | h
      · omega
      · have : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
        omega
    rcases this with rfl | rfl | rfl
    · rw [omegaOrd_three]; cases ε <;> decide
    · rw [omegaOrd_four]; cases ε <;> decide
    · rw [omegaOrd_five]; cases ε <;> decide

theorem statedModel_of_om {T : Type} [Group T] (e : T ≃* ↥Om) :
    StatedClassicalModel T .POmegaOdd 3 3 1 := by
  refine ⟨⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩, ZMod 3, inferInstance, inferInstance,
    by rw [Nat.card_zmod]; norm_num, ⟨e.trans (modelEquiv (K := ZMod 3) ?_).symm⟩⟩
  rw [Nat.card_zmod]

theorem mem_inner_of_om {T : Type} [Group T] (e : T ≃* ↥Om) (α : MulAut T) (hα : α ^ 3 = 1) :
    α ∈ inner T := by
  by_contra hout
  have := dvd_of_outer_omegaOdd (statedModel_of_om e) Nat.prime_three (by norm_num) hα hout
  omega


theorem downClosed_PFi23 (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : DownClosed 3 PFi23 := by
  intro T _ _ hs hnab hP α hα I hI
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  rcases hP with hT | ⟨⟨e⟩⟩
  · obtain ⟨bF⟩ := hBr .Fi23
    haveI : Finite (NativeSporadic.Carrier .Fi23) := Finite.of_equiv _ (hT.some.trans bF.symm).toEquiv
    exact pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bF
      (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) hRk fi23CentShapeRk_native isoInv_PFi23
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ h => Or.inr h) hnab hT α hα I hI
  · have hC : IsChevSimple 3 T := isChevSimple_of_mulEquiv e.symm tabFi23_isChevSimple_om
    obtain ⟨f⟩ := pSimple_equiv_of_terminal Nat.prime_three hKD hnab hC
      (mem_inner_of_om e) α hα I hI
    exact Or.inr ⟨f.trans e⟩

theorem sporPairCase_Fi23_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : SporPairCase .Fi23 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ _ hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exact (false_of_sieve hp hp2 h183 hSpM hOrd (downClosed_PFi23 hOut hBr hKD) isoInv_PFi23
    (fun _ _ _ h => dvd_card_of_PFi23 hOrd h) (Or.inl ⟨MulEquiv.refl _⟩)
    (by simp only [sporOrd, CFSG.Open.orderFi23]; norm_num) j0Free_Fi23 hLK hLq hB hBN hname hJ0
    hJt hEB hEl hE2).elim

end PairFi23Assembly

section PairThTable

open CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.HardMathSupport.Dickson.Sec6
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.Sporadic.Th
open CFSG.GH74.QTGen4.Recog.G23 (g23Words SatisfiesG23Words Ghat)


theorem thShape_S : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) thS := by
  haveI : Finite ↥J := finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr => (lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨-, hsimp, hnab, hcard⟩ := Chev2Th.leaf_closure_of_six thEps hε hne
  obtain ⟨eG⟩ := nonempty_mulEquiv_adjointG2_of_six thEps hε ⟨0, hne⟩
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hs3 : orderOf thS = 3 := th_orderOf.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thS} : Set ↥J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thS hs3
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    th3_facts.2.2.2.2.2
  refine Chev2Th.shapeRkAt_of_simple_small_index' (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩)
    hs3 hO _ hEC hsimp hnab ?_ ?_ ?_ ⟨eG⟩
  · rw [hcard]; norm_num
  · rw [hcard]
    intro n hn
    interval_cases n <;> decide
  · rw [hcard]; omega

theorem thShape_Z : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) thZ := by
  unfold ShapeRkAt
  left
  have hz : orderOf thZ = 3 := th_orderOf.2.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thZ} : Set ↥CFSG.Sporadic.Th.J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thZ hz
  haveI : Finite ↥CFSG.Sporadic.Th.J := finite_J
  exact pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three card_centralizer_zJ_dvd) hO

theorem thShape_U : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) thU := by
  unfold ShapeRkAt
  left
  refine pConstrainedShape_of_map_injective J.subtype J.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨R, hle, hnorm, hcard, hcent⟩ := th_caseU_spec
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) hcard) hcent

theorem thCentShapeRk : CentShapeRk 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) ↥J := by
  haveI : Finite ↥J := finite_J
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nonempty (T ≃* Ghat) →
      Nonempty (T' ≃* Ghat) := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hS3, hZ3, hU3⟩ := th_orders
  intro k hk1 hkp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨h, c, hc, e, he, hcon⟩ := th_census k hk3
  have hrep : c ^ 3 = 1 ∧ ShapeRkAt 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) c := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨hS3, thShape_S⟩
    · exact ⟨hZ3, thShape_Z⟩
    · exact ⟨hU3, thShape_U⟩
  obtain ⟨hc3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True) (c ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj h) hshape'
  have hk : (MulAut.conj h) (c ^ e) = k := by
    rw [MulAut.conj_apply]
    exact hcon
  rw [hk] at hconj
  exact hconj

theorem thCentShapeRk_native :
    CentShapeRk 3 (fun T _ => Nonempty (T ≃* Ghat)) (fun _ _ => True)
      (NativeSporadic.Carrier .Th) := by
  haveI : Finite ↥J := finite_J
  have e : NativeSporadic.Th ≃* ↥J := thEquivJ
  haveI : Finite NativeSporadic.Th := Finite.of_equiv ↥J e.symm.toEquiv
  exact CentShapeRk.of_equiv (Q := ↥J) (Q' := NativeSporadic.Th) Nat.prime_three
    (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) (fun _ _ _ _ _ h => h) e.symm thCentShapeRk

end PairThTable

section PairThAssembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Dickson.I271
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.GH74.QTGen4.Recog.G23 (Ghat)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def PTh (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Th).Group) ∨ Nonempty (T ≃* Ghat)

theorem isoInv_PTh : IsoInv PTh := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr ⟨e.symm.trans f⟩

theorem j0Free_Th : J0Free 3 4245696 (12 * sporOrd .Th) := by
  refine j0Free_of_checks (m₀ := 11) (b := 17) (by decide) (by decide) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · simp only [sporOrd, CFSG.Open.orderTh]
    decide
  · decide
  · simp only [sporOrd, CFSG.Open.orderTh]
    decide
  · intro n hn3 hn
    have : n = 3 ∨ n = 4 := by
      rcases Nat.lt_or_ge n 5 with h | h
      · omega
      · have : 5 * 5 ≤ n ^ 2 := by nlinarith
        omega
    rcases this with rfl | rfl
    · rw [spTwoOrd_three]; decide
    · rw [spTwoOrd_four]; decide
  · intro ε m hm3 hm
    have : m = 3 ∨ m = 4 := by
      rcases Nat.lt_or_ge m 5 with h | h
      · omega
      · have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
        omega
    rcases this with rfl | rfl
    · rw [omegaOrd_three]; cases ε <;> decide
    · rw [omegaOrd_four]; cases ε <;> decide


theorem dvd_card_of_PTh (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T] (h : PTh T) :
    4245696 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rw [Nat.card_congr f.toEquiv, hOrd .Th]
    simp only [sporOrd, CFSG.Open.orderTh]
    norm_num
  · rw [(leafType_three_of_equiv_adjointG2 f).2.2.2]

theorem mem_inner_of_Ghat {T : Type} [Group T] (e : T ≃* Ghat) (α : MulAut T) (hα : α ^ 3 = 1) :
    α ∈ inner T := by
  by_contra hout
  have h1 : MulAut.congr e α ^ 3 = 1 := congr_pow_eq_one e hα
  have h2 : MulAut.congr e α ∉ inner Ghat := congr_not_inner e hout
  have := dvd_of_outer_adjoint (τ := .G2) (Or.inl rfl) Nat.prime_three (by norm_num) le_rfl
    (ZMod 3) (by rw [Nat.card_zmod, pow_one]) (MulAut.congr e α) h1 h2
  omega

theorem downClosed_PTh (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : DownClosed 3 PTh := by
  intro T _ _ hs hnab hP α hα I hI
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  rcases hP with hT | ⟨⟨e⟩⟩
  · obtain ⟨bT⟩ := hBr .Th
    haveI : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv _ (hT.some.trans bT.symm).toEquiv
    exact pSimple_of_sporShape Nat.prime_three (by norm_num) hOut bT
      (fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩) hRk thCentShapeRk_native isoInv_PTh
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ h => Or.inr h) hnab hT α hα I hI
  · have hC0 := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted.isChevSimple_adjoint
      .G2 (Or.inl rfl) Nat.prime_three (by norm_num) (d := 1) le_rfl (ZMod 3)
      (by rw [Nat.card_zmod, pow_one])
    have hC : IsChevSimple 3 T := isChevSimple_of_mulEquiv e.symm hC0
    obtain ⟨f⟩ := pSimple_equiv_of_terminal Nat.prime_three hKD hnab hC
      (mem_inner_of_Ghat e) α hα I hI
    exact Or.inr ⟨f.trans e⟩

theorem sporPairCase_Th_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) : SporPairCase .Th 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ _ hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  exact (false_of_sieve hp hp2 h183 hSpM hOrd (downClosed_PTh hOut hBr hKD) isoInv_PTh
    (fun _ _ _ h => dvd_card_of_PTh hOrd h) (Or.inl ⟨MulEquiv.refl _⟩)
    (by simp only [sporOrd, CFSG.Open.orderTh]; norm_num) j0Free_Th hLK hLq hB hBN hname hJ0
    hJt hEB hEl hE2).elim

end PairThAssembly

section JZeroClosure

open CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

@[expose] def AltOrChevTwo (T : Type) [Group T] : Prop :=
  (∃ m : ℕ, 5 ≤ m ∧ Nonempty (T ≃* alternatingGroup (Fin m))) ∨ IsChevSimple 2 T

theorem isoInv_altOrChevTwo : IsoInv AltOrChevTwo := by
  intro T T' _ _ e h
  rcases h with ⟨m, hm, ⟨f⟩⟩ | hC
  · exact Or.inl ⟨m, hm, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e hC)

theorem downClosed_altOrChevTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p 2) : DownClosed p AltOrChevTwo := by
  intro S _ _ hs hnab hP α hα I hI
  rcases hP with ⟨m, hm, ⟨e⟩⟩ | hC
  · by_cases hα1 : α = 1
    · subst hα1
      rw [fixSubgroup_one_eq_top'] at hI
      obtain ⟨f⟩ := chevQ_pSimple_top_equiv hp hnab hI
      exact Or.inl ⟨m, hm, ⟨f.trans e⟩⟩
    · obtain ⟨hI', ⟨g⟩⟩ := chevQ_transport hp e hI
      have hβ : MulAut.congr e α ^ p = 1 := congr_pow_eq_one e hα
      have hβ1 : MulAut.congr e α ≠ 1 := fun h => hα1 (by
        have h2 := congrArg (MulAut.congr e).symm h
        rwa [MulEquiv.symm_apply_apply, map_one] at h2)
      obtain ⟨m', hm', -, ⟨f⟩⟩ := kdAltDown_holds m p hm hp hp2 _ hβ hβ1 _ hI'
      exact Or.inl ⟨m', le_trans (le_max_left 5 p) hm', ⟨g.trans f⟩⟩
  · exact Or.inr (hD2 S hs hnab hC α hα I hI)

noncomputable def projEquivTwo {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι (ZMod 2))) :
    ↥H ≃* StatedProj H :=
  ((QuotientGroup.quotientMulEquivOfEq (by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot).symm


theorem j0_trichotomy {p : ℕ} (hp3 : 3 ≤ p) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (hT : J0Type p Y) :
    (Subgroup.center Y = ⊥ ∧ AltOrChevTwo Y) ∨ Nat.card Y ∣ 720 ∨ Nat.card Y = 20160 ∨
      Nat.card Y = 25920 ∨ Nat.card Y = 60 := by
  have halt : ∀ m, (m ≤ 2 ∨ 5 ≤ m) → IsAltType m Y →
      (Subgroup.center Y = ⊥ ∧ AltOrChevTwo Y) := by
    intro m hm5 ⟨e⟩
    rcases hm5 with hm | hm
    · exfalso
      haveI : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.toNontrivial
      have hnt : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
      have h1 : 1 < Nat.card Y := Finite.one_lt_card_iff_nontrivial.2 hnt
      rcases card_altType ⟨e⟩ with h | ⟨h2, h⟩
      · omega
      · have hm2 : m = 2 := by omega
        subst hm2
        rw [h] at h1
        norm_num [Nat.factorial] at h1
    · have hc : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
        alternatingGroup.center_eq_bot (by simp; omega)
      refine ⟨?_, Or.inl ⟨m, hm, ⟨e⟩⟩⟩
      rw [← Subgroup.map_center_eq e.symm, hc, Subgroup.map_bot]
  rcases hT with ⟨k, hk5, hk⟩ | ⟨k, hk⟩ | ⟨ε, n, -, -, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, -⟩
  · exact Or.inl (halt _ (Or.inr hk5) hk)
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl (halt _ (Or.inl (by omega)) hk)
    · have : 5 ≤ k * p + 2 := by nlinarith
      exact Or.inl (halt _ (Or.inr this) hk)
  · rcases card_spTwo e with ⟨hn3, -⟩ | ⟨-, hc⟩
    · left
      have hperf : Group.IsPerfect ↥(StatedSp n (ZMod 2)) :=
        CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n := n) (K := ZMod 2)
          (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn3⟩))
      let e1 : Y ≃* StatedProj (StatedSp n (ZMod 2)) :=
        (e.trans (MulEquiv.subgroupCongr (commutator_self_eq_of_perfect hperf))).trans
          (projEquivTwo _)
      have hM : StatedClassicalModel Y .PSp n 2 1 :=
        ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega⟩, ZMod 2, inferInstance,
          inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨e1⟩⟩
      haveI := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y n 2 1 hM
      have hnab : ∃ a b : Y, a * b ≠ b * a :=
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq |>.elim
          fun a ha => by
            obtain ⟨b, hb⟩ := ha
            obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) a
            obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) b
            exact ⟨x, y, fun h => hb (by rw [← map_mul, ← map_mul, h])⟩
      exact ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab,
        Or.inr (CFSG.LocalAnalysis.GLTheoremA.conv_B (r := n) (n := 1) (by omega) (fun h => by omega)
          le_rfl (Or.inl ⟨by simp [classicalTags], hM⟩))⟩
    · exact Or.inr (Or.inl hc)
  · rcases OmegaFacts.omega_data hΩ with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, hsol, -⟩ | ⟨-, -, h60, -⟩ |
        ⟨hn2, hc, -, -⟩
    · omega
    · omega
    · exact (not_isSolvable_of_isQuasisimple' hq hsol).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr h60)))
    · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · right
        rw [hc, omegaOrd_three]
        cases ε
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inl rfl)
      · left
        have hnab : ∀ [IsSimpleGroup Y], ∃ a b : Y, a * b ≠ b * a := fun {_} => by
          obtain ⟨a, b, hb⟩ :=
            CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) b
          exact ⟨x, y, fun h => hb (by rw [← map_mul, ← map_mul, h])⟩
        cases ε
        · obtain ⟨e⟩ := hΩ
          have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
          have hM : StatedClassicalModel Y .POmegaMinus (n + 1) 2 1 :=
            ⟨⟨Nat.prime_two, le_rfl, by omega⟩, ZMod 2, inferInstance, inferInstance,
              by rw [Nat.card_zmod]; norm_num, 1, 1, hirr, ⟨e.trans (projEquivTwo _)⟩⟩
          haveI := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
            Y (n + 1) 2 1 hM).2
          exact ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab,
            Or.inr (CFSG.LocalAnalysis.GLTheoremA.chev2Minus_holds Y (n + 1) 1 (by omega) le_rfl
              (Or.inl ⟨by simp [classicalTags], hM⟩))⟩
        · obtain ⟨e⟩ := hΩ
          have hM : StatedClassicalModel Y .POmegaPlus (n + 1) 2 1 :=
            ⟨⟨Nat.prime_two, le_rfl, by omega⟩, ZMod 2, inferInstance, inferInstance,
              by rw [Nat.card_zmod]; norm_num, ⟨e.trans (projEquivTwo _)⟩⟩
          haveI := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
            Y (n + 1) 2 1 hM).2
          exact ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab,
            Or.inr (CFSG.LocalAnalysis.GLTheoremA.conv_Dp (r := n + 1) (n := 1) (by omega) le_rfl
              (Or.inl ⟨by simp [classicalTags], hM⟩))⟩

end JZeroClosure

section NotTop

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g : G, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 hz g)
  have hw' : ∀ g : G, g * w = w * g := fun g => (Subgroup.mem_center_iff.1 hw g)
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w)) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * (b * w * z) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by rw [hz' (b * w)]
    _ = a * b * (w * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * w) * (w⁻¹ * b⁻¹) := by rw [hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem not_dvd_card_pSimple_of_centralizer {L E J : Subgroup X} (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) ∣ 12)
    (h12 : ¬ Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.factorial 12)
    (hE : ¬ E ≤ Subgroup.centralizer (L : Set X))
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set X)) J) :
    ¬ Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card (PSimple p J) := by
  intro hd
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  set C : Subgroup X := L ⊓ Subgroup.centralizer (E : Set X) with hCdef
  have hCL : C ≤ L := inf_le_left
  have hdC : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card C :=
    hd.trans ((card_pSimple_dvd p J).trans (Subgroup.card_dvd_of_le hJ.1))
  set C' : Subgroup ↥L := C.subgroupOf L with hC'def
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCL).toEquiv
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  set H : Subgroup (↥L ⧸ Subgroup.center ↥L) := C'.map π with hHdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hLcard : Nat.card ↥L = Nat.card (Subgroup.center ↥L) * Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rw [← Subgroup.card_mul_index (Subgroup.center ↥L), Subgroup.index_eq_card]
  have hC'pos : 0 < Nat.card C' := Nat.card_pos
  have hidxC : C'.index ≤ Nat.card (Subgroup.center ↥L) := by
    have h1 := C'.card_mul_index
    have h2 : Nat.card (↥L ⧸ Subgroup.center ↥L) ≤ Nat.card C' := by
      rw [hC'card]; exact Nat.le_of_dvd Nat.card_pos hdC
    rw [hLcard] at h1
    by_contra hlt
    push Not at hlt
    have : Nat.card C' * Nat.card (Subgroup.center ↥L) < Nat.card C' * C'.index :=
      Nat.mul_lt_mul_of_pos_left hlt hC'pos
    nlinarith
  have hidxH : H.index ≤ 12 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) (C'.index_map_dvd hπs)).trans
      (hidxC.trans (Nat.le_of_dvd (by norm_num) hZ))
  by_cases hHt : H = ⊤
  ·
    apply hE
    have hcomm : commutator ↥L ≤ C' := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      have ha : π a ∈ H := hHt ▸ Subgroup.mem_top _
      have hb : π b ∈ H := hHt ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hca⟩ := ha
      obtain ⟨d, hd', hdb⟩ := hb
      have hza : c⁻¹ * a ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq]; exact hca
      have hzb : d⁻¹ * b ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq]; exact hdb
      have h1 : a = c * (c⁻¹ * a) := by group
      have h2 : b = d * (d⁻¹ * b) := by group
      rw [h1, h2, commutatorElement_mul_central hza hzb]
      exact Subgroup.commutator_mem_commutator hc hd' |> fun h => by
        have : ⁅c, d⁆ ∈ C' := C'.mul_mem (C'.mul_mem (C'.mul_mem hc hd') (C'.inv_mem hc)) (C'.inv_mem hd')
        exact this
    have htop : C' = ⊤ := top_le_iff.1 (hLq.1 ▸ hcomm)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlC : (⟨l, hl⟩ : ↥L) ∈ C' := htop ▸ Subgroup.mem_top _
    have hlE : l ∈ Subgroup.centralizer (E : Set X) := (Subgroup.mem_subgroupOf.1 hlC).2
    exact (Subgroup.mem_centralizer_iff.1 hlE e he).symm
  ·
    have hcore : H.normalCore = ⊥ := by
      haveI := Subgroup.normalCore_normal H
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
      · exact h
      · exact absurd (top_le_iff.1 (h ▸ Subgroup.normalCore_le H)) hHt
    have h1 := H.index_normalCore_dvd_factorial_index
    rw [hcore, Subgroup.index_bot] at h1
    exact h12 (h1.trans (Nat.factorial_dvd_factorial hidxH))

end NotTop

section Sieve2

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem map_conj_le_gamma {L B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X)) {b : X} (hb : b ∈ B) :
    (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)).map (MulAut.conj b).toMonoidHom ≤
      ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun U => iSup_le fun hU => iSup_le fun hU2 => ?_
  intro x hx
  have hbU : b ∈ Subgroup.normalizer (U : Set X) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_of_elem hB hU hb)
  have h1 : b * x * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hBN hb) x).1 hx.1
  have h2 : b * x * b⁻¹ ∈ Subgroup.normalizer (U : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hbU hx.2) (Subgroup.inv_mem _ hbU)
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hle : L ⊓ Subgroup.normalizer (U : Set X) ≤
      ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X) :=
    le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le hU2 le_rfl))
  exact hle ⟨h1, h2⟩

theorem le_normalizer_of_component (hp : p.Prime) {L B J0 E J : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hJ0 : CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X))) (hEB : E ≤ B)
    (hJ : GLAPComponent p (J0 ⊓ Subgroup.centralizer (E : Set X)) J) :
    E ≤ Subgroup.normalizer (J0 : Set X) := by
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    L ⊓ Subgroup.normalizer (U : Set X) with hΓdef
  intro e he
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hbinv : e⁻¹ ∈ B := B.inv_mem (hEB he)
  have hΓ : Γ.map (MulAut.conj e⁻¹).toMonoidHom = Γ := by
    refine Subgroup.eq_of_le_of_card_ge (map_conj_le_gamma hB hBN hbinv) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj e⁻¹).injective]
  have hJ' : CFSG.Open.IsComponentOf (GLBConj e J0) Γ := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj e⁻¹) hJ0
    have hc : ((MulAut.conj e⁻¹ : MulAut X) : X →* X) = (MulAut.conj e⁻¹).toMonoidHom := rfl
    rw [hc, hΓ] at h
    exact h
  have hcomm := CFSG.Quasithin.F918V3S1.comp_commute hJ0 hJ' (Ne.symm hne)
  have hJJ0 : J ≤ J0 := hJ.1.trans inf_le_left
  have hJJ' : J ≤ GLBConj e J0 := by
    intro y hy
    have hyE : y ∈ Subgroup.centralizer (E : Set X) := (hJ.1 hy).2
    have hey : e * y = y * e := Subgroup.mem_centralizer_iff.1 hyE e he
    refine ⟨y, hJJ0 hy, ?_⟩
    show (MulAut.conj e⁻¹) y = y
    rw [MulAut.conj_apply, inv_inv]
    calc e⁻¹ * y * e = e⁻¹ * (e * y) := by rw [hey, mul_assoc]
      _ = y := by group
  obtain ⟨-, hnab⟩ := chev_pSimple_simple_nonabelian hp hJ
  obtain ⟨a, b, hab⟩ := hnab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) a'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) b'
  apply hab
  have hxy : x * y = y * x := Subtype.ext (hcomm x (hJJ0 x.2) y (hJJ' y.2))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hxy]

theorem dvd_card_pSimple (hp : p.Prime) {Y J : Subgroup X} (hJ : GLAPComponent p Y J) :
    p ∣ Nat.card (PSimple p J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hs, hnab⟩ := chev_pSimple_simple_nonabelian hp hJ
  by_contra hnd
  have hbot := glaPPrimeCore_pSimple_eq_bot hp hJ
  have hle : (⊤ : Subgroup (PSimple p J)) ≤ GLAPPrimeCore p (PSimple p J) := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact (hp.coprime_iff_not_dvd).2 hnd
  rw [hbot, top_le_iff] at hle
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  have ha : a = 1 := by rw [← Subgroup.mem_bot, hle]; trivial
  have hb : b = 1 := by rw [← Subgroup.mem_bot, hle]; trivial
  rw [ha, hb]


theorem false_of_sieve2 (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p 2)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) {P : ∀ (T : Type) [Group T], Prop} (hD : DownClosed p P)
    (hinv : IsoInv P) {N : ℕ} (hPN : ∀ (T : Type) [Group T] [Finite T], P T → N ∣ Nat.card T)
    (hsmall : ¬ N ∣ 720 ∧ ¬ N ∣ 20160 ∧ ¬ N ∣ 25920 ∧ ¬ N ∣ 60)
    {name : TauCeti.SporadicName}
    (hdisj : ∀ (T : Type) [Group T] [Finite T], P T → AltOrChevTwo T → ¬ sporOrd name ∣ Nat.card T →
      False)
    (hPS : P (TauCeti.CFSGIndex.sporadic name).Group) (hpS : p ∣ sporOrd name)
    (h12 : ¬ sporOrd name ∣ Nat.factorial 12)
    {L B J0 E : Subgroup X} (hLK : CFSG.IsKGroup ↥L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (L : Set X))
    (hC1 : CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (L : Set X)) ≤ 1)
    (hname : IsSporType name (↥L ⧸ Subgroup.center ↥L))
    (hJ0 : CFSG.Open.IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      L ⊓ Subgroup.normalizer (U : Set X))) (hJt : J0Type p ↥J0) (hEB : E ≤ B)
    (hEl : GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) (hE2 : 2 ≤ CFSG.Open.pRank p E) :
    False := by
  set Γ := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    L ⊓ Subgroup.normalizer (U : Set X) with hΓ
  obtain ⟨J, hJ⟩ := Inputs2711.exists_glaPComponent_of_ne_bot hEl
  have hΓL : Γ ≤ L := iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hJ0L : J0 ≤ L := hJ0.1.trans hΓL
  have hLE : L ⊓ Subgroup.centralizer (E : Set X) ≤ Γ :=
    le_iSup_of_le E (le_iSup_of_le hEB (le_iSup_of_le hE2
      (inf_le_inf_left L (Subgroup.centralizer_le_normalizer _))))
  have hsn : IsSubnormal (J0 ⊓ Subgroup.centralizer (E : Set X))
      (L ⊓ Subgroup.centralizer (E : Set X)) := by
    have h1 := hJ0.2.1.inf (L ⊓ Subgroup.centralizer (E : Set X))
    rwa [inf_eq_right.2 hLE, ← inf_assoc, inf_eq_left.2 hJ0L] at h1
  have hJL : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set X)) J :=
    glaPComponent_of_isSubnormal' hp hsn hJ
  have hLK' : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  obtain ⟨eS⟩ := hname
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  have hcardS : Nat.card (↥L ⧸ Subgroup.center ↥L) = sporOrd name :=
    (Nat.card_congr eS.toEquiv).trans (hOrd name)
  have hpLZ : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := hcardS ▸ hpS
  have hLL : GLAPComponent p L L := S10.glaPComponent_of_quasisimple hp (IsSubnormal.refl L) hLq hpLZ
  have hnabL : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLq
  obtain ⟨ePL⟩ := pSimple_equiv_of_surjective_simple hp hLL hnabL
    (glaPPrimeCore_eq_bot_of_simple hp hpLZ) (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _)
  have hPL : P (PSimple p L) := hinv _ _ (ePL.trans eS).symm hPS
  have hEel : IsElemAbelian p E := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB hEB
  have hPJ : P (PSimple p J) :=
    typeClosure hp hp2 hD hinv h183 hLK' hLL hPL hEel (hEB.trans hBN) hJL
  have hJJ0 : J ≤ J0 := hJ.1.trans inf_le_left
  have hN : N ∣ Nat.card J0 :=
    (hPN _ hPJ).trans ((card_pSimple_dvd p J).trans (Subgroup.card_dvd_of_le hJJ0))
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hp.two_le
      obtain ⟨k, hk⟩ := h
      omega
  have hq0 : CFSG.Open.IsQuasisimple ↥J0 := hJ0.2.2
  rcases j0_trichotomy hp3 hq0 hJt with ⟨hZ, hA0⟩ | h720 | h20160 | h25920 | h60
  ·
    have hEN : E ≤ Subgroup.normalizer (J0 : Set X) := le_normalizer_of_component hp hB hBN hJ0 hEB hJ
    have eZ : (↥J0 ⧸ Subgroup.center ↥J0) ≃* ↥J0 :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    haveI hs0 : IsSimpleGroup ↥J0 := eZ.isSimpleGroup_congr.1 hq0.2
    have hnab0 : ∃ a b : ↥J0, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq0
      exact ⟨eZ a, eZ b, fun h => hab (eZ.injective (by rw [map_mul, map_mul, h]))⟩
    have hpJ0 : p ∣ Nat.card ↥J0 :=
      (dvd_card_pSimple hp hJ).trans ((card_pSimple_dvd p J).trans (Subgroup.card_dvd_of_le hJJ0))
    have hpJ0Z : p ∣ Nat.card (↥J0 ⧸ Subgroup.center ↥J0) := by
      rw [Nat.card_congr eZ.toEquiv]; exact hpJ0
    have hJ0J0 : GLAPComponent p J0 J0 :=
      S10.glaPComponent_of_quasisimple hp (IsSubnormal.refl J0) hq0 hpJ0Z
    obtain ⟨eP0⟩ := pSimple_equiv_of_surjective_simple hp hJ0J0 hnab0
      (glaPPrimeCore_eq_bot_of_simple hp hpJ0) (MonoidHom.id ↥J0) Function.surjective_id
    have hPJ0 : AltOrChevTwo (PSimple p J0) := isoInv_altOrChevTwo _ _ eP0.symm hA0
    have hJ0K : CFSG.Open.IsKGroup ↥J0 := CFSG.Open.IsKGroup.of_le hLK' hJ0L
    have hAJ : AltOrChevTwo (PSimple p J) :=
      typeClosure hp hp2 (downClosed_altOrChevTwo hp hp2 hD2) isoInv_altOrChevTwo h183 hJ0K hJ0J0
        hPJ0 hEel hEN hJ
    have hZ12 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hLq name eS
    have hEnot : ¬ E ≤ Subgroup.centralizer (L : Set X) := by
      obtain ⟨e, he, heC⟩ := Inputs2711b.exists_not_mem_centralizer hp hEB hE2 hC1
      exact fun h => heC (h he)
    have hnotS : ¬ sporOrd name ∣ Nat.card (PSimple p J) := by
      rw [← hcardS]
      exact not_dvd_card_pSimple_of_centralizer hLq hZ12 (by rw [hcardS]; exact h12) hEnot hJL
    exact hdisj _ hPJ hAJ hnotS
  · exact hsmall.1 (hN.trans h720)
  · exact hsmall.2.1 (h20160 ▸ hN)
  · exact hsmall.2.2.1 (h25920 ▸ hN)
  · exact hsmall.2.2.2 (h60 ▸ hN)

end Sieve2

section Exclusions

open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

theorem not_alt_of_card {T : Type} [Group T] {N m₀ : ℕ} (hT : Nat.card T = N) (hm₀ : 2 ≤ m₀)
    (hM : ¬ m₀.factorial / 2 ∣ N) (hA : ∀ m < m₀, 2 ≤ m → m.factorial / 2 ≠ N) :
    ¬ ∃ m : ℕ, 5 ≤ m ∧ Nonempty (T ≃* alternatingGroup (Fin m)) := by
  rintro ⟨m, hm, ⟨e⟩⟩
  rcases card_altType ⟨e⟩ with h | ⟨h2, h⟩
  · have : m.factorial / 2 = 1 := by
      haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [← h, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
    have h5 : (5 : ℕ).factorial / 2 ≤ m.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le hm)
    norm_num [Nat.factorial] at h5
    omega
  · rw [h] at hT
    rcases Nat.lt_or_ge m m₀ with hlt | hge
    · exact hA m hlt h2 hT
    · exact hM (hT ▸ factorial_half_dvd hm₀ hge)

theorem not_altOrChevTwo_U35 (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 126000) : ¬ AltOrChevTwo T := by
  rintro (h | h)
  · exact not_alt_of_card hT (m₀ := 10) (by norm_num) (by decide) (by decide) h
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (a := 4) (m := 7875)
      (by rw [hT]; norm_num) (by decide) (by norm_num) (by decide) h

theorem not_altOrChevTwo_HN (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 273030912000000) : ¬ AltOrChevTwo T := by
  rintro (h | h)
  · exact not_alt_of_card hT (m₀ := 13) (by norm_num) (by decide) (by decide) h
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (a := 14)
      (m := 16664484375) (by rw [hT]; norm_num) (by decide) (by norm_num) (by decide) h

theorem not_altOrChevTwo_U43 (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 3265920) : ¬ AltOrChevTwo T := by
  rintro (h | h)
  · exact not_alt_of_card hT (m₀ := 10) (by norm_num) (by decide) (by decide) h
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.not_isChevSimple_two_of_card hb (a := 7)
      (m := 25515) (by rw [hT]; norm_num) (by decide) (by norm_num) (by decide) h

theorem not_altOrChevTwo_Fi22 (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 64561751654400) : ¬ AltOrChevTwo T := by
  rintro (h | h)
  · exact not_alt_of_card hT (m₀ := 14) (by norm_num) (by decide) (by decide) h
  · exact CFSG.HardMathSupport.Dickson.BMRows.not_isChevSimple_of_card_fi22 hb hT 2 h

end Exclusions

section SporCensus

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)

theorem pSimple_of_sporCensus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (htab : ∀ x : Q, orderOf x = p → ∀ J : Subgroup Q,
      GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J → Good (PSimple p J))
    {P : ∀ (T : Type) [Group T], Prop} (hinv : IsoInv P)
    (hPS : P (TauCeti.CFSGIndex.sporadic s).Group) (hGP : ∀ (T : Type) [Group T], Good T → P T)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hT : Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic s).Group)) (α : MulAut T) (hα : α ^ p = 1)
    (I : Subgroup T) (hI : GLAPComponent p (fixSubgroup α) I) : P (PSimple p I) := by
  obtain ⟨e⟩ := hT
  have hcen : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout := hOut T inferInstance hnab s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hcen hout α hα
  by_cases hx1 : x = 1
  · subst hx1
    rw [map_one, fixSubgroup_one_eq_top'] at hI
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv hp hnab hI
    exact hinv _ _ (f.trans e).symm hPS
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [fixSubgroup_conj_eq'] at hI
    let φ : T ≃* Q := e.trans b.symm
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    have hφo : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq, hxo]
    have hI' := glaPComponent_map_equiv hp φ hI
    rw [map_centralizer_singleton φ x] at hI'
    have hG := htab (φ x) hφo _ hI'
    exact hGP _ (hGood _ _ (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv p
      (I.equivMapOfInjective φ.toMonoidHom φ.injective)).symm hG)

theorem isKGroup_carrier {X : Type} [Group X] {L : Subgroup X} (hLK : CFSG.IsKGroup ↥L)
    {s : TauCeti.SporadicName} (hname : IsSporType s (↥L ⧸ Subgroup.center ↥L))
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CFSG.Open.IsKGroup (NativeSporadic.Carrier s) := by
  obtain ⟨eS⟩ := hname
  have h1 : CFSG.Open.IsKGroup ↥L := CFSG.KCore.KGroupAllSimple.kGroupNonab hLK
  have h2 := h1.of_surjective (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  have h3 := h2.of_surjective eS.toMonoidHom eS.surjective
  exact h3.of_surjective (hBr s).some.symm.toMonoidHom (hBr s).some.symm.surjective

end SporCensus

section PairsBM

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)

@[expose] def PM5 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .M).Group) ∨ PHN T

theorem isoInv_PM5 : IsoInv PM5 := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | h
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (isoInv_PHN T T' e h)

theorem dvd_card_of_PM5 (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T] (h : PM5 T) :
    126000 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | h
  · rw [Nat.card_congr f.toEquiv, hOrd .M]
    simp only [sporOrd, CFSG.Open.orderMonster]
    norm_num
  · exact dvd_card_of_PHN hOrd h

theorem disj_PM5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) (T : Type) [Group T] [Finite T]
    (hP : PM5 T) (hA : AltOrChevTwo T) (hnd : ¬ sporOrd .M ∣ Nat.card T) : False := by
  rcases hP with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | hU
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .M])
  · exact not_altOrChevTwo_HN hb (by
      rw [Nat.card_congr f.toEquiv, hOrd .HN]
      simp only [sporOrd, CFSG.Open.orderHN]
      norm_num) hA
  · exact not_altOrChevTwo_U35 hb
      (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five hU) hA

@[expose] def PB3 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .B).Group) ∨ PFi22 T

theorem isoInv_PB3 : IsoInv PB3 := by
  intro T T' _ _ e h
  rcases h with ⟨⟨f⟩⟩ | h
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (isoInv_PFi22 T T' e h)

theorem dvd_card_of_PB3 (hOrd : SporadicOrdersTable) {T : Type} [Group T] [Finite T] (h : PB3 T) :
    3265920 ∣ Nat.card T := by
  rcases h with ⟨⟨f⟩⟩ | h
  · rw [Nat.card_congr f.toEquiv, hOrd .B]
    simp only [sporOrd, CFSG.Open.orderBabyMonster]
    norm_num
  · exact dvd_card_of_PFi22 hOrd h

theorem disj_PB3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) (T : Type) [Group T] [Finite T]
    (hP : PB3 T) (hA : AltOrChevTwo T) (hnd : ¬ sporOrd .B ∣ Nat.card T) : False := by
  rcases hP with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact hnd (by rw [Nat.card_congr f.toEquiv, hOrd .B])
  · exact not_altOrChevTwo_Fi22 hb (by rw [Nat.card_congr f.toEquiv, hOrd .Fi22]; rfl) hA
  · exact not_altOrChevTwo_U43 hb
      (by rw [Nat.card_congr f.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]) hA

end PairsBM

section PairM5

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)


theorem downClosed_PM5 (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5)
    (hcen : PCompCensus 5 (NativeSporadic.Carrier .M) (· = .sporadic .HN)) : DownClosed 5 PM5 := by
  intro T _ _ hs hnab hP α hα I hI
  rcases hP with hT | hH
  · obtain ⟨bM⟩ := hBr .M
    haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv _ (hT.some.trans bM.symm).toEquiv
    exact pSimple_of_sporCensus Nat.prime_five (by norm_num) hOut bM
      (Good := fun T _ => CFSG.Yardstones.Md0ec50421ce4.catalogIs T (· = .sporadic .HN))
      (fun _ _ _ _ e ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.symm.trans f⟩⟩) hcen isoInv_PM5
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ ⟨i, hi, hf⟩ => by subst hi; exact Or.inr (Or.inl hf))
      hnab hT α hα I hI
  · exact Or.inr (downClosed_PHN hOut hBr hKD T hs hnab hH α hα I hI)

theorem sporPairCase_M_five (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 2)
    (hcen : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M) →
      PCompCensus 5 (NativeSporadic.Carrier .M) (· = .sporadic .HN)) : SporPairCase .M 5 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ hC1 hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  have hKM := isKGroup_carrier hLK hname hBr
  exact (false_of_sieve2 hp hp2 h183 hD2 hSpM hOrd (downClosed_PM5 hOut hBr hKD (hcen hKM)) isoInv_PM5
    (fun _ _ _ h => dvd_card_of_PM5 hOrd h) (by decide) (disj_PM5 hOrd hb)
    (Or.inl ⟨MulEquiv.refl _⟩) (by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num)
    (fun h => absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderMonster]; norm_num [Nat.factorial]))
    hLK hLq hB hBN hC1 hname hJ0 hJt hEB hEl hE2).elim

end PairM5

section PairB3

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)


theorem downClosed_PB3 (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3)
    (hcen : PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22)) : DownClosed 3 PB3 := by
  intro T _ _ hs hnab hP α hα I hI
  rcases hP with hT | hF
  · obtain ⟨bB⟩ := hBr .B
    haveI : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv _ (hT.some.trans bB.symm).toEquiv
    exact pSimple_of_sporCensus Nat.prime_three (by norm_num) hOut bB
      (Good := fun T _ => CFSG.Yardstones.Md0ec50421ce4.catalogIs T (· = .sporadic .Fi22))
      (fun _ _ _ _ e ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨e.symm.trans f⟩⟩) hcen isoInv_PB3
      (Or.inl ⟨MulEquiv.refl _⟩) (fun _ _ ⟨i, hi, hf⟩ => by subst hi; exact Or.inr (Or.inl hf))
      hnab hT α hα I hI
  · exact Or.inr (downClosed_PFi22 hOut hBr hKD T hs hnab hF α hα I hI)

theorem sporPairCase_B_three (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hKD : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3) (hb : LieOrderBridge)
    (hD2 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hcen : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22)) : SporPairCase .B 3 := by
  intro X _ _ hp hp2 L B hLK hLq hB hBN _ _ _ _ _ hC1 hname _ J0 hJ0 hJt _ E hEB _ _ hEl hE2 _ _
  have hKB := isKGroup_carrier hLK hname hBr
  exact (false_of_sieve2 hp hp2 h183 hD2 hSpM hOrd (downClosed_PB3 hOut hBr hKD (hcen hKB)) isoInv_PB3
    (fun _ _ _ h => dvd_card_of_PB3 hOrd h) (by decide) (disj_PB3 hOrd hb)
    (Or.inl ⟨MulEquiv.refl _⟩) (by simp only [sporOrd, CFSG.Open.orderBabyMonster]; norm_num)
    (fun h => absurd (Nat.le_of_dvd (Nat.factorial_pos 12) h)
      (by simp only [sporOrd, CFSG.Open.orderBabyMonster]; norm_num [Nat.factorial]))
    hLK hLq hB hBN hC1 hname hJ0 hJt hEB hEl hE2).elim

end PairB3

section Assembly

open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges SporadicOnePair)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd LieOrderBridge)
open CFSG.HardMathSupport.Dickson.BMRows (PCompCensus)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (Input18_3_4)

structure SporPairsResidual : Prop where
  J3_three : SporPairCase .J3 3
  Suz_three : SporPairCase .Suz 3
  ONan_three : SporPairCase .ONan 3
  Co3_three : SporPairCase .Co3 3
  Co2_three : SporPairCase .Co2 3
  Co1_three : SporPairCase .Co1 3
  Fi24Prime_three : SporPairCase .Fi24Prime 3
  HN_three : SporPairCase .HN 3
  M_three : SporPairCase .M 3
  Co1_five : SporPairCase .Co1 5
  B_five : SporPairCase .B 5
  M_seven : SporPairCase .M 7


theorem inputI2711SporPairs_of_residual (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hMcL : ConstrainedShape .McL 3) (hKD3 : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3)
    (hKD5 : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5) (hb : LieOrderBridge)
    (hD32 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hD52 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 2)
    (hcenB : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22))
    (hcenM : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M) →
      PCompCensus 5 (NativeSporadic.Carrier .M) (· = .sporadic .HN)) (h : SporPairsResidual) :
    Inputs2711b.InputI2711SporPairs := by
  refine inputI2711SporPairs_of_cases fun name p hpair hMcL' hLy' => ?_
  rcases hpair with ⟨rfl, hmem⟩ | ⟨rfl, hmem⟩ | ⟨rfl, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact h.J3_three
    · exact (hMcL' ⟨rfl, rfl⟩).elim
    · exact h.Suz_three
    · exact h.ONan_three
    · exact h.Co3_three
    · exact h.Co2_three
    · exact h.Co1_three
    · exact sporPairCase_Fi22_three h183 hSpM hOrd hOut hBr hKD3
    · exact sporPairCase_Fi23_three h183 hSpM hOrd hOut hBr hKD3
    · exact h.Fi24Prime_three
    · exact h.HN_three
    · exact sporPairCase_Ly_three h183 hSpM hOrd hOut hBr hMcL
    · exact sporPairCase_Th_three h183 hSpM hOrd hOut hBr hKD3
    · exact sporPairCase_B_three h183 hSpM hOrd hOut hBr hKD3 hb hD32 hcenB
    · exact h.M_three
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl
    · exact h.Co1_five
    · exact sporPairCase_HN_five h183 hSpM hOrd hOut hBr hKD5
    · exact (hLy' ⟨rfl, rfl⟩).elim
    · exact h.B_five
    · exact sporPairCase_M_five h183 hSpM hOrd hOut hBr hKD5 hb hD52 hcenM
  · exact h.M_seven

theorem inputI2711Rest_of_residual (hGA : CFSG.Open.GriessAllModelsStatement) (h183 : Input18_3_4)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hMcL : ConstrainedShape .McL 3) (hKD3 : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3)
    (hKD5 : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 5) (hb : LieOrderBridge)
    (hD32 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 2)
    (hD52 : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 2)
    (hcenB : CFSG.Open.IsKGroup (NativeSporadic.Carrier .B) →
      PCompCensus 3 (NativeSporadic.Carrier .B) (· = .sporadic .Fi22))
    (hcenM : CFSG.Open.IsKGroup (NativeSporadic.Carrier .M) →
      PCompCensus 5 (NativeSporadic.Carrier .M) (· = .sporadic .HN)) (h : SporPairsResidual) :
    Inputs2711b.InputI2711Rest :=
  ⟨inputI2711ChevPOuter_of_griess hGA,
    inputI2711SporPairs_of_residual h183 hSpM hOrd hOut hBr hMcL hKD3 hKD5 hb hD32 hD52 hcenB hcenM h⟩

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c

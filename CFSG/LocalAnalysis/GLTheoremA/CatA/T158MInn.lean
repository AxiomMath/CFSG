module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTriv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

private theorem t158i_indAut_mul {p : ℕ} {L : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L (g * h) (Subgroup.mul_mem _ hg hh) = indAut p L h hh * indAut p L g hg := by
  unfold indAut
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp

private theorem t158i_indAut_zpow {p : ℕ} {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (k : ℤ) : indAut p L (g ^ k) (Subgroup.zpow_mem _ hg k) = indAut p L g hg ^ k := by
  unfold indAut
  rw [← map_zpow]
  congr 1
  apply Subtype.ext
  simp [zpow_neg, inv_zpow]

private theorem t158i_innDiagOn_mono {p : ℕ} {A A' L : Subgroup G} (hA : InnDiagOn p A L) (h : A' ≤ A) :
    InnDiagOn p A' L :=
  ⟨h.trans hA.1, Canonical.largeEvenMarking_mono
    (fun _ _ _ _ _ _ hP a ha => hP a (h ha)) hA.2⟩

end Basic

section Marking


variable {G : Type} [Group G] [Finite G]

theorem t158_innDiagOn_mul {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hchev : IsChevSimple 2 (PSimple p L)) {a b : G} (ha : InnDiagOn p (Subgroup.zpowers a) L)
    (hb : InnDiagOn p (Subgroup.zpowers b) L) : InnDiagOn p (Subgroup.zpowers (a * b)) L := by
  have haN : a ∈ Subgroup.normalizer (L : Set G) := ha.1 (Subgroup.mem_zpowers a)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hb.1 (Subgroup.mem_zpowers b)
  have habN : a * b ∈ Subgroup.normalizer (L : Set G) := Subgroup.mul_mem _ haN hbN
  have hdA : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L a) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh a (Subgroup.mem_zpowers a)) ha.2
  have hdB : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L b) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh b (Subgroup.mem_zpowers b)) hb.2
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_any hL
  have h0 := CFSG.StandardType.ChevTwo.ys08_holds (PQuot p L) hq hchev
  have h2 := canon_marking_and_labelAll_simple (P' := RawInnBody p)
    (fun lab hlab => canonRawInnAny hp.ne_one hlab) h0
  have h3 := marking_transport (indRel p L a) hdA h2
  have h4 := marking_transport (indRel p L b) hdB h3
  refine ⟨Subgroup.zpowers_le.2 habN, Canonical.largeEvenMarking_mono ?_ h4⟩
  rintro lab R _ I F θ ⟨⟨⟨-, hmul, hinv, hinn, -⟩, φa, hφa, hindA⟩, φb, hφb, hindB⟩ c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hck : (a * b) ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.zpow_mem _ habN k
  let J : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {x y} hx hy => hmul x hx y hy
      one_mem' := by
        have := hinn 1
        rwa [map_one] at this
      inv_mem' := fun {x} hx => hinv x hx }
  have ea := (induces_indRel_iff haN θ).1 hindA
  have eb := (induces_indRel_iff hbN θ).1 hindB
  refine ⟨(φb * φa) ^ k, J.zpow_mem (J.mul_mem hφb hφa) k, (induces_indRel_iff hck θ).2 ?_⟩
  rw [ea, eb, t158i_indAut_zpow habN k, t158i_indAut_mul haN hbN, map_zpow, map_mul]

theorem t158_innDiagOn_sup {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L)
    (hchev : IsChevSimple 2 (PSimple p L)) {a b : G} (hab : a * b = b * a)
    (ha : InnDiagOn p (Subgroup.zpowers a) L) (hb : InnDiagOn p (Subgroup.zpowers b) L) :
    InnDiagOn p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) L := by
  have haN : a ∈ Subgroup.normalizer (L : Set G) := ha.1 (Subgroup.mem_zpowers a)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hb.1 (Subgroup.mem_zpowers b)
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    intro u hu
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j).eq).symm
  refine innDiag_unif_holds (sup_le (Subgroup.zpowers_le.2 haN) (Subgroup.zpowers_le.2 hbN))
    (fun c hc => ?_)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hc
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 hc
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  exact t158_innDiagOn_mul hp hL hchev
    (t158i_innDiagOn_mono ha (Subgroup.zpowers_le.2 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) i)))
    (t158i_innDiagOn_mono hb (Subgroup.zpowers_le.2 (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) j)))

end Marking

@[expose] def T158InnElemOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    catalogIs (PSimple p K) Q → p.Prime → p ≠ 2 → I158HypK p (⊤ : Subgroup X) K B x₁ x₂ L₁ L₂ →
      InnDiagOn p (Subgroup.zpowers x₁) K ∧ InnDiagOn p (Subgroup.zpowers x₂) K

section Group


theorem t158InnOn_of_elem (h : T158InnElemOn t158FamTwo) : T158InnOn t158FamTwo := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hp hp2 hh
  obtain ⟨h1, h2⟩ := h X p K B x₁ x₂ L₁ L₂ hQ hp hp2 hh
  obtain ⟨⟨-, hK, hBel, -, -, hx1B, hx2B, -⟩, -, -⟩ := hh
  have hKc : IsChevSimple 2 (PSimple p K) := Or.inl hQ
  exact t158_innDiagOn_sup hp hK hKc (isElemAbelian_commute hBel hx1B hx2B) h1 h2

end Group

end CFSG.LocalAnalysis.GLTheoremA.T158

end

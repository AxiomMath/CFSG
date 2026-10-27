module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch11SecOE5B
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

structure P622Conf {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T S : Subgroup G) : Prop where
  failure : Prop627Failure G p P M x z T
  prop614 : P622Prop614At M x z
  isMax : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) S
  le_S : smallRankS x T ≤ S

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T S : Subgroup G}

namespace P622Conf

theorem S_le_centralizer (c : P622Conf p P M x z T S) : S ≤ centralizer ({x} : Set G) :=
  c.isMax.1.1

theorem S_isPGroup (c : P622Conf p P M x z T S) : IsPGroup 2 S := c.isMax.1.2.1

theorem B_le_normalizer (c : P622Conf p P M x z T S) :
    zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) := c.isMax.1.2.2

theorem z_le_normalizer (c : P622Conf p P M x z T S) :
    zpowers z ≤ normalizer (S : Set G) := le_sup_right.trans c.B_le_normalizer

theorem S_ne_bot (hS : Setting G) (c : P622Conf p P M x z T S) : S ≠ ⊥ :=
  fun h => c.failure.S_ne_bot hS (le_bot_iff.mp (c.le_S.trans h.le))

theorem normalizer_le_of_invariant (c : P622Conf p P M x z T S) {W : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW1 : W ≠ ⊥) (hWM : W ≤ M)
    (hBW : zpowers x ⊔ zpowers z ≤ normalizer (W : Set G)) : normalizer (W : Set G) ≤ M :=
  c.prop614 (normalizer (W : Set G)) ⟨W, hW1, hW2, rfl⟩ hBW
    ⟨W, le_inf le_normalizer hWM, hW2, hW1, hBW⟩

theorem S_le_M (hS : Setting G) (c : P622Conf p P M x z T S) : S ≤ M := by
  have hSM : S ⊓ M ≠ ⊥ := by
    intro h
    apply c.failure.S_ne_bot hS
    rw [eq_bot_iff]
    exact (le_inf c.le_S c.failure.S_le_M).trans h.le
  have hH : IsTwoLocal (normalizer (S : Set G)) := ⟨S, c.S_ne_bot hS, c.S_isPGroup, rfl⟩
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer ((S ⊓ M : Subgroup G) : Set G) :=
    (le_inf c.B_le_normalizer ((c.failure.B_le_M hS).trans le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact le_normalizer.trans (c.prop614 _ hH c.B_le_normalizer
    ⟨S ⊓ M, inf_le_inf le_normalizer le_rfl, c.S_isPGroup.to_le inf_le_left, hSM, hBN⟩)

theorem B_le_normalizer_of_z (c : P622Conf p P M x z T S) {W : Subgroup G}
    (hWC : W ≤ centralizer ({x} : Set G)) (hz : zpowers z ≤ normalizer (W : Set G)) :
    zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) := by
  refine sup_le ?_ hz
  rw [zpowers_le]
  exact Subgroup.centralizer_le_normalizer (W : Set G) (mem_centralizer_iff.mpr fun h hh =>
    (mem_centralizer_singleton_iff.mp (hWC hh)))

theorem normalizer_le (hS : Setting G) (c : P622Conf p P M x z T S) {S₀ : Subgroup G}
    (hS₀S : S₀ ≤ S) (hS₀1 : S₀ ≠ ⊥) (hz : zpowers z ≤ normalizer (S₀ : Set G)) :
    normalizer (S₀ : Set G) ≤ M :=
  normalizer_le_of_invariant c (c.S_isPGroup.to_le hS₀S) hS₀1 (hS₀S.trans (c.S_le_M hS))
    (c.B_le_normalizer_of_z (hS₀S.trans c.S_le_centralizer) hz)

theorem R_le_S (c : P622Conf p P M x z T S) : ⁅zpowers z, S⁆ ≤ S := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hanorm : a ∈ normalizer (S : Set G) := c.z_le_normalizer ha
  have h1 : a * b * a⁻¹ ∈ S := (mem_normalizer_iff.mp hanorm b).mp hb
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hb)

theorem z_le_normalizer_R (c : P622Conf p P M x z T S) :
    zpowers z ≤ normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) := by
  rw [zpowers_le, mem_normalizer_iff_map_conj_eq]
  have hzS : S.map (MulAut.conj z).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (c.z_le_normalizer (mem_zpowers z))
  have hzz : (zpowers z).map (MulAut.conj z).toMonoidHom = zpowers z := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have h := Subgroup.map_commutator (H₁ := zpowers z) (H₂ := S) (MulAut.conj z).toMonoidHom
  rw [hzS, hzz] at h
  exact h

theorem R_ne_bot (hS : Setting G) (c : P622Conf p P M x z T S) : ⁅zpowers z, S⁆ ≠ ⊥ := by
  intro h
  apply c.failure.R_ne_bot hS
  rw [eq_bot_iff]
  exact (Subgroup.commutator_mono le_rfl c.le_S).trans h.le

theorem R_isPGroup (c : P622Conf p P M x z T S) : IsPGroup 2 (⁅zpowers z, S⁆ : Subgroup G) := by
  exact c.S_isPGroup.to_le c.R_le_S

theorem centralizer_le_M (hS : Setting G) (c : P622Conf p P M x z T S) :
    centralizer ({z} : Set G) ≤ M := by
  refine le_trans ?_ (c.failure.normalizer_zpowers_le hS)
  intro g hg
  have hgz : Commute g z := mem_centralizer_singleton_iff.mp hg
  refine Subgroup.centralizer_le_normalizer ((zpowers z : Subgroup G) : Set G)
    (mem_centralizer_iff.mpr fun h hh => ?_)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (SetLike.mem_coe.mp hh)
  exact (hgz.zpow_right k).symm.eq

theorem B_le_P (c : P622Conf p P M x z T S) : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
  c.failure.B_le_P

theorem B_le_M (hS : Setting G) (c : P622Conf p P M x z T S) : zpowers x ⊔ zpowers z ≤ M :=
  c.failure.B_le_M hS

theorem z_mem_centralizer (c : P622Conf p P M x z T S) : z ∈ centralizer ({x} : Set G) := by
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp c.failure.central.centralizes x c.failure.point.mem).symm

theorem B_le_centralizer (c : P622Conf p P M x z T S) :
    zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) := by
  exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    (zpowers_le.mpr c.z_mem_centralizer)

end P622Conf

theorem p622_exists_conf (hf : Prop627Failure G p P M x z T) (h614 : P622Prop614At M x z) :
    ∃ S : Subgroup G, P622Conf p P M x z T S := by
  have hinv : IsTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G))
      (smallRankS x T) := ⟨inf_le_right, hf.S_isPGroup, hf.B_le_normalizer_S⟩
  obtain ⟨S, hle, hmax⟩ := exists_isMaxTwoInvariantIn_of_le hinv
  exact ⟨S, ⟨hf, h614, hmax, hle⟩⟩

theorem p622_exists_central (hS : Setting G) {q : ℕ} (Q : Sylow q G) (hq : q ∈ rankThreeSigmaA G) :
    ∃ w : G, SmallRankCentral Q w := by
  have hprime : q.Prime := sigmaA_prime q hq
  haveI : Fact q.Prime := ⟨hprime⟩
  obtain ⟨-, -, -, -, hQ3, -⟩ := exists_isCoreMaxLocal hS hq Q
  have hQne : (Q : Subgroup G) ≠ ⊥ := by
    intro h0
    have h0' : CFSG.Open.pRank q (⊥ : Subgroup G) = 0 := pRank_bot_eq_zero hprime
    rw [h0, h0'] at hQ3
    omega
  have hnt : Nontrivial (Q : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hQne
  have hZ : Nontrivial (center (Q : Subgroup G)) := Q.isPGroup'.center_nontrivial
  have hdvd : q ∣ Nat.card (center (Q : Subgroup G)) :=
    (Q.isPGroup'.to_subgroup _).card_eq_or_dvd.resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hc' : orderOf ((c : Q) : G) = q := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨((c : Q) : G), (c : Q).2, ?_, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  · intro h1
    rw [h1, orderOf_one] at hc'
    exact (Fact.out : q.Prime).one_lt.ne hc'
  · have h := pow_orderOf_eq_one ((c : Q) : G)
    rwa [hc'] at h

theorem p622_failure_of_not (hsit : SmallRankSituation G p P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) (hT : SmallRankSylowTwo P M T) (hnc : ¬ SmallRankCover p M x)
    (hn1 : ¬ (p = 3 ∧ SmallRankCaseOne x T)) : Prop627Failure G p P M x z T := by
  refine ⟨hsit, hx, hz, hT, ?_⟩
  rintro ⟨rfl, hcase⟩
  rcases hcase with h1 | ⟨-, h2⟩
  · exact hn1 ⟨rfl, h1⟩
  · exact hnc h2

theorem p622_centralizer_ne_top (hS : Setting G) (hx1 : x ≠ 1) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hS.simple
  have hc : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact hx1 (by simpa [h] using hc)
  · obtain ⟨b, c, hbc⟩ := hS.nonab
    exact hbc (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) c).symm

theorem p622_isKGroup_primeCore (hS : Setting G) (hx1 : x ≠ 1) :
    CFSG.Open.IsKGroup ↥(smallRankD p x) := by
  have : IsSimpleGroup G := hS.simple
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) := sSup_le fun _ hN => hN.1
  have hDne : smallRankD p x ≠ ⊤ := fun h =>
    p622_centralizer_ne_top hS hx1 (top_le_iff.mp (h.symm.trans_le hDC))
  exact CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
    (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper _ hDne)

theorem p622_x_not_mem_zpowers (hS : Setting G) (hsit : SmallRankSituation G p P M)
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) : x ∉ zpowers z := by
  intro hxz
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hBc := hpl.card_eq
  have hsup : zpowers x ⊔ zpowers z = zpowers z := sup_eq_right.mpr (zpowers_le.mpr hxz)
  rw [hsup, Nat.card_zpowers, orderOf_eq_prime hz.pow_eq_one hz.ne_one] at hBc
  have hp2 := hprime.two_le
  nlinarith [pow_two p]

theorem p622_cover_of_hasNormalPComplement (hS : Setting G) (hsit : SmallRankSituation G p P M)
    (hx : SmallRankPoint P M x) (h : CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G))) :
    centralizer ({x} : Set G) ≤ (M ⊓ centralizer ({x} : Set G)) ⊔ smallRankD p x := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hPx : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨inf_le_right, P.isPGroup'.to_inf_left, hx.sylow_centralizer⟩
  exact (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.s622_le_sup_of_hasNormalPComplement hprime
    hPx h).trans (sup_le_sup_right (inf_le_inf_right _ hPM) _)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

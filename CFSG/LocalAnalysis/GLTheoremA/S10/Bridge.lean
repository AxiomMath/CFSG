module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private theorem bridge_commutator_quot_eq_top {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (h : commutator Q = ⊤) : commutator (Q ⧸ N) = ⊤ := by
  have h1 : commutator (Q ⧸ N) = (commutator Q).map (QuotientGroup.mk' N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  rw [h1, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

private theorem bridge_center_quot_eq_bot {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with h | h
  · exact h
  · exfalso
    have hcomm : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      have ha : a ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := h ▸ Subgroup.mem_top a
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact Subgroup.mem_center_iff.1 ha b
    rw [bridge_commutator_quot_eq_top (Subgroup.center Q) hQ.1] at hcomm
    have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    apply hab
    have ha : a ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

private theorem bridge_eq_of_bot {Q : Type*} [Group Q] (K : Subgroup Q) (hK : K = ⊥) (a b : ↥K) :
    a = b := by
  subst hK
  exact Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)

private theorem bridge_O_ne_top {X L : Subgroup G} (hL : GLAPComponent p X L) :
    GLAPPrimeCore p ↥L ≠ ⊤ := by
  intro htop
  have hLO : L ≤ GLAPPrimeCoreOf p X := by
    have h1 : L ≤ GLAPPrimeCoreOf p L := fun x hx =>
      Subgroup.mem_map.2 ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩
    exact h1.trans
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hL.2.1)
  have hbot : (L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hLO (Subgroup.mem_subgroupOf.1 hx))
    exact (Subtype.ext hyx : y = x) ▸ hy
  obtain ⟨a, b, hab⟩ :=
    (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hL.2.2.1.2.2).exists_pair_ne
  exact hab (bridge_eq_of_bot _ hbot a b)

private noncomputable def bridgeF (L : Subgroup G) :
    ↥L →* (PQuot p L ⧸ Subgroup.center (PQuot p L)) :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))

private theorem bridgeF_surjective (L : Subgroup G) : Function.Surjective (bridgeF (p := p) L) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p L)) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) z
  exact ⟨x, rfl⟩

private theorem bridge_ker {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) : (bridgeF (p := p) L).ker = Subgroup.center ↥L := by
  have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hO
  ext n
  rw [MonoidHom.mem_ker]
  constructor
  · intro hn
    have hn2 : (QuotientGroup.mk (QuotientGroup.mk n : PQuot p L) :
        PQuot p L ⧸ Subgroup.center (PQuot p L)) = 1 := hn
    have hn' : (QuotientGroup.mk n : PQuot p L) ∈ Subgroup.center (PQuot p L) :=
      (QuotientGroup.eq_one_iff _).1 hn2
    have hmem : (QuotientGroup.mk n : ↥L ⧸ Subgroup.center ↥L) ∈
        Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      have hc : (x * n)⁻¹ * (n * x) ∈ GLAPPrimeCore p ↥L := by
        have hc0 := Subgroup.mem_center_iff.1 hn' (QuotientGroup.mk x)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc0
        exact hc0
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hOZ hc
    rw [bridge_center_quot_eq_bot hq] at hmem
    exact (QuotientGroup.eq_one_iff n).1 (Subgroup.mem_bot.1 hmem)
  · intro hz
    have hn' : (QuotientGroup.mk n : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz x]
    show (QuotientGroup.mk (QuotientGroup.mk n : PQuot p L) :
      PQuot p L ⧸ Subgroup.center (PQuot p L)) = 1
    exact (QuotientGroup.eq_one_iff _).2 hn'

private noncomputable def bridgeE {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) :
    (↥L ⧸ Subgroup.center ↥L) ≃* (PQuot p L ⧸ Subgroup.center (PQuot p L)) :=
  (QuotientGroup.quotientMulEquivOfEq (bridge_ker hq hO).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (bridgeF (p := p) L) (bridgeF_surjective L))

private theorem bridgeE_mk {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) (l : ↥L) :
    bridgeE hq hO (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l) := rfl

private theorem bridgeE_symm_mk {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) (l : ↥L) :
    (bridgeE hq hO).symm (QuotientGroup.mk (QuotientGroup.mk l)) = QuotientGroup.mk l := by
  rw [MulEquiv.symm_apply_eq, bridgeE_mk]

private theorem bridge_rawDatum_exists {lab : CFSG.Assembly.LargeEvenLabel}
    {Q : CFSG.Assembly.LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem innDiagOn_of_inner {X L B : Subgroup G} (hL : GLAPComponent p X L) (hq : CFSG.Open.IsQuasisimple ↥L) :
    InnerDiagMarking B L → InnDiagOn p B L := by
  intro h
  obtain ⟨_, lab, hlab, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := bridge_rawDatum_exists hraw
  obtain ⟨_, _, _, hBN, _⟩ := hQ
  have hO := bridge_O_ne_top hL
  refine ⟨hBN, bridge_commutator_quot_eq_top (GLAPPrimeCore p ↥L) hq.1, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ, _, hI⟩
  refine ⟨hs, hna, (bridgeE hq hO).symm.trans θ, fun a ha => ?_⟩
  obtain ⟨φ, hφI, hφ⟩ := hI a ha
  refine ⟨φ, hφI, ?_⟩
  rintro _ _ ⟨l, l', rfl, rfl, hll⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, bridgeE_symm_mk, bridgeE_symm_mk]
  exact hφ l l' hll

theorem inner_of_innDiagOn {X L B : Subgroup G} (hL : GLAPComponent p X L) (hq : CFSG.Open.IsQuasisimple ↥L) :
    InnDiagOn p B L → InnerDiagMarking B L := by
  rintro ⟨hBN, _, lab, hlab, hraw⟩
  have hO := bridge_O_ne_top hL
  refine ⟨hq.1, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ, hI⟩
  refine ⟨hs, hna, (bridgeE hq hO).trans θ, hBN, fun b hb => ?_⟩
  obtain ⟨φ, hφI, hφ⟩ := hI b hb
  refine ⟨φ, hφI, ?_⟩
  intro l l' hll
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, bridgeE_mk, bridgeE_mk]
  exact hφ (QuotientGroup.mk l) (QuotientGroup.mk l') ⟨l, l', rfl, rfl, hll⟩

theorem innDiagOn_iff {X L B : Subgroup G} (hL : GLAPComponent p X L) (hq : CFSG.Open.IsQuasisimple ↥L) :
    InnerDiagMarking B L ↔ InnDiagOn p B L :=
  ⟨innDiagOn_of_inner hL hq, inner_of_innDiagOn hL hq⟩

theorem innDiagOn_mono {A A' L : Subgroup G} (hA : InnDiagOn p A L) (h : A' ≤ A) : InnDiagOn p A' L :=
  ⟨h.trans hA.1, CFSG.StandardType.Canonical.largeEvenMarking_mono
    (fun _ _ _ _ _ _ hP a ha => hP a (h ha)) hA.2⟩

end S10

end CFSG.LocalAnalysis.GLTheoremA

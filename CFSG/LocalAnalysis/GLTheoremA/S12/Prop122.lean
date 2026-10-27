module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop122C

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Concl122 (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (J : Subgroup G) : Prop where
  norm : B ≤ Subgroup.normalizer (J : Set G)
  qs : CFSG.Open.IsQuasisimple ↥J
  chev2 : IsChevSimple 2 (PSimple p J)
  half : S12.Half122 p B x J

namespace S12

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G} {y : G} {J : Subgroup G}

theorem prop122 (h : NbrCfg G m p B x L D K y J) (hin : Inputs122 G p) : Concl122 G p B x J :=
  ⟨nbr_norm h hin, qs_J h hin, chev2_J h hin, half_J h hin⟩

private theorem fbridge_commutator_quot_eq_top {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (h : commutator Q = ⊤) : commutator (Q ⧸ N) = ⊤ := by
  have h1 : commutator (Q ⧸ N) = (commutator Q).map (QuotientGroup.mk' N) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  rw [h1, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

private theorem fbridge_center_quot_eq_bot {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
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
    rw [fbridge_commutator_quot_eq_top (Subgroup.center Q) hQ.1] at hcomm
    have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    apply hab
    have ha : a ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) := hcomm ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

private theorem fbridge_eq_of_bot {Q : Type*} [Group Q] (K : Subgroup Q) (hK : K = ⊥) (a b : ↥K) :
    a = b := by
  subst hK
  exact Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)

private theorem fbridge_O_ne_top {X L : Subgroup G} (hL : GLAPComponent p X L) :
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
  exact hab (fbridge_eq_of_bot _ hbot a b)

private noncomputable def fbridgeF (L : Subgroup G) :
    ↥L →* (PQuot p L ⧸ Subgroup.center (PQuot p L)) :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))

private theorem fbridgeF_surjective (L : Subgroup G) : Function.Surjective (fbridgeF (p := p) L) := by
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p L)) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) z
  exact ⟨x, rfl⟩

private theorem fbridge_ker {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) : (fbridgeF (p := p) L).ker = Subgroup.center ↥L := by
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
    rw [fbridge_center_quot_eq_bot hq] at hmem
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

private noncomputable def fbridgeE {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) :
    (↥L ⧸ Subgroup.center ↥L) ≃* (PQuot p L ⧸ Subgroup.center (PQuot p L)) :=
  (QuotientGroup.quotientMulEquivOfEq (fbridge_ker hq hO).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (fbridgeF (p := p) L) (fbridgeF_surjective L))

private theorem fbridgeE_mk {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hO : GLAPPrimeCore p ↥L ≠ ⊤) (l : ↥L) :
    fbridgeE hq hO (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l) := rfl

theorem glaPPrimeCore_ne_top_of_glaPComponent {X L : Subgroup G} (hL : GLAPComponent p X L) :
    GLAPPrimeCore p ↥L ≠ ⊤ := fbridge_O_ne_top hL

theorem marking_of_fieldOn {X J : Subgroup G} {g : G} (hJ : GLAPComponent p X J) (hq : CFSG.Open.IsQuasisimple ↥J)
    (hf : FieldOn p g J) :
    GLAMarking J (fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ fun j j' => (j' : G) = g⁻¹ * j * g)) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hf.2
  have hO := fbridge_O_ne_top hJ
  refine ⟨hq.1, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ, htag, f, hfF, u, huI, hord, hind⟩
  refine ⟨hs, hna, (fbridgeE hq hO).trans θ, htag, f, hfF, u, huI, hord, ?_⟩
  intro l l' hll
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, fbridgeE_mk, fbridgeE_mk]
  exact hind (QuotientGroup.mk l) (QuotientGroup.mk l') ⟨l, l', rfl, rfl, hll⟩

end S12

end CFSG.LocalAnalysis.GLTheoremA

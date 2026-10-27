module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieNodeSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutUnitary
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSU)

theorem exists_elemAbelian_of_le_pRank {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} {k : ℕ} (hk : k ≤ CFSG.Open.pRank p H) (hk0 : 0 < k) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ p ^ k ≤ Nat.card E := by
  set S : Set ℕ := {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}
    with hS
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : CFSG.Open.pRank p H = 0 := by
      show sSup S = 0
      rw [hemp]; simp
    omega
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, fun m ⟨E, _, _, hE⟩ => ?_⟩
    have h1 : p ^ m ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    have h2 : m < p ^ m := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  obtain ⟨E, hEH, hEel, hEc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨E, hEH, hEel, ?_⟩
  rw [hEc]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup h

theorem exists_inner_sq_of_card_outer_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card (Outer G) ≤ 2) (ψ : G ≃* G) : ∃ a : G, ∀ x, ψ (ψ x) = a * x * a⁻¹ := by
  have : Finite (MulAut G) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  set q : Outer G := QuotientGroup.mk (s := CFSG.ComponentClassification.OuterAutomorphisms.inner G) ψ with hq
  have hq2 : q * q = 1 := by
    have h12 : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2 := by omega
    rcases h12 with h1 | h2
    · have h1' := pow_card_eq_one' (G := Outer G) (x := q)
      rw [h1, pow_one] at h1'
      rw [h1', mul_one]
    · have := pow_card_eq_one' (G := Outer G) (x := q)
      rwa [h2, pow_two] at this
  have hmem : ψ * ψ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hq2
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, fun x => by
    have hx := congrArg (fun φ : MulAut G => φ x) ha
    simp only [MulAut.conj_apply] at hx
    simpa using hx.symm⟩

theorem autSqInner_psu_five {X : Type} [Group X] [Finite X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 5 2 1) (ψ : X ≃* X) :
    ∃ a : X, ∀ x, ψ (ψ x) = a * x * a⁻¹ := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel h
  have hout : Nat.card (Outer X) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      card_outer_projSU_eq 5 2 1 le_rfl (by omega) (by omega)]
    norm_num
  exact exists_inner_sq_of_card_outer_le_two hout ψ

theorem exists_inducedAut {Q : Type*} [Group Q] {Lb : Subgroup Q} {n : Q}
    (hn : n ∈ Subgroup.normalizer (Lb : Set Q)) :
    ∃ ψ : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* (↥Lb ⧸ Subgroup.center ↥Lb),
      ∀ a : ↥Lb, ψ (QuotientGroup.mk a) = QuotientGroup.mk (conjOnNormalizer Lb n hn a) := by
  set ψ0 : Lb ≃* Lb := conjOnNormalizer Lb n hn with hψ0
  have hcen : (Subgroup.center Lb).map ψ0.toMonoidHom = Subgroup.center Lb := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := Subgroup.mem_center_iff.mp hw
      refine Subgroup.mem_center_iff.mpr fun a => ?_
      have := hw' (ψ0.symm a)
      have h2 := congrArg ψ0 this
      simpa using h2
    · intro hz
      have hz' := Subgroup.mem_center_iff.mp hz
      refine ⟨ψ0.symm z, Subgroup.mem_center_iff.mpr fun a => ?_, by simp⟩
      have := hz' (ψ0 a)
      have h2 := congrArg ψ0.symm this
      simpa using h2
  exact ⟨QuotientGroup.congr (Subgroup.center Lb) (Subgroup.center Lb) ψ0 hcen, fun a => rfl⟩

theorem comm_mem_of_le_normalizer_psu_five {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSU 5 2 1) (T : Sylow 2 Y) {y z : Y}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hz : z ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    z⁻¹ * y⁻¹ * z * y ∈ (T : Subgroup Y) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have : Finite (SU (unitaryInvolution F 2 1) 5) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e
  exact comm_mem_of_le_normalizer_borel hB ⟨⟨0, by show 0 < 5 / 2; omega⟩⟩ T hy hz

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

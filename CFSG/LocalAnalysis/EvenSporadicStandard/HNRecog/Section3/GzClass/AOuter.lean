module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzNE
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private lemma sq_eq_one_of_isConj {G : Type*} [Group G] {a c : G} (ha : orderOf a = 2)
    (hc : IsConj a c) : c ^ 2 = 1 := by
  have ha2 : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  have h1 : IsConj (a ^ 2) (c ^ 2) := hc.pow 2
  rw [ha2] at h1
  exact isConj_one_right.mp h1

private lemma barOf_sq_eq_one {G : Type} [Group G] {z c : G} (hc : c ∈ Gx z)
    (hc2 : c ^ 2 = 1) : (barOf z (⟨c, hc⟩ : ↥(Gx z))) ^ 2 = 1 := by
  have hc' : (⟨c, hc⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hc2
  change (QuotientGroup.mk (⟨c, hc⟩ : ↥(Gx z))) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, hc', QuotientGroup.mk_one]

theorem barOf_not_mem_commutator (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    {c : G} (hcz : c ∈ Gx z) (hcQ : c ∉ Qz z) (hcA : IsConj a c) :
    barOf z (⟨c, hcz⟩ : ↥(Gx z)) ∉ _root_.commutator (Gbar z) := by
  classical
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hOrb' : GzOrbitFacts a z := hOrb.self
  have hIrr : CIrreducible ↥(Gx z) Q := cIrreducible_pCore h hOrb'
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_isConj h.orderOf_a hcA
  have hc'2 : (⟨c, hcz⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hc2
  have hcbar2 : (barOf z (⟨c, hcz⟩ : ↥(Gx z))) ^ 2 = 1 := barOf_sq_eq_one hcz hc2
  have hcbar1 : barOf z (⟨c, hcz⟩ : ↥(Gx z)) ≠ 1 := by
    intro h1
    exact hcQ (by simpa using (barOf_eq_one_iff (⟨c, hcz⟩ : ↥(Gx z))).mp h1)
  have hQcard : Nat.card ↥Q = 512 := by
    rw [hQ.plus.2.1]
    norm_num
  have hcentK : Nat.card ↥(Subgroup.centralizer ({(⟨c, hcz⟩ : ↥(Gx z))} : Set ↥(Gx z))) =
      3840 := by
    have h1 : Nat.card ↥(Subgroup.centralizer ({(⟨c, hcz⟩ : ↥(Gx z))} : Set ↥(Gx z))) =
        2 ^ 8 * 15 := by
      rw [← card_Gx_inf_eq hcz]
      exact hOrb'.orbit_outA.2 c ⟨hcz, hcQ, hcA⟩
    rw [h1]
    norm_num
  have hcentBar : Nat.card ↥(Subgroup.centralizer
      ({((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} : Set (↥(Gx z) ⧸ Q))) =
      Nat.card ↥(CbarCent z (⟨c, hcz⟩ : ↥(Gx z))) := rfl
  have hfiber := card_fiber_mul_card_centralizer Q (⟨c, hcz⟩ : ↥(Gx z))
  have hFiberEq :
      Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ = s) ∧
        (s : ↥(Gx z) ⧸ Q) = ((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} * 3840 =
        512 * Nat.card ↥(CbarCent z (⟨c, hcz⟩ : ↥(Gx z))) := by
    rw [hQcard, hcentK, hcentBar] at hfiber
    exact hfiber
  have hζ : GxSelf z ∈ centerOf Q := by
    rw [centerOf_eq_zpowers h.orderOf_z hQ]
    exact Subgroup.mem_zpowers (GxSelf z)
  have hne : ∀ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ ≠
      (⟨c, hcz⟩ : ↥(Gx z)) * GxSelf z := by
    intro k hk
    have hkG : (k : G) * c * (k : G)⁻¹ = c * z := by
      have h := congrArg (fun t : ↥(Gx z) => (t : G)) hk
      simpa [GxSelf] using h
    have hconj : IsConj c (c * z) := isConj_iff.mpr ⟨(k : G), hkG⟩
    have hf3 : Fusion3Facts c z := hF3 c z hcA (IsConj.refl z)
    exact hcQ (hf3.shape_2AB z ⟨IsConj.refl z, hconj⟩).2
  have hlt := card_fiber_lt Q hQ.plus hc'2 hζ hne
  rcases involution_cases_of_mulEquiv e hcbar2 hcbar1 with
    ⟨hout, _⟩ | ⟨hin, hcard⟩ | ⟨_, hcard⟩
  · exact hout
  · exfalso
    have hF32 :
        Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * (⟨c, hcz⟩ : ↥(Gx z)) * k⁻¹ = s) ∧
          (s : ↥(Gx z) ⧸ Q) = ((⟨c, hcz⟩ : ↥(Gx z)) : ↥(Gx z) ⧸ Q)} = 32 := by
      rw [hcard] at hFiberEq
      omega
    have hcentQ :
        Nat.card {q : ↥(Gx z) // q ∈ Q ∧ ⁅q, (⟨c, hcz⟩ : ↥(Gx z))⁆ ∈ centerOf Q} = 32 := by
      have h := hC.centQ_inv_base ↥(Gx z) Q hQ hIrr (⟨c, hcz⟩ : ↥(Gx z)) hcbar2 hcbar1 hin
      norm_num at h
      exact h
    rw [hF32] at hlt
    rw [hcentQ] at hlt
    omega
  · exfalso
    have h := hFiberEq
    rw [hcard] at h
    omega

theorem exists_outer_lift (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    {v : Gbar z} (hv2 : v ^ 2 = 1) (hv : v ∉ _root_.commutator (Gbar z)) :
    ∃ y : ↥(Gx z), IsConj a (y : G) ∧ barOf z y = v := by
  classical
  obtain ⟨c, hcz, hcQ, hcA⟩ := exists_mem_Gx_not_mem_Qz hF1.self hF2.self
  have hc2 : c ^ 2 = 1 := sq_eq_one_of_isConj h.orderOf_a hcA
  have hcbar2 : (barOf z (⟨c, hcz⟩ : ↥(Gx z))) ^ 2 = 1 := barOf_sq_eq_one hcz hc2
  have hout : barOf z (⟨c, hcz⟩ : ↥(Gx z)) ∉ _root_.commutator (Gbar z) :=
    barOf_not_mem_commutator hI hC h hF1 hF2 hF3 hOrb hcz hcQ hcA
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  obtain ⟨b, _, hbc⟩ := exists_conj_of_outer_of_mulEquiv e hout hv hcbar2 hv2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective b
  refine ⟨g * (⟨c, hcz⟩ : ↥(Gx z)) * g⁻¹, ?_, ?_⟩
  · have hconj : IsConj c (((g * (⟨c, hcz⟩ : ↥(Gx z)) * g⁻¹ : ↥(Gx z)) : G)) :=
      isConj_iff.mpr ⟨(g : G), by simp⟩
    exact hcA.trans hconj
  · have hmul : barOf z (g * (⟨c, hcz⟩ : ↥(Gx z)) * g⁻¹) =
        barOf z g * barOf z (⟨c, hcz⟩ : ↥(Gx z)) * (barOf z g)⁻¹ := by
      simp [barOf, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hgb : barOf z g = b := hg
    rw [hmul, hgb, hbc]

end CFSG.EvenSporadicStandard.HNRecog.Section3

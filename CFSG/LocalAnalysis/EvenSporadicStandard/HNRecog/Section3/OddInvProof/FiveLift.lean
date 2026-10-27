module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.FixFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Outer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.A5OddGbar
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_five_lift_bar {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) (hNo : GzNoFacts a z) (hx : IsConj a x) (haz : a ∈ Gx z)
    (hxz : x ∈ Gx z) (haQ : a ∉ Qz z) (hxQ : x ∉ Qz z) :
    ∃ t₀ : G, ∃ ht₀ : t₀ ∈ Gx z, IsConj a t₀ ∧ t₀ ∉ Qz z ∧
      barOf z ⟨t₀, ht₀⟩ ∉ _root_.commutator (Gbar z) ∧
      barOf z ⟨t₀, ht₀⟩ * barOf z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ =
        barOf z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ * barOf z ⟨t₀, ht₀⟩ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have ha2 : a ^ 2 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [h.orderOf_a] at this
  have hx2 : x ^ 2 = 1 := oddInv_sq_eq_one h hx
  have hA2 : (barOf z ⟨a, haz⟩) ^ 2 = 1 := oddInv_barOf_sq_eq_one haz ha2
  have hxB2 : (barOf z ⟨x, hxz⟩) ^ 2 = 1 := oddInv_barOf_sq_eq_one hxz hx2
  have hA_out : barOf z ⟨a, haz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo haz haQ (IsConj.refl a)
  have hxB_out : barOf z ⟨x, hxz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo hxz hxQ hx
  obtain ⟨wB, hwB2, hwBout, hwBcomm⟩ :=
    oddInv_gbar_exists_outer e hA_out hxB_out hA2 hxB2
  obtain ⟨b, _hb_mem, hb⟩ :=
    exists_conj_of_outer_of_mulEquiv e hA_out hwBout hA2 hwB2
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective b
  let y : ↥(Gx z) := g * ⟨a, haz⟩ * g⁻¹
  have hgb : barOf z g = b := hg
  have hmul : barOf z y = barOf z g * barOf z ⟨a, haz⟩ * (barOf z g)⁻¹ := by
    simp [y, barOf, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have htbar : barOf z y = wB := by
    rw [hmul, hgb, hb]
  have hne1 : wB ≠ 1 := fun h1 => hwBout (h1.symm ▸ Subgroup.one_mem _)
  have hax : barOf z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ =
      barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩ := rfl
  refine ⟨(y : G), y.2, ?_, ?_, ?_, ?_⟩
  · exact (IsConj.refl a).trans (isConj_iff.mpr ⟨(g : G), by simp [y]⟩)
  · intro hQmem
    exact hne1 (htbar ▸ (barOf_eq_one_iff y).mpr hQmem)
  · change barOf z y ∉ _root_.commutator (Gbar z)
    rw [htbar]
    exact hwBout
  · change barOf z y * barOf z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ =
      barOf z ⟨a * x, Subgroup.mul_mem _ haz hxz⟩ * barOf z y
    rw [htbar, hax]
    exact hwBcomm

theorem oddInv_five_lift {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) (hNo : GzNoFacts a z) (hx : IsConj a x) (haz : a ∈ Gx z)
    (hxz : x ∈ Gx z) (haQ : a ∉ Qz z) (hxQ : x ∉ Qz z) (h5 : (a * x) ^ 5 = 1) :
    ∃ t : G, ∃ ht : t ∈ Gx z, IsConj a t ∧ barOf z ⟨t, ht⟩ ∉ _root_.commutator (Gbar z) ∧
      t * (a * x) = a * x * t := by
  obtain ⟨t₀, ht₀, ht₀A, ht₀Q, ht₀out, ht₀comm⟩ :=
    oddInv_five_lift_bar h hOrb hNo hx haz hxz haQ hxQ
  let c : ↥(Gx z) := ⟨t₀, ht₀⟩
  let σ : ↥(Gx z) := ⟨a * x, Subgroup.mul_mem _ haz hxz⟩
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  have ht₀sq : t₀ ^ 2 = 1 := oddInv_sq_eq_one h ht₀A
  have hQcard : Nat.card ↥Q = 512 := by
    change Nat.card ↥(CFSG.pCore 2 ↥(Gx z)) = 512
    rw [(isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z).plus.2.1]
    norm_num
  have hcentK : Nat.card ↥(Subgroup.centralizer ({c} : Set ↥(Gx z))) = 3840 := by
    have h1 : Nat.card ↥(Subgroup.centralizer ({c} : Set ↥(Gx z))) = 2 ^ 8 * 15 := by
      rw [← card_Gx_inf_eq ht₀]
      exact hOrb.orbit_outA.2 t₀ ⟨ht₀, ht₀Q, ht₀A⟩
    rw [h1]
    norm_num
  have hcent120 : Nat.card ↥(Subgroup.centralizer
      ({(c : ↥(Gx z) ⧸ Q)} : Set (↥(Gx z) ⧸ Q))) = 120 := by
    obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
    have hcbar2 : (c : ↥(Gx z) ⧸ Q) ^ 2 = 1 := by
      change (barOf z ⟨t₀, ht₀⟩) ^ 2 = 1
      exact oddInv_barOf_sq_eq_one ht₀ ht₀sq
    have hcbar1 : (c : ↥(Gx z) ⧸ Q) ≠ 1 := by
      intro h1
      apply ht₀out
      rw [show barOf z ⟨t₀, ht₀⟩ = (c : ↥(Gx z) ⧸ Q) from rfl, h1]
      exact Subgroup.one_mem _
    rcases involution_cases_of_mulEquiv e hcbar2 hcbar1 with
      ⟨_, hcard⟩ | ⟨hin, _⟩ | ⟨hin, _⟩
    · exact hcard
    · exact absurd hin ht₀out
    · exact absurd hin ht₀out
  have hfiber := card_fiber_mul_card_centralizer Q c
  rw [hQcard, hcentK, hcent120] at hfiber
  have hF16 : Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * c * k⁻¹ = s) ∧
      (s : ↥(Gx z) ⧸ Q) = (c : ↥(Gx z) ⧸ Q)} = 16 := by
    have h1 : (512 : ℕ) * 120 = 16 * 3840 := by norm_num
    rw [h1] at hfiber
    exact Nat.mul_right_cancel (by norm_num) hfiber
  have hF : ¬ 5 ∣ Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * c * k⁻¹ = s) ∧
      (s : ↥(Gx z) ⧸ Q) = (c : ↥(Gx z) ⧸ Q)} := by
    rw [hF16]
    norm_num
  have hσ : σ ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h5
  have hcomm : (σ : ↥(Gx z) ⧸ Q) * (c : ↥(Gx z) ⧸ Q) =
      (c : ↥(Gx z) ⧸ Q) * (σ : ↥(Gx z) ⧸ Q) := by
    simpa [σ, c, barOf] using ht₀comm.symm
  obtain ⟨s, hs_conj, hs_bar, hs_comm⟩ := oddInv_exists_fixed_conj Q hσ hcomm hF
  obtain ⟨k, hk⟩ := hs_conj
  have hkG : (k : G) * t₀ * (k : G)⁻¹ = (s : G) := by
    have := congrArg (fun y : ↥(Gx z) => (y : G)) hk
    simpa [c] using this
  have hs_commG : (a * x) * (s : G) = (s : G) * (a * x) := by
    have := congrArg (fun y : ↥(Gx z) => (y : G)) hs_comm
    simpa [σ] using this
  refine ⟨(s : G), s.2, ?_, ?_, ?_⟩
  · exact ht₀A.trans (isConj_iff.mpr ⟨(k : G), hkG⟩)
  · change barOf z s ∉ _root_.commutator (Gbar z)
    rw [show barOf z s = (s : ↥(Gx z) ⧸ Q) from rfl, hs_bar]
    simpa [c, barOf] using ht₀out
  · exact hs_commG.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3

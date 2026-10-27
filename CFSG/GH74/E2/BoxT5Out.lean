module

public import CFSG.GH74.E2.BoxT5Pair
public import CFSG.GH74.E2.OuterL33GBase

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

theorem inner_of_simple_acts {Q : Type*} [Group Q] [Finite Q]
    (hcen : ∀ x : Q, (∀ y : Q, x * y = y * x) → x = 1)
    (hcard : Nat.card (MulAut Q) = 2 * Nat.card Q)
    {P : Type*} [Group P] [Finite P] [IsSimpleGroup P] (hP : 2 < Nat.card P)
    (ρ : P →* MulAut Q) : ∀ p : P, ∃ w : Q, ρ p = MulAut.conj w := by
  have hinj : Function.Injective (MulAut.conj : Q →* MulAut Q) := by
    intro a b hab
    have h1 : ∀ x, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
      have := congrArg (fun f : MulAut Q => f x) hab
      simpa [MulAut.conj_apply] using this
    have h2 : (b⁻¹ * a) = 1 := by
      refine hcen _ fun x => ?_
      have := h1 x
      calc (b⁻¹ * a) * x = (b⁻¹ * (a * x * a⁻¹)) * a := by group
        _ = (b⁻¹ * (b * x * b⁻¹)) * a := by rw [this]
        _ = x * (b⁻¹ * a) := by group
    exact (inv_mul_eq_one.1 h2).symm
  let Inn : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range
  have hcardInn : Nat.card Inn = Nat.card Q :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hidx : Inn.index = 2 := by
    have h := Subgroup.card_mul_index Inn
    rw [hcardInn, hcard] at h
    have hQ : 0 < Nat.card Q := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hQ (by rw [h, mul_comm])
  have hnormal : Inn.Normal := Subgroup.normal_of_index_eq_two hidx
  have hdvd : (Inn.comap ρ).index ∣ 2 := by
    rw [Subgroup.index_comap, ← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  have hF : (Inn.comap ρ).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · exfalso
      have hn : (Inn.comap ρ).Normal := Subgroup.normal_of_index_eq_two h2
      have := hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Inn.comap ρ) with hb | ht
      · rw [hb, Subgroup.index_bot] at h2
        omega
      · rw [ht, Subgroup.index_top] at h2
        omega
  have htop : Inn.comap ρ = ⊤ := Subgroup.index_eq_one.1 hF
  intro p
  have : p ∈ Inn.comap ρ := by rw [htop]; exact Subgroup.mem_top p
  obtain ⟨w, hw⟩ := (Subgroup.mem_comap.1 this)
  exact ⟨w, hw.symm⟩


section Out

variable {G : Type} [Group G] [Finite G] {K M : Subgroup G}

theorem Setup.center_bot_of (S : Setup K) (h : ConjOf K M) : center ↥M = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine S.centerFree_of h x.1 x.2 fun y hy => ?_
  exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hx) ⟨y, hy⟩)).symm

theorem Setup.simple_of (S : Setup K) (h : ConjOf K M) : IsSimpleGroup ↥M := by
  have hq := S.quasi_of h
  have hZ := S.center_bot_of h
  have : IsSimpleGroup (↥M ⧸ center ↥M) := hq.2.1
  let e : (↥M ⧸ center ↥M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact MulEquiv.isSimpleGroup e.symm

theorem Setup.card_gt_two (S : Setup K) (h : ConjOf K M) : 2 < Nat.card ↥M := by
  by_contra hle
  push Not at hle
  obtain ⟨A, hAM, -, hr⟩ := S.rank_of h
  have hAcard : Nat.card ↥A ≤ 2 := (Subgroup.card_le_of_le hAM).trans hle
  have := rank_le_one_of_card_le_two hAcard
  omega

theorem Setup.inner_action
    (S : Setup K) {L P : Subgroup G} (hL : ConjOf K L) (hP : ConjOf K P)
    (hPN : P ≤ normalizer (L : Set G)) :
    ∀ p ∈ P, ∃ w ∈ L, ∀ x ∈ L, p * x * p⁻¹ = w * x * w⁻¹ := by
  intro p hp
  let ρ : ↥P →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have hρ : ∀ (q : ↥P) (x : ↥L), ((ρ q x : ↥L) : G) = (q : G) * x * (q : G)⁻¹ := fun q x => rfl
  have key : ∃ w : ↥L, ρ ⟨p, hp⟩ = MulAut.conj w := by
    rcases S.shape_of hL with h33 | h11
    · have := S.simple_of hP
      refine inner_of_simple_acts (fun x hx => ?_) (l33_card_aut h33) (S.card_gt_two hP) ρ ⟨p, hp⟩
      exact Subtype.ext (S.centerFree_of hL x.1 x.2 fun y hy =>
        congrArg Subtype.val (hx ⟨y, hy⟩))
    · obtain ⟨k, hk⟩ := S.m11.aut_inner ↥L h11 (ρ ⟨p, hp⟩)
      exact ⟨k, MulEquiv.ext fun x => by rw [hk]; rfl⟩
  obtain ⟨w, hw⟩ := key
  refine ⟨w, w.2, fun x hx => ?_⟩
  have := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hw
  simpa [hρ, MulAut.conj_apply] using this

end Out

end CFSG.GH74.E2.Box

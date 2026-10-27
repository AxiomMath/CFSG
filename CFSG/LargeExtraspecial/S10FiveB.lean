module

public import CFSG.LargeExtraspecial.S10FiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem comm_mem_Abar (X : Hyp10 S g t) {x : S.O} (hxL : x ∈ S.Lbar g) {b : S.O}
    (hb : b ∈ Nbar S g t) : b * x * b⁻¹ * x⁻¹ ∈ S.Lbar g ⊓ Nbar S g t := by
  have h := comm_mem_Lbar_inf_Nbar X.H (Lbar_mem_Dset X.ht) hxL hb
  have e : b * x * b⁻¹ * x⁻¹ = (x * b * x⁻¹ * b⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h

theorem comm_mul_eq {X : Type*} [Group X] {t b b' β : X} (hbt : b * t = t * b)
    (hk : b' * β * b'⁻¹ * β⁻¹ ∈ zpowers t) (hj : b * β * b⁻¹ * β⁻¹ ∈ zpowers t) :
    (b * b') * β * (b * b')⁻¹ * β⁻¹ = (b * β * b⁻¹ * β⁻¹) * (b' * β * b'⁻¹ * β⁻¹) := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨j, hj⟩ := hj
  have hc : Commute b (t ^ k) := Commute.zpow_right hbt k
  calc (b * b') * β * (b * b')⁻¹ * β⁻¹ = b * (b' * β * b'⁻¹ * β⁻¹) * β * b⁻¹ * β⁻¹ := by group
    _ = t ^ k * (b * β * b⁻¹ * β⁻¹) := by
        rw [← hk, hc.eq]
        group
    _ = (b * β * b⁻¹ * β⁻¹) * (b' * β * b'⁻¹ * β⁻¹) := by
        rw [← hj, ← hk, zpow_mul_comm]

theorem eq_one_or_eq_t (X : Hyp10 S g t) {b : S.O} (hb : b ∈ zpowers t) : b = 1 ∨ b = t :=
  mem_zpowers_of_orderOf_two X.orderOf_t hb

theorem card_le_two_mul_card_centralizer [NQHyp S g t] (X : Hyp10 S g t) {B : Subgroup S.O}
    (hB : B ≤ Nbar S g t) {β : S.O} (hβ : β ∈ Nbar S g t) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ centralizer {β} : Subgroup S.O) := by
  by_cases h : B ≤ centralizer {β}
  · rw [inf_of_le_left h]
    omega
  obtain ⟨b₀, hb₀, hb₀C⟩ := IsConcreteLE.not_le_iff_exists.mp h
  have hcomm_t : ∀ b ∈ B, b * t = t * b := fun b hb =>
    commute_of_mem_Rbar X.haQ (Nbar_le_Rbar (hB hb))
  have hct : ∀ b ∈ B, b ∉ centralizer ({β} : Set S.O) → b * β * b⁻¹ * β⁻¹ = t := by
    intro b hb hbC
    rcases eq_one_or_eq_t X (NQHyp.comm b (hB hb) β hβ) with h1 | h1
    · exact absurd (mem_centralizer_singleton_iff.mpr (by
        calc b * β = (b * β * b⁻¹ * β⁻¹) * (β * b) := by group
          _ = β * b := by rw [h1, one_mul])) hbC
    · exact h1
  have hsurj : Function.Surjective (Sum.elim
      (fun c : (B ⊓ centralizer {β} : Subgroup S.O) => (⟨c, c.2.1⟩ : B))
      (fun c : (B ⊓ centralizer {β} : Subgroup S.O) => (⟨b₀ * c, mul_mem hb₀ c.2.1⟩ : B))) := by
    rintro ⟨b, hb⟩
    by_cases hbC : b ∈ centralizer ({β} : Set S.O)
    · exact ⟨Sum.inl ⟨b, Subgroup.mem_inf.mpr ⟨hb, hbC⟩⟩, rfl⟩
    · refine ⟨Sum.inr ⟨b₀⁻¹ * b, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb₀) hb, ?_⟩⟩, ?_⟩
      · have e1 := comm_mul_eq (hcomm_t _ (inv_mem hb₀))
          (NQHyp.comm b (hB hb) β hβ) (NQHyp.comm _ (hB (inv_mem hb₀)) β hβ)
        have e2 := comm_mul_eq (hcomm_t _ (inv_mem hb₀))
          (NQHyp.comm b₀ (hB hb₀) β hβ) (NQHyp.comm _ (hB (inv_mem hb₀)) β hβ)
        rw [inv_mul_cancel, one_mul, inv_one, mul_one, mul_inv_cancel, hct b₀ hb₀ hb₀C] at e2
        rw [hct b hb hbC] at e1
        have e3 : b₀⁻¹ * β * b₀⁻¹⁻¹ * β⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_left e2.symm
        rw [e3, inv_mul_cancel] at e1
        refine mem_centralizer_singleton_iff.mpr ?_
        calc b₀⁻¹ * b * β = ((b₀⁻¹ * b) * β * (b₀⁻¹ * b)⁻¹ * β⁻¹) * (β * (b₀⁻¹ * b)) := by group
          _ = β * (b₀⁻¹ * b) := by rw [e1, one_mul]
      · exact Subtype.ext (by simp)
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_sum] at h1
  omega

theorem exists_conj_pair (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) (h7 : 7 ≤ S.width)
    {x : S.O} (hxL : x ∈ S.Lbar g) (hxN : x ∉ Nbar S g t) (hxW : x ∈ fixWstar X) :
    ∃ α ∈ S.Lbar g ⊓ Nbar S g t, ∃ β ∈ S.Lbar g ⊓ Nbar S g t, α ≠ 1 ∧ β ≠ 1 ∧ β * α ≠ 1 ∧
      (∃ m ∈ Nbar S g t, m * x * m⁻¹ = α * x) ∧ (∃ m ∈ Nbar S g t, m * x * m⁻¹ = β * x) ∧
      (∃ m ∈ Nbar S g t, m * x * m⁻¹ = β * α * x) := by
  classical
  have := X.nqHyp hCE
  obtain ⟨k, hk, hβk, -⟩ := X.exists_pair
  have hBN : S.Lbar ((k : G) * g) ⊓ Nbar S g t ≤ Nbar S g t := inf_le_right
  have hcardB : Nat.card (S.Lbar ((k : G) * g) ⊓ Nbar S g t : Subgroup S.O) =
      2 ^ (S.width - 3) := by
    rw [card_Abar_mul X hk, X.card_Abar]
  have h16 : 16 ≤ 2 ^ (S.width - 3) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAB := Abar_inf_Bbar hCE X hk hβk
  have hinj : ∀ b ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t, b * x * b⁻¹ * x⁻¹ ∈ zpowers t →
      b ∈ zpowers t := by
    intro b hb hc
    have hc' : x * b * x⁻¹ * b⁻¹ ∈ zpowers t := by
      have e : x * b * x⁻¹ * b⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hc
    have hbL := mem_Lbar_of_comm_tau hCE X hxL hxN hxW hb.2 hc'
    rw [← hAB]
    exact ⟨⟨hbL, hb.2⟩, hb⟩
  obtain ⟨b₂, hb₂B, hb₂t⟩ : ∃ b ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t, b ∉ zpowers t := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show S.Lbar ((k : G) * g) ⊓ Nbar S g t ≤ zpowers t from h)
    rw [Nat.card_zpowers, X.orderOf_t, hcardB] at h1
    omega
  have hβA := comm_mem_Abar X hxL hb₂B.2
  obtain ⟨b₁, hb₁C, hb₁F⟩ : ∃ b₁ ∈ (S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊓
      centralizer {b₂ * x * b₂⁻¹ * x⁻¹}, b₁ ∉ ({1, t, b₂, b₂ * t} : Finset S.O) := by
    by_contra h
    push Not at h
    have h1 := card_le_two_mul_card_centralizer X hBN hβA.2
    have h2 : Nat.card ((S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊓
        centralizer {b₂ * x * b₂⁻¹ * x⁻¹} : Subgroup S.O) ≤ 4 := by
      calc Nat.card ((S.Lbar ((k : G) * g) ⊓ Nbar S g t) ⊓
            centralizer {b₂ * x * b₂⁻¹ * x⁻¹} : Subgroup S.O) ≤
            Nat.card ({1, t, b₂, b₂ * t} : Finset S.O) :=
            Nat.card_le_card_of_injective (fun b => ⟨(b : S.O), h b b.2⟩)
              (fun b b' hbb' => Subtype.ext (congrArg Subtype.val hbb' :))
        _ ≤ 4 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_coe]
            exact Finset.card_le_four
    rw [hcardB] at h1
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb₁F
  obtain ⟨hb₁1, hb₁t, hb₁b₂, hb₁b₂t⟩ := hb₁F
  have hb₁B := hb₁C.1
  set b₁' : S.O := b₁ with hb₁'
  have hcomm : b₁' * (b₂ * x * b₂⁻¹ * x⁻¹) = (b₂ * x * b₂⁻¹ * x⁻¹) * b₁' :=
    mem_centralizer_singleton_iff.mp hb₁C.2
  have hαA := comm_mem_Abar X hxL hb₁B.2
  have hb₂sq := NQHyp.sq b₂ hb₂B.2
  refine ⟨b₁' * x * b₁'⁻¹ * x⁻¹, hαA, b₂ * x * b₂⁻¹ * x⁻¹, hβA, ?_, ?_, ?_,
    ⟨b₁', hb₁B.2, by group⟩, ⟨b₂, hb₂B.2, by group⟩, ⟨b₁' * b₂, mul_mem hb₁B.2 hb₂B.2, ?_⟩⟩
  · intro h
    rcases eq_one_or_eq_t X (hinj b₁' hb₁B (h ▸ one_mem _)) with h1 | h1
    · exact hb₁1 h1
    · exact hb₁t h1
  · intro h
    exact hb₂t (hinj b₂ hb₂B (h ▸ one_mem _))
  · intro h
    have hc : (b₁' * b₂) * x * (b₁' * b₂)⁻¹ * x⁻¹ =
        (b₂ * x * b₂⁻¹ * x⁻¹) * (b₁' * x * b₁'⁻¹ * x⁻¹) := by
      calc (b₁' * b₂) * x * (b₁' * b₂)⁻¹ * x⁻¹ =
            (b₁' * (b₂ * x * b₂⁻¹ * x⁻¹)) * b₁'⁻¹ * (b₁' * x * b₁'⁻¹ * x⁻¹) := by group
        _ = (b₂ * x * b₂⁻¹ * x⁻¹) * (b₁' * x * b₁'⁻¹ * x⁻¹) := by rw [hcomm]; group
    rw [h] at hc
    rcases eq_one_or_eq_t X (hinj _ (mul_mem hb₁B hb₂B) (hc ▸ one_mem _)) with h1 | h1
    ·
      have e : b₁' = b₂⁻¹ := eq_inv_of_mul_eq_one_left h1
      rcases eq_one_or_eq_t X hb₂sq with h2 | h2
      · exact hb₁b₂ (e.trans (inv_eq_of_mul_eq_one_left h2))
      · have e2 : b₂⁻¹ = b₂ * t := by
          have ht2 : t * t = 1 := by
            have := pow_orderOf_eq_one t
            rwa [X.orderOf_t, _root_.sq] at this
          calc b₂⁻¹ = b₂⁻¹ * (b₂ * b₂) * t := by rw [h2, mul_assoc, ht2, mul_one]
            _ = b₂ * t := by group
        exact hb₁b₂t (e.trans e2)
    · have e : b₁' = t * b₂⁻¹ := by
        calc b₁' = (b₁' * b₂) * b₂⁻¹ := by group
          _ = t * b₂⁻¹ := by rw [h1]
      have ht2 : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rwa [X.orderOf_t, _root_.sq] at this
      have hb₂t' : b₂ * t = t * b₂ := commute_of_mem_Rbar X.haQ (Nbar_le_Rbar hb₂B.2)
      rcases eq_one_or_eq_t X hb₂sq with h2 | h2
      · refine hb₁b₂t (e.trans ?_)
        rw [inv_eq_of_mul_eq_one_left h2, hb₂t']
      · refine hb₁b₂ (e.trans ?_)
        rw [← h2]
        group
  · calc (b₁' * b₂) * x * (b₁' * b₂)⁻¹ =
          (b₁' * (b₂ * x * b₂⁻¹ * x⁻¹)) * b₁'⁻¹ * (b₁' * x * b₁'⁻¹ * x⁻¹) * x := by group
      _ = (b₂ * x * b₂⁻¹ * x⁻¹) * (b₁' * x * b₁'⁻¹ * x⁻¹) * x := by rw [hcomm]; group

end CFSG.LargeExtraspecial.S10

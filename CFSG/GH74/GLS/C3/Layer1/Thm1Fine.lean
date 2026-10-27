module

public import CFSG.GH74.GLS.C3.Layer1.Thm1End
public import CFSG.GH74.GLS.C3.Layer1.Thm1Lemmas

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem exists_max_of_bdd {α : Type*} (S : Set α) (φ : α → ℕ) (hne : S.Nonempty)
    (hb : ∃ B : ℕ, ∀ a ∈ S, φ a ≤ B) : ∃ a ∈ S, ∀ b ∈ S, φ b ≤ φ a := by
  obtain ⟨B, hB⟩ := hb
  have hne' : (φ '' S).Nonempty := hne.image φ
  have hbdd : BddAbove (φ '' S) := ⟨B, by rintro _ ⟨a, ha, rfl⟩; exact hB a ha⟩
  obtain ⟨a, ha, hEq⟩ := Nat.sSup_mem hne' hbdd
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hEq]
  exact le_csSup hbdd ⟨b, hb, rfl⟩

theorem twoPartCard_le [Finite G] (H : Subgroup G) : twoPartCard H ≤ Nat.card G := by
  have h1 : 2 ^ (Nat.card H).factorization 2 ≤ Nat.card H :=
    Nat.ordProj_le 2 (Nat.card_pos).ne'
  exact h1.trans (Subgroup.card_le_card_group H)

theorem card_kBar_le [Finite G] (K : Subgroup G) : Nat.card (kBar K) ≤ Nat.card G := by
  have h1 : Nat.card (kBar K) ≤ Nat.card ↥K := by
    have := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K)
    exact Nat.le_of_dvd Nat.card_pos this
  exact h1.trans (Subgroup.card_le_card_group K)

theorem exists_fmax3 [Finite G] (h : ∃ (x y : G) (K : Subgroup G) (f : G), IsFU2 x y K f) :
    ∃ (x y : G) (K : Subgroup G) (f : G), FMax3 x y K f := by
  obtain ⟨x₀, y₀, K₀, f₀, h₀⟩ := h
  obtain ⟨p₁, hp₁, hmax₁⟩ := exists_max_of_bdd
    {p : G × G × Subgroup G × G | IsFU2 p.1 p.2.1 p.2.2.1 p.2.2.2}
    (fun p => Nat.card (kBar p.2.2.1)) ⟨(x₀, y₀, K₀, f₀), h₀⟩
    ⟨Nat.card G, fun p _ => card_kBar_le p.2.2.1⟩
  have h1 : FMax1 p₁.1 p₁.2.1 p₁.2.2.1 p₁.2.2.2 :=
    ⟨hp₁, fun x' y' K' f' h' => hmax₁ (x', y', K', f') h'⟩
  obtain ⟨p₂, hp₂, hmax₂⟩ := exists_max_of_bdd
    {p : G × G × Subgroup G × G | FMax1 p.1 p.2.1 p.2.2.1 p.2.2.2}
    (fun p => twoPartCard (centralizer ({p.1} : Set G))) ⟨p₁, h1⟩
    ⟨Nat.card G, fun p _ => twoPartCard_le _⟩
  have h2 : FMax2 p₂.1 p₂.2.1 p₂.2.2.1 p₂.2.2.2 :=
    ⟨hp₂, fun x' y' K' f' h' => hmax₂ (x', y', K', f') h'⟩
  obtain ⟨p₃, hp₃, hmax₃⟩ := exists_max_of_bdd
    {p : G × G × Subgroup G × G | FMax2 p.1 p.2.1 p.2.2.1 p.2.2.2}
    (fun p => twoPartCard (centralizer ({p.2.2.2} : Set G))) ⟨p₂, h2⟩
    ⟨Nat.card G, fun p _ => twoPartCard_le _⟩
  exact ⟨p₃.1, p₃.2.1, p₃.2.2.1, p₃.2.2.2, hp₃, fun x' y' K' f' h' => hmax₃ (x', y', K', f') h'⟩

theorem exists_special [Finite G] {x y : G} {K T : Subgroup G} {f : G} (hf : FMax3 x y K f)
    (hT : IsFMember x K T f) :
    ∃ f' : G, FMax3 x y K f' ∧ IsFMember x K T f' ∧ IsSpecial x y K T f' := by
  obtain ⟨f', ⟨hf'1, hf'2⟩, hmax⟩ := exists_max_of_bdd
    {f' : G | FMax3 x y K f' ∧ IsFMember x K T f'}
    (fun f' => Nat.card ↥(thompsonJ2 T ⊓ centralizer ({f'} : Set G))) ⟨f, hf, hT⟩
    ⟨Nat.card G, fun f' _ => Subgroup.card_le_card_group _⟩
  exact ⟨f', hf'1, hf'2, fun f'' h1 h2 => hmax f'' ⟨h1, h2⟩⟩

theorem exists_z [Finite G] {x : G} {K T : Subgroup G} (hsetup : Setup1D x K T)
    (hnormal : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hZ : ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
      ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z) :
    ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ ∀ t ∈ T, t * z = z * t := by
  obtain ⟨z, hzP, hz2, hzc, hZ'⟩ := hZ
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
    ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hnormal t (hsetup.sylowT.le ht) p hp.2⟩
  exact ⟨z, hzP, hz2, central_of_normal_of_center hPn hzP hz1 hzc hZ'⟩

theorem layerI_le_pumpJ (K : Subgroup G) (f : G) : layerI K f ≤ pumpJ K f := by
  unfold pumpJ pumpUp layerI
  refine le_iSup₂_of_le (1 : G) (one_mem _) ?_
  intro u hu
  exact ⟨u, hu, by simp⟩

theorem pPrimeCoreOf_le_self (J : Subgroup G) : pPrimeCoreOf 2 J ≤ J := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end CFSG.GH74.GLS.C3.Layer1.Thm1

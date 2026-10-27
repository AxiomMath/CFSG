module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

open CFSG CFSG.GH74 Subgroup

theorem not_sectionalTwoRankLE_of_char {Y : Type*} [Group Y] (X : Subgroup Y) [Finite X]
    {K : Type*} [Group K] (f : K →* Y) (hX : ∀ k, f k ∈ X)
    {E : Type*} [CommGroup E] (ψ : K →* E) (hψ : ∀ k, ψ k ^ 2 = 1)
    (hker : ∀ k, f k = 1 → ψ k = 1) {r : ℕ} (hcard : 2 ^ r < Nat.card ψ.range) :
    ¬ SectionalTwoRankLE X r := by
  intro hX4
  let φ : K →* X := f.codRestrict X hX
  have hker' : φ.rangeRestrict.ker ≤ ψ.ker := fun k hk => by
    rw [MonoidHom.mem_ker] at hk ⊢
    apply hker
    have h1 : φ k = 1 := congrArg (fun x : φ.range => (x : X)) hk
    exact congrArg (fun x : X => (x : Y)) h1
  let ψ' : φ.range →* E :=
    MonoidHom.liftOfSurjective φ.rangeRestrict φ.rangeRestrict_surjective ⟨ψ, hker'⟩
  have hψ' : ∀ k, ψ' (φ.rangeRestrict k) = ψ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ψ, hker'⟩ k
  have hrange : ψ'.range = ψ.range := by
    ext e
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨k, rfl⟩ := φ.rangeRestrict_surjective p
      exact ⟨k, (hψ' k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨φ.rangeRestrict k, hψ' k⟩
  have h2 : SectionalTwoRankLE ψ'.range r :=
    (hX4.subgroup φ.range).of_surjective ψ'.rangeRestrict ψ'.rangeRestrict_surjective
  have hψ2 : ∀ x : ψ'.range, x ^ 2 = 1 := by
    rintro ⟨_, p, rfl⟩
    obtain ⟨k, rfl⟩ := φ.rangeRestrict_surjective p
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hψ' k]
    exact hψ k
  have h3 := h2.card_le_of_elementary (⊤ : Subgroup ψ'.range) ⟨inferInstance, fun x _ => hψ2 x⟩
  rw [Subgroup.card_top, hrange] at h3
  omega

theorem two_pow_le_card_of_mulSingle_mem {F : Type*} [Field F] {n : ℕ} [Finite F]
    (hne : (-1 : Fˣ) ≠ 1) (R : Subgroup (Fin n → Fˣ))
    (h : ∀ l, (Pi.mulSingle l (-1 : Fˣ) : Fin n → Fˣ) ∈ R) : 2 ^ n ≤ Nat.card R := by
  classical
  let v : (Fin n → Bool) → (Fin n → Fˣ) := fun b l => if b l then -1 else 1
  have hv : ∀ b, v b ∈ R := by
    intro b
    have : v b = ∏ l, Pi.mulSingle l (v b l) := (Finset.univ_prod_mulSingle _).symm
    rw [this]
    refine Subgroup.prod_mem _ fun l _ => ?_
    by_cases hb : b l
    · have h1 : v b l = -1 := by simp [v, hb]
      rw [h1]
      exact h l
    · have h1 : v b l = 1 := by simp [v, hb]
      rw [h1, Pi.mulSingle_one]
      exact one_mem R
  have hinj : Function.Injective (fun b => (⟨v b, hv b⟩ : R)) := by
    intro b b' hbb
    funext l
    have h1 := congrFun (congrArg Subtype.val hbb) l
    simp only [v] at h1
    cases hb : b l <;> cases hb' : b' l
    · rfl
    · rw [hb, hb'] at h1
      exact absurd (by simpa using h1.symm) hne
    · rw [hb, hb'] at h1
      exact absurd (by simpa using h1) hne
    · rfl
  have h2 := Nat.card_le_card_of_injective _ hinj
  simpa using h2

end CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutL2Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega.AutL2

open CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

abbrev projHom (A : Subgroup (PGammaL2 F)) : A →* (F ≃+* F) :=
  SemidirectProduct.rightHom.comp A.subtype

theorem projHom_apply (A : Subgroup (PGammaL2 F)) (x : A) :
    projHom A x = (x : PGammaL2 F).right := rfl

theorem card_ker_le_ncard (A : Subgroup (PGammaL2 F)) (T : Set (PGammaL2 F))
    (h : ∀ x ∈ A, x.right = 1 → x ∈ T) : Nat.card (projHom A).ker ≤ T.ncard := by
  have : Finite ↥T := Set.toFinite T
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : PGammaL2 F), h _ x.1.2 x.2⟩) ?_
  intro x y hxy
  have h := congrArg (fun z : ↥T => (z : PGammaL2 F)) hxy
  exact Subtype.ext (Subtype.ext h)

theorem mem_zpowers_of_nm_mem {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F) {a : Fˣ}
    {ε : Bool} {σ : F ≃+* F} (hx : nm F a ε σ ∈ A) : a ∈ zpowers (stdGen F) := by
  obtain ⟨a', ha', ε', σ', -, h⟩ := hA hx
  exact (nm_injective h).1 ▸ ha'

theorem exists_nm_of_right_eq_one {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F)
    {x : PGammaL2 F} (hx : x ∈ A) (hr : x.right = 1) :
    ∃ a ∈ zpowers (stdGen F), ∃ ε : Bool, x = nm F a ε 1 := by
  obtain ⟨a, ha, ε, σ, -, rfl⟩ := hA hx
  have hσ : σ = 1 := hr
  subst hσ
  exact ⟨a, ha, ε, rfl⟩

theorem eq_of_right_eq_one_of_refl {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c : Fˣ} (ht : nm F c true 1 ∈ A)
    {x : PGammaL2 F} (hx : x ∈ A) (hr : x.right = 1) :
    x = 1 ∨ x = nm F (-1) false 1 ∨ x = nm F c true 1 ∨ x = nm F (-c) true 1 := by
  obtain ⟨a, -, ε, rfl⟩ := exists_nm_of_right_eq_one hA hx hr
  have h := (nm_commute_iff a c ε true 1 1).mp (hc _ hx _ ht)
  rw [fu_one, fu_one, twist_true] at h
  cases ε
  · rw [twist_false] at h
    have h2 : a ^ 2 = 1 := by
      have h3 : a * a * c = 1 * c :=
        calc a * a * c = a * c * a := by rw [mul_right_comm]
          _ = c * a⁻¹ * a := by rw [h]
          _ = 1 * c := by rw [inv_mul_cancel_right, one_mul]
      rw [pow_two]
      exact mul_right_cancel h3
    rcases units_eq_one_or_neg_one h2 with rfl | rfl
    · exact Or.inl nm_one
    · exact Or.inr (Or.inl rfl)
  · rw [twist_true] at h
    have h2 : (a * c⁻¹) ^ 2 = 1 := by
      have h3 : a * c⁻¹ * (a * c⁻¹) = c * a⁻¹ * (a * c⁻¹) := congrArg (· * (a * c⁻¹)) h
      rw [pow_two, h3]
      group
    rcases units_eq_one_or_neg_one h2 with h3 | h3
    · rw [mul_inv_eq_one.mp h3]
      exact Or.inr (Or.inr (Or.inl rfl))
    · have h4 : a = -c :=
        calc a = a * c⁻¹ * c := by group
          _ = -1 * c := by rw [h3]
          _ = -c := neg_one_mul c
      rw [h4]
      exact Or.inr (Or.inr (Or.inr rfl))

theorem card_ker_le_four {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F)
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {c : Fˣ} (ht : nm F c true 1 ∈ A) :
    Nat.card (projHom A).ker ≤ 4 := by
  classical
  refine (card_ker_le_ncard A
    (↑({1, nm F (-1) false 1, nm F c true 1, nm F (-c) true 1} : Finset (PGammaL2 F)))
    fun x hx hr => ?_).trans ?_
  · simpa [Finset.mem_insert] using eq_of_right_eq_one_of_refl hA hc ht hx hr
  · rw [Set.ncard_coe_finset]
    exact Finset.card_le_four

theorem card_ker_le_pow {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F)
    (hnr : ∀ c : Fˣ, nm F c true 1 ∉ A) {n : ℕ} [NeZero n]
    (hn : ∀ a : Fˣ, nm F a false 1 ∈ A → a ^ n = 1) : Nat.card (projHom A).ker ≤ n := by
  refine (card_ker_le_ncard A ((fun a : Fˣ => nm F a false 1) '' {a : Fˣ | a ^ n = 1})
    fun x hx hr => ?_).trans ?_
  · obtain ⟨a, -, ε, rfl⟩ := exists_nm_of_right_eq_one hA hx hr
    cases ε
    · exact ⟨a, hn a hx, rfl⟩
    · exact absurd hx (hnr a)
  · exact (Set.ncard_image_le (Set.toFinite _)).trans (ncard_pow_eq_one_le n)

end CFSG.OddStandard.SmallF3.Omega.AutL2

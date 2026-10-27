module

public import CFSG.CGT.PushingUpLit.BlocksCommutePrime6

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def normalClosureIn (H X : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | ∃ h ∈ H, ∃ x ∈ X, g = h * x * h⁻¹}

theorem le_normalClosureIn {H X : Subgroup G} : X ≤ normalClosureIn H X :=
  fun x hx => Subgroup.subset_closure ⟨1, one_mem H, x, hx, by simp⟩

theorem conjSub_le_normalClosureIn {H X : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSub h X ≤ normalClosureIn H X := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure ⟨h, hh, x, hx, by simp [MulAut.conj_apply]⟩

theorem normalClosureIn_le {H X : Subgroup G} (hXH : X ≤ H) : normalClosureIn H X ≤ H := by
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨h, hh, x, hx, rfl⟩
  exact mul_mem (mul_mem hh (hXH hx)) (inv_mem hh)

theorem conj_mem_normalClosureIn {H X : Subgroup G} {h' : G} (hh' : h' ∈ H) {z : G}
    (hz : z ∈ normalClosureIn H X) : h' * z * h'⁻¹ ∈ normalClosureIn H X := by
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, hh, x, hx, rfl⟩ := hg
    refine Subgroup.subset_closure ⟨h' * h, mul_mem hh' hh, x, hx, ?_⟩
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : h' * (a * b) * h'⁻¹ = (h' * a * h'⁻¹) * (h' * b * h'⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : h' * a⁻¹ * h'⁻¹ = (h' * a * h'⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem le_normalizer_normalClosureIn {H X : Subgroup G} :
    H ≤ Subgroup.normalizer (normalClosureIn H X : Set G) := by
  intro h' hh'
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_normalClosureIn hh' hz, fun hz => ?_⟩
  have := conj_mem_normalClosureIn (inv_mem hh') hz
  simpa [mul_assoc] using this

theorem normalClosureIn_lt {H X : Subgroup G} (hXH : X ≤ H) (hXs : (X.subgroupOf H).IsSubnormal)
    (hne : X ≠ H) : normalClosureIn H X < H := by
  rcases hXs.lt_normal with htop | ⟨K, hKn, hXK, hKlt⟩
  · exact absurd (le_antisymm hXH (Subgroup.subgroupOf_eq_top.1 htop)) hne
  have hle : normalClosureIn H X ≤ K.map H.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨h, hh, x, hx, rfl⟩
    refine ⟨⟨h, hh⟩ * ⟨x, hXH hx⟩ * ⟨h, hh⟩⁻¹, ?_, by simp⟩
    exact hKn.conj_mem _ (hXK (show (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H from hx)) _
  have hlt : K.map H.subtype < H := by
    refine lt_of_le_of_ne (by rintro _ ⟨k, -, rfl⟩; exact k.2) ?_
    intro heq
    apply hKlt.ne
    refine (Subgroup.eq_top_iff' _).2 fun g => ?_
    have : (g : G) ∈ K.map H.subtype := by
      rw [heq]
      exact g.2
    obtain ⟨k, hk, hkg⟩ := this
    have : k = g := Subtype.ext hkg
    rwa [← this]
  exact lt_of_le_of_lt hle hlt

variable [Finite G]

theorem eq_one_or_orderOf_eq_of_odd {Y : Subgroup G} {p : ℕ} (hprime : p.Prime)
    (hYp : Nat.card (↥Y ⧸ pCore 2 ↥Y) = p) {g : G} (hg : g ∈ Y) (hodd : Odd (orderOf g)) :
    g = 1 ∨ orderOf g = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥Y = p * Nat.card ↥(pCore 2 ↥Y) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥Y), hYp]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (pCore_isPGroup (p := 2) (G := ↥Y))
  have hdvd : orderOf g ∣ p * 2 ^ k := by
    have := orderOf_dvd_natCard (⟨g, hg⟩ : ↥Y)
    rw [Subgroup.orderOf_mk, hcard, hk] at this
    exact this
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hdp : orderOf g ∣ p := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime hprime).1 hdp with h1 | h1
  · exact Or.inl (orderOf_eq_one_iff.1 h1)
  · exact Or.inr h1

theorem card_top_conjSub (X : Subgroup G) (g : G) :
    Nat.card (↥(conjSub g X) ⧸ pCore 2 ↥(conjSub g X)) = Nat.card (↥X ⧸ pCore 2 ↥X) :=
  (Nat.card_congr (quotTopEquiv ((MulAut.conj g).subgroupMap X)).toEquiv).symm

theorem commutator_eq_bot_aux (hG : IsCharacteristicP 2 G) {p : ℕ} (hprime : p.Prime) :
    ∀ n : ℕ, ∀ H : Subgroup G, H.IsSubnormal → Nat.card ↥H = n →
      ∀ X Y : Subgroup G, IsBlockOf X → IsBlockOf Y → X ≤ H → Y ≤ H →
        Nat.card (↥X ⧸ pCore 2 ↥X) = p → Nat.card (↥Y ⧸ pCore 2 ↥Y) = p → X ≠ Y →
        ⁅X, Y⁆ = ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hH hn X Y hX hY hXH hYH hXp hYp hne
  have hXne : X ≠ H := by
    intro h
    subst h
    exact hne (eq_of_le_of_isBlock hY hX hYH).symm
  have hYne : Y ≠ H := by
    intro h
    subst h
    exact hne (eq_of_le_of_isBlock hX hY hXH)
  have hX1 := normalClosureIn_lt hXH hX.1.subgroupOf hXne
  have hY1 := normalClosureIn_lt hYH hY.1.subgroupOf hYne
  have hsubX : (normalClosureIn H X).IsSubnormal :=
    Subgroup.IsSubnormal.trans (normalClosureIn_le hXH)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le hXH)).2
        le_normalizer_normalClosureIn).isSubnormal hH
  have hsubY : (normalClosureIn H Y).IsSubnormal :=
    Subgroup.IsSubnormal.trans (normalClosureIn_le hYH)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosureIn_le hYH)).2
        le_normalizer_normalClosureIn).isSubnormal hH
  have hcommX : ∀ g₁ ∈ Y, ∀ g₂ ∈ Y, conjSub g₁ X ≠ conjSub g₂ X →
      ⁅conjSub g₁ X, conjSub g₂ X⁆ = ⊥ := by
    intro g₁ hg₁ g₂ hg₂ hne'
    exact ih (Nat.card ↥(normalClosureIn H X)) (by rw [← hn]; exact Subgroup.card_lt_of_lt hX1)
      (normalClosureIn H X) hsubX rfl (conjSub g₁ X) (conjSub g₂ X) (hX.map_conj g₁)
      (hX.map_conj g₂)
      (conjSub_le_normalClosureIn (hYH hg₁)) (conjSub_le_normalClosureIn (hYH hg₂))
      ((card_top_conjSub X g₁).trans hXp) ((card_top_conjSub X g₂).trans hXp) hne'
  have hcommY : ∀ g₁ ∈ X, ∀ g₂ ∈ X, conjSub g₁ Y ≠ conjSub g₂ Y →
      ⁅conjSub g₁ Y, conjSub g₂ Y⁆ = ⊥ := by
    intro g₁ hg₁ g₂ hg₂ hne'
    exact ih (Nat.card ↥(normalClosureIn H Y)) (by rw [← hn]; exact Subgroup.card_lt_of_lt hY1)
      (normalClosureIn H Y) hsubY rfl (conjSub g₁ Y) (conjSub g₂ Y) (hY.map_conj g₁)
      (hY.map_conj g₂)
      (conjSub_le_normalClosureIn (hXH hg₁)) (conjSub_le_normalClosureIn (hXH hg₂))
      ((card_top_conjSub Y g₁).trans hYp) ((card_top_conjSub Y g₂).trans hYp) hne'
  have hYnX : Y ≤ Subgroup.normalizer (X : Set G) := by
    refine (eq_oTwoUpper_of_short hY.2).le.trans ((Subgroup.closure_le _).2 fun g hg => ?_)
    rcases eq_one_or_orderOf_eq_of_odd hprime hYp hg.1 hg.2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact normalizes_of_prime hX hY hprime hXp hYp hcommX hg.1 h1
  have hXnY : X ≤ Subgroup.normalizer (Y : Set G) := by
    refine (eq_oTwoUpper_of_short hX.2).le.trans ((Subgroup.closure_le _).2 fun g hg => ?_)
    rcases eq_one_or_orderOf_eq_of_odd hprime hXp hg.1 hg.2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · exact normalizes_of_prime hY hX hprime hYp hXp hcommY hg.1 h1
  exact commutator_eq_bot_of_prime_normalizing hG hX hY hprime hXp hYp hXnY hYnX hne

theorem commutator_eq_bot_of_prime (hG : IsCharacteristicP 2 G) {X Y : Subgroup G}
    (hX : IsBlockOf X) (hY : IsBlockOf Y) {p : ℕ} (hprime : p.Prime)
    (hXp : Nat.card (↥X ⧸ pCore 2 ↥X) = p) (hYp : Nat.card (↥Y ⧸ pCore 2 ↥Y) = p)
    (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ :=
  commutator_eq_bot_aux hG hprime _ ⊤ Subgroup.IsSubnormal.top rfl X Y hX hY le_top le_top hXp hYp
    hne

end CFSG.CGT.PushingUpLit

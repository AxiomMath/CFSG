module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFullness

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Generic

variable {G : Type} [Group G] [Finite G]

theorem two_class_count {A : Type} [Group A] [Finite A] {P : Subgroup G} (ρ : ↥P →* Wr2 A)
    (a c : ↥P) (haτ : ρ a = tau) {γ : A} (hc : ρ c = base γ γ) (hac : IsConj (a : G) (c : G))
    {m k q : ℕ} (hm : Nat.card (centralizer ({a} : Set ↥P)) ≤ m) (hk : Nat.card ρ.ker ≤ k)
    (hq : Nat.card (centralizer ({γ} : Set A)) ≤ q) :
    ∃ c₁ c₂ : ℕ, c₁ + c₂ ≤ {g : G | IsConj (a : G) g ∧ g ∈ P}.ncard ∧
      Nat.card P ≤ c₁ * m ∧ Nat.card P ≤ c₂ * (k * (2 * q ^ 2)) := by
  have hnc : ¬ IsConj a c := by
    intro h
    have := ρ.map_isConj h
    rw [haτ, hc] at this
    have h1 : (tau : Wr2 A) = base 1 1 * tau := by rw [base_one, one_mul]
    rw [h1] at this
    exact not_isConj_base_tau γ γ 1 1 this.symm
  refine ⟨(subgroupConjClass P a).ncard, (subgroupConjClass P c).ncard, ?_, ?_, ?_⟩
  · rw [← Set.ncard_union_eq (disjoint_subgroupConjClass P hnc) (Set.toFinite _) (Set.toFinite _)]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨MonoidHom.map_isConj P.subtype hy, y.2⟩
    · exact ⟨hac.trans (MonoidHom.map_isConj P.subtype hy), y.2⟩
  · have h := ncard_subgroupConjClass_mul_card_centralizer P a
    rw [← h]
    exact Nat.mul_le_mul_left _ hm
  · have h := ncard_subgroupConjClass_mul_card_centralizer P c
    rw [← h]
    refine Nat.mul_le_mul_left _ ?_
    have hb := card_centralizer_le_card_ker_mul ρ c
    rw [hc] at hb
    have hcen : Nat.card (centralizer ({base γ γ} : Set (Wr2 A)) ⊓ ρ.range : Subgroup (Wr2 A)) ≤
        2 * q ^ 2 := by
      refine (Subgroup.card_le_of_le inf_le_left).trans ?_
      rw [card_centralizer_base_self]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq 2)
    exact hb.trans (Nat.mul_le_mul hk hcen)

omit [Finite G] in
theorem set_conj_cen_eq (a b : G) :
    {g : G | IsConj a g ∧ g ∈ Cen b} = conjCommSet a b := by
  ext g
  refine and_congr_right fun _ => ?_
  change g ∈ centralizer ({b} : Set G) ↔ g * b = b * g
  exact mem_centralizer_singleton_iff

theorem ncard_conj_in_cen_mul_le (a b : G) {n : ℕ} (hn : (conjCommSet b a).ncard ≤ n) :
    {g : G | IsConj a g ∧ g ∈ Cen b}.ncard * Nat.card (Cen a) ≤ n * Nat.card (Cen b) := by
  rw [set_conj_cen_eq]
  rw [ncard_conjCommSet_mul_card_centralizer a b]
  exact Nat.mul_le_mul_right _ hn

omit [Finite G] in
theorem ncard_involutions_le_of_quotient {C X : Type} [Group C] [Finite C] [Group X] (π : C →* X) (z : C)
    (hker : ∀ g, π g = 1 → g = 1 ∨ g = z)
    (hX : {x : X | orderOf x = 2}.Finite) :
    {g : C | orderOf g = 2}.ncard ≤ 2 * {x : X | orderOf x = 2}.ncard + 1 := by
  classical
  let S' : Set C := {g | orderOf g = 2 ∧ g ≠ z}
  have hS : {g : C | orderOf g = 2} ⊆ insert z S' := by
    intro g hg
    by_cases h : g = z
    · exact Or.inl h
    · exact Or.inr ⟨hg, h⟩
  have hS' : S'.ncard ≤ 2 * {x : X | orderOf x = 2}.ncard := by
    let rep : X → C := fun x => if h : ∃ g ∈ S', π g = x then h.choose else 1
    have hrep : ∀ g ∈ S', π (rep (π g)) = π g ∧ rep (π g) ∈ S' := by
      intro g hg
      have h : ∃ g' ∈ S', π g' = π g := ⟨g, hg, rfl⟩
      simp only [rep, h, dite_true]
      exact ⟨h.choose_spec.2, h.choose_spec.1⟩
    let f : C → X × Bool := fun g => (π g, decide (g = rep (π g)))
    have hmaps : ∀ g ∈ S', f g ∈ {x : X | orderOf x = 2} ×ˢ (Set.univ : Set Bool) := by
      intro g hg
      refine ⟨?_, Set.mem_univ _⟩
      obtain ⟨hg2, hgz⟩ := hg
      have h2 : g * g = 1 := by
        have := pow_orderOf_eq_one g
        rwa [hg2, pow_two] at this
      have h1 : π g * π g = 1 := by rw [← map_mul, h2, map_one]
      have hne : π g ≠ 1 := by
        intro h
        rcases hker g h with h' | h'
        · rw [h', orderOf_one] at hg2
          omega
        · exact hgz h'
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rwa [pow_two]) hne
    have hinj : Set.InjOn f S' := by
      intro g hg g' hg' hf
      have hπ : π g = π g' := congrArg Prod.fst hf
      have hb : decide (g = rep (π g)) = decide (g' = rep (π g')) := congrArg Prod.snd hf
      rw [← hπ] at hb
      have key : ∀ h ∈ S', π h = π g → h = rep (π g) ∨ h = rep (π g) * z := by
        intro h hh hπh
        obtain ⟨hr1, hr2⟩ := hrep g hg
        have : π ((rep (π g))⁻¹ * h) = 1 := by rw [map_mul, map_inv, hr1, hπh, inv_mul_cancel]
        rcases hker _ this with h1 | h1
        · left
          exact (inv_mul_eq_one.1 h1).symm
        · right
          rw [← h1]
          simp
      have hg1 := key g hg rfl
      have hg1' := key g' hg' hπ.symm
      have hb' : g = rep (π g) ↔ g' = rep (π g) := decide_eq_decide.1 hb
      by_cases hgr : g = rep (π g)
      · rw [hgr, hb'.1 hgr]
      · have hg'r : g' ≠ rep (π g) := fun h => hgr (hb'.2 h)
        rw [hg1.resolve_left hgr, hg1'.resolve_left hg'r]
    calc S'.ncard ≤ ({x : X | orderOf x = 2} ×ˢ (Set.univ : Set Bool)).ncard :=
          Set.ncard_le_ncard_of_injOn f hmaps hinj (hX.prod Set.finite_univ)
      _ = 2 * {x : X | orderOf x = 2}.ncard := by
          rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
          ring
  calc {g : C | orderOf g = 2}.ncard ≤ (insert z S').ncard :=
        Set.ncard_le_ncard hS (Set.toFinite _)
    _ ≤ S'.ncard + 1 := Set.ncard_insert_le z S'
    _ ≤ 2 * {x : X | orderOf x = 2}.ncard + 1 := by omega

end Generic

section HS

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem orderOf_eq_two_of_sq {x : G} (h : x * x = 1) (h1 : x ≠ 1) : orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rwa [pow_two]) h1

theorem card_cen_t_inf_cen_u_le (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {u : G}
    (hcu : Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 2880) :
    Nat.card ↥(Cen t ⊓ Cen u) ≤ 5760 := by
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  have hle := card_le_two_mul_card_inf (D := Cen t ⊓ Cen u) (L := L) (t := t)
    (fun x hx => by
      have := hx.1
      change x ∈ centralizer ({t} : Set G) at this
      rw [hin] at this
      exact mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc this)
  have hsub : Cen t ⊓ Cen u ⊓ L ≤ L ⊓ centralizer ({u} : Set G) :=
    fun x hx => ⟨hx.2, hx.1.2⟩
  have h2 := Subgroup.card_le_of_le hsub
  rw [hcu] at h2
  omega

theorem ncard_conjCommSet_le_of_twist (hL : IsSporadic ↥L .HS)
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {x : G} (hx2 : orderOf x = 2)
    (hxt : ¬ IsConj t x)
    (hA : ∀ ℓ ∈ L, orderOf ℓ = 2 → Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = 7680 →
      IsConj t (t * ℓ))
    (hB : ∀ ℓ ∈ L, orderOf ℓ = 2 → Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = 2880 →
      IsConj t ℓ) :
    (conjCommSet x t).ncard ≤ 21175 := by
  have ht : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 htL a ha
  have hLn : t ∉ L := t_not_mem_of_isSporadic_hs hL htL ht2
  rw [← ncard_involutions_hs_le_of_le L hL]
  classical
  let φ : G → G := fun y => if y ∈ L then y else t * y
  have hφ1 : ∀ y, y ∈ L → φ y = y := fun y hy => by simp [φ, hy]
  have hφ2 : ∀ y, y ∉ L → φ y = t * y := fun y hy => by simp [φ, hy]
  have hcls : ∀ y ∈ conjCommSet x t, orderOf y = 2 ∧
      ((y ∈ L ∧ Nat.card ↥(L ⊓ centralizer ({y} : Set G)) = 7680) ∨
        (y ∉ L ∧ t * y ∈ L ∧ orderOf (t * y) = 2 ∧
          Nat.card ↥(L ⊓ centralizer ({t * y} : Set G)) = 2880)) := by
    rintro y ⟨hxy, hyt⟩
    have hy2 : orderOf y = 2 := (orderOf_eq_of_isConj' hxy).symm.trans hx2
    refine ⟨hy2, ?_⟩
    have hy1 : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hy2
    have hyC : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hyt.eq
    rw [hin] at hyC
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hyC with hyL | hyL
    · left
      refine ⟨hyL, ?_⟩
      rcases card_inf_centralizer_of_involution hL hyL hy2 with h | h
      · exact h
      · exact absurd (((hB y hyL hy2 h).trans hxy.symm)) hxt
    · right
      rw [hti] at hyL
      have hyL' : y ∉ L := fun h => hLn (by simpa using mul_mem hyL (inv_mem h))
      have hyt' : y * t = t * y := hyt.eq
      have hsq : (t * y) * (t * y) = 1 := by
        calc t * y * (t * y) = t * (y * t) * y := by simp only [mul_assoc]
          _ = t * (t * y) * y := by rw [hyt']
          _ = (t * t) * (y * y) := by simp only [mul_assoc]
          _ = 1 := by rw [ht, hy1, one_mul]
      have hne : t * y ≠ 1 := by
        intro h
        have : y = t := by
          have := congrArg (fun w => t⁻¹ * w) h
          simpa [hti, ← mul_assoc, ht] using this
        exact hxt (this ▸ hxy.symm)
      have h2 : orderOf (t * y) = 2 := orderOf_eq_two_of_sq hsq hne
      refine ⟨hyL', hyL, h2, ?_⟩
      rcases card_inf_centralizer_of_involution hL hyL h2 with h | h
      · exfalso
        have := hA _ hyL h2 h
        rw [← mul_assoc, ht, one_mul] at this
        exact hxt (this.trans hxy.symm)
      · exact h
  refine Set.ncard_le_ncard_of_injOn φ ?_ ?_ (Set.toFinite _)
  · intro y hy
    obtain ⟨hy2, h | h⟩ := hcls y hy
    · rw [hφ1 y h.1]
      exact ⟨h.1, hy2⟩
    · rw [hφ2 y h.1]
      exact ⟨h.2.1, h.2.2.1⟩
  · intro y hy y' hy' hφ
    obtain ⟨-, h | h⟩ := hcls y hy <;> obtain ⟨-, h' | h'⟩ := hcls y' hy'
    · rwa [hφ1 y h.1, hφ1 y' h'.1] at hφ
    · exfalso
      rw [hφ1 y h.1, hφ2 y' h'.1] at hφ
      rw [hφ] at h
      have := h.2.symm.trans h'.2.2.2
      omega
    · exfalso
      rw [hφ2 y h.1, hφ1 y' h'.1] at hφ
      rw [← hφ] at h'
      have := h'.2.symm.trans h.2.2.2
      omega
    · rw [hφ2 y h.1, hφ2 y' h'.1] at hφ
      exact mul_left_cancel hφ

end HS

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

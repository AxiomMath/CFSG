module

import CFSG.GH74.Generic.GKFCover
import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.AGLEmbeddingD2.InnerTypes

open CFSG.Open CFSG.AGLEmbedding

section Block

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem block_perfect_nonabelian {M S L : Subgroup G} (hL : IsWeakSBlock M S L) :
    Group.IsPerfect ↥(barM M L) ∧ (∃ a b : ↥(barM M L), a * b ≠ b * a) := by
  have hq := hL.component.2.2
  refine ⟨⟨hq.1⟩, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L)) b
  exact ⟨a', b', fun h' => hab (by rw [← map_mul, ← map_mul, h'])⟩

theorem isQuasisimple_of_open {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    CFSG.IsQuasisimple Y := by
  have hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    have : Group.IsPerfect Y := ⟨hY.1⟩
    have : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hnoncomm := Group.IsPerfect.not_isMulCommutative (Y ⧸ Subgroup.center Y)
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact ⟨⟨hY.1⟩, hY.2, hnonab⟩

theorem not_three_dvd_card_center_of_alt {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {n : ℕ}
    (hn : 8 ≤ n)
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin n)) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  intro h3
  have hd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier
    (isQuasisimple_of_open hL.component.2.2) e
  rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn] at hd
  have := h3.trans hd
  omega

end Block

section PCore

theorem dvd_card_of_dvd_card_pCore_quotient {X Q : Type*} [Group X] [Finite X] [Group Q]
    (e : X ⧸ CFSG.pCore 2 X ≃* Q) {m : ℕ} (hm : Nat.Coprime m 2) (h : m ∣ Nat.card X) :
    m ∣ Nat.card Q := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X)
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  rw [hcard, ha, Nat.card_congr e.toEquiv] at h
  exact (Nat.Coprime.pow_right a hm).dvd_of_dvd_mul_right h

theorem pRank_eq_of_pCore_quotient {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    {Q : Type*} [Group Q] [Finite Q] (e : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Q) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : Open.pRank p P = Open.pRank p (⊤ : Subgroup Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥P) := by
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).exists_card_eq
    rw [ha]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have h1 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) P
  have h2 := CFSG.SectionRank.pRank_quotient_eq (p := p) (CFSG.pCore 2 ↥P) hN
  have h3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  rw [h1, ← h2, h3]

end PCore

section Rank

def shiftHom (p k : ℕ) : Multiplicative (Fin k → ZMod p) →* Equiv.Perm (Fin k × ZMod p) where
  toFun v :=
    { toFun := fun a => (a.1, a.2 + Multiplicative.toAdd v a.1)
      invFun := fun a => (a.1, a.2 - Multiplicative.toAdd v a.1)
      left_inv := fun a => by simp
      right_inv := fun a => by simp }
  map_one' := by
    ext a <;> simp
  map_mul' u v := by
    ext a <;> simp
    ring

theorem shiftHom_injective (p k : ℕ) : Function.Injective (shiftHom p k) := by
  intro u v h
  have key : ∀ i : Fin k, Multiplicative.toAdd u i = Multiplicative.toAdd v i := by
    intro i
    have := congrArg (fun σ : Equiv.Perm (Fin k × ZMod p) => (σ (i, 0)).2) h
    simpa [shiftHom] using this
  exact Multiplicative.toAdd.injective (funext key)

theorem le_pRank_perm {p : ℕ} (hp : p.Prime) {k n : ℕ} (hkn : k * p ≤ n) :
    k ≤ Open.pRank p (⊤ : Subgroup (Equiv.Perm (Fin n))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (Fin k × ZMod p) ≤ Fintype.card (Fin n) := by
    simpa [Fintype.card_prod, ZMod.card] using hkn
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ψ : Multiplicative (Fin k → ZMod p) →* Equiv.Perm (Fin n) :=
    (Equiv.Perm.viaEmbeddingHom ι).comp (shiftHom p k)
  have hψ : Function.Injective ψ :=
    (Equiv.Perm.viaEmbeddingHom_injective ι).comp (shiftHom_injective p k)
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm a b) ?_ ?_ ψ hψ
    le_top
  · intro v
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext i
    simp
  · simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_subgroup_prod {A B : Type*} [Group A] [Group B] (E : Subgroup A) (F : Subgroup B) :
    Nat.card (E.prod F) = Nat.card E * Nat.card F := by
  have h : Nat.card ((E : Set A) ×ˢ (F : Set B) : Set (A × B)) =
      Nat.card (E : Set A) * Nat.card (F : Set B) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  exact h

theorem pRank_prod_ge {p : ℕ} (hp : 1 < p) {A B : Type*} [Group A] [Finite A] [Group B]
    [Finite B] :
    Open.pRank p (⊤ : Subgroup A) + Open.pRank p (⊤ : Subgroup B) ≤
      Open.pRank p (⊤ : Subgroup (A × B)) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup A)
  obtain ⟨F, -, hF, hFc⟩ := CFSG.SectionRank.exists_pRank hp (⊤ : Subgroup B)
  have hEF : IsElemAbelian p (E.prod F) := by
    have h1 := hE.1
    have h2 := hF.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have e1 := congrArg Subtype.val (mul_comm' (⟨a.1.1, a.2.1⟩ : E) ⟨b.1.1, b.2.1⟩)
      have e2 := congrArg Subtype.val (mul_comm' (⟨a.1.2, a.2.2⟩ : F) ⟨b.1.2, b.2.2⟩)
      exact Prod.ext e1 e2
    · exact Prod.ext (hE.2 x.1 hx.1) (hF.2 x.2 hx.2)
  have hcard : Nat.card (E.prod F) =
      p ^ (Open.pRank p (⊤ : Subgroup A) + Open.pRank p (⊤ : Subgroup B)) := by
    rw [card_subgroup_prod, hEc, hFc, pow_add]
  exact CFSG.SectionRank.le_pRank hp le_top hEF hcard

end Rank

section Arithmetic

open scoped Nat

theorem ten_le_of_dvd_factorial {n : ℕ} (h : 25 ∣ n !) : 10 ≤ n := by
  by_contra hn
  have hn9 : n ≤ 9 := by omega
  revert h
  interval_cases n <;> decide

theorem fifteen_le_of_dvd_factorial {n : ℕ} (h : 125 ∣ n !) : 15 ≤ n := by
  by_contra hn
  have hn14 : n ≤ 14 := by omega
  revert h
  interval_cases n <;> decide

theorem three_le_div_add_div {r m : ℕ} (h : 25 ∣ r ! * m !) (hm : 6 ≤ m) :
    3 ≤ r / 3 + m / 3 := by
  by_contra hlt
  have hr : r ≤ 2 := by omega
  have hm8 : m ≤ 8 := by omega
  revert h
  interval_cases r <;> interval_cases m <;> decide

theorem three_le_div_five_add_div_five {r m : ℕ} (h : 125 ∣ r ! * m !) :
    3 ≤ r / 5 + m / 5 := by
  by_contra hlt
  have hr : r < 15 := by omega
  have hm : m < 15 := by omega
  have key : ∀ r < 15, ∀ m < 15, r / 5 + m / 5 < 3 → ¬ 125 ∣ r ! * m ! := by decide +kernel
  exact key r hr m hm (by omega) h

end Arithmetic

end CFSG.AGLEmbeddingD2.InnerTypes

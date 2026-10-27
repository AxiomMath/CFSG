module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightNormalizer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem blockFix_ext {r : ℕ} (x y : blockFix (Fin r))
    (h : ∀ i, (x.1 (i, false)).2 = (y.1 (i, false)).2) : x = y := by
  classical
  apply Subtype.ext
  refine Equiv.ext fun p => ?_
  obtain ⟨i, b⟩ := p
  have hx1 : ∀ p, ((x.1 p).1) = p.1 := x.2
  have hy1 : ∀ p, ((y.1 p).1) = p.1 := y.2
  have hfl : (x.1 (i, false)).2 = (y.1 (i, false)).2 := h i
  have hxne : (x.1 (i, true)).2 ≠ (x.1 (i, false)).2 := fun h => by
    have : x.1 (i, true) = x.1 (i, false) := Prod.ext (by rw [hx1, hx1]) h
    exact absurd (x.1.injective this) (by simp)
  have hyne : (y.1 (i, true)).2 ≠ (y.1 (i, false)).2 := fun h => by
    have : y.1 (i, true) = y.1 (i, false) := Prod.ext (by rw [hy1, hy1]) h
    exact absurd (y.1.injective this) (by simp)
  have hbool : ∀ a b c d : Bool, a ≠ b → c ≠ d → b = d → a = c := by decide
  refine Prod.ext (by rw [hx1, hy1]) ?_
  cases b
  · exact hfl
  · exact hbool _ _ _ _ hxne hyne hfl

variable {G : Type} [Group G]

theorem relIndex_le_card_image [Finite G] {M A V : Subgroup G} (hAM : A ≤ M) {d : ℕ}
    (θ : ↥M →* Perm (Fin d))
    (hθ : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G)) :
    (Subgroup.centralizer (V : Set G)).relIndex A ≤ Nat.card ((A.subgroupOf M).map θ) := by
  classical
  let f : ↥A →* Perm (Fin d) := θ.comp (Subgroup.inclusion hAM)
  have hker : f.ker ≤ (Subgroup.centralizer (V : Set G)).subgroupOf A := fun a ha => by
    have ha' : θ (Subgroup.inclusion hAM a) = 1 := ha
    exact hθ _ ha'
  have h1 := Subgroup.index_dvd_of_le hker
  have h2 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have hrange : f.range ≤ (A.subgroupOf M).map θ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Subgroup.inclusion hAM a, Subgroup.mem_subgroupOf.2 a.2, rfl⟩
  have h3 : Nat.card f.range ≤ Nat.card ((A.subgroupOf M).map θ) := Subgroup.card_le_of_le hrange
  have hpos : f.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (Subgroup.centralizer (V : Set G)).relIndex A
      = ((Subgroup.centralizer (V : Set G)).subgroupOf A).index := rfl
    _ ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h1
    _ ≤ _ := by rw [h2]; exact h3

theorem mk_mem_altFix_of_fixed {d : ℕ} {E : Subgroup (Perm (Fin d))} (x0 : evenWeight d)
    (hfix : ∀ g ∈ E, evenWeightPerm g x0 = x0) :
    (QuotientAddGroup.mk x0 : altHeart d) ∈ altFix d E := by
  rw [mem_altFix_iff]
  intro g hg x hx
  have h1 := QuotientAddGroup.eq.1 hx
  obtain ⟨c, hc⟩ := (mem_evenWeightOnes_iff d _).1 h1
  refine QuotientAddGroup.eq.2 ((mem_evenWeightOnes_iff d _).2 ⟨c, fun i => ?_⟩)
  have h2 : (x0 : Fin d → ZMod 2) i = (x0 : Fin d → ZMod 2) (g⁻¹ i) := by
    have := congrArg (fun y : evenWeight d => (y : Fin d → ZMod 2) i) (hfix g hg)
    exact this.symm
  have h3 := hc (g⁻¹ i)
  show -(x : Fin d → ZMod 2) (g⁻¹ i) + (x0 : Fin d → ZMod 2) i = c
  rw [h2]
  exact h3

def K4 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨
    σ = swap 0 3 * swap 1 2}
  mul_mem' := by
    have : ∀ a b : Perm (Fin 4), (a = 1 ∨ a = swap 0 1 * swap 2 3 ∨ a = swap 0 2 * swap 1 3 ∨
        a = swap 0 3 * swap 1 2) → (b = 1 ∨ b = swap 0 1 * swap 2 3 ∨ b = swap 0 2 * swap 1 3 ∨
        b = swap 0 3 * swap 1 2) → (a * b = 1 ∨ a * b = swap 0 1 * swap 2 3 ∨
        a * b = swap 0 2 * swap 1 3 ∨ a * b = swap 0 3 * swap 1 2) := by decide +kernel
    exact fun {a b} ha hb => this a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := by
    have : ∀ a : Perm (Fin 4), (a = 1 ∨ a = swap 0 1 * swap 2 3 ∨ a = swap 0 2 * swap 1 3 ∨
        a = swap 0 3 * swap 1 2) → (a⁻¹ = 1 ∨ a⁻¹ = swap 0 1 * swap 2 3 ∨
        a⁻¹ = swap 0 2 * swap 1 3 ∨ a⁻¹ = swap 0 3 * swap 1 2) := by decide +kernel
    exact fun {a} ha => this a ha

theorem K4_normal : ∀ g σ : Perm (Fin 4), σ ∈ K4 → g * σ * g⁻¹ ∈ K4 := by
  have : ∀ g σ : Perm (Fin 4), (σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨
      σ = swap 0 3 * swap 1 2) → (g * σ * g⁻¹ = 1 ∨ g * σ * g⁻¹ = swap 0 1 * swap 2 3 ∨
      g * σ * g⁻¹ = swap 0 2 * swap 1 3 ∨ g * σ * g⁻¹ = swap 0 3 * swap 1 2) := by
    decide +kernel
  exact fun g σ h => this g σ h

theorem K4_isPGroup : IsPGroup 2 K4 := by
  have : ∀ σ : Perm (Fin 4), (σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨
      σ = swap 0 3 * swap 1 2) → σ ^ 2 ^ 1 = 1 := by decide +kernel
  intro x
  exact ⟨1, Subtype.ext (this x.1 x.2)⟩

theorem a4_mem_K4 : (swap (0 : Fin 4) 1 * swap 2 3) ∈ K4 := Or.inr (Or.inl rfl)

@[expose] def xvec {d : ℕ} (g0 g2 : Fin d) : evenWeight d :=
  ⟨fun p => (if p = g0 then 1 else 0) + (if p = g2 then 1 else 0), by
    classical
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    decide⟩

theorem xvec_apply {d : ℕ} (g0 g2 p : Fin d) :
    ((xvec g0 g2 : evenWeight d) : Fin d → ZMod 2) p =
      (if p = g0 then 1 else 0) + (if p = g2 then 1 else 0) := rfl

theorem mk_ewp_ne {d : ℕ} (f : Perm (Fin d)) {g0 g1 g2 g3 q : Fin d} (h01 : f g0 = g1)
    (h23 : f g2 = g3) (hq0 : q ≠ g0) (hq1 : q ≠ g1)
    (hq2 : q ≠ g2) (hq3 : q ≠ g3) (h10' : g1 ≠ g0) (h12 : g1 ≠ g2) (h02 : g0 ≠ g2) :
    (QuotientAddGroup.mk (evenWeightPerm f (xvec g0 g2)) : altHeart d) ≠
      QuotientAddGroup.mk (xvec g0 g2) := by
  intro h
  have h1 := QuotientAddGroup.eq.1 h.symm
  obtain ⟨c, hc⟩ := (mem_evenWeightOnes_iff d _).1 h1
  have hcoord : ∀ p, c = -((xvec g0 g2 : evenWeight d) : Fin d → ZMod 2) p +
      ((xvec g0 g2 : evenWeight d) : Fin d → ZMod 2) (f⁻¹ p) := fun p => (hc p).symm
  have hfq0 : f⁻¹ q ≠ g0 := fun h' => hq1 (by rw [Equiv.Perm.inv_eq_iff_eq, h01] at h'; exact h')
  have hfq2 : f⁻¹ q ≠ g2 := fun h' => hq3 (by rw [Equiv.Perm.inv_eq_iff_eq, h23] at h'; exact h')
  have hc0 : c = 0 := by
    have := hcoord q
    simp only [xvec_apply, hq0, hq2, hfq0, hfq2, ite_false] at this
    rw [this]; decide
  have hf1 : f⁻¹ g1 = g0 := by rw [Equiv.Perm.inv_eq_iff_eq, h01]
  have h' := hcoord g1
  simp only [xvec_apply, hf1, h10', h12, h02, ite_true, ite_false, hc0] at h'
  revert h'
  decide

noncomputable def movedPairs {r s : ℕ} (E : Subgroup (Perm (OmegaE r s))) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter fun k => ∃ g ∈ E, g (Sum.inl (k, true)) = Sum.inl (k, false)

theorem mem_movedPairs {r s : ℕ} {E : Subgroup (Perm (OmegaE r s))} {k : Fin r} :
    k ∈ movedPairs E ↔ ∃ g ∈ E, g (Sum.inl (k, true)) = Sum.inl (k, false) := by
  classical
  unfold movedPairs
  simp

theorem card_le_two_pow_movedPairs {r s : ℕ} {E : Subgroup (Perm (OmegaE r s))} (hE : E ≤ Wr r s) :
    Nat.card E ≤ 2 ^ (movedPairs E).card := by
  classical
  have hrep : ∀ g : E, ∃ x : blockFix (Fin r), embL r s x = g.1 := fun g => by
    obtain ⟨x, hx, hxg⟩ := hE g.2
    exact ⟨⟨x, hx⟩, hxg⟩
  choose X hX using hrep
  let F : E → (↥(movedPairs E) → Bool) := fun g k => ((X g).1 (k.1, false)).2
  have hF : Function.Injective F := by
    intro g h hgh
    have hbit : ∀ (g : E) (k : Fin r), k ∉ movedPairs E → ((X g).1 (k, false)).2 = false := by
      intro g k hk
      by_contra hb
      have hb' : ((X g).1 (k, false)).2 = true := by simpa using hb
      have hx1 : ∀ p, (((X g).1 p).1) = p.1 := (X g).2
      have h1 : (X g).1 (k, false) = (k, true) :=
        Prod.ext (by rw [hx1]) hb'
      have h2 : (X g).1 (k, true) = (k, false) := by
        rcases hq : (X g).1 (k, true) with ⟨k', b'⟩
        have hk' : k' = k := by have := hx1 (k, true); rw [hq] at this; exact this
        subst hk'
        cases b'
        · rfl
        · exfalso
          have : (X g).1 (k', true) = (X g).1 (k', false) := by rw [hq, h1]
          exact absurd ((X g).1.injective this) (by simp)
      apply hk
      rw [mem_movedPairs]
      refine ⟨g.1, g.2, ?_⟩
      rw [← hX g, embL_apply_inl, h2]
    have hall : ∀ k, ((X g).1 (k, false)).2 = ((X h).1 (k, false)).2 := by
      intro k
      by_cases hk : k ∈ movedPairs E
      · exact congrFun hgh ⟨k, hk⟩
      · rw [hbit g k hk, hbit h k hk]
    have := blockFix_ext (X g) (X h) hall
    exact Subtype.ext (by rw [← hX g, ← hX h, this])
  calc Nat.card E ≤ Nat.card (↥(movedPairs E) → Bool) := Nat.card_le_card_of_injective F hF
    _ = 2 ^ (movedPairs E).card := by simp [Nat.card_eq_fintype_card]

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

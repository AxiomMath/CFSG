module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtCard
public import Mathlib.GroupTheory.SemidirectProduct

public section

universe u

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

open Subgroup CFSG.GroupTheory.TwoWeights

theorem weights_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    {a u₁ u₂ u₃ x y : G} (D : Data a u₁ u₂ u₃ x y) {U : Type*} [Group U] [Finite U]
    (ρ : G →* MulAut U) (E : Subgroup U) (hEp : ∀ e ∈ E, e ^ p = 1)
    (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hEN : ∀ g : G, g * a = a * g → ∀ e ∈ E, ρ g e ∈ E)
    (hEinv : ∀ e ∈ E, ρ a e = e⁻¹) : E = ⊥ ∨ p ^ 8 ≤ Nat.card E := by
  let E' : Subgroup (SemidirectProduct U G ρ) := E.map SemidirectProduct.inl
  have hfin : Finite E' :=
    Finite.of_equiv E (E.equivMapOfInjective SemidirectProduct.inl SemidirectProduct.inl_injective
      ).toEquiv
  have D' := D.map (SemidirectProduct.inr : G →* SemidirectProduct U G ρ)
  have hmem : ∀ z : SemidirectProduct U G ρ, z ∈ E' ↔ ∃ e ∈ E, SemidirectProduct.inl e = z :=
    fun z => Iff.rfl
  have hconj : ∀ (g : G) (e : U), SemidirectProduct.inr g * SemidirectProduct.inl e *
      (SemidirectProduct.inr g)⁻¹ = SemidirectProduct.inl (ρ g e) := fun g e => by
    rw [SemidirectProduct.inl_aut]
    simp
  have hEp' : ∀ e ∈ E', e ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hEp e he, map_one]
  have hEc' : ∀ e ∈ E', ∀ f ∈ E', e * f = f * e := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    rw [← map_mul, ← map_mul, hEc e he f hf]
  have hcomm_a : ∀ g ∈ ({u₁, u₂, u₃, a, x, y, x⁻¹, y⁻¹} : Set G), g * a = a * g := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact D.u₁_a
    · exact D.u₂_a
    · exact D.u₃_a
    · rfl
    · exact D.a_x.symm
    · exact D.a_y.symm
    · calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * a) * x⁻¹ := by rw [D.a_x]
        _ = a * x⁻¹ := by group
    · calc y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * a) * y⁻¹ := by rw [D.a_y]
        _ = a * y⁻¹ := by group
  have hN' : ∀ g ∈ ({SemidirectProduct.inr u₁, SemidirectProduct.inr u₂, SemidirectProduct.inr u₃,
      SemidirectProduct.inr a, SemidirectProduct.inr x, SemidirectProduct.inr y,
      (SemidirectProduct.inr x)⁻¹, (SemidirectProduct.inr y)⁻¹} :
      Set (SemidirectProduct U G ρ)), ∀ e ∈ E', g * e * g⁻¹ ∈ E' := by
    intro g hg e he
    obtain ⟨e₀, he₀, rfl⟩ := he
    have key : ∀ g₀ : G, g₀ ∈ ({u₁, u₂, u₃, a, x, y, x⁻¹, y⁻¹} : Set G) →
        (SemidirectProduct.inr g₀ : SemidirectProduct U G ρ) * SemidirectProduct.inl e₀ *
          (SemidirectProduct.inr g₀)⁻¹ ∈ E' := by
      intro g₀ hg₀
      rw [hconj]
      exact ⟨ρ g₀ e₀, hEN g₀ (hcomm_a g₀ hg₀) e₀ he₀, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact key _ (by simp)
    · exact key _ (by simp)
    · exact key _ (by simp)
    · exact key _ (by simp)
    · exact key _ (by simp)
    · exact key _ (by simp)
    · have := key x⁻¹ (by simp)
      simpa using this
    · have := key y⁻¹ (by simp)
      simpa using this
  have hinv' : ∀ e ∈ E', SemidirectProduct.inr a * e * (SemidirectProduct.inr a)⁻¹ = e⁻¹ := by
    rintro _ ⟨e, he, rfl⟩
    rw [hconj, hEinv e he, map_inv]
  have hw := WtP.weights_card_p hp2 D' E' hEp' hEc' hN' hinv'
  rcases hw with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective E SemidirectProduct.inl_injective).1 h
  · right
    have hc : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective SemidirectProduct.inl_injective
    rwa [hc] at h

theorem star_mod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    {a u₁ u₂ u₃ x y : G} (D : Data a u₁ u₂ u₃ x y) :
    ∀ (n : ℕ) (U : Type u) [Group U] [Finite U], IsPGroup p U → Nat.card U = n → n < p ^ 8 →
      ∀ ρ : G →* MulAut U, ρ a = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ _ hU hcard hlt ρ
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have hρa2 : ∀ u : U, ρ a (ρ a u) = u := by
    intro u
    have h1 : ρ (a * a) = 1 := by rw [D.a_a, map_one]
    have h2 : (ρ a * ρ a) u = u := by rw [← map_mul, D.a_a, map_one]; rfl
    exact h2
  by_cases hsub : Subsingleton U
  · refine MulEquiv.ext fun u => ?_
    exact Subsingleton.elim _ _
  have : Nontrivial U := not_subsingleton_iff_nontrivial.1 hsub
  let Z : Subgroup U :=
    { carrier := {z | z ∈ center U ∧ z ^ p = 1}
      mul_mem' := fun {z z'} hz hz' => ⟨mul_mem hz.1 hz'.1, by
        have hc : Commute z z' := (Subgroup.mem_center_iff.1 hz'.1 z)
        rw [hc.mul_pow, hz.2, hz'.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {z} hz => ⟨inv_mem hz.1, by rw [inv_pow, hz.2, inv_one]⟩ }
  have hZmem : ∀ z, z ∈ Z ↔ z ∈ center U ∧ z ^ p = 1 := fun z => Iff.rfl
  have hZc : ∀ z ∈ Z, ∀ v : U, v * z = z * v := fun z hz v => Subgroup.mem_center_iff.1 hz.1 v
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [hZc z hz g]
    simpa using hz⟩
  have hZne : ∃ z ∈ Z, z ≠ 1 := by
    have : Nontrivial ↥(center U) := hU.center_nontrivial
    have hZp : IsPGroup p ↥(center U) := hU.to_subgroup _
    have hZcard : p ∣ Nat.card ↥(center U) := by
      rcases hZp.card_eq_or_dvd with h | h
      · have := Finite.one_lt_card (α := ↥(center U))
        omega
      · exact h
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' p hZcard
    refine ⟨((z₀ : ↥(center U)) : U), ⟨z₀.2, ?_⟩, ?_⟩
    · have h : z₀ ^ p = 1 := by rw [← hz₀]; exact pow_orderOf_eq_one z₀
      have := congrArg (fun g : ↥(center U) => (g : U)) h
      simpa using this
    · intro h
      have h1 : z₀ = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hz₀
      exact hp.out.one_lt.ne hz₀
  have hZinv : ∀ (g : G), ∀ z ∈ Z, ρ g z ∈ Z := by
    intro g z hz
    refine ⟨Subgroup.mem_center_iff.2 fun v => ?_, ?_⟩
    · obtain ⟨w, rfl⟩ := (ρ g).surjective v
      rw [← map_mul, ← map_mul, hZc z hz w]
    · rw [← map_pow, hz.2, map_one]
  let E : Subgroup U :=
    { carrier := {z | z ∈ Z ∧ ρ a z = z⁻¹}
      mul_mem' := fun {z z'} hz hz' => ⟨mul_mem hz.1 hz'.1, by
        rw [map_mul, hz.2, hz'.2, mul_inv_rev, ← mul_inv_rev, ← mul_inv_rev, hZc z hz.1 z']⟩
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {z} hz => ⟨inv_mem hz.1, by rw [map_inv, hz.2]⟩ }
  have hEmem : ∀ z, z ∈ E ↔ z ∈ Z ∧ ρ a z = z⁻¹ := fun z => Iff.rfl
  have hEcard : Nat.card E < p ^ 8 := by
    have h1 : Nat.card E ≤ Nat.card U := Nat.card_le_card_of_injective _ Subtype.val_injective
    omega
  have hEa : E = ⊥ := by
    have hw := weights_mod hp2 D ρ E (fun e he => he.1.2) (fun e he f hf => (hZc e he.1 f).symm)
      (fun g hg e he => by
        refine ⟨hZinv g e he.1, ?_⟩
        have h1 : ρ a (ρ g e) = ρ g (ρ a e) := by
          have : ρ (a * g) = ρ (g * a) := by rw [hg]
          have h2 := congrArg (fun m : MulAut U => m e) this
          simpa using h2
        rw [h1, he.2, map_inv])
      (fun e he => he.2)
    rcases hw with h | h
    · exact h
    · exact absurd (lt_of_lt_of_le hEcard h) (lt_irrefl _)
  have hZfix : ∀ z ∈ Z, ρ a z = z := by
    intro z hz
    have hw : z⁻¹ * ρ a z ∈ E := by
      refine ⟨mul_mem (inv_mem hz) (hZinv a z hz), ?_⟩
      rw [map_mul, map_inv, hρa2, mul_inv_rev, inv_inv]
    rw [hEa, Subgroup.mem_bot] at hw
    exact (inv_mul_eq_one.1 hw).symm
  have hmapZ : ∀ g : G, Z.map ((ρ g : U ≃* U) : U →* U) = Z := by
    intro g
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hZinv g z hz
    · intro z hz
      refine ⟨ρ g⁻¹ z, hZinv g⁻¹ z hz, ?_⟩
      show ρ g (ρ g⁻¹ z) = z
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  let ρ' : G →* MulAut (U ⧸ Z) :=
    { toFun := fun g => QuotientGroup.congr Z Z (ρ g) (hmapZ g)
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | _ u => simp
      map_mul' := fun g g' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | _ u => simp [QuotientGroup.congr_mk] }
  have hQp : IsPGroup p (U ⧸ Z) := hU.of_surjective (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z)
  have hQcard : Nat.card (U ⧸ Z) < n := by
    have h1 := Subgroup.card_mul_index Z
    have h2 : 2 ≤ Nat.card Z := by
      obtain ⟨z, hz, hz1⟩ := hZne
      have : 1 < Nat.card Z := by
        apply Finite.one_lt_card_iff_nontrivial.2
        exact ⟨⟨⟨z, hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
      omega
    have h3 : Z.index = Nat.card (U ⧸ Z) := rfl
    have h4 : 0 < Nat.card (U ⧸ Z) := Nat.card_pos
    rw [h3] at h1
    calc Nat.card (U ⧸ Z) < 2 * Nat.card (U ⧸ Z) := by omega
      _ ≤ Nat.card Z * Nat.card (U ⧸ Z) := Nat.mul_le_mul_right _ h2
      _ = n := by rw [h1, hcard]
  have hρ'a := ih _ hQcard (U ⧸ Z) hQp rfl (lt_trans hQcard hlt) ρ'
  refine MulEquiv.ext fun u => ?_
  have hq : ρ' a (QuotientGroup.mk u) = QuotientGroup.mk u := by rw [hρ'a]; rfl
  have hq' : QuotientGroup.mk (ρ a u) = (QuotientGroup.mk u : U ⧸ Z) := by
    have := hq
    simpa [ρ', QuotientGroup.congr_mk] using this
  have hc : u⁻¹ * ρ a u ∈ Z := QuotientGroup.eq.1 hq'.symm
  have hc1 : ρ a (u⁻¹ * ρ a u) = (u⁻¹ * ρ a u)⁻¹ := by
    rw [map_mul, map_inv, hρa2, mul_inv_rev, inv_inv]
  have hc2 := hZfix _ hc
  rw [hc1] at hc2
  have h3 : (u⁻¹ * ρ a u) * (u⁻¹ * ρ a u) = 1 := by
    calc (u⁻¹ * ρ a u) * (u⁻¹ * ρ a u) = (u⁻¹ * ρ a u) * (u⁻¹ * ρ a u)⁻¹ := by rw [hc2]
      _ = 1 := mul_inv_cancel _
  have h4 : u⁻¹ * ρ a u = 1 := by
    obtain ⟨m, hm⟩ := hpodd
    have h5 : (u⁻¹ * ρ a u) ^ p = u⁻¹ * ρ a u := by
      rw [hm, pow_succ, pow_mul, sq, h3, one_pow, one_mul]
    rw [hc.2] at h5
    exact h5.symm
  exact (inv_mul_eq_one.1 h4).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WtP

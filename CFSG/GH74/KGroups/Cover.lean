module

public import CFSG.GH74.KGroups.Generic
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.KGroups

variable {K : Type*} [Group K]

@[expose] def inducedAut (φ : MulAut K) : MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) φ (Subgroup.map_center_eq φ)

@[expose] def inducedHom : MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun := inducedAut
  map_one' := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem inducedHom_mk (φ : MulAut K) (x : K) :
    inducedHom φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem hom_center_trivial (hK : Group.IsPerfect K) (f : K →* Subgroup.center K) :
    ∀ x, f x = 1 := by
  have := hK
  have h1 : Subsingleton f.range := by
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    have : IsMulCommutative f.range := by
      constructor
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact (b.1.2.comm ?_).symm
    infer_instance
  intro x
  have : (⟨f x, x, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

theorem inducedHom_injective (hK : Group.IsPerfect K) :
    Function.Injective (inducedHom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro φ hφ
  have h1 : ∀ x : K, x⁻¹ * φ x ∈ Subgroup.center K := by
    intro x
    have := congrArg (fun f : MulAut (K ⧸ Subgroup.center K) => f (QuotientGroup.mk x)) hφ
    simp only [inducedHom_mk, MulAut.one_apply] at this
    have h2 := QuotientGroup.eq.1 this.symm
    exact h2
  let f : K →* Subgroup.center K := MonoidHom.mk' (fun x => ⟨x⁻¹ * φ x, h1 x⟩) (by
    intro x y
    apply Subtype.ext
    have h3 := Subgroup.mem_center_iff.1 (h1 x) y⁻¹
    show (x * y)⁻¹ * φ (x * y) = (x⁻¹ * φ x) * (y⁻¹ * φ y)
    calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by simp [mul_assoc]
      _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by rw [h3]
      _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by simp [mul_assoc])
  have hf := hom_center_trivial hK f
  apply MulEquiv.ext
  intro x
  have := congrArg Subtype.val (hf x)
  simp only [f, MonoidHom.mk'_apply] at this
  have h4 : x⁻¹ * φ x = 1 := this
  simpa using (inv_mul_eq_one.1 h4).symm

theorem elemAb_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (p : ℕ) (B : Subgroup G) (hB : ElemAb p B) :
    ElemAb p (B.map f) ∧ Nat.card (B.map f) = Nat.card B := by
  refine ⟨⟨?_, ?_⟩, Subgroup.card_map_of_injective hf⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hB.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hB.2 a ha, map_one]

theorem cover_elemAb_card_le (hK : Group.IsPerfect K) (p N : ℕ)
    (H : ∀ B : Subgroup (MulAut (K ⧸ Subgroup.center K)), ElemAb p B → Nat.card B ≤ N)
    (B : Subgroup (MulAut K)) (hB : ElemAb p B) : Nat.card B ≤ N := by
  obtain ⟨h1, h2⟩ := elemAb_map (inducedHom (K := K)) (inducedHom_injective hK) p B hB
  have := H _ h1
  rwa [h2] at this

theorem cover_autCentralizer (hK : Group.IsPerfect K)
    (H : ∀ R : Subgroup (MulAut (K ⧸ Subgroup.center K)), ElemAb 3 R → Nat.card R = 9 →
      ∀ ψ : MulAut (K ⧸ Subgroup.center K), ψ ^ 2 = 1 → (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1)
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  obtain ⟨h1, h2⟩ := elemAb_map (inducedHom (K := K)) (inducedHom_injective hK) 3 R hR
  have := H _ h1 (by rw [h2, hcard]) (inducedHom ψ) (by rw [← map_pow, hψ, map_one])
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hc r hr])
  exact inducedHom_injective hK (by rw [this, map_one])

theorem cover_pumpup [Finite K] (hK : Group.IsPerfect K) (hZ : Nat.card (Subgroup.center K) ≤ 2)
    (H : ∀ β : MulAut (K ⧸ Subgroup.center K), β ^ 2 = 1 → β ≠ 1 →
      ∀ Lb : Subgroup (K ⧸ Subgroup.center K), (∀ x ∈ Lb, β x = x) → Group.IsPerfect Lb →
        Lb ≠ ⊥ → Nat.card Lb = 60)
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K) (hL : ∀ x ∈ L, α x = x)
    (hLp : Group.IsPerfect L) (hLn : ¬ ∀ a b : L, a * b = b * a) :
    Nat.card L = 60 ∨ Nat.card L = 120 := by
  have hb1 : inducedHom α ≠ 1 := fun h => hα1 (inducedHom_injective hK (by rw [h, map_one]))
  set Z := Subgroup.center K with hZdef
  let q : K →* K ⧸ Z := QuotientGroup.mk' Z
  let Lb : Subgroup (K ⧸ Z) := L.map q
  have hperf : Group.IsPerfect Lb := Group.IsPerfect.map q
  have hne : Lb ≠ ⊥ := by
    intro hbot
    apply hLn
    have hLZ : ∀ x ∈ L, x ∈ Z := by
      intro x hx
      have : q x ∈ Lb := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    intro a b
    apply Subtype.ext
    exact ((Subgroup.mem_center_iff.1 (hLZ a a.2)) b).symm
  have hfix : ∀ y ∈ Lb, inducedHom α y = y := by
    rintro _ ⟨x, hx, rfl⟩
    show inducedHom α (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [inducedHom_mk, hL x hx]
  have h60 : Nat.card Lb = 60 :=
    H (inducedHom α) (by rw [← map_pow, hα2, map_one]) hb1 Lb hfix hperf hne
  let g : L →* K ⧸ Z := q.comp L.subtype
  have hrange : g.range = Lb := by
    ext y
    simp only [MonoidHom.mem_range, g, q]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, h60] at hcard
  have hkerZ : ∀ x : g.ker, ((x : L) : K) ∈ Z := by
    intro x
    have := x.2
    simp only [MonoidHom.mem_ker, g, q, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hker : Nat.card g.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : g.ker => (⟨((x : L) : K), hkerZ x⟩ : Z)) ?_) hZ
    intro a b hab
    have h1 : ((a : L) : K) = ((b : L) : K) := congrArg (fun z : Z => (z : K)) hab
    apply Subtype.ext
    exact Subtype.ext h1
  have hpos : 0 < Nat.card g.ker := Nat.card_pos
  have : Nat.card g.ker = 1 ∨ Nat.card g.ker = 2 := by omega
  rcases this with h | h
  · left; rw [hcard, h]
  · right; rw [hcard, h]

theorem cover_pumpup_solvable [Finite K] (hK : Group.IsPerfect K)
    (H : ∀ β : MulAut (K ⧸ Subgroup.center K), β ^ 2 = 1 → β ≠ 1 →
      ∀ Lb : Subgroup (K ⧸ Subgroup.center K), (∀ x ∈ Lb, β x = x) → Group.IsSolvable Lb)
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K) (hL : ∀ x ∈ L, α x = x)
    (hLp : Group.IsPerfect L) (hLn : ¬ ∀ a b : L, a * b = b * a) : False := by
  have hb1 : inducedHom α ≠ 1 := fun h => hα1 (inducedHom_injective hK (by rw [h, map_one]))
  set Z := Subgroup.center K with hZdef
  let q : K →* K ⧸ Z := QuotientGroup.mk' Z
  let Lb : Subgroup (K ⧸ Z) := L.map q
  have hperf : Group.IsPerfect Lb := Group.IsPerfect.map q
  have hfix : ∀ y ∈ Lb, inducedHom α y = y := by
    rintro _ ⟨x, hx, rfl⟩
    show inducedHom α (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [inducedHom_mk, hL x hx]
  have hsol := H (inducedHom α) (by rw [← map_pow, hα2, map_one]) hb1 Lb hfix
  have hbot : Lb = ⊥ := by
    by_contra hne
    have : Nontrivial Lb := (Subgroup.nontrivial_iff_ne_bot Lb).2 hne
    have := hsol
    have h2 := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Lb)
    have h3 := hperf.commutator_eq_top
    exact absurd h3 (ne_of_lt h2)
  apply hLn
  have hLZ : ∀ x ∈ L, x ∈ Z := by
    intro x hx
    have : q x ∈ Lb := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  intro a b
  apply Subtype.ext
  exact ((Subgroup.mem_center_iff.1 (hLZ a a.2)) b).symm

end CFSG.GH74.KGroups

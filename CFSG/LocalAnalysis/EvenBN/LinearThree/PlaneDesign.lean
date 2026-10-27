module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Equiv

section Plane

variable {Ω : Type*}

@[expose] def orbitLines (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) : Set (Set Ω) :=
  {ℓ | ∃ γ ∈ Γ, ℓ = (γ : Ω → Ω) '' ℓ₀}

theorem image_mem_orbitLines {Γ : Subgroup (Perm Ω)} {ℓ₀ : Set Ω} {γ : Perm Ω} (hγ : γ ∈ Γ) :
    (γ : Ω → Ω) '' ℓ₀ ∈ orbitLines Γ ℓ₀ :=
  ⟨γ, hγ, rfl⟩

theorem exists_two_trans {Γ : Subgroup (Perm Ω)} {o : Ω} (h1 : ∀ x, ∃ g ∈ Γ, g o = x)
    (h2 : ∀ x y, x ≠ o → y ≠ o → ∃ g ∈ Γ, g o = o ∧ g x = y) {x₁ x₂ y₁ y₂ : Ω} (hx : x₁ ≠ x₂)
    (hy : y₁ ≠ y₂) : ∃ g ∈ Γ, g x₁ = y₁ ∧ g x₂ = y₂ := by
  obtain ⟨a, ha, hao⟩ := h1 x₁
  obtain ⟨b, hb, hbo⟩ := h1 y₁
  have hax : a⁻¹ x₂ ≠ o := fun h => hx (by
    rw [Perm.inv_eq_iff_eq] at h
    rw [← hao, h])
  have hby : b⁻¹ y₂ ≠ o := fun h => hy (by
    rw [Perm.inv_eq_iff_eq] at h
    rw [← hbo, h])
  obtain ⟨c, hc, hco, hcx⟩ := h2 _ _ hax hby
  refine ⟨b * c * a⁻¹, Γ.mul_mem (Γ.mul_mem hb hc) (Γ.inv_mem ha), ?_, ?_⟩
  · have : a⁻¹ x₁ = o := by rw [Perm.inv_eq_iff_eq, hao]
    simp only [Perm.mul_apply, this, hco, hbo]
  · simp only [Perm.mul_apply, hcx]
    simp

theorem orbitLines_eq_of_mem {Γ : Subgroup (Perm Ω)} {ℓ₀ : Set Ω} {o : Ω}
    (hstab : ∀ a ∈ ℓ₀, ∃ σ ∈ Γ, (σ : Ω → Ω) '' ℓ₀ = ℓ₀ ∧ σ o = a)
    (hspread : ∀ δ ∈ Γ, δ o = o → ∀ b ∈ ℓ₀, b ≠ o → δ b ∈ ℓ₀ → (δ : Ω → Ω) '' ℓ₀ = ℓ₀)
    {ℓ₁ ℓ₂ : Set Ω} (h₁ : ℓ₁ ∈ orbitLines Γ ℓ₀) (h₂ : ℓ₂ ∈ orbitLines Γ ℓ₀) {x y : Ω}
    (hxy : x ≠ y) (hx₁ : x ∈ ℓ₁) (hy₁ : y ∈ ℓ₁) (hx₂ : x ∈ ℓ₂) (hy₂ : y ∈ ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨γ₁, hγ₁, rfl⟩ := h₁
  obtain ⟨γ₂, hγ₂, rfl⟩ := h₂
  have norm : ∀ γ ∈ Γ, x ∈ (γ : Ω → Ω) '' ℓ₀ →
      ∃ γ' ∈ Γ, γ' o = x ∧ (γ' : Ω → Ω) '' ℓ₀ = (γ : Ω → Ω) '' ℓ₀ := by
    rintro γ hγ ⟨a, ha, hax⟩
    obtain ⟨σ, hσ, hσℓ, hσo⟩ := hstab a ha
    refine ⟨γ * σ, Γ.mul_mem hγ hσ, ?_, ?_⟩
    · rw [Perm.mul_apply, hσo, hax]
    · rw [Perm.coe_mul, Set.image_comp, hσℓ]
  obtain ⟨γ₁', hγ₁', hγ₁'o, hγ₁'ℓ⟩ := norm γ₁ hγ₁ hx₁
  obtain ⟨γ₂', hγ₂', hγ₂'o, hγ₂'ℓ⟩ := norm γ₂ hγ₂ hx₂
  rw [← hγ₁'ℓ, ← hγ₂'ℓ]
  rw [← hγ₁'ℓ] at hy₁
  rw [← hγ₂'ℓ] at hy₂
  obtain ⟨b, hb, hby⟩ := hy₂
  obtain ⟨b', hb', hb'y⟩ := hy₁
  have hδΓ : γ₁'⁻¹ * γ₂' ∈ Γ := Γ.mul_mem (Γ.inv_mem hγ₁') hγ₂'
  have hδo : (γ₁'⁻¹ * γ₂') o = o := by
    rw [Perm.mul_apply, hγ₂'o, Perm.inv_eq_iff_eq, hγ₁'o]
  have hbo : b ≠ o := by
    rintro rfl
    exact hxy (hγ₂'o.symm.trans hby)
  have hδb : (γ₁'⁻¹ * γ₂') b = b' := by
    rw [Perm.mul_apply, hby, Perm.inv_eq_iff_eq, hb'y]
  have hsp := hspread _ hδΓ hδo b hb hbo (hδb ▸ hb')
  have e : (γ₂' : Ω → Ω) = (γ₁' : Ω → Ω) ∘ ((γ₁'⁻¹ * γ₂' : Perm Ω) : Ω → Ω) := by
    funext z
    simp
  rw [e, Set.image_comp, hsp]

structure GoodLineQ (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) (o : Ω) (q : ℕ) : Prop where
  one_lt : 1 < q
  card : Nat.card Ω = q ^ 2
  mem : o ∈ ℓ₀
  ncard : ℓ₀.ncard = q
  trans₂ : ∀ x₁ x₂ y₁ y₂ : Ω, x₁ ≠ x₂ → y₁ ≠ y₂ → ∃ g ∈ Γ, g x₁ = y₁ ∧ g x₂ = y₂
  stab : ∀ a ∈ ℓ₀, ∃ σ ∈ Γ, (σ : Ω → Ω) '' ℓ₀ = ℓ₀ ∧ σ o = a
  spread : ∀ δ ∈ Γ, δ o = o → ∀ b ∈ ℓ₀, b ≠ o → δ b ∈ ℓ₀ → (δ : Ω → Ω) '' ℓ₀ = ℓ₀

namespace GoodLineQ

variable {Γ : Subgroup (Perm Ω)} {ℓ₀ : Set Ω} {o : Ω} {q : ℕ}

theorem finite (hG : GoodLineQ Γ ℓ₀ o q) : Finite Ω :=
  Nat.finite_of_card_ne_zero (by rw [hG.card]; exact pow_ne_zero 2 (by have := hG.one_lt; omega))

theorem exists_ne (hG : GoodLineQ Γ ℓ₀ o q) : ∃ o' ∈ ℓ₀, o' ≠ o := by
  by_contra hcon
  push Not at hcon
  have hsub : ℓ₀ ⊆ {o} := fun x hx => hcon x hx
  have := Set.ncard_le_ncard hsub (Set.finite_singleton o)
  rw [hG.ncard, Set.ncard_singleton] at this
  have := hG.one_lt
  omega

theorem exists_line (hG : GoodLineQ Γ ℓ₀ o q) {x y : Ω} (hxy : x ≠ y) :
    ∃ ℓ ∈ orbitLines Γ ℓ₀, x ∈ ℓ ∧ y ∈ ℓ := by
  obtain ⟨o', ho', hne⟩ := hG.exists_ne
  obtain ⟨g, hg, hgo, hgo'⟩ := hG.trans₂ o o' x y hne.symm hxy
  exact ⟨(g : Ω → Ω) '' ℓ₀, ⟨g, hg, rfl⟩, ⟨o, hG.mem, hgo⟩, ⟨o', ho', hgo'⟩⟩

theorem eq_of_mem (hG : GoodLineQ Γ ℓ₀ o q) {ℓ₁ ℓ₂ : Set Ω} (h₁ : ℓ₁ ∈ orbitLines Γ ℓ₀)
    (h₂ : ℓ₂ ∈ orbitLines Γ ℓ₀) {x y : Ω} (hxy : x ≠ y) (hx₁ : x ∈ ℓ₁) (hy₁ : y ∈ ℓ₁)
    (hx₂ : x ∈ ℓ₂) (hy₂ : y ∈ ℓ₂) : ℓ₁ = ℓ₂ :=
  orbitLines_eq_of_mem hG.stab hG.spread h₁ h₂ hxy hx₁ hy₁ hx₂ hy₂

theorem ncard_line (hG : GoodLineQ Γ ℓ₀ o q) {ℓ : Set Ω} (hℓ : ℓ ∈ orbitLines Γ ℓ₀) :
    ℓ.ncard = q := by
  obtain ⟨γ, -, rfl⟩ := hℓ
  rw [Set.ncard_image_of_injective _ γ.injective, hG.ncard]

theorem card_lines_through (hG : GoodLineQ Γ ℓ₀ o q) (x : Ω) :
    {ℓ | ℓ ∈ orbitLines Γ ℓ₀ ∧ x ∈ ℓ}.ncard = q + 1 := by
  classical
  have := hG.finite
  have : Fintype Ω := Fintype.ofFinite Ω
  set F : Finset (Set Ω) := Finset.univ.filter (fun ℓ => ℓ ∈ orbitLines Γ ℓ₀ ∧ x ∈ ℓ) with hF
  set t : Set Ω → Finset Ω := fun ℓ => (Finset.univ.filter (· ∈ ℓ)).erase x with ht
  have hdisj : (F : Set (Set Ω)).PairwiseDisjoint t := by
    intro ℓ hℓ ℓ' hℓ' hne
    simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hℓ hℓ'
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    simp only [ht, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    exact hne (hG.eq_of_mem hℓ.1 hℓ'.1 (Ne.symm hy.1) hℓ.2 hy.2 hℓ'.2 hy'.2)
  have hunion : F.biUnion t = Finset.univ.erase x := by
    ext y
    simp only [Finset.mem_biUnion, hF, ht, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨ℓ, -, hy, -⟩
      exact hy
    · intro hy
      obtain ⟨ℓ, hℓ, hx, hy'⟩ := hG.exists_line (Ne.symm hy)
      exact ⟨ℓ, ⟨hℓ, hx⟩, hy, hy'⟩
  have hline : ∀ ℓ ∈ F, (t ℓ).card = q - 1 := by
    intro ℓ hℓ
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rw [ht, Finset.card_erase_of_mem (by simpa using hℓ.2), ← hG.ncard_line hℓ.1,
      ← Set.ncard_coe_finset, Finset.coe_filter_univ]
    rfl
  have hsum : (F.biUnion t).card = F.card * (q - 1) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hline]
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hG.card] at hsum
  have hset : {ℓ | ℓ ∈ orbitLines Γ ℓ₀ ∧ x ∈ ℓ} = (F : Set (Set Ω)) := by
    ext ℓ
    simp [hF]
  rw [hset, Set.ncard_coe_finset]
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by have := hG.one_lt; omega⟩
  have h1 : (r + 2) ^ 2 - 1 = (r + 3) * (r + 1) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [h1, show r + 2 - 1 = r + 1 by omega] at hsum
  have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos r) hsum.symm
  omega

@[expose] def joinLine (Γ : Subgroup (Perm Ω)) (ℓ₀ : Set Ω) (x y : Ω) : Set Ω :=
  {z | ∀ ℓ ∈ orbitLines Γ ℓ₀, x ∈ ℓ → y ∈ ℓ → z ∈ ℓ}

theorem joinLine_eq (hG : GoodLineQ Γ ℓ₀ o q) {ℓ : Set Ω} (hℓ : ℓ ∈ orbitLines Γ ℓ₀) {x y : Ω}
    (hxy : x ≠ y) (hx : x ∈ ℓ) (hy : y ∈ ℓ) : joinLine Γ ℓ₀ x y = ℓ := by
  ext z
  refine ⟨fun hz => hz ℓ hℓ hx hy, fun hz ℓ' hℓ' hx' hy' => ?_⟩
  rwa [← hG.eq_of_mem hℓ hℓ' hxy hx hy hx' hy']

theorem joinLine_spec (hG : GoodLineQ Γ ℓ₀ o q) {x y : Ω} (hxy : x ≠ y) :
    joinLine Γ ℓ₀ x y ∈ orbitLines Γ ℓ₀ ∧ x ∈ joinLine Γ ℓ₀ x y ∧ y ∈ joinLine Γ ℓ₀ x y := by
  obtain ⟨ℓ, hℓ, hx, hy⟩ := hG.exists_line hxy
  rw [hG.joinLine_eq hℓ hxy hx hy]
  exact ⟨hℓ, hx, hy⟩

theorem existsUnique_parallel (hG : GoodLineQ Γ ℓ₀ o q) {ℓ : Set Ω} (hℓ : ℓ ∈ orbitLines Γ ℓ₀)
    {x : Ω} (hx : x ∉ ℓ) : ∃! m, m ∈ orbitLines Γ ℓ₀ ∧ x ∈ m ∧ Disjoint ℓ m := by
  have := hG.finite
  have hxa : ∀ a ∈ ℓ, x ≠ a := fun a ha h => hx (h ▸ ha)
  set Lx : Set (Set Ω) := {m | m ∈ orbitLines Γ ℓ₀ ∧ x ∈ m} with hLx
  set Mx : Set (Set Ω) := {m | m ∈ Lx ∧ ¬ Disjoint ℓ m} with hMx
  have himage : Mx = joinLine Γ ℓ₀ x '' ℓ := by
    ext m
    constructor
    · rintro ⟨⟨hm, hxm⟩, hdm⟩
      obtain ⟨a, haℓ, ham⟩ := Set.not_disjoint_iff.mp hdm
      exact ⟨a, haℓ, hG.joinLine_eq hm (hxa a haℓ) hxm ham⟩
    · rintro ⟨a, haℓ, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hG.joinLine_spec (hxa a haℓ)
      exact ⟨⟨h1, h2⟩, Set.not_disjoint_iff.mpr ⟨a, haℓ, h3⟩⟩
  have hinj : Set.InjOn (joinLine Γ ℓ₀ x) ℓ := by
    intro a ha b hb hab
    by_contra hne
    obtain ⟨h1, h2, h3⟩ := hG.joinLine_spec (hxa a ha)
    have hb' : b ∈ joinLine Γ ℓ₀ x a := by
      rw [hab]
      exact (hG.joinLine_spec (hxa b hb)).2.2
    exact hx ((hG.eq_of_mem hℓ h1 hne ha hb h3 hb').symm ▸ h2)
  have hMcard : Mx.ncard = q := by
    rw [himage, hinj.ncard_image, ← hG.ncard_line hℓ]
  have hLcard : Lx.ncard = q + 1 := hG.card_lines_through x
  have hsub : Mx ⊆ Lx := fun m hm => hm.1
  have hdiff : (Lx \ Mx).ncard = 1 := by
    rw [Set.ncard_sdiff hsub (Set.toFinite _), hLcard, hMcard]
    omega
  have hset : {m | m ∈ orbitLines Γ ℓ₀ ∧ x ∈ m ∧ Disjoint ℓ m} = Lx \ Mx := by
    ext m
    simp only [hLx, hMx, Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hm, hxm, hdm⟩
      exact ⟨⟨hm, hxm⟩, fun h => h.2 hdm⟩
    · rintro ⟨⟨hm, hxm⟩, hdm⟩
      exact ⟨hm, hxm, Classical.byContradiction fun h => hdm ⟨⟨hm, hxm⟩, h⟩⟩
  rw [← hset] at hdiff
  obtain ⟨m₀, hm₀⟩ := Set.ncard_eq_one.mp hdiff
  have key : ∀ m, (m ∈ orbitLines Γ ℓ₀ ∧ x ∈ m ∧ Disjoint ℓ m) ↔ m = m₀ := fun m => by
    rw [← Set.mem_singleton_iff, ← hm₀]
    rfl
  exact ⟨m₀, (key m₀).mpr rfl, fun m hm => (key m).mp hm⟩

end GoodLineQ

end Plane

end CFSG.LocalAnalysis.EvenBN.LinearThree

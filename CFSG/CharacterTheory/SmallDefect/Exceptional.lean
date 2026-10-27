module

public import CFSG.CharacterTheory.Blocks.NormTwoGram
public import CFSG.CharacterTheory.Blocks.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.SmallDefect

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

@[expose] def IsSpecialSet (H : Subgroup G) (K : Set G) : Prop :=
  K ⊆ H ∧ (∀ x ∈ K, ∀ h ∈ H, h⁻¹ * x * h ∈ K) ∧ ∀ x ∈ K, ∀ a : G, a⁻¹ * x * a ∈ H → a ∈ H

theorem inducedFunction_sub' (H : Subgroup G) (α β : H → ℂ) :
    inducedFunction H (α - β) = inducedFunction H α - inducedFunction H β := by
  funext x
  simp only [inducedFunction, Pi.sub_apply, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem inducedFunction_add' (H : Subgroup G) (α β : H → ℂ) :
    inducedFunction H (α + β) = inducedFunction H α + inducedFunction H β := by
  funext x
  simp only [inducedFunction, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem inducedFunction_smul' (H : Subgroup G) (c : ℂ) (α : H → ℂ) :
    inducedFunction H (c • α) = c • inducedFunction H α := by
  funext x
  simp only [inducedFunction, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

theorem inducedFunction_special_restrict {H : Subgroup G} {K : Set G} (hK : IsSpecialSet H K)
    {α : H → ℂ} (hα : BlocksIsClassFunction α) (hsupp : ∀ h : H, (h : G) ∉ K → α h = 0)
    (h : H) : inducedFunction H α h = α h := by
  by_cases hhK : (h : G) ∈ K
  · refine inducedFunction_eq_on_trivial_intersection_support H K α (fun e c => hα e c) hsupp
      ?_ h hhK
    intro x hx c hc hcx
    exact hc (hK.2.2 x hx c (hK.1 hcx))
  · rw [hsupp h hhK]
    unfold inducedFunction
    rw [Finset.sum_eq_zero, mul_zero]
    intro c _
    split_ifs with hc
    · apply hsupp
      intro hcK
      apply hhK
      have hback : c⁻¹⁻¹ * (c⁻¹ * (h : G) * c) * c⁻¹ = h := by group
      have hcH : c⁻¹ ∈ H := by
        refine hK.2.2 _ hcK c⁻¹ ?_
        rw [hback]
        exact h.property
      have h2 := hK.2.1 _ hcK c⁻¹ hcH
      rwa [hback] at h2
    · rfl

theorem inducedFunction_special_vanish {H : Subgroup G} {K : Set G}
    {α : H → ℂ} (hsupp : ∀ h : H, (h : G) ∉ K → α h = 0)
    (x : G) (hx : ∀ a : G, a⁻¹ * x * a ∉ K) : inducedFunction H α x = 0 :=
  inducedFunction_eq_zero_of_support_avoids_conjugates H K α hsupp x hx

theorem inducedFunction_special_inner {H : Subgroup G} {K : Set G} (hK : IsSpecialSet H K)
    {α β : H → ℂ} (hβ : BlocksIsClassFunction β) (hβsupp : ∀ h : H, (h : G) ∉ K → β h = 0) :
    BlocksInnerProduct (inducedFunction H α) (inducedFunction H β) = BlocksInnerProduct α β := by
  rw [blocksInnerProduct_inducedFunction_left H α _
    (fun e c => inducedFunction_conjugate H β e c)]
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  dsimp only
  rw [inducedFunction_special_restrict hK hβ hβsupp h]

theorem blocksInnerProduct_inducedFunction_right (H : Subgroup G) (α : H → ℂ) {ψ : G → ℂ}
    (hψ : BlocksIsClassFunction ψ) :
    BlocksInnerProduct ψ (inducedFunction H α) = BlocksInnerProduct (fun h : H => ψ h) α := by
  have h1 := blocksInnerProduct_inducedFunction_left H α ψ hψ
  have hswap : ∀ {X : Type} [Group X] [Fintype X] (f g : X → ℂ),
      BlocksInnerProduct f g = starRingEnd ℂ (BlocksInnerProduct g f) := by
    intro X _ _ f g
    unfold BlocksInnerProduct
    rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hswap, h1, ← hswap]

theorem blocksInnerProduct_sub_sub {X : Type} [Group X] [Fintype X] {a b c d : X → ℂ}
    (ha : a ∈ BlocksIrr X) (hb : b ∈ BlocksIrr X) (hc : c ∈ BlocksIrr X)
    (hd : d ∈ BlocksIrr X) :
    BlocksInnerProduct (a - b) (c - d) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
        (if b = d then 1 else 0) := by
  have h := blocksInnerProduct_irreducible_differences ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
  simpa only [Subtype.mk.injEq] using h

theorem isClassFunction_of_mem {X : Type} [Group X] [Finite X] {χ : X → ℂ}
    (hχ : χ ∈ BlocksIrr X) : BlocksIsClassFunction χ :=
  blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)

theorem exceptional_characters {ι : Type} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    {H : Subgroup G} {K : Set G} (hK : IsSpecialSet H K) (h1 : (1 : G) ∉ K)
    (θ : ι → H → ℂ) (hθ : ∀ i, θ i ∈ BlocksIrr H) (hθinj : Function.Injective θ)
    (hagree : ∀ i j, ∀ h : H, (h : G) ∉ K → θ i h = θ j h) :
    ∃ (χ : ι → G → ℂ) (ε : ℤ), (∀ i, χ i ∈ BlocksIrr G) ∧ Function.Injective χ ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ i j, inducedFunction H (θ i - θ j) = (ε : ℂ) • (χ i - χ j)) ∧
      (∀ i j, ∀ h : H, χ i h - ε * θ i h = χ j h - ε * θ j h) ∧
      (∀ ψ ∈ BlocksIrr G, ∀ i j,
        BlocksInnerProduct (fun h : H => ψ h) (θ i) -
            BlocksInnerProduct (fun h : H => ψ h) (θ j) =
          ε * ((if ψ = χ i then 1 else 0) - (if ψ = χ j then 1 else 0))) ∧
      (∀ x : G, (∀ a : G, a⁻¹ * x * a ∉ K) → ∀ i j, χ i x = χ j x) := by
  have hne : Nonempty ι := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨i₀⟩ := hne
  let ρ := {i : ι // i ≠ i₀}
  have hρ : Nonempty ρ := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hcard : Fintype.card ι ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro a b
      by_contra hab
      by_cases ha : a = i₀
      · exact hempty.false ⟨b, fun hb => hab (ha.trans hb.symm)⟩
      · exact hempty.false ⟨a, ha⟩
    omega
  have hdiffsupp : ∀ i j, ∀ h : H, (h : G) ∉ K → (θ i - θ j) h = 0 := by
    intro i j h hh
    rw [Pi.sub_apply, hagree i j h hh, sub_self]
  have hdiffclass : ∀ i j, BlocksIsClassFunction (θ i - θ j) := by
    intro i j g c
    simp only [Pi.sub_apply]
    rw [isClassFunction_of_mem (hθ i), isClassFunction_of_mem (hθ j)]
  let f : ρ → G → ℂ := fun i => inducedFunction H (θ i.1 - θ i₀)
  have hfv : ∀ i, f i ∈ BlocksVChar G := fun i =>
    inducedFunction_mem_blocksVChar H ((BlocksVChar H).sub_mem
      (AddSubgroup.subset_closure (hθ i.1)) (AddSubgroup.subset_closure (hθ i₀)))
  have hf1 : ∀ i, f i 1 = 0 := by
    intro i
    have hv := inducedFunction_special_vanish (H := H) (hdiffsupp i.1 i₀) (1 : G) (by
      intro a
      simpa only [mul_one, inv_mul_cancel] using h1)
    exact hv
  have hgram : ∀ i j, BlocksInnerProduct (f i) (f j) = 1 + if i = j then 1 else 0 := by
    intro i j
    change BlocksInnerProduct (inducedFunction H (θ i.1 - θ i₀))
      (inducedFunction H (θ j.1 - θ i₀)) = _
    rw [inducedFunction_special_inner hK (hdiffclass j.1 i₀) (hdiffsupp j.1 i₀),
      blocksInnerProduct_sub_sub (hθ i.1) (hθ i₀) (hθ j.1) (hθ i₀)]
    have hij : θ i.1 = θ j.1 ↔ i = j := ⟨fun h => Subtype.ext (hθinj h), fun h => h ▸ rfl⟩
    have hi0 : θ i.1 ≠ θ i₀ := fun h => i.2 (hθinj h)
    have hj0 : θ i₀ ≠ θ j.1 := fun h => j.2 (hθinj h).symm
    simp only [hij, hi0, hj0, ↓reduceIte]
    split_ifs <;> ring
  obtain ⟨common, χ', ε, hχ'inj, hχ'ne, hε, -, hχ'⟩ :=
    blocksVChar_norm_two_gram_common_sign f hfv hf1 (by intro i j; rw [hgram i j]; congr)
  let χ : ι → G → ℂ := fun i => if hi : i = i₀ then (common : G → ℂ) else (χ' ⟨i, hi⟩ : G → ℂ)
  have hχ0 : χ i₀ = common := by simp [χ]
  have hχi : ∀ i (hi : i ≠ i₀), χ i = χ' ⟨i, hi⟩ := by
    intro i hi
    simp [χ, hi]
  have hind0 : ∀ i, inducedFunction H (θ i - θ i₀) = (ε : ℂ) • (χ i - χ i₀) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [sub_self, sub_self, smul_zero]
      funext x
      simp [inducedFunction]
    · rw [hχi i hi, hχ0]
      exact hχ' ⟨i, hi⟩
  have hind : ∀ i j, inducedFunction H (θ i - θ j) = (ε : ℂ) • (χ i - χ j) := by
    intro i j
    have h := congrArg₂ (· - ·) (hind0 i) (hind0 j)
    rw [← inducedFunction_sub', sub_sub_sub_cancel_right, ← smul_sub,
      sub_sub_sub_cancel_right] at h
    exact h
  have hχirr : ∀ i, χ i ∈ BlocksIrr G := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, hχ0]
      exact common.2
    · rw [hχi i hi]
      exact (χ' ⟨i, hi⟩).2
  have hχinj : Function.Injective χ := by
    intro i j hij
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · rw [hi, hj]
    · rw [hi, hχ0, hχi j hj] at hij
      exact absurd (Subtype.ext hij.symm) (hχ'ne _)
    · rw [hj, hχ0, hχi i hi] at hij
      exact absurd (Subtype.ext hij) (hχ'ne _)
    · rw [hχi i hi, hχi j hj] at hij
      exact congrArg Subtype.val (hχ'inj (Subtype.ext hij))
  have hεc : (ε : ℂ) = 1 ∨ (ε : ℂ) = -1 := by
    rcases hε with rfl | rfl <;> simp
  refine ⟨χ, ε, hχirr, hχinj, hε, hind, ?_, ?_, ?_⟩
  ·
    intro i j h
    have hr := congrFun (hind i j) h
    rw [inducedFunction_special_restrict hK (hdiffclass i j) (hdiffsupp i j) h] at hr
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
    have hsq : (ε : ℂ) * ε = 1 := by rcases hεc with h | h <;> rw [h] <;> norm_num
    linear_combination (-(ε : ℂ)) * hr - (χ i h - χ j h) * hsq
  ·
    intro ψ hψ i j
    have hψc := isClassFunction_of_mem hψ
    have hfr := blocksInnerProduct_inducedFunction_right H (θ i - θ j) hψc
    rw [hind i j] at hfr
    have hlin : BlocksInnerProduct (fun h : H => ψ h) (θ i - θ j) =
        BlocksInnerProduct (fun h : H => ψ h) (θ i) -
          BlocksInnerProduct (fun h : H => ψ h) (θ j) := by
      unfold BlocksInnerProduct
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [Pi.sub_apply, map_sub, mul_sub]
    rw [← hlin, ← hfr]
    have hreal : starRingEnd ℂ (ε : ℂ) = ε := map_intCast (starRingEnd ℂ) ε
    unfold BlocksInnerProduct
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_sub, hreal]
    have hpair : ∀ k, (Nat.card G : ℂ)⁻¹ * ∑ x, ψ x * starRingEnd ℂ (χ k x) =
        if ψ = χ k then 1 else 0 := by
      intro k
      have h := blocksInnerProduct_irreducible ⟨ψ, hψ⟩ ⟨χ k, hχirr k⟩
      simpa only [BlocksInnerProduct, Subtype.mk.injEq] using h
    rw [← hpair i, ← hpair j]
    have hterm : ∀ x, ψ x * (ε * (starRingEnd ℂ (χ i x) - starRingEnd ℂ (χ j x))) =
        ε * (ψ x * starRingEnd ℂ (χ i x)) - ε * (ψ x * starRingEnd ℂ (χ j x)) := by
      intro x
      ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  ·
    intro x hx i j
    have hv := congrFun (hind i j) x
    rw [inducedFunction_special_vanish (hdiffsupp i j) x hx] at hv
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hv
    have hε0 : (ε : ℂ) ≠ 0 := by rcases hεc with h | h <;> rw [h] <;> norm_num
    have := (mul_eq_zero.mp hv.symm).resolve_left hε0
    exact sub_eq_zero.mp this

theorem exceptional_disjoint {ι κ : Type} {H : Subgroup G} {K : Set G} (hK : IsSpecialSet H K)
    (θ : ι → H → ℂ) (θ' : κ → H → ℂ) (χ : ι → G → ℂ) (χ' : κ → G → ℂ) (ε ε' : ℤ)
    (hχ : ∀ i, χ i ∈ BlocksIrr G) (hχ' : ∀ k, χ' k ∈ BlocksIrr G)
    (hχinj : Function.Injective χ) (hχ'inj : Function.Injective χ')
    (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hind : ∀ i j, inducedFunction H (θ i - θ j) = (ε : ℂ) • (χ i - χ j))
    (hind' : ∀ k l, inducedFunction H (θ' k - θ' l) = (ε' : ℂ) • (χ' k - χ' l))
    (hclass' : ∀ k l, BlocksIsClassFunction (θ' k - θ' l))
    (hsupp' : ∀ k l, ∀ h : H, (h : G) ∉ K → (θ' k - θ' l) h = 0)
    (horth : ∀ i j k l, BlocksInnerProduct (θ i - θ j) (θ' k - θ' l) = 0)
    (hι : ∀ i : ι, ∃ j, j ≠ i) (hκ : ∀ k : κ, ∃ l, l ≠ k) :
    ∀ i k, χ i ≠ χ' k := by
  intro i k hik
  obtain ⟨j, hji⟩ := hι i
  obtain ⟨l, hlk⟩ := hκ k
  have h := inducedFunction_special_inner (α := θ i - θ j) hK (hclass' k l) (hsupp' k l)
  rw [horth, hind, hind'] at h
  have hscal : ∀ (a b : ℤ) (f g : G → ℂ), (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      BlocksInnerProduct ((a : ℂ) • f) ((b : ℂ) • g) = (a * b : ℂ) * BlocksInnerProduct f g := by
    intro a b f g _ _
    unfold BlocksInnerProduct
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_intCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hscal ε ε' _ _ hε hε'] at h
  have hεε : ((ε * ε' : ℤ) : ℂ) ≠ 0 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num
  push_cast at hεε
  have h0 := (mul_eq_zero.mp h).resolve_left hεε
  rw [blocksInnerProduct_sub_sub (hχ i) (hχ j) (hχ' k) (hχ' l), ← hik] at h0
  have hjn : χ j ≠ χ i := fun h => hji (hχinj h)
  have hil : χ i ≠ χ' l := by
    rw [hik]
    exact fun h => hlk (hχ'inj h).symm
  simp only [hjn, hil, ↓reduceIte] at h0
  split_ifs at h0 <;> norm_num at h0

end CFSG.SmallDefect

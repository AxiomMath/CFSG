module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

section Frob

variable {I : Type} [CommGroup I]

theorem pow_apply_eq_self {γ : MulAut I} {x : I} (h : γ x = x) (n : ℕ) : (γ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem pow_apply_mem {γ : MulAut I} {D : Subgroup I} (hD : ∀ x ∈ D, γ x ∈ D) {x : I} (hx : x ∈ D)
    (n : ℕ) : (γ ^ n) x ∈ D := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hD _ ih

theorem prod_shift {F : ℕ → I} (h : F 7 = F 0) :
    ∏ j ∈ Finset.range 7, F (j + 1) = ∏ j ∈ Finset.range 7, F j := by
  have h3 : (∏ j ∈ Finset.range 7, F j) * F 7 = (∏ j ∈ Finset.range 7, F (j + 1)) * F 0 := by
    rw [← Finset.prod_range_succ, Finset.prod_range_succ' F 7]
  rw [h] at h3
  exact (mul_right_cancel h3).symm

theorem prod_pow_eq_one {γ : MulAut I} {D : Subgroup I} (hD : ∀ x ∈ D, γ x ∈ D) (h7 : γ ^ 7 = 1)
    (hfpf : ∀ x ∈ D, γ x = x → x = 1) {w : I} (hw : w ∈ D) :
    ∏ j ∈ Finset.range 7, (γ ^ j) w = 1 := by
  set F : ℕ → I := fun j => (γ ^ j) w with hF
  have h1 : γ (∏ j ∈ Finset.range 7, F j) = ∏ j ∈ Finset.range 7, F (j + 1) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hF]
    rw [← MulAut.mul_apply, ← pow_succ']
  have h2 : F 7 = F 0 := by simp [hF, h7]
  have h4 := prod_shift h2
  have hmem : ∏ j ∈ Finset.range 7, F j ∈ D :=
    Subgroup.prod_mem _ fun j _ => pow_apply_mem hD hw j
  exact hfpf _ hmem (h1.trans h4)

theorem mul_pow_comm_aux {α β : MulAut I} (hαβ : α * β = β ^ 2 * α) (j : ℕ) :
    α * β ^ j = (β ^ j) ^ 2 * α := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc α * β ^ (j + 1) = (α * β ^ j) * β := by rw [pow_succ, mul_assoc]
      _ = (β ^ j) ^ 2 * α * β := by rw [ih]
      _ = (β ^ j) ^ 2 * (α * β) := by rw [mul_assoc]
      _ = (β ^ j) ^ 2 * (β ^ 2 * α) := by rw [hαβ]
      _ = (β ^ (j + 1)) ^ 2 * α := by
        rw [← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
        congr 2
        ring

theorem frob_core (D : Subgroup I) (hsq : ∀ x : I, x * x = 1) {α β : MulAut I}
    (hαD : ∀ x ∈ D, α x ∈ D) (hβD : ∀ x ∈ D, β x ∈ D)
    (hα3 : α ^ 3 = 1) (hβ7 : β ^ 7 = 1) (hαβ : α * β = β ^ 2 * α)
    (hfpf : ∀ x ∈ D, β x = x → x = 1) :
    (∃ x ∈ D, x ≠ 1 ∧ α x = x) ∨ ∀ z ∈ D, z = 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hno, z₀, hz₀, hz₀1⟩ := hcon
  have hT : ∀ x ∈ D, x * α x * (α ^ 2) x = 1 := by
    intro x hx
    set t := x * α x * (α ^ 2) x with ht
    have hxα : α x ∈ D := hαD x hx
    have hxα2 : (α ^ 2) x ∈ D := by rw [pow_two, MulAut.mul_apply]; exact hαD _ hxα
    have htD : t ∈ D := D.mul_mem (D.mul_mem hx hxα) hxα2
    by_contra h1
    apply hno t htD h1
    have h3 : (α ^ 3) x = x := by rw [hα3]; rfl
    have e1 : α ((α ^ 2) x) = x := by
      rw [← MulAut.mul_apply, ← pow_succ']; exact h3
    have e2 : α (α x) = (α ^ 2) x := by
      rw [pow_two, MulAut.mul_apply]
    rw [ht, map_mul, map_mul, e1, e2]
    exact (mul_comm _ _).trans (mul_assoc _ _ _).symm
  have hkey : ∀ z ∈ D, ∀ j : ℕ, z * ((β ^ j * α) z) * ((β ^ (3 * j) * α ^ 2) z) = 1 := by
    intro z hz j
    set γ := β ^ j with hγ
    have hαγ : α * γ = γ ^ 2 * α := mul_pow_comm_aux hαβ j
    have c1 : γ⁻¹ * α * γ = γ * α := by
      calc γ⁻¹ * α * γ = γ⁻¹ * (α * γ) := by rw [mul_assoc]
        _ = γ⁻¹ * (γ ^ 2 * α) := by rw [hαγ]
        _ = γ * α := by rw [pow_two, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
    have c2 : γ⁻¹ * α ^ 2 * γ = γ ^ 3 * α ^ 2 := by
      have h2 : α ^ 2 * γ = γ ^ 4 * α ^ 2 := by
        calc α ^ 2 * γ = α * (α * γ) := by rw [pow_two, mul_assoc]
          _ = α * (γ ^ 2 * α) := by rw [hαγ]
          _ = (α * γ ^ 2) * α := by rw [mul_assoc]
          _ = ((α * γ) * γ) * α := by rw [pow_two, ← mul_assoc]
          _ = ((γ ^ 2 * α) * γ) * α := by rw [hαγ]
          _ = (γ ^ 2 * (α * γ)) * α := by rw [mul_assoc (γ ^ 2)]
          _ = (γ ^ 2 * (γ ^ 2 * α)) * α := by rw [hαγ]
          _ = γ ^ 4 * α ^ 2 := by
            rw [← mul_assoc, ← pow_add, mul_assoc, ← pow_two]
      calc γ⁻¹ * α ^ 2 * γ = γ⁻¹ * (α ^ 2 * γ) := by rw [mul_assoc]
        _ = γ⁻¹ * (γ ^ 4 * α ^ 2) := by rw [h2]
        _ = γ ^ 3 * α ^ 2 := by
          rw [show γ ^ 4 = γ * γ ^ 3 from pow_succ' γ 3, ← mul_assoc, ← mul_assoc,
            inv_mul_cancel, one_mul]
    have hγz : γ z ∈ D := pow_apply_mem hβD hz j
    have h := hT (γ z) hγz
    have h' := congrArg (fun y => γ⁻¹ y) h
    simp only [map_mul, map_one] at h'
    have e0 : γ⁻¹ (γ z) = z := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl
    have e1 : γ⁻¹ (α (γ z)) = (γ * α) z := by
      rw [← c1]; rfl
    have e2 : γ⁻¹ ((α ^ 2) (γ z)) = (γ ^ 3 * α ^ 2) z := by
      rw [← c2]; rfl
    rw [e0, e1, e2] at h'
    have e3 : β ^ (3 * j) = γ ^ 3 := by rw [hγ, ← pow_mul, mul_comm]
    rw [e3]
    exact h'
  have hγ7 : (β ^ 3) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hβ7, one_pow]
  have hγD : ∀ x ∈ D, (β ^ 3) x ∈ D := fun x hx => pow_apply_mem hβD hx 3
  have hγfpf : ∀ x ∈ D, (β ^ 3) x = x → x = 1 := by
    intro x hxD hx
    apply hfpf x hxD
    have h5 : ((β ^ 3) ^ 5) x = x := pow_apply_eq_self hx 5
    have e : (β ^ 3) ^ 5 = β := by
      rw [← pow_mul, show 3 * 5 = 7 * 2 + 1 by norm_num, pow_add, pow_mul, hβ7, one_pow, one_mul,
        pow_one]
    rwa [e] at h5
  have hz : z₀ = 1 := by
    have hz0 := hz₀
    have hprod : ∏ j ∈ Finset.range 7,
        (z₀ * ((β ^ j * α) z₀) * ((β ^ (3 * j) * α ^ 2) z₀)) = 1 :=
      Finset.prod_eq_one fun j _ => hkey z₀ hz₀ j
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range] at hprod
    have hA : ∏ j ∈ Finset.range 7, (β ^ j * α) z₀ = 1 := by
      have := prod_pow_eq_one hβD hβ7 hfpf (hαD z₀ hz₀)
      simpa [MulAut.mul_apply] using this
    have hB : ∏ j ∈ Finset.range 7, (β ^ (3 * j) * α ^ 2) z₀ = 1 := by
      have hα2 : (α ^ 2) z₀ ∈ D := by rw [pow_two, MulAut.mul_apply]; exact hαD _ (hαD z₀ hz₀)
      have := prod_pow_eq_one hγD hγ7 hγfpf hα2
      simpa [MulAut.mul_apply, pow_mul] using this
    rw [hA, hB, mul_one, mul_one] at hprod
    have : z₀ ^ 7 = z₀ := by
      calc z₀ ^ 7 = z₀ ^ 6 * z₀ := pow_succ z₀ 6
        _ = (z₀ * z₀) ^ 3 * z₀ := by rw [← pow_two, ← pow_mul]
        _ = z₀ := by rw [hsq z₀, one_pow, one_mul]
    rwa [this] at hprod
  exact hz₀1 hz

theorem frob_fixed (hsq : ∀ x : I, x * x = 1) {α β : MulAut I}
    (hα3 : α ^ 3 = 1) (hβ7 : β ^ 7 = 1) (hαβ : α * β = β ^ 2 * α) :
    (∃ x : I, x ≠ 1 ∧ α x = x) ∨ ∀ x : I, β x = x := by
  let D : Subgroup I :=
    { carrier := {d | ∃ x : I, d = β x * x⁻¹}
      mul_mem' := fun {d e} ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by
        rw [hx, hy, map_mul, mul_inv_rev]
        ac_rfl⟩
      one_mem' := ⟨1, by simp⟩
      inv_mem' := fun {d} ⟨x, hx⟩ => ⟨x⁻¹, by rw [hx, map_inv, mul_inv_rev, inv_inv]; ac_rfl⟩ }
  have hmemD : ∀ x : I, β x * x⁻¹ ∈ D := fun x => ⟨x, rfl⟩
  have hβx : ∀ x : I, (β ^ 2) x = β (β x) := fun x => by rw [pow_two, MulAut.mul_apply]
  have hαβx : ∀ x : I, α (β x) = β (β (α x)) := fun x => by
    have := congrArg (fun φ : MulAut I => φ x) hαβ
    simp only [MulAut.mul_apply, hβx] at this
    exact this
  have hαD : ∀ d ∈ D, α d ∈ D := by
    rintro d ⟨x, rfl⟩
    have : α (β x * x⁻¹) = (β (β (α x)) * (β (α x))⁻¹) * (β (α x) * (α x)⁻¹) := by
      rw [map_mul, map_inv, hαβx]; group
    rw [this]
    exact D.mul_mem (hmemD _) (hmemD _)
  have hβD : ∀ d ∈ D, β d ∈ D := by
    rintro d ⟨x, rfl⟩
    exact ⟨β x, by rw [map_mul, map_inv]⟩
  have hfpf : ∀ d ∈ D, β d = d → d = 1 := by
    rintro d ⟨x, rfl⟩ hd
    set G : ℕ → I := fun j => (β ^ j) x with hG
    have hG7 : G 7 = G 0 := by simp [hG, hβ7]
    have h1 : ∏ j ∈ Finset.range 7, (β ^ j) (β x * x⁻¹) = 1 := by
      have : ∀ j : ℕ, (β ^ j) (β x * x⁻¹) = G (j + 1) * (G j)⁻¹ := by
        intro j
        simp only [hG, map_mul, map_inv, pow_succ, MulAut.mul_apply]
      simp only [this]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, prod_shift hG7, mul_inv_cancel]
    have h2 : ∏ j ∈ Finset.range 7, (β ^ j) (β x * x⁻¹) = (β x * x⁻¹) ^ 7 := by
      rw [← Finset.card_range 7, ← Finset.prod_const]
      exact Finset.prod_congr rfl fun j _ => pow_apply_eq_self hd j
    have h3 : (β x * x⁻¹) ^ 7 = β x * x⁻¹ := by
      have hdd : (β x * x⁻¹) * (β x * x⁻¹) = 1 := by
        calc (β x * x⁻¹) * (β x * x⁻¹) = (β x * β x) * (x⁻¹ * x⁻¹) := by ac_rfl
          _ = 1 := by rw [hsq (β x), ← mul_inv_rev, hsq x, inv_one, one_mul]
      generalize β x * x⁻¹ = d at hdd ⊢
      calc d ^ 7 = d ^ 6 * d := pow_succ d 6
        _ = (d * d) ^ 3 * d := by rw [← pow_two, ← pow_mul]
        _ = d := by rw [hdd, one_pow, one_mul]
    rw [← h3, ← h2, h1]
  rcases frob_core D hsq hαD hβD hα3 hβ7 hαβ hfpf with ⟨x, -, hx1, hx⟩ | hall
  · exact Or.inl ⟨x, hx1, hx⟩
  · exact Or.inr fun x => mul_inv_eq_one.1 (hall _ (hmemD x))

end Frob

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

module

public import CFSG.CGT.Timmesfeld75.Sec77R1

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.mul_mem_of_same_center (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]
    (M : TModel T T₁ n m) {x z : G} (hx : x ∈ normD T) (hxT : x ∉ T) (hz : z ∈ normD T)
    (hzT : z ∉ T) (hxz : x * z = z * x)
    {fx fz : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {v : Fin n → GaloisField 2 m} (hv : v ≠ 0) (hfx : fx v = 0) (hfz : fz v = 0) (hfx0 : fx ≠ 0)
    (hfz0 : fz ≠ 0) (hdx : ∀ w, sact (ubar M.ε x) w = w + fx w • v)
    (hdz : ∀ w, sact (ubar M.ε z) w = w + fz w • v) : x * z ∈ T ∨ x * z ∈ classD T := by
  have := hc.finite
  have hTab := hc.hy.pair.wc.1
  have hxH := M.mem_H hx
  have hzH := M.mem_H hz
  by_cases hfxz : fx = fz
  · left
    have h1' : ubar M.ε x * ubar M.ε z = 1 := (data_mul_eq_one_iff hfx hv hdx hdz).2 hfxz
    rw [← ubar_mul M.ε hxH hzH] at h1'
    exact (ubar_eq_one_iff M.ε ((hSub T (normIn T₁ T)).mul_mem hxH hzH)).1 h1'
  by_cases hind : ∀ r s : GaloisField 2 m, r • fx + s • fz = 0 → r = 0 ∧ s = 0
  · right
    exact hc.mul_mem_classD_of_data h66 h62 h63 M hx hz hzT hxz hv hfx hfz hind hdx hdz
  push Not at hind
  obtain ⟨r, s, hrs, hne⟩ := hind
  have hs0 : s ≠ 0 := by
    intro hs
    subst hs
    rw [zero_smul, add_zero] at hrs
    exact hne ((smul_eq_zero.1 hrs).resolve_right hfx0) rfl
  have hr0 : r ≠ 0 := by
    intro hr
    subst hr
    rw [zero_smul, zero_add] at hrs
    exact hs0 ((smul_eq_zero.1 hrs).resolve_right hfz0)
  set κ : GaloisField 2 m := -(s⁻¹ * r) with hκdef
  have hκ : fz = κ • fx := by
    have h6 : s • fz = -(r • fx) := eq_neg_of_add_eq_zero_right hrs
    calc fz = s⁻¹ • (s • fz) := by rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = s⁻¹ • (-(r • fx)) := by rw [h6]
      _ = κ • fx := by rw [hκdef, smul_neg, smul_smul]; exact (neg_smul _ _).symm
  have hκ0 : κ ≠ 0 := by
    rw [hκdef]
    exact neg_ne_zero.2 (mul_ne_zero (inv_ne_zero hs0) hr0)
  have hκ1 : κ ≠ 1 := by
    intro h
    apply hfxz
    rw [hκ, h, one_smul]
  obtain ⟨f₂, hf₂v, hind₂⟩ := exists_dual_indep hfx0 hv hn3
  have hf₂0 : f₂ ≠ 0 := fun h0 => one_ne_zero (hind₂ 0 1 (by rw [h0]; simp)).2
  obtain ⟨u₂, hu₂tr, hu₂act⟩ := exists_sl_transvection hf₂v hf₂0 hv
  obtain ⟨x₂, hx₂, hx₂T, hx₂ub⟩ := hc.exists_lift M hu₂tr
  have hdx₂ : ∀ w, sact (ubar M.ε x₂) w = w + f₂ w • v := by
    intro w
    rw [hx₂ub]
    exact hu₂act w
  have hx₂x : x * x₂ = x₂ * x := by
    symm
    refine hc.comm_of_ubar_comm h66 h1 h62 h63 hnat hn3 hA8 M hx₂ hx₂T hx hxT ?_
    rw [hx₂ub]
    exact mul_comm_of_data hf₂v hfx hu₂act hdx
  have hzx₂ : z * x₂ = x₂ * z := by
    symm
    refine hc.comm_of_ubar_comm h66 h1 h62 h63 hnat hn3 hA8 M hx₂ hx₂T hz hzT ?_
    rw [hx₂ub]
    exact mul_comm_of_data hf₂v hfz hu₂act hdz
  have hind_z₂ : ∀ r s : GaloisField 2 m, r • fz + s • f₂ = 0 → r = 0 ∧ s = 0 := by
    intro r' s' h0
    rw [hκ, smul_smul] at h0
    obtain ⟨h1', h2'⟩ := hind₂ _ _ h0
    exact ⟨(mul_eq_zero.1 h1').resolve_right hκ0, h2'⟩
  have hxx₂D : x * x₂ ∈ classD T :=
    hc.mul_mem_classD_of_data h66 h62 h63 M hx hx₂ hx₂T hx₂x hv hfx hf₂v hind₂ hdx hdx₂
  have hzx₂D : z * x₂ ∈ classD T :=
    hc.mul_mem_classD_of_data h66 h62 h63 M hz hx₂ hx₂T hzx₂ hv hfz hf₂v hind_z₂ hdz hdx₂
  have hx₂H := M.mem_H hx₂
  have hw₁ : x * x₂ ∈ normD T := ⟨hxx₂D, (Subgroup.normalizer (T : Set G)).mul_mem hx.2 hx₂.2⟩
  have hw₂ : z * x₂ ∈ normD T := ⟨hzx₂D, (Subgroup.normalizer (T : Set G)).mul_mem hz.2 hx₂.2⟩
  have hw₂H : z * x₂ ∈ hSub T (normIn T₁ T) := (hSub T (normIn T₁ T)).mul_mem hzH hx₂H
  have hubw₁ : ubar M.ε (x * x₂) = ubar M.ε x * ubar M.ε x₂ := ubar_mul M.ε hxH hx₂H
  have hubw₂ : ubar M.ε (z * x₂) = ubar M.ε z * ubar M.ε x₂ := ubar_mul M.ε hzH hx₂H
  have hdw₁ : ∀ w, sact (ubar M.ε (x * x₂)) w = w + (fx + f₂) w • v := by
    intro w
    rw [hubw₁]
    exact sact_mul_of_data hfx hdx hdx₂ w
  have hdw₂ : ∀ w, sact (ubar M.ε (z * x₂)) w = w + (fz + f₂) w • v := by
    intro w
    rw [hubw₂]
    exact sact_mul_of_data hfz hdz hdx₂ w
  have hw₂T : z * x₂ ∉ T := by
    intro h
    have h2 := (ubar_eq_one_iff M.ε hw₂H).2 h
    rw [hubw₂] at h2
    have hff : fz = f₂ := (data_mul_eq_one_iff hfz hv hdz hdx₂).1 h2
    have h3 : (1 : GaloisField 2 m) • fz + (1 : GaloisField 2 m) • f₂ = 0 := by
      rw [← hff]
      ext w
      simp [CharTwo.add_self_eq_zero]
    exact one_ne_zero (hind_z₂ 1 1 h3).1
  have hx₂2 : x₂ * x₂ = 1 := mul_self_eq_one_of_mem_classD hTab hx₂.1
  have e1 : (x * x₂) * (z * x₂) = x * z := by
    calc (x * x₂) * (z * x₂) = x * (x₂ * z) * x₂ := by group
      _ = x * (z * x₂) * x₂ := by rw [← hzx₂]
      _ = x * z * (x₂ * x₂) := by group
      _ = x * z := by rw [hx₂2, mul_one]
  have e2 : (z * x₂) * (x * x₂) = z * x := by
    calc (z * x₂) * (x * x₂) = z * (x₂ * x) * x₂ := by group
      _ = z * (x * x₂) * x₂ := by rw [← hx₂x]
      _ = z * x * (x₂ * x₂) := by group
      _ = z * x := by rw [hx₂2, mul_one]
  have hcomm12 : (x * x₂) * (z * x₂) = (z * x₂) * (x * x₂) := by rw [e1, e2, hxz]
  have hind_w : ∀ r s : GaloisField 2 m, r • (fx + f₂) + s • (fz + f₂) = 0 → r = 0 ∧ s = 0 := by
    intro r' s' h0
    have h1' : (r' + s' * κ) • fx + (r' + s') • f₂ = 0 := by
      rw [← h0, hκ]
      module
    obtain ⟨hA, hB⟩ := hind₂ _ _ h1'
    have hs' : s' * (κ - 1) = 0 := by linear_combination hA - hB
    have hs'0 : s' = 0 := (mul_eq_zero.1 hs').resolve_right (sub_ne_zero.2 hκ1)
    refine ⟨?_, hs'0⟩
    rw [hs'0, add_zero] at hB
    exact hB
  have hfin := hc.mul_mem_classD_of_data h66 h62 h63 M hw₁ hw₂ hw₂T hcomm12 hv
    (f := fx + f₂) (f' := fz + f₂) (by simp [hfx, hf₂v]) (by simp [hfz, hf₂v]) hind_w hdw₁ hdw₂
  right
  rwa [e1] at hfin

end CFSG.CGT.Timmesfeld75

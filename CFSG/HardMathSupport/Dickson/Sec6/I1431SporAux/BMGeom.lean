module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section Fixed

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjSMulOn (K : Subgroup G) (F : Set G)
    (hF : ∀ g ∈ K, ∀ s ∈ F, g * s * g⁻¹ ∈ F) : MulAction K F :=
  { smul := fun g s => ⟨(g : G) * (s : G) * (g : G)⁻¹, hF g g.2 s s.2⟩
    one_smul := fun s => Subtype.ext (by
      show ((1 : K) : G) * (s : G) * ((1 : K) : G)⁻¹ = s
      simp)
    mul_smul := fun g h s => Subtype.ext (by
      show ((g * h : K) : G) * (s : G) * ((g * h : K) : G)⁻¹ =
        (g : G) * ((h : G) * (s : G) * (h : G)⁻¹) * (g : G)⁻¹
      simp [mul_assoc]) }

theorem ncard_modEq_fixed [Finite G] {p : ℕ} (hp : p.Prime) {a : G} (ha : orderOf a = p)
    {F : Set G} (hF : ∀ g ∈ zpowers a, ∀ s ∈ F, g * s * g⁻¹ ∈ F) :
    F.ncard ≡ {s | s ∈ F ∧ a * s = s * a}.ncard [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction (zpowers a) F := conjSMulOn (zpowers a) F hF
  have hP : IsPGroup p (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have h := hP.card_modEq_card_fixedPoints (α := F)
  have e : MulAction.fixedPoints (zpowers a) F ≃ {s | s ∈ F ∧ a * s = s * a} :=
    { toFun := fun s => ⟨s.1.1, s.1.2, by
        have h1 := congrArg Subtype.val (s.2 ⟨a, mem_zpowers a⟩)
        have h2 : a * (s.1.1 : G) * a⁻¹ = s.1.1 := h1
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2⟩
      invFun := fun s => ⟨⟨s.1, s.2.1⟩, by
        intro g
        obtain ⟨g, hg⟩ := g
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
        refine Subtype.ext ?_
        have hc : Commute (a ^ k) s.1 := Commute.zpow_left (show Commute a s.1 from s.2.2) k
        show a ^ k * s.1 * (a ^ k)⁻¹ = s.1
        rw [mul_inv_eq_iff_eq_mul]
        exact hc.eq⟩
      left_inv := fun s => rfl
      right_inv := fun s => rfl }
  have h' : Nat.card F ≡ Nat.card {s | s ∈ F ∧ a * s = s * a} [MOD p] := by
    rwa [← Nat.card_congr e]
  rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h'

theorem invol_conj_prod {f f' : G} (hf : f * f = 1) (hf' : f' * f' = 1) :
    f * (f * f') * f = (f * f')⁻¹ := by
  have hf1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hf1' : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right hf'
  rw [mul_inv_rev, hf1, hf1']
  calc f * (f * f') * f = (f * f) * f' * f := by simp only [mul_assoc]
    _ = f' * f := by rw [hf, one_mul]

theorem false_of_commute_three {f f' h : G} (hf : f * f = 1) (hf' : f' * f' = 1)
    (hh : h * h = 1) (hj : orderOf (f * f') = 3) (hc : orderOf (h * f) = 3)
    (hcomm : h * (f * f') = (f * f') * h) : False := by
  have hf1 : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hf1' : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right hf'
  have hh1 : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  set j := f * f' with hjdef
  set c := h * f with hcdef
  have hfj : f * j * f = j⁻¹ := invol_conj_prod hf hf'
  have hhj : h * j⁻¹ * h = j⁻¹ := by
    have hc' : Commute h j⁻¹ := Commute.inv_right (show Commute h j from hcomm)
    calc h * j⁻¹ * h = j⁻¹ * h * h := by rw [hc'.eq]
      _ = j⁻¹ := by rw [mul_assoc, hh, mul_one]
  have hcinv : c⁻¹ = f * h := by rw [hcdef, mul_inv_rev, hf1, hh1]
  have h1 : c * j * c⁻¹ = j⁻¹ := by
    rw [hcinv, hcdef]
    calc h * f * j * (f * h) = h * (f * j * f) * h := by simp only [mul_assoc]
      _ = h * j⁻¹ * h := by rw [hfj]
      _ = j⁻¹ := hhj
  have h2 : c * j⁻¹ * c⁻¹ = j := by
    have := congrArg (fun y => y⁻¹) h1
    simpa [mul_inv_rev, mul_assoc] using this
  have hc3 : c * c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc] at h
    calc c * c * c = c ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := h
  clear_value c j
  have h3 : (c * c * c) * j * (c * c * c)⁻¹ = j⁻¹ := by
    calc (c * c * c) * j * (c * c * c)⁻¹ = c * (c * (c * j * c⁻¹) * c⁻¹) * c⁻¹ := by group
      _ = c * (c * j⁻¹ * c⁻¹) * c⁻¹ := by rw [h1]
      _ = c * j * c⁻¹ := by rw [h2]
      _ = j⁻¹ := h1
  rw [hc3, inv_one, one_mul, mul_one] at h3
  have hjj : j * j = 1 := by
    rw [mul_eq_one_iff_eq_inv]
    exact h3
  have : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hjj)
  rw [hj] at this
  omega

end Fixed

section InvComm

variable {G : Type*} [Group G]

@[expose] def invComm (x : G) : Set G := {f | f * f = 1 ∧ f ≠ 1 ∧ f * x = x * f}

theorem conj_mem_invComm {x c f : G} (hc : c * x = x * c) (hf : f ∈ invComm x) :
    c * f * c⁻¹ ∈ invComm x := by
  obtain ⟨hf2, hf1, hfx⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · calc c * f * c⁻¹ * (c * f * c⁻¹) = c * (f * f) * c⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  · intro h
    apply hf1
    have : f = c⁻¹ * (c * f * c⁻¹) * c := by group
    rw [this, h]
    group
  · have hc' : Commute c x := hc
    have hf' : Commute f x := hfx
    exact ((hc'.mul_left hf').mul_left hc'.inv_left).eq

theorem conj_closed_invComm {x a : G} (hax : a * x = x * a) :
    ∀ g ∈ zpowers a, ∀ s ∈ invComm x, g * s * g⁻¹ ∈ invComm x := by
  intro g hg s hs
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  exact conj_mem_invComm (Commute.zpow_left (show Commute a x from hax) k).eq hs

theorem three_dvd_ncard_invComm [Finite G] {x f f' : G} (hf : f ∈ invComm x)
    (hf' : f' ∈ invComm x) (hne : f ≠ f')
    (h3 : ∀ u ∈ invComm x, ∀ v ∈ invComm x, u ≠ v → orderOf (u * v) = 3) :
    3 ∣ (invComm x).ncard := by
  have hj : orderOf (f * f') = 3 := h3 f hf f' hf' hne
  have hjx : Commute (f * f') x := Commute.mul_left hf.2.2 hf'.2.2
  have hmod := ncard_modEq_fixed (p := 3) Nat.prime_three hj
    (conj_closed_invComm (x := x) (a := f * f') hjx.eq)
  have hempty : {s | s ∈ invComm x ∧ (f * f') * s = s * (f * f')} = ∅ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hs, hcomm⟩
    by_cases hsf : s = f
    · rw [hsf] at hcomm
      have h1 : f * (f * f') * f = (f * f') := by
        calc f * (f * f') * f = f * f' * f * f := by rw [← hcomm]
          _ = f * f' := by simp only [mul_assoc, hf.1, mul_one]
      rw [invol_conj_prod hf.1 hf'.1] at h1
      have hjj : (f * f') * (f * f') = 1 := by
        rw [mul_eq_one_iff_eq_inv]
        exact h1.symm
      have : orderOf (f * f') ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hjj)
      rw [hj] at this
      omega
    · exact false_of_commute_three hf.1 hf'.1 hs.1 hj (h3 s hs f hf hsf) hcomm.symm
  rw [hempty, Set.ncard_empty] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

theorem exists_fixed_ne [Finite G] {x t w f₀ : G} (ht : t ∈ invComm x) (hf₀ : f₀ ∈ invComm x)
    (hne : f₀ ≠ t)
    (h3 : ∀ u ∈ invComm x, ∀ v ∈ invComm x, u ≠ v → orderOf (u * v) = 3)
    (hw : orderOf w = 3) (hwx : w * x = x * w) (hwt : w * t = t * w) :
    ∃ f ∈ invComm x, f ≠ t ∧ w * f = f * w := by
  have h3F : 3 ∣ (invComm x).ncard := three_dvd_ncard_invComm hf₀ ht hne h3
  have hmod := ncard_modEq_fixed (p := 3) Nat.prime_three hw
    (conj_closed_invComm (x := x) (a := w) hwx)
  have hdvd : 3 ∣ {s | s ∈ invComm x ∧ w * s = s * w}.ncard :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 h3F))
  by_contra hcon
  push Not at hcon
  have hsub : {s | s ∈ invComm x ∧ w * s = s * w} ⊆ {t} := by
    intro s hs
    by_contra hst
    exact hcon s hs.1 (by simpa using hst) hs.2
  have hle : {s | s ∈ invComm x ∧ w * s = s * w}.ncard ≤ 1 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    simpa using this
  have hpos : 0 < {s | s ∈ invComm x ∧ w * s = s * w}.ncard :=
    Set.ncard_pos (Set.toFinite _) |>.2 ⟨t, ht, hwt⟩
  have := Nat.le_of_dvd hpos hdvd
  omega

end InvComm

end CFSG.HardMathSupport.Dickson.Sec6.I1431

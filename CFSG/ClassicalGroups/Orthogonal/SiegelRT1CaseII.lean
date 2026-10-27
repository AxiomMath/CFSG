module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Defs
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair
public import CFSG.ClassicalGroups.Alternating.RT1SpGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Qf : QuadraticForm K V}

theorem movedSpace_one_eq_bot : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  have h : ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) - 1 = 0 := by
    ext
    simp
  rw [movedSpace, h, LinearMap.range_zero]

theorem movedSpace_mul_mul_inv (g s : V ≃ₗ[K] V) :
    movedSpace (g * s * g⁻¹) = (movedSpace s).map (g : V →ₗ[K] V) := by
  ext w
  rw [mem_movedSpace_iff, Submodule.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s (g⁻¹ x) - g⁻¹ x, mem_movedSpace_iff.mpr ⟨_, rfl⟩, by simp [LinearEquiv.mul_apply]⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨y, rfl⟩ := mem_movedSpace_iff.mp hv
    exact ⟨g y, by simp [LinearEquiv.mul_apply]⟩

theorem polar_eq_zero_of_mem_iSup_of_pairwise {ι κ : Type*} {A : ι → Submodule K V}
    {B : κ → Submodule K V} (h : ∀ i j, ∀ x ∈ A i, ∀ y ∈ B j, polar Qf x y = 0) {x y : V}
    (hx : x ∈ ⨆ i, A i) (hy : y ∈ ⨆ j, B j) : polar Qf x y = 0 := by
  refine Submodule.iSup_induction A (motive := fun x => polar Qf x y = 0) hx (fun i x hxi => ?_)
    (by simp) (fun x x' hx hx' => by rw [polar_add_left, hx, hx', add_zero])
  refine Submodule.iSup_induction B (motive := fun y => polar Qf x y = 0) hy
    (fun j y hyj => h i j x hxi y hyj) (by simp)
    (fun y y' hy hy' => by rw [polar_add_right, hy, hy', add_zero])

theorem qf_eq_zero_of_mem_iSup_of_pairwise {ι : Type*} {A : ι → Submodule K V}
    (hA : ∀ i, ∀ w ∈ A i, Qf w = 0) (h : ∀ i j, ∀ x ∈ A i, ∀ y ∈ A j, polar Qf x y = 0) {w : V}
    (hw : w ∈ ⨆ i, A i) : Qf w = 0 := by
  refine Submodule.iSup_induction' A (motive := fun w _ => Qf w = 0) (fun i x hx => hA i x hx)
    (QuadraticMap.map_zero Qf) (fun x y hx hy hx0 hy0 => ?_) hw
  rw [QuadraticMap.map_add Qf, hx0, hy0, polar_eq_zero_of_mem_iSup_of_pairwise h hx hy, add_zero,
    add_zero]

theorem mem_orthogonal_bot {y : V} :
    y ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (⊥ : Submodule K V) := by
  rw [mem_orthogonal_iff_polar]
  intro x hx
  rw [(Submodule.mem_bot K).mp hx]
  simp

end Generic

section Calculus

variable {K : Type} [Field K] {N : Type*} [AddCommGroup N] [Module K N]
  {BN : LinearMap.BilinForm K N} {V : Type*} [AddCommGroup V] [Module K V]
  {hBN : BN.IsAlt} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

@[expose] def rhoFixSubgroup (ρ : Gsp BN →* (V ≃ₗ[K] V)) (S : Submodule K V) :
    Subgroup (Gsp BN) where
  carrier := {g | ∀ w ∈ S, ρ g w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := fun {g h} hg hh w hw => by
    rw [map_mul, LinearEquiv.mul_apply, hh w hw, hg w hw]
  inv_mem' := fun {g} hg w hw => by
    calc ρ g⁻¹ w = ρ g⁻¹ (ρ g w) := by rw [hg w hw]
      _ = w := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_rhoFixSubgroup {S : Submodule K V} {g : Gsp BN} :
    g ∈ rhoFixSubgroup ρ S ↔ ∀ w ∈ S, ρ g w = w := Iff.rfl

theorem rho_conj_Tsp (g : Gsp BN) (x : N) (c : K) :
    ρ g * ρ (Tsp hBN x c) * (ρ g)⁻¹ = ρ (Tsp hBN (g.app x) c) := by
  rw [← map_inv, ← map_mul, ← map_mul, Tsp_conj]

theorem map_axis_eq (g : Gsp BN) (a : N) (c : K) :
    (axis hBN ρ a c).map (ρ g : V →ₗ[K] V) = axis hBN ρ (g.app a) c := by
  rw [axis, axis, ← rho_conj_Tsp g a c, movedSpace_mul_mul_inv]

theorem map_rootSpace_eq (g : Gsp BN) (a : N) :
    (rootSpace hBN ρ a).map (ρ g : V →ₗ[K] V) = rootSpace hBN ρ (g.app a) := by
  rw [rootSpace, rootSpace, Submodule.map_iSup]
  exact iSup_congr fun c => map_axis_eq g a c

theorem axis_le_rootSpace (a : N) (c : K) : axis hBN ρ a c ≤ rootSpace hBN ρ a :=
  le_iSup (axis hBN ρ a) c

theorem axis_smul_eq (r : K) (a : N) (c : K) :
    axis hBN ρ (r • a) c = axis hBN ρ a (r ^ 2 * c) := by
  rw [axis, axis, Tsp_smul]

theorem rootSpace_smul_of_ne_zero {r : K} (hr : r ≠ 0) (a : N) :
    rootSpace hBN ρ (r • a) = rootSpace hBN ρ a := by
  unfold rootSpace
  simp only [axis_smul_eq]
  exact Function.Surjective.iSup_comp (f := fun c : K => r ^ 2 * c)
    (fun y => ⟨(r ^ 2)⁻¹ * y, by field_simp⟩) (axis hBN ρ a)

theorem axis_zero_scalar (hBNnd : BN.Nondegenerate) (a : N) : axis hBN ρ a 0 = ⊥ := by
  rw [axis, (Tsp_eq_one_iff hBN hBNnd a 0).mpr (Or.inr rfl), map_one, movedSpace_one_eq_bot]

theorem axis_zero_point (hBNnd : BN.Nondegenerate) (c : K) : axis hBN ρ 0 c = ⊥ := by
  rw [axis, (Tsp_eq_one_iff hBN hBNnd 0 c).mpr (Or.inl rfl), map_one, movedSpace_one_eq_bot]

theorem Tsp_app_self (b : N) (c : K) : (Tsp hBN b c).app b = b := by
  rw [Tsp_app, hBN.self_eq_zero, mul_zero, zero_smul, add_zero]

end Calculus

section CaseIIScalars

variable {K : Type} [Field K] [Finite K] [CharP K 2] {N : Type*} [AddCommGroup N] [Module K N]
  {BN : LinearMap.BilinForm K N} {V : Type*} [AddCommGroup V] [Module K V]
  {hBN : BN.IsAlt} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hII : ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
    axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥)

include hII

theorem caseII_axis_inf_eq_bot {a c : N} (hli : LinearIndependent K ![a, c]) (hac : BN a c = 0)
    {l m : K} (hl : l ≠ 0) (hm : m ≠ 0) : axis hBN ρ a l ⊓ axis hBN ρ c m = ⊥ := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' l
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' m
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hl (by rw [hr, mul_zero])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hm (by rw [ht, mul_zero])
  have hli' : LinearIndependent K ![r • a, t • c] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro p q hpq
    have h := hli (p * r) (q * t) (by rw [← hpq, mul_smul, mul_smul])
    exact ⟨(mul_eq_zero.mp h.1).resolve_right hr0, (mul_eq_zero.mp h.2).resolve_right ht0⟩
  have h0 : BN (r • a) (t • c) = 0 := by
    simp [hac]
  have h := hII (r • a) (t • c) hli' h0
  have e1 : r ^ 2 * 1 = l := by rw [hr]; ring
  have e2 : t ^ 2 * 1 = m := by rw [ht]; ring
  rwa [axis_smul_eq, axis_smul_eq, e1, e2] at h

end CaseIIScalars

section CaseII

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

variable (hs : Setting hBN Qf ρ)

include hs

theorem axis_totallySingular (a : N) (l : K) : ∀ w ∈ axis hBN ρ a l, Qf w = 0 := by
  intro w hw
  by_cases ha : a = 0
  · rw [ha, axis_zero_point hs.nondegN] at hw
    rw [(Submodule.mem_bot K).mp hw]
    exact QuadraticMap.map_zero Qf
  by_cases hl : l = 0
  · rw [hl, axis_zero_scalar hs.nondegN] at hw
    rw [(Submodule.mem_bot K).mp hw]
    exact QuadraticMap.map_zero Qf
  exact (hs.siegel a ha l hl).qf_eq_zero_of_mem_movedSpace hw

theorem axis_le_orthogonal_axis_self (a : N) (l m : K) :
    axis hBN ρ a l ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (axis hBN ρ a m) := by
  by_cases ha : a = 0
  · rw [ha, axis_zero_point hs.nondegN]
    exact bot_le
  by_cases hl : l = 0
  · rw [hl, axis_zero_scalar hs.nondegN]
    exact bot_le
  by_cases hm : m = 0
  · rw [hm, axis_zero_scalar hs.nondegN]
    intro y _
    exact mem_orthogonal_bot
  have hSl := hs.siegel a ha l hl
  have hSm := hs.siegel a ha m hm
  have hcomm : ρ (Tsp hBN a l) * ρ (Tsp hBN a m) = ρ (Tsp hBN a m) * ρ (Tsp hBN a l) := by
    rw [← map_mul, ← map_mul, Tsp_mul_Tsp, Tsp_mul_Tsp, add_comm]
  by_cases hlm : l = m
  · subst hlm
    exact le_orthogonal_of_totallySingular (axis_totallySingular hs a l)
  · have hsum : l + m ≠ 0 := fun h => hlm (CharTwo.add_eq_zero.mp h)
    have hmul : IsLongRootElement Qf (ρ (Tsp hBN a l) * ρ (Tsp hBN a m)) := by
      rw [← map_mul, Tsp_mul_Tsp]
      exact hs.siegel a ha (l + m) hsum
    exact movedSpace_le_orthogonal_of_commute_of_isLongRootElement_mul hs.nondeg hSl hSm hcomm
      hmul

variable (hII : ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
  axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥)

include hII

theorem axis_le_orthogonal_axis {a x : N} (hax : BN a x = 0) (l c : K) :
    axis hBN ρ a l ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (axis hBN ρ x c) := by
  by_cases ha : a = 0
  · rw [ha, axis_zero_point hs.nondegN]
    exact bot_le
  by_cases hx : x = 0
  · rw [hx, axis_zero_point hs.nondegN]
    intro y _
    exact mem_orthogonal_bot
  by_cases hl : l = 0
  · rw [hl, axis_zero_scalar hs.nondegN]
    exact bot_le
  by_cases hc : c = 0
  · rw [hc, axis_zero_scalar hs.nondegN]
    intro y _
    exact mem_orthogonal_bot
  by_cases hli : LinearIndependent K ![a, x]
  · have hcomm : ρ (Tsp hBN a l) * ρ (Tsp hBN x c) = ρ (Tsp hBN x c) * ρ (Tsp hBN a l) := by
      rw [← map_mul, ← map_mul, Tsp_comm hBN hax l c]
    rcases movedSpace_le_orthogonal_or_inf_ne_bot_of_commute (hs.siegel a ha l hl)
        (hs.siegel x hx c hc) hcomm with h | h
    · exact h
    · exact absurd (caseII_axis_inf_eq_bot hII hli hax hl hc) h
  · rw [LinearIndependent.pair_iff' ha] at hli
    push Not at hli
    obtain ⟨r, rfl⟩ := hli
    rw [axis_smul_eq]
    exact axis_le_orthogonal_axis_self hs a l (r ^ 2 * c)

theorem rootSpace_le_orthogonal_axis {a x : N} (hax : BN a x = 0) (c : K) :
    rootSpace hBN ρ a ≤ LinearMap.BilinForm.orthogonal (polarBilin Qf) (axis hBN ρ x c) :=
  iSup_le fun l => axis_le_orthogonal_axis hs hII hax l c

theorem apply_Tsp_eq_of_mem_rootSpace {a x : N} (hax : BN a x = 0) (c : K) {w : V}
    (hw : w ∈ rootSpace hBN ρ a) : ρ (Tsp hBN x c) w = w := by
  have h := rootSpace_le_orthogonal_axis hs hII hax c hw
  rw [axis, ← ker_sub_one_eq_orthogonal_movedSpace hs.nondeg (hs.iso (Tsp hBN x c))] at h
  simpa [sub_eq_zero] using h

theorem apply_eq_of_app_eq_of_mem_rootSpace {a : N} {g : Gsp BN} (hg : g.app a = a) {w : V}
    (hw : w ∈ rootSpace hBN ρ a) : ρ g w = w := by
  have hcl := mem_closure_Tsp_of_app_eq hBN hs.nondegN hg
  have hle : Subgroup.closure {t : Gsp BN | ∃ (x : N) (c : K), BN a x = 0 ∧ t = Tsp hBN x c} ≤
      rhoFixSubgroup ρ (rootSpace hBN ρ a) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, c, hax, rfl⟩ w hw
    exact apply_Tsp_eq_of_mem_rootSpace hs hII hax c hw
  exact hle hcl w hw

theorem rootSpace_totallySingular_and_fixed {a : N} (_ha : a ≠ 0) :
    (∀ w ∈ rootSpace hBN ρ a, Qf w = 0) ∧
      ∀ g : Gsp BN, g.app a = a → ∀ w ∈ rootSpace hBN ρ a, ρ g w = w := by
  refine ⟨fun w hw => qf_eq_zero_of_mem_iSup_of_pairwise (axis_totallySingular hs a)
    (fun l m x hx y hy => ?_) hw, fun g hg w hw =>
    apply_eq_of_app_eq_of_mem_rootSpace hs hII hg hw⟩
  have h := axis_le_orthogonal_axis_self hs a l m hx
  rw [mem_orthogonal_iff_polar] at h
  rw [polar_comm]
  exact h y hy

theorem rootSpace_inf_eq_bot {a b : N} (hab : BN a b ≠ 0) :
    rootSpace hBN ρ a ⊓ rootSpace hBN ρ b = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  refine hs.fix v fun g => ?_
  have hH : rhoFixSubgroup ρ (rootSpace hBN ρ a ⊓ rootSpace hBN ρ b) = ⊤ := by
    refine eq_top_of_stabilizer_le_of_Tsp_mem hBN hs.nondegN hab ?_ ?_
    · intro g hg w hw
      exact apply_eq_of_app_eq_of_mem_rootSpace hs hII hg (Submodule.mem_inf.mp hw).1
    · intro c w hw
      exact apply_eq_of_app_eq_of_mem_rootSpace hs hII (Tsp_app_self b c)
        (Submodule.mem_inf.mp hw).2
  have hg : g ∈ rhoFixSubgroup ρ (rootSpace hBN ρ a ⊓ rootSpace hBN ρ b) := by
    rw [hH]
    exact Subgroup.mem_top g
  exact hg v hv

theorem rootSpace_sub_one_eq {a b : N} (hab : BN a b ≠ 0) {α l : K} (hl : l ≠ 0)
    (h : α * l * BN a b ^ 2 = 1) {u : V} (hu : u ∈ rootSpace hBN ρ a) :
    ρ (Tsp hBN b l) u - u = ρ (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) u ∧
      u ∈ axis hBN ρ a α := by
  set ta : V ≃ₗ[K] V := ρ (Tsp hBN a α) with hta
  set tb : V ≃ₗ[K] V := ρ (Tsp hBN b l) with htb
  have hta_u : ta u = u := apply_eq_of_app_eq_of_mem_rootSpace hs hII (Tsp_app_self a α) hu
  set θ : V := tb u - u with hθ
  have hθb : θ ∈ rootSpace hBN ρ b := axis_le_rootSpace b l (sub_mem_movedSpace tb u)
  have hφ : ta θ - θ ∈ axis hBN ρ a α := sub_mem_movedSpace ta θ
  have hwu : ρ (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) u = u + θ + (ta θ - θ) := by
    have h1 : tb u = u + θ := by rw [hθ]; abel
    rw [map_mul, map_mul]
    show ta (tb (ta u)) = _
    rw [hta_u, h1, map_add, hta_u]
    abel
  have hwb : ρ (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) u ∈ rootSpace hBN ρ b := by
    have hmem := Submodule.mem_map_of_mem
      (f := (ρ (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) : V →ₗ[K] V)) hu
    rw [map_rootSpace_eq, app_Tsp_mul_Tsp_mul_Tsp_left hBN h,
      rootSpace_smul_of_ne_zero (mul_ne_zero hl hab)] at hmem
    exact hmem
  have hsum_b : u + (ta θ - θ) ∈ rootSpace hBN ρ b := by
    have e : u + (ta θ - θ) =
        ρ (Tsp hBN a α * Tsp hBN b l * Tsp hBN a α) u - θ := by
      rw [hwu]
      abel
    rw [e]
    exact Submodule.sub_mem _ hwb hθb
  have hsum_a : u + (ta θ - θ) ∈ rootSpace hBN ρ a :=
    Submodule.add_mem _ hu (axis_le_rootSpace a α hφ)
  have h0 : u + (ta θ - θ) = 0 := by
    have hmem : u + (ta θ - θ) ∈ rootSpace hBN ρ a ⊓ rootSpace hBN ρ b := ⟨hsum_a, hsum_b⟩
    rw [rootSpace_inf_eq_bot hs hII hab] at hmem
    exact (Submodule.mem_bot K).mp hmem
  refine ⟨?_, ?_⟩
  · rw [hwu]
    have e : u + θ + (ta θ - θ) = θ + (u + (ta θ - θ)) := by abel
    rw [e, h0, add_zero]
  · have e : u = -(ta θ - θ) := eq_neg_of_add_eq_zero_left h0
    rw [e]
    exact Submodule.neg_mem _ hφ

theorem finrank_rootSpace {a : N} (ha : a ≠ 0) :
    finrank K (rootSpace hBN ρ a) = 2 ∧
      ∀ c : K, c ≠ 0 → axis hBN ρ a c = rootSpace hBN ρ a := by
  obtain ⟨b, hab⟩ : ∃ b, BN a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (hs.nondegN.1 a hcon)
  set α : K := (BN a b ^ 2)⁻¹ with hαdef
  have hα0 : α ≠ 0 := inv_ne_zero (pow_ne_zero 2 hab)
  have hrel : α * 1 * BN a b ^ 2 = 1 := by
    rw [hαdef, mul_one]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hab)
  have hroot : rootSpace hBN ρ a = axis hBN ρ a α :=
    le_antisymm (fun u hu => (rootSpace_sub_one_eq hs hII hab one_ne_zero hrel hu).2)
      (axis_le_rootSpace a α)
  have hfin : finrank K (axis hBN ρ a α) = 2 :=
    (hs.siegel a ha α hα0).finrank_movedSpace hs.nondeg
  have h2 : finrank K (rootSpace hBN ρ a) = 2 := by
    rw [hroot]
    exact hfin
  refine ⟨h2, fun c hc => ?_⟩
  have hfinc : finrank K (axis hBN ρ a c) = 2 :=
    (hs.siegel a ha c hc).finrank_movedSpace hs.nondeg
  have : FiniteDimensional K (rootSpace hBN ρ a) := inferInstance
  exact Submodule.eq_of_le_of_finrank_eq (axis_le_rootSpace a c) (hfinc.trans h2.symm)

end CaseII

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1

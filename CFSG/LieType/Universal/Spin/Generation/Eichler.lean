module

public import CFSG.LieType.Universal.Spin.Chevalley.Frame
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LieType.Universal.Spin.Chevalley.Braid

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

variable (Q) in
theorem spinAction_rootHom_eq_eichler {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) (c : K) :
    spinAction Q (rootHom Q hu huw hmem (Multiplicative.ofAdd c)) = eichler Q u (c • w) := by
  have hcw : polar Q u (c • w) = 0 := by rw [polar_smul_right, huw, smul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [spinAction_rootHom, eichler_apply hu hcw, add_smul, sub_sub]

theorem eichler_smul_self {u : V} (hu : Q u = 0) (c : K) : eichler Q u (c • u) = 1 := by
  rw [← zero_add (c • u), eichler_add_smul_self hu, eichler_zero_right]

namespace HypFrame

variable (F : HypFrame Q n)

theorem spinAction_longRoot_eq_eichler {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    spinAction Q (F.longRoot hij s t (.ofAdd c)) = eichler Q (F.vec j t) (c • F.vec i s) := by
  have hcw : polar Q (F.vec j t) (c • F.vec i s) = 0 := by
    rw [polar_smul_right, F.polar_vec_of_ne hij.symm, smul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [F.spinAction_longRoot, eichler_apply (F.map_vec j t) hcw]
  simp only [polar_smul_right, QuadraticMap.map_smul, F.map_vec, smul_eq_mul]
  module

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n)

theorem spinAction_shortRoot_eq_eichler (i : Fin n) (s : Bool) (c : K) :
    spinAction Q (F.shortRoot i s (.ofAdd c)) = eichler Q (F.vec i s) (c • F.z) := by
  have hcw : polar Q (F.vec i s) (c • F.z) = 0 := by
    rw [polar_smul_right, F.polar_vec_z, smul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [F.spinAction_shortRoot, eichler_apply (F.map_vec i s) hcw]
  simp only [polar_smul_right, QuadraticMap.map_smul, F.map_z, smul_eq_mul, mul_one]
  module

end OddFrame

namespace HypFrame

variable (F : HypFrame Q n)

theorem polar_sum_vec (v : V) (i : Fin n) (s : Bool) :
    polar Q (∑ k, ∑ r, polar Q v (F.vec k (!r)) • F.vec k r) (F.vec i s) =
      polar Q v (F.vec i s) := by
  rw [← polarBilin_apply_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, polarBilin_apply_apply,
    smul_eq_mul, F.polar_vec_vec]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  cases s <;> simp

private def eichlerParams (Q : QuadraticForm K V) (H : Subgroup (V ≃ₗ[K] V)) (u : V) :
    AddSubgroup V where
  carrier := {w | polar Q u w = 0 ∧ eichler Q u w ∈ H}
  add_mem' {w w'} hw hw' := ⟨by rw [polar_add_right, hw.1, hw'.1, add_zero], by
    rw [← eichler_mul hw.1 hw'.1]
    exact mul_mem hw.2 hw'.2⟩
  zero_mem' := ⟨polar_zero_right Q u, by
    rw [eichler_zero_right]
    exact one_mem H⟩
  neg_mem' {w} hw := ⟨by rw [polar_neg_right, hw.1, neg_zero], by
    rw [← eichler_inv hw.1]
    exact inv_mem hw.2⟩

private theorem mem_eichlerParams {H : Subgroup (V ≃ₗ[K] V)} {u w : V} :
    w ∈ eichlerParams Q H u ↔ polar Q u w = 0 ∧ eichler Q u w ∈ H :=
  Iff.rfl

section RootGroups

variable {H : Subgroup (V ≃ₗ[K] V)}
  (hlong : ∀ {i j : Fin n}, i ≠ j → ∀ (s t : Bool) (c : K),
    eichler Q (F.vec j t) (c • F.vec i s) ∈ H)
  (hperp : ∀ (i : Fin n) (s : Bool) (v : V), (∀ k r, polar Q v (F.vec k r) = 0) →
    eichler Q (F.vec i s) v ∈ H)
include hlong hperp

theorem eichler_vec_mem (i : Fin n) (s : Bool) {w : V} (hw : polar Q (F.vec i s) w = 0) :
    eichler Q (F.vec i s) w ∈ H := by
  have hu : Q (F.vec i s) = 0 := F.map_vec i s
  have hterm : ∀ k r, polar Q w (F.vec k (!r)) • F.vec k r ∈ eichlerParams Q H (F.vec i s) := by
    intro k r
    rw [mem_eichlerParams]
    by_cases hki : k = i
    · rw [hki]
      by_cases hrs : r = s
      · rw [hrs]
        exact ⟨by rw [polar_smul_right, F.polar_vec_self, smul_zero], by
          rw [eichler_smul_self hu]
          exact one_mem H⟩
      · have hr : r = !s := by
          revert hrs
          cases r <;> cases s <;> decide
        rw [hr, Bool.not_not, polar_comm Q w (F.vec i s), hw, zero_smul]
        exact (eichlerParams Q H (F.vec i s)).zero_mem
    · exact ⟨by rw [polar_smul_right, F.polar_vec_of_ne (Ne.symm hki), smul_zero],
        hlong hki r s _⟩
  have hsum : ∑ k, ∑ r, polar Q w (F.vec k (!r)) • F.vec k r ∈ eichlerParams Q H (F.vec i s) :=
    sum_mem fun k _ => sum_mem fun r _ => hterm k r
  have hrest : w - ∑ k, ∑ r, polar Q w (F.vec k (!r)) • F.vec k r ∈
      eichlerParams Q H (F.vec i s) :=
    ⟨by rw [polar_comm]; exact F.polar_sub_sum_vec w i s, hperp i s _ (F.polar_sub_sum_vec w)⟩
  have h := add_mem hsum hrest
  rw [add_sub_cancel] at h
  exact h.2

theorem rootGroup_vec_le (i : Fin n) (s : Bool) : rootGroup Q (F.vec i s) ≤ H := by
  intro g hg
  obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
  exact F.eichler_vec_mem hlong hperp i s hw

theorem exists_mem_apply_eq_of_polar_eq (i : Fin n) (s : Bool) {x y : V} (hxy : Q x = Q y)
    {t : K} (hx : polar Q (F.vec i s) x = t) (hy : polar Q (F.vec i s) y = t) (ht : t ≠ 0) :
    ∃ g ∈ H, g x = y :=
  ⟨eichler Q (F.vec i s) (t⁻¹ • (y - x)),
    F.eichler_vec_mem hlong hperp i s (by
      rw [polar_smul_right, polar_sub_right, hx, hy, sub_self, smul_zero]),
    eichler_apply_eq_of_polar_eq (F.map_vec i s) hxy hx hy ht⟩

theorem exists_mem_apply_eq_smul_vec_not {v : V} (hv : Q v = 0) {i : Fin n} {s : Bool}
    (h : polar Q v (F.vec i s) ≠ 0) :
    ∃ g ∈ H, g v = polar Q v (F.vec i s) • F.vec i (!s) := by
  refine F.exists_mem_apply_eq_of_polar_eq hlong hperp i s ?_ (polar_comm Q _ _) ?_ h
  · rw [hv, QuadraticMap.map_smul, F.map_vec, smul_zero]
  · rw [polar_smul_right, F.polar_vec_not, smul_eq_mul, mul_one]

theorem exists_mem_apply_eq_smul_vec
    (hrest : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → Q v = 0 → v = 0) {v : V}
    (hv : Q v = 0) (hv0 : v ≠ 0) :
    ∃ g ∈ H, ∃ (i : Fin n) (s : Bool) (t : K), t ≠ 0 ∧ g v = t • F.vec i s := by
  have h : ∃ i s, polar Q v (F.vec i s) ≠ 0 := by
    by_contra! h
    exact hv0 (hrest v h hv)
  obtain ⟨i, s, his⟩ := h
  obtain ⟨g, hg, hgv⟩ := F.exists_mem_apply_eq_smul_vec_not hlong hperp hv his
  exact ⟨g, hg, i, !s, _, his, hgv⟩

theorem exists_mem_smul_vec_eq_smul_vec {i j : Fin n} (hij : i ≠ j) (r r' : Bool) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ g ∈ H, g (a • F.vec i r) = b • F.vec j r' := by
  have hQ : Q (a • F.vec i r + b • F.vec j r') = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, F.map_vec,
      F.map_vec, polar_smul_left, polar_smul_right, F.polar_vec_of_ne hij]
    simp
  obtain ⟨g₁, hg₁, h₁⟩ := F.exists_mem_apply_eq_of_polar_eq hlong hperp i (!r)
    (x := a • F.vec i r) (y := a • F.vec i r + b • F.vec j r') (t := a)
    (by rw [hQ, QuadraticMap.map_smul, F.map_vec, smul_zero])
    (by rw [polar_smul_right, F.polar_not_vec, smul_eq_mul, mul_one])
    (by
      rw [polar_add_right, polar_smul_right, polar_smul_right, F.polar_not_vec,
        F.polar_vec_of_ne hij]
      simp) ha
  obtain ⟨g₂, hg₂, h₂⟩ := F.exists_mem_apply_eq_of_polar_eq hlong hperp j (!r')
    (x := a • F.vec i r + b • F.vec j r') (y := b • F.vec j r') (t := b)
    (by rw [hQ, QuadraticMap.map_smul, F.map_vec, smul_zero])
    (by
      rw [polar_add_right, polar_smul_right, polar_smul_right, F.polar_not_vec,
        F.polar_vec_of_ne hij.symm]
      simp)
    (by rw [polar_smul_right, F.polar_not_vec, smul_eq_mul, mul_one]) hb
  exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [LinearEquiv.mul_apply, h₁, h₂]⟩

theorem exists_mem_smul_vec_eq_vec (hn : 2 ≤ n) (i : Fin n) (r : Bool) {a : K} (ha : a ≠ 0)
    (j : Fin n) (r' : Bool) : ∃ g ∈ H, g (a • F.vec i r) = F.vec j r' := by
  by_cases hij : i = j
  ·
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨k, hk⟩ := exists_ne i
    obtain ⟨g₁, hg₁, h₁⟩ := F.exists_mem_smul_vec_eq_smul_vec hlong hperp hk.symm r true ha
      one_ne_zero
    obtain ⟨g₂, hg₂, h₂⟩ := F.exists_mem_smul_vec_eq_smul_vec hlong hperp (hij ▸ hk) true r'
      (one_ne_zero (α := K)) one_ne_zero
    exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [LinearEquiv.mul_apply, h₁, h₂, one_smul]⟩
  · obtain ⟨g, hg, h⟩ := F.exists_mem_smul_vec_eq_smul_vec hlong hperp hij r r' ha
      (one_ne_zero (α := K))
    exact ⟨g, hg, by rw [h, one_smul]⟩

theorem exists_mem_apply_eq_vec
    (hrest : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → Q v = 0 → v = 0) (hn : 2 ≤ n)
    (j : Fin n) (r : Bool) {v : V} (hv : Q v = 0) (hv0 : v ≠ 0) : ∃ g ∈ H, g v = F.vec j r := by
  obtain ⟨g₁, hg₁, i, s, t, ht, h₁⟩ := F.exists_mem_apply_eq_smul_vec hlong hperp hrest hv hv0
  obtain ⟨g₂, hg₂, h₂⟩ := F.exists_mem_smul_vec_eq_vec hlong hperp hn i s ht j r
  exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [LinearEquiv.mul_apply, h₁, h₂]⟩

theorem exists_mem_apply_eq
    (hrest : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → Q v = 0 → v = 0) (hn : 2 ≤ n)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : ∃ g ∈ H, g x = y := by
  obtain ⟨a, ha, hax⟩ := F.exists_mem_apply_eq_vec hlong hperp hrest hn ⟨0, by omega⟩ true hx hx0
  obtain ⟨b, hb, hby⟩ := F.exists_mem_apply_eq_vec hlong hperp hrest hn ⟨0, by omega⟩ true hy hy0
  refine ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, ?_⟩
  rw [LinearEquiv.mul_apply, hax, ← hby, LinearEquiv.inv_apply_apply']

theorem elementaryGroup_le
    (hrest : ∀ v : V, (∀ k r, polar Q v (F.vec k r) = 0) → Q v = 0 → v = 0) :
    elementaryGroup Q ≤ H := by
  have hlong' : ∀ {i j : Fin n}, i ≠ j → ∀ (s t : Bool) (c : K),
      eichler Q (F.vec j t) (c • F.vec i s) ∈ H ⊓ elementaryGroup Q :=
    fun hij s t c => ⟨hlong hij s t c, eichler_mem_elementaryGroup Q _ _⟩
  have hperp' : ∀ (i : Fin n) (s : Bool) (v : V), (∀ k r, polar Q v (F.vec k r) = 0) →
      eichler Q (F.vec i s) v ∈ H ⊓ elementaryGroup Q :=
    fun i s v hv => ⟨hperp i s v hv, eichler_mem_elementaryGroup Q _ _⟩
  refine elementaryGroup_le_of_eichler_mem fun v w hv hvw => ?_
  by_cases hv0 : v = 0
  · rw [hv0, eichler_zero_left]
    exact one_mem H
  obtain ⟨g, hg, i, s, t, -, hgv⟩ := F.exists_mem_apply_eq_smul_vec hlong' hperp' hrest hv hv0
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (Subgroup.mem_inf.mp hg).2
  have hgw : polar Q (F.vec i s) (t • g w) = 0 := by
    rw [polar_smul_right, ← polar_smul_left, ← hgv, polar_map_of_mem hgO, hvw]
  have key : eichler Q v w = g⁻¹ * eichler Q (F.vec i s) (t • g w) * g := by
    rw [← eichler_smul_left, ← hgv, ← eichler_conj hgO]
    group
  rw [key]
  exact mul_mem (mul_mem (inv_mem (Subgroup.mem_inf.mp hg).1)
    (F.eichler_vec_mem hlong hperp i s hgw)) (Subgroup.mem_inf.mp hg).1

end RootGroups

end HypFrame

end CFSG.LieType.Universal.Spin

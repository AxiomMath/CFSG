module

public import CFSG.LinearAlgebra.FrobeniusIsometrySimple
public import CFSG.LinearAlgebra.FrobeniusIsometryPair

public section

namespace CFSG.LinearAlgebra

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace FrobeniusIsometry

variable {B : LinearMap.BilinForm K V} {E : Subgroup (V ≃ₗ[K] V)}

def fixSub (E : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ x ∈ E, x v = v}
  add_mem' {v w} hv hw x hx := by rw [map_add, hv x hx, hw x hx]
  zero_mem' x _ := map_zero x
  smul_mem' c v hv x hx := by rw [map_smul, hv x hx]

theorem mem_fixSub {v : V} : v ∈ fixSub E ↔ ∀ x ∈ E, x v = v := Iff.rfl

theorem natCast_eq_one_of_odd [CharP K 2] {n : ℕ} (hn : Odd n) : (n : K) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
    Nat.cast_one]

theorem mem_orthogonal {S : Submodule K V} {v : V} : v ∈ B.orthogonal S ↔ ∀ n ∈ S, B n v = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem orthogonal_inv (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) {S : Submodule K V}
    (hS : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) : ∀ x ∈ E, ∀ v ∈ B.orthogonal S, x v ∈ B.orthogonal S := by
  intro x hx v hv
  rw [mem_orthogonal] at hv ⊢
  intro n hn
  have h := hv (x⁻¹ n) (hS x⁻¹ (inv_mem hx) n hn)
  rw [← hiso x hx (x⁻¹ n) v] at h
  simpa using h

theorem restrict_nondegenerate_iff (hsymm : ∀ v w, B v w = B w v) {S : Submodule K V} :
    (B.restrict S).Nondegenerate ↔ ∀ v ∈ S, (∀ w ∈ S, B v w = 0) → v = 0 := by
  have hr : (B.restrict S).IsRefl := fun x y h => by
    change B y x = 0
    rw [hsymm]
    exact h
  rw [LinearMap.BilinForm.Nondegenerate, hr.nondegenerate_iff_separatingLeft]
  constructor
  · intro h v hv hw
    have := h ⟨v, hv⟩ fun w => hw w w.2
    simpa using congrArg Subtype.val this
  · intro h v hv
    exact Subtype.ext (h v v.2 fun w hw => hv ⟨w, hw⟩)

theorem exists_add_of_le [FiniteDimensional K V]
    (hsymm : ∀ v w, B v w = B w v) {U S : Submodule K V} (hUS : U ≤ S)
    (hU : (B.restrict U).Nondegenerate) {v : V} (hv : v ∈ S) :
    ∃ u ∈ U, ∃ s ∈ S ⊓ B.orthogonal U, v = u + s := by
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (B := B) (W := U) (fun x y h => by rw [hsymm]; exact h) hU
  have hv' : v ∈ U ⊔ B.orthogonal U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.mp hv'
  refine ⟨u, hu, s, ⟨?_, hs⟩, rfl⟩
  have := S.sub_mem hv (hUS hu)
  simpa using this

theorem restrict_inf_orthogonal_nondegenerate [FiniteDimensional K V] (hsymm : ∀ v w, B v w = B w v)
    {U S : Submodule K V} (hUS : U ≤ S) (hU : (B.restrict U).Nondegenerate)
    (hS : (B.restrict S).Nondegenerate) : (B.restrict (S ⊓ B.orthogonal U)).Nondegenerate := by
  rw [restrict_nondegenerate_iff hsymm] at hS ⊢
  intro v hv hvw
  refine hS v hv.1 fun w hw => ?_
  obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_le hsymm hUS hU hw
  rw [map_add, hvw s hs, add_zero, hsymm]
  exact mem_orthogonal.mp hv.2 u hu

theorem inf_inf_orthogonal_eq_bot (hsymm : ∀ v w, B v w = B w v) {U S : Submodule K V}
    (hU : (B.restrict U).Nondegenerate) : U ⊓ (S ⊓ B.orthogonal U) = ⊥ := by
  rw [restrict_nondegenerate_iff hsymm] at hU
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  refine hU v hv.1 fun w hw => ?_
  rw [hsymm]
  exact mem_orthogonal.mp hv.2.2 w hw

theorem finrank_inf_orthogonal_lt [FiniteDimensional K V]
    (hsymm : ∀ v w, B v w = B w v) {U S : Submodule K V}
    (hUS : U ≤ S) (hU : (B.restrict U).Nondegenerate) (hU0 : U ≠ ⊥) :
    finrank K ↥(S ⊓ B.orthogonal U) < finrank K S := by
  have hle : S ⊓ B.orthogonal U < S := by
    refine lt_of_le_of_ne inf_le_left fun h => hU0 ?_
    have hb := inf_inf_orthogonal_eq_bot hsymm (S := S) hU
    rw [h, inf_eq_left.mpr hUS] at hb
    exact hb
  exact Submodule.finrank_lt_finrank_of_lt hle

theorem good_of_split [FiniteDimensional K V] (f : (V ≃ₗ[K] V) → (V ≃ₗ[K] V))
    (hsymm : ∀ v w, B v w = B w v) {U S : Submodule K V} (hUS : U ≤ S)
    (hU : (B.restrict U).Nondegenerate) (hUE : ∀ x ∈ E, ∀ v ∈ U, x v ∈ U)
    (hSE : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w)
    {gU : V →ₗ[K] V} (h1 : ∀ v ∈ U, gU v ∈ U) (h2 : ∀ v ∈ B.orthogonal U, gU v = v)
    (h3 : ∀ v ∈ U, ∀ w ∈ U, B (gU v) (gU w) = B v w)
    (h4 : ∀ x ∈ E, ∀ v ∈ U, gU (x v) = (f x) (gU v))
    (h5 : ∀ v ∈ U, (∀ x ∈ E, x v = v) → gU v = v)
    {g' : V →ₗ[K] V} (k1 : ∀ v ∈ S ⊓ B.orthogonal U, g' v ∈ S ⊓ B.orthogonal U)
    (k2 : ∀ v ∈ B.orthogonal (S ⊓ B.orthogonal U), g' v = v)
    (k3 : ∀ v ∈ S ⊓ B.orthogonal U, ∀ w ∈ S ⊓ B.orthogonal U, B (g' v) (g' w) = B v w)
    (k4 : ∀ x ∈ E, ∀ v ∈ S ⊓ B.orthogonal U, g' (x v) = (f x) (g' v))
    (k5 : ∀ v ∈ S ⊓ B.orthogonal U, (∀ x ∈ E, x v = v) → g' v = v) :
    ∃ g : V →ₗ[K] V, (∀ v ∈ S, g v ∈ S) ∧ (∀ v ∈ B.orthogonal S, g v = v) ∧
      (∀ v ∈ S, ∀ w ∈ S, B (g v) (g w) = B v w) ∧
      (∀ x ∈ E, ∀ v ∈ S, g (x v) = (f x) (g v)) ∧
      ∀ v ∈ S, (∀ x ∈ E, x v = v) → g v = v := by
  have hUo : ∀ u ∈ U, u ∈ B.orthogonal (S ⊓ B.orthogonal U) := fun u hu =>
    mem_orthogonal.mpr fun n hn => by
      rw [hsymm]
      exact mem_orthogonal.mp hn.2 u hu
  have hS'E : ∀ x ∈ E, ∀ v ∈ S ⊓ B.orthogonal U, x v ∈ S ⊓ B.orthogonal U := fun x hx v hv =>
    ⟨hSE x hx v hv.1, orthogonal_inv hiso hUE x hx v hv.2⟩
  have hgu : ∀ u ∈ U, gU (g' u) = gU u := fun u hu => by rw [k2 u (hUo u hu)]
  have hgs : ∀ s ∈ S ⊓ B.orthogonal U, gU (g' s) = g' s := fun s hs => h2 _ (k1 s hs).2
  have hz : ∀ a ∈ U, ∀ b ∈ S ⊓ B.orthogonal U, B a b = 0 := fun a ha b hb =>
    mem_orthogonal.mp hb.2 a ha
  have hz' : ∀ a ∈ U, ∀ b ∈ S ⊓ B.orthogonal U, B b a = 0 := fun a ha b hb => by
    rw [hsymm]
    exact hz a ha b hb
  refine ⟨gU ∘ₗ g', fun v hv => ?_, fun v hv => ?_, fun v hv w hw => ?_, fun x hx v hv => ?_,
    fun v hv hfix => ?_⟩
  · obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_le hsymm hUS hU hv
    simp only [LinearMap.comp_apply, map_add]
    rw [hgu u hu, hgs s hs]
    exact S.add_mem (hUS (h1 u hu)) (k1 s hs).1
  · have hv1 : v ∈ B.orthogonal (S ⊓ B.orthogonal U) :=
      mem_orthogonal.mpr fun n hn => mem_orthogonal.mp hv n hn.1
    have hv2 : v ∈ B.orthogonal U := mem_orthogonal.mpr fun n hn => mem_orthogonal.mp hv n (hUS hn)
    rw [LinearMap.comp_apply, k2 v hv1, h2 v hv2]
  · obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_le hsymm hUS hU hv
    obtain ⟨u', hu', s', hs', rfl⟩ := exists_add_of_le hsymm hUS hU hw
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
    rw [hgu u hu, hgu u' hu', hgs s hs, hgs s' hs', h3 u hu u' hu', k3 s hs s' hs',
      hz _ (h1 u hu) _ (k1 s' hs'), hz' _ (h1 u' hu') _ (k1 s hs), hz u hu s' hs',
      hz' u' hu' s hs]
  · obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_le hsymm hUS hU hv
    simp only [LinearMap.comp_apply, map_add]
    rw [hgu _ (hUE x hx u hu), hgs _ (hS'E x hx s hs), h4 x hx u hu, k4 x hx s hs, hgu u hu,
      hgs s hs]
  · obtain ⟨u, hu, s, hs, rfl⟩ := exists_add_of_le hsymm hUS hU hv
    have hfix' : ∀ x ∈ E, x u = u ∧ x s = s := fun x hx => by
      have h := hfix x hx
      rw [map_add] at h
      have hd : x u - u = s - x s := by
        rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
      have hmem : x u - u ∈ U ⊓ (S ⊓ B.orthogonal U) := by
        refine ⟨U.sub_mem (hUE x hx u hu) hu, ?_⟩
        rw [hd]
        exact Submodule.sub_mem _ hs (hS'E x hx s hs)
      rw [inf_inf_orthogonal_eq_bot hsymm hU, Submodule.mem_bot] at hmem
      refine ⟨sub_eq_zero.mp hmem, ?_⟩
      rw [hmem] at hd
      exact (sub_eq_zero.mp hd.symm).symm
    simp only [LinearMap.comp_apply, map_add]
    rw [hgu u hu, hgs s hs, h5 u hu fun x hx => (hfix' x hx).1,
      k5 s hs fun x hx => (hfix' x hx).2]

theorem restrict_fixSub_nondegenerate [CharP K 2] [Finite E] (hsymm : ∀ v w, B v w = B w v)
    (hodd : Odd (Nat.card E)) (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) {S : Submodule K V}
    (hSE : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) (hS : (B.restrict S).Nondegenerate) :
    (B.restrict (S ⊓ fixSub E)).Nondegenerate := by
  classical
  have := Fintype.ofFinite E
  rw [restrict_nondegenerate_iff hsymm] at hS ⊢
  intro v hv hvw
  refine hS v hv.1 fun w hw => ?_
  have hPS : (∑ x : E, (x : V ≃ₗ[K] V) w) ∈ S := Submodule.sum_mem _ fun x _ => hSE x x.2 w hw
  have hPfix : (∑ x : E, (x : V ≃ₗ[K] V) w) ∈ fixSub E := fun y hy => by
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : E)) _ _ fun x => rfl
  have hBP : B v (∑ x : E, (x : V ≃ₗ[K] V) w) = B v w := by
    rw [map_sum]
    have h : ∀ x : E, B v ((x : V ≃ₗ[K] V) w) = B v w := fun x => by
      rw [← hiso x x.2 v w, hv.2 x x.2]
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul, natCast_eq_one_of_odd hodd, one_mul]
  rw [← hBP]
  exact hvw _ ⟨hPS, hPfix⟩

theorem exists_inv_compl [CharP K 2] [Finite E] (hodd : Odd (Nat.card E)) {A S : Submodule K V}
    (hAS : A ≤ S) (hAE : ∀ x ∈ E, ∀ v ∈ A, x v ∈ A) (hSE : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) :
    ∃ C : Submodule K V, C ≤ S ∧ (∀ x ∈ E, ∀ v ∈ C, x v ∈ C) ∧ A ⊓ C = ⊥ ∧ A ⊔ C = S := by
  classical
  have := Fintype.ofFinite E
  obtain ⟨A', hA'⟩ := Submodule.exists_isCompl A
  let p : V →ₗ[K] V := A.subtype ∘ₗ A.projectionOnto A' hA'
  have hpA : ∀ v, p v ∈ A := fun v => (A.projectionOnto A' hA' v).2
  have hpa : ∀ a ∈ A, p a = a := fun a ha => by
    change ((A.projectionOnto A' hA' a : A) : V) = a
    rw [Submodule.projectionOnto_apply_left hA' ⟨a, ha⟩]
  let π : V →ₗ[K] V :=
    ∑ x : E, ((x : V ≃ₗ[K] V) : V →ₗ[K] V) ∘ₗ p ∘ₗ (((x⁻¹ : E) : V ≃ₗ[K] V) : V →ₗ[K] V)
  have hπ : ∀ v, π v = ∑ x : E, (x : V ≃ₗ[K] V) (p (((x⁻¹ : E) : V ≃ₗ[K] V) v)) := fun v => by
    simp only [π, LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hπA : ∀ v, π v ∈ A := fun v => by
    rw [hπ]
    exact Submodule.sum_mem _ fun x _ => hAE x x.2 _ (hpA _)
  have hπa : ∀ a ∈ A, π a = a := fun a ha => by
    rw [hπ]
    have h : ∀ x : E, (x : V ≃ₗ[K] V) (p (((x⁻¹ : E) : V ≃ₗ[K] V) a)) = a := fun x => by
      rw [hpa _ (hAE _ (x⁻¹).2 a ha)]
      change ((x * x⁻¹ : E) : V ≃ₗ[K] V) a = a
      rw [mul_inv_cancel]
      rfl
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, natCast_eq_one_of_odd hodd, one_smul]
  have hπE : ∀ y ∈ E, ∀ v, π (y v) = y (π v) := fun y hy v => by
    rw [hπ, hπ, map_sum, ← Equiv.sum_comp (Equiv.mulLeft (⟨y, hy⟩ : E))]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
      LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  refine ⟨S ⊓ LinearMap.ker π, inf_le_left,
    fun x hx v hv => Submodule.mem_inf.mpr ⟨hSE x hx v hv.1, ?_⟩, ?_, ?_⟩
  · rw [LinearMap.mem_ker, hπE x hx, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).2, map_zero]
  · rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot, ← hπa v hv.1]
    exact LinearMap.mem_ker.mp hv.2.2
  · refine le_antisymm (sup_le hAS inf_le_left) fun v hv => ?_
    have h1 : v - π v ∈ S ⊓ LinearMap.ker π := Submodule.mem_inf.mpr
      ⟨S.sub_mem hv (hAS (hπA v)), by rw [LinearMap.mem_ker, map_sub, hπa _ (hπA v), sub_self]⟩
    have := Submodule.add_mem_sup (hπA v) h1
    rwa [add_sub_cancel] at this

theorem exists_minimal [FiniteDimensional K V]
    {S : Submodule K V} (hSE : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) (hS0 : S ≠ ⊥) :
    ∃ W ≤ S, W ≠ ⊥ ∧ (∀ x ∈ E, ∀ v ∈ W, x v ∈ W) ∧
      ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W := by
  classical
  have hex : ∃ n, ∃ W ≤ S, W ≠ ⊥ ∧ (∀ x ∈ E, ∀ v ∈ W, x v ∈ W) ∧ finrank K W = n :=
    ⟨_, S, le_rfl, hS0, hSE, rfl⟩
  obtain ⟨W, hWS, hW0, hWE, hWn⟩ := Nat.find_spec hex
  refine ⟨W, hWS, hW0, hWE, fun U hUW hUE => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  · refine Or.inr (Submodule.eq_of_le_of_finrank_le hUW ?_)
    rw [hWn]
    exact Nat.find_min' hex ⟨U, hUW.trans hWS, hU0, hUE, rfl⟩

theorem isotropic_of_minimal (hsymm : ∀ v w, B v w = B w v)
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) {W : Submodule K V}
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W)
    (hmin : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hnd : ¬ (B.restrict W).Nondegenerate) : ∀ v ∈ W, ∀ w ∈ W, B v w = 0 := by
  rcases hmin (W ⊓ B.orthogonal W) inf_le_left fun x hx v hv =>
    ⟨hWE x hx v hv.1, orthogonal_inv hiso hWE x hx v hv.2⟩ with h | h
  · refine absurd ((restrict_nondegenerate_iff hsymm).mpr fun v hv hvw => ?_) hnd
    have hv' : v ∈ W ⊓ B.orthogonal W :=
      ⟨hv, mem_orthogonal.mpr fun n hn => by rw [hsymm]; exact hvw n hn⟩
    rwa [h, Submodule.mem_bot] at hv'
  · intro v hv w hw
    have hw' : w ∈ W ⊓ B.orthogonal W := by rw [h]; exact hw
    exact mem_orthogonal.mp hw'.2 v hv

@[expose] def MinPieces (B : LinearMap.BilinForm K V) (E : Subgroup (V ≃ₗ[K] V))
    (f : (V ≃ₗ[K] V) → (V ≃ₗ[K] V)) : Prop :=
  ∀ W : Submodule K V, (∀ x ∈ E, ∀ v ∈ W, x v ∈ W) →
    (∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W) →
    W ≠ ⊥ → (B.restrict W).Nondegenerate → (∀ v ∈ W, (∀ x ∈ E, x v = v) → v = 0) →
    ∃ g : V →ₗ[K] V, (∀ v ∈ W, g v ∈ W) ∧ (∀ v ∈ B.orthogonal W, g v = v) ∧
      (∀ v ∈ W, ∀ w ∈ W, B (g v) (g w) = B v w) ∧ ∀ x ∈ E, ∀ v ∈ W, g (x v) = (f x) (g v)

@[expose] def PairPieces (B : LinearMap.BilinForm K V) (E : Subgroup (V ≃ₗ[K] V))
    (f : (V ≃ₗ[K] V) → (V ≃ₗ[K] V)) : Prop :=
  ∀ W W' : Submodule K V, (∀ x ∈ E, ∀ v ∈ W, x v ∈ W) → (∀ x ∈ E, ∀ v ∈ W', x v ∈ W') →
    (∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W) →
    (∀ U : Submodule K V, U ≤ W' → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W') →
    (∀ v ∈ W, ∀ w ∈ W, B v w = 0) → (∀ v ∈ W', ∀ w ∈ W', B v w = 0) →
    (∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0) →
    (B.restrict (W ⊔ W')).Nondegenerate ∧
      ∃ g : V →ₗ[K] V, (∀ v ∈ W ⊔ W', g v ∈ W ⊔ W') ∧ (∀ v ∈ B.orthogonal (W ⊔ W'), g v = v) ∧
        (∀ v ∈ W ⊔ W', ∀ w ∈ W ⊔ W', B (g v) (g w) = B v w) ∧
        ∀ x ∈ E, ∀ v ∈ W ⊔ W', g (x v) = (f x) (g v)

theorem exists_piece [CharP K 2] [FiniteDimensional K V] [Finite E]
    (hsymm : ∀ v w, B v w = B w v) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (f : (V ≃ₗ[K] V) → (V ≃ₗ[K] V))
    (hMin : MinPieces B E f) (hPair : PairPieces B E f) {S : Submodule K V}
    (hSE : ∀ x ∈ E, ∀ v ∈ S, x v ∈ S) (hS : (B.restrict S).Nondegenerate) (hS0 : S ≠ ⊥)
    (hfix : ∀ v ∈ S, (∀ x ∈ E, x v = v) → v = 0) :
    ∃ U ≤ S, U ≠ ⊥ ∧ (B.restrict U).Nondegenerate ∧ (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) ∧
      ∃ gU : V →ₗ[K] V, (∀ v ∈ U, gU v ∈ U) ∧ (∀ v ∈ B.orthogonal U, gU v = v) ∧
        (∀ v ∈ U, ∀ w ∈ U, B (gU v) (gU w) = B v w) ∧
        ∀ x ∈ E, ∀ v ∈ U, gU (x v) = (f x) (gU v) := by
  have hsimple : ∀ W ≤ S, W ≠ ⊥ → (∀ x ∈ E, ∀ v ∈ W, x v ∈ W) →
      (∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W) →
      (B.restrict W).Nondegenerate → ∃ U ≤ S, U ≠ ⊥ ∧ (B.restrict U).Nondegenerate ∧
        (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) ∧
        ∃ gU : V →ₗ[K] V, (∀ v ∈ U, gU v ∈ U) ∧ (∀ v ∈ B.orthogonal U, gU v = v) ∧
          (∀ v ∈ U, ∀ w ∈ U, B (gU v) (gU w) = B v w) ∧
          ∀ x ∈ E, ∀ v ∈ U, gU (x v) = (f x) (gU v) :=
    fun W hWS hW0 hWE hmin hWnd => ⟨W, hWS, hW0, hWnd, hWE,
      hMin W hWE hmin hW0 hWnd fun v hv hv' => hfix v (hWS hv) hv'⟩
  obtain ⟨W, hWS, hW0, hWE, hmin⟩ := exists_minimal hSE hS0
  by_cases hWnd : (B.restrict W).Nondegenerate
  · exact hsimple W hWS hW0 hWE hmin hWnd
  have hWi := isotropic_of_minimal hsymm hiso hWE hmin hWnd
  have hAE := fun x hx v (hv : v ∈ S ⊓ B.orthogonal W) =>
    (⟨hSE x hx v hv.1, orthogonal_inv hiso hWE x hx v hv.2⟩ : x v ∈ S ⊓ B.orthogonal W)
  obtain ⟨C, hCS, hCE, hAC, hACS⟩ := exists_inv_compl hodd inf_le_left hAE hSE
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq] at hACS
    apply hW0
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    refine (restrict_nondegenerate_iff hsymm).mp hS v (hWS hv) fun w hw => ?_
    have hw' : w ∈ S ⊓ B.orthogonal W := by rw [hACS]; exact hw
    exact mem_orthogonal.mp hw'.2 v hv
  obtain ⟨W', hW'C, hW'0, hW'E, hmin'⟩ := exists_minimal hCE hC0
  have hpair : ∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hW'0
    rw [eq_bot_iff]
    intro w hw
    have hmem : w ∈ (S ⊓ B.orthogonal W) ⊓ C :=
      ⟨⟨hCS (hW'C hw), mem_orthogonal.mpr fun v hv => hcon v hv w hw⟩, hW'C hw⟩
    rwa [hAC] at hmem
  by_cases hW'nd : (B.restrict W').Nondegenerate
  · exact hsimple W' (hW'C.trans hCS) hW'0 hW'E hmin' hW'nd
  have hW'i := isotropic_of_minimal hsymm hiso hW'E hmin' hW'nd
  obtain ⟨hUnd, gU, hg⟩ := hPair W W' hWE hW'E hmin hmin' hWi hW'i hpair
  refine ⟨W ⊔ W', sup_le hWS (hW'C.trans hCS), fun h => hW0 (eq_bot_iff.mpr ?_), hUnd,
    fun x hx v hv => ?_, gU, hg⟩
  · rw [← h]
    exact le_sup_left
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hWE x hx a ha) (hW'E x hx b hb)

theorem exists_good [CharP K 2] [FiniteDimensional K V] [Finite E]
    (hsymm : ∀ v w, B v w = B w v) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (f : (V ≃ₗ[K] V) → (V ≃ₗ[K] V))
    (hfE : ∀ x ∈ E, f x ∈ E) (hMin : MinPieces B E f) (hPair : PairPieces B E f) (n : ℕ) :
    ∀ S : Submodule K V, finrank K S = n → (∀ x ∈ E, ∀ v ∈ S, x v ∈ S) →
      (B.restrict S).Nondegenerate →
      ∃ g : V →ₗ[K] V, (∀ v ∈ S, g v ∈ S) ∧ (∀ v ∈ B.orthogonal S, g v = v) ∧
        (∀ v ∈ S, ∀ w ∈ S, B (g v) (g w) = B v w) ∧
        (∀ x ∈ E, ∀ v ∈ S, g (x v) = (f x) (g v)) ∧
        ∀ v ∈ S, (∀ x ∈ E, x v = v) → g v = v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hSE hS
  by_cases hS0 : S = ⊥
  · subst hS0
    refine ⟨LinearMap.id, fun v hv => hv, fun v _ => rfl, fun v _ w _ => rfl, fun x _ v hv => ?_,
      fun v _ _ => rfl⟩
    rw [Submodule.mem_bot] at hv
    simp [hv]
  obtain ⟨U, hUS, hU0, hUnd, hUE, gU, h1, h2, h3, h4, h5⟩ :
      ∃ U ≤ S, U ≠ ⊥ ∧ (B.restrict U).Nondegenerate ∧ (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) ∧
        ∃ gU : V →ₗ[K] V, (∀ v ∈ U, gU v ∈ U) ∧ (∀ v ∈ B.orthogonal U, gU v = v) ∧
          (∀ v ∈ U, ∀ w ∈ U, B (gU v) (gU w) = B v w) ∧
          (∀ x ∈ E, ∀ v ∈ U, gU (x v) = (f x) (gU v)) ∧
          ∀ v ∈ U, (∀ x ∈ E, x v = v) → gU v = v := by
    by_cases hF : S ⊓ fixSub E = ⊥
    · have hfix : ∀ v ∈ S, (∀ x ∈ E, x v = v) → v = 0 := fun v hv hv' => by
        have hmem : v ∈ S ⊓ fixSub E := ⟨hv, hv'⟩
        rwa [hF, Submodule.mem_bot] at hmem
      obtain ⟨U, hUS, hU0, hUnd, hUE, gU, h1, h2, h3, h4⟩ :=
        exists_piece hsymm hodd hiso f hMin hPair hSE hS hS0 hfix
      refine ⟨U, hUS, hU0, hUnd, hUE, gU, h1, h2, h3, h4, fun v hv hv' => ?_⟩
      rw [hfix v (hUS hv) hv', map_zero]
    · refine ⟨S ⊓ fixSub E, inf_le_left, hF, restrict_fixSub_nondegenerate hsymm hodd hiso hSE hS,
        fun x hx v hv => ⟨hSE x hx v hv.1, fun y hy => ?_⟩, LinearMap.id, fun v hv => hv,
        fun v _ => rfl, fun v _ w _ => rfl, fun x hx v hv => ?_, fun v _ _ => rfl⟩
      · rw [hv.2 x hx, hv.2 y hy]
      · change x v = (f x) v
        rw [hv.2 x hx, hv.2 _ (hfE x hx)]
  have hlt := finrank_inf_orthogonal_lt hsymm hUS hUnd hU0
  obtain ⟨g', k1, k2, k3, k4, k5⟩ := ih _ (hn ▸ hlt) (S ⊓ B.orthogonal U) rfl
    (fun x hx v hv => ⟨hSE x hx v hv.1, orthogonal_inv hiso hUE x hx v hv.2⟩)
    (restrict_inf_orthogonal_nondegenerate hsymm hUS hUnd hS)
  exact good_of_split f hsymm hUS hUnd hUE hSE hiso h1 h2 h3 h4 h5 k1 k2 k3 k4 k5

end FrobeniusIsometry

open FrobeniusIsometry in
theorem exists_isometry_conj_eq_pow_card [Fintype K] [CharP K 2] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    {E : Subgroup (V ≃ₗ[K] V)} [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hodd : Odd (Nat.card E)) (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) :
    ∃ g : V ≃ₗ[K] V, (∀ v w, B (g v) (g w) = B v w) ∧
      (∀ x ∈ E, g * x * g⁻¹ = x ^ Fintype.card K) ∧ ∀ v, (∀ x ∈ E, x v = v) → g v = v := by
  have hnd' : (B.restrict ⊤).Nondegenerate :=
    (restrict_nondegenerate_iff hsymm).mpr fun v _ hv => hnd v fun w => hv w trivial
  obtain ⟨g, -, -, h3, h4, h5⟩ := exists_good hsymm hodd hiso (fun x => x ^ Fintype.card K)
    (fun x hx => pow_mem hx _)
    (fun W hWE hmin hW0 hWnd hfix =>
      exists_isometry_pow_card_of_minimal B hsymm hcomm hodd hiso W hWE hmin hW0 hWnd hfix)
    (fun W W' hWE hW'E hmW hmW' hiW hiW' hp =>
      exists_isometry_pow_card_of_pair B hsymm hcomm hodd hiso W W' hWE hW'E hmW hmW' hiW hiW' hp)
    _ ⊤ rfl (fun _ _ _ _ => trivial) hnd'
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    refine hnd v fun w => ?_
    have h := h3 v trivial w trivial
    rwa [LinearMap.mem_ker.mp hv, map_zero, LinearMap.zero_apply, eq_comm] at h
  let ge : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo g hinj
  refine ⟨ge, fun v w => h3 v trivial w trivial, fun x hx => ?_, fun v hv => h5 v trivial hv⟩
  refine LinearEquiv.ext fun v => ?_
  change ge (x (ge.symm v)) = (x ^ Fintype.card K) v
  have h := h4 x hx (ge.symm v) trivial
  change ge (x (ge.symm v)) = (x ^ Fintype.card K) (ge (ge.symm v)) at h
  rw [h, LinearEquiv.apply_symm_apply]

end CFSG.LinearAlgebra

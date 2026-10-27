module

public import CFSG.GF2Type.CenterFour.Setting
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem cj_mem_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

private theorem cj_conj_conj (H : Subgroup G) (g k : G) :
    CFSG.conjugate (CFSG.conjugate H g) k = CFSG.conjugate H (g * k) := by
  ext x
  rw [cj_mem_iff, cj_mem_iff, cj_mem_iff]
  simp only [mul_assoc, mul_inv_rev, inv_inv]

private theorem cj_card (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
    (MulEquiv.injective _)).toEquiv).symm

private theorem cj_centralizer (z g : G) :
    centralizer ({g⁻¹ * z * g} : Set G) = CFSG.conjugate (centralizer ({z} : Set G)) g := by
  ext x
  rw [mem_centralizer_singleton_iff, cj_mem_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * x) * g⁻¹ := by rw [h]
      _ = z * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * z * g * x := by group

private theorem cj_normalizer (H : Subgroup G) (g : G) :
    Subgroup.normalizer (CFSG.conjugate H g : Set G) =
      CFSG.conjugate (Subgroup.normalizer (H : Set G)) g :=
  (Subgroup.map_normalizer_eq_of_bijective H
    (f := (MulAut.conj g⁻¹).toMonoidHom) (MulEquiv.bijective _)).symm

private theorem cj_cyclic (H : Subgroup G) (g : G) [IsCyclic H] :
    IsCyclic (CFSG.conjugate H g) :=
  isCyclic_of_surjective
    (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
      (MulEquiv.injective _)).toMonoidHom
    (MulEquiv.surjective _)

private theorem cj_le_iff (A B : Subgroup G) (g : G) :
    CFSG.conjugate A g ≤ CFSG.conjugate B g ↔ A ≤ B := by
  constructor
  · intro h x hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have hy : g⁻¹ * x * g ∈ CFSG.conjugate A g := cj_mem_iff.mpr (by rw [e]; exact hx)
    have hz := cj_mem_iff.mp (h hy)
    rwa [e] at hz
  · intro h x hx
    exact cj_mem_iff.mpr (h (cj_mem_iff.mp hx))

private theorem cj_conj_eq (z g : G) : (MulAut.conj g⁻¹).toMonoidHom z = g⁻¹ * z * g := by
  show MulAut.conj g⁻¹ z = g⁻¹ * z * g
  rw [MulAut.conj_apply, inv_inv]

private theorem cj_orderOf (z g : G) : orderOf (g⁻¹ * z * g) = orderOf z := by
  rw [← cj_conj_eq z g]
  exact orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _) z

private theorem card_map_injective (H : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    Nat.card (H.map f) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H f hf).toEquiv).symm

private theorem cj_center_le_iff {z : G} {n : ℕ} (hC : Config z n) (g k : G) :
    CFSG.conjugate (centerAt (g⁻¹ * z * g)) k ≤ centralizer ({g⁻¹ * z * g} : Set G) ↔
      k⁻¹ * (g⁻¹ * z * g) * k ∈ coreAt (g⁻¹ * z * g) := by
  have hm := hC.center_le_iff (g * k * g⁻¹)
  have e1 : CFSG.conjugate (centerAt (g⁻¹ * z * g)) k =
      CFSG.conjugate (CFSG.conjugate (centerAt z) (g * k * g⁻¹)) g := by
    rw [centerAt_conj z g, cj_conj_conj, cj_conj_conj,
      show g * k * g⁻¹ * g = g * k by group]
  rw [e1, cj_centralizer, cj_le_iff, hm, coreAt_conj z g, cj_mem_iff]
  rw [show g * (k⁻¹ * (g⁻¹ * z * g) * k) * g⁻¹ = (g * k * g⁻¹)⁻¹ * z * (g * k * g⁻¹) by group]

private theorem cj_selfC {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ h ∈ centralizer ({g⁻¹ * z * g} : Set G),
      (∀ q ∈ coreAt (g⁻¹ * z * g), h * q = q * h) → h ∈ coreAt (g⁻¹ * z * g) := by
  intro h hh hcomm
  rw [cj_centralizer, cj_mem_iff] at hh
  rw [coreAt_conj z g, cj_mem_iff]
  apply hC.selfCentralizing _ hh
  intro q hq
  have hq' : g⁻¹ * q * g ∈ coreAt (g⁻¹ * z * g) := by
    rw [coreAt_conj z g, cj_mem_iff, show g * (g⁻¹ * q * g) * g⁻¹ = q by group]
    exact hq
  have key := hcomm _ hq'
  calc g * h * g⁻¹ * q = g * (h * (g⁻¹ * q * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * q * g * h) * g⁻¹ := by rw [key]
    _ = q * (g * h * g⁻¹) := by group

private theorem cj_sq {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ x ∈ coreAt (g⁻¹ * z * g), x ^ 2 = 1 ∨ x ^ 2 = g⁻¹ * z * g := by
  intro x hx
  rw [coreAt_conj z g, cj_mem_iff] at hx
  have key : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by
    rw [pow_two, pow_two]; group
  rcases hC.sq_eq _ hx with h | h
  · left; rw [key, h]; group
  · right; rw [key, h]

private theorem cj_comm {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ x ∈ coreAt (g⁻¹ * z * g), ∀ y ∈ coreAt (g⁻¹ * z * g),
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = g⁻¹ * z * g := by
  intro x hx y hy
  rw [coreAt_conj z g, cj_mem_iff] at hx hy
  have key : ⁅x, y⁆ = g⁻¹ * ⁅g * x * g⁻¹, g * y * g⁻¹⁆ * g := by
    simp only [commutatorElement_def]; group
  rw [key]
  rcases hC.comm_eq _ hx _ hy with h | h
  · left; rw [h]; group
  · right; rw [h]

private theorem cj_pullback_le {z : G} {n : ℕ} (hC : Config z n) (g : G) (U : Subgroup G)
    (hU : U ≤ coreAt (g⁻¹ * z * g)) : U.map (MulAut.conj g).toMonoidHom ≤ coreAt z := by
  intro y hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  have hu' := hU hu
  rw [coreAt_conj z g, cj_mem_iff] at hu'
  simpa [MulAut.conj_apply] using hu'

private theorem cj_centralizer_sub (H : Subgroup G) (g : G) :
    centralizer (CFSG.conjugate H g : Set G) = CFSG.conjugate (centralizer (H : Set G)) g := by
  ext x
  rw [cj_mem_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hyp h' hh'
    have hm' : g * (g⁻¹ * h' * g) * g⁻¹ ∈ H := by
      rw [show g * (g⁻¹ * h' * g) * g⁻¹ = h' by group]
      exact hh'
    have hm : g⁻¹ * h' * g ∈ CFSG.conjugate H g := cj_mem_iff.mpr hm'
    have h1 := hyp (g⁻¹ * h' * g) hm
    calc h' * (g * x * g⁻¹) = g * ((g⁻¹ * h' * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h' * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * h' := by group
  · intro hyp h hh
    have hh2 : h ∈ CFSG.conjugate H g := hh
    have hh' : g * h * g⁻¹ ∈ H := cj_mem_iff.mp hh2
    have e := hyp (g * h * g⁻¹) hh'
    calc h * x = g⁻¹ * ((g * h * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * h * g⁻¹)) * g := by rw [e]
      _ = x * h := by group

private theorem cj_elemAb_map {U : Subgroup G} (hU : CFSG.Open.IsElemAbelian 2 U) (f : G →* G) :
    CFSG.Open.IsElemAbelian 2 (U.map f) := by
  exact CFSG.Open.IsElemAbelian.map hU f

private theorem cj_elem {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ U : Subgroup G, U ≤ coreAt (g⁻¹ * z * g) → CFSG.Open.IsElemAbelian 2 U →
      Nat.card U ≤ 2 ^ (n + 1) := by
  intro U hU hE
  have h := hC.card_elem_le _ (cj_pullback_le hC g U hU)
    (cj_elemAb_map hE (MulAut.conj g).toMonoidHom)
  rwa [card_map_injective U (MulAut.conj g).toMonoidHom (MulEquiv.injective _)] at h

private theorem cj_disj {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ U : Subgroup G, U ≤ coreAt (g⁻¹ * z * g) → CFSG.Open.IsElemAbelian 2 U →
      U ⊓ centerAt (g⁻¹ * z * g) = ⊥ → Nat.card U ≤ 2 ^ n := by
  intro U hU hE hdisj
  have hVd : U.map (MulAut.conj g).toMonoidHom ⊓ centerAt z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy1
    have hz : u ∈ centerAt (g⁻¹ * z * g) := by
      rw [centerAt_conj z g, cj_mem_iff]
      simpa [MulAut.conj_apply] using hy2
    have hu1 : u ∈ U ⊓ centerAt (g⁻¹ * z * g) := Subgroup.mem_inf.mpr ⟨hu, hz⟩
    rw [hdisj, Subgroup.mem_bot] at hu1
    rw [hu1, map_one, Subgroup.mem_bot]
  have h := hC.card_elem_le_of_disjoint _ (cj_pullback_le hC g U hU)
    (cj_elemAb_map hE (MulAut.conj g).toMonoidHom) hVd
  rwa [card_map_injective U (MulAut.conj g).toMonoidHom (MulEquiv.injective _)] at h

private theorem cj_pairwise {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∀ (s : ℕ) (f : Fin s → G), (∀ i, f i ∈ coreAt (g⁻¹ * z * g)) →
      (∀ i j, i ≠ j → ⁅f i, f j⁆ = g⁻¹ * z * g) → s ≤ 2 * n + 1 := by
  intro s f hf hcomm
  apply hC.card_pairwise_le s (fun i => g * f i * g⁻¹)
  · intro i
    have h := hf i
    rw [coreAt_conj z g, cj_mem_iff] at h
    exact h
  · intro i j hij
    have e : ⁅g * f i * g⁻¹, g * f j * g⁻¹⁆ = g * ⁅f i, f j⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    show ⁅g * f i * g⁻¹, g * f j * g⁻¹⁆ = z
    rw [e, hcomm i j hij]; group

private theorem cj_mem_core {z : G} {n : ℕ} (hC : Config z n) (g k : G)
    (hk : k⁻¹ * (g⁻¹ * z * g) * k ∈ centralizer (centerAt (g⁻¹ * z * g) : Set G)) :
    k⁻¹ * (g⁻¹ * z * g) * k ∈ coreAt (g⁻¹ * z * g) := by
  rw [centerAt_conj z g, cj_centralizer_sub, cj_mem_iff] at hk
  have hm : (g * k * g⁻¹)⁻¹ * z * (g * k * g⁻¹) ∈ centralizer (centerAt z : Set G) := by
    rw [show (g * k * g⁻¹)⁻¹ * z * (g * k * g⁻¹) = g * (k⁻¹ * (g⁻¹ * z * g) * k) * g⁻¹ by group]
    exact hk
  rw [coreAt_conj z g, cj_mem_iff,
    show g * (k⁻¹ * (g⁻¹ * z * g) * k) * g⁻¹ = (g * k * g⁻¹)⁻¹ * z * (g * k * g⁻¹) by group]
  exact hC.mem_core_of_centralizes (g * k * g⁻¹) hm

private theorem cj_fused {z : G} {n : ℕ} (hC : Config z n) (g : G) :
    ∃ k : G, k⁻¹ * (g⁻¹ * z * g) * k ∈ coreAt (g⁻¹ * z * g) ∧
      k⁻¹ * (g⁻¹ * z * g) * k ≠ g⁻¹ * z * g := by
  obtain ⟨k, hk1, hk2⟩ := hC.exists_fused
  have e : (g⁻¹ * k * g)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * k * g) = g⁻¹ * (k⁻¹ * z * k) * g := by
    group
  refine ⟨g⁻¹ * k * g, ?_, ?_⟩
  · rw [e, coreAt_conj z g, cj_mem_iff,
      show g * (g⁻¹ * (k⁻¹ * z * k) * g) * g⁻¹ = k⁻¹ * z * k by group]
    exact hk1
  · intro heq
    apply hk2
    rw [e] at heq
    calc k⁻¹ * z * k = g * (g⁻¹ * (k⁻¹ * z * k) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [heq]
      _ = z := by group

theorem Config.conj {z : G} {n : ℕ} (hC : Config z n) (g : G) : Config (g⁻¹ * z * g) n where
  orderOf_eq := (cj_orderOf z g).trans hC.orderOf_eq
  three_le := hC.three_le
  mem_center := by
    rw [centerAt_conj z g, cj_mem_iff, show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hC.mem_center
  center_cyclic := by
    haveI := hC.center_cyclic
    rw [centerAt_conj z g]
    exact cj_cyclic _ g
  card_center := by
    rw [centerAt_conj z g, cj_card]
    exact hC.card_center
  normalizer_center := by
    rw [centerAt_conj z g, cj_normalizer, hC.normalizer_center, cj_centralizer z g]
  selfCentralizing := cj_selfC hC g
  sq_eq := cj_sq hC g
  comm_eq := cj_comm hC g
  card_core := by
    rw [coreAt_conj z g, cj_card]
    exact hC.card_core
  card_elem_le := cj_elem hC g
  card_elem_le_of_disjoint := cj_disj hC g
  card_pairwise_le := cj_pairwise hC g
  center_le_iff := fun k => cj_center_le_iff hC g k
  mem_core_of_centralizes := fun k hk => cj_mem_core hC g k hk
  exists_fused := cj_fused hC g

end CFSG.GF2Type.CenterFour

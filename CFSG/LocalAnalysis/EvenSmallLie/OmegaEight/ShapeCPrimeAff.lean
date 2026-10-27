module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeAffine

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] noncomputable def aff (t : G) (ψ : V6 → G) (g : G) (v : V6) : V6 :=
  coord ψ (t * (g * (t * ψ v) * g⁻¹))

abbrev Kgrp (t : G) (Q : Subgroup G) : Subgroup G :=
  normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ⊓ normalizer (Q : Set G)

theorem add_self_V6 (x : V6) : x + x = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = y
  fin_cases y <;> rfl

namespace Setting

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G} {c : G}
  {v₀ : ℕ} (hS : Setting ε t L U Q P a ψ p c v₀)
include hS

theorem lin_zero {g : G} (hg : g ∈ normalizer (Q : Set G)) : lin ψ g 0 = 0 := by
  have h := hS.rad.lin_add hg 0 0
  rw [add_zero] at h
  have h2 : lin ψ g 0 + lin ψ g 0 = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize lin ψ g 0 i = x
    fin_cases x <;> rfl
  rw [← h] at h2
  exact h2

theorem tψ_injective {v w : V6} (h : t * ψ v = t * ψ w) : v = w :=
  hS.rad.ψ_inj (mul_left_cancel h)

theorem exists_aff_eq {g : G} (hg : g ∈ Kgrp t Q) :
    ∃ w, g * t * g⁻¹ = t * ψ w ∧ ∀ v, g * (t * ψ v) * g⁻¹ = t * ψ (w + lin ψ g v) ∧
      aff t ψ g v = w + lin ψ g v := by
  obtain ⟨w, hw⟩ := hS.conj_t_eq hg.1
  refine ⟨w, hw, fun v => ?_⟩
  have h1 : g * (t * ψ v) * g⁻¹ = t * ψ (w + lin ψ g v) := by
    rw [hS.rad.ψ_add, hS.rad.ψ_lin hg.2]
    calc g * (t * ψ v) * g⁻¹ = (g * t * g⁻¹) * (g * ψ v * g⁻¹) := by group
      _ = t * ψ w * (g * ψ v * g⁻¹) := by rw [hw]
      _ = t * (ψ w * (g * ψ v * g⁻¹)) := by group
  refine ⟨h1, ?_⟩
  rw [aff, h1, ← mul_assoc, hS.shape.mul_self, one_mul, hS.rad.coord_ψ]

theorem conj_tψ {g : G} (hg : g ∈ Kgrp t Q) (v : V6) :
    g * (t * ψ v) * g⁻¹ = t * ψ (aff t ψ g v) := by
  obtain ⟨w, -, h⟩ := hS.exists_aff_eq hg
  rw [(h v).1, (h v).2]

theorem aff_eq {g : G} (hg : g ∈ Kgrp t Q) (v : V6) :
    aff t ψ g v = aff t ψ g 0 + lin ψ g v := by
  obtain ⟨w, -, h⟩ := hS.exists_aff_eq hg
  rw [(h v).2, (h 0).2, hS.lin_zero hg.2, add_zero]

theorem conj_t_aff {g : G} (hg : g ∈ Kgrp t Q) : g * t * g⁻¹ = t * ψ (aff t ψ g 0) := by
  have h := hS.conj_tψ hg 0
  rwa [hS.rad.ψ_zero, mul_one] at h

theorem aff_mul {g h : G} (hg : g ∈ Kgrp t Q) (hh : h ∈ Kgrp t Q) (v : V6) :
    aff t ψ (g * h) v = aff t ψ g (aff t ψ h v) := by
  apply hS.tψ_injective
  rw [← hS.conj_tψ (mul_mem hg hh), ← hS.conj_tψ hg, ← hS.conj_tψ hh]
  group

theorem aff_one (v : V6) : aff t ψ 1 v = v := by
  rw [aff, one_mul, inv_one, mul_one, ← mul_assoc, hS.shape.mul_self, one_mul, hS.rad.coord_ψ]

@[expose] noncomputable def affHom : Kgrp t Q →* Equiv.Perm V6 where
  toFun g :=
    { toFun := aff t ψ g
      invFun := aff t ψ (g : G)⁻¹
      left_inv := fun v => by
        rw [← hS.aff_mul (inv_mem g.2) g.2, inv_mul_cancel, hS.aff_one]
      right_inv := fun v => by
        rw [← hS.aff_mul g.2 (inv_mem g.2), mul_inv_cancel, hS.aff_one] }
  map_one' := Equiv.ext fun v => hS.aff_one v
  map_mul' g h := Equiv.ext fun v => hS.aff_mul g.2 h.2 v

theorem E_le_Kgrp : Q ⊔ zpowers t ≤ Kgrp t Q := by
  intro x hx
  refine ⟨le_normalizer hx, mem_normalizer_iff.2 fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · rw [hS.E_comm hx (mem_sup_left hn), mul_inv_cancel_right]
    exact hn
  · have h := hS.E_comm hx (mem_sup_left hn)
    have : n = x * n * x⁻¹ := by
      have h2 : x * n * x⁻¹ * x = x * (x * n * x⁻¹) := h.symm
      calc n = x⁻¹ * (x * n * x⁻¹ * x) := by group
        _ = x⁻¹ * (x * (x * n * x⁻¹)) := by rw [h2]
        _ = x * n * x⁻¹ := by group
    rw [this]
    exact hn

theorem affHom_eq_one_iff (g : Kgrp t Q) : hS.affHom g = 1 ↔ (g : G) ∈ Q ⊔ zpowers t := by
  constructor
  · intro h
    have hv : ∀ v, (g : G) * (t * ψ v) * (g : G)⁻¹ = t * ψ v := fun v => by
      rw [hS.conj_tψ g.2]
      congr 2
      exact congrArg (fun σ : Equiv.Perm V6 => σ v) h
    have ht : (g : G) * t * (g : G)⁻¹ = t := by simpa [hS.rad.ψ_zero] using hv 0
    refine hS.data.centralizer_Q ⟨mem_centralizer_singleton_iff.2 ?_,
      mem_centralizer_iff.2 fun x hx => ?_⟩
    · calc (g : G) * t = (g : G) * t * (g : G)⁻¹ * g := by group
        _ = t * g := by rw [ht]
    · obtain ⟨v, rfl⟩ := hS.rad.mem_ψ x hx
      have h2 : (g : G) * ψ v * (g : G)⁻¹ = ψ v := by
        have := hv v
        calc (g : G) * ψ v * (g : G)⁻¹ = ((g : G) * t * (g : G)⁻¹)⁻¹ *
              ((g : G) * (t * ψ v) * (g : G)⁻¹) := by group
          _ = ψ v := by rw [ht, this, ← mul_assoc, inv_mul_cancel, one_mul]
      calc ψ v * g = (g : G) * ψ v * (g : G)⁻¹ * g := by rw [h2]
        _ = (g : G) * ψ v := by group
  · intro h
    refine Equiv.ext fun v => ?_
    change aff t ψ g v = v
    rw [aff, hS.E_comm h (mul_mem t_mem_E (hS.ψ_mem_E v)), mul_inv_cancel_right,
      ← mul_assoc, hS.shape.mul_self, one_mul, hS.rad.coord_ψ]

theorem card_range_mul [Finite G] :
    Nat.card hS.affHom.range * 128 = Nat.card (Kgrp t Q) := by
  have e : hS.affHom.ker ≃ (Q ⊔ zpowers t : Subgroup G) :=
    { toFun := fun g => ⟨g.1.1, (hS.affHom_eq_one_iff g.1).1 g.2⟩
      invFun := fun x => ⟨⟨x.1, hS.E_le_Kgrp x.2⟩, (hS.affHom_eq_one_iff _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Subgroup.card_ker_mul_card_range hS.affHom, Nat.card_congr e, hS.card_E, mul_comm]

theorem aff_zero_mem_Zset {g : G} (hg : g ∈ Kgrp t Q) : aff t ψ g 0 ∈ Zset t Q ψ :=
  ⟨g, hg.1, hS.conj_t_aff hg⟩

theorem aff_zero_eq_zero_iff {g : G} (hg : g ∈ Kgrp t Q) : aff t ψ g 0 = 0 ↔ g * t = t * g := by
  constructor
  · intro h
    have h1 := hS.conj_t_aff hg
    rw [h, hS.rad.ψ_zero, mul_one] at h1
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]
  · intro h
    apply hS.tψ_injective
    rw [← hS.conj_t_aff hg, hS.rad.ψ_zero, mul_one, h, mul_inv_cancel_right]

theorem aff_eq_lin {g : G} (hg : g ∈ Kgrp t Q) (hgt : g * t = t * g) (v : V6) :
    aff t ψ g v = lin ψ g v := by
  rw [hS.aff_eq hg, (hS.aff_zero_eq_zero_iff hg).2 hgt, zero_add]

theorem aff_add3 {g : G} (hg : g ∈ Kgrp t Q) (x y z : V6) :
    aff t ψ g (x + y + z) = aff t ψ g x + aff t ψ g y + aff t ψ g z := by
  rw [hS.aff_eq hg, hS.aff_eq hg x, hS.aff_eq hg y, hS.aff_eq hg z, hS.rad.lin_add hg.2,
    hS.rad.lin_add hg.2]
  have h := add_self_V6 (aff t ψ g 0)
  calc aff t ψ g 0 + (lin ψ g x + lin ψ g y + lin ψ g z) =
      aff t ψ g 0 + (aff t ψ g 0 + aff t ψ g 0) + (lin ψ g x + lin ψ g y + lin ψ g z) := by
        rw [h, add_zero]
    _ = _ := by abel

theorem c_mem_Kgrp : c ∈ Kgrp t Q := ⟨hS.c_mem_normalizer_E, hS.c_mem_normalizer_Q⟩

theorem P_le_Kgrp : P ≤ Kgrp t Q := fun _ hx =>
  ⟨hS.P_le_normalizer_E hx, hS.rad.P_le_normalizer hx⟩

theorem aff_c (v : V6) : aff t ψ c v = toMat 6 6 (reflRows ε v₀) *ᵥ v := by
  rw [hS.aff_eq_lin hS.c_mem_Kgrp hS.shape.c_comm, hS.lin_c]

theorem aff_P {x : G} (hx : x ∈ P) (v : V6) : aff t ψ x v = lin ψ x v :=
  hS.aff_eq_lin (hS.P_le_Kgrp hx) (hS.commute_of_mem_P hx) v

end Setting

end CFSG.EvenSmallLie.OmegaEight.CPrime

module

public import CFSG.CGT.Foote82.T66.MC1Steps
import CFSG.CGT.Foote82.Lemma61
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.CaseIPerm

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure Hyp (G L : Subgroup (GLV V)) (z : GLV V) (v : V) (H₁ : Subgroup (GLV V)) (m : ℕ)
    (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : Prop where
  std : StdForm G L z
  rank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1
  mem : v ∈ commSpace (Subgroup.zpowers z) ⊤
  data : CaseIData G L z v H₁ (m + 6) ψ

variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

@[expose] noncomputable def pe (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) :
    Perm (Fin (m + 6 + 2)) →* GLV V :=
  H₁.subtype.comp ψ.symm.toMonoidHom

theorem pe_apply (σ : Perm (Fin (m + 6 + 2))) : pe ψ σ = ((ψ.symm σ : ↥H₁) : GLV V) := rfl

theorem pe_injective : Function.Injective (pe ψ) := fun σ τ h =>
  ψ.symm.injective (Subtype.ext h)

theorem pe_mem (σ : Perm (Fin (m + 6 + 2))) : pe ψ σ ∈ H₁ := (ψ.symm σ).2

theorem pe_psi (x : ↥H₁) : pe ψ (ψ x) = x := by
  rw [pe_apply, MulEquiv.symm_apply_apply]

theorem psi_pe (σ : Perm (Fin (m + 6 + 2))) : ψ ⟨pe ψ σ, pe_mem σ⟩ = σ := by
  have : (⟨pe ψ σ, pe_mem σ⟩ : ↥H₁) = ψ.symm σ := rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem mem_H₁_iff {x : GLV V} : x ∈ H₁ ↔ ∃ σ, pe ψ σ = x :=
  ⟨fun hx => ⟨ψ ⟨x, hx⟩, pe_psi ⟨x, hx⟩⟩, by rintro ⟨σ, rfl⟩; exact pe_mem σ⟩

abbrev HH (G L : Subgroup (GLV V)) (v : V) : Subgroup (GLV V) :=
  normalClosure (layerIn (G ⊓ vFix v)) L

abbrev KK (G L : Subgroup (GLV V)) : Subgroup (GLV V) :=
  G ⊓ Subgroup.centralizer (L : Set (GLV V))

abbrev NN (G L : Subgroup (GLV V)) : Subgroup (GLV V) :=
  G ⊓ Subgroup.normalizer (L : Set (GLV V))

theorem Hyp.z_mem_H₁ (h : Hyp G L z v H₁ m ψ) : z ∈ H₁ := h.data.z_mem

theorem Hyp.z_eq (h : Hyp G L z v H₁ m ψ) : z = pe ψ (swap 0 1) := by
  rw [← h.data.ψ_z, pe_psi]

theorem Hyp.H₁_le (h : Hyp G L z v H₁ m ψ) : H₁ ≤ G ⊓ vFix v := h.data.le

theorem Hyp.H₁_le_G (h : Hyp G L z v H₁ m ψ) : H₁ ≤ G := h.H₁_le.trans inf_le_left

theorem Hyp.L_le_H₁ (h : Hyp G L z v H₁ m ψ) : L ≤ H₁ := h.data.L_le

theorem Hyp.L_eq (h : Hyp G L z v H₁ m ψ) :
    L = (altOn {i : Fin (m + 6 + 2) | i ≠ 0 ∧ i ≠ 1}).map (pe ψ) := by
  rw [← h.data.ψ_L]
  ext x
  constructor
  · intro hx
    refine ⟨ψ ⟨x, h.L_le_H₁ hx⟩, ⟨⟨x, h.L_le_H₁ hx⟩, hx, rfl⟩, pe_psi _⟩
  · rintro ⟨σ, ⟨y, hy, rfl⟩, rfl⟩
    rw [show pe ψ (ψ.toMonoidHom y) = y from pe_psi y]
    exact hy

theorem Hyp.mem_L_iff (h : Hyp G L z v H₁ m ψ) (σ : Perm (Fin (m + 6 + 2))) :
    pe ψ σ ∈ L ↔ σ ∈ altOn {i : Fin (m + 6 + 2) | i ≠ 0 ∧ i ≠ 1} := by
  rw [h.L_eq]
  exact ⟨fun ⟨τ, hτ, e⟩ => pe_injective e ▸ hτ, fun hσ => ⟨σ, hσ, rfl⟩⟩

theorem Hyp.H_eq (h : Hyp G L z v H₁ m ψ) :
    HH G L v = (alternatingGroup (Fin (m + 6 + 2))).map (pe ψ) := by
  show normalClosure (layerIn (G ⊓ vFix v)) L = _
  rw [← h.data.ψ_H]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, hy, pe_psi y⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨ψ.symm σ, ?_, rfl⟩
    show ψ (ψ.symm σ) ∈ alternatingGroup (Fin (m + 6 + 2))
    rw [MulEquiv.apply_symm_apply]
    exact hσ

theorem Hyp.mem_H_iff (h : Hyp G L z v H₁ m ψ) (σ : Perm (Fin (m + 6 + 2))) :
    pe ψ σ ∈ HH G L v ↔ σ ∈ alternatingGroup (Fin (m + 6 + 2)) := by
  rw [h.H_eq]
  exact ⟨fun ⟨τ, hτ, e⟩ => pe_injective e ▸ hτ, fun hσ => ⟨σ, hσ, rfl⟩⟩

theorem Hyp.H_le_H₁ (h : Hyp G L z v H₁ m ψ) : HH G L v ≤ H₁ := by
  rw [h.H_eq]
  rintro _ ⟨σ, -, rfl⟩
  exact pe_mem σ

theorem Hyp.L_le_H (h : Hyp G L z v H₁ m ψ) : L ≤ HH G L v := by
  intro x hx
  have hx' := hx
  rw [h.L_eq] at hx'
  obtain ⟨σ, hσ, rfl⟩ := hx'
  exact (h.mem_H_iff σ).2 (mem_altOn_iff.1 hσ).1

theorem Hyp.H_le_G (h : Hyp G L z v H₁ m ψ) : HH G L v ≤ G := h.H_le_H₁.trans h.H₁_le_G

theorem Hyp.H_isComponentOf (h : Hyp G L z v H₁ m ψ) :
    IsComponentOf (HH G L v) (G ⊓ vFix v) := h.data.component

theorem Hyp.fix_v (h : Hyp G L z v H₁ m ψ) {x : GLV V} (hx : x ∈ H₁) : x v = v :=
  (h.H₁_le hx).2

theorem ne01 : (0 : Fin (m + 6 + 2)) ≠ 1 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by decide)
theorem ne02 : (0 : Fin (m + 6 + 2)) ≠ 2 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 2 by decide)
theorem ne03 : (0 : Fin (m + 6 + 2)) ≠ 3 := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 3 by decide)
theorem ne12 : (1 : Fin (m + 6 + 2)) ≠ 2 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 2 by decide)
theorem ne13 : (1 : Fin (m + 6 + 2)) ≠ 3 := Fin.ne_of_val_ne (show (1 : ℕ) ≠ 3 by decide)
theorem ne23 : (2 : Fin (m + 6 + 2)) ≠ 3 := Fin.ne_of_val_ne (show (2 : ℕ) ≠ 3 by decide)

@[expose] def tau : Perm (Fin (m + 6 + 2)) := swap 0 2 * swap 1 3

theorem tau_apply_zero : (tau : Perm (Fin (m + 6 + 2))) 0 = 2 := by
  rw [tau, Perm.mul_apply, swap_apply_of_ne_of_ne ne01 ne03, swap_apply_left]

theorem tau_apply_one : (tau : Perm (Fin (m + 6 + 2))) 1 = 3 := by
  rw [tau, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne ne03.symm ne23.symm]

theorem tau_apply_two : (tau : Perm (Fin (m + 6 + 2))) 2 = 0 := by
  rw [tau, Perm.mul_apply, swap_apply_of_ne_of_ne ne12.symm ne23, swap_apply_right]

theorem tau_apply_three : (tau : Perm (Fin (m + 6 + 2))) 3 = 1 := by
  rw [tau, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne ne01.symm ne12]

theorem tau_inv : (tau : Perm (Fin (m + 6 + 2)))⁻¹ = tau := by
  rw [tau, mul_inv_rev, swap_inv, swap_inv]
  exact (Equiv.Perm.Disjoint.commute (by
    intro x
    by_cases h0 : x = 0
    · right; rw [h0]; exact swap_apply_of_ne_of_ne ne01 ne03
    by_cases h2 : x = 2
    · right; rw [h2]; exact swap_apply_of_ne_of_ne ne12.symm ne23
    · left; exact swap_apply_of_ne_of_ne h0 h2)).eq.symm

theorem tau_mem_alt : (tau : Perm (Fin (m + 6 + 2))) ∈ alternatingGroup (Fin (m + 6 + 2)) := by
  rw [Equiv.Perm.mem_alternatingGroup, tau, map_mul, sign_swap ne02, sign_swap ne13]
  rfl

theorem tau_swap01 : tau * swap (0 : Fin (m + 6 + 2)) 1 * tau⁻¹ = swap 2 3 := by
  rw [← Equiv.swap_apply_apply, tau_apply_zero, tau_apply_one]

@[expose] noncomputable def gg (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : GLV V := pe ψ tau

@[expose] noncomputable def yy (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : GLV V :=
  pe ψ (swap 2 3)

theorem Hyp.yy_eq (h : Hyp G L z v H₁ m ψ) : yy ψ = gg ψ * z * (gg ψ)⁻¹ := by
  rw [h.z_eq, gg, yy, ← map_inv, ← map_mul, ← map_mul, tau_swap01]

theorem Hyp.gg_mem_H (h : Hyp G L z v H₁ m ψ) : gg ψ ∈ HH G L v :=
  (h.mem_H_iff tau).2 tau_mem_alt

theorem Hyp.gg_mem_G (h : Hyp G L z v H₁ m ψ) : gg ψ ∈ G := h.H_le_G h.gg_mem_H

theorem Hyp.conj_L_eq (h : Hyp G L z v H₁ m ψ) :
    L.map (MulAut.conj (gg ψ)).toMonoidHom =
      (altOn {i : Fin (m + 6 + 2) | i ≠ 2 ∧ i ≠ 3}).map (pe ψ) := by
  rw [h.L_eq, Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨tau * σ * tau⁻¹, ?_, ?_⟩
    · rw [mem_altOn_iff] at hσ ⊢
      refine ⟨(alternatingGroup _).mul_mem ((alternatingGroup _).mul_mem tau_mem_alt hσ.1)
        ((alternatingGroup _).inv_mem tau_mem_alt), fun i hi => ?_⟩
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hi
      rw [tau_inv]
      rcases hi with rfl | rfl
      · rw [Perm.mul_apply, Perm.mul_apply, tau_apply_two, hσ.2 0 (by simp), tau_apply_zero]
      · rw [Perm.mul_apply, Perm.mul_apply, tau_apply_three, hσ.2 1 (by simp), tau_apply_one]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, gg, map_mul, map_inv]
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨tau⁻¹ * σ * tau, ?_, ?_⟩
    · rw [mem_altOn_iff] at hσ ⊢
      refine ⟨(alternatingGroup _).mul_mem ((alternatingGroup _).mul_mem
        ((alternatingGroup _).inv_mem tau_mem_alt) hσ.1) tau_mem_alt, fun i hi => ?_⟩
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hi
      rw [tau_inv]
      rcases hi with rfl | rfl
      · rw [Perm.mul_apply, Perm.mul_apply, tau_apply_zero, hσ.2 2 (by simp), tau_apply_two]
      · rw [Perm.mul_apply, Perm.mul_apply, tau_apply_one, hσ.2 3 (by simp), tau_apply_three]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, gg, map_mul, map_inv]
      group

theorem add_self_eq_zero' (a : V) : a + a = 0 := by
  have h : (2 : ZMod 2) • a = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rwa [two_smul] at h

theorem neg_eq_self' (a : V) : -a = a := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero']

theorem sub_eq_add' (a b : V) : a - b = a + b := by rw [sub_eq_add_neg, neg_eq_self']

theorem eq_one_or_eq_of_mem_zpowers {Γ : Type*} [Group Γ] {g k : Γ} (hg : orderOf g = 2)
    (hk : k ∈ Subgroup.zpowers g) : k = 1 ∨ k = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : (orderOf g : ℤ) = 2 := by rw [hg]; rfl
  have h : g ^ n = g ^ (n % 2) := by rw [← h2, zpow_mod_orderOf]
  rw [h]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h0
  · left; rw [h0, zpow_zero]
  · right; rw [h0, zpow_one]

theorem mul_self_of_orderOf_two {Γ : Type*} [Group Γ] {g : Γ} (hg : orderOf g = 2) :
    g * g = 1 := by
  have := pow_orderOf_eq_one g
  rw [hg, sq] at this
  exact this

theorem fix_commSpace_of_involution {t : GLV V} (ht : orderOf t = 2) {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers t) ⊤) : t w = w := by
  have htt : ∀ u : V, t (t u) = u := fun u => by
    have := congrArg (fun f : GLV V => f u) (mul_self_of_orderOf_two ht)
    simpa using this
  have hle : commSpace (Subgroup.zpowers t) ⊤ ≤
      LinearMap.eqLocus (t : V →ₗ[ZMod 2] V) LinearMap.id := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    rw [LinearMap.mem_eqLocus]
    rcases eq_one_or_eq_of_mem_zpowers ht hk with hk1 | hkt
    · subst hk1; simp
    · subst hkt
      show k (k u - u) = k u - u
      rw [map_sub, htt, sub_eq_add', sub_eq_add', add_comm]
  exact hle hw

theorem mem_commSpace_conj {t g : GLV V} {w : V} (hw : w ∈ commSpace (Subgroup.zpowers t) ⊤) :
    g w ∈ commSpace (Subgroup.zpowers (g * t * g⁻¹)) ⊤ := by
  have hle : commSpace (Subgroup.zpowers t) ⊤ ≤
      (commSpace (Subgroup.zpowers (g * t * g⁻¹)) ⊤).comap (g : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    show g ((t ^ i) u - u) ∈ commSpace (Subgroup.zpowers (g * t * g⁻¹)) ⊤
    have e : g ((t ^ i) u - u) = ((g * t * g⁻¹) ^ i) (g u) - g u := by
      rw [conj_zpow]; simp [mul_assoc]
    rw [e]
    exact sub_mem_commSpace (Subgroup.zpow_mem_zpowers _ _) Submodule.mem_top
  exact hle hw

theorem mem_commSpace_conj_inv {t g : GLV V} {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers (g * t * g⁻¹)) ⊤) :
    g⁻¹ w ∈ commSpace (Subgroup.zpowers t) ⊤ := by
  have := mem_commSpace_conj (g := g⁻¹) hw
  simpa [mul_assoc] using this

noncomputable abbrev UU (z : GLV V) (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) : Submodule (ZMod 2) V :=
  commSpace (Subgroup.zpowers z) ⊤ ⊓ commSpace (Subgroup.zpowers (yy ψ)) ⊤

theorem Hyp.zz (h : Hyp G L z v H₁ m ψ) : z * z = 1 :=
  mul_self_of_orderOf_two h.std.orderOf_s

theorem Hyp.setup6 (h : Hyp G L z v H₁ m ψ) : Setup6 G (Subgroup.zpowers z) L :=
  h.std.extremal.toConf66.setup.toSetup6

theorem Hyp.L_fix_Vz (h : Hyp G L z v H₁ m ψ) {l : GLV V} (hl : l ∈ L) {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers z) ⊤) : l w = w :=
  (h.setup6.lemma61 (Subgroup.mem_zpowers z)).1 l hl w hw

theorem Hyp.fixes_U (h : Hyp G L z v H₁ m ψ) {x : GLV V} (hx : x ∈ H₁) {w : V}
    (hw : w ∈ UU z ψ) : x w = w := by
  let S : Subgroup (Perm (Fin (m + 6 + 2))) := (centralizerOn ⊤ (UU z ψ)).comap (pe ψ)
  have hA : altOn {i : Fin (m + 6 + 2) | i ≠ 0 ∧ i ≠ 1} ≤ S := fun σ hσ =>
    ⟨Subgroup.mem_top _, fun u hu => h.L_fix_Vz ((h.mem_L_iff σ).2 hσ) hu.1⟩
  have hB : altOn {i : Fin (m + 6 + 2) | i ≠ 2 ∧ i ≠ 3} ≤ S := by
    intro σ hσ
    refine ⟨Subgroup.mem_top _, fun u hu => ?_⟩
    have hmem : pe ψ σ ∈ L.map (MulAut.conj (gg ψ)).toMonoidHom := by
      rw [h.conj_L_eq]; exact ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl, hle⟩ := hmem
    rw [← hle]
    have hu' : u ∈ commSpace (Subgroup.zpowers (gg ψ * z * (gg ψ)⁻¹)) ⊤ := by
      rw [← h.yy_eq]; exact hu.2
    have h1 := h.L_fix_Vz hl (mem_commSpace_conj_inv hu')
    show gg ψ (l ((gg ψ)⁻¹ u)) = u
    rw [h1]
    exact (gg ψ).apply_symm_apply u
  have hz : swap (0 : Fin (m + 6 + 2)) 1 ∈ S := by
    refine ⟨Subgroup.mem_top _, fun u hu => ?_⟩
    rw [← h.z_eq]
    exact fix_commSpace_of_involution h.std.orderOf_s hu.1
  have hAlt : alternatingGroup (Fin (m + 6 + 2)) ≤ S :=
    (alternatingGroup_le_sup_altOn (by omega) ne01 ne02 ne03 ne12 ne13 ne23).trans (sup_le hA hB)
  obtain ⟨σ, rfl⟩ := (mem_H₁_iff (ψ := ψ)).1 hx
  have hσ : σ ∈ S := by
    by_cases hσA : σ ∈ alternatingGroup (Fin (m + 6 + 2))
    · exact hAlt hσA
    · have h1 : σ * swap 0 1 ∈ alternatingGroup (Fin (m + 6 + 2)) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap ne01]
        rw [Equiv.Perm.mem_alternatingGroup] at hσA
        rcases Int.units_eq_one_or (sign σ) with h' | h'
        · exact absurd h' hσA
        · rw [h']; rfl
      have := S.mul_mem (hAlt h1) hz
      rwa [mul_assoc, swap_mul_self, mul_one] at this
  exact hσ.2 w hw

theorem Hyp.v_mem_U (h : Hyp G L z v H₁ m ψ) : v ∈ UU z ψ := by
  refine ⟨h.mem, ?_⟩
  have hg : gg ψ v = v := h.fix_v (pe_mem _)
  have := mem_commSpace_conj (g := gg ψ) h.mem
  rw [hg, ← h.yy_eq] at this
  exact this

end CaseIAux

end CFSG.CGT.Foote82

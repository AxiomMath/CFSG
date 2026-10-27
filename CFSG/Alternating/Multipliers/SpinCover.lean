module

public import CFSG.Alternating.Multipliers.Spin
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.RankThree.PerfectCover.HopfCover

public noncomputable section

namespace CFSG.Alternating.Multipliers.Spin

open Equiv Equiv.Perm Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {n : ℕ}

theorem mul_r (g : monomial n) (e f : Fin n) :
    ((g : (Cl n)ˣ) : Cl n) * r e f = r (perm g e) (perm g f) * (g : (Cl n)ˣ) := by
  rw [r, r, mul_sub, sub_mul, perm_spec, perm_spec]

theorem commutator_dd {p q s t : Fin n} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s)
    (hqt : q ≠ t) (hst : s ≠ t) : ⁅dd hpq hst, dd hps hqt⁆ = negOne := by
  set x := dd hpq hst
  set y := dd hps hqt
  have hx : perm x = swap p q * swap s t := perm_dd hpq hst
  have ep : perm x p = q := by
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne hps hpt, swap_apply_left]
  have es : perm x s = t := by
    rw [hx, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hpt) (Ne.symm hqt)]
  have eq : perm x q = p := by
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne hqs hqt, swap_apply_right]
  have et : perm x t = s := by
    rw [hx, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hps) (Ne.symm hqs)]
  have key : x * y = negOne * (y * x) := by
    apply Subtype.ext
    apply Units.ext
    set X : Cl n := ((x : (Cl n)ˣ) : Cl n) with hX
    change X * (half * r p s * r q t) = -1 * ((half * r p s * r q t) * X)
    have hxh : X * half = half * X := (half_comm _).symm
    have m1 : X * r p s = r q t * X := by rw [hX, mul_r, ep, es]
    have m2 : X * r q t = r p s * X := by rw [hX, mul_r, eq, et]
    calc X * (half * r p s * r q t) = half * (X * r p s) * r q t := by
          rw [← mul_assoc, ← mul_assoc, hxh, mul_assoc half]
      _ = half * r q t * (X * r q t) := by
          rw [m1, ← mul_assoc half, mul_assoc (half * r q t)]
      _ = half * (r q t * r p s) * X := by
          rw [m2, ← mul_assoc, mul_assoc half]
      _ = -1 * ((half * r p s * r q t) * X) := by
          rw [r_mul_r (Ne.symm hpq) hqs (Ne.symm hpt) (Ne.symm hst)]
          simp only [mul_neg, neg_mul, one_mul, mul_assoc]
  rw [commutatorElement_def, key]
  group

variable (n) in
@[expose] def ddSet : Set (monomial n) :=
  {g | ∃ (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d), dd hab hcd = g}

variable (n) in
abbrev H : Subgroup (monomial n) := closure (ddSet n)

theorem commute_dd_of_perm_eq_one {g : monomial n} (hg : perm g = 1) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) : dd hab hcd * g = g * dd hab hcd := by
  have hv := commute_v_of_perm_eq_one hg
  have hr : ∀ e f, Commute ((g : (Cl n)ˣ) : Cl n) (r e f) := fun e f =>
    (hv e).sub_right (hv f)
  have hh : Commute ((g : (Cl n)ˣ) : Cl n) half := (half_comm _).symm
  have hc : Commute ((g : (Cl n)ˣ) : Cl n) (half * r a b * r c d) :=
    (hh.mul_right (hr a b)).mul_right (hr c d)
  exact Subtype.ext (Units.ext hc.symm.eq)

theorem H_le_centralizer {g : monomial n} (hg : perm g = 1) :
    H n ≤ centralizer ({g} : Set (monomial n)) := by
  rw [closure_le]
  rintro _ ⟨a, b, c, d, hab, hcd, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (commute_dd_of_perm_eq_one hg hab hcd)

abbrev permH : H n →* Perm (Fin n) := perm.comp (H n).subtype

theorem ker_permH_le_center : (permH (n := n)).ker ≤ center (H n) := by
  intro g hg
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (H_le_centralizer hg h.2))

theorem range_permH {m : ℕ} : (permH (n := m + 2)).range = alternatingGroup (Fin (m + 2)) := by
  rw [MonoidHom.range_comp, range_subtype, H, MonoidHom.map_closure]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨_, ⟨a, b, c, d, hab, hcd, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, perm_dd]
    exact swap_mul_swap_mem_alternatingGroup hab hcd
  · rw [← closure_altThreeCyclePerm]
    refine closure_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨dd (addNat_two_ne_zero i).symm zero_ne_one_fin, ⟨_, _, _, _, _, _, rfl⟩, perm_dd _ _⟩

theorem commutator_alternatingGroup_self {α : Type*} [Fintype α] [DecidableEq α]
    (h5 : 5 ≤ Nat.card α) :
    ⁅alternatingGroup α, alternatingGroup α⁆ = alternatingGroup α := by
  have h := congrArg (Subgroup.map (alternatingGroup α).subtype)
    (commutator_alternatingGroup_eq_top h5)
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h

variable (n) in
abbrev E : Subgroup (H n) := commutator (H n)

theorem map_permH_E {m : ℕ} (hm : 3 ≤ m) :
    (E (m + 2)).map permH = alternatingGroup (Fin (m + 2)) := by
  rw [E, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_permH]
  exact commutator_alternatingGroup_self (by simp; omega)

theorem E_isPerfect {m : ℕ} (hm : 3 ≤ m) : Group.IsPerfect (E (m + 2)) := by
  have hsup : E (m + 2) ⊔ (permH (n := m + 2)).ker = ⊤ := by
    rw [eq_top_iff]
    intro h _
    have hh : permH h ∈ (E (m + 2)).map permH := by
      rw [map_permH_E hm, ← range_permH]
      exact ⟨h, rfl⟩
    obtain ⟨e, he, hee⟩ := hh
    have hk : e⁻¹ * h ∈ (permH (n := m + 2)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hee, inv_mul_cancel]
    rw [show h = e * (e⁻¹ * h) by group]
    exact mul_mem_sup he hk
  have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central (E (m + 2))
    (permH (n := m + 2)).ker ker_permH_le_center
  rw [hsup, ← _root_.commutator_def] at h
  rw [Group.isPerfect_def]
  apply map_injective (E (m + 2)).subtype_injective
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact h.symm

@[expose] def psi {m : ℕ} : E (m + 2) →* alternatingGroup (Fin (m + 2)) :=
  ((permH (n := m + 2)).comp (E (m + 2)).subtype).codRestrict _ fun x => by
    rw [← range_permH]
    exact ⟨x, rfl⟩

theorem psi_surjective {m : ℕ} (hm : 3 ≤ m) : Function.Surjective (psi (m := m)) := by
  rintro ⟨σ, hσ⟩
  rw [← map_permH_E hm] at hσ
  obtain ⟨e, he, rfl⟩ := hσ
  exact ⟨⟨e, he⟩, rfl⟩

theorem ker_psi_le_center {m : ℕ} : (psi (m := m)).ker ≤ center (E (m + 2)) := by
  intro x hx
  have hx' : (x : H (m + 2)) ∈ (permH (n := m + 2)).ker := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact this
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.mp (ker_permH_le_center hx') y)

theorem ker_psi_ne_bot {m : ℕ} (hm : 2 ≤ m) : (psi (m := m)).ker ≠ ⊥ := by
  set p₀ : Fin (m + 2) := ⟨0, by omega⟩
  set p₁ : Fin (m + 2) := ⟨1, by omega⟩
  set p₂ : Fin (m + 2) := ⟨2, by omega⟩
  set p₃ : Fin (m + 2) := ⟨3, by omega⟩
  have h01 : p₀ ≠ p₁ := by simp [p₀, p₁]
  have h02 : p₀ ≠ p₂ := by simp [p₀, p₂, Fin.ext_iff]
  have h03 : p₀ ≠ p₃ := by simp [p₀, p₃, Fin.ext_iff]
  have h12 : p₁ ≠ p₂ := by simp [p₁, p₂, Fin.ext_iff]
  have h13 : p₁ ≠ p₃ := by simp [p₁, p₃, Fin.ext_iff]
  have h23 : p₂ ≠ p₃ := by simp [p₂, p₃, Fin.ext_iff]
  set x : H (m + 2) := ⟨dd h01 h23, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set y : H (m + 2) := ⟨dd h02 h13, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set w : E (m + 2) := ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩
  have hw : ((w : H (m + 2)) : monomial (m + 2)) = negOne :=
    commutator_dd h01 h02 h03 h12 h13 h23
  intro hbot
  have hker : w ∈ (psi (m := m)).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change perm ((w : H (m + 2)) : monomial (m + 2)) = 1
    rw [hw, perm_negOne]
  rw [hbot, mem_bot] at hker
  exact negOne_ne_one (by rw [← hw, hker]; rfl)

theorem exists_perfect_central_extension {m : ℕ} (hm : 3 ≤ m) :
    ∃ (E : Type) (_ : Group E) (ψ : E →* alternatingGroup (Fin (m + 2))),
      Group.IsPerfect E ∧ Function.Surjective ψ ∧ ψ.ker ≤ center E ∧ ψ.ker ≠ ⊥ :=
  ⟨E (m + 2), inferInstance, psi, E_isPerfect hm, psi_surjective hm, ker_psi_le_center,
    ker_psi_ne_bot (by omega)⟩

theorem hopfMultiplier_ne_bot {n : ℕ} (hn : 5 ≤ n) :
    RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin n)) ≠ ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨E, _, ψ, hE, hψ, hK, hne⟩ := exists_perfect_central_extension (by omega : 3 ≤ m)
  intro hM
  have := RankThree.PerfectCover.map_hopfMultiplier_hopfLift ψ hψ hK
  rw [hM, Subgroup.map_bot] at this
  exact hne this.symm

end CFSG.Alternating.Multipliers.Spin

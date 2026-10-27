module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinQuotient

public section

namespace CFSG.SeitzReduction.RankOne.Finkelstein

open CFSG.ComponentClassification.GMS78.Finkelstein

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U}

omit [Finite U] in
theorem psi_map_of_comm {s : MulAut U} (hs : t * s = s * t) (u : U) :
    psi t (s u) = s (psi t u) := by
  have h1 : t (s u) = s (t u) := by rw [← MulAut.mul_apply, hs, MulAut.mul_apply]
  rw [psi, psi, map_mul, map_inv, h1]

@[expose] def restrictAut (s : MulAut U) (H : Subgroup U) (hs : H.map (s : U →* U) = H) :
    MulAut H :=
  (s.subgroupMap H).trans (MulEquiv.subgroupCongr hs)

omit [Finite U] in
theorem coe_restrictAut (s : MulAut U) (H : Subgroup U) (hs : H.map (s : U →* U) = H) (x : H) :
    ((restrictAut s H hs x : H) : U) = s x :=
  rfl

omit [Finite U] in
theorem coe_restrictAut_pow (s : MulAut U) (H : Subgroup U) (hs : H.map (s : U →* U) = H)
    (k : ℕ) (x : H) : (((restrictAut s H hs ^ k) x : H) : U) = (s ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, coe_restrictAut, ih, pow_succ', MulAut.mul_apply]

namespace Hyp

variable (h : Hyp U n t y)
include h

@[expose] def bSub : Subgroup U where
  carrier := {u | psi t u ∈ fixSubgroup t}
  mul_mem' := fun {u v} hu hv => by
    show psi t (u * v) ∈ fixSubgroup t
    rw [h.psi_mul_of_mem hu]
    exact mul_mem hu hv
  one_mem' := by
    show psi t 1 ∈ fixSubgroup t
    rw [psi_eq_one_iff.mpr (one_mem _)]
    exact one_mem _
  inv_mem' := fun {u} hu => by
    show psi t u⁻¹ ∈ fixSubgroup t
    rw [h.psi_inv_of_mem hu]
    exact inv_mem hu

theorem mem_bSub {u : U} : u ∈ h.bSub ↔ psi t u ∈ fixSubgroup t :=
  Iff.rfl

theorem fix_le_bSub : fixSubgroup t ≤ h.bSub := fun a ha => by
  rw [mem_bSub, psi_eq_one_iff.mpr ha]
  exact one_mem _

theorem map_bSub_of_comm {s : MulAut U} (hs : t * s = s * t) :
    h.bSub.map (s : U →* U) = h.bSub := by
  have hle : h.bSub.map (s : U →* U) ≤ h.bSub := by
    rintro _ ⟨u, hu, rfl⟩
    show psi t (s u) ∈ fixSubgroup t
    rw [psi_map_of_comm hs]
    have h1 : (fixSubgroup t).map (s : U →* U) ≤ fixSubgroup t := (map_fix_of_comm hs).le
    exact h1 ⟨_, hu, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective s.injective])

@[expose] def psiB : h.bSub →* fixSubgroup t where
  toFun u := ⟨psi t u, u.2⟩
  map_one' := Subtype.ext (psi_eq_one_iff.mpr (one_mem _))
  map_mul' u v := Subtype.ext (h.psi_mul_of_mem u.2 v)

theorem psiB_surjective (hA : fixSubgroup t ≠ ⊤) : Function.Surjective h.psiB := by
  have := h.fix_normal
  obtain ⟨u₀, hu₀A, hu₀⟩ := h.exists_not_mem_psi_mem (N := fixSubgroup t)
    (fun x hx => by rw [mem_fixSubgroup, h.t_t]; exact hx.symm) hA
  have hu₀1 : psi t u₀ ≠ 1 := fun h1 => hu₀A (psi_eq_one_iff.mp h1)
  rintro ⟨a, ha⟩
  by_cases ha1 : a = 1
  · exact ⟨1, Subtype.ext (by rw [map_one]; exact ha1.symm)⟩
  obtain ⟨k, hk⟩ := h.exists_pow_eq hu₀ ha hu₀1 ha1
  have hmem : (y ^ k) u₀ ∈ h.bSub := by
    rw [mem_bSub, h.psi_pow_y]
    exact h.pow_mem_fix k hu₀
  exact ⟨⟨_, hmem⟩, Subtype.ext ((h.psi_pow_y k u₀).trans hk)⟩

theorem natCard_bSub (hA : fixSubgroup t ≠ ⊤) : Nat.card h.bSub = 2 ^ (2 * n) := by
  have hker : Nat.card h.psiB.ker = Nat.card (fixSubgroup t) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨((u : h.bSub) : U), psi_eq_one_iff.mp (congrArg Subtype.val u.2)⟩
        invFun := fun a => ⟨⟨a, h.fix_le_bSub a.2⟩, Subtype.ext (psi_eq_one_iff.mpr a.2)⟩
        left_inv := fun u => rfl
        right_inv := fun a => rfl }
  have h1 := Subgroup.card_ker_mul_card_of_surjective (h.psiB_surjective hA)
  rw [hker, h.natCard_fix, ← pow_add, ← two_mul] at h1
  exact h1.symm

theorem finkHyp_bSub (hA : fixSubgroup t ≠ ⊤) :
    FinkHyp h.bSub n (restrictAut t h.bSub (h.map_bSub_of_comm rfl))
      (restrictAut y h.bSub (h.map_bSub_of_comm h.comm)) := by
  set tB := restrictAut t h.bSub (h.map_bSub_of_comm rfl) with htB
  set yB := restrictAut y h.bSub (h.map_bSub_of_comm h.comm) with hyB
  have hpow : ∀ (k : ℕ) (x : h.bSub), (((yB ^ k) x : h.bSub) : U) = (y ^ k) x :=
    fun k x => coe_restrictAut_pow _ _ _ k x
  have hpos : 0 < 2 ^ n - 1 := by have := h.three_le; omega
  refine ⟨by have := h.two_le; omega, h.natCard_bSub hA, ?_, ?_, ?_, ?_⟩
  · ext x
    show t (t x) = x
    exact h.t_t x
  · ext x
    show t (y x) = y (t x)
    exact h.t_y x
  · rw [orderOf_eq_iff hpos]
    refine ⟨?_, fun k hk hk0 hyk => ?_⟩
    · ext x
      rw [hpow, ← h.order, pow_orderOf_eq_one, MulAut.one_apply, MulAut.one_apply]
    · obtain ⟨a₀, ha₀, ha₀1⟩ := h.exists_fix_ne_one
      have h1 : (y ^ k) a₀ = a₀ := by
        have h2 := hpow k ⟨a₀, h.fix_le_bSub ha₀⟩
        rw [hyk, MulAut.one_apply] at h2
        exact h2.symm
      have h3 := h.pow_eq_one_of_fix ha₀ ha₀1 h1
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [h.order] at h4
      exact absurd (Nat.le_of_dvd hk0 h4) (by omega)
  · intro a b ha hb ha1 hb1
    have ha' : t (a : U) = a := congrArg Subtype.val ha
    have hb' : t (b : U) = b := congrArg Subtype.val hb
    have ha1' : (a : U) ≠ 1 := fun e => ha1 (Subtype.ext e)
    have hb1' : (b : U) ≠ 1 := fun e => hb1 (Subtype.ext e)
    obtain ⟨k, ⟨hk, hkab⟩, hu⟩ := h.reg _ _ ha' hb' ha1' hb1'
    refine ⟨k, ⟨hk, Subtype.ext ((hpow k a).trans hkab)⟩, fun k' ⟨hk', hk'ab⟩ => ?_⟩
    exact hu k' ⟨hk', (hpow k' a).symm.trans (congrArg Subtype.val hk'ab)⟩

theorem bSub_comm (hA : fixSubgroup t ≠ ⊤) {a b : U} (ha : a ∈ h.bSub) (hb : b ∈ h.bSub) :
    a * b = b * a :=
  congrArg Subtype.val ((h.finkHyp_bSub hA).mul_comm' ⟨a, ha⟩ ⟨b, hb⟩)

theorem le_natCard_of_not_comm (hnc : ∃ a b : U, a * b ≠ b * a) : 2 ^ (3 * n) ≤ Nat.card U := by
  obtain ⟨m, -, hm⟩ := h.exists_natCard_eq
  obtain ⟨a, b, hab⟩ := hnc
  have hA : fixSubgroup t ≠ ⊤ := by
    intro hA
    exact hab (h.mem_center_of_mem_fix (hA ▸ Subgroup.mem_top b) a)
  have hB : h.bSub ≠ ⊤ := by
    intro hB
    exact hab (h.bSub_comm hA (hB ▸ Subgroup.mem_top a) (hB ▸ Subgroup.mem_top b))
  by_contra hlt
  have hm2 : m ≤ 2 := by
    by_contra hm3
    have h1 : 2 ^ (3 * n) ≤ 2 ^ (n * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have hle : Nat.card U ≤ Nat.card h.bSub := by
    rw [hm, h.natCard_bSub hA]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  exact hB (Subgroup.eq_top_of_le_card _ hle)

end Hyp

end CFSG.SeitzReduction.RankOne.Finkelstein

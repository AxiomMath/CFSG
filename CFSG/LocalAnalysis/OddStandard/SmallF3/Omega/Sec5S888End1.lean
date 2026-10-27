module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

structure IsPlaneData {X : Type} [Group X] (V : Subgroup X) (W : Fin 4 → Subgroup X)
    (ρ : Fin 4 → X) : Prop where
  le : ∀ i, W i ≤ V
  card_V : Nat.card V = 2 ^ 8
  card : ∀ i, Nat.card (W i) = 4
  decomp : ∀ v ∈ V, ∃ w : Fin 4 → X, (∀ i, w i ∈ W i) ∧ v = w 0 * w 1 * w 2 * w 3
  rho_mem : ∀ i, ρ i ∈ normalizer (V : Set X)
  rho_order : ∀ i, orderOf (ρ i) = 3
  rho_comm : ∀ i j, ρ i * ρ j = ρ j * ρ i
  rho_inv : ∀ i, ∀ w ∈ W i, ρ i * w * (ρ i)⁻¹ ∈ W i
  rho_triv : ∀ i j, i ≠ j → ∀ w ∈ W j, ρ i * w = w * ρ i
  rho_fpf : ∀ i, ∀ w ∈ W i, w ≠ 1 → ρ i * w * (ρ i)⁻¹ ≠ w
  trans : ∀ i j, ∃ g ∈ normalizer (V : Set X), ∀ w ∈ W i, g * w * g⁻¹ ∈ W j

private theorem s888_diff_mem {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hP : IsPlaneData V W ρ)
    (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (i : Fin 4) (w : Fin 4 → X)
    (hw : ∀ k, w k ∈ W k) :
    (ρ i * (w 0 * w 1 * w 2 * w 3) * (ρ i)⁻¹) * (w 0 * w 1 * w 2 * w 3)⁻¹ =
      (ρ i * w i * (ρ i)⁻¹) * (w i)⁻¹ := by
  letI : CommGroup V := { (inferInstance : Group V) with
    mul_comm := fun a b => Subtype.ext (hVcomm a.1 a.2 b.1 b.2) }
  let wv : Fin 4 → V := fun k => ⟨w k, hP.le k (hw k)⟩
  let q : V →* V :=
    { toFun := fun v =>
        ⟨ρ i * v.1 * (ρ i)⁻¹, (Subgroup.mem_set_normalizer_iff.mp (hP.rho_mem i) v.1).mp v.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hb : ∀ k, k ≠ i → q (wv k) = wv k := by
    intro k hk
    ext
    show ρ i * w k * (ρ i)⁻¹ = w k
    rw [hP.rho_triv i k (Ne.symm hk) (w k) (hw k), mul_assoc, mul_inv_cancel, mul_one]
  have hV : q (∏ k, wv k) * (∏ k, wv k)⁻¹ = q (wv i) * (wv i)⁻¹ := by
    rw [map_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rw [Finset.prod_eq_single i]
    · intro k _ hk
      rw [hb k hk, mul_inv_cancel]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hp : (wv 0 * wv 1 * wv 2 * wv 3) = ∏ k, wv k :=
    (Fin.prod_univ_four wv).symm
  have hV' : q (wv 0 * wv 1 * wv 2 * wv 3) * (wv 0 * wv 1 * wv 2 * wv 3)⁻¹ =
      q (wv i) * (wv i)⁻¹ := by
    rw [hp]
    exact hV
  have := congrArg (Subtype.val) hV'
  simpa [q, wv] using this

theorem plane_le_of_invariant {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hP : IsPlaneData V W ρ) (i : Fin 4) (U : Subgroup X)
    (hU : ∀ u ∈ U, ρ i * u * (ρ i)⁻¹ ∈ U) {a : X} (haW : a ∈ W i) (ha1 : a ≠ 1) (haU : a ∈ U) :
    W i ≤ U := by
  haveI : Finite (W i) := Nat.finite_of_card_ne_zero (by rw [hP.card i]; norm_num)
  haveI : Finite ↥(U ⊓ W i) := Finite.of_injective
    (Subgroup.inclusion (inf_le_right : U ⊓ W i ≤ W i)) (Subgroup.inclusion_injective _)
  let κ : MulAut X := MulAut.conj (ρ i)
  let a1 : X := κ a
  let a2 : X := κ a1
  have ha1W : a1 ∈ W i := by simpa [a1, κ, MulAut.conj_apply] using hP.rho_inv i a haW
  have hfpf : κ a ≠ a := by simpa [κ, MulAut.conj_apply] using hP.rho_fpf i a haW ha1
  have ha1ne : a1 ≠ 1 := fun h => ha1 (by have := congrArg κ.symm h; simpa [a1] using this)
  have ha1U : a1 ∈ U := by simpa [a1, κ, MulAut.conj_apply] using hU a haU
  have ha2W : a2 ∈ W i := by simpa [a2, κ, MulAut.conj_apply] using hP.rho_inv i a1 ha1W
  have ha2U : a2 ∈ U := by simpa [a2, κ, MulAut.conj_apply] using hU a1 ha1U
  have ha2ne : a2 ≠ 1 := fun h => ha1ne (by have := congrArg κ.symm h; simpa [a2] using this)
  have ha1a2 : a1 ≠ a2 := fun h =>
    hP.rho_fpf i a1 ha1W ha1ne (by simpa [a2, κ, MulAut.conj_apply] using h.symm)
  have hκ3 : κ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (ρ i)
    rw [hP.rho_order i] at h
    rw [show κ ^ 3 = MulAut.conj ((ρ i) ^ 3) from (map_pow (MulAut.conj) (ρ i) 3).symm,
      h, map_one]
  have ha2a : a2 ≠ a := fun h => hfpf (by
    calc κ a = κ ((κ ^ 2) a) := by
          rw [show (κ ^ 2) a = a by rw [pow_two, MulAut.mul_apply]; exact h]
      _ = (κ * κ ^ 2) a := by rw [MulAut.mul_apply]
      _ = (κ ^ 3) a := by rw [show κ ^ 3 = κ * κ ^ 2 from pow_succ' κ 2]
      _ = a := by rw [hκ3, MulAut.one_apply])
  have haa1 : a ≠ a1 := hfpf.symm
  have haa2 : a ≠ a2 := ha2a.symm
  let f : Fin 4 → ↥(U ⊓ W i) :=
    ![⟨1, Subgroup.mem_inf.mpr ⟨U.one_mem, (W i).one_mem⟩⟩,
      ⟨a, Subgroup.mem_inf.mpr ⟨haU, haW⟩⟩,
      ⟨a1, Subgroup.mem_inf.mpr ⟨ha1U, ha1W⟩⟩,
      ⟨a2, Subgroup.mem_inf.mpr ⟨ha2U, ha2W⟩⟩]
  have hf : Function.Injective f := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [f, Fin.cons_zero, Fin.cons_succ]
  have h4 : 4 ≤ Nat.card ↥(U ⊓ W i) := by
    simpa using Nat.card_le_card_of_injective f hf
  exact (Subgroup.eq_of_le_of_card_ge inf_le_right
    (by rw [hP.card i]; exact h4)) ▸ inf_le_left

theorem irr_of_planes {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}
    {ρ : Fin 4 → X} (hP : IsPlaneData V W ρ) (hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (U : Subgroup X) (hUV : U ≤ V)
    (hUinv : ∀ g ∈ normalizer (V : Set X), ∀ u ∈ U, g⁻¹ * u * g ∈ U) : U = ⊥ ∨ U = V := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  have hex : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    exact hbot ((Subgroup.eq_bot_iff_forall U).mpr fun x hx => by_contra fun hx1 => h ⟨x, hx, hx1⟩)
  obtain ⟨u, huU, hu1⟩ := hex
  obtain ⟨w, hw, hueq⟩ := hP.decomp u (hUV huU)
  have hex_i : ∃ i : Fin 4, w i ≠ 1 := by
    by_contra h; push Not at h
    exact hu1 (by rw [hueq, h 0, h 1, h 2, h 3]; simp)
  obtain ⟨i, hwi1⟩ := hex_i
  have hUinv_rho : ∀ x ∈ U, ρ i * x * (ρ i)⁻¹ ∈ U := fun x hx =>
    (by have := hUinv (ρ i)⁻¹ ((normalizer (V : Set X)).inv_mem (hP.rho_mem i)) x hx
        simpa using this)
  have hdiffeq := s888_diff_mem hP hVcomm i w hw
  have hcW : (ρ i * u * (ρ i)⁻¹) * u⁻¹ ∈ W i := by
    rw [hueq, hdiffeq]
    exact (W i).mul_mem (hP.rho_inv i (w i) (hw i)) ((W i).inv_mem (hw i))
  have hWi : W i ≤ U := plane_le_of_invariant hP i U hUinv_rho hcW
    (by rw [hueq, hdiffeq]; intro h
        exact hP.rho_fpf i (w i) (hw i) hwi1 (mul_inv_eq_one.mp h))
    (U.mul_mem (hUinv_rho u huU) (U.inv_mem huU))
  have hall : ∀ j, W j ≤ U := by
    intro j
    obtain ⟨g, hg, hgw⟩ := hP.trans i j
    haveI : Finite (W j) := Nat.finite_of_card_ne_zero (by rw [hP.card j]; norm_num)
    have hmapeq : (W i).map (MulAut.conj g).toMonoidHom = W j := by
      refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_)
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card i, hP.card j])
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
      rw [← hxy]
      exact hgw y hy
    have hmaple : (W i).map (MulAut.conj g).toMonoidHom ≤ U := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
      rw [← hxy]
      simpa [MulAut.conj_apply] using hUinv g⁻¹ ((normalizer (V : Set X)).inv_mem hg) y (hWi hy)
    rw [← hmapeq]
    exact hmaple
  have hVU : V ≤ U := fun v hv => by
    obtain ⟨w', hw', rfl⟩ := hP.decomp v hv
    exact U.mul_mem (U.mul_mem (U.mul_mem (hall 0 (hw' 0)) (hall 1 (hw' 1)))
      (hall 2 (hw' 2))) (hall 3 (hw' 3))
  exact le_antisymm hUV hVU

end CFSG.OddStandard.SmallF3.Omega

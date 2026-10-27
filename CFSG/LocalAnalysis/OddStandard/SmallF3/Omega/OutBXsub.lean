module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem aor_perfect_le_closure_odd {P : Type} [Group P] [Finite P] (E : Subgroup P)
    (hE : Group.IsPerfect ↥E) :
    E ≤ Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)} := by
  classical
  set S : Set ↥E := {c : ↥E | Odd (orderOf c)} with hS
  set N : Subgroup ↥E := Subgroup.closure S with hN
  have hnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * y * g⁻¹))
      have h1 : orderOf (g * y * g⁻¹) = orderOf y := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) y
        simpa [MulAut.conj_apply] using this
      rw [h1]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact N.mul_mem ihx ihy
    | inv x hx ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact N.inv_mem ih
  have h2 : IsPGroup 2 (↥E ⧸ N) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨a, ?_⟩
    have hordpow : orderOf (c ^ (2 ^ a)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hcm⟩, hcm,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hmem : c ^ 2 ^ a ∈ N := Subgroup.subset_closure (by
      show Odd (orderOf (c ^ 2 ^ a))
      rw [hordpow]; exact hm)
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hperfQ : Group.IsPerfect (↥E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' N)) (QuotientGroup.mk'_surjective N)
  have hnil : Group.IsNilpotent (↥E ⧸ N) := h2.isNilpotent
  have hsub : Subsingleton (↥E ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent _ hnil
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (Subsingleton.elim _ _)
  have key : ∀ (c : ↥E), c ∈ N → (c : P) ∈ Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)} := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      refine ⟨y.2, ?_⟩
      have : orderOf (y : P) = orderOf y := Subgroup.orderOf_coe y
      rw [this]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy => simpa using Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => simpa using Subgroup.inv_mem _ ih
  intro y hy
  exact key ⟨y, hy⟩ (hNtop ▸ Subgroup.mem_top _)

theorem aor_twoRes_mono {H H' : Subgroup G} (h : H ≤ H') : twoRes H ≤ twoRes H' := by
  unfold twoRes
  exact Subgroup.closure_mono fun g hg => ⟨h hg.1, hg.2⟩

theorem aor_perfect_le_twoRes [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (hK : Group.IsPerfect K) : K ≤ twoRes H := by
  calc K ≤ Subgroup.closure {y : G | y ∈ K ∧ Odd (orderOf y)} :=
        aor_perfect_le_closure_odd K hK
    _ ≤ Subgroup.closure {y : G | y ∈ H ∧ Odd (orderOf y)} :=
        Subgroup.closure_mono fun y hy => ⟨hKH hy.1, hy.2⟩
    _ = twoRes H := rfl

theorem aor_inSubgroup_layer_le_twoRes [Finite G] (K : Subgroup G) :
    CFSG.inSubgroup CFSG.layer K ≤ twoRes K := by
  unfold CFSG.inSubgroup
  rw [CFSG.layer.eq_sSup]
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J hJ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact aor_perfect_le_twoRes (Subgroup.map_subtype_le J) (hJ.1.1.map K.subtype)

theorem asc82XSub_le_twoRes [Finite G] (L : Subgroup G) (s : G) (ε : ℤˣ) (X : Subgroup G)
    (hX : Asc82XSub L s ε X) : X ≤ twoRes (centralizer ({s} : Set G)) := by
  have hmono : twoRes (L ⊓ centralizer ({s} : Set G)) ≤ twoRes (centralizer ({s} : Set G)) :=
    aor_twoRes_mono inf_le_right
  rcases hX with rfl | ⟨-, rfl⟩
  · exact (aor_inSubgroup_layer_le_twoRes (L ⊓ centralizer ({s} : Set G))).trans hmono
  · exact (Subgroup.map_subtype_le _).trans hmono

end CFSG.OddStandard.SmallF3.Omega

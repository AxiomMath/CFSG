module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import CFSG.FeitThompson.Representations.CyclicPermutedSummandsFixedSpace

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {K R : Subgroup G}

theorem normalizer_le_normalizer_commutator_self (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer ((⁅D, D⁆ : Subgroup G) : Set G) := by
  intro g hg
  have h := (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, h]

theorem commutator_self_eq_map_commutator (D : Subgroup G) :
    (⁅D, D⁆ : Subgroup G) = (_root_.commutator ↥D).map D.subtype := by
  rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem isSolvable_commutator_self {D : Subgroup G} (hsol : Group.IsSolvable ↥D) :
    Group.IsSolvable ↥(⁅D, D⁆ : Subgroup G) :=
  have : Group.IsSolvable ↥((⁅D, D⁆).subgroupOf D) := inferInstance
  Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self D)).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self D)).surjective

theorem commutator_self_lt_of_isSolvable {D : Subgroup G} (hsol : Group.IsSolvable ↥D)
    (hne : D ≠ ⊥) : ⁅D, D⁆ < D := by
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).2 hne
  have h1 : _root_.commutator ↥D < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥D
  rw [commutator_self_eq_map_commutator D]
  calc (_root_.commutator ↥D).map D.subtype < (⊤ : Subgroup ↥D).map D.subtype :=
        (Subgroup.map_lt_map_iff_of_injective D.subtype_injective).2 h1
    _ = D := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_self_normal (hK : K.Normal) : (⁅K, K⁆ : Subgroup G).Normal :=
  have := hK
  Subgroup.commutator_normal K K

private def weightSpace (ρ : Representation k G V) (N : Subgroup G) (χ : ↥N → k) :
    Submodule k V where
  carrier := {v | ∀ y : ↥N, ρ y v = χ y • v}
  add_mem' := by
    intro a b ha hb y
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha y, hb y, smul_add]
  zero_mem' := by intro y; simp
  smul_mem' := by
    intro c v hv y
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, hv y, smul_comm]

private theorem mem_weightSpace {ρ : Representation k G V} {N : Subgroup G} {χ : ↥N → k}
    {v : V} :
    v ∈ weightSpace ρ N χ ↔ ∀ y : ↥N, ρ y v = χ y • v := Iff.rfl

private theorem weightSpace_eq_iInf (ρ : Representation k G V) (N : Subgroup G) (χ : ↥N → k) :
    weightSpace ρ N χ = ⨅ y : ↥N, Module.End.eigenspace (ρ (y : G)) (χ y) := by
  ext v
  simp [mem_weightSpace, Submodule.mem_iInf]

private theorem isSemisimple_rho [Finite G] (ρ : Representation k G V)
    (hk : (Nat.card G : k) ≠ 0) (g : G) : Module.End.IsSemisimple (ρ g) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ (Nat.card G) - Polynomial.C 1) ?_ ?_
  · exact (Polynomial.separable_X_pow_sub_C (1 : k) hk one_ne_zero).squarefree
  · rw [map_sub, Polynomial.aeval_X_pow, ← map_pow, pow_card_eq_one', map_one, Polynomial.aeval_C,
      map_one, sub_self]

private theorem isFinitelySemisimple_rho [Finite G] (ρ : Representation k G V)
    (hk : (Nat.card G : k) ≠ 0) (g : G) : Module.End.IsFinitelySemisimple (ρ g) :=
  (isSemisimple_rho ρ hk g).isFinitelySemisimple

private theorem iInf_maxGenEigenspace_eq_weightSpace [Finite G] (ρ : Representation k G V)
    (hk : (Nat.card G : k) ≠ 0) (N : Subgroup G) (χ : ↥N → k) :
    ⨅ y : ↥N, Module.End.maxGenEigenspace (ρ (y : G)) (χ y) = weightSpace ρ N χ := by
  rw [weightSpace_eq_iInf]
  exact iInf_congr fun y => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (isFinitelySemisimple_rho ρ hk (y : G)) _

private theorem iSup_weightSpace_eq_top [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) (hk : (Nat.card G : k) ≠ 0) (N : Subgroup G)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G))) :
    ⨆ χ : ↥N → k, weightSpace ρ N χ = ⊤ := by
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (f := fun y : ↥N => ρ (y : G)) (fun i j _ => hcomm i j)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  simpa only [iInf_maxGenEigenspace_eq_weightSpace ρ hk N] using h

private theorem iSupIndep_weightSpace [Finite G] (ρ : Representation k G V)
    (hk : (Nat.card G : k) ≠ 0) (N : Subgroup G)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G))) :
    iSupIndep (fun χ : ↥N → k => weightSpace ρ N χ) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (f := fun y : ↥N => ρ (y : G))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  simpa only [iInf_maxGenEigenspace_eq_weightSpace ρ hk N] using h

section WeightSpaces

variable {ρ : Representation k G V} {N : Subgroup G} {χ : ↥N → k}

private theorem map_mul_of_weightSpace_ne_bot (h : weightSpace ρ N χ ≠ ⊥) (y z : ↥N) :
    χ (y * z) = χ y * χ z := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : χ (y * z) • v = (χ y * χ z) • v := by
    rw [← hv (y * z), Subgroup.coe_mul, map_mul, Module.End.mul_apply, hv z, map_smul, hv y,
      smul_smul, mul_comm]
  have h2 : (χ (y * z) - χ y * χ z) • v = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hv0

private theorem map_one_of_weightSpace_ne_bot (h : weightSpace ρ N χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : χ (1 : ↥N) • v = v := by rw [← hv 1]; simp
  have h2 : (χ (1 : ↥N) - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact sub_eq_zero.1 h3
  · exact absurd h3 hv0

private theorem ne_zero_of_weightSpace_ne_bot (h : weightSpace ρ N χ ≠ ⊥) (y : ↥N) :
    χ y ≠ 0 := by
  intro h0
  have := map_mul_of_weightSpace_ne_bot h y y⁻¹
  rw [mul_inv_cancel, map_one_of_weightSpace_ne_bot h, h0, zero_mul] at this
  exact one_ne_zero this

private theorem injective_rho (ρ : Representation k G V) (g : G) : Function.Injective (ρ g) := by
  intro a b hab
  have h := congrArg (ρ g⁻¹) hab
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Module.End.one_apply] at h

private def conjChar (N : Subgroup G) (v : ↥(Subgroup.normalizer (N : Set G)))
    (χ : ↥N → k) : ↥N → k :=
  fun y => χ (v⁻¹ • y)

omit [Field k] in
private theorem conjChar_apply (N : Subgroup G) (v : ↥(Subgroup.normalizer (N : Set G)))
    (χ : ↥N → k) (y : ↥N) : conjChar N v χ y = χ (v⁻¹ • y) := rfl

private theorem coe_smul_normalizer (N : Subgroup G)
    (v : ↥(Subgroup.normalizer (N : Set G))) (y : ↥N) :
    ((v • y : ↥N) : G) = (v : G) * (y : G) * (v : G)⁻¹ := rfl

omit [Field k] in
private theorem conjChar_one (N : Subgroup G) (χ : ↥N → k) : conjChar N 1 χ = χ := by
  funext y; simp [conjChar]

omit [Field k] in
private theorem conjChar_mul (N : Subgroup G) (v w : ↥(Subgroup.normalizer (N : Set G)))
    (χ : ↥N → k) :
    conjChar N (v * w) χ = conjChar N v (conjChar N w χ) := by
  funext y; simp [conjChar, mul_inv_rev, mul_smul]

private theorem rho_smul_apply (ρ : Representation k G V) {N : Subgroup G}
    (v : ↥(Subgroup.normalizer (N : Set G))) (y : ↥N) (x : V) :
    ρ ((v • y : ↥N) : G) (ρ (v : G) x) = ρ (v : G) (ρ (y : G) x) := by
  have h : ((v • y : ↥N) : G) * (v : G) = (v : G) * (y : G) := by
    rw [coe_smul_normalizer]; group
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply]

private theorem mem_weightSpace_conj (ρ : Representation k G V) {N : Subgroup G}
    (v : ↥(Subgroup.normalizer (N : Set G))) (χ : ↥N → k) (x : V) :
    ρ (v : G) x ∈ weightSpace ρ N (conjChar N v χ) ↔ x ∈ weightSpace ρ N χ := by
  constructor
  · intro h y
    have h1 := h (v • y)
    rw [rho_smul_apply, conjChar_apply, inv_smul_smul] at h1
    refine injective_rho ρ (v : G) ?_
    rw [h1, map_smul]
  · intro h y
    have h1 := h (v⁻¹ • y)
    have h2 : (v • (v⁻¹ • y) : ↥N) = y := by rw [smul_inv_smul]
    have h3 := rho_smul_apply ρ v (v⁻¹ • y) x
    rw [h2, h1, map_smul] at h3
    rw [h3, conjChar_apply]

private theorem map_weightSpace (ρ : Representation k G V) {N : Subgroup G}
    (v : ↥(Subgroup.normalizer (N : Set G))) (χ : ↥N → k) :
    (weightSpace ρ N χ).map (ρ (v : G)) = weightSpace ρ N (conjChar N v χ) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_weightSpace_conj ρ v χ x).2 hx
  · intro hw
    have hid : ρ (v : G) (ρ ((v : G)⁻¹) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    refine ⟨ρ ((v : G)⁻¹) w, ?_, hid⟩
    exact (mem_weightSpace_conj ρ v χ _).1 (by rw [hid]; exact hw)

private theorem eq_one_of_conjChar_fixed {N : Subgroup G} [Finite ↥N] {χ : ↥N → k}
    (hmul : ∀ y z : ↥N, χ (y * z) = χ y * χ z) (hne : ∀ y : ↥N, χ y ≠ 0)
    (u : ↥(Subgroup.normalizer (N : Set G)))
    (hcent : N ⊓ Subgroup.centralizer {(u : G)} = ⊥)
    (hfix : conjChar N u χ = χ) (y : ↥N) : χ y = 1 := by
  have h1 : χ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h2 : χ 1 * (χ 1 - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (hne 1)
    · exact sub_eq_zero.1 h3
  have hinj : Function.Injective (fun z : ↥N => z⁻¹ * (u • z)) := by
    intro z₁ z₂ h
    simp only at h
    have key : z₂ * z₁⁻¹ * (u • z₁) = u • z₂ := by
      rw [mul_assoc, h, ← mul_assoc, mul_inv_cancel, one_mul]
    have hw : u • (z₂ * z₁⁻¹) = z₂ * z₁⁻¹ := by
      rw [smul_mul', smul_inv', ← key, mul_assoc, mul_inv_cancel, mul_one]
    have hc : (u : G) * ((z₂ * z₁⁻¹ : ↥N) : G) * (u : G)⁻¹
        = ((z₂ * z₁⁻¹ : ↥N) : G) := by
      rw [← coe_smul_normalizer, hw]
    have hmem : ((z₂ * z₁⁻¹ : ↥N) : G) ∈ N ⊓ Subgroup.centralizer {(u : G)} := by
      refine Subgroup.mem_inf.2 ⟨(z₂ * z₁⁻¹ : ↥N).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact mul_inv_eq_iff_eq_mul.1 hc
    rw [hcent] at hmem
    have hw1 : (z₂ * z₁⁻¹ : ↥N) = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 hmem)
    exact (mul_inv_eq_one.1 hw1).symm
  obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.1 hinj y
  have hzz : χ (u • z) = χ z := by
    have h := congrFun hfix (u • z)
    rw [conjChar_apply, inv_smul_smul] at h
    exact h.symm
  rw [← hz]
  change χ (z⁻¹ * (u • z)) = 1
  rw [hmul, hzz, ← hmul, inv_mul_cancel, h1]

private theorem eq_zero_of_rank_le_one {C U W : Submodule k V} [Module.Free k ↥C]
    (hrank : Module.rank k ↥C ≤ 1) (hUW : Disjoint U W) {a b : V}
    (haC : a ∈ C) (hbC : b ∈ C) (haU : a ∈ U) (hbW : b ∈ W) (ha0 : a ≠ 0) : b = 0 := by
  obtain ⟨v₀, hle⟩ := (rank_submodule_le_one_iff' C).1 hrank
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hle haC)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 (hle hbC)
  have hα0 : α ≠ 0 := by rintro rfl; exact ha0 (by simpa using hα.symm)
  have hv₀ : v₀ ∈ U := by
    have h : α⁻¹ • a ∈ U := U.smul_mem _ haU
    rwa [← hα, smul_smul, inv_mul_cancel₀ hα0, one_smul] at h
  exact Submodule.disjoint_def.1 hUW b (hβ ▸ U.smul_mem β hv₀) hbW

private theorem sum_mem_invariants (ρ : Representation k G V) (R : Subgroup G) [Fintype ↥R]
    (v : V) :
    (∑ w : ↥R, ρ (w : G) v) ∈ Representation.invariants (ρ.comp R.subtype) := by
  rw [Representation.mem_invariants]
  intro w'
  change ρ ((w' : G)) (∑ w : ↥R, ρ (w : G) v) = _
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w') _ _ ?_
  intro w
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

private def conjCharPerm (N : Subgroup G) (v : ↥(Subgroup.normalizer (N : Set G))) :
    Equiv.Perm (↥N → k) where
  toFun := conjChar N v
  invFun := conjChar N v⁻¹
  left_inv χ := by rw [← conjChar_mul, inv_mul_cancel, conjChar_one]
  right_inv χ := by rw [← conjChar_mul, mul_inv_cancel, conjChar_one]

private def conjCharPermHom (N : Subgroup G) :
    ↥(Subgroup.normalizer (N : Set G)) →* Equiv.Perm (↥N → k) where
  toFun := conjCharPerm N
  map_one' := Equiv.ext fun χ => conjChar_one N χ
  map_mul' a b := Equiv.ext fun χ => conjChar_mul N a b χ

@[instance_reducible]
private def conjCharAction (k : Type*) [Field k] {N H : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : MulAction ↥H (↥N → k) :=
  MulAction.compHom (↥N → k) ((conjCharPermHom (k := k) N).comp (Subgroup.inclusion h))

end WeightSpaces

section Core

variable {ρ : Representation k G V} {N R : Subgroup G}

private theorem conjChar_ne_self [Finite ↥N] {χ : ↥N → k}
    (hχ : weightSpace ρ N χ ≠ ⊥) {b : ↥N} (hb : χ b ≠ 1)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    {w : ↥R} (hfix : conjChar N (Subgroup.inclusion hRN w) χ = χ) : w = 1 := by
  by_contra hw
  refine hb (eq_one_of_conjChar_fixed (map_mul_of_weightSpace_ne_bot hχ)
    (ne_zero_of_weightSpace_ne_bot hχ) (Subgroup.inclusion hRN w) (hCN (w : G) w.2 ?_) hfix b)
  exact fun hcoe => hw (Subtype.ext hcoe)

private theorem injective_conjChar [Finite ↥N] {χ : ↥N → k}
    (hχ : weightSpace ρ N χ ≠ ⊥) {b : ↥N} (hb : χ b ≠ 1)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥) :
    Function.Injective (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ) := by
  intro w₁ w₂ h
  simp only at h
  have key : conjChar N (Subgroup.inclusion hRN (w₁⁻¹ * w₂)) χ = χ := by
    rw [map_mul, map_inv, conjChar_mul, ← h, ← conjChar_mul, inv_mul_cancel, conjChar_one]
  have hw := conjChar_ne_self hχ hb hRN hCN key
  exact inv_mul_eq_one.1 hw

private theorem sum_rho_apply_ne_zero [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    [Fintype ↥R] {χ : ↥N → k} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (hχ : weightSpace ρ N χ ≠ ⊥) {b : ↥N} (hb : χ b ≠ 1)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    {x : V} (hx : x ∈ weightSpace ρ N χ) (hx0 : x ≠ 0) :
    (∑ w : ↥R, ρ (w : G) x) ≠ 0 := by
  classical
  intro hsum
  have hχY : χ ∉
      (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ) '' {w : ↥R | w ≠ 1} := by
    rintro ⟨w, hw, hwe⟩
    exact hw (conjChar_ne_self hχ hb hRN hCN hwe)
  have hindep : iSupIndep (fun ψ : ↥N → k => weightSpace ρ N ψ) :=
    iSupIndep_weightSpace ρ hk N hcomm
  have hdisj := hindep.disjoint_biSup hχY
  have hrest : (∑ w ∈ Finset.univ.erase (1 : ↥R), ρ (w : G) x) ∈
      ⨆ i ∈ (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ) '' {w : ↥R | w ≠ 1},
        weightSpace ρ N i := by
    refine Submodule.sum_mem _ fun w hw => ?_
    have hwne : w ≠ 1 := Finset.ne_of_mem_erase hw
    have hmem : ρ (w : G) x ∈ weightSpace ρ N (conjChar N (Subgroup.inclusion hRN w) χ) :=
      (mem_weightSpace_conj ρ _ χ x).2 hx
    have hiY : conjChar N (Subgroup.inclusion hRN w) χ ∈
        (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ) '' {w : ↥R | w ≠ 1} :=
      ⟨w, hwne, rfl⟩
    exact le_biSup (fun i => weightSpace ρ N i) hiY hmem
  have hxe : x = -(∑ w ∈ Finset.univ.erase (1 : ↥R), ρ (w : G) x) := by
    have h := Finset.add_sum_erase Finset.univ (fun w : ↥R => ρ (w : G) x) (Finset.mem_univ 1)
    rw [hsum] at h
    have h1 : ρ ((1 : ↥R) : G) x = x := by simp
    rw [h1] at h
    exact eq_neg_of_add_eq_zero_left h
  exact hx0 (Submodule.disjoint_def.1 hdisj x hx (hxe ▸ Submodule.neg_mem _ hrest))

private theorem exists_smul_eq_of_mem_weightSpace [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    {χ : ↥N → k} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (hχ : weightSpace ρ N χ ≠ ⊥) {b : ↥N} (hb : χ b ≠ 1)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1)
    {x x' : V} (hx : x ∈ weightSpace ρ N χ) (hx' : x' ∈ weightSpace ρ N χ) (hx0 : x ≠ 0) :
    ∃ c : k, x' = c • x := by
  have : Fintype ↥R := Fintype.ofFinite _
  obtain ⟨v₀, hle⟩ := (rank_submodule_le_one_iff' _).1 hrank
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 (hle (sum_mem_invariants ρ R x))
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 (hle (sum_mem_invariants ρ R x'))
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact sum_rho_apply_ne_zero hk hcomm hχ hb hRN hCN hx hx0 (by simpa using hα.symm)
  refine ⟨β / α, ?_⟩
  by_contra hne
  have hmem : x' - (β / α) • x ∈ weightSpace ρ N χ :=
    Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ hx)
  refine sum_rho_apply_ne_zero hk hcomm hχ hb hRN hCN hmem (sub_ne_zero.2 hne) ?_
  have e1 : ∀ w : ↥R,
      ρ (w : G) (x' - (β / α) • x) = ρ (w : G) x' - (β / α) • ρ (w : G) x :=
    fun w => by rw [map_sub, map_smul]
  rw [Finset.sum_congr rfl (fun w _ => e1 w), Finset.sum_sub_distrib, ← Finset.smul_sum,
    ← hα, ← hβ, smul_smul, div_mul_cancel₀ _ hα0, sub_self]

private theorem sum_mem_biSup_range [Fintype ↥R] {χ : ↥N → k}
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) {x : V} (hx : x ∈ weightSpace ρ N χ) :
    (∑ w : ↥R, ρ (w : G) x) ∈
      ⨆ i ∈ Set.range (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ),
        weightSpace ρ N i := by
  refine Submodule.sum_mem _ fun w _ => ?_
  have hmem : ρ (w : G) x ∈ weightSpace ρ N (conjChar N (Subgroup.inclusion hRN w) χ) :=
    (mem_weightSpace_conj ρ _ χ x).2 hx
  exact le_biSup (fun i => weightSpace ρ N i) (Set.mem_range_self w) hmem

private theorem exists_conjChar_eq [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    {χ₁ χ₂ : ↥N → k} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (h1 : weightSpace ρ N χ₁ ≠ ⊥) {b₁ : ↥N} (hb₁ : χ₁ b₁ ≠ 1)
    (h2 : weightSpace ρ N χ₂ ≠ ⊥) {b₂ : ↥N} (hb₂ : χ₂ b₂ ≠ 1)
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1) :
    ∃ w : ↥R, χ₂ = conjChar N (Subgroup.inclusion hRN w) χ₁ := by
  have : Fintype ↥R := Fintype.ofFinite _
  by_contra hcon
  simp only [not_exists] at hcon
  have hdisjO : Disjoint (Set.range (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ₁))
      (Set.range (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ₂)) := by
    rw [Set.disjoint_left]
    rintro ψ ⟨w₁, rfl⟩ ⟨w₂, hw₂⟩
    refine hcon (w₂⁻¹ * w₁) ?_
    simp only at hw₂
    rw [map_mul, map_inv, conjChar_mul, ← hw₂, ← conjChar_mul, inv_mul_cancel, conjChar_one]
  obtain ⟨x₁, hx₁, hx₁0⟩ := (Submodule.ne_bot_iff _).1 h1
  obtain ⟨x₂, hx₂, hx₂0⟩ := (Submodule.ne_bot_iff _).1 h2
  have ha0 := sum_rho_apply_ne_zero hk hcomm h1 hb₁ hRN hCN hx₁ hx₁0
  have hb0 := sum_rho_apply_ne_zero hk hcomm h2 hb₂ hRN hCN hx₂ hx₂0
  have hindep : iSupIndep (fun ψ : ↥N → k => weightSpace ρ N ψ) :=
    iSupIndep_weightSpace ρ hk N hcomm
  exact hb0 (eq_zero_of_rank_le_one hrank (hindep.disjoint_biSup_biSup hdisjO)
    (sum_mem_invariants ρ R x₁) (sum_mem_invariants ρ R x₂)
    (sum_mem_biSup_range hRN hx₁) (sum_mem_biSup_range hRN hx₂) ha0)

private theorem not_dvd_card_of_fixedPointFree [Finite G] {D : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hRcard : Nat.card ↥R = p)
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hCD : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hR1 : R ≠ ⊥) : ¬ (p ∣ Nat.card ↥D) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hR1
  let _ : MulAction ↥R ↥D := MulAction.compHom _ (Subgroup.inclusion hRD)
  have hsmul : ∀ (w : ↥R) (z : ↥D), ((w • z : ↥D) : G) = (w : G) * (z : G) * (w : G)⁻¹ :=
    fun _ _ => rfl
  obtain ⟨v, hv1⟩ := exists_ne (1 : ↥R)
  have hpg : IsPGroup p ↥R := IsPGroup.of_card (n := 1) (by rw [hRcard, pow_one])
  have key : ∀ z : ↥(MulAction.fixedPoints ↥R ↥D), (z : ↥D) = 1 := by
    intro z
    have hz := z.2 v
    have hmem : ((z : ↥D) : G) ∈ D ⊓ Subgroup.centralizer {(v : G)} := by
      refine Subgroup.mem_inf.2 ⟨(z : ↥D).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hc := congrArg (fun t : ↥D => (t : G)) hz
      rw [hsmul] at hc
      exact mul_inv_eq_iff_eq_mul.1 hc
    rw [hCD (v : G) v.2 (fun hc => hv1 (Subtype.ext hc))] at hmem
    exact Subtype.ext (by simpa using Subgroup.mem_bot.1 hmem)
  have hfix : Nat.card ↥(MulAction.fixedPoints ↥R ↥D) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩, ⟨⟨1, fun w => ?_⟩⟩⟩
    exact Subtype.ext (by simp [hsmul])
  have hmod := hpg.card_modEq_card_fixedPoints (α := ↥D)
  rw [hfix] at hmod
  rintro ⟨c, hc⟩
  have h1 : (1 : ℕ) % p = 1 := Nat.one_mod_eq_one.2 hp.one_lt.ne'
  rw [Nat.ModEq, hc, Nat.mul_mod_right, h1] at hmod
  exact absurd hmod (by norm_num)

private theorem weightSpace_conjChar_ne_bot {χ : ↥N → k} (hχ : weightSpace ρ N χ ≠ ⊥)
    (v : ↥(Subgroup.normalizer (N : Set G))) : weightSpace ρ N (conjChar N v χ) ≠ ⊥ := by
  intro hbot
  rw [← map_weightSpace ρ v χ] at hbot
  refine hχ (le_bot_iff.1 fun x hx => (Submodule.mem_bot k).2 ?_)
  have h1 : ρ (v : G) x ∈ (weightSpace ρ N χ).map (ρ (v : G)) := Submodule.mem_map_of_mem hx
  rw [hbot] at h1
  exact injective_rho ρ (v : G) (by rw [(Submodule.mem_bot k).1 h1, map_zero])

private theorem conjChar_fixed_of_mem [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    {D : Subgroup G} {χ : ↥N → k} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (hχ : weightSpace ρ N χ ≠ ⊥) {b : ↥N} (hb : χ b ≠ 1)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    (hCD : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hR1 : R ≠ ⊥) (hr : Nat.Prime (Nat.card ↥R))
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1)
    (g : ↥D) : conjChar N (Subgroup.inclusion hDN g) χ = χ := by
  classical
  have : Fintype ↥R := Fintype.ofFinite _
  have : Fact (Nat.card ↥R).Prime := ⟨hr⟩
  let _ : MulAction ↥D (↥N → k) := conjCharAction k hDN
  have hconjb : ∀ v : ↥(Subgroup.normalizer (N : Set G)), conjChar N v χ (v • b) ≠ 1 := by
    intro v; rwa [conjChar_apply, inv_smul_smul]
  have horbsub : ∀ h : ↥D, ∃ w : ↥R,
      conjChar N (Subgroup.inclusion hDN h) χ = conjChar N (Subgroup.inclusion hRN w) χ := fun h =>
    exists_conjChar_eq hk hcomm hχ hb (weightSpace_conjChar_ne_bot hχ _)
      (hconjb _) hRN hCN hrank
  have hswap : ∀ (a : ↥R) (c : ↥D), ∃ c' : ↥D,
      Subgroup.inclusion hRN a * Subgroup.inclusion hDN c
        = Subgroup.inclusion hDN c' * Subgroup.inclusion hRN a := by
    intro a c
    refine ⟨⟨(a : G) * (c : G) * (a : G)⁻¹, (hRD a.2 (c : G)).mp c.2⟩, ?_⟩
    apply Subtype.ext
    change (a : G) * (c : G) = (a : G) * (c : G) * (a : G)⁻¹ * (a : G)
    group
  have hRcancel : ∀ (a : ↥R) (ψ : ↥N → k), conjChar N (Subgroup.inclusion hRN a⁻¹)
      (conjChar N (Subgroup.inclusion hRN a) ψ) = ψ := by
    intro a ψ; rw [← conjChar_mul, ← map_mul, inv_mul_cancel, map_one, conjChar_one]
  have hDcancel : ∀ (c : ↥D) (ψ : ↥N → k), conjChar N (Subgroup.inclusion hDN c⁻¹)
      (conjChar N (Subgroup.inclusion hDN c) ψ) = ψ := by
    intro c ψ; rw [← conjChar_mul, ← map_mul, inv_mul_cancel, map_one, conjChar_one]
  let T : Subgroup ↥R :=
    { carrier := {w : ↥R | conjChar N (Subgroup.inclusion hRN w) χ ∈ MulAction.orbit ↥D χ}
      one_mem' := by
        refine ⟨1, ?_⟩
        change conjChar N (Subgroup.inclusion hDN 1) χ = conjChar N (Subgroup.inclusion hRN 1) χ
        rw [map_one, map_one]
      mul_mem' := by
        rintro a c ⟨ga, hga⟩ ⟨gc, hgc⟩
        replace hga : conjChar N (Subgroup.inclusion hDN ga) χ
          = conjChar N (Subgroup.inclusion hRN a) χ := hga
        replace hgc : conjChar N (Subgroup.inclusion hDN gc) χ
          = conjChar N (Subgroup.inclusion hRN c) χ := hgc
        obtain ⟨c', hc'⟩ := hswap a gc
        refine ⟨c' * ga, ?_⟩
        change conjChar N (Subgroup.inclusion hDN (c' * ga)) χ
          = conjChar N (Subgroup.inclusion hRN (a * c)) χ
        calc conjChar N (Subgroup.inclusion hDN (c' * ga)) χ
            = conjChar N (Subgroup.inclusion hDN c') (conjChar N (Subgroup.inclusion hDN ga) χ) := by
              rw [map_mul, conjChar_mul]
          _ = conjChar N (Subgroup.inclusion hDN c') (conjChar N (Subgroup.inclusion hRN a) χ) := by
              rw [hga]
          _ = conjChar N (Subgroup.inclusion hDN c' * Subgroup.inclusion hRN a) χ := by
              rw [conjChar_mul]
          _ = conjChar N (Subgroup.inclusion hRN a * Subgroup.inclusion hDN gc) χ := by rw [hc']
          _ = conjChar N (Subgroup.inclusion hRN a) (conjChar N (Subgroup.inclusion hDN gc) χ) := by
              rw [conjChar_mul]
          _ = conjChar N (Subgroup.inclusion hRN a) (conjChar N (Subgroup.inclusion hRN c) χ) := by
              rw [hgc]
          _ = conjChar N (Subgroup.inclusion hRN (a * c)) χ := by rw [map_mul, conjChar_mul]
      inv_mem' := by
        rintro a ⟨ga, hga⟩
        replace hga : conjChar N (Subgroup.inclusion hDN ga) χ
          = conjChar N (Subgroup.inclusion hRN a) χ := hga
        obtain ⟨c', hc'⟩ := hswap a⁻¹ ga⁻¹
        refine ⟨c', ?_⟩
        change conjChar N (Subgroup.inclusion hDN c') χ
          = conjChar N (Subgroup.inclusion hRN a⁻¹) χ
        calc conjChar N (Subgroup.inclusion hDN c') χ
            = conjChar N (Subgroup.inclusion hDN c')
                (conjChar N (Subgroup.inclusion hRN a⁻¹)
                  (conjChar N (Subgroup.inclusion hRN a) χ)) := by rw [hRcancel]
          _ = conjChar N (Subgroup.inclusion hDN c' * Subgroup.inclusion hRN a⁻¹)
                (conjChar N (Subgroup.inclusion hRN a) χ) := by rw [conjChar_mul]
          _ = conjChar N (Subgroup.inclusion hRN a⁻¹ * Subgroup.inclusion hDN ga⁻¹)
                (conjChar N (Subgroup.inclusion hRN a) χ) := by rw [hc']
          _ = conjChar N (Subgroup.inclusion hRN a⁻¹)
                (conjChar N (Subgroup.inclusion hDN ga⁻¹)
                  (conjChar N (Subgroup.inclusion hRN a) χ)) := by rw [conjChar_mul]
          _ = conjChar N (Subgroup.inclusion hRN a⁻¹)
                (conjChar N (Subgroup.inclusion hDN ga⁻¹)
                  (conjChar N (Subgroup.inclusion hDN ga) χ)) := by rw [hga]
          _ = conjChar N (Subgroup.inclusion hRN a⁻¹) χ := by rw [hDcancel] }
  rcases T.eq_bot_or_eq_top_of_prime_card with hTbot | hTtop
  · obtain ⟨w, hw⟩ := horbsub g
    have hwT : w ∈ T := ⟨g, hw⟩
    rw [hTbot, Subgroup.mem_bot] at hwT
    subst hwT
    rw [map_one, conjChar_one] at hw
    exact hw
  · exfalso
    have horb_eq : MulAction.orbit ↥D χ
        = Set.range (fun w : ↥R => conjChar N (Subgroup.inclusion hRN w) χ) := by
      apply Set.Subset.antisymm
      · rintro ψ ⟨h, rfl⟩
        obtain ⟨w, hw⟩ := horbsub h
        exact ⟨w, hw.symm⟩
      · rintro ψ ⟨w, rfl⟩
        exact (hTtop ▸ Subgroup.mem_top w : w ∈ T)
    have hcard1 : Nat.card ↥(MulAction.orbit ↥D χ) = Nat.card ↥R := by
      rw [horb_eq]
      exact Nat.card_range_of_injective (injective_conjChar hχ hb hRN hCN)
    have hdvd : Nat.card ↥(MulAction.orbit ↥D χ) ∣ Nat.card ↥D := by
      rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥D χ)]
      exact Subgroup.index_dvd_card (MulAction.stabilizer ↥D χ)
    rw [hcard1] at hdvd
    exact not_dvd_card_of_fixedPointFree hr rfl hRD hCD hR1 hdvd

private theorem weight_eq_one [Finite G] [IsAlgClosed k] [FiniteDimensional k V] {D : Subgroup G}
    {χ : ↥N → k} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (hχ : weightSpace ρ N χ ≠ ⊥)
    (hND : N ≤ D) (hNc : N ≤ ⁅D, D⁆)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    (hCD : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hR1 : R ≠ ⊥) (hr : Nat.Prime (Nat.card ↥R))
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1)
    (b : ↥N) : χ b = 1 := by
  classical
  have : Fintype ↥R := Fintype.ofFinite _
  by_contra hb
  have hfix := conjChar_fixed_of_mem hk hcomm hχ hb hDN hRN hRD hCN hCD hR1 hr hrank
  have hinv : ∀ (g : ↥D) (x : V),
      x ∈ weightSpace ρ N χ → ρ ((g : G)) x ∈ weightSpace ρ N χ := by
    intro g x hx
    have h := (mem_weightSpace_conj ρ (Subgroup.inclusion hDN g) χ x).2 hx
    rwa [hfix g] at h
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hχ
  have hact : ∀ g : ↥D, ∃ c : k, ρ ((g : G)) z = c • z := fun g =>
    exists_smul_eq_of_mem_weightSpace hk hcomm hχ hb hRN hCN hrank hz (hinv g z hz) hz0
  choose ψ hψ using hact
  have hψmul : ∀ g h : ↥D, ψ (g * h) = ψ g * ψ h := by
    intro g h
    have e1 : ρ (((g * h : ↥D) : G)) z = ρ ((g : G)) (ρ ((h : G)) z) := by
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [hψ (g * h), hψ h, map_smul, hψ g, smul_smul] at e1
    have e2 : (ψ (g * h) - ψ g * ψ h) • z = 0 := by rw [sub_smul, e1, mul_comm, sub_self]
    rcases smul_eq_zero.1 e2 with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hz0
  have hψone : ψ 1 = 1 := by
    have e := hψ 1
    rw [OneMemClass.coe_one, map_one, Module.End.one_apply] at e
    have e2 : (ψ 1 - 1) • z = 0 := by rw [sub_smul, ← e, one_smul, sub_self]
    rcases smul_eq_zero.1 e2 with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hz0
  have hψne : ∀ g : ↥D, ψ g ≠ 0 := by
    intro g h0
    have e := hψmul g g⁻¹
    rw [mul_inv_cancel, hψone, h0, zero_mul] at e
    exact one_ne_zero e
  let Ψ : ↥D →* kˣ :=
    { toFun := fun g => Units.mk0 (ψ g) (hψne g)
      map_one' := by ext; simpa using hψone
      map_mul' := fun a b => by ext; simpa using hψmul a b }
  have hbD : (b : G) ∈ D := hND b.2
  have hbc : (⟨(b : G), hbD⟩ : ↥D) ∈ _root_.commutator ↥D := by
    have h1 : (b : G) ∈ (⁅D, D⁆ : Subgroup G) := hNc b.2
    rw [commutator_self_eq_map_commutator D] at h1
    obtain ⟨x, hx, hxv⟩ := h1
    have hxe : x = (⟨(b : G), hbD⟩ : ↥D) := Subtype.ext hxv
    rwa [hxe] at hx
  have hψb : ψ (⟨(b : G), hbD⟩ : ↥D) = 1 := by
    have h := Abelianization.commutator_subset_ker Ψ hbc
    rw [MonoidHom.mem_ker] at h
    simpa [Ψ, Units.ext_iff] using h
  have h2 : ρ ((b : G)) z = z := by
    have h3 := hψ (⟨(b : G), hbD⟩ : ↥D)
    rw [hψb, one_smul] at h3
    exact h3
  have hbz : ρ ((b : G)) z = χ b • z := hz b
  have h4 : (χ b - 1) • z = 0 := by rw [sub_smul, ← hbz, h2, one_smul, sub_self]
  rcases smul_eq_zero.1 h4 with h' | h'
  · exact hb (sub_eq_zero.1 h')
  · exact hz0 h'

private theorem eq_one_of_mem_of_forall_commute [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    {D : Subgroup G} (hk : (Nat.card G : k) ≠ 0)
    (hcomm : ∀ y z : ↥N, Commute (ρ (y : G)) (ρ (z : G)))
    (hND : N ≤ D) (hNc : N ≤ ⁅D, D⁆)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hCN : ∀ x ∈ R, x ≠ 1 → N ⊓ Subgroup.centralizer {x} = ⊥)
    (hCD : ∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥)
    (hR1 : R ≠ ⊥) (hr : Nat.Prime (Nat.card ↥R))
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1)
    (y : G) (hy : y ∈ N) : ρ y = 1 := by
  classical
  have hspan : (⨆ χ : ↥N → k, weightSpace ρ N χ) = ⊤ := iSup_weightSpace_eq_top ρ hk N hcomm
  have hle : (⨆ χ : ↥N → k, weightSpace ρ N χ) ≤ LinearMap.ker ((ρ y) - 1) := by
    refine iSup_le fun χ x hx => ?_
    by_cases hbot : weightSpace ρ N χ = ⊥
    · rw [hbot, Submodule.mem_bot] at hx
      simp [hx]
    · have htriv := weight_eq_one hk hcomm hbot hND hNc hDN hRN hRD hCN hCD hR1 hr hrank
        (⟨y, hy⟩ : ↥N)
      have hxy := hx (⟨y, hy⟩ : ↥N)
      rw [htriv, one_smul] at hxy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hxy
  rw [hspan, top_le_iff] at hle
  ext v
  have hv : v ∈ LinearMap.ker ((ρ y) - 1) := by rw [hle]; trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

private theorem eq_one_of_mem_commutator_of_card_le [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) {R : Subgroup G}
    (hk : (Nat.card G : k) ≠ 0) (hR1 : R ≠ ⊥) (hr : Nat.Prime (Nat.card ↥R))
    (hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1) :
    ∀ (n : ℕ) (D : Subgroup G), Nat.card ↥D ≤ n →
      R ≤ Subgroup.normalizer (D : Set G) →
      (∀ x ∈ R, x ≠ 1 → D ⊓ Subgroup.centralizer {x} = ⊥) →
      Group.IsSolvable ↥D → ∀ y ∈ (⁅D, D⁆ : Subgroup G), ρ y = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hDn hRD hCD hsol y hy
    by_cases hD : D = ⊥
    · subst hD
      rw [Subgroup.commutator_bot_left, Subgroup.mem_bot] at hy
      subst hy
      exact map_one ρ
    · have hND : (⁅D, D⁆ : Subgroup G) ≤ D := Subgroup.commutator_le_self D
      have hlt : (⁅D, D⁆ : Subgroup G) < D := commutator_self_lt_of_isSolvable hsol hD
      have hcardlt : Nat.card ↥(⁅D, D⁆ : Subgroup G) < Nat.card ↥D :=
        Set.card_strictMono (SetLike.coe_ssubset_coe.2 hlt)
      have hRN : R ≤ Subgroup.normalizer ((⁅D, D⁆ : Subgroup G) : Set G) :=
        hRD.trans (normalizer_le_normalizer_commutator_self D)
      have hDN : D ≤ Subgroup.normalizer ((⁅D, D⁆ : Subgroup G) : Set G) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_commutator_self D)
      have hCN : ∀ x ∈ R, x ≠ 1 →
          (⁅D, D⁆ : Subgroup G) ⊓ Subgroup.centralizer {x} = ⊥ := fun x hx hx1 =>
        le_antisymm ((inf_le_inf_right _ hND).trans (hCD x hx hx1).le) bot_le
      have hIH := ih (Nat.card ↥(⁅D, D⁆ : Subgroup G)) (lt_of_lt_of_le hcardlt hDn)
        (⁅D, D⁆ : Subgroup G) le_rfl hRN hCN (isSolvable_commutator_self hsol)
      have hcomm : ∀ a b : ↥(⁅D, D⁆ : Subgroup G), Commute (ρ ((a : G))) (ρ ((b : G))) := by
        intro a b
        have h1 : ρ ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) = 1 :=
          hIH _ (Subgroup.commutator_mem_commutator a.2 b.2)
        have he : ((a : G)) * ((b : G))
            = ((a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹) * (((b : G)) * ((a : G))) := by
          group
        have h2 : ρ (((a : G)) * ((b : G))) = ρ (((b : G)) * ((a : G))) := by
          rw [he, map_mul, h1, one_mul]
        rwa [map_mul, map_mul] at h2
      exact eq_one_of_mem_of_forall_commute hk hcomm hND le_rfl hDN hRN hRD hCN hCD hR1 hr hrank y hy

private theorem eq_one_of_mem_commutator_final [Finite G] [IsAlgClosed k] [FiniteDimensional k V]
    {K R : Subgroup G} (hK : K.Normal) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hfinrank : Module.finrank k ↥(Representation.invariants (ρ.comp R.subtype)) = 1)
    {x : G} (hx : x ∈ (⁅K, K⁆ : Subgroup G)) : ρ x = 1 := by
  have hrank : Module.rank k ↥(Representation.invariants (ρ.comp R.subtype)) ≤ 1 := by
    exact_mod_cast FiniteDimensional.finrank_le_iff_rank_le.mp hfinrank.le
  have hRK : R ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff.2 fun r _ z hz => hK.conj_mem z hz r
  exact eq_one_of_mem_commutator_of_card_le ρ hk hR1 hr hrank (Nat.card ↥K) K le_rfl hRK hC hsol x hx

end Core

theorem eq_one_of_mem_commutator_of_finrank_invariants_eq_one
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hfinrank : Module.finrank k (Representation.invariants (ρ.comp R.subtype)) = 1)
    {x : G} (hx : x ∈ ⁅K, K⁆) : ρ x = 1 :=
  eq_one_of_mem_commutator_final hK hR1 hC hsol hr hk ρ hfinrank hx

theorem eq_one_of_generalLinearGroup_of_mem_commutator_of_finrank_invariants_eq_one
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hk : (Nat.card G : k) ≠ 0) (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hfinrank : Module.finrank k
      (Representation.invariants (((Units.coeHom (V →ₗ[k] V)).comp ρ).comp R.subtype)) = 1)
    {x : G} (hx : x ∈ ⁅K, K⁆) : ρ x = 1 := by
  have h := eq_one_of_mem_commutator_of_finrank_invariants_eq_one hK hKR hK1 hR1 hC hsol hr hk
    ((Units.coeHom (V →ₗ[k] V)).comp ρ) hfinrank hx
  refine Units.ext ?_
  simpa using h

theorem forall_apply_eq_self_of_mem_commutator_of_finrank_invariants_eq_one
    [IsAlgClosed k] [FiniteDimensional k V] [Finite G]
    (hK : K.Normal) (hKR : Subgroup.IsComplement' K R) (hK1 : K ≠ ⊥) (hR1 : R ≠ ⊥)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ Subgroup.centralizer {x} = ⊥)
    (hsol : Group.IsSolvable ↥K) (hr : Nat.Prime (Nat.card ↥R))
    (hk : (Nat.card G : k) ≠ 0) (ρ : Representation k G V)
    (hfinrank : Module.finrank k (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ x ∈ ⁅K, K⁆, ∀ v : V, ρ x v = v := by
  intro x hx v
  rw [eq_one_of_mem_commutator_of_finrank_invariants_eq_one hK hKR hK1 hR1 hC hsol hr hk ρ
    hfinrank hx]
  simp

end CFSG.FeitThompson

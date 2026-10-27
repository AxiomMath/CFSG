module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpALevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {N j : ℕ}

section Proj

variable [CharP K 2] (hjN : 2 * j = N)

theorem spALeviHom_mem_range_spALeviOne
    (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    spALeviHom hjN.le g ∈ (spALeviOne (K := K) hjN.le).range := by
  obtain ⟨x, y, hxy⟩ := exists_spALeviOne_mul_spALeviTwo hjN.le ⟨g, rfl⟩
  have hy : y = 1 := by
    have h0 : N - 2 * j = 0 := by omega
    have : IsEmpty (Fin (N - 2 * j)) := by rw [h0]; infer_instance
    apply mat_injective
    ext a b
    exact isEmptyElim a
  exact ⟨x, by rw [← hxy, hy, map_one, mul_one]⟩

@[expose] noncomputable def spLagProj :
    centralizer ({spARep N j} : Set (StatedSp N K)) →* StatedSp j K :=
  (MonoidHom.ofInjective (spALeviOne_injective (K := K) hjN.le)).symm.toMonoidHom.comp
    ((spALeviHom hjN.le).codRestrict _ (spALeviHom_mem_range_spALeviOne hjN))

theorem spALeviOne_spLagProj (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    spALeviOne hjN.le (spLagProj hjN g) = spALeviHom hjN.le g := by
  rw [spLagProj, MonoidHom.comp_apply]
  exact MonoidHom.apply_ofInjective_symm _ _

@[expose] noncomputable def spLagIncl :
    StatedSp j K →* centralizer ({spARep N j} : Set (StatedSp N K)) :=
  (spALeviOne hjN.le).codRestrict _ (spALeviOne_mem_centralizer hjN.le)

theorem coe_spLagIncl (x : StatedSp j K) :
    (spLagIncl (K := K) hjN x : StatedSp N K) = spALeviOne hjN.le x := rfl

theorem spLagProj_spLagIncl (x : StatedSp j K) : spLagProj hjN (spLagIncl hjN x) = x := by
  apply spALeviOne_injective (K := K) hjN.le
  rw [spALeviOne_spLagProj]
  obtain ⟨g, hg⟩ := spALeviOne_mem_range (K := K) hjN.le x
  have e : spLagIncl hjN x = ⟨spALeviHom hjN.le g, spALeviHom_mem_centralizer hjN.le g⟩ :=
    Subtype.ext (by rw [coe_spLagIncl]; exact hg.symm)
  rw [e, spALeviHom_spALeviHom, hg]

theorem spLagProj_surjective : Function.Surjective (spLagProj (K := K) hjN) :=
  fun x => ⟨spLagIncl hjN x, spLagProj_spLagIncl hjN x⟩

theorem spLagProj_eq_one_iff (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    spLagProj hjN g = 1 ↔ (g : StatedSp N K) ∈ spARadical K N j hjN.le := by
  rw [mem_spARadical_iff hjN.le]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    rw [← spALeviOne_spLagProj hjN, h, map_one]
  · rintro ⟨hx, h⟩
    apply spALeviOne_injective (K := K) hjN.le
    rw [spALeviOne_spLagProj, map_one]
    exact h

theorem spLagIncl_inv_mul_mem (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    (((spLagIncl hjN (spLagProj hjN g))⁻¹ * g : centralizer ({spARep N j} : Set (StatedSp N K)))
      : StatedSp N K) ∈ spARadical K N j hjN.le := by
  rw [← spLagProj_eq_one_iff hjN, map_mul, map_inv, spLagProj_spLagIncl, inv_mul_cancel]

end Proj

section Radical

variable (hjN : 2 * j = N)

theorem mem_spARadical_iff_eq_upperUnipotentSp {x : StatedSp N K} :
    x ∈ spARadical K N j hjN.le ↔
      ∃ (X : Matrix (Fin N) (Fin N) K) (hX : Xᵀ = X), x = upperUnipotentSp N K hX := by
  constructor
  · intro hx
    obtain ⟨B, hB, X, hX, -, rfl⟩ := exists_spARadElt_of_mem hjN.le hx
    have hB0 : B = 0 := by
      ext a b
      rw [Matrix.zero_apply]
      by_contra hne
      have h1 := (hB a b hne).2
      have h2 := b.isLt
      omega
    have hU : spAOffUnit hB = 1 :=
      Units.ext (by rw [coe_spAOffUnit, hB0, add_zero, Units.val_one])
    exact ⟨X, hX, by rw [spARadElt, hU, map_one, one_mul]⟩
  · rintro ⟨X, hX, rfl⟩
    have hB : SpAOff j (0 : Matrix (Fin N) (Fin N) K) := fun a b h => absurd rfl h
    have hU : spAOffUnit hB = 1 := Units.ext (by rw [coe_spAOffUnit, add_zero, Units.val_one])
    have e : upperUnipotentSp N K hX = spARadElt hB hX := by
      rw [spARadElt, hU, map_one, one_mul]
    rw [e]
    exact spARadElt_mem_spARadical hjN.le hB hX (fun k _ hk _ => by have := k.isLt; omega)

theorem upperUnipotentSp_mem_spARadical {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) :
    upperUnipotentSp N K hX ∈ spARadical K N j hjN.le :=
  (mem_spARadical_iff_eq_upperUnipotentSp hjN).2 ⟨X, hX, rfl⟩

theorem spARadical_commute {x y : StatedSp N K} (hx : x ∈ spARadical K N j hjN.le)
    (hy : y ∈ spARadical K N j hjN.le) : x * y = y * x := by
  obtain ⟨X, hX, rfl⟩ := (mem_spARadical_iff_eq_upperUnipotentSp hjN).1 hx
  obtain ⟨Y, hY, rfl⟩ := (mem_spARadical_iff_eq_upperUnipotentSp hjN).1 hy
  exact upperUnipotentSp_commute hX hY

end Radical

section Aut

variable [Finite K] [CharP K 2] (hjN : 2 * j = N)

omit [Finite K] in
theorem mem_spARadical_of_normal_of_isPGroup (hK : Nat.card K = 2) (hj3 : 3 ≤ j)
    {M : Subgroup (centralizer ({spARep N j} : Set (StatedSp N K)))} (hM : M.Normal)
    (h2 : IsPGroup 2 M) {g : centralizer ({spARep N j} : Set (StatedSp N K))} (hg : g ∈ M) :
    (g : StatedSp N K) ∈ spARadical K N j hjN.le := by
  have hN : (M.map (spLagProj hjN)).Normal := hM.map _ (spLagProj_surjective hjN)
  have hbot := eq_bot_of_normal_of_isPGroup_of_mulEquiv_two hK hj3
    (MulEquiv.refl (StatedSp j K)) _ hN (h2.map _)
  have hmem : spLagProj hjN g ∈ M.map (spLagProj hjN) := ⟨g, hg, rfl⟩
  rw [hbot, mem_bot] at hmem
  exact (spLagProj_eq_one_iff hjN g).1 hmem

omit [Finite K] in
theorem spARadical_subgroupOf_normal_isPGroup :
    ((spARadical K N j hjN.le).subgroupOf
        (centralizer ({spARep N j} : Set (StatedSp N K)))).Normal ∧
      IsPGroup 2 ((spARadical K N j hjN.le).subgroupOf
        (centralizer ({spARep N j} : Set (StatedSp N K)))) := by
  refine ⟨?_, (isPGroup_spARadical hjN.le).comap_subtype⟩
  have e : (spARadical K N j hjN.le).subgroupOf
      (centralizer ({spARep N j} : Set (StatedSp N K))) = (spLagProj hjN).ker := by
    ext g
    rw [mem_subgroupOf, MonoidHom.mem_ker, spLagProj_eq_one_iff hjN]
  rw [e]
  exact MonoidHom.normal_ker _

omit [Finite K] in
theorem mem_spARadical_map_iff (hK : Nat.card K = 2) (hj3 : 3 ≤ j)
    (φ : centralizer ({spARep N j} : Set (StatedSp N K)) ≃*
      centralizer ({spARep N j} : Set (StatedSp N K)))
    (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    (φ g : StatedSp N K) ∈ spARadical K N j hjN.le ↔
      (g : StatedSp N K) ∈ spARadical K N j hjN.le := by
  obtain ⟨hRn, hR2⟩ := spARadical_subgroupOf_normal_isPGroup (K := K) hjN
  constructor
  · intro h
    refine mem_spARadical_of_normal_of_isPGroup hjN hK hj3
      (hRn.map φ.symm.toMonoidHom φ.symm.surjective) (hR2.map _) ⟨φ g, ?_, ?_⟩
    · exact mem_subgroupOf.2 h
    · simp
  · intro h
    exact mem_spARadical_of_normal_of_isPGroup hjN hK hj3
      (hRn.map φ.toMonoidHom φ.surjective) (hR2.map _) ⟨g, mem_subgroupOf.2 h, rfl⟩

theorem exists_spLagProj_map_eq_conj (hK : Nat.card K = 2) (hj3 : 3 ≤ j)
    (φ : centralizer ({spARep N j} : Set (StatedSp N K)) ≃*
      centralizer ({spARep N j} : Set (StatedSp N K))) :
    ∃ s : StatedSp j K, ∀ g : centralizer ({spARep N j} : Set (StatedSp N K)),
      spLagProj hjN (φ g) = s * spLagProj hjN g * s⁻¹ := by
  have : Finite (StatedSp j K) := by
    have : Finite (GL (Fin j ⊕ Fin j) K) := inferInstance
    exact Subtype.finite
  set α : StatedSp j K →* StatedSp j K :=
    (spLagProj hjN).comp (φ.toMonoidHom.comp (spLagIncl hjN)) with hα
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : spLagProj hjN (φ (spLagIncl hjN x)) = 1 := hx
    rw [spLagProj_eq_one_iff hjN, mem_spARadical_map_iff hjN hK hj3,
      ← spLagProj_eq_one_iff hjN, spLagProj_spLagIncl] at h1
    exact h1
  set αE : MulAut (StatedSp j K) := MulEquiv.ofBijective α hαinj.bijective_of_finite with hαE
  obtain ⟨s, σ, hs⟩ := exists_eq_conj_mul_fieldSp hj3 αE
  have hσ : σ = 1 := by
    ext c
    rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl <;> simp
  rw [hσ, map_one, mul_one] at hs
  have hαs : ∀ x, α x = s * x * s⁻¹ := by
    intro x
    have h1 : αE x = α x := rfl
    rw [← h1, hs, MulAut.conj_apply]
  refine ⟨s, fun g => ?_⟩
  set r := (spLagIncl hjN (spLagProj hjN g))⁻¹ * g with hr
  have hrR : (r : StatedSp N K) ∈ spARadical K N j hjN.le := spLagIncl_inv_mul_mem hjN g
  have hφr : spLagProj hjN (φ r) = 1 := by
    rw [spLagProj_eq_one_iff hjN, mem_spARadical_map_iff hjN hK hj3]
    exact hrR
  have hg : g = spLagIncl hjN (spLagProj hjN g) * r := by rw [hr, mul_inv_cancel_left]
  rw [hg, map_mul, map_mul, hφr, mul_one, map_mul, spLagProj_spLagIncl,
    (spLagProj_eq_one_iff hjN r).2 hrR, mul_one]
  exact hαs _

end Aut

end CFSG.SeitzReduction.SymplecticPilot

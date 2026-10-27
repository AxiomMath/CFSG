module

public import CFSG.LargeExtraspecial.AS35YTSymp
public import CFSG.LargeExtraspecial.AS35YTSpOrd
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClWitt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.Natural

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ClassicalGroups.Symplectic Matrix

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem range_mem_commSpaceOf : ∀ g ∈ ρ.range, ∀ u ∈ commSpaceOf ρ ⊤, g u ∈ commSpaceOf ρ ⊤ := by
  rintro _ ⟨x, rfl⟩ u hu
  exact apply_mem_commSpaceOf ρ (Subgroup.mem_top x) hu

theorem range_isometry (hiso : ∀ x v, Q (ρ x v) = Q v) : ∀ g ∈ ρ.range, ∀ v, Q (g v) = Q v := by
  rintro _ ⟨x, rfl⟩ v
  exact hiso x v

theorem polar_apply_apply (hiso : ∀ x v, Q (ρ x v) = Q v) (x : X) (a b : V) :
    polar Q (ρ x a) (ρ x b) = polar Q a b :=
  AS35YS.polar_map_YS (hiso x) a b

theorem polar_eq_zero_of_fixed (hiso : ∀ x v, Q (ρ x v) = Q v) {v : V} (hv : ∀ x, ρ x v = v)
    {u : V} (hu : u ∈ commSpaceOf ρ ⊤) : polar Q v u = 0 := by
  have hle : commSpaceOf ρ ⊤ ≤ LinearMap.ker (Q.polarBilin v) := by
    refine (commSpaceOf_le_iff ρ).mpr fun x _ y hy => ?_
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hy
    rw [LinearMap.mem_ker, map_sub, polarBilin_apply_apply, polarBilin_apply_apply,
      ← polar_apply_apply hiso x v w, hv x, sub_self]
  have h := hle hu
  rwa [LinearMap.mem_ker, polarBilin_apply_apply] at h

theorem fixed_of_forall_polar (hQ : Q.polarBilin.Nondegenerate) (hiso : ∀ x v, Q (ρ x v) = Q v)
    {v : V} (hv : ∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) (x : X) : ρ x v = v := by
  rw [← sub_eq_zero]
  refine hQ.1 _ fun w => ?_
  have hw : ρ x⁻¹ w - w ∈ commSpaceOf ρ ⊤ :=
    commSpace_le_commSpaceOf ρ (Subgroup.mem_top _) (sub_mem_commSpace _ w)
  have e : ρ x (ρ x⁻¹ w) = w := by rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, LinearEquiv.coe_one, id]
  have h1 : polar Q (ρ x v) w = polar Q v (ρ x⁻¹ w) := by
    conv_lhs => rw [← e]
    exact polar_apply_apply hiso x v _
  have h2 := hv _ hw
  rw [map_sub, LinearMap.sub_apply, polarBilin_apply_apply, polarBilin_apply_apply, h1]
  rw [← polarBilin_apply_apply, ← polarBilin_apply_apply, ← map_sub, polarBilin_apply_apply] at *
  exact h2

theorem fixed_iff_forall_polar (hQ : Q.polarBilin.Nondegenerate) (hiso : ∀ x v, Q (ρ x v) = Q v)
    (v : V) : (∀ u ∈ commSpaceOf ρ ⊤, polar Q v u = 0) ↔ ∀ x, ρ x v = v :=
  ⟨fun h => fixed_of_forall_polar hQ hiso h, fun h _ hu => polar_eq_zero_of_fixed hiso h hu⟩

theorem mem_radU_iff_fixed (hQ : Q.polarBilin.Nondegenerate) (hiso : ∀ x v, Q (ρ x v) = Q v)
    (u : commSpaceOf ρ ⊤) : u ∈ AS35YS.radU Q (commSpaceOf ρ ⊤) ↔ ∀ x, ρ x u = u := by
  rw [AS35YS.mem_radU]
  exact fixed_iff_forall_polar hQ hiso u

@[expose] noncomputable def natAct (hiso : ∀ x v, Q (ρ x v) = Q v) :
    X →* (AS35YS.Quo Q (commSpaceOf ρ ⊤) ≃ₗ[ZMod 2] AS35YS.Quo Q (commSpaceOf ρ ⊤)) :=
  (AS35YS.quoHom Q (commSpaceOf ρ ⊤) ρ.range (range_isometry hiso)
    range_mem_commSpaceOf).comp ρ.rangeRestrict

@[simp] theorem natAct_mk (hiso : ∀ x v, Q (ρ x v) = Q v) (x : X) (u : commSpaceOf ρ ⊤) :
    natAct hiso x (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨ρ x u, apply_mem_commSpaceOf ρ (Subgroup.mem_top x) u.2⟩ :=
  rfl

theorem natAct_mem_isometryGroup (hiso : ∀ x v, Q (ρ x v) = Q v) (x : X) :
    natAct hiso x ∈ TauCeti.BilinForm.isometryGroup (AS35YS.bQuo Q (commSpaceOf ρ ⊤)) :=
  TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun v w =>
    AS35YS.bQuo_quoHom (hiso := range_isometry hiso) (hU := range_mem_commSpaceOf) _ v w

theorem natAct_injective [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) :
    Function.Injective (natAct hiso) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine h2 _ (MonoidHom.normal_ker _) fun ⟨k, hk⟩ => ⟨2, ?_⟩
  rw [MonoidHom.mem_ker] at hk
  have hW : ∀ u ∈ commSpaceOf ρ ⊤, ∀ x, ρ x (ρ k u - u) = ρ k u - u := by
    intro u hu
    have h := LinearEquiv.congr_fun hk (Submodule.Quotient.mk ⟨u, hu⟩)
    rw [natAct_mk, LinearEquiv.coe_one, id_eq, Submodule.Quotient.eq] at h
    exact (mem_radU_iff_fixed hQ hiso _).mp h
  refine Subtype.ext (hinj ?_)
  ext v
  set g := ρ k with hg
  have hv1 : g v - v ∈ commSpaceOf ρ ⊤ :=
    commSpace_le_commSpaceOf ρ (Subgroup.mem_top k) (sub_mem_commSpace _ v)
  set w₁ := g v - v with hw₁
  set w₂ := g w₁ - w₁ with hw₂
  have hfix : ∀ x, ρ x w₂ = w₂ := hW w₁ hv1
  have e1 : g v = v + w₁ := by rw [hw₁]; abel
  have e2 : g w₁ = w₁ + w₂ := by rw [hw₂]; abel
  have e3 : g w₂ = w₂ := hfix k
  have hsq : ∀ y : V, y + y = 0 := fun y => ZModModule.add_self y
  have hg2 : g (g v) = v + w₂ := by
    rw [e1, map_add, e1, e2]
    calc v + w₁ + (w₁ + w₂) = v + (w₁ + w₁) + w₂ := by abel
      _ = v + w₂ := by rw [hsq, add_zero]
  have hg2' : g (g w₂) = w₂ := by rw [e3, e3]
  show (ρ (k ^ 2 ^ 2)) v = (ρ 1) v
  rw [map_pow, map_one, LinearEquiv.coe_one, id]
  show (g ^ 4) v = v
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_one]
  simp only [LinearEquiv.mul_apply]
  rw [hg2, map_add, map_add, hg2, hg2']
  calc v + w₂ + w₂ = v + (w₂ + w₂) := by abel
    _ = v := by rw [hsq, add_zero]

section Symplectic

variable [FiniteDimensional (ZMod 2) V]

theorem exists_card_le_spOrd [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∃ j, finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) = 2 * j ∧
      Nat.card X ≤ 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) := by
  obtain ⟨j, hj⟩ := S2.sp_even_finrank (f := AS35YS.bQuo Q (commSpaceOf ρ ⊤))
    AS35YS.bQuo_isAlt AS35YS.bQuo_nondegenerate
  have hdim : finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) = 2 * j := by
    rw [two_mul]
    exact hj
  refine ⟨j, hdim, ?_⟩
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤)) := Module.finite_of_finite (ZMod 2)
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤) ≃ₗ[ZMod 2] AS35YS.Quo Q (commSpaceOf ρ ⊤)) :=
    AS35YR.finite_linearEquiv_YR
  have h1 := Nat.card_le_card_of_injective
    (fun x : X => (⟨natAct hiso x, natAct_mem_isometryGroup hiso x⟩ :
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo Q (commSpaceOf ρ ⊤))))
    fun a b hab => natAct_injective hQ hiso hinj h2 (congrArg Subtype.val hab)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup j
    (AS35YS.bQuo Q (commSpaceOf ρ ⊤)) AS35YS.bQuo_isAlt AS35YS.bQuo_nondegenerate hdim,
    Nat.card_zmod] at h1
  exact h1

theorem finrank_quo_le :
    finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) ≤ finrank (ZMod 2) (commSpaceOf ρ ⊤) :=
  (Submodule.finrank_quotient_le _)

theorem range_natAct_eq [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {j : ℕ}
    (hj : finrank (ZMod 2) (AS35YS.Quo Q (commSpaceOf ρ ⊤)) = 2 * j)
    (hX : Nat.card X = 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1)) :
    (natAct hiso).range =
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo Q (commSpaceOf ρ ⊤)) := by
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤)) := Module.finite_of_finite (ZMod 2)
  have : Finite (AS35YS.Quo Q (commSpaceOf ρ ⊤) ≃ₗ[ZMod 2] AS35YS.Quo Q (commSpaceOf ρ ⊤)) :=
    AS35YR.finite_linearEquiv_YR
  have hle : (natAct hiso).range ≤
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo Q (commSpaceOf ρ ⊤)) := by
    rintro _ ⟨x, rfl⟩
    exact natAct_mem_isometryGroup hiso x
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup j
    (AS35YS.bQuo Q (commSpaceOf ρ ⊤)) AS35YS.bQuo_isAlt AS35YS.bQuo_nondegenerate hj,
    Nat.card_zmod, ← hX]
  exact (Nat.card_congr (MonoidHom.ofInjective (natAct_injective hQ hiso hinj h2)).toEquiv).le

theorem exists_natural_symplectic [Finite X] (hQ : Q.polarBilin.Nondegenerate)
    (hiso : ∀ x v, Q (ρ x v) = Q v) (hinj : Function.Injective ρ)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) {m : ℕ}
    (hX : Nat.card X = 2 ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1))
    (hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m + 1) :
    ∃ (φ : X ≃* ↥(StatedSp m (ZMod 2))) (π : V →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧
      (∀ v ∈ commSpaceOf ρ ⊤, π v = 0 ↔ ∀ x, ρ x v = v) ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ u ∈ commSpaceOf ρ ⊤, ∀ v ∈ commSpaceOf ρ ⊤, polar Q u v = spForm m (ZMod 2) (π u) (π v))
    := by
  set U := commSpaceOf ρ ⊤ with hU
  set W := AS35YS.Quo Q U
  set F := AS35YS.bQuo Q U with hF
  obtain ⟨j, hj, hcard⟩ := exists_card_le_spOrd hQ hiso hinj h2
  have hjm : j = m := by
    refine le_antisymm ?_ (AS35YT.le_of_spOrd_le (hX ▸ hcard))
    have := (finrank_quo_le (ρ := ρ) (Q := Q)).trans hdim
    omega
  subst hjm
  have hrange := range_natAct_eq hQ hiso hinj h2 hj hX
  obtain ⟨m', b, hb⟩ := (AS35YS.bQuo_isAlt (q := Q) (U := U)).exists_basis_toMatrix_eq_J
    AS35YS.bQuo_nondegenerate
  have hm' : m' = j := by
    have := Module.finrank_eq_card_basis b
    rw [Fintype.card_sum, Fintype.card_fin, hj] at this
    omega
  subst hm'
  have hG : ∀ u w, F u w = spForm m' (ZMod 2) (b.equivFun u) (b.equivFun w) := by
    intro u w
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b F u w, hb,
      CFSG.RankThree.GF2n.Stroth80.Classify.basis_J_eq_spJ, spForm_apply]
    rfl
  set ψ : X →* GL (Fin m' ⊕ Fin m') (ZMod 2) := b.toGL.toMonoidHom.comp (natAct hiso) with hψ
  have hψmem : ∀ x, ψ x ∈ StatedSp m' (ZMod 2) := by
    intro x
    rw [mem_statedSp_iff_forall]
    intro y z
    obtain ⟨u, rfl⟩ := b.equivFun.surjective y
    obtain ⟨w, rfl⟩ := b.equivFun.surjective z
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun,
      CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun, ← hG, ← hG]
    exact (TauCeti.BilinForm.mem_isometryGroup_iff.mp (natAct_mem_isometryGroup hiso x)) u w
  have hψinj : Function.Injective ψ :=
    b.toGL.injective.comp (natAct_injective hQ hiso hinj h2)
  have hψsurj : ∀ A : StatedSp m' (ZMod 2), ∃ x, ψ x = A := by
    rintro ⟨A, hA⟩
    obtain ⟨g, rfl⟩ := b.toGL.surjective A
    have hg : g ∈ TauCeti.BilinForm.isometryGroup F := by
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro u w
      have h' := (mem_statedSp_iff_forall _).mp hA (b.equivFun u) (b.equivFun w)
      rw [CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun,
        CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun, ← hG, ← hG] at h'
      exact h'
    rw [← hrange] at hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, by rw [hψ, MonoidHom.comp_apply, hx]; rfl⟩
  let φ : X ≃* ↥(StatedSp m' (ZMod 2)) := MulEquiv.ofBijective
    ((ψ.codRestrict _ hψmem))
    ⟨fun x y hxy => hψinj (congrArg Subtype.val hxy), fun A => by
      obtain ⟨x, hx⟩ := hψsurj A
      exact ⟨x, Subtype.ext hx⟩⟩
  set π₀ : U →ₗ[ZMod 2] (Fin m' ⊕ Fin m' → ZMod 2) :=
    b.equivFun.toLinearMap.comp (AS35YS.radU Q U).mkQ with hπ₀
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend π₀
  have hπU : ∀ u : U, π u = b.equivFun (Submodule.Quotient.mk u) := fun u =>
    LinearMap.congr_fun hπ u
  refine ⟨φ, π, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨w, rfl⟩ := b.equivFun.surjective y
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact ⟨u, u.2, hπU u⟩
  · intro v hv
    have h := hπU ⟨v, hv⟩
    rw [h, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero,
      mem_radU_iff_fixed hQ hiso]
  · intro x v hv
    have h1 := hπU ⟨ρ x v, apply_mem_commSpaceOf ρ (Subgroup.mem_top x) hv⟩
    have h2 := hπU ⟨v, hv⟩
    rw [h1, h2]
    have : (Submodule.Quotient.mk ⟨ρ x v, apply_mem_commSpaceOf ρ (Subgroup.mem_top x) hv⟩ : W) =
        natAct hiso x (Submodule.Quotient.mk ⟨v, hv⟩) := rfl
    rw [this, ← CFSG.RankThree.GF2n.Stroth80.Classify.basis_toGL_mulVec_equivFun]
    rfl
  · intro u hu v hv
    rw [hπU ⟨u, hu⟩, hπU ⟨v, hv⟩, ← hG, hF, AS35YS.bQuo_mk]

end Symplectic

end CFSG.LargeExtraspecial.A2Mod.Natural

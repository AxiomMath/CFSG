module

public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Orth
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Frame
public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Lift
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal.Spin QuadraticMap
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

omit [Group S] in
theorem pow_apply_of_fix {g : V ≃ₗ[K] V} {v : V} (h : g v = v) (m : ℕ) : (g ^ m) v = v := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]

omit [Group S] in
theorem inv_apply_of_fix {g : V ≃ₗ[K] V} {v : V} (h : g v = v) : g⁻¹ v = v := by
  conv_lhs => rw [← h]
  exact LinearEquiv.inv_apply_apply' g v

omit [Group S] in
theorem det_eq_one_of_mem_orthDerived {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) :
    LinearEquiv.det g = 1 := by
  have hker : orthDerived Q ≤ (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
  exact MonoidHom.mem_ker.mp (hker hg)

omit [Group S] in
@[expose] noncomputable def smulEquiv (c : K) (hc : c ≠ 0) (g : V ≃ₗ[K] V) : V ≃ₗ[K] V :=
  LinearEquiv.smulOfUnit (Units.mk0 c hc) * g

omit [Group S] in
theorem smulEquiv_apply (c : K) (hc : c ≠ 0) (g : V ≃ₗ[K] V) (v : V) :
    smulEquiv c hc g v = c • g v := rfl

omit [Group S] in
theorem smulEquiv_mem {c : K} (hc : c ≠ 0) (hcc : c * c = 1) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    smulEquiv c hc g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [smulEquiv_apply, QuadraticMap.map_smul, hcc, one_smul, map_of_mem hg]

omit [Group S] in
theorem eq_of_smul_of_apply_eq {m m' : V ≃ₗ[K] V} {c : K} (h : ∀ v, m' v = c • m v) {v : V}
    (hv0 : m v ≠ 0) (hv : m' v = m v) : m' = m := by
  have hc : c = 1 := by
    have h1 : c • m v = (1 : K) • m v := by rw [← h, hv, one_smul]
    exact smul_left_injective K hv0 h1
  exact LinearEquiv.ext fun w => by rw [h, hc, one_smul]

variable [Finite K] [FiniteDimensional K V]

omit [Group S] in
theorem elementaryGroup_le_orthDerived (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) :
    elementaryGroup Q ≤ orthDerived Q := by
  have : NeZero (2 : K) := ⟨two_ne_zero' hK⟩
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero' hK)
  exact elementaryGroup_le_of_eichler_mem fun u w _ huw =>
    mem_commutator_orthogonalGroup_of_pow_three (QuadraticMap.nondegenerate_polar_iff.mp hQ)
      (eichler_mem_orthogonalGroup Q u w) (eichler_pow_three (three_eq_zero hK) huw)

structure Ctx (θ : ↥(orthDerived Q) →* S) (A : Subgroup S) (r : S)
    (e : ↥A ≃* QuaternionGroup 2) (x y : ↥(orthDerived Q)) : Prop where
  card : Nat.card K = 3
  nondeg : (polarBilin Q).Nondegenerate
  dim : 7 ≤ Module.finrank K V
  ker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)
  datum : QuatTwinDatum A r
  lift_x : θ x = Lift.genX e
  lift_y : θ y = Lift.genY e

omit [Group S] [Finite K] [FiniteDimensional K V] in
private theorem ne_zero_of_apply {g : V ≃ₗ[K] V} {v : V} (hv0 : v ≠ 0) {c₀ : K}
    (h : g v = c₀ • v) : c₀ ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  exact hv0 (g.injective (h.trans (map_zero g).symm))

omit [Group S] [Finite K] [FiniteDimensional K V] in
theorem comm_coe {g T : ↥(orthDerived Q)} (h : g * T = T * g) :
    (T : V ≃ₗ[K] V) * g = g * T :=
  (congrArg Subtype.val h).symm

omit [Group S] [Finite K] [FiniteDimensional K V] in
theorem xrho (x : ↥(orthDerived Q)) :
    (x : V ≃ₗ[K] V) * (↑x * ↑x : V ≃ₗ[K] V) = (↑x * ↑x : V ≃ₗ[K] V) * ↑x :=
  (mul_assoc _ _ _).symm

omit [Group S] [Finite K] [FiniteDimensional K V] in
theorem rho_mem (x : ↥(orthDerived Q)) :
    (↑x * ↑x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  mul_mem (orthDerived_le x.2) (orthDerived_le x.2)

namespace Ctx

variable {θ : ↥(orthDerived Q) →* S} {A : Subgroup S} {r : S} {e : ↥A ≃* QuaternionGroup 2}
  {x y : ↥(orthDerived Q)} (c : Ctx θ A r e x y)
include c

omit [Finite K] [FiniteDimensional K V] in
theorem nontriv : Nontrivial V :=
  Module.nontrivial_of_finrank_pos (R := K) (by have := c.dim; omega)

omit [FiniteDimensional K V] in
theorem two : (2 : K) ≠ 0 := two_ne_zero' c.card

omit [FiniteDimensional K V] in
theorem three : (3 : K) = 0 := three_eq_zero c.card

omit [Finite K] [FiniteDimensional K V] in
theorem center : θ.ker ≤ Subgroup.center ↥(orthDerived Q) := ker_le_center c.ker

omit [Finite K] [FiniteDimensional K V] in
theorem expTwo : ∀ z ∈ θ.ker, z * z = 1 := by
  have := c.nontriv
  exact ker_mul_self c.nondeg c.ker

omit [Finite K] [FiniteDimensional K V] in
theorem rho : x * x * (x * x) = 1 ∧ y * (x * x) = x * x * y :=
  Lift.rho_mul_rho θ e c.center c.expTwo c.lift_x c.lift_y

omit [Finite K] [FiniteDimensional K V] in
theorem rhoV : (↑x * ↑x : V ≃ₗ[K] V) * (↑x * ↑x : V ≃ₗ[K] V) = 1 := by
  simpa only [Subgroup.coe_mul, Subgroup.coe_one] using congrArg Subtype.val c.rho.1

omit [Finite K] [FiniteDimensional K V] in
theorem yrhoV : (y : V ≃ₗ[K] V) * (↑x * ↑x : V ≃ₗ[K] V) = (↑x * ↑x : V ≃ₗ[K] V) * ↑y := by
  simpa only [Subgroup.coe_mul] using congrArg Subtype.val c.rho.2

omit [Finite K] [FiniteDimensional K V] in
theorem theta_rho : θ (x * x) = r := by
  have hmem : Lift.genX e ^ 2 ∈ A := A.pow_mem (Lift.genX_mem e) 2
  have hsq : Lift.genX e ^ 2 * Lift.genX e ^ 2 = 1 := by
    rw [← pow_add]
    exact Lift.genX_pow_four e
  rcases c.datum.inv.unique _ hmem hsq with h | h
  · exact absurd h (Lift.genX_sq_ne_one e)
  · rw [map_mul, c.lift_x, ← pow_two, h]

omit [FiniteDimensional K V] in
theorem isCompl :
    IsCompl (plusSp (↑x * ↑x : V ≃ₗ[K] V)) (minusSp (↑x * ↑x : V ≃ₗ[K] V)) :=
  isCompl_plusSp_minusSp c.two c.rhoV

theorem finrank_add :
    Module.finrank K (plusSp (↑x * ↑x : V ≃ₗ[K] V)) +
      Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V)) = Module.finrank K V :=
  Submodule.finrank_add_eq_of_isCompl c.isCompl

omit [FiniteDimensional K V] in
theorem nondeg_minus : PolarNondegOn Q (minusSp (↑x * ↑x : V ≃ₗ[K] V)) :=
  polarNondegOn_minusSp c.two c.nondeg (rho_mem x) c.rhoV

omit [FiniteDimensional K V] in
theorem nondeg_plus : PolarNondegOn Q (plusSp (↑x * ↑x : V ≃ₗ[K] V)) := by
  rw [← minusSp_negI]
  exact polarNondegOn_minusSp c.two c.nondeg (negI_mem_orthogonalGroup (rho_mem x))
    (negI_mul_self c.rhoV)

omit [FiniteDimensional K V] in
theorem polar_plus_minus {p q : V} (hp : p ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V))
    (hq : q ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V)) : polar Q q p = 0 := by
  rw [polar_comm]
  exact polar_plusSp_minusSp c.two (rho_mem x) hp hq

omit [FiniteDimensional K V] in
theorem minus_ne_bot : minusSp (↑x * ↑x : V ≃ₗ[K] V) ≠ ⊥ := by
  intro hbot
  apply c.datum.inv.ne_one
  rw [← c.theta_rho]
  have h1 : x * x = 1 := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq c.two c.rhoV v
    rw [hbot, Submodule.mem_bot] at hw
    subst hw
    rw [add_zero]
    exact mem_plusSp.mp hu
  rw [h1, map_one]

omit [FiniteDimensional K V] in
theorem plus_ne_bot : plusSp (↑x * ↑x : V ≃ₗ[K] V) ≠ ⊥ := by
  intro hbot
  apply c.datum.inv.ne_one
  rw [← c.theta_rho]
  have hk : x * x ∈ θ.ker := by
    rw [c.ker, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    refine mem_scalars.mpr ⟨-1, fun v => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq c.two c.rhoV v
    rw [hbot, Submodule.mem_bot] at hu
    subst hu
    rw [zero_add, neg_one_smul]
    exact mem_minusSp.mp hw
  exact hk

omit [Finite K] [FiniteDimensional K V] in
theorem mem_A_x : θ x ∈ A := c.lift_x ▸ Lift.genX_mem e

omit [Finite K] [FiniteDimensional K V] in
theorem mem_A_y : θ y ∈ A := c.lift_y ▸ Lift.genY_mem e

theorem gen_mem {S' : Submodule K V} {ε : K} (hε : ε * ε = 1)
    (hS : ∀ v ∈ S', (↑x * ↑x : V ≃ₗ[K] V) v = ε • v) {u w : V} (hu : u ∈ S') (hw : w ∈ S')
    (huw : polar Q u w = 0) :
    ∃ hg : eichler Q u w ∈ orthDerived Q, (⟨_, hg⟩ : ↥(orthDerived Q)) ^ 3 = 1 ∧
      (⟨_, hg⟩ : ↥(orthDerived Q)) * (x * x) = x * x * ⟨_, hg⟩ := by
  have : NeZero (2 : K) := ⟨c.two⟩
  have : Invertible (2 : K) := invertibleOfNonzero c.two
  have h3 := eichler_pow_three c.three huw
  have hg := mem_commutator_orthogonalGroup_of_pow_three
    (QuadraticMap.nondegenerate_polar_iff.mp c.nondeg) (eichler_mem_orthogonalGroup Q u w) h3
  refine ⟨hg, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h3
  · have := comm_of_scalar_elemOn (rho_mem x) hε hS (eichler_mem_elemOn (Q := Q) hu hw)
    simp only [Subgroup.coe_mul]
    exact this.symm

omit [Finite K] [FiniteDimensional K V] in
theorem dichotomy (g : ↥(orthDerived Q)) (hg3 : g ^ 3 = 1) (hgρ : g * (x * x) = x * x * g) :
    (∀ T : ↥(orthDerived Q), θ T ∈ A → g * T = T * g) ∨
      (y * y = x * x ∧ y * x * (y * x) = x * x ∧ ∃ m : ℕ, ∃ z ∈ θ.ker,
        g ^ m * x * (g ^ m)⁻¹ = z * y ∨ g ^ m * x * (g ^ m)⁻¹ = z * y⁻¹) := by
  have hA := Lift.conjSub_eq_of_sq θ c.datum.sq c.theta_rho hg3 hgρ
  have hx2 : θ x ^ 2 ≠ 1 := c.lift_x ▸ Lift.genX_sq_ne_one e
  have hy2 : θ y ^ 2 ≠ 1 := c.lift_y ▸ Lift.genY_sq_ne_one e
  have hyxA : θ (y * x) ∈ A := by
    rw [map_mul]
    exact A.mul_mem c.mem_A_y c.mem_A_x
  have hyx2 : θ (y * x) ^ 2 ≠ 1 := by
    rw [map_mul, c.lift_x, c.lift_y]
    exact Lift.genYX_sq_ne_one e
  rcases Lift.comm_or_moved θ c.center c.expTwo e hg3 hA c.mem_A_x hx2 c.mem_A_y hy2 with
    h | ⟨m, z, hz, hm⟩
  · exact Or.inl h
  rcases Lift.comm_or_moved θ c.center c.expTwo e hg3 hA c.mem_A_x hx2 hyxA hyx2 with
    h | ⟨m', z', hz', hm'⟩
  · exact Or.inl h
  exact Or.inr ⟨Lift.mul_self_eq_of_moved θ c.center c.expTwo c.rho.1 hgρ hz hm,
    Lift.mul_self_eq_of_moved θ c.center c.expTwo c.rho.1 hgρ hz' hm', m, z, hz, hm⟩

omit [FiniteDimensional K V] in
theorem false_of_minus_scalar {c₀ : K}
    (hc₀ : ∀ v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V), (x : V ≃ₗ[K] V) v = c₀ • v) : False := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.minus_ne_bot
  have h1 : (x : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v) = -v := mem_minusSp.mp hv
  rw [hc₀ v hv, map_smul, hc₀ v hv, smul_smul] at h1
  exact sq_ne_neg_one c.card c₀ (smul_left_injective K hv0
    (show (c₀ * c₀) • v = (-1 : K) • v by rw [h1, neg_one_smul]))

theorem untw : y * y = x * x ∧ y * x * (y * x) = x * x := by
  by_contra hT
  have hcomm : ∀ {S' : Submodule K V} {ε : K}, ε * ε = 1 →
      (∀ v ∈ S', (↑x * ↑x : V ≃ₗ[K] V) v = ε • v) → ∀ u w, u ∈ S' → w ∈ S' → Q u = 0 →
        polar Q u w = 0 → (x : V ≃ₗ[K] V) * eichler Q u w = eichler Q u w * (x : V ≃ₗ[K] V) ∧
          (y : V ≃ₗ[K] V) * eichler Q u w = eichler Q u w * (y : V ≃ₗ[K] V) := by
    intro S' ε hε hS u w hu hw _ huw
    obtain ⟨hg, hg3, hgρ⟩ := c.gen_mem hε hS hu hw huw
    rcases c.dichotomy _ hg3 hgρ with h | ⟨h1, h2, -⟩
    · exact ⟨comm_coe (h x c.mem_A_x), comm_coe (h y c.mem_A_y)⟩
    · exact absurd ⟨h1, h2⟩ hT
  have hminus : ∀ v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V), (↑x * ↑x : V ≃ₗ[K] V) v = (-1 : K) • v :=
    fun v hv => by rw [mem_minusSp.mp hv, neg_one_smul]
  have hplus : ∀ v ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), (↑x * ↑x : V ≃ₗ[K] V) v = (1 : K) • v :=
    fun v hv => by rw [mem_plusSp.mp hv, one_smul]
  have hsum := c.finrank_add
  have hn := c.dim
  by_cases hm3 : 3 ≤ Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V))
  · obtain ⟨c₀, hc₀⟩ := exists_smul_of_gens c.card c.nondeg_minus hm3 (orthDerived_le x.2)
      (mem_minusSp_iff_of_comm (xrho x))
      (fun u w hu hw hQu huw => (hcomm (by ring) hminus u w hu hw hQu huw).1)
    exact c.false_of_minus_scalar hc₀
  · have hp3 : 3 ≤ Module.finrank K (plusSp (↑x * ↑x : V ≃ₗ[K] V)) := by omega
    obtain ⟨c₁, hc₁⟩ := exists_smul_of_gens c.card c.nondeg_plus hp3 (orthDerived_le x.2)
      (mem_plusSp_iff_of_comm (xrho x))
      (fun u w hu hw hQu huw => (hcomm (by ring) hplus u w hu hw hQu huw).1)
    obtain ⟨c₂, hc₂⟩ := exists_smul_of_gens c.card c.nondeg_plus hp3 (orthDerived_le y.2)
      (mem_plusSp_iff_of_comm c.yrhoV)
      (fun u w hu hw hQu huw => (hcomm (by ring) hplus u w hu hw hQu huw).2)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.plus_ne_bot
    have hc₁0 := ne_zero_of_apply hv0 (hc₁ v hv)
    have hc₂0 := ne_zero_of_apply hv0 (hc₂ v hv)
    have hρv : (↑x * ↑x : V ≃ₗ[K] V) v = v := mem_plusSp.mp hv
    have hρv0 : (↑x * ↑x : V ≃ₗ[K] V) v ≠ 0 := by rw [hρv]; exact hv0
    have hyy : θ (x * x) = θ (y * y) := by
      rw [map_mul, map_mul, c.lift_x, c.lift_y, ← pow_two, ← pow_two, Lift.genY_sq]
    have hyx : θ (x * x) = θ (y * x * (y * x)) := by
      simp only [map_mul, c.lift_x, c.lift_y]
      rw [← pow_two, ← pow_two, Lift.genYX_sq]
    have := c.nontriv
    obtain ⟨l₁, -, hl₁⟩ := exists_smul_of_map_eq c.nondeg c.ker hyy
    obtain ⟨l₂, -, hl₂⟩ := exists_smul_of_map_eq c.nondeg c.ker hyx
    have e1 : (x : V ≃ₗ[K] V) v = c₁ • v := hc₁ v hv
    have e2 : (y : V ≃ₗ[K] V) v = c₂ • v := hc₂ v hv
    apply hT
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · refine eq_of_smul_of_apply_eq (m := ((x * x : ↥(orthDerived Q)) : V ≃ₗ[K] V))
        (m' := ((y * y : ↥(orthDerived Q)) : V ≃ₗ[K] V)) hl₁ (v := v)
        (by simpa only [Subgroup.coe_mul] using hρv0) ?_
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at hρv ⊢
      rw [hρv, e2, map_smul, e2, smul_smul, mul_self_eq_one c.card hc₂0, one_smul]
    · refine eq_of_smul_of_apply_eq (m := ((x * x : ↥(orthDerived Q)) : V ≃ₗ[K] V))
        (m' := ((y * x * (y * x) : ↥(orthDerived Q)) : V ≃ₗ[K] V)) hl₂ (v := v)
        (by simpa only [Subgroup.coe_mul] using hρv0) ?_
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at hρv ⊢
      rw [hρv]
      have h4 : (y : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) ((y : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v))) =
          ((c₁ * c₁) * (c₂ * c₂)) • v := by
        simp only [e1, e2, map_smul, smul_smul]
        congr 1
        ring
      rw [h4, mul_self_eq_one c.card hc₁0, mul_self_eq_one c.card hc₂0, one_mul, one_smul]

theorem hYY : (↑y * ↑y : V ≃ₗ[K] V) = ↑x * ↑x := by
  simpa only [Subgroup.coe_mul] using congrArg Subtype.val c.untw.1

theorem hYX : (↑y * ↑x * (↑y * ↑x) : V ≃ₗ[K] V) = ↑x * ↑x := by
  simpa only [Subgroup.coe_mul] using congrArg Subtype.val c.untw.2

theorem false_of_moved_vec {g : ↥(orthDerived Q)} {m : ℕ} {z : ↥(orthDerived Q)}
    (hz : z ∈ θ.ker) (hm : g ^ m * x * (g ^ m)⁻¹ = z * y ∨ g ^ m * x * (g ^ m)⁻¹ = z * y⁻¹)
    {v : V} (hv : v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V)) (hv0 : v ≠ 0)
    (hgv : (g : V ≃ₗ[K] V) v = v)
    (hgxv : (g : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v) = (x : V ≃ₗ[K] V) v) : False := by
  have := c.nontriv
  obtain ⟨l, hl, hlz⟩ := exists_smul_of_mem_ker c.nondeg c.ker hz
  have hlhs : ((g ^ m * x * (g ^ m)⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = (x : V ≃ₗ[K] V) v := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, LinearEquiv.mul_apply]
    rw [inv_apply_of_fix (pow_apply_of_fix hgv m), pow_apply_of_fix hgxv m]
  refine false_of_moved c.two c.hYY c.hYX hv hv0 hl ?_
  rcases hm with hm | hm
  · left
    rw [← hlhs, hm, Subgroup.coe_mul, LinearEquiv.mul_apply, hlz]
  · right
    rw [← hlhs, hm, Subgroup.coe_mul, LinearEquiv.mul_apply, hlz, Subgroup.coe_inv]

theorem plus_gen_comm {u w : V} (hu : u ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V))
    (hw : w ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V)) (huw : polar Q u w = 0) :
    (x : V ≃ₗ[K] V) * eichler Q u w = eichler Q u w * (x : V ≃ₗ[K] V) ∧
      (y : V ≃ₗ[K] V) * eichler Q u w = eichler Q u w * (y : V ≃ₗ[K] V) := by
  have hplus : ∀ v ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), (↑x * ↑x : V ≃ₗ[K] V) v = (1 : K) • v :=
    fun v hv => by rw [mem_plusSp.mp hv, one_smul]
  obtain ⟨hg, hg3, hgρ⟩ := c.gen_mem (by ring) hplus hu hw huw
  rcases c.dichotomy _ hg3 hgρ with h | ⟨-, -, m, z, hz, hm⟩
  · exact ⟨comm_coe (h x c.mem_A_x), comm_coe (h y c.mem_A_y)⟩
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.minus_ne_bot
    have hfix := (support_of_mem_elemOn (eichler_mem_elemOn (Q := Q) hu hw)).2
    have hxv : (x : V ≃ₗ[K] V) v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V) :=
      map_mem_minusSp (xrho x) hv
    exact c.false_of_moved_vec hz hm hv hv0 (hfix v fun p hp => c.polar_plus_minus hp hv)
      (hfix _ fun p hp => c.polar_plus_minus hp hxv)

theorem minus_le_four : Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V)) ≤ 4 := by
  by_contra h5
  push Not at h5
  have hm3 : 3 ≤ Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V)) := by omega
  have hminus : ∀ v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V), (↑x * ↑x : V ≃ₗ[K] V) v = (-1 : K) • v :=
    fun v hv => by rw [mem_minusSp.mp hv, neg_one_smul]
  by_cases hall : ∀ u w, u ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V) →
      w ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V) → Q u = 0 → polar Q u w = 0 →
        (x : V ≃ₗ[K] V) * eichler Q u w = eichler Q u w * (x : V ≃ₗ[K] V)
  · obtain ⟨c₀, hc₀⟩ := exists_smul_of_gens c.card c.nondeg_minus hm3 (orthDerived_le x.2)
      (mem_minusSp_iff_of_comm (xrho x)) hall
    exact c.false_of_minus_scalar hc₀
  push Not at hall
  obtain ⟨u, w, hu, hw, hQu, huw, hne⟩ := hall
  obtain ⟨hg, hg3, hgρ⟩ := c.gen_mem (by ring) hminus hu hw huw
  rcases c.dichotomy _ hg3 hgρ with h | ⟨-, -, m, z, hz, hm⟩
  · exact hne (comm_coe (h x c.mem_A_x))
  · have := finrank_le_four (W := minusSp (↑x * ↑x : V ≃ₗ[K] V)) (X := (x : V ≃ₗ[K] V))
      (u := u) (w := w) fun v hv h1 h2 h3 h4 => by
        by_contra hv0
        exact c.false_of_moved_vec hz hm hv hv0 (eichler_fix hQu huw h1 h2)
          (eichler_fix hQu huw h3 h4)
    omega

theorem minus_ge_two : 2 ≤ Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V)) := by
  have hdet : LinearEquiv.det (↑x * ↑x : V ≃ₗ[K] V) = 1 := by
    have := det_eq_one_of_mem_orthDerived (x * x).2
    simpa only [Subgroup.coe_mul] using this
  obtain ⟨k, hk⟩ := even_finrank_minusSp c.two c.rhoV hdet
  have h0 : Module.finrank K (minusSp (↑x * ↑x : V ≃ₗ[K] V)) ≠ 0 := fun h0 =>
    c.minus_ne_bot (Submodule.finrank_eq_zero.mp h0)
  omega

theorem plus_ge_three : 3 ≤ Module.finrank K (plusSp (↑x * ↑x : V ≃ₗ[K] V)) := by
  have := c.finrank_add
  have := c.minus_le_four
  have := c.dim
  omega

theorem plus_scalars : ∃ c₁ c₂ : K, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧
    (∀ v ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), (x : V ≃ₗ[K] V) v = c₁ • v) ∧
    ∀ v ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), (y : V ≃ₗ[K] V) v = c₂ • v := by
  obtain ⟨c₁, hc₁⟩ := exists_smul_of_gens c.card c.nondeg_plus c.plus_ge_three
    (orthDerived_le x.2) (mem_plusSp_iff_of_comm (xrho x))
    (fun u w hu hw _ huw => (c.plus_gen_comm hu hw huw).1)
  obtain ⟨c₂, hc₂⟩ := exists_smul_of_gens c.card c.nondeg_plus c.plus_ge_three
    (orthDerived_le y.2) (mem_plusSp_iff_of_comm c.yrhoV)
    (fun u w hu hw _ huw => (c.plus_gen_comm hu hw huw).2)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.plus_ne_bot
  have hc₁0 := ne_zero_of_apply hv0 (hc₁ v hv)
  have hc₂0 := ne_zero_of_apply hv0 (hc₂ v hv)
  exact ⟨c₁, c₂, hc₁0, hc₂0, mul_self_eq_one c.card hc₁0, mul_self_eq_one c.card hc₂0, hc₁, hc₂⟩

theorem exists_frame_La : ∃ (F : Frame Q) (c₁ c₂ : K), c₁ * c₁ = 1 ∧ c₂ * c₂ = 1 ∧
    (∀ v, F.La sl2I v = c₁ • (x : V ≃ₗ[K] V) v) ∧
      ∀ v, F.La (sl2J c.three) v = c₂ • (y : V ≃ₗ[K] V) v := by
  obtain ⟨c₁, c₂, hc₁0, hc₂0, hc₁, hc₂, hXp, hYp⟩ := c.plus_scalars
  have hodd : Odd (Nat.card K) := by rw [c.card]; decide
  have : Invertible (2 : K) := invertibleOfNonzero c.two
  have hP : (Q.restrict (minusSp (↑x * ↑x : V ≃ₗ[K] V))).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict c.nondeg_minus)
  obtain ⟨v₀, hv₀, hQv₀⟩ := exists_mem_eq_unit hodd hP c.minus_ge_two 1
  set X₁ := smulEquiv c₁ hc₁0 (x : V ≃ₗ[K] V) with hX₁
  set Y₁ := smulEquiv c₂ hc₂0 (y : V ≃ₗ[K] V) with hY₁
  have hmapX : ∀ v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V), (x : V ≃ₗ[K] V) v ∈
      minusSp (↑x * ↑x : V ≃ₗ[K] V) := fun v hv => map_mem_minusSp (xrho x) hv
  have hmapY : ∀ v ∈ minusSp (↑x * ↑x : V ≃ₗ[K] V), (y : V ≃ₗ[K] V) v ∈
      minusSp (↑x * ↑x : V ≃ₗ[K] V) := fun v hv => map_mem_minusSp c.yrhoV hv
  have hq : QuatQuad Q (minusSp (↑x * ↑x : V ≃ₗ[K] V)) X₁ Y₁ v₀ := by
    refine ⟨smulEquiv_mem hc₁0 hc₁ (orthDerived_le x.2),
      smulEquiv_mem hc₂0 hc₂ (orthDerived_le y.2), fun v hv => ?_, fun v hv => ?_,
      fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, hv₀, by rw [hQv₀]; rfl⟩
    · rw [hX₁, smulEquiv_apply]
      exact Submodule.smul_mem _ _ (hmapX v hv)
    · rw [hY₁, smulEquiv_apply]
      exact Submodule.smul_mem _ _ (hmapY v hv)
    · obtain ⟨h1, -, -⟩ := quat_rels c.hYY c.hYX hv
      rw [hX₁, smulEquiv_apply, smulEquiv_apply, map_smul, smul_smul, hc₁, one_smul, h1]
    · obtain ⟨-, h2, -⟩ := quat_rels c.hYY c.hYX hv
      rw [hY₁, smulEquiv_apply, smulEquiv_apply, map_smul, smul_smul, hc₂, one_smul, h2]
    · obtain ⟨-, -, h3⟩ := quat_rels c.hYY c.hYX hv
      rw [hX₁, hY₁, smulEquiv_apply, smulEquiv_apply, smulEquiv_apply, smulEquiv_apply,
        map_smul, map_smul, h3]
      simp only [smul_neg, smul_smul, mul_comm c₂ c₁]
  obtain ⟨F, hspan, hXF, hYF⟩ := exists_frame_of_quat c.three hq
  have hspanEq : F.span = minusSp (↑x * ↑x : V ≃ₗ[K] V) :=
    Submodule.eq_of_le_of_finrank_le hspan (by rw [Frame.finrank_span]; exact c.minus_le_four)
  have hperp : ∀ p ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), F.coords p = 0 := fun p hp =>
    (Frame.mem_perp_iff F).mp ((Frame.mem_perp_iff_forall_incl F).mpr fun M =>
      polar_plusSp_minusSp c.two (rho_mem x) hp (hspanEq ▸ ⟨M, rfl⟩))
  have key : ∀ (A' : SL(2, K)) (G : V ≃ₗ[K] V) (cG : K),
      (∀ M, G (F.incl M) = F.incl ((A' : Matrix (Fin 2) (Fin 2) K) * M)) →
      (∀ p ∈ plusSp (↑x * ↑x : V ≃ₗ[K] V), G p = p) → ∀ v, F.La A' v = G v := by
    intro A' G _ hG hGp v
    obtain ⟨p, hp, q, hq', rfl⟩ := exists_add_eq c.two c.rhoV v
    rw [map_add, map_add, Frame.La_apply_of_coords_eq_zero F A' (hperp p hp), hGp p hp]
    rw [← hspanEq] at hq'
    obtain ⟨M, rfl⟩ := hq'
    rw [Frame.La_apply_incl, hG]
  refine ⟨F, c₁, c₂, hc₁, hc₂, fun v => ?_, fun v => ?_⟩
  · rw [key sl2I X₁ c₁ hXF (fun p hp => by
      rw [hX₁, smulEquiv_apply, hXp p hp, smul_smul, hc₁, one_smul]) v, hX₁, smulEquiv_apply]
  · rw [key (sl2J c.three) Y₁ c₂ hYF (fun p hp => by
      rw [hY₁, smulEquiv_apply, hYp p hp, smul_smul, hc₂, one_smul]) v, hY₁, smulEquiv_apply]

omit [Finite K] [FiniteDimensional K V] in
theorem theta_eq_of_smul {G : V ≃ₗ[K] V} (hG : G ∈ orthDerived Q) {T : ↥(orthDerived Q)}
    {c₀ : K} (h : ∀ v, G v = c₀ • (T : V ≃ₗ[K] V) v) : θ ⟨G, hG⟩ = θ T := by
  have hk : (⟨G, hG⟩ : ↥(orthDerived Q)) * T⁻¹ ∈ θ.ker := by
    rw [c.ker, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_scalars.mpr ⟨c₀, fun v => ?_⟩
    rw [LinearEquiv.mul_apply, h, LinearEquiv.apply_inv_apply']
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
  exact hk

theorem exists_frame : ∃ F : Frame Q, A = frameMember θ F ∧ r = frameInv θ F := by
  obtain ⟨F, c₁, c₂, hc₁, hc₂, hI, hJ⟩ := c.exists_frame_La
  have hIc : (sl2I : SL(2, K)) ∈ commutator SL(2, K) :=
    (mem_commutator_sl2_iff c.card).mpr sl2I_pow_four
  have hJc : sl2J c.three ∈ commutator SL(2, K) :=
    (mem_commutator_sl2_iff c.card).mpr (sl2J_pow_four c.three)
  have hx : θ ⟨F.La sl2I, frameQ8_le F (La_mem_frameQ8 F hIc)⟩ = Lift.genX e := by
    rw [c.theta_eq_of_smul _ hI, c.lift_x]
  have hy : θ ⟨F.La (sl2J c.three), frameQ8_le F (La_mem_frameQ8 F hJc)⟩ = Lift.genY e := by
    rw [c.theta_eq_of_smul _ hJ, c.lift_y]
  have hle : A ≤ frameMember θ F := Lift.le_of_mem e (hx ▸ La_mem_frameMember θ F hIc)
    (hy ▸ La_mem_frameMember θ F hJc)
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  have : Finite ↥(frameMember θ F) :=
    Finite.of_surjective _ (MonoidHom.subgroupMap_surjective θ _)
  refine ⟨F, Subgroup.eq_of_le_of_card_ge hle ?_, ?_⟩
  · rw [Lift.natCard_eq e]
    exact natCard_frameMember_le c.card θ F
  · rw [← c.theta_rho]
    show θ (x * x) = θ ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩
    congr 1
    apply Subtype.ext
    show (↑x * ↑x : V ≃ₗ[K] V) = F.La (-1)
    refine LinearEquiv.ext fun v => ?_
    have h1 : F.La (-1) = F.La sl2I * F.La sl2I := by rw [← map_mul, ← pow_two, sl2I_sq]
    rw [h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hI v, map_smul, hI, smul_smul, hc₁,
      one_smul]

end Ctx

theorem exists_frame_of_quatTwinDatum (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hn : 7 ≤ Module.finrank K V) (θ : ↥(orthDerived Q) →* S) (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) {A : Subgroup S} {r : S}
    (hd : QuatTwinDatum A r) : ∃ F : Frame Q, A = frameMember θ F ∧ r = frameInv θ F := by
  obtain ⟨e⟩ := hd.q8
  obtain ⟨x, hx⟩ := hθ (Lift.genX e)
  obtain ⟨y, hy⟩ := hθ (Lift.genY e)
  exact (Ctx.mk hK hQ hn hker hd hx hy).exists_frame

theorem frameMember_mem_conjClass_frameMember (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (θ : ↥(orthDerived Q) →* S) (F F' : Frame Q) :
    frameMember θ F' ∈ CoreAssembly.conjClass (frameMember θ F) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero' hK)
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hperp : 2 ≤ Module.finrank K F.perp := by
    have := finrank_perp_add_four F
    omega
  obtain ⟨s, hs⟩ := exists_spin_conj hodd hQ F F' hperp
  have hgE : spinAction Q s ∈ elementaryGroup Q :=
    range_spinAction_le_elementaryGroup hQ F.orth ⟨s, rfl⟩
  have hgΩ := elementaryGroup_le_orthDerived hK hQ hgE
  exact ⟨θ ⟨_, hgΩ⟩, (frameMember_eq_conjSub θ hgΩ hs).symm⟩

section Inv

omit [Finite K] in
theorem La_eq_one_of_mem_scalars (hn : 5 ≤ Module.finrank K V) (F : Frame Q) {g : SL(2, K)}
    (hg : F.La g ∈ scalars K V) : F.La g = 1 := by
  obtain ⟨c₀, hc₀⟩ := mem_scalars.mp hg
  have hperp : F.perp ≠ ⊥ := by
    intro h
    have := finrank_perp_add_four F
    rw [h, finrank_bot] at this
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have h1 : c₀ = 1 := by
    have h2 := hc₀ p
    rw [Frame.La_apply_of_coords_eq_zero F g ((Frame.mem_perp_iff F).mp hp)] at h2
    have h3 : (1 : K) • p = c₀ • p := by rw [one_smul]; exact h2
    exact (smul_left_injective K hp0 h3).symm
  exact LinearEquiv.ext fun v => by rw [hc₀, h1, one_smul]; rfl

theorem isUniqueInvolution_frameMember (hK : Nat.card K = 3) (hn : 5 ≤ Module.finrank K V)
    (θ : ↥(orthDerived Q) →* S)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) (F : Frame Q) :
    IsUniqueInvolution (frameMember θ F) (frameInv θ F) := by
  have hneg : (-1 : SL(2, K)) ∈ commutator SL(2, K) :=
    (mem_commutator_sl2_iff hK).mpr (by rw [show 4 = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow])
  have hker1 : ∀ {g : SL(2, K)} (hg : F.La g ∈ orthDerived Q), θ ⟨F.La g, hg⟩ = 1 → g = 1 := by
    intro g hg h1
    have h2 : (⟨F.La g, hg⟩ : ↥(orthDerived Q)) ∈ θ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact F.La_injective ((La_eq_one_of_mem_scalars hn F h2).trans (map_one F.La).symm)
  refine ⟨La_mem_frameMember θ F hneg, fun h => ?_, ?_, fun y hy hyy => ?_⟩
  · have := hker1 (La_neg_one_mem_orthDerived F) h
    have h3 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h3
    exact two_ne_zero' hK (by linear_combination -h3)
  · rw [frameInv, ← map_mul]
    have : (⟨F.La (-1), La_neg_one_mem_orthDerived F⟩ : ↥(orthDerived Q)) *
        ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩ = 1 :=
      Subtype.ext (F.La_neg_one_mul_self)
    rw [this, map_one]
  · obtain ⟨g, hg, rfl⟩ := (mem_frameMember_iff θ F).mp hy
    have hg2 : g * g = 1 := by
      refine hker1 (frameQ8_le F (La_mem_frameQ8 F (mul_mem hg hg))) ?_
      rw [← hyy, ← map_mul]
      congr 1
      exact Subtype.ext (map_mul F.La g g)
    rcases eq_one_or_neg_one hK (by rw [pow_two]; exact hg2) with h | h
    · left
      subst h
      rw [← map_one θ]
      congr 1
      exact Subtype.ext (map_one F.La)
    · right
      subst h
      rfl

theorem frameMember_swap_ne (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hn : 5 ≤ Module.finrank K V) (θ : ↥(orthDerived Q) →* S)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) (F : Frame Q) :
    frameMember θ F.swap ≠ frameMember θ F := by
  intro h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hIc : (sl2I : SL(2, K)) ∈ commutator SL(2, K) :=
    (mem_commutator_sl2_iff hK).mpr sl2I_pow_four
  have hI := La_mem_frameMember θ F hIc
  rw [← h] at hI
  obtain ⟨g, hg, hgeq⟩ := (mem_frameMember_iff θ F.swap).mp hI
  obtain ⟨l, -, hl⟩ := exists_smul_of_map_eq hQ hker hgeq
  have hperp : F.perp ≠ ⊥ := by
    intro h0
    have := finrank_perp_add_four F
    rw [h0, finrank_bot] at this
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have hp' : F.swap.coords p = 0 := (Frame.mem_perp_iff F.swap).mp (F.perp_swap ▸ hp)
  have heq : F.La sl2I = F.swap.La g := by
    refine eq_of_smul_of_apply_eq (m := F.swap.La g) (m' := F.La sl2I) hl (v := p) ?_ ?_
    · rw [Frame.La_apply_of_coords_eq_zero _ g hp']
      exact hp0
    · rw [Frame.La_apply_of_coords_eq_zero _ g hp',
        Frame.La_apply_of_coords_eq_zero F _ ((Frame.mem_perp_iff F).mp hp)]
  rcases (Frame.La_mem_swap_range_iff F sl2I).mp ⟨g, heq.symm⟩ with h1 | h1
  · have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp [coe_sl2I] at this
  · have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp [coe_sl2I] at this

end Inv

end CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

module

public import CFSG.GF2Type.Smith1979W3.Cert690.Q0
public import CFSG.GF2Type.Smith1979W3.MbarModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690
  CFSG.RankThree.Literature.FSmith QuadraticMap

variable {G : Type} [Group G] [Finite G] (S : Setting G) (φ : S.Q ≃* Q0)

noncomputable def rhoQ0 (y : S.M) : Q0 ≃* Q0 :=
  φ.symm.trans ((conjAut S.normal y⁻¹).trans φ)

theorem coe_symm_rhoQ0_apply (y : S.M) (x : S.Q) :
    ((φ.symm (rhoQ0 S φ y (φ x)) : S.Q) : S.M) = y⁻¹ * x * y := by
  dsimp only [rhoQ0]
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, conjAut_apply, inv_inv]

private theorem symm_rhoQ0_apply (y : S.M) (x : S.Q) :
    φ.symm (rhoQ0 S φ y (φ x)) = conjAut S.normal y⁻¹ x := by
  apply Subtype.ext
  rw [coe_symm_rhoQ0_apply, conjAut_apply, inv_inv]

private theorem rhoQ0_apply_phi (y : S.M) (x : S.Q) :
    rhoQ0 S φ y (φ x) = φ (conjAut S.normal y⁻¹ x) := by
  have h := congrArg φ (symm_rhoQ0_apply S φ y x)
  rwa [MulEquiv.apply_symm_apply] at h

theorem rhoQ0_one : rhoQ0 S φ 1 = 1 := by
  refine MulEquiv.ext fun x => ?_
  dsimp only [rhoQ0]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : conjAut S.normal ((1 : S.M)⁻¹) = 1 := by
    refine MulEquiv.ext fun z => Subtype.ext ?_
    rw [conjAut_apply]
    simp
  rw [h1, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]

theorem rhoQ0_mul (y y' : S.M) :
    rhoQ0 S φ y * rhoQ0 S φ y' = rhoQ0 S φ (y' * y) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨w, rfl⟩ : ∃ w : S.Q, φ w = z := ⟨φ.symm z, MulEquiv.apply_symm_apply φ z⟩
  apply φ.symm.injective
  rw [MulAut.mul_apply, rhoQ0_apply_phi, rhoQ0_apply_phi, MulEquiv.symm_apply_apply,
    symm_rhoQ0_apply]
  apply Subtype.ext
  rw [conjAut_apply, conjAut_apply, conjAut_apply, mul_inv_rev]
  group

theorem phi_zQ : φ S.zQ = z0 := by
  have hmem : φ S.zQ ∈ Subgroup.center Q0 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp S.zQ_mem_center x]
  have hv : (φ S.zQ).v = 0 := by
    rw [center_eq_Q0Z, mem_Q0Z_iff] at hmem
    exact hmem
  have hne : φ S.zQ ≠ 1 := by
    intro h
    exact S.zQ_ne_one (φ.injective (h.trans (map_one φ).symm))
  apply Q0.ext
  · rcases zmod2_cases (φ S.zQ).a with h | h
    · exfalso
      apply hne
      exact Q0.ext (by simpa using h) (by simpa using hv)
    · simpa [z0] using h
  · simpa [z0] using hv

theorem rhoQ0_eq_rhoQ0_iff {y y' : S.M} :
    rhoQ0 S φ y' = rhoQ0 S φ y ↔ y' = y ∨ y' = y * S.zM := by
  constructor
  · intro h
    have hact : ∀ x : S.Q, (y'⁻¹ * x * y' : S.M) = y⁻¹ * x * y := by
      intro x
      have h1 := coe_symm_rhoQ0_apply S φ y' x
      have h2 := coe_symm_rhoQ0_apply S φ y x
      rw [h] at h1
      exact h1.symm.trans h2
    have hcent : y' * y⁻¹ ∈ Subgroup.centralizer (S.Q : Set S.M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' := hact ⟨x, hx⟩
      calc x * (y' * y⁻¹) = y' * (y'⁻¹ * x * y') * y⁻¹ := by group
        _ = y' * (y⁻¹ * x * y) * y⁻¹ := by rw [hx']
        _ = (y' * y⁻¹) * x := by group
    have hmQ : y' * y⁻¹ ∈ S.Q := S.centralizer_le hcent
    have hmcenter : (⟨y' * y⁻¹, hmQ⟩ : S.Q) ∈ Subgroup.center S.Q := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hcent) (x : S.M) x.2
    rcases S.mem_center_Q_iff.mp hmcenter with h1 | h2
    · left
      have hm : y' * y⁻¹ = 1 := by
        simpa using congrArg (fun q : S.Q => (q : S.M)) h1
      calc y' = (y' * y⁻¹) * y := by group
        _ = y := by rw [hm, one_mul]
    · right
      have hm : y' * y⁻¹ = (S.zQ : S.M) := by
        simpa using congrArg (fun q : S.Q => (q : S.M)) h2
      have hzQ : (S.zQ : S.M) = S.zM := rfl
      calc y' = (y' * y⁻¹) * y := by group
        _ = (S.zQ : S.M) * y := by rw [hm]
        _ = S.zM * y := by rw [hzQ]
        _ = y * S.zM := (Subgroup.mem_center_iff.mp S.zM_mem_center y).symm
  · rintro (rfl | rfl)
    · rfl
    · have hz2 : S.zM * S.zM = 1 := by
        apply Subtype.ext
        exact S.z_mul_z
      have hz : S.zM⁻¹ = S.zM := inv_eq_of_mul_eq_one_right hz2
      have hz' : ((y * S.zM)⁻¹ : S.M) = S.zM * y⁻¹ := by
        rw [mul_inv_rev, hz]
      refine MulEquiv.ext fun z => ?_
      dsimp only [rhoQ0]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hz']
      have hcomm : conjAut S.normal (S.zM * y⁻¹) = conjAut S.normal y⁻¹ := by
        refine MulEquiv.ext fun x => Subtype.ext ?_
        rw [conjAut_apply, conjAut_apply]
        have hcommA : ((y⁻¹ * (x : S.M) * y) * S.zM) =
            S.zM * (y⁻¹ * (x : S.M) * y) :=
          Subgroup.mem_center_iff.mp S.zM_mem_center _
        calc S.zM * y⁻¹ * (x : S.M) * (S.zM * y⁻¹)⁻¹
            = S.zM * (y⁻¹ * (x : S.M) * y) * S.zM := by
              rw [mul_inv_rev, hz]
              group
          _ = y⁻¹ * (x : S.M) * (y⁻¹)⁻¹ := by
              rw [mul_assoc, hcommA, ← mul_assoc, hz2, one_mul, inv_inv]
      rw [hcomm]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply]

theorem rhoQ0_coe (e : S.Q) : rhoQ0 S φ e = inn (φ e) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨w, rfl⟩ : ∃ w : S.Q, φ w = z := ⟨φ.symm z, MulEquiv.apply_symm_apply φ z⟩
  apply φ.symm.injective
  rw [symm_rhoQ0_apply]
  have h : inn (φ e) (φ w) = φ (e⁻¹ * w * e) := by
    rw [inn, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul]
  rw [h, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [conjAut_apply, inv_inv]
  simp

theorem rhoQ0_apply_eq_iff (y : S.M) (x : S.Q) :
    rhoQ0 S φ y (φ x) = φ x ↔ (x : S.M) * y = y * x := by
  constructor
  · intro h
    have h' : y⁻¹ * (x : S.M) * y = (x : S.M) := by
      have h1 := coe_symm_rhoQ0_apply S φ y x
      rw [h, MulEquiv.symm_apply_apply] at h1
      exact h1.symm
    calc (x : S.M) * y = y * (y⁻¹ * (x : S.M) * y) := by group
      _ = y * (x : S.M) := by rw [h']
  · intro h
    have h' : y⁻¹ * (x : S.M) * y = (x : S.M) := by
      calc y⁻¹ * (x : S.M) * y = y⁻¹ * ((x : S.M) * y) := by group
        _ = y⁻¹ * (y * (x : S.M)) := by rw [← h]
        _ = (x : S.M) := by group
    apply φ.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [coe_symm_rhoQ0_apply]
    exact h'

theorem v_rhoQ0 {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) (y : S.M) (x : Q0) :
    (rhoQ0 S φ y x).v = conjL L ↑(S.ρ y⁻¹) x.v := by
  obtain ⟨x', rfl⟩ : ∃ x' : S.Q, φ x' = x := ⟨φ.symm x, MulEquiv.apply_symm_apply φ x⟩
  rw [rhoQ0_apply_phi, hφ, hφ x', conjL_apply, LinearEquiv.symm_apply_apply, S.ρ_toQt]

theorem v_φ_conjAut {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) (w : S.M) (x : S.Q) :
    (φ (conjAut S.normal w x)).v = conjL L ↑(S.ρ w) (φ x).v := by
  rw [hφ, hφ x, conjL_apply, LinearEquiv.symm_apply_apply, S.ρ_toQt]

private theorem beta0_add_left (u v w : V₀) : beta0 (u + v) w = beta0 u w + beta0 v w := by
  simp only [beta0, Pi.add_apply]
  ring

private theorem inn_a (e x : Q0) :
    (inn e x).a = x.a + beta0 e.v x.v + beta0 x.v e.v := by
  have h1 : (e⁻¹ * x).a = e.a + beta0 e.v e.v + x.a + beta0 e.v x.v := by
    rw [mul_a, inv_a, inv_v]
  have h2 : (e⁻¹ * x * e).a = (e⁻¹ * x).a + e.a + beta0 (e.v + x.v) e.v := by
    rw [mul_a, mul_v, inv_v]
  rw [inn, MulAut.conj_apply, inv_inv, h2, h1, beta0_add_left]
  have hzero : (e.a + e.a) + (beta0 e.v e.v + beta0 e.v e.v) = 0 := by
    rw [CharTwo.add_self_eq_zero e.a, CharTwo.add_self_eq_zero (beta0 e.v e.v), add_zero]
  rw [show e.a + beta0 e.v e.v + x.a + beta0 e.v x.v + e.a +
      (beta0 e.v e.v + beta0 x.v e.v) =
      x.a + beta0 e.v x.v + beta0 x.v e.v +
        ((e.a + e.a) + (beta0 e.v e.v + beta0 e.v e.v)) by abel,
    hzero, add_zero]

private theorem inn_v (e x : Q0) : (inn e x).v = x.v := by
  rw [inn, MulAut.conj_apply, inv_inv]
  simp only [mul_v, inv_v]
  rw [add_comm (e.v) (x.v), add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem inn_apply (e x : Q0) :
    inn e x = ⟨x.a + beta0 e.v x.v + beta0 x.v e.v, x.v⟩ :=
  Q0.ext (inn_a e x) (inn_v e x)

private theorem inn_apply_polar (e x : Q0) :
    inn e x = ⟨x.a + polar qPlus e.v x.v, x.v⟩ := by
  rw [inn_apply]
  apply Q0.ext
  · rw [← polar_qPlus_eq_beta0_add]
    abel_nf
  · rfl

theorem exists_eq_inn_of_forall_v_eq {α : Q0 ≃* Q0} (h : ∀ x, (α x).v = x.v) :
    ∃ e : Q0, α = inn e := by
  classical
  let f : V₀ → ZMod 2 := fun v => (α ⟨0, v⟩).a
  have hcenter : ∀ c : Q0, c ∈ Subgroup.center Q0 → α c = c := fun c hc =>
    CFSG.GroupTheory.mulAut_apply_eq_of_mem_center (by rw [center_eq_Q0Z, card_Q0Z]) α hc
  have hα : ∀ x : Q0, α x = ⟨x.a + f x.v, x.v⟩ := by
    intro x
    have hx : x = (⟨x.a, 0⟩ : Q0) * ⟨0, x.v⟩ := by
      ext <;> simp [beta0]
    rw [hx, map_mul]
    have h1 : α (⟨x.a, 0⟩ : Q0) = ⟨x.a, 0⟩ :=
      hcenter _ (by rw [center_eq_Q0Z, mem_Q0Z_iff])
    have h2 : α (⟨0, x.v⟩ : Q0) = ⟨f x.v, x.v⟩ := by
      apply Q0.ext
      · rfl
      · exact h ⟨0, x.v⟩
    rw [h1, h2]
    ext <;> simp [beta0]
  have hfadd : ∀ u v : V₀, f (u + v) = f u + f v := by
    intro u v
    have h1 : (α ((⟨0, u⟩ : Q0) * ⟨0, v⟩)).a = f u + f v + beta0 u v := by
      rw [map_mul, hα, hα]
      simp [beta0]
    have h2 : (α ((⟨0, u⟩ : Q0) * ⟨0, v⟩)).a = beta0 u v + f (u + v) := by
      have hmul : (⟨0, u⟩ : Q0) * ⟨0, v⟩ = (⟨beta0 u v, 0⟩ : Q0) * ⟨0, u + v⟩ := by
        ext <;> simp [beta0]
      rw [hmul, map_mul]
      have h1' : α (⟨beta0 u v, 0⟩ : Q0) = ⟨beta0 u v, 0⟩ :=
        hcenter _ (by rw [center_eq_Q0Z, mem_Q0Z_iff])
      rw [h1', hα]
      simp [beta0]
    have hEq : beta0 u v + f (u + v) = f u + f v + beta0 u v := h2.symm.trans h1
    have hEq' : beta0 u v + f (u + v) = beta0 u v + (f u + f v) := by
      rw [hEq, add_comm (f u + f v) (beta0 u v)]
    exact add_left_cancel hEq'
  have hf0 : f 0 = 0 := by
    have h1 := hα (1 : Q0)
    rw [map_one] at h1
    have h2 := congrArg Q0.a h1
    simpa using h2.symm
  let Fadd : V₀ →+ ZMod 2 :=
    { toFun := f, map_zero' := hf0, map_add' := hfadd }
  let F : Module.Dual (ZMod 2) V₀ := Fadd.toZModLinearMap 2
  let w : V₀ :=
    (LinearMap.BilinForm.toDual (polarBilin qPlus) qPlus_nondegenerate).symm F
  have hw : ∀ v : V₀, polar qPlus w v = f v := by
    intro v
    have h1 := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := polarBilin qPlus) (hB := qPlus_nondegenerate) F v
    rw [show (LinearMap.BilinForm.toDual (polarBilin qPlus) qPlus_nondegenerate).symm F
      = w from rfl] at h1
    simp only [polarBilin_apply_apply] at h1
    exact h1
  refine ⟨⟨0, w⟩, ?_⟩
  refine MulEquiv.ext fun x => ?_
  rw [hα x, inn_apply_polar, hw]

theorem exists_rhoQ0_eq {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x))
    {ψ : Q0 ≃* Q0} (hψ : ψ ∈ XOver (mbarModel S L)) :
    ∃ y : S.M, rhoQ0 S φ y = ψ := by
  classical
  obtain ⟨g, hgK, hgv⟩ := hψ
  obtain ⟨m, hm⟩ := (mem_mbarModel_iff S L).mp hgK
  have hρ : ∀ x : Q0, (rhoQ0 S φ m⁻¹ x).v = g x.v := by
    intro x
    rw [v_rhoQ0 S φ hφ, inv_inv, ← hm]
  have hαv : ∀ x : Q0, ((ψ * (rhoQ0 S φ m⁻¹)⁻¹) x).v = x.v := by
    intro x
    rw [MulAut.mul_apply, hgv]
    have hx : rhoQ0 S φ m⁻¹ ((rhoQ0 S φ m⁻¹)⁻¹ x) = x :=
      MulAut.apply_inv_self (M := Q0) (rhoQ0 S φ m⁻¹) x
    have h := hρ ((rhoQ0 S φ m⁻¹)⁻¹ x)
    rw [hx] at h
    exact h.symm
  obtain ⟨e, he⟩ := exists_eq_inn_of_forall_v_eq hαv
  refine ⟨m⁻¹ * (φ.symm e : S.Q), ?_⟩
  have hco : rhoQ0 S φ (φ.symm e : S.Q) = inn e := by
    simpa using rhoQ0_coe S φ (φ.symm e)
  have hψeq : ψ = inn e * rhoQ0 S φ m⁻¹ := by
    calc ψ = (ψ * (rhoQ0 S φ m⁻¹)⁻¹) * rhoQ0 S φ m⁻¹ := by group
      _ = inn e * rhoQ0 S φ m⁻¹ := by rw [he]
  rw [hψeq, ← hco, ← rhoQ0_mul]

theorem rhoQ0_mem_ThetaOver_iff {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) (y : S.M) :
    rhoQ0 S φ y ∈ ThetaOver (mbarModel S L) ↔ y * y ∈ S.Q := by
  constructor
  · rintro ⟨g, hgK, hgg, hgv⟩
    have hg_eq : g = conjL L (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨x, rfl⟩ : ∃ x : Q0, x.v = v := ⟨⟨0, v⟩, rfl⟩
      rw [← hgv x, v_rhoQ0 S φ hφ y x]
    rw [hg_eq] at hgg
    have hρlin : (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
      apply (conjL L).injective
      rw [map_mul, map_one]
      exact hgg
    have hρ : S.ρ y⁻¹ * S.ρ y⁻¹ = 1 := Subtype.ext hρlin
    have hρ' : S.ρ (y⁻¹ * y⁻¹) = 1 := by
      rw [map_mul]
      exact hρ
    have hyQ : y⁻¹ * y⁻¹ ∈ S.Q := by
      rw [← S.ker_ρ, MonoidHom.mem_ker]
      exact hρ'
    have hsq : y * y = (y⁻¹ * y⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv]
    rw [hsq]
    exact S.Q.inv_mem hyQ
  · intro hy
    have hyinv : y⁻¹ * y⁻¹ ∈ S.Q := by
      have hsq : y⁻¹ * y⁻¹ = (y * y)⁻¹ := by simp only [mul_inv_rev, inv_inv]
      rw [hsq]
      exact S.Q.inv_mem hy
    have hρ1 : S.ρ (y⁻¹ * y⁻¹) = 1 := S.ρ_eq_one_of_mem_Q hyinv
    have hρ1' : (↑(S.ρ (y⁻¹ * y⁻¹)) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
      simpa using congrArg (fun o : S.O => (o : S.Qt ≃ₗ[ZMod 2] S.Qt)) hρ1
    have hgg : conjL L (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        conjL L (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
      have hcoe : (↑(S.ρ y⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ↑(S.ρ y⁻¹) =
          ↑(S.ρ (y⁻¹ * y⁻¹)) := by
        rw [← Subgroup.coe_mul, ← map_mul]
      rw [← map_mul, hcoe, hρ1', map_one]
    exact ⟨conjL L ↑(S.ρ y⁻¹), conjL_ρ_mem_mbarModel S L y⁻¹, hgg,
      fun x => v_rhoQ0 S φ hφ y x⟩

private theorem rhoQ0_conj (m y : S.M) :
    rhoQ0 S φ m * rhoQ0 S φ y * (rhoQ0 S φ m)⁻¹ =
      rhoQ0 S φ (m⁻¹ * y * m) := by
  have hinv : (rhoQ0 S φ m)⁻¹ = rhoQ0 S φ m⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [rhoQ0_mul, inv_mul_cancel, rhoQ0_one]
  rw [hinv, rhoQ0_mul, rhoQ0_mul]
  exact congrArg (rhoQ0 S φ) (by group)

theorem exists_rhoQ0_mul_eq {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) (y : S.M) {θ : Q0 ≃* Q0}
    (hθ : ∀ e, (θ e).v = (rhoQ0 S φ y e).v) :
    ∃ x : S.Q, rhoQ0 S φ (y * x) = θ := by
  classical
  have hαv : ∀ e : Q0, ((θ * (rhoQ0 S φ y)⁻¹) e).v = e.v := by
    intro e
    rw [MulAut.mul_apply, hθ ((rhoQ0 S φ y)⁻¹ e)]
    exact congrArg Q0.v (MulAut.apply_inv_self (M := Q0) (rhoQ0 S φ y) e)
  obtain ⟨e, he⟩ := exists_eq_inn_of_forall_v_eq hαv
  refine ⟨φ.symm e, ?_⟩
  have hco : rhoQ0 S φ (φ.symm e : S.Q) = inn e := by
    simpa using rhoQ0_coe S φ (φ.symm e)
  have hθeq : θ = inn e * rhoQ0 S φ y := by
    calc θ = (θ * (rhoQ0 S φ y)⁻¹) * rhoQ0 S φ y := by group
      _ = inn e * rhoQ0 S φ y := by rw [he]
  rw [hθeq, ← hco, ← rhoQ0_mul]

noncomputable def sqData (S : Setting G) (φ : S.Q ≃* Q0) : (Q0 ≃* Q0) → Q0 := by
  classical
  exact fun θ =>
    if h : ∃ y : S.M, rhoQ0 S φ y = θ ∧ y * y ∈ S.Q then
      φ ⟨h.choose * h.choose, h.choose_spec.2⟩
    else 1

theorem sqData_rhoQ0 {y : S.M} (hy : y * y ∈ S.Q) :
    sqData S φ (rhoQ0 S φ y) = φ ⟨y * y, hy⟩ := by
  classical
  have hex : ∃ y' : S.M, rhoQ0 S φ y' = rhoQ0 S φ y ∧ y' * y' ∈ S.Q := ⟨y, rfl, hy⟩
  unfold sqData
  rw [dif_pos hex]
  have hz2 : S.zM * S.zM = 1 := by
    apply Subtype.ext
    exact S.z_mul_z
  have hcomm : ∀ g : S.M, g * S.zM = S.zM * g := fun g =>
    Subgroup.mem_center_iff.mp S.zM_mem_center g
  have hsq : hex.choose * hex.choose = y * y := by
    rcases (rhoQ0_eq_rhoQ0_iff S φ).mp hex.choose_spec.1 with h1 | h1
    · rw [h1]
    · rw [h1]
      calc (y * S.zM) * (y * S.zM) = y * (S.zM * y) * S.zM := by group
        _ = y * (y * S.zM) * S.zM := by rw [hcomm y]
        _ = (y * y) * (S.zM * S.zM) := by group
        _ = y * y := by rw [hz2, mul_one]
  exact congrArg φ (Subtype.ext hsq)

theorem isSquareData {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) :
    IsSquareData (mbarModel S L) (sqData S φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hy : (1 : S.M) * 1 ∈ S.Q := by simp
    rw [← rhoQ0_one S φ, sqData_rhoQ0 S φ hy]
    simp
  · intro θ hθ
    have hθT : θ ∈ ThetaOver (mbarModel S L) := hθ
    obtain ⟨g, hgK, hgg, hgv⟩ := hθ
    have hX : θ ∈ XOver (mbarModel S L) := ⟨g, hgK, hgv⟩
    obtain ⟨y, hyθ⟩ := exists_rhoQ0_eq S φ hφ hX
    have hyQ : y * y ∈ S.Q := by
      rw [← rhoQ0_mem_ThetaOver_iff S φ hφ y, hyθ]
      exact hθT
    have hσ : sqData S φ θ = φ ⟨y * y, hyQ⟩ := by
      rw [← hyθ, sqData_rhoQ0 S φ hyQ]
    rw [hσ, ← hyθ, rhoQ0_mul]
    simpa using rhoQ0_coe S φ ⟨y * y, hyQ⟩
  · intro θ hθ ψ hψ
    have hθT : θ ∈ ThetaOver (mbarModel S L) := hθ
    obtain ⟨g, hgK, hgg, hgv⟩ := hθ
    have hX : θ ∈ XOver (mbarModel S L) := ⟨g, hgK, hgv⟩
    obtain ⟨y, hyθ⟩ := exists_rhoQ0_eq S φ hφ hX
    have hyQ : y * y ∈ S.Q := by
      rw [← rhoQ0_mem_ThetaOver_iff S φ hφ y, hyθ]
      exact hθT
    obtain ⟨m, hmψ⟩ := exists_rhoQ0_eq S φ hφ hψ
    have hmyQ : (m⁻¹ * y * m) * (m⁻¹ * y * m) ∈ S.Q := by
      have hsq : (m⁻¹ * y * m) * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m := by group
      rw [hsq]
      simpa using S.normal.conj_mem (y * y) hyQ m⁻¹
    have hσ : sqData S φ (ψ * θ * ψ⁻¹) =
        φ ⟨(m⁻¹ * y * m) * (m⁻¹ * y * m), hmyQ⟩ := by
      rw [← hmψ, ← hyθ, rhoQ0_conj, sqData_rhoQ0 S φ hmyQ]
    have hσθ : sqData S φ θ = φ ⟨y * y, hyQ⟩ := by
      rw [← hyθ, sqData_rhoQ0 S φ hyQ]
    rw [hσ, hσθ, ← hmψ, rhoQ0_apply_phi]
    have hq : (⟨(m⁻¹ * y * m) * (m⁻¹ * y * m), hmyQ⟩ : S.Q) =
        conjAut S.normal m⁻¹ ⟨y * y, hyQ⟩ := by
      apply Subtype.ext
      rw [conjAut_apply, inv_inv]
      group
    rw [hq]
  · intro θ hθ e
    have hθT : θ ∈ ThetaOver (mbarModel S L) := hθ
    obtain ⟨g, hgK, hgg, hgv⟩ := hθ
    have hX : θ ∈ XOver (mbarModel S L) := ⟨g, hgK, hgv⟩
    obtain ⟨y, hyθ⟩ := exists_rhoQ0_eq S φ hφ hX
    have hyQ : y * y ∈ S.Q := by
      rw [← rhoQ0_mem_ThetaOver_iff S φ hφ y, hyθ]
      exact hθT
    let e' : S.Q := φ.symm e
    have he' : φ e' = e := MulEquiv.apply_symm_apply φ e
    have hzQ : (y * (e' : S.M)) * (y * (e' : S.M)) ∈ S.Q := by
      have hsq : (y * (e' : S.M)) * (y * (e' : S.M)) =
          (y * y) * (y⁻¹ * (e' : S.M) * y) * (e' : S.M) := by group
      rw [hsq]
      exact S.Q.mul_mem (S.Q.mul_mem hyQ (by
        simpa using S.normal.conj_mem (e' : S.M) e'.2 y⁻¹)) e'.2
    have hσ : sqData S φ (inn e * θ) =
        φ ⟨(y * (e' : S.M)) * (y * (e' : S.M)), hzQ⟩ := by
      have heq : inn e * θ = rhoQ0 S φ (y * (e' : S.M)) := by
        rw [← he', ← rhoQ0_coe S φ e', ← hyθ, rhoQ0_mul]
      rw [heq, sqData_rhoQ0 S φ hzQ]
    have hσθ : sqData S φ θ = φ ⟨y * y, hyQ⟩ := by
      rw [← hyθ, sqData_rhoQ0 S φ hyQ]
    have hθe : θ e = φ (conjAut S.normal y⁻¹ e') := by
      rw [← hyθ, ← he']
      exact rhoQ0_apply_phi S φ y e'
    rw [hσ, hσθ, hθe, ← he', ← map_mul, ← map_mul]
    have hq : (⟨(y * (e' : S.M)) * (y * (e' : S.M)), hzQ⟩ : S.Q) =
        (⟨y * y, hyQ⟩ * conjAut S.normal y⁻¹ e') * e' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conjAut_apply, inv_inv]
      group
    rw [hq]

private theorem natCard_eq_two_mul_of_fiber {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hfib : ∀ b : β, Nat.card {a : α // f a = b} = 2) :
    Nat.card α = 2 * Nat.card β := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype β := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card α = Nat.card α := (Nat.card_eq_fintype_card (α := α)).symm
    _ = Nat.card (Σ b : β, {a : α // f a = b}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : β, Nat.card {a : α // f a = b} := Nat.card_sigma
    _ = ∑ _b : β, 2 := by simp [hfib]
    _ = Fintype.card β * 2 := by simp
    _ = 2 * Fintype.card β := Nat.mul_comm _ _

private theorem zM_ne_one : S.zM ≠ 1 := by
  intro h
  exact S.z_ne_one (by simpa using congrArg (fun g : S.M => (g : G)) h)

private theorem zM_mul_self : S.zM * S.zM = 1 := by
  apply Subtype.ext
  exact S.z_mul_z

private theorem zM_comm (g : S.M) : g * S.zM = S.zM * g :=
  Subgroup.mem_center_iff.mp S.zM_mem_center g

private theorem rhoQ0_mul_zM (y : S.M) : rhoQ0 S φ (y * S.zM) = rhoQ0 S φ y :=
  (rhoQ0_eq_rhoQ0_iff S φ).mpr (Or.inr rfl)

private theorem coe_zQ : (S.zQ : S.M) = S.zM := rfl

private theorem ρ_inv_mul_mem_Q (y : S.M) (x : S.Q) :
    (S.ρ ((y * (x : S.M))⁻¹) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (S.ρ y⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hx : S.ρ (x : S.M) = 1 := S.ρ_eq_one_of_mem_Q x.2
  have h : S.ρ ((y * (x : S.M))⁻¹) = S.ρ y⁻¹ := by
    rw [mul_inv_rev, map_mul, map_inv, map_inv, hx, inv_one, one_mul]
  exact congrArg (fun o : S.O => (o : S.Qt ≃ₗ[ZMod 2] S.Qt)) h

theorem card_centralizer_eq_ncard (y : S.M) :
    Nat.card {x : S.Q // (x : S.M) * y = y * x} =
      Set.ncard {e : Q0 | rhoQ0 S φ y e = e} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨φ x.1, (rhoQ0_apply_eq_iff S φ y x.1).mpr x.2⟩
      invFun := fun e => ⟨φ.symm e.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (rhoQ0_apply_eq_iff S φ y (φ.symm e.1)).mp (by
      rw [MulEquiv.apply_symm_apply]
      exact e.2)
  · intro x
    apply Subtype.ext
    exact MulEquiv.symm_apply_apply φ x.1
  · intro e
    apply Subtype.ext
    exact MulEquiv.apply_symm_apply φ e.1

theorem card_sq_eq {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) (a c : S.Q) :
    Nat.card {x : S.M // x * a = a * x ∧ x * x = c} =
      2 * Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (mbarModel S L) ∧ θ (φ a) = φ a ∧ sqData S φ θ = φ c} := by
  classical
  let A : Type := {x : S.M // x * a = a * x ∧ x * x = c}
  let T : Type := {θ : Q0 ≃* Q0 // θ ∈ ThetaOver (mbarModel S L) ∧
    θ (φ a) = φ a ∧ sqData S φ θ = φ c}
  let f : A → T := fun x =>
    let hxQ : x.1 * x.1 ∈ S.Q := by rw [x.2.2]; exact c.2
    ⟨rhoQ0 S φ x.1,
      (rhoQ0_mem_ThetaOver_iff S φ hφ x.1).mpr hxQ,
      (rhoQ0_apply_eq_iff S φ x.1 a).mpr x.2.1.symm,
      by
        rw [sqData_rhoQ0 S φ hxQ]
        exact congrArg φ (Subtype.ext x.2.2)⟩
  have hfib : ∀ θ : T, Nat.card {x : A // f x = θ} = 2 := by
    intro θ
    have hex : ∃ x : A, f x = θ := by
      have hX : θ.1 ∈ XOver (mbarModel S L) := by
        obtain ⟨g, hgK, hgg, hgv⟩ := θ.2.1
        exact ⟨g, hgK, hgv⟩
      obtain ⟨y, hyθ⟩ := exists_rhoQ0_eq S φ hφ hX
      have hyQ : y * y ∈ S.Q := by
        rw [← rhoQ0_mem_ThetaOver_iff S φ hφ y, hyθ]
        exact θ.2.1
      have hya : y * a = a * y := by
        have h := (rhoQ0_apply_eq_iff S φ y a).mp (by rw [hyθ]; exact θ.2.2.1)
        exact h.symm
      have hyc : y * y = (c : S.M) := by
        have h1 : φ (⟨y * y, hyQ⟩ : S.Q) = φ c := by
          rw [← sqData_rhoQ0 S φ hyQ, hyθ]
          exact θ.2.2.2
        exact congrArg (fun q : S.Q => (q : S.M)) (φ.injective h1)
      exact ⟨⟨y, hya, hyc⟩, Subtype.ext hyθ⟩
    let x₀ : A := Classical.choose hex
    have hx₀ : f x₀ = θ := Classical.choose_spec hex
    have hzA : (x₀.1 * S.zM) * a = a * (x₀.1 * S.zM) ∧
        (x₀.1 * S.zM) * (x₀.1 * S.zM) = c := by
      constructor
      · calc (x₀.1 * S.zM) * (a : S.M) = x₀.1 * (S.zM * (a : S.M)) := by rw [mul_assoc]
          _ = x₀.1 * ((a : S.M) * S.zM) := by rw [← zM_comm S (a : S.M)]
          _ = (x₀.1 * (a : S.M)) * S.zM := by rw [mul_assoc]
          _ = ((a : S.M) * x₀.1) * S.zM := by rw [x₀.2.1]
          _ = (a : S.M) * (x₀.1 * S.zM) := by rw [mul_assoc]
      · calc (x₀.1 * S.zM) * (x₀.1 * S.zM)
            = x₀.1 * (S.zM * x₀.1) * S.zM := by group
          _ = x₀.1 * (x₀.1 * S.zM) * S.zM := by rw [← zM_comm S x₀.1]
          _ = (x₀.1 * x₀.1) * (S.zM * S.zM) := by group
          _ = x₀.1 * x₀.1 := by rw [zM_mul_self S, mul_one]
          _ = (c : S.M) := x₀.2.2
    let x₁ : A := ⟨x₀.1 * S.zM, hzA⟩
    have hfx₁ : f x₁ = θ := by
      rw [← hx₀]
      apply Subtype.ext
      exact rhoQ0_mul_zM S φ x₀.1
    have hne : x₁ ≠ x₀ := by
      intro h
      have h' : x₀.1 * S.zM = x₀.1 := congrArg (fun x : A => x.1) h
      have hz1 : S.zM = 1 := by
        have := congrArg (fun g : S.M => x₀.1⁻¹ * g) h'
        simpa using this
      exact zM_ne_one S hz1
    rw [Nat.card_eq_two_iff' ⟨x₀, hx₀⟩]
    refine ⟨⟨x₁, hfx₁⟩, ?_, ?_⟩
    · intro h
      exact hne (congrArg Subtype.val h)
    · intro y hyne
      have hfeq : f y.1 = f x₀ := y.2.trans hx₀.symm
      have hyval : rhoQ0 S φ y.1.1 = rhoQ0 S φ x₀.1 := congrArg Subtype.val hfeq
      rcases (rhoQ0_eq_rhoQ0_iff S φ).mp hyval with h1 | h1
      · exfalso
        apply hyne
        apply Subtype.ext
        apply Subtype.ext
        exact h1
      · apply Subtype.ext
        apply Subtype.ext
        exact h1
  rw [← Nat.card_coe_set_eq]
  exact natCard_eq_two_mul_of_fiber f hfib

theorem card_mul_sq_eq {L : S.Qt ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x : S.Q, (φ x).v = L (S.toQt x)) {y : S.M} (hy : y * y ∈ S.Q)
    (c : S.Q) :
    Nat.card {x : S.Q // (y * (x : S.M)) * (y * (x : S.M)) = c} =
      2 * Set.ncard {θ : Q0 ≃* Q0 |
        (∀ e, (θ e).v = conjL L ↑(S.ρ y⁻¹) e.v) ∧
          sqData S φ θ = φ c} := by
  classical
  let A : Type := {x : S.Q // (y * (x : S.M)) * (y * (x : S.M)) = c}
  let T : Type := {θ : Q0 ≃* Q0 //
    (∀ e, (θ e).v = conjL L ↑(S.ρ y⁻¹) e.v) ∧
      sqData S φ θ = φ c}
  let f : A → T := fun x =>
    let hxQ : (y * (x.1 : S.M)) * (y * (x.1 : S.M)) ∈ S.Q := by rw [x.2]; exact c.2
    ⟨rhoQ0 S φ (y * (x.1 : S.M)),
      by
        intro e
        rw [v_rhoQ0 S φ hφ (y * (x.1 : S.M)) e, ρ_inv_mul_mem_Q S y x.1],
      by
        rw [sqData_rhoQ0 S φ hxQ]
        exact congrArg φ (Subtype.ext x.2)⟩
  have hfib : ∀ θ : T, Nat.card {x : A // f x = θ} = 2 := by
    intro θ
    have hex : ∃ x : A, f x = θ := by
      have hvec : ∀ e, (θ.1 e).v = (rhoQ0 S φ y e).v := by
        intro e
        rw [v_rhoQ0 S φ hφ y e]
        exact θ.2.1 e
      obtain ⟨x, hxθ⟩ := exists_rhoQ0_mul_eq S φ hφ y hvec
      have hyxQ : (y * (x : S.M)) * (y * (x : S.M)) ∈ S.Q := by
        have hsq : (y * (x : S.M)) * (y * (x : S.M)) =
            (y * y) * (y⁻¹ * (x : S.M) * y) * (x : S.M) := by group
        rw [hsq]
        exact S.Q.mul_mem (S.Q.mul_mem hy (by
          simpa using S.normal.conj_mem (x : S.M) x.2 y⁻¹)) x.2
      have hc : (y * (x : S.M)) * (y * (x : S.M)) = (c : S.M) := by
        have h1 : φ (⟨(y * (x : S.M)) * (y * (x : S.M)), hyxQ⟩ : S.Q) = φ c := by
          rw [← sqData_rhoQ0 S φ hyxQ, hxθ]
          exact θ.2.2
        exact congrArg (fun q : S.Q => (q : S.M)) (φ.injective h1)
      exact ⟨⟨x, hc⟩, Subtype.ext hxθ⟩
    let x₀ : A := Classical.choose hex
    have hx₀ : f x₀ = θ := Classical.choose_spec hex
    have hzA : (y * ((x₀.1 * S.zQ : S.Q) : S.M)) *
        (y * ((x₀.1 * S.zQ : S.Q) : S.M)) = (c : S.M) := by
      rw [Subgroup.coe_mul, coe_zQ S]
      calc (y * (x₀.1 * S.zM)) * (y * (x₀.1 * S.zM))
          = (y * x₀.1) * (S.zM * (y * x₀.1)) * S.zM := by group
        _ = (y * x₀.1) * ((y * x₀.1) * S.zM) * S.zM := by rw [← zM_comm S (y * x₀.1)]
        _ = ((y * x₀.1) * (y * x₀.1)) * (S.zM * S.zM) := by group
        _ = (y * x₀.1) * (y * x₀.1) := by rw [zM_mul_self S, mul_one]
        _ = (c : S.M) := x₀.2
    let x₁ : A := ⟨x₀.1 * S.zQ, hzA⟩
    have hfx₁ : f x₁ = θ := by
      rw [← hx₀]
      apply Subtype.ext
      change rhoQ0 S φ (y * (x₁.1 : S.M)) = rhoQ0 S φ (y * (x₀.1 : S.M))
      have hcoe : ((x₁.1 : S.Q) : S.M) = x₀.1 * S.zM := by
        rw [Subgroup.coe_mul, coe_zQ S]
      rw [hcoe, ← mul_assoc, rhoQ0_mul_zM]
    have hne : x₁ ≠ x₀ := by
      intro h
      have hval : ((x₁.1 : S.Q) : S.M) = (x₀.1 : S.M) :=
        congrArg (fun q : S.Q => (q : S.M)) (congrArg (fun x : A => x.1) h)
      have h' : (x₀.1 : S.M) * S.zM = (x₀.1 : S.M) := by
        rwa [show ((x₁.1 : S.Q) : S.M) = (x₀.1 : S.M) * S.zM from by
          rw [Subgroup.coe_mul, coe_zQ S]] at hval
      have hz1 : S.zM = 1 := by
        have := congrArg (fun g : S.M => x₀.1⁻¹ * g) h'
        simpa using this
      exact zM_ne_one S hz1
    rw [Nat.card_eq_two_iff' ⟨x₀, hx₀⟩]
    refine ⟨⟨x₁, hfx₁⟩, ?_, ?_⟩
    · intro h
      exact hne (congrArg Subtype.val h)
    · intro z hz
      have hfeq : f z.1 = f x₀ := z.2.trans hx₀.symm
      have hval : rhoQ0 S φ (y * (z.1.1 : S.M)) =
          rhoQ0 S φ (y * (x₀.1 : S.M)) := congrArg Subtype.val hfeq
      rcases (rhoQ0_eq_rhoQ0_iff S φ).mp hval with h1 | h1
      · exfalso
        apply hz
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact mul_left_cancel h1
      · apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        have hzval : (z.1.1 : S.M) = (x₀.1 : S.M) * S.zM := by
          have := congrArg (fun g : S.M => y⁻¹ * g) h1
          simpa [mul_assoc] using this
        have hx₁coe : ((x₁.1 : S.Q) : S.M) = (x₀.1 : S.M) * S.zM := by
          rw [Subgroup.coe_mul, coe_zQ S]
        rw [hx₁coe]
        exact hzval
  rw [← Nat.card_coe_set_eq]
  exact natCard_eq_two_mul_of_fiber f hfib

end CFSG.GF2Type.Smith1979W3

end

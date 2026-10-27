module

public import CFSG.LargeExtraspecial.FS77A4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

variable (D : CaseA S)

@[expose] def CQa : Subgroup G := S.QG ⊓ centralizer ({D.a} : Set G)

theorem mem_CQa {c : G} : c ∈ D.CQa ↔ c ∈ S.QG ∧ c * D.a = D.a * c := by
  rw [CQa, mem_inf, mem_centralizer_singleton_iff]

theorem CQa_le_X : D.CQa ≤ D.X := fun _ hc =>
  D.mem_X.mpr ⟨S.z_comm (S.QG_le_M (D.mem_CQa.mp hc).1), (D.mem_CQa.mp hc).2⟩

theorem polar_cl_e_of_mem_CQa {c : G} (hc : c ∈ D.CQa) : polar S.q (S.cl c) D.P.e = 0 := by
  rw [← D.cl_a]
  exact (S.polar_cl_eq_zero_iff (D.mem_CQa.mp hc).1 D.a_mem_QG).mpr (D.mem_CQa.mp hc).2

theorem exists_CQa_cl (v : D.N) : ∃ c ∈ D.CQa, S.cl c = v := by
  obtain ⟨c, hcQ, hcv⟩ := S.exists_cl (v : S.Qt)
  refine ⟨c, D.mem_CQa.mpr ⟨hcQ, ?_⟩, hcv⟩
  refine (S.polar_cl_eq_zero_iff hcQ D.a_mem_QG).mp ?_
  rw [hcv, D.cl_a]
  exact D.polar_e_of_mem_N v.2

theorem z_mem_CQa : S.z ∈ D.CQa := D.mem_CQa.mpr ⟨S.z_mem_QG, D.a_comm_z.symm⟩

theorem a_mem_CQa : D.a ∈ D.CQa := D.mem_CQa.mpr ⟨D.a_mem_QG, rfl⟩

theorem eq_mul_of_proj_eq {c c' : G} (hc : c ∈ D.CQa) (hc' : c' ∈ D.CQa)
    (h : D.P.proj (S.cl c) = D.P.proj (S.cl c')) :
    c' = c ∨ c' = c * S.z ∨ c' = c * D.a ∨ c' = c * D.a * S.z := by
  have hcQ := (D.mem_CQa.mp hc).1
  have hcQ' := (D.mem_CQa.mp hc').1
  have e1 := D.eq_proj_add_of_polar_e (D.polar_cl_e_of_mem_CQa hc)
  have e2 := D.eq_proj_add_of_polar_e (D.polar_cl_e_of_mem_CQa hc')
  have key : S.cl c' = S.cl c +
      (polar S.q (S.cl c') D.P.f - polar S.q (S.cl c) D.P.f) • D.P.e := by
    have h1 : S.cl c' - S.cl c = (D.P.proj (S.cl c') + polar S.q (S.cl c') D.P.f • D.P.e) -
        (D.P.proj (S.cl c) + polar S.q (S.cl c) D.P.f • D.P.e) := by
      rw [← e1, ← e2]
    rw [h, sub_smul] at *
    rw [← sub_eq_iff_eq_add', h1]
    abel
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide)
    (polar S.q (S.cl c') D.P.f - polar S.q (S.cl c) D.P.f) with h0 | h1
  · rw [h0, zero_smul, add_zero] at key
    rcases (S.cl_eq_cl_iff hcQ hcQ').mp key.symm with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · rw [h1, one_smul, ← D.cl_a, ← S.cl_mul hcQ D.a_mem_QG] at key
    rcases (S.cl_eq_cl_iff (S.QG.mul_mem hcQ D.a_mem_QG) hcQ').mp key.symm with h2 | h2
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h2))

theorem conj_mem_CQa {m : G} (hm : m ∈ D.X) {c : G} (hc : c ∈ D.CQa) : m * c * m⁻¹ ∈ D.CQa := by
  obtain ⟨hcQ, hca⟩ := D.mem_CQa.mp hc
  refine D.mem_CQa.mpr ⟨S.conj_mem_QG (D.X_le_M hm) hcQ, ?_⟩
  have hma := (D.mem_X.mp hm).2
  calc m * c * m⁻¹ * D.a = m * c * m⁻¹ * (m * D.a * m⁻¹) := by rw [D.conj_a_of_mem_X hm]
    _ = m * (c * D.a) * m⁻¹ := by group
    _ = m * (D.a * c) * m⁻¹ := by rw [hca]
    _ = (m * D.a * m⁻¹) * (m * c * m⁻¹) := by group
    _ = D.a * (m * c * m⁻¹) := by rw [D.conj_a_of_mem_X hm]

@[expose] def IsTwist (w : G) : Prop :=
  (w * S.z * w⁻¹ = D.a ∨ w * S.z * w⁻¹ = D.a * S.z) ∧
    (w * D.a * w⁻¹ = S.z ∨ w * D.a * w⁻¹ = D.a * S.z)

variable {D}

theorem IsCycle.isTwist {w : G} (hw : D.IsCycle w) : D.IsTwist w := ⟨Or.inr hw.1, Or.inl hw.2⟩

theorem IsCycle.inv_isTwist {w : G} (hw : D.IsCycle w) : D.IsTwist w⁻¹ := by
  refine ⟨Or.inl ?_, Or.inr ?_⟩
  · calc w⁻¹ * S.z * w⁻¹⁻¹ = w⁻¹ * (w * D.a * w⁻¹) * w := by rw [hw.2, inv_inv]
      _ = D.a := by group
  · calc w⁻¹ * D.a * w⁻¹⁻¹ = w⁻¹ * (w * (D.a * S.z) * w⁻¹) * w := by rw [hw.conj_az D, inv_inv]
      _ = D.a * S.z := by group

theorem IsTwist.isAorAZ {w : G} (hw : D.IsTwist w) : D.IsAorAZ w := hw.1

theorem conj_z_ne_conj_a (D : CaseA S) (w : G) : w * S.z * w⁻¹ ≠ w * D.a * w⁻¹ := fun h =>
  D.a_ne_z (mul_left_cancel (mul_right_cancel h)).symm

theorem IsTwist.commute_of {w : G} (hw : D.IsTwist w) {x : G}
    (h1 : Commute x (w * S.z * w⁻¹)) (h2 : Commute x (w * D.a * w⁻¹)) :
    Commute x S.z ∧ Commute x D.a := by
  have hzz : D.a * (D.a * S.z) = S.z := by rw [← mul_assoc, D.a_mul_a, one_mul]
  rcases hw.1 with e1 | e1 <;> rcases hw.2 with e2 | e2 <;> rw [e1] at h1 <;> rw [e2] at h2
  · exact ⟨h2, h1⟩
  · exact ⟨hzz ▸ h1.mul_right h2, h1⟩
  · refine ⟨h2, ?_⟩
    have := h1.mul_right h2
    rwa [D.a_mul_z_mul_z] at this
  · exact absurd (e1.trans e2.symm) (D.conj_z_ne_conj_a w)

theorem IsTwist.commute_conj {w : G} (hw : D.IsTwist w) {x : G} (hx : x ∈ D.X) :
    Commute (w * x * w⁻¹) S.z ∧ Commute (w * x * w⁻¹) D.a := by
  obtain ⟨hxz, hxa⟩ := D.mem_X.mp hx
  have hc : ∀ t : G, x * t = t * x → Commute (w * x * w⁻¹) (w * t * w⁻¹) :=
    fun t ht => by
      change (w * x * w⁻¹) * (w * t * w⁻¹) = (w * t * w⁻¹) * (w * x * w⁻¹)
      calc (w * x * w⁻¹) * (w * t * w⁻¹) = w * (x * t) * w⁻¹ := by group
        _ = w * (t * x) * w⁻¹ := by rw [ht]
        _ = (w * t * w⁻¹) * (w * x * w⁻¹) := by group
  exact hw.commute_of (hc _ hxz) (hc _ hxa)

theorem IsTwist.conj_mem_X {w : G} (hw : D.IsTwist w) {x : G} (hx : x ∈ D.X) :
    w * x * w⁻¹ ∈ D.X := by
  obtain ⟨h1, h2⟩ := hw.commute_conj hx
  exact D.mem_X.mpr ⟨h1, h2⟩

theorem IsTwist.inv_isAorAZ {w : G} (hw : D.IsTwist w) : D.IsAorAZ w⁻¹ := by
  rcases hw.2 with e2 | e2
  · left
    calc w⁻¹ * S.z * w⁻¹⁻¹ = w⁻¹ * (w * D.a * w⁻¹) * w := by rw [e2, inv_inv]
      _ = D.a := by group
  · right
    have e1 : w * S.z * w⁻¹ = D.a := by
      rcases hw.1 with e1 | e1
      · exact e1
      · exact absurd (e1.trans e2.symm) (D.conj_z_ne_conj_a w)
    have e3 : w * (D.a * S.z) * w⁻¹ = S.z := by
      calc w * (D.a * S.z) * w⁻¹ = (w * D.a * w⁻¹) * (w * S.z * w⁻¹) := by group
        _ = D.a * S.z * D.a := by rw [e1, e2]
        _ = S.z * D.a * D.a := by rw [S.z_comm D.a_mem_M]
        _ = S.z := by rw [mul_assoc, D.a_mul_a, mul_one]
    calc w⁻¹ * S.z * w⁻¹⁻¹ = w⁻¹ * (w * (D.a * S.z) * w⁻¹) * w := by rw [e3, inv_inv]
      _ = D.a * S.z := by group

theorem IsTwist.conj_mem_L0 {w : G} (hw : D.IsTwist w) {c : G} (hc : c ∈ D.CQa) :
    w * c * w⁻¹ ∈ S.L0 w := by
  obtain ⟨hcQ, -⟩ := D.mem_CQa.mp hc
  refine ⟨?_, ?_⟩
  · rw [Setting.Qa_eq_map]
    exact ⟨c, hcQ, by simp [MulAut.conj_apply]⟩
  · show w * c * w⁻¹ ∈ S.M
    rw [Setting.mem_M_iff]
    exact (hw.commute_conj (D.CQa_le_X hc)).1

@[expose] noncomputable def IsTwist.conjHom {w : G} (hw : D.IsTwist w) : D.CQa →* S.L0 w where
  toFun c := ⟨w * c * w⁻¹, hw.conj_mem_L0 c.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' c c' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def IsTwist.Φ {w : G} (hw : D.IsTwist w) :
    D.CQa →* Multiplicative D.N :=
  (D.ψL0hom hw.isAorAZ).comp hw.conjHom

theorem IsTwist.Φ_apply {w : G} (hw : D.IsTwist w) (c : D.CQa) :
    Multiplicative.toAdd (hw.Φ c) = D.ψ (D.L0toX hw.isAorAZ (hw.conjHom c)) := rfl

theorem IsTwist.Φ_eq_one_of_mem_QG {w : G} (hw : D.IsTwist w) {c : D.CQa}
    (h : w * (c : G) * w⁻¹ ∈ S.QG) : hw.Φ c = 1 := by
  rw [← toAdd_eq_zero, hw.Φ_apply]
  exact (D.ψ_eq_zero_iff (D.L0toX_mem_K hw.isAorAZ _)).mpr h

theorem IsTwist.Φ_z {w : G} (hw : D.IsTwist w) : hw.Φ ⟨S.z, D.z_mem_CQa⟩ = 1 :=
  hw.Φ_eq_one_of_mem_QG (by
    change w * S.z * w⁻¹ ∈ S.QG
    exact hw.isAorAZ.mem_QG)

theorem IsTwist.Φ_a {w : G} (hw : D.IsTwist w) : hw.Φ ⟨D.a, D.a_mem_CQa⟩ = 1 :=
  hw.Φ_eq_one_of_mem_QG (by
    change w * D.a * w⁻¹ ∈ S.QG
    rcases hw.2 with e | e <;> rw [e]
    exacts [S.z_mem_QG, D.az_mem_QG])

theorem IsTwist.Φ_eq_of_proj_eq {w : G} (hw : D.IsTwist w) {c c' : D.CQa}
    (h : D.P.proj (S.cl c) = D.P.proj (S.cl c')) : hw.Φ c' = hw.Φ c := by
  have hz : hw.Φ ⟨S.z, D.z_mem_CQa⟩ = 1 := hw.Φ_z
  have ha : hw.Φ ⟨D.a, D.a_mem_CQa⟩ = 1 := hw.Φ_a
  rcases D.eq_mul_of_proj_eq c.2 c'.2 h with h1 | h1 | h1 | h1
  · rw [Subtype.ext h1]
  · rw [show c' = c * ⟨S.z, D.z_mem_CQa⟩ from Subtype.ext h1, map_mul, hz, mul_one]
  · rw [show c' = c * ⟨D.a, D.a_mem_CQa⟩ from Subtype.ext h1, map_mul, ha, mul_one]
  · rw [show c' = c * ⟨D.a, D.a_mem_CQa⟩ * ⟨S.z, D.z_mem_CQa⟩ from Subtype.ext h1, map_mul,
      map_mul, ha, hz, mul_one, mul_one]

@[expose] noncomputable def liftN (D : CaseA S) (v : D.N) : D.CQa :=
  ⟨(D.exists_CQa_cl v).choose, (D.exists_CQa_cl v).choose_spec.1⟩

theorem cl_liftN (D : CaseA S) (v : D.N) : S.cl (D.liftN v) = v :=
  (D.exists_CQa_cl v).choose_spec.2

theorem proj_cl_liftN (D : CaseA S) (v : D.N) : D.P.proj (S.cl (D.liftN v)) = v := by
  rw [D.cl_liftN, D.proj_of_mem_N v.2]

@[expose] noncomputable def IsTwist.phi {w : G} (hw : D.IsTwist w) (v : D.N) : D.N :=
  Multiplicative.toAdd (hw.Φ (D.liftN v))

theorem IsTwist.Φ_eq_phi {w : G} (hw : D.IsTwist w) (c : D.CQa) :
    Multiplicative.toAdd (hw.Φ c) = hw.phi (D.projN (S.cl c)) := by
  rw [IsTwist.phi, hw.Φ_eq_of_proj_eq (c := c) (c' := D.liftN _)]
  rw [D.proj_cl_liftN, D.coe_projN]

theorem IsTwist.phi_add {w : G} (hw : D.IsTwist w) (v v' : D.N) :
    hw.phi (v + v') = hw.phi v + hw.phi v' := by
  have h1 := hw.Φ_eq_phi (D.liftN v * D.liftN v')
  have hcl : D.projN (S.cl ((D.liftN v * D.liftN v' : D.CQa) : G)) = v + v' := by
    apply Subtype.ext
    rw [D.coe_projN, Subgroup.coe_mul,
      S.cl_mul (D.mem_CQa.mp (D.liftN v).2).1 (D.mem_CQa.mp (D.liftN v').2).1,
      D.cl_liftN, D.cl_liftN, ← Submodule.coe_add, D.proj_of_mem_N (v + v').2]
  rw [hcl, map_mul, toAdd_mul] at h1
  rw [← h1]
  rfl

@[expose] noncomputable def IsTwist.phiLin {w : G} (hw : D.IsTwist w) : D.N →ₗ[ZMod 2] D.N :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := hw.phi
      map_zero' := by
        have h := hw.phi_add 0 0
        rw [add_zero] at h
        have h2 : hw.phi 0 + hw.phi 0 = 0 := by
          rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
        rw [← h] at h2
        exact h2
      map_add' := hw.phi_add }

theorem IsTwist.phiLin_apply {w : G} (hw : D.IsTwist w) (v : D.N) : hw.phiLin v = hw.phi v := rfl

theorem e_not_mem_N : D.P.e ∉ D.N := fun h => by
  have := (D.mem_N_iff.mp h).2
  rw [D.P.polar_fe] at this
  exact one_ne_zero this

theorem IsTwist.phiLin_injective {w : G} (hw : D.IsTwist w) : Function.Injective hw.phiLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  set c := D.liftN v with hc
  have h1 : hw.Φ c = 1 := by
    rw [← toAdd_eq_zero]
    exact hv
  rw [← toAdd_eq_zero, hw.Φ_apply,
    D.ψ_eq_zero_iff (D.L0toX_mem_K hw.isAorAZ _)] at h1
  have h1' : w * (c : G) * w⁻¹ ∈ S.QG := h1
  have h2 : (c : G) ∈ S.QG ⊓ S.Qa w⁻¹ := by
    refine ⟨(D.mem_CQa.mp c.2).1, ?_⟩
    rw [Setting.Qa_eq_map]
    exact ⟨_, h1', by simp; group⟩
  rw [D.mem_QG_inf_Qa_iff hw.inv_isAorAZ] at h2
  have hv' : (v : S.Qt) = S.cl (c : G) := (D.cl_liftN v).symm
  apply Subtype.ext
  rw [hv', Submodule.coe_zero]
  rcases h2 with h | h | h | h <;> rw [h]
  · exact S.cl_one
  · exact S.cl_z
  · exfalso
    apply D.e_not_mem_N
    rw [← D.cl_a, ← h, ← hv']
    exact v.2
  · exfalso
    apply D.e_not_mem_N
    rw [← D.cl_a, ← S.cl_mul_z D.a_mem_QG, ← h, ← hv']
    exact v.2

@[expose] def IsTwist.σ {w : G} (hw : D.IsTwist w) (m : D.X) : D.X :=
  ⟨w * m * w⁻¹, hw.conj_mem_X m.2⟩

theorem IsTwist.phi_ρN {w : G} (hw : D.IsTwist w) (m : D.X) (v : D.N) :
    hw.phiLin (D.ρN m v) = D.ρN (hw.σ m) (hw.phiLin v) := by
  set c := D.liftN v with hc
  have hcQ : (c : G) ∈ S.QG := (D.mem_CQa.mp c.2).1
  set c' : D.CQa := ⟨m * c * (m : G)⁻¹, D.conj_mem_CQa m.2 c.2⟩ with hc'
  have hproj : D.projN (S.cl (c' : G)) = D.ρN m v := by
    apply Subtype.ext
    rw [D.coe_projN, hc', ← D.ρX_apply_cl m hcQ, D.proj_ρX_of_polar_e m
      (D.polar_cl_e_of_mem_CQa c.2)]
    congr 2
    exact Subtype.ext (D.proj_cl_liftN v)
  have h1 := hw.Φ_eq_phi c'
  rw [hproj] at h1
  rw [hw.phiLin_apply, ← h1, hw.phiLin_apply, IsTwist.phi, hw.Φ_apply, hw.Φ_apply,
    ← D.ψ_conj (hw.σ m) (D.L0toX_mem_K hw.isAorAZ _)]
  congr 1
  apply Subtype.ext
  change w * (m * c * (m : G)⁻¹) * w⁻¹ = w * m * w⁻¹ * (w * c * w⁻¹) * (w * m * w⁻¹)⁻¹
  group

@[expose] noncomputable def IsTwist.phiE {w : G} (hw : D.IsTwist w) : D.N ≃ₗ[ZMod 2] D.N :=
  LinearEquiv.ofInjectiveEndo hw.phiLin hw.phiLin_injective

theorem IsTwist.phiE_apply {w : G} (hw : D.IsTwist w) (v : D.N) : hw.phiE v = hw.phiLin v :=
  rfl

theorem nontrivial_N : Nontrivial D.N :=
  Module.nontrivial_of_finrank_pos (R := ZMod 2) (by have := D.three_le_finrank_N; omega)

theorem IsTwist.phiE_mem_orthogonalGroup {w : G} (hw : D.IsTwist w) :
    hw.phiE ∈ TauCeti.QuadraticMap.orthogonalGroup D.qN := by
  set q' : QuadraticForm (ZMod 2) D.N := D.qN.comp hw.phiLin with hq'
  have hinv : ∀ s u, D.qN s = 0 → polar D.qN s u = 0 →
      ∀ x, q' (eichler D.qN s u x) = q' x := by
    intro s u _ _ x
    obtain ⟨m, hm⟩ := D.exists_ρN_eq_eichler s u
    rw [← hm, hq', QuadraticMap.comp_apply, QuadraticMap.comp_apply, hw.phi_ρN m x,
      map_of_mem (D.ρN_mem_orthogonalGroup _)]
  rcases eichler_invariant_quadraticForm D.qN_nondegenerate D.three_le_finrank_N q' hinv with
    h | h
  · exfalso
    have := D.nontrivial_N
    obtain ⟨v, hv⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero D.qN_nondegenerate
    apply hv
    have h1 : q' (hw.phiE.symm v) = 0 := by rw [h]; rfl
    rwa [hq', QuadraticMap.comp_apply, ← hw.phiE_apply, LinearEquiv.apply_symm_apply] at h1
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    have h1 : q' v = D.qN v := by rw [h]
    rwa [hq', QuadraticMap.comp_apply, ← hw.phiE_apply] at h1

theorem IsCycle.σ_σ_σ {w : G} (hw : D.IsCycle w) (m : D.X) :
    hw.isTwist.σ (hw.isTwist.σ (hw.isTwist.σ m)) =
      ⟨w ^ 3, hw.pow_three_mem_X D⟩ * m * ⟨w ^ 3, hw.pow_three_mem_X D⟩⁻¹ :=
  Subtype.ext (by
    change w * (w * (w * m * w⁻¹) * w⁻¹) * w⁻¹ = w ^ 3 * m * (w ^ 3)⁻¹
    simp only [pow_succ, pow_zero, one_mul]
    group)

theorem IsCycle.phiE_pow_three {w : G} (hw : D.IsCycle w) :
    hw.isTwist.phiE ^ 3 = D.ρN ⟨w ^ 3, hw.pow_three_mem_X D⟩ := by
  set w3 : D.X := ⟨w ^ 3, hw.pow_three_mem_X D⟩ with hw3
  have hphi : ∀ m : D.X, ∀ v,
      hw.isTwist.phiE (D.ρN m v) = D.ρN (hw.isTwist.σ m) (hw.isTwist.phiE v) :=
    fun m v => hw.isTwist.phi_ρN m v
  have hcube : ∀ m : D.X,
      hw.isTwist.phiE ^ 3 * D.ρN m = D.ρN (w3 * m * w3⁻¹) * hw.isTwist.phiE ^ 3 := by
    intro m
    refine LinearEquiv.ext fun v => ?_
    simp only [pow_three, LinearEquiv.mul_apply]
    rw [hphi, hphi, hphi, hw.σ_σ_σ]
  set θ : D.N ≃ₗ[ZMod 2] D.N := (D.ρN w3)⁻¹ * hw.isTwist.phiE ^ 3 with hθ
  have hcomm : ∀ m : D.X, θ * D.ρN m = D.ρN m * θ := by
    intro m
    rw [hθ, mul_assoc, hcube m, map_mul, map_mul, map_inv]
    group
  have hcomm' : ∀ m : D.X, ∀ v, (θ : D.N →ₗ[ZMod 2] D.N) (D.ρN m v) =
      D.ρN m ((θ : D.N →ₗ[ZMod 2] D.N) v) := fun m v => by
    have := congrArg (fun f : D.N ≃ₗ[ZMod 2] D.N => f v) (hcomm m)
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_coe] using this
  rcases D.eq_zero_or_id θ hcomm' with h | h
  · exfalso
    have := D.nontrivial_N
    obtain ⟨v, hv⟩ := exists_ne (0 : D.N)
    apply hv
    apply θ.injective
    have h1 := LinearMap.congr_fun h v
    rw [LinearEquiv.coe_coe] at h1
    rw [h1, map_zero]
    rfl
  · have h1 : θ = 1 := LinearEquiv.ext fun v => LinearMap.congr_fun h v
    rw [hθ, inv_mul_eq_one] at h1
    exact h1.symm

theorem IsCycle.exists_ρN_eq_phiE {w : G} (hw : D.IsCycle w) :
    ∃ l : D.X, D.ρN l = hw.isTwist.phiE := by
  have hle : CFSG.RankThree.OrthogonalInvolutions.omegaGroup D.qN D.qN_nondegenerate ≤
      D.ρN.range := fun h hh => D.mem_range_ρN hh
  have h3 : hw.isTwist.phiE ^ 3 ∈ D.ρN.range := ⟨_, hw.phiE_pow_three.symm⟩
  exact mem_omegaGroup_of_pow_three D.qN_nondegenerate hle hw.isTwist.phiE_mem_orthogonalGroup h3

theorem IsCycle.ρN_σ_of_phi {w : G} (hw : D.IsCycle w) (m : D.X) :
    D.ρN (hw.isTwist.σ m) = hw.isTwist.phiE * D.ρN m * hw.isTwist.phiE⁻¹ := by
  have h : hw.isTwist.phiE * D.ρN m = D.ρN (hw.isTwist.σ m) * hw.isTwist.phiE :=
    LinearEquiv.ext fun v => hw.isTwist.phi_ρN m v
  rw [h, mul_inv_cancel_right]

theorem IsCycle.pow_centralizing {w : G} (hw : D.IsCycle w)
    (hc : ∀ m : D.X, D.ρN (hw.isTwist.σ m) = D.ρN m) (k : ℕ) :
    ∀ m : D.X, ∃ h : w ^ k * m * (w ^ k)⁻¹ ∈ D.X, D.ρN ⟨w ^ k * m * (w ^ k)⁻¹, h⟩ = D.ρN m := by
  induction k with
  | zero => intro m; exact ⟨by simp, by congr 1; exact Subtype.ext (by simp)⟩
  | succ k ih =>
    intro m
    obtain ⟨h, hk⟩ := ih m
    have e : w ^ (k + 1) * m * (w ^ (k + 1))⁻¹ = w * (w ^ k * m * (w ^ k)⁻¹) * w⁻¹ := by
      rw [pow_succ']
      group
    refine ⟨e ▸ hw.conj_mem_X D h, ?_⟩
    have h2 := hc ⟨w ^ k * m * (w ^ k)⁻¹, h⟩
    rw [← hk, ← h2]
    congr 1
    exact Subtype.ext e

theorem exists_cycle_centralizing (D : CaseA S) :
    ∃ y : G, D.IsCycle y ∧ (∃ e : ℕ, orderOf y = 3 ^ e) ∧
      ∀ m : D.X, ∃ h : y * m * y⁻¹ ∈ D.X, D.ρN ⟨y * m * y⁻¹, h⟩ = D.ρN m := by
  obtain ⟨w, hw⟩ := D.exists_cycle
  obtain ⟨l, hl⟩ := hw.exists_ρN_eq_phiE
  have hw₁ : D.IsCycle ((l : G)⁻¹ * w) := hw.mul_mem_X D (inv_mem l.2)
  have hc₁ : ∀ m : D.X, D.ρN (hw₁.isTwist.σ m) = D.ρN m := by
    intro m
    have e : hw₁.isTwist.σ m = l⁻¹ * hw.isTwist.σ m * l := Subtype.ext (by
      change (l : G)⁻¹ * w * m * ((l : G)⁻¹ * w)⁻¹ = (l : G)⁻¹ * (w * m * w⁻¹) * l
      group)
    rw [e, map_mul, map_mul, map_inv, hl, hw.ρN_σ_of_phi]
    group
  obtain ⟨j, hcyc, e, he⟩ := D.exists_isCycle_pow_three hw₁
  exact ⟨_, hcyc, ⟨e, he⟩, hw₁.pow_centralizing hc₁ j⟩

end CaseA

end CFSG.LargeExtraspecial.FS77

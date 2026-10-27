module

public import CFSG.LargeExtraspecial.S3bTransport
public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

theorem Qa_mul (g h : G) : S.Qa (h * g) = (S.Qa g).map (MulAut.conj h).toMonoidHom := by
  rw [S.Qa_eq_map, S.Qa_eq_map, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_Qa_mul_iff {g h x : G} : x ∈ S.Qa (h * g) ↔ h⁻¹ * x * h ∈ S.Qa g := by
  rw [S.Qa_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩

theorem conj_mem_Qa_mul {g h x : G} (hx : x ∈ S.Qa g) : h * x * h⁻¹ ∈ S.Qa (h * g) := by
  rw [S.mem_Qa_mul_iff]
  simpa [mul_assoc] using hx

theorem conj_z_mem_Qa (g : G) : g * S.z * g⁻¹ ∈ S.Qa g := (S.conjBy g).z_mem_QG

theorem conj_mem_M_iff {h x : G} (hh : h ∈ S.M) : h⁻¹ * x * h ∈ S.M ↔ x ∈ S.M := by
  constructor
  · intro hx
    have := S.M.mul_mem (S.M.mul_mem hh hx) (S.M.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hh) hx) hh

theorem mem_L0_mul_iff {g h x : G} (hh : h ∈ S.M) : x ∈ S.L0 (h * g) ↔ h⁻¹ * x * h ∈ S.L0 g := by
  rw [S.L0_eq, S.L0_eq, mem_inf, mem_inf, S.mem_Qa_mul_iff]
  exact and_congr Iff.rfl (S.conj_mem_M_iff hh).symm

theorem conj_mem_L0_mul {g h x : G} (hh : h ∈ S.M) (hx : x ∈ S.L0 g) :
    h * x * h⁻¹ ∈ S.L0 (h * g) := by
  rw [S.mem_L0_mul_iff hh]
  simpa [mul_assoc] using hx

variable [Finite G]

theorem mem_Lbar_iff {g : G} {s : S.O} :
    s ∈ S.Lbar g ↔ ∃ y : S.M, (y : G) ∈ S.L0 g ∧ S.ρ y = s := by
  simp only [Lbar, mem_map, mem_subgroupOf]

theorem ρ_mem_Lbar {g y : G} (hy : y ∈ S.L0 g) : S.ρ ⟨y, S.L0_le_M g hy⟩ ∈ S.Lbar g :=
  S.mem_Lbar_iff.mpr ⟨_, hy, rfl⟩

theorem Lbar_mul {g h : G} (hh : h ∈ S.M) :
    S.Lbar (h * g) = (S.Lbar g).map (MulAut.conj (S.ρ ⟨h, hh⟩)).toMonoidHom := by
  ext s
  rw [S.mem_Lbar_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨S.ρ ((⟨h, hh⟩ : S.M)⁻¹ * y * ⟨h, hh⟩), S.mem_Lbar_iff.mpr ⟨_, ?_, rfl⟩, ?_⟩
    · exact (S.mem_L0_mul_iff hh).mp hy
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp ht
    refine ⟨⟨h, hh⟩ * y * (⟨h, hh⟩ : S.M)⁻¹, ?_, ?_⟩
    · exact S.conj_mem_L0_mul hh hy
    · simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conj_mem_Lbar_mul {g h : G} (hh : h ∈ S.M) {s : S.O} (hs : s ∈ S.Lbar g) :
    S.ρ ⟨h, hh⟩ * s * (S.ρ ⟨h, hh⟩)⁻¹ ∈ S.Lbar (h * g) := by
  rw [S.Lbar_mul hh]
  exact ⟨s, hs, by simp⟩

theorem Lbar_eq_of_conj_eq {g g' : G} (h : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) :
    S.Lbar g = S.Lbar g' := by
  unfold Lbar L0
  rw [S.Qa_eq_of_conj_eq h]

theorem Lbar_mul_of_mem_QG {g q : G} (hq : q ∈ S.QG) : S.Lbar (q * g) = S.Lbar g := by
  rw [S.Lbar_mul (S.QG_le_M hq), (S.ρ_eq_one_iff ⟨q, S.QG_le_M hq⟩).mpr hq]
  ext s
  simp

theorem ρ_cl_conj_z {g h : G} (hh : h ∈ S.M) (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    (S.ρ ⟨h, hh⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) := by
  rw [S.ρ_cl _ haQ]
  congr 1
  change h * (g * S.z * g⁻¹) * h⁻¹ = _
  group

theorem Qa_conjBy (g h : G) : (S.conjBy g).Qa h = S.Qa (h * g) :=
  QG_eq_of_z_eq _ _ (by simp only [conjBy_z]; group)

theorem mem_Qa_symm {g₁ g₂ : G} (hne : g₁ * S.z * g₁⁻¹ ≠ g₂ * S.z * g₂⁻¹)
    (h : g₁ * S.z * g₁⁻¹ ∈ S.Qa g₂) : g₂ * S.z * g₂⁻¹ ∈ S.Qa g₁ := by
  set T := S.conjBy g₂ with hT
  have hTz : T.z = g₂ * S.z * g₂⁻¹ := rfl
  have hgt : (g₁ * g₂⁻¹) * T.z * (g₁ * g₂⁻¹)⁻¹ = g₁ * S.z * g₁⁻¹ := by
    rw [hTz]
    group
  have h1 := T.z_mem_Qa_of_mem_QG hgt h (by rw [hTz]; exact hne)
  rw [hT, S.Qa_conjBy, inv_mul_cancel_right] at h1
  exact h1

theorem z_mem_Qa {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.z ∈ S.Qa g :=
  S.z_mem_Qa_of_mem_QG rfl haQ hne

theorem Qa_eq_QG_of_conj_eq {g : G} (h : g * S.z * g⁻¹ = S.z) : S.Qa g = S.QG := by
  rw [← S.Qa_one]
  exact S.Qa_eq_of_conj_eq (by rw [h]; group)

omit [Finite G] in
theorem exists_mul_conj_eq_mul_z {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃ q ∈ S.QG, (q * g) * S.z * (q * g)⁻¹ = g * S.z * g⁻¹ * S.z := by
  have ha1 : g * S.z * g⁻¹ ≠ 1 := (S.conjBy g).z_ne_one
  obtain ⟨q, hq, hqa⟩ := S.exists_conj_eq_mul_z haQ ha1 hne
  refine ⟨q, hq, ?_⟩
  rw [← hqa]
  group

theorem QG_inf_Qa_mul_of_mem_QG {g q : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hq : q ∈ S.QG) : S.QG ⊓ S.Qa (q * g) = S.QG ⊓ S.Qa g := by
  have hzQa := S.z_mem_Qa haQ hne
  ext x
  simp only [mem_inf, S.mem_Qa_mul_iff]
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hw : q⁻¹ * x * q ∈ S.QG := by
      have := S.conj_mem_QG (S.M.inv_mem (S.QG_le_M hq)) hx
      simpa [mul_assoc] using this
    rcases S.mul_comm_or hx (S.QG.inv_mem hq) with h | h
    · have e : q⁻¹ * x * q = x := by rw [← h]; group
      rwa [e] at hx'
    · have e : q⁻¹ * x * q = S.z * x := by
        have h2 : x = S.z * (q⁻¹ * x * q) := by
          calc x = x * q⁻¹ * q := by group
            _ = S.z * (q⁻¹ * x) * q := by rw [h]
            _ = S.z * (q⁻¹ * x * q) := by group
        calc q⁻¹ * x * q = S.z * (S.z * (q⁻¹ * x * q)) := by
              rw [← mul_assoc, S.z_mul_z, one_mul]
          _ = S.z * x := by rw [← h2]
      rw [e] at hx'
      have := (S.Qa g).mul_mem (inv_mem hzQa) hx'
      rwa [inv_mul_cancel_left] at this
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rcases S.mul_comm_or hx (S.QG.inv_mem hq) with h | h
    · have e : q⁻¹ * x * q = x := by rw [← h]; group
      rwa [e]
    · have e : q⁻¹ * x * q = S.z * x := by
        have h2 : x = S.z * (q⁻¹ * x * q) := by
          calc x = x * q⁻¹ * q := by group
            _ = S.z * (q⁻¹ * x) * q := by rw [h]
            _ = S.z * (q⁻¹ * x * q) := by group
        calc q⁻¹ * x * q = S.z * (S.z * (q⁻¹ * x * q)) := by
              rw [← mul_assoc, S.z_mul_z, one_mul]
          _ = S.z * x := by rw [← h2]
      rw [e]
      exact (S.Qa g).mul_mem hzQa hx'

theorem Lbar_eq_of_conj_eq_mul_z {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (h : g' * S.z * g'⁻¹ = g * S.z * g⁻¹ * S.z) :
    S.Lbar g' = S.Lbar g := by
  obtain ⟨q, hq, hqa⟩ := S.exists_mul_conj_eq_mul_z haQ hne
  rw [S.Lbar_eq_of_conj_eq (h.trans hqa.symm), S.Lbar_mul_of_mem_QG hq]

theorem QG_inf_Qa_eq_of_conj_eq_mul_z {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (h : g' * S.z * g'⁻¹ = g * S.z * g⁻¹ * S.z) :
    S.QG ⊓ S.Qa g' = S.QG ⊓ S.Qa g := by
  obtain ⟨q, hq, hqa⟩ := S.exists_mul_conj_eq_mul_z haQ hne
  rw [S.Qa_eq_of_conj_eq (h.trans hqa.symm), S.QG_inf_Qa_mul_of_mem_QG haQ hne hq]

noncomputable def fixLbar (g : G) : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  add_mem' := fun {v w} hv hw s hs => by
    rw [map_add, hv s hs, hw s hs]
  zero_mem' := fun s _ => map_zero _
  smul_mem' := fun c v hv s hs => by
    rw [map_smul, hv s hs]

theorem mem_fixLbar {g : G} {v : S.Qt} :
    v ∈ S.fixLbar g ↔ ∀ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

theorem cl_mem_fixLbar_iff {g x : G} (hx : x ∈ S.QG) :
    S.cl x ∈ S.fixLbar g ↔ ∀ y ∈ S.L0 g, y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x * S.z := by
  constructor
  · intro h y hy
    have h1 := h _ (S.ρ_mem_Lbar hy)
    rw [S.ρ_cl _ hx] at h1
    exact (S.cl_eq_cl_iff hx (S.conj_mem_QG (S.L0_le_M g hy) hx)).mp h1.symm
  · intro h s hs
    obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
    rw [S.ρ_cl _ hx]
    exact ((S.cl_eq_cl_iff hx (S.conj_mem_QG y.2 hx)).mpr (h y hy)).symm

theorem cl_mem_fixLbar_self {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ∈ S.fixLbar g := by
  rw [S.cl_mem_fixLbar_iff haQ]
  intro y hy
  left
  have h := ((S.conjBy g).z_comm_QG hy.1).symm
  change g * S.z * g⁻¹ * y = y * (g * S.z * g⁻¹) at h
  rw [← h]
  group

omit [Finite G] in
theorem cl_conj_z_ne_zero {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.cl (g * S.z * g⁻¹) ≠ 0 := by
  intro h
  rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
  · exact (S.conjBy g).z_ne_one h1
  · exact hne h1

theorem q_cl_conj_z {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) : S.q (S.cl (g * S.z * g⁻¹)) = 0 :=
  (S.q_cl_eq_zero_iff haQ).mpr ((S.conjBy g).z_sq)

@[expose] def HasTypeAInL (g : G) : Prop :=
  ∃ α : S.M, (α : G) ∈ S.La g ∧ (α : G) ∉ S.QG ∧ S.IsTypeAOn α 2

theorem hasTypeAInL_of_mem_L0 {g : G} {α : S.M} (hα : (α : G) ∈ S.L0 g) (hαQ : (α : G) ∉ S.QG)
    (h : S.IsTypeAOn α 2) : S.HasTypeAInL g :=
  ⟨α, (le_sup_right : S.L0 g ≤ S.La g) hα, hαQ, h⟩

omit [Finite G] in
theorem QG_map_conj {h : G} (hh : h ∈ S.M) : S.QG.map (MulAut.conj h).toMonoidHom = S.QG := by
  refine le_antisymm ?_ fun x hx => ⟨h⁻¹ * x * h, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact S.conj_mem_QG hh hx
  · have := S.conj_mem_QG (S.M.inv_mem hh) hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem La_mul {g h : G} (hh : h ∈ S.M) :
    S.La (h * g) = (S.La g).map (MulAut.conj h).toMonoidHom := by
  have hL0 : S.L0 (h * g) = (S.L0 g).map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [S.mem_L0_mul_iff hh]
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  unfold La
  rw [Subgroup.map_sup, S.QG_map_conj hh]
  exact congrArg (S.QG ⊔ ·) hL0

theorem hasTypeAInL_of_mul {g h : G} (hh : h ∈ S.M) (h1 : S.HasTypeAInL (h * g)) :
    S.HasTypeAInL g := by
  obtain ⟨α, hαL, hαQ, hα⟩ := h1
  have hh' : h⁻¹ ∈ S.M := S.M.inv_mem hh
  refine ⟨⟨h⁻¹ * α * h⁻¹⁻¹, S.M.mul_mem (S.M.mul_mem hh' α.2) (S.M.inv_mem hh')⟩, ?_, ?_,
    S.isTypeAOn_conj hh' hα⟩
  · rw [S.La_mul hh] at hαL
    obtain ⟨β, hβ, hβα⟩ := hαL
    change h⁻¹ * α * h⁻¹⁻¹ ∈ S.La g
    rw [← hβα]
    simpa [mul_assoc] using hβ
  · intro hmem
    apply hαQ
    have := S.conj_mem_QG hh hmem
    simpa [mul_assoc] using this

theorem hasTypeAInL_mul {g h : G} (hh : h ∈ S.M) (h1 : S.HasTypeAInL g) :
    S.HasTypeAInL (h * g) := by
  refine S.hasTypeAInL_of_mul (S.M.inv_mem hh) ?_
  rwa [inv_mul_cancel_left]

@[expose] def IsReducible : Prop :=
  ∃ W : Submodule (ZMod 2) S.Qt, W ≠ ⊥ ∧ W ≠ ⊤ ∧
    ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W

end Setting

end CFSG.LargeExtraspecial

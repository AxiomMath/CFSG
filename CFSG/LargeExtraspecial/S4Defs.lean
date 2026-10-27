module

public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] (S : Setting G)

theorem Qa_mul (h g : G) : S.Qa (h * g) = (S.Qa g).map (MulAut.conj h).toMonoidHom := by
  rw [Setting.Qa_eq_map, Setting.Qa_eq_map, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mem_Qa_mul_iff {h g x : G} : x ∈ S.Qa (h * g) ↔ h⁻¹ * x * h ∈ S.Qa g := by
  rw [Qa_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

theorem conj_mem_Qa_mul {h g x : G} (hx : x ∈ S.Qa g) : h * x * h⁻¹ ∈ S.Qa (h * g) := by
  rw [mem_Qa_mul_iff]
  simpa [mul_assoc] using hx

theorem conj_mem_M {h x : G} (hh : h ∈ S.M) (hx : x ∈ S.M) : h * x * h⁻¹ ∈ S.M :=
  S.M.mul_mem (S.M.mul_mem hh hx) (S.M.inv_mem hh)

theorem mem_L0_mul_iff {h g x : G} (hh : h ∈ S.M) :
    x ∈ S.L0 (h * g) ↔ h⁻¹ * x * h ∈ S.L0 g := by
  change x ∈ S.Qa (h * g) ⊓ S.M ↔ h⁻¹ * x * h ∈ S.Qa g ⊓ S.M
  rw [mem_inf, mem_inf, mem_Qa_mul_iff]
  refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using conj_mem_M S (S.M.inv_mem hh) hx
  · simpa [mul_assoc] using conj_mem_M S hh hx

theorem conj_mem_L0_mul {h g x : G} (hh : h ∈ S.M) (hx : x ∈ S.L0 g) :
    h * x * h⁻¹ ∈ S.L0 (h * g) := by
  rw [mem_L0_mul_iff S hh]
  simpa [mul_assoc] using hx

theorem mul_conj_z (h g : G) : h * g * S.z * (h * g)⁻¹ = h * (g * S.z * g⁻¹) * h⁻¹ := by
  group

theorem QG_le_La (g : G) : S.QG ≤ S.La g := le_sup_left

theorem L0_le_La (g : G) : S.L0 g ≤ S.La g := le_sup_right

theorem La_le_M (g : G) : S.La g ≤ S.M := sup_le S.QG_le_M inf_le_right

theorem conj_mem_QG' {h : G} (hh : h ∈ S.M) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    h * g * S.z * (h * g)⁻¹ ∈ S.QG := by
  rw [mul_conj_z]
  exact S.conj_mem_QG hh haQ

theorem conj_ne_z' {h : G} (hh : h ∈ S.M) {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) :
    h * g * S.z * (h * g)⁻¹ ≠ S.z := by
  rw [mul_conj_z]
  intro h1
  apply hne
  calc g * S.z * g⁻¹ = h⁻¹ * (h * (g * S.z * g⁻¹) * h⁻¹) * h := by group
    _ = h⁻¹ * S.z * h := by rw [h1]
    _ = S.z := by rw [S.z_comm (S.M.inv_mem hh)]; group

theorem conj_z_ne_one (k : G) : k * S.z * k⁻¹ ≠ 1 := (S.conjBy k).z_ne_one

variable [Finite G]

theorem mem_Lbar {g : G} {t : S.O} :
    t ∈ S.Lbar g ↔ ∃ y : S.M, (y : G) ∈ S.L0 g ∧ S.ρ y = t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_subgroupOf.mp hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_subgroupOf.mpr hy, rfl⟩

theorem ρ_mem_Lbar {g : G} {y : S.M} (hy : (y : G) ∈ S.L0 g) : S.ρ y ∈ S.Lbar g :=
  (mem_Lbar S).mpr ⟨y, hy, rfl⟩

theorem Lbar_mul (h : S.M) (g : G) :
    S.Lbar ((h : G) * g) = (S.Lbar g).map (MulAut.conj (S.ρ h)).toMonoidHom := by
  ext t
  rw [mem_Lbar, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨S.ρ (h⁻¹ * y * h), (mem_Lbar S).mpr ⟨h⁻¹ * y * h, ?_, rfl⟩, ?_⟩
    · have := (mem_L0_mul_iff S h.2).mp hy
      simpa using this
    · simp [map_mul, mul_assoc]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp hs
    refine ⟨h * y * h⁻¹, ?_, by simp [map_mul]⟩
    rw [mem_L0_mul_iff S h.2]
    simpa [mul_assoc] using hy

theorem mem_Lbar_mul_iff (h : S.M) (g : G) {t : S.O} :
    t ∈ S.Lbar ((h : G) * g) ↔ (S.ρ h)⁻¹ * t * S.ρ h ∈ S.Lbar g := by
  rw [Lbar_mul, mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [mul_assoc] using hs
  · intro ht
    exact ⟨_, ht, by simp [mul_assoc]⟩

theorem conj_mem_Lbar_mul (h : S.M) {g : G} {t : S.O} (ht : t ∈ S.Lbar g) :
    S.ρ h * t * (S.ρ h)⁻¹ ∈ S.Lbar ((h : G) * g) := by
  rw [mem_Lbar_mul_iff]
  simpa [mul_assoc] using ht

theorem Lbar_eq_of_conj_eq {g g' : G} (h : g * S.z * g⁻¹ = g' * S.z * g'⁻¹) :
    S.Lbar g = S.Lbar g' := by
  unfold Setting.Lbar Setting.L0
  rw [S.Qa_eq_of_conj_eq h]

theorem Lbar_mul_of_mem_QG {g q : G} (hq : q ∈ S.QG) : S.Lbar (q * g) = S.Lbar g := by
  have h1 := Lbar_mul S ⟨q, S.QG_le_M hq⟩ g
  rw [(S.ρ_eq_one_iff _).mpr hq] at h1
  rw [h1]
  ext t
  simp

theorem ρ_cl_conj_z (h : S.M) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
  rw [S.ρ_cl h haQ, mul_conj_z]

omit [Finite G] in
theorem cl_conj_z_ne_zero {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.cl (g * S.z * g⁻¹) ≠ 0 := by
  intro h
  rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
  · exact conj_z_ne_one S g h1
  · exact hne h1

theorem q_cl_conj_z {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) : S.q (S.cl (g * S.z * g⁻¹)) = 0 :=
  (S.q_cl_eq_zero_iff haQ).mpr (S.conjBy g).z_sq

theorem Lbar_eq_of_conj_eq_mul_z {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (h : g' * S.z * g'⁻¹ = g * S.z * g⁻¹ * S.z) :
    S.Lbar g' = S.Lbar g := by
  obtain ⟨q, hq, hqa⟩ := S.exists_conj_eq_mul_z haQ (conj_z_ne_one S g) hne
  rw [Lbar_eq_of_conj_eq S (h.trans (hqa.symm.trans (mul_conj_z S q g).symm)),
    Lbar_mul_of_mem_QG S hq]

theorem Lbar_eq_of_cl_eq {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (ha'Q : g' * S.z * g'⁻¹ ∈ S.QG)
    (h : S.cl (g' * S.z * g'⁻¹) = S.cl (g * S.z * g⁻¹)) : S.Lbar g' = S.Lbar g := by
  rcases (S.cl_eq_cl_iff haQ ha'Q).mp h.symm with h1 | h1
  · exact Lbar_eq_of_conj_eq S h1
  · exact Lbar_eq_of_conj_eq_mul_z S haQ hne h1

@[expose] def fixSub (X : Subgroup S.O) : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  add_mem' := fun {v w} hv hw x hx => by rw [map_add, hv x hx, hw x hx]
  zero_mem' := fun x _ => map_zero _
  smul_mem' := fun c v hv x hx => by rw [map_smul, hv x hx]

theorem mem_fixSub {X : Subgroup S.O} {v : S.Qt} :
    v ∈ fixSub S X ↔ ∀ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  Iff.rfl

structure Hyp4 (g : G) : Prop where
  conj_mem : g * S.z * g⁻¹ ∈ S.QG
  conj_ne : g * S.z * g⁻¹ ≠ S.z
  fixSub_eq : fixSub S (S.Lbar g) = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
  two_lt_width : 2 < S.width

@[expose] def NoA2 (g : G) : Prop :=
  ∀ α : S.M, (α : G) ∈ S.La g → (α : G) ∉ S.QG → ¬ S.IsTypeAOn α 2

structure Cons311 (g : G) : Prop where
  weaklyClosed : ∀ h : G, h ∈ S.M → S.Lbar (h * g) ≤ normalizer (S.Lbar g : Set S.O) →
    S.Lbar (h * g) = S.Lbar g
  card_Lbar : Nat.card (S.Lbar g) = 2 ^ (S.width - 1)
  card_QG_inf_Qa : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (S.width + 1)
  comm_le : ∀ x ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G), ∀ s ∈ S.Lbar g,
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) - S.cl x ∈ S.clSub (S.QG ⊓ S.Qa g)
  faithful : ∀ s ∈ S.Lbar g,
    (∀ v ∈ S.clSub (S.QG ⊓ S.Qa g), (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → s = 1

@[expose] def Dset (g : G) (t : S.O) : Set (Subgroup S.O) :=
  {X | ∃ h : S.M, X = S.Lbar ((h : G) * g) ∧ t ∈ X}

@[expose] noncomputable def Rbar (g : G) (t : S.O) : Subgroup S.O := sSup (Dset S g t)

@[expose] noncomputable def R (g : G) (t : S.O) : Subgroup G :=
  ⨆ (h : S.M) (_ : t ∈ S.Lbar ((h : G) * g)), S.La ((h : G) * g)

@[expose] noncomputable def Vt (g : G) (t : S.O) : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) {v | ∃ h : S.M, t ∈ S.Lbar ((h : G) * g) ∧
    v = S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)}

@[expose] noncomputable def Nbar (g : G) (t : S.O) : Subgroup S.O where
  carrier := {x | x ∈ Rbar S g t ∧ ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun v hv => by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy.2 v hv, hx.2 v hv]⟩
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun v hv => by
    conv_lhs => rw [← hx.2 v hv]
    exact LinearEquiv.symm_apply_apply _ v⟩

@[expose] noncomputable def N (g : G) (t : S.O) : Subgroup G :=
  ((Nbar S g t).comap S.ρ).map S.M.subtype ⊓ R S g t

@[expose] noncomputable def V (g : G) (t : S.O) : Subgroup G := S.clPre (Vt S g t)

@[expose] noncomputable def W (g : G) (t : S.O) : Subgroup G :=
  S.QG ⊓ centralizer (V S g t : Set G)

end CFSG.LargeExtraspecial.S4

module

public import CFSG.LargeExtraspecial.DW2AStruct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] noncomputable def XbarD : Subgroup S.O :=
  closure {t | ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧
    t ∈ Abar S (S.clPre (spanD S)) h}

theorem Abar_le_XbarD {h : G} (hyQ : h * S.z * h⁻¹ ∈ S.QG) (hyz : h * S.z * h⁻¹ ≠ S.z) :
    Abar S (S.clPre (spanD S)) h ≤ XbarD S := fun _ ht => subset_closure ⟨h, hyQ, hyz, ht⟩

theorem XbarD_le_Mbar : XbarD S ≤ S.Mbar := by
  rw [XbarD, closure_le]
  rintro t ⟨h, -, -, ht⟩
  exact Abar_le_Mbar _ _ ht

theorem conj_mem_Abar {A : Subgroup G} {h : G} (m : S.M) {t : S.O}
    (ht : t ∈ Abar S A h) : S.ρ m * t * (S.ρ m)⁻¹ ∈ Abar S A ((m : G) * h) := by
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
  refine mem_Abar.mpr ⟨m * a * (m : G)⁻¹, ⟨conj_mem_conjSub_mul ha.1,
    S.M.mul_mem (S.M.mul_mem m.2 ha.2) (S.M.inv_mem m.2)⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem conj_mem_XbarD (m : S.M) {t : S.O} (ht : t ∈ XbarD S) :
    S.ρ m * t * (S.ρ m)⁻¹ ∈ XbarD S := by
  induction ht using closure_induction with
  | mem t ht =>
    obtain ⟨h, hyQ, hyz, ht⟩ := ht
    have hmh : ((m : G) * h) * S.z * ((m : G) * h)⁻¹ = m * (h * S.z * h⁻¹) * (m : G)⁻¹ := by
      group
    refine subset_closure ⟨(m : G) * h, ?_, ?_, conj_mem_Abar m ht⟩
    · rw [hmh]
      exact S.conj_mem_QG m.2 hyQ
    · rw [hmh]
      intro e
      apply hyz
      calc h * S.z * h⁻¹ = (m : G)⁻¹ * ((m : G) * (h * S.z * h⁻¹) * (m : G)⁻¹) * m := by
            group
        _ = (m : G)⁻¹ * S.z * m := by rw [e]
        _ = S.z := by simpa using S.s12_conj_z_of_mem_M (S.M.inv_mem m.2)
  | one => simp
  | mul x y _ _ hx hy =>
    have : S.ρ m * (x * y) * (S.ρ m)⁻¹ =
        (S.ρ m * x * (S.ρ m)⁻¹) * (S.ρ m * y * (S.ρ m)⁻¹) := by group
    rw [this]
    exact (XbarD S).mul_mem hx hy
  | inv x _ hx =>
    have : S.ρ m * x⁻¹ * (S.ρ m)⁻¹ = (S.ρ m * x * (S.ρ m)⁻¹)⁻¹ := by group
    rw [this]
    exact (XbarD S).inv_mem hx

section Fix

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)
include hWs

theorem XbarD_sub_mem {t : S.O} (ht : t ∈ XbarD S) :
    ∀ v ∈ perp S (spanD S), (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ spanD S := by
  have hW := isMbarInvariant_spanD (S := S)
  have hinvW : ∀ x ∈ XbarD S, ∀ w ∈ spanD S, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ spanD S := by
    intro x hx w hw
    obtain ⟨mx, hmx⟩ := XbarD_le_Mbar hx
    rw [← hmx]
    exact hW mx w hw
  induction ht using closure_induction with
  | mem t ht =>
    intro v hv
    obtain ⟨h, hyQ, hyz, ht⟩ := ht
    obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
    have := ρ_sub_mem_span_of_mem_perp hW hDQ_spanD hWs hyQ (cl_conj_mem_spanD hyQ) hyz ha.1 hv
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (cl_conj_mem_spanD hyQ))) this
  | one => intro v _; simp
  | mul x y hx' hy' hx hy =>
    intro v hv
    have e : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) +
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
      rw [map_sub]
      change (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) - v = _
      abel
    rw [e]
    exact add_mem (hinvW x hx' _ (hy v hv)) (hx v hv)
  | inv x hx' hx =>
    intro v hv
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
        -(((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) := by
      rw [map_sub]
      have : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
        change ((x⁻¹ * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
        rw [inv_mul_cancel]
        rfl
      rw [this]
      abel
    rw [e]
    exact neg_mem (hinvW _ ((XbarD S).inv_mem hx') _ (hx v hv))

theorem XbarD_eq_one {t : S.O} (ht : t ∈ XbarD S)
    (h : ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : t = 1 := by
  obtain ⟨m, hm⟩ := XbarD_le_Mbar ht
  have hy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Ybar S := ⟨t, ⟨m, hm⟩, rfl⟩
  exact Subtype.ext (eq_one_of_trivial_perp isMbarInvariant_spanD hy h
    fun v hv => XbarD_sub_mem hWs ht v hv)

end Fix

variable (S) in
@[expose] noncomputable def fixD : Submodule (ZMod 2) S.Qt :=
  fixIn ((XbarD S).map S.O.subtype) (perp S (spanD S))

theorem mem_fixD {v : S.Qt} :
    v ∈ fixD S ↔ v ∈ perp S (spanD S) ∧ ∀ t ∈ XbarD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun t ht => h _ ⟨t, ht, rfl⟩⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, by rintro _ ⟨t, ht, rfl⟩; exact h t ht⟩

theorem isMbarInvariant_fixD : IsMbarInvariant S (fixD S) := by
  intro m v hv
  rw [mem_fixD] at hv ⊢
  refine ⟨isMbarInvariant_spanD.perp m v hv.1, fun t ht => ?_⟩
  have ht' := conj_mem_XbarD m⁻¹ ht
  rw [map_inv, inv_inv] at ht'
  have h1 := hv.2 _ ht'
  have e : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((S.ρ m)⁻¹ * t * S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    change ((S.ρ m * ((S.ρ m)⁻¹ * t * S.ρ m) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = _
    rw [show S.ρ m * ((S.ρ m)⁻¹ * t * S.ρ m) = t * S.ρ m by group]
    rfl
  rw [← e, h1]

end CFSG.LargeExtraspecial.DW

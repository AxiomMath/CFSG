module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.CharHelpers

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.HardMathSupport.RichardWeiss.Proving
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Phi_le (S : Subgroup G) : Phi S ≤ S := by
  unfold Phi
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
  · rw [Subgroup.closure_le]
    rintro x ⟨s, hs, rfl⟩
    exact S.pow_mem hs 2

@[expose] def OSub (S : Subgroup G) : Subgroup S :=
  Subgroup.closure {x : S | (x : G) ∈ Phi S ∧ x ^ 2 = 1}

@[expose] def OmPhi (S : Subgroup G) : Subgroup G := (OSub S).map S.subtype

theorem OSub_characteristic (S : Subgroup G) : (OSub S).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  unfold OSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
  have hcomap := (sqComm_characteristic S).fixed φ
  have h1 : φ x ∈ sqComm S := by
    have : x ∈ (sqComm S).comap φ.toMonoidHom := by
      rw [hcomap]; exact (Phi_eq_sqComm S x).1 hx1
    exact this
  refine Subgroup.subset_closure ⟨(Phi_eq_sqComm S _).2 h1, ?_⟩
  show (φ x) ^ 2 = 1
  rw [← map_pow, hx2, map_one]

theorem OmPhi_subgroupOf (S : Subgroup G) : (OmPhi S).subgroupOf S = OSub S :=
  Subgroup.comap_map_eq_self_of_injective S.subtype_injective _

theorem OmPhi_characteristic (S : Subgroup G) : ((OmPhi S).subgroupOf S).Characteristic := by
  rw [OmPhi_subgroupOf]; exact OSub_characteristic S

theorem OmPhi_le_S (S : Subgroup G) : OmPhi S ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_OmPhi_of_involution {S : Subgroup G} {y : G} (hy : y ∈ Phi S) (h2 : y ^ 2 = 1) :
    y ∈ OmPhi S := by
  refine ⟨⟨y, Phi_le S hy⟩, Subgroup.subset_closure ⟨hy, ?_⟩, rfl⟩
  apply Subtype.ext
  simpa using h2

theorem OmPhi_eq_closure (S : Subgroup G) :
    OmPhi S = Subgroup.closure {y | y ∈ Phi S ∧ y ^ 2 = 1} := by
  unfold OmPhi OSub
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨hx1, ?_⟩
    simpa using congrArg Subtype.val hx2
  · rintro ⟨hy1, hy2⟩
    refine ⟨⟨y, Phi_le S hy1⟩, ⟨hy1, ?_⟩, rfl⟩
    apply Subtype.ext
    simpa using hy2

theorem conj_mem_OmPhi {S : Subgroup G} {m : G} (hm : ∀ s ∈ S, m * s * m⁻¹ ∈ S) :
    ∀ y ∈ OmPhi S, m * y * m⁻¹ ∈ OmPhi S := by
  have hle : OmPhi S ≤ (OmPhi S).comap (MulAut.conj m).toMonoidHom := by
    refine (OmPhi_eq_closure S).le.trans ((Subgroup.closure_le _).2 ?_)
    rintro y ⟨hy1, hy2⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have e : (MulAut.conj m).toMonoidHom y = m * y * m⁻¹ := rfl
    rw [e]
    refine mem_OmPhi_of_involution (conj_mem_Phi hm _ hy1) ?_
    have : (m * y * m⁻¹) ^ 2 = m * y ^ 2 * m⁻¹ := by
      simp [pow_two, mul_assoc]
    rw [this, hy2]
    simp
  intro y hy
  exact hle hy

theorem commutator_OmPhi_characteristic (S : Subgroup G) :
    ((⁅OmPhi S, S⁆).subgroupOf S).Characteristic := by
  have hYS : OmPhi S ≤ S := OmPhi_le_S S
  have : ((OmPhi S).subgroupOf S).Characteristic := OmPhi_characteristic S
  have : (⊤ : Subgroup S).Characteristic := inferInstance
  have hc : (⁅(OmPhi S).subgroupOf S, (⊤ : Subgroup S)⁆).Characteristic := inferInstance
  have hmap : (⁅(OmPhi S).subgroupOf S, (⊤ : Subgroup S)⁆).map S.subtype =
      ⁅OmPhi S, S⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYS,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (⁅OmPhi S, S⁆).subgroupOf S = ⁅(OmPhi S).subgroupOf S, (⊤ : Subgroup S)⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  rw [this]
  exact hc

theorem centralizer_OmPhi_characteristic (S : Subgroup G) :
    ((S ⊓ Subgroup.centralizer ((OmPhi S : Subgroup G) : Set G)).subgroupOf S).Characteristic := by
  have hYS : OmPhi S ≤ S := OmPhi_le_S S
  have hch : ((OmPhi S).subgroupOf S).Characteristic := OmPhi_characteristic S
  have hc := Subgroup.characteristic_centralizer (H := (OmPhi S).subgroupOf S)
  have e : (S ⊓ Subgroup.centralizer ((OmPhi S : Subgroup G) : Set G)).subgroupOf S =
      Subgroup.centralizer (((OmPhi S).subgroupOf S : Subgroup S) : Set S) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨-, h⟩ y hy
      apply Subtype.ext
      exact h _ hy
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      have := h ⟨y, hYS hy⟩ hy
      exact congrArg Subtype.val this
  rw [e]
  exact hc

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

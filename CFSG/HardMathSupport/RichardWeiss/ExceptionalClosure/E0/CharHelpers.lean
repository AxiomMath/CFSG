module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.GroupE0
public import CFSG.HardMathSupport.RichardWeiss.Proving.OmegaFrattini

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.HardMathSupport.RichardWeiss.Proving
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Phi_eq_sqComm (S : Subgroup G) (x : S) :
    (x : G) ∈ Phi S ↔ x ∈ sqComm S := (mem_sqComm_iff S x).symm

theorem Y_characteristic {V S : Subgroup G} (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hY : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ V) :
    ((V ⊓ Phi S).subgroupOf S).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : (y : G) ∈ V ⊓ Phi S := hy
  have hyV : (y : G) ∈ V := hy'.1
  have hyPhi : (y : G) ∈ Phi S := hy'.2
  have hcomap := (sqComm_characteristic S).fixed φ
  have h1 : φ y ∈ sqComm S := by
    have : y ∈ (sqComm S).comap φ.toMonoidHom := by
      rw [hcomap]; exact (Phi_eq_sqComm S y).1 hyPhi
    exact this
  have hy2 : y ^ 2 = 1 := Subtype.ext (hV2 _ hyV)
  have h2 : (φ y : S) ^ 2 = 1 := by
    rw [← map_pow, hy2, map_one]
  have h2' : ((φ y : S) : G) ^ 2 = 1 := by
    have := congrArg Subtype.val h2
    simpa using this
  have hPhi : ((φ y : S) : G) ∈ Phi S := (Phi_eq_sqComm S _).2 h1
  exact Subgroup.mem_subgroupOf.2 ⟨hY _ hPhi h2', hPhi⟩

theorem commutator_Y_characteristic {V S : Subgroup G} (hVS : V ≤ S)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hY : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ V) :
    ((⁅V ⊓ Phi S, S⁆).subgroupOf S).Characteristic := by
  have hYS : V ⊓ Phi S ≤ S := inf_le_left.trans hVS
  have : ((V ⊓ Phi S).subgroupOf S).Characteristic := Y_characteristic hV2 hY
  have : (⊤ : Subgroup S).Characteristic := inferInstance
  have hc : (⁅(V ⊓ Phi S).subgroupOf S, (⊤ : Subgroup S)⁆).Characteristic := inferInstance
  have hmap : (⁅(V ⊓ Phi S).subgroupOf S, (⊤ : Subgroup S)⁆).map S.subtype =
      ⁅V ⊓ Phi S, S⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYS,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : (⁅V ⊓ Phi S, S⁆).subgroupOf S = ⁅(V ⊓ Phi S).subgroupOf S, (⊤ : Subgroup S)⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  rw [this]
  exact hc

theorem centralizer_Y_characteristic {V S : Subgroup G} (hVS : V ≤ S)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hY : ∀ y ∈ Phi S, y ^ 2 = 1 → y ∈ V) :
    ((S ⊓ Subgroup.centralizer ((V ⊓ Phi S : Subgroup G) : Set G)).subgroupOf S).Characteristic := by
  have hYS : V ⊓ Phi S ≤ S := inf_le_left.trans hVS
  have hch : ((V ⊓ Phi S).subgroupOf S).Characteristic := Y_characteristic hV2 hY
  have hc := Subgroup.characteristic_centralizer (H := (V ⊓ Phi S).subgroupOf S)
  have e : (S ⊓ Subgroup.centralizer ((V ⊓ Phi S : Subgroup G) : Set G)).subgroupOf S =
      Subgroup.centralizer (((V ⊓ Phi S).subgroupOf S : Subgroup S) : Set S) := by
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

module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.OmPhi

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.HardMathSupport.RichardWeiss.Proving
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_of_char [Finite G] {S Y : Subgroup G} (hYS : Y ≤ S)
    (hch : (Y.subgroupOf S).Characteristic) {m : G} (hm : ∀ s ∈ S, m * s * m⁻¹ ∈ S) :
    ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := by
  classical
  let f : S →* S :=
    { toFun := fun s => ⟨m * s * m⁻¹, hm s s.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hinj : Function.Injective f := by
    intro a b h
    have := congrArg Subtype.val h
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk] at this
    exact Subtype.ext (by simpa using this)
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).1 hinj
  let φ : S ≃* S := MulEquiv.ofBijective f hbij
  have h1 := Subgroup.characteristic_iff_map_le.1 hch φ
  intro y hy
  have : (⟨y, hYS hy⟩ : S) ∈ Y.subgroupOf S := hy
  have h2 := h1 ⟨_, this, rfl⟩
  exact h2

theorem Phi_iff_of_aut (S : Subgroup G) (φ : S ≃* S) (x : S) :
    ((φ x : S) : G) ∈ Phi S ↔ (x : G) ∈ Phi S := by
  have hcomap := (sqComm_characteristic S).fixed φ
  rw [Phi_eq_sqComm, Phi_eq_sqComm]
  constructor
  · intro h
    have : x ∈ (sqComm S).comap φ.toMonoidHom := h
    rwa [hcomap] at this
  · intro h
    have : x ∈ (sqComm S).comap φ.toMonoidHom := by rw [hcomap]; exact h
    exact this

@[expose] def ZSub (S : Subgroup G) : Subgroup S :=
  Subgroup.closure {x : S | (x : G) ∈ Phi S ∧ x ^ 2 = 1 ∧ ∀ z : S, (z : G) ∈ Phi S → z * x = x * z}

@[expose] def OmZPhi (S : Subgroup G) : Subgroup G := (ZSub S).map S.subtype

theorem ZSub_characteristic (S : Subgroup G) : (ZSub S).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  unfold ZSub
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hx1, hx2, hx3⟩, rfl⟩
  refine Subgroup.subset_closure ⟨(Phi_iff_of_aut S φ x).2 hx1, ?_, ?_⟩
  · show (φ x) ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  · intro z hz
    have hz' : ((φ.symm z : S) : G) ∈ Phi S := by
      rw [← Phi_iff_of_aut S φ (φ.symm z)]; simpa using hz
    have := hx3 (φ.symm z) hz'
    have h2 := congrArg φ this
    simpa using h2

theorem OmZPhi_subgroupOf (S : Subgroup G) : (OmZPhi S).subgroupOf S = ZSub S :=
  Subgroup.comap_map_eq_self_of_injective S.subtype_injective _

theorem OmZPhi_characteristic (S : Subgroup G) : ((OmZPhi S).subgroupOf S).Characteristic := by
  rw [OmZPhi_subgroupOf]; exact ZSub_characteristic S

theorem OmZPhi_le_S (S : Subgroup G) : OmZPhi S ≤ S := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_OmZPhi_of_central {S : Subgroup G} {y : G} (hy : y ∈ Phi S) (h2 : y ^ 2 = 1)
    (hc : ∀ z ∈ Phi S, z * y = y * z) : y ∈ OmZPhi S := by
  refine ⟨⟨y, Phi_le S hy⟩, Subgroup.subset_closure ⟨hy, ?_, fun z hz => ?_⟩, rfl⟩
  · apply Subtype.ext
    simpa using h2
  · apply Subtype.ext
    exact hc z hz

theorem OmZPhi_eq_closure (S : Subgroup G) :
    OmZPhi S = Subgroup.closure {y | y ∈ Phi S ∧ y ^ 2 = 1 ∧ ∀ z ∈ Phi S, z * y = y * z} := by
  unfold OmZPhi ZSub
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2, hx3⟩, rfl⟩
    refine ⟨hx1, ?_, fun z hz => ?_⟩
    · simpa using congrArg Subtype.val hx2
    · have := hx3 ⟨z, Phi_le S hz⟩ hz
      exact congrArg Subtype.val this
  · rintro ⟨hy1, hy2, hy3⟩
    refine ⟨⟨y, Phi_le S hy1⟩, ⟨hy1, ?_, fun z hz => ?_⟩, rfl⟩
    · apply Subtype.ext
      simpa using hy2
    · apply Subtype.ext
      exact hy3 z hz

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

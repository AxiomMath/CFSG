module

public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport
public import CFSG.GH74.GLS.LU.Local.Defs
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LieType.Universal.Unitary.Model

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelLUT

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

@[expose] def subEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (X : Subgroup G) :
    ↥X ≃* ↥(X.map Φ.toMonoidHom) := MulEquiv.subgroupMap Φ X

theorem subEquiv_apply {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (X : Subgroup G) (x : ↥X) :
    ((subEquiv Φ X x : ↥(X.map Φ.toMonoidHom)) : H) = Φ (x : G) := rfl

theorem subgroupOf_map_equiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (X A : Subgroup G) :
    (A.subgroupOf X).map (subEquiv Φ X).toMonoidHom =
      (A.map Φ.toMonoidHom).subgroupOf (X.map Φ.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : G), hx, rfl⟩
  · rintro ⟨a, ha, hay⟩
    obtain ⟨x', hx', hx'y⟩ := y.2
    have hax : a = x' := Φ.injective (hay.trans hx'y.symm)
    refine ⟨⟨a, hax ▸ hx'⟩, ha, ?_⟩
    apply Subtype.ext
    exact hay

theorem isCompIn_map {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) {X K : Subgroup G}
    (h : IsCompIn X K) : IsCompIn (X.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  rw [← subgroupOf_map_equiv]
  exact CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent _ h.2

theorem isPCompIn_map {G H : Type*} [Group G] [Group H] (p : ℕ) (Φ : G ≃* H) {X L : Subgroup G}
    (h : IsPCompIn p X L) : IsPCompIn p (X.map Φ.toMonoidHom) (L.map Φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  rw [← subgroupOf_map_equiv]
  exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p _ h.2

theorem map_map_symm {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (A : Subgroup H) :
    (A.map Φ.symm.toMonoidHom).map Φ.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id H := by ext; simp
  rw [this, Subgroup.map_id]

theorem map_symm_map {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (A : Subgroup G) :
    (A.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  have : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id G := by ext; simp
  rw [this, Subgroup.map_id]

theorem hasSL2Model_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {P : ℕ → Prop}
    (h : HasSL2Model A P) : HasSL2Model B P := by
  obtain ⟨F', iF, fF, hP, ⟨e'⟩⟩ := h
  exact ⟨F', iF, fF, hP, ⟨e.symm.trans e'⟩⟩

theorem luComps_map {G H : Type} [Group G] [Group H] (Φ : G ≃* H) {q : ℕ} {z : G}
    {K₁ K₂ : Subgroup G} (h : LUComps G q z K₁ K₂) :
    LUComps H q (Φ z) (K₁.map Φ.toMonoidHom) (K₂.map Φ.toMonoidHom) := by
  have hC : ∀ (w : G), (Subgroup.centralizer ({w} : Set G)).map Φ.toMonoidHom =
      Subgroup.centralizer ({Φ w} : Set H) := fun w =>
    ModelLT.centralizer_map_equiv Φ w
  have hcen : ∀ K : Subgroup G, (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers z →
      (Subgroup.center ↥(K.map Φ.toMonoidHom)).map (K.map Φ.toMonoidHom).subtype =
        Subgroup.zpowers (Φ z) := by
    intro K hK
    let e : ↥K ≃* ↥(K.map Φ.toMonoidHom) := subEquiv Φ K
    have h1 : (Subgroup.center ↥(K.map Φ.toMonoidHom)) = (Subgroup.center ↥K).map e.toMonoidHom :=
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e).symm
    rw [h1, Subgroup.map_map]
    have h2 : (K.map Φ.toMonoidHom).subtype.comp e.toMonoidHom = Φ.toMonoidHom.comp K.subtype := by
      ext x; rfl
    rw [h2, ← Subgroup.map_map, hK, MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hcen K₁ h.cen₁, hcen K₂ h.cen₂⟩
  · have := isCompIn_map Φ h.comp₁
    rwa [hC] at this
  · have := isCompIn_map Φ h.comp₂
    rwa [hC] at this
  · intro heq
    exact h.ne (Subgroup.map_injective Φ.injective heq)
  · intro L hL
    have h1 := isPCompIn_map 2 Φ.symm hL
    have h2 : (Subgroup.centralizer ({Φ z} : Set H)).map Φ.symm.toMonoidHom =
        Subgroup.centralizer ({z} : Set G) := by
      rw [← hC z, map_symm_map]
    rw [h2] at h1
    rcases h.only _ h1 with h3 | h3
    · left
      rw [← h3, map_map_symm]
    · right
      rw [← h3, map_map_symm]
  · exact hasSL2Model_of_equiv (subEquiv Φ K₁) h.sl₁
  · exact hasSL2Model_of_equiv (subEquiv Φ K₂) h.sl₂

end CFSG.GH74.GLS.Stage2.Final.ModelLUT

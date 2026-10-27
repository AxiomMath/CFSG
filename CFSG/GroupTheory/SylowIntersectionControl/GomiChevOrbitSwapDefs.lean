module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup

@[expose] def GomiAtomOrbitTop (K : Type) [Group K] : Prop :=
  ∀ (S A : Subgroup K) (𝒜 : Subgroup (MulAut K)), IsSylowOf 2 S ⊤ → IsPGroup 2 𝒜 →
    (∀ α ∈ 𝒜, S.map α.toMonoidHom = S) → IsGomiAtom ⊤ S A →
      ∀ α₁ ∈ 𝒜, ∀ α₂ ∈ 𝒜, A.map α₁.toMonoidHom = A ∨ A.map α₂.toMonoidHom = A ∨
        A.map α₁.toMonoidHom = A.map α₂.toMonoidHom

@[expose] def GomiSwapTop (K : Type) [Group K] : Prop :=
  ∀ (S A : Subgroup K) (α : MulAut K), IsSylowOf 2 S ⊤ → S.map α.toMonoidHom = S →
    IsGomiAtom ⊤ S A → A.map α.toMonoidHom ≠ A → A ⊔ A.map α.toMonoidHom = ⊤ →
      IsGomiL3 K ∨ IsGomiSp4 K

@[expose] def GomiNoAtomSwap (K : Type) [Group K] : Prop :=
  ∀ (S A : Subgroup K) (α : MulAut K), IsSylowOf 2 S ⊤ → S.map α.toMonoidHom = S →
    IsGomiAtom ⊤ S A → A.map α.toMonoidHom ≠ A → A ⊔ A.map α.toMonoidHom ≠ ⊤

@[expose] def GomiAtomsFixed (K : Type) [Group K] : Prop :=
  ∀ (S A : Subgroup K) (α : MulAut K), IsSylowOf 2 S ⊤ → S.map α.toMonoidHom = S →
    IsGomiAtom ⊤ S A → A.map α.toMonoidHom = A

variable {K : Type} [Group K]

private theorem exists_sylow_of_isSylowOf_top {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) : ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hdvd⟩ := isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hT2.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

theorem GomiAtomsFixed.gomiAtomOrbitTop (h : GomiAtomsFixed K) : GomiAtomOrbitTop K :=
  fun S A _ hS _ hfix hA α₁ hα₁ _ _ => Or.inl (h S A α₁ hS (hfix α₁ hα₁) hA)

theorem GomiAtomsFixed.gomiNoAtomSwap (h : GomiAtomsFixed K) : GomiNoAtomSwap K :=
  fun S A α hS hα hA hne _ => hne (h S A α hS hα hA)

theorem GomiNoAtomSwap.gomiSwapTop (h : GomiNoAtomSwap K) : GomiSwapTop K :=
  fun S A α hS hα hA hne hsup => absurd hsup (h S A α hS hα hA hne)

theorem gomiSwapTop_of_isGomiL3 (h : IsGomiL3 K) : GomiSwapTop K :=
  fun _ _ _ _ _ _ _ _ => Or.inl h

theorem gomiSwapTop_of_isGomiSp4 (h : IsGomiSp4 K) : GomiSwapTop K :=
  fun _ _ _ _ _ _ _ _ => Or.inr h

theorem GomiAtomsFixed.of_mulEquiv [Finite K] {K' : Type} [Group K'] [Finite K'] (e : K ≃* K')
    (h : GomiAtomsFixed K') : GomiAtomsFixed K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S A α hS hfix hA
  let α' : MulAut K' := (e.symm.trans α).trans e
  have hα' : α'.toMonoidHom = e.toMonoidHom.comp (α.toMonoidHom.comp e.symm.toMonoidHom) := rfl
  have hS' : IsSylowOf 2 (S.map e.toMonoidHom) ⊤ :=
    isSylowOf_top_map_of_surjective e.surjective hS
  have hcomp : e.symm.toMonoidHom.comp (α'.toMonoidHom.comp e.toMonoidHom) = α.toMonoidHom := by
    rw [hα']
    ext x
    simp
  have hfix' : (S.map e.toMonoidHom).map α'.toMonoidHom = S.map e.toMonoidHom := by
    rw [hα', Subgroup.map_map]
    have hcc : (e.toMonoidHom.comp (α.toMonoidHom.comp e.symm.toMonoidHom)).comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp
    rw [hcc, ← Subgroup.map_map, hfix]
  have hA' : IsGomiAtom ⊤ (S.map e.toMonoidHom) (A.map e.toMonoidHom) :=
    (isGomiAtom_top_map_mulEquiv_iff e S A).mpr hA
  have hBA := h (S.map e.toMonoidHom) (A.map e.toMonoidHom) α' hS' hfix' hA'
  have hmap : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    have hsymm : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id K := by
      ext x
      simp
    rw [hsymm, Subgroup.map_id]
  calc A.map α.toMonoidHom
      = A.map (e.symm.toMonoidHom.comp (α'.toMonoidHom.comp e.toMonoidHom)) := by rw [hcomp]
    _ = ((A.map e.toMonoidHom).map α'.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (A.map e.toMonoidHom).map e.symm.toMonoidHom := by rw [hBA]
    _ = A := hmap

theorem gomiAtomsFixed_of_isSylowOf [Finite K] {T : Subgroup K} (hT : IsSylowOf 2 T ⊤)
    (h : ∀ (A : Subgroup K) (α : MulAut K), T.map α.toMonoidHom = T → IsGomiAtom ⊤ T A →
      A.map α.toMonoidHom = A) : GomiAtomsFixed K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S A α hS hfix hA
  obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowOf_top hT
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowOf_top hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T' S'
  have hSg : T.map (MulAut.conj g).toMonoidHom = S := by
    have h := congrArg (fun P : Sylow 2 K => (P : Subgroup K)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hT', hS'] at h
    exact h
  let c : MulAut K := MulAut.conj g
  let β : MulAut K := c⁻¹ * α * c
  have hβ : β.toMonoidHom = (c⁻¹).toMonoidHom.comp (α.toMonoidHom.comp c.toMonoidHom) := rfl
  have hcT : S.map (c⁻¹).toMonoidHom = T := by
    rw [← hSg, Subgroup.map_map]
    have hcc : (c⁻¹).toMonoidHom.comp c.toMonoidHom = MonoidHom.id K := by
      ext x
      simp
    rw [hcc, Subgroup.map_id]
  have hfixT : T.map β.toMonoidHom = T := by
    rw [hβ, ← Subgroup.map_map, ← Subgroup.map_map, hSg, hfix, hcT]
  let A₀ : Subgroup K := A.map (c⁻¹).toMonoidHom
  have hA₀ : IsGomiAtom ⊤ T A₀ := by
    have h0 := (isGomiAtom_top_map_mulEquiv_iff c⁻¹ S A).mpr hA
    rwa [hcT] at h0
  have hβA : A₀.map β.toMonoidHom = A₀ := h A₀ β hfixT hA₀
  have hcA : A₀.map c.toMonoidHom = A := by
    rw [Subgroup.map_map]
    have hcc : c.toMonoidHom.comp (c⁻¹).toMonoidHom = MonoidHom.id K := by
      ext x
      simp
    rw [hcc, Subgroup.map_id]
  have hfinal : A₀.map (α.toMonoidHom.comp c.toMonoidHom) = A := by
    have h2 := congrArg (Subgroup.map c.toMonoidHom) hβA
    rw [Subgroup.map_map, hβ] at h2
    have hcc : c.toMonoidHom.comp ((c⁻¹).toMonoidHom.comp (α.toMonoidHom.comp c.toMonoidHom)) =
        α.toMonoidHom.comp c.toMonoidHom := by
      ext x
      simp
    rw [hcc] at h2
    rw [h2, hcA]
  calc A.map α.toMonoidHom = (A₀.map c.toMonoidHom).map α.toMonoidHom := by rw [hcA]
    _ = A₀.map (α.toMonoidHom.comp c.toMonoidHom) := by rw [Subgroup.map_map]
    _ = A := hfinal

end CFSG.GroupTheory

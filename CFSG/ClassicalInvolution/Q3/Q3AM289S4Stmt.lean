module

public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3AMBadConj
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3NM

section Defs


@[expose] def S4LayerKind {X : Type} [Group X] (c : CompData) (Φ : Set (Subgroup X)) (zb : X) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι X Φ), ShapeSingle D c zb

@[expose] def S4Layer {X : Type} [Group X] (Φ : Set (Subgroup X)) (zb : X) : Prop :=
  S4LayerKind (CompData.model .PSU 4) Φ zb ∨ S4LayerKind (CompData.model .POmegaOdd 3) Φ zb ∨
    S4LayerKind (CompData.model .POmegaMinus 4) Φ zb

end Defs

section Plain

@[expose] def S4Pair {X : Type} [Group X] (Φ : Set (Subgroup X)) (zb : X) : Prop :=
  zb ≠ 1 ∧ ∃ A ∈ Φ, ∃ A' ∈ Φ, ∃ a a' : X, IsUniqueInvolution A a ∧ IsUniqueInvolution A' a' ∧
    (∀ x ∈ A, ∀ y ∈ A', x * y = y * x) ∧ zb = a * a'

@[expose] def S4Frame {X : Type} [Group X] (Φ : Set (Subgroup X)) (zb a : X) : Prop :=
  ∃ M ∈ Φ, ∃ b u : X, IsUniqueInvolution M b ∧ b ≠ a ∧ b ≠ zb * a ∧ a * b = b * a ∧
    u ∈ M ∧ orderOf u = 4 ∧ u * u = b ∧ a * u = u * a ∧
    (∃ C ∈ Φ, IsUniqueInvolution C (a * b)) ∧
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) ⊔
      Subgroup.centralizer ({a * b} : Set X) = ⊤

end Plain

section Leaves


@[expose] def S4VertexModelLeafAt (c : CompData) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) (zb : X), ConjInvariant Φ →
    S4LayerKind c Φ zb → S4Pair Φ zb →
      CFSG.IsQuasisimple X ∧ AutOddFreeOn X (fun f => ∃ A ∈ Φ, ∀ a ∈ A, f a = a) ∧
        ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B

@[expose] def S4LinkModelLeafAt (c : CompData) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) (zb : X), ConjInvariant Φ →
    S4LayerKind c Φ zb → S4Pair Φ zb → ∀ A ∈ Φ, ∀ a : X, IsUniqueInvolution A a →
      S4Frame Φ zb a

@[expose] def S4VertexModelLeaf : Prop :=
  S4VertexModelLeafAt (CompData.model .PSU 4) ∧ S4VertexModelLeafAt (CompData.model .POmegaOdd 3) ∧
    S4VertexModelLeafAt (CompData.model .POmegaMinus 4)

@[expose] def S4LinkModelLeaf : Prop :=
  S4LinkModelLeafAt (CompData.model .PSU 4) ∧ S4LinkModelLeafAt (CompData.model .POmegaOdd 3) ∧
    S4LinkModelLeafAt (CompData.model .POmegaMinus 4)

theorem S4LayerKind.zb_mem_center {X : Type} [Group X] {c : CompData} {Φ : Set (Subgroup X)}
    {zb : X} (h : S4LayerKind c Φ zb) : zb ∈ Subgroup.center X := by
  obtain ⟨ι, -, D, i₁, hi, -, f, hf, rfl⟩ := h
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ ⨆ i, (D.hom i).range := by rw [D.generate]; exact Subgroup.mem_top g
  have hg' : g ∈ (D.hom i₁).range := by
    have : (⨆ i, (D.hom i).range) = (D.hom i₁).range := by
      apply le_antisymm
      · exact iSup_le fun i => by rw [hi i]
      · exact le_iSup (fun i => (D.hom i).range) i₁
    rwa [this] at hg
  obtain ⟨y, rfl⟩ := hg'
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hf y]

theorem S4Layer.zb_mem_center {X : Type} [Group X] {Φ : Set (Subgroup X)} {zb : X}
    (h : S4Layer Φ zb) : zb ∈ Subgroup.center X := by
  rcases h with h | h | h <;> exact h.zb_mem_center

end Leaves

section Conj

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {zb : X}

theorem S4Frame.conj (hz : zb ∈ Subgroup.center X) (hΦ : ConjInvariant Φ) {a : X}
    (h : S4Frame Φ zb a) (g : X) : S4Frame Φ zb (g * a * g⁻¹) := by
  obtain ⟨M, hM, b, u, hb, hba, hbz, hab, hu, hu4, huu, hau, ⟨C, hC, hCab⟩, hgen⟩ := h
  have hzc : g * zb * g⁻¹ = zb := by
    have := Subgroup.mem_center_iff.mp hz g
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have e1 : ∀ x y : X, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := fun x y => by group
  refine ⟨conjSub g M, hΦ g M hM, g * b * g⁻¹, g * u * g⁻¹, hb.conj g, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨conjSub g C, hΦ g C hC, ?_⟩, ?_⟩
  · intro h1
    exact hba (by simpa [mul_assoc] using congrArg (fun y => g⁻¹ * y * g) h1)
  · intro h1
    apply hbz
    have h2 : g * b * g⁻¹ = g * (zb * a) * g⁻¹ := by rw [e1, hzc]; exact h1
    simpa [mul_assoc] using congrArg (fun y => g⁻¹ * y * g) h2
  · rw [← e1, ← e1, hab]
  · exact conj_mem_conjSub hu
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj g) u
    rw [MulAut.conj_apply] at h1
    rw [h1, hu4]
  · rw [← e1, huu]
  · rw [← e1, ← e1, hau]
  · rw [← e1]
    exact hCab.conj g
  ·
    have hc : ∀ y : X, conjSub g (Subgroup.centralizer ({y} : Set X)) =
        Subgroup.centralizer ({g * y * g⁻¹} : Set X) := by
      intro y
      ext x
      rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
          _ = g * y * g⁻¹ * x := by group
      · intro hx
        calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [hx]
          _ = y * (g⁻¹ * x * g) := by group
    have h2 : conjSub g (Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) ⊔
        Subgroup.centralizer ({a * b} : Set X)) = ⊤ := by
      rw [hgen]
      exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    rw [conjSub, Subgroup.map_sup, Subgroup.map_sup] at h2
    have h3 := h2
    simp only [conjSub] at hc
    rw [hc a, hc b, hc (a * b), e1] at h3
    exact h3

theorem s4Frame_of_exists (hz : zb ∈ Subgroup.center X) (hΦ : ConjInvariant Φ)
    (htrans : ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B) {A₀ : Subgroup X} {a₀ : X}
    (hA₀ : A₀ ∈ Φ) (ha₀ : IsUniqueInvolution A₀ a₀) (h : S4Frame Φ zb a₀) {A : Subgroup X}
    (hA : A ∈ Φ) {a : X} (ha : IsUniqueInvolution A a) : S4Frame Φ zb a := by
  obtain ⟨g, hg⟩ := htrans A₀ hA₀ A hA
  have h1 : IsUniqueInvolution A (g * a₀ * g⁻¹) := hg ▸ ha₀.conj g
  have : a = g * a₀ * g⁻¹ := ha.eq h1
  rw [this]
  exact h.conj hz hΦ g

theorem exists_partner_member (hz : zb ∈ Subgroup.center X) (hΦ : ConjInvariant Φ)
    (htrans : ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B) {A A' : Subgroup X} {a : X}
    (hA : A ∈ Φ) (hA' : A' ∈ Φ) (ha : IsUniqueInvolution A a)
    (ha' : IsUniqueInvolution A' (zb * a)) {C : Subgroup X} (hC : C ∈ Φ) {c : X}
    (hc : IsUniqueInvolution C c) : ∃ D ∈ Φ, IsUniqueInvolution D (zb * c) := by
  obtain ⟨g, hg⟩ := htrans A hA C hC
  have h1 : IsUniqueInvolution C (g * a * g⁻¹) := hg ▸ ha.conj g
  have hcg : c = g * a * g⁻¹ := hc.eq h1
  have hzc : g * zb * g⁻¹ = zb := by
    have := Subgroup.mem_center_iff.mp hz g
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine ⟨conjSub g A', hΦ g A' hA', ?_⟩
  have h2 := ha'.conj g
  have e : g * (zb * a) * g⁻¹ = zb * c := by
    rw [hcg]
    calc g * (zb * a) * g⁻¹ = (g * zb * g⁻¹) * (g * a * g⁻¹) := by group
      _ = zb * (g * a * g⁻¹) := by rw [hzc]
  rwa [e] at h2

theorem classical_involution_not_central (htrans : ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B)
    (hP : S4Pair Φ zb) {A : Subgroup X} (hA : A ∈ Φ) {a : X} (ha : IsUniqueInvolution A a) :
    a ∉ Subgroup.center X := by
  intro hac
  obtain ⟨hzb1, A₀, hA₀, A₀', hA₀', a₀, a₀', ha₀, ha₀', -, hzba⟩ := hP
  have key : ∀ {B : Subgroup X} {b : X}, B ∈ Φ → IsUniqueInvolution B b → b = a := by
    intro B b hB hb
    obtain ⟨g, hg⟩ := htrans A hA B hB
    have h1 : IsUniqueInvolution B (g * a * g⁻¹) := hg ▸ ha.conj g
    have hga : g * a * g⁻¹ = a := by
      have := Subgroup.mem_center_iff.mp hac g
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    rw [← hga]
    exact hb.eq h1
  apply hzb1
  rw [hzba, key hA₀ ha₀, key hA₀' ha₀']
  exact ha.sq

end Conj

end CFSG.ClassicalInvolution.Q3.Q3AM

module

import CFSG.ClassicalInvolution.AschTight.CSM
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def conjRel (a : G) (l l' : ↥L) : Prop := (l' : G) = a⁻¹ * (l : G) * a

theorem conjRel_total {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    ∀ l : ↥L, ∃ l' : ↥L, conjRel a l l' := by
  intro l
  refine ⟨⟨a⁻¹ * (l : G) * a, ?_⟩, rfl⟩
  have h := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) (l : G)).mp l.2
  simpa using h

theorem largeEvenInduces_unique {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {rel : ↥L → ↥L → Prop} {φ ψ : MulAut R}
    (hφ : LargeEvenInduces θ rel φ) (hψ : LargeEvenInduces θ rel ψ)
    (hex : ∀ l : ↥L, ∃ l' : ↥L, rel l l') : φ = ψ := by
  ext x
  obtain ⟨q, rfl⟩ := θ.surjective x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l', hl'⟩ := hex l
  rw [hφ l l' hl', hψ l l' hl']

theorem largeEvenInduces_one {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {rel : ↥L → ↥L → Prop}
    (h : ∀ l l' : ↥L, rel l l' → l = l') : LargeEvenInduces θ rel 1 := by
  intro l l' hl
  rw [MulAut.one_apply, h l l' hl]

theorem largeEvenInduces_pow {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) {φ : MulAut R}
    (hφ : LargeEvenInduces θ (conjRel a) φ) (n : ℕ) :
    LargeEvenInduces θ (conjRel (a ^ n)) (φ ^ n) := by
  induction n with
  | zero =>
      refine largeEvenInduces_one (rel := conjRel (a ^ 0)) ?_
      intro l l' hl
      have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
      exact Subtype.ext hl'.symm
  | succ n ih =>
      intro l l' hl
      have hm' : a⁻¹ * (l : G) * a ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) (l : G)).mp l.2
        simpa using h
      show (φ ^ (n + 1)) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
      rw [pow_succ, MulAut.mul_apply]
      rw [hφ l ⟨_, hm'⟩ rfl]
      refine ih ⟨_, hm'⟩ l' ?_
      simp only [conjRel] at hl ⊢
      rw [hl, pow_succ']
      group

theorem largeEvenInduces_mul {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {a b : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hab : a * b = b * a) {φ ψ : MulAut R}
    (hφ : LargeEvenInduces θ (conjRel a) φ) (hψ : LargeEvenInduces θ (conjRel b) ψ) :
    LargeEvenInduces θ (conjRel (a * b)) (φ * ψ) := by
  intro l l' hl
  have hm : b⁻¹ * (l : G) * b ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) (l : G)).mp l.2
    simpa using h
  rw [MulAut.mul_apply]
  rw [hψ l ⟨_, hm⟩ rfl]
  refine hφ ⟨_, hm⟩ l' ?_
  simp only [conjRel] at hl ⊢
  rw [hl, hab]
  group

theorem exists_center_of_largeEvenInduces_one {R : Type} [Group R]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G))
    (h : LargeEvenInduces θ (conjRel a) (1 : MulAut R)) :
    ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L, a⁻¹ * (l : G) * a = (l : G) * (z : G) := by
  intro l
  have hm : a⁻¹ * (l : G) * a ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) (l : G)).mp l.2
    simpa using h
  have h1 := h l ⟨_, hm⟩ rfl
  simp only [MulAut.one_apply] at h1
  have heq : QuotientGroup.mk l = QuotientGroup.mk (⟨_, hm⟩ : ↥L) := θ.injective h1
  have hmem : l⁻¹ * (⟨_, hm⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.eq]
    exact heq
  refine ⟨l⁻¹ * (⟨_, hm⟩ : ↥L), hmem, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem centralizes_of_conjRel_center {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L, a⁻¹ * (l : G) * a = (l : G) * (z : G))
    (hL : Group.IsPerfect ↥L) :
    a ∈ Subgroup.centralizer (L : Set G) := by
  have hcomm : ∀ l ∈ L, l * a⁻¹ = a⁻¹ * l := by
    refine CFSG.ClassicalInvolution.Disconnected.AschTight.commute_of_commutator_mem_center
      (K := L) hL (inv_mem ha) ?_
    intro l hl
    obtain ⟨z, hz, hzeq⟩ := h ⟨l, hl⟩
    refine Subgroup.mem_map.mpr ⟨z⁻¹, inv_mem hz, ?_⟩
    have h2 : a⁻¹ * (l : G)⁻¹ * a = (z : G)⁻¹ * (l : G)⁻¹ := by
      calc a⁻¹ * (l : G)⁻¹ * a = (a⁻¹ * (l : G) * a)⁻¹ := by group
        _ = ((l : G) * (z : G))⁻¹ := by rw [hzeq]
        _ = (z : G)⁻¹ * (l : G)⁻¹ := by group
    have hzc : (l : G) * (z : G)⁻¹ = (z : G)⁻¹ * (l : G) := by
      have hc := Subgroup.mem_center_iff.mp (inv_mem hz) ⟨l, hl⟩
      exact congrArg Subtype.val hc
    calc ((z⁻¹ : ↥L) : G) = (z : G)⁻¹ := rfl
      _ = (l : G) * (z : G)⁻¹ * (l : G)⁻¹ := by
          rw [hzc]
          group
      _ = (l : G) * ((z : G)⁻¹ * (l : G)⁻¹) := by group
      _ = (l : G) * (a⁻¹ * (l : G)⁻¹ * a) := by rw [h2]
      _ = (l : G) * a⁻¹ * (l : G)⁻¹ * (a⁻¹)⁻¹ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : l * a⁻¹ = a⁻¹ * l := hcomm l hl
  have h1' : a * l⁻¹ = l⁻¹ * a := by
    have := congrArg Inv.inv h1
    simpa using this
  calc l * a = l * (a * l⁻¹) * l := by group
    _ = l * (l⁻¹ * a) * l := by rw [h1']
    _ = a * l := by group

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Hull
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvolutionInner
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Borel

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

namespace Lemma34

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

namespace Minimal

variable (m : Minimal S A₁ A₂)
include m

theorem exists_mem_centralizer_of_involution {K : Subgroup G} [K.Normal]
    (hK : CFSG.Open.fusionIsBenderGroup K)
    (hKH : ∃ T : Sylow 2 K, (overlapClosure A₁ A₂).subgroupOf K ≤
      Subgroup.normalizer ((T : Subgroup K) : Set K))
    {x : G} (hx : x ∈ (A₁ : Set G) ∪ A₂) (hx2 : orderOf x = 2) :
    ∃ y ∈ K, y⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by
  have hx1 : x ≠ 1 := (orderOf_eq_prime_iff.mp hx2).2
  have hxx : x * x = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hx2).1
  obtain ⟨T, hT⟩ := hKH
  let α : MulAut K := MulAut.conjNormal x
  have hα : ∀ k : K, ((α k : K) : G) = x * k * x⁻¹ := fun k => MulAut.conjNormal_apply x k
  have hαα : α * α = 1 := by
    ext k
    change (((α (α k)) : K) : G) = (k : G)
    rw [hα, hα]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
    rw [hxinv]
    calc x * (x * (k : G) * x) * x = (x * x) * k * (x * x) := by group
      _ = k := by rw [hxx, one_mul, mul_one]
  have hfix : ∀ k : K, α k = k → k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    intro k hk
    apply hT
    rw [Subgroup.mem_subgroupOf]
    apply m.centralizer_le hx hx1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val hk
    rw [hα] at h1
    calc (k : G) * x = x * k * x⁻¹ * x := by rw [h1]
      _ = x * k := by group
  obtain ⟨y, hy⟩ :=
    AschbacherToolkit.bender_involution_automorphism_inner K hK α hαα ⟨T, hfix⟩
  refine ⟨y, y.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : x * k * x⁻¹ = (y : G) * k * (y : G)⁻¹ := by
    have := congrArg (fun β : MulAut K => ((β ⟨k, hk⟩ : K) : G)) hy
    simp only [hα, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  calc k * ((y : G)⁻¹ * x) = (y : G)⁻¹ * ((y : G) * k * (y : G)⁻¹) * x := by group
    _ = (y : G)⁻¹ * (x * k * x⁻¹) * x := by rw [h1]
    _ = (y : G)⁻¹ * x * k := by group

theorem false
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity) : False := by
  have h := m.hyp
  set H := overlapClosure A₁ A₂ with hHdef
  obtain ⟨K, hKn, hK, hse, hKr⟩ := m.exists_bender himp hcov
  have hKs : IsSimpleGroup K :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hK
  obtain ⟨T, hT⟩ := eq_normalizer_of_stronglyEmbedded hKs hse hKr
  have hKH : ¬ K ≤ H := fun hle => hse.1 (by
    rw [eq_top_iff]
    intro k _
    exact hle k.2)
  set Y : Subgroup G := K ⊔ (S : Subgroup G) with hYdef
  have hKY : K ≤ Y := le_sup_left
  have hSY : (S : Subgroup G) ≤ Y := le_sup_right
  have hAY : ∀ {A : Subgroup G}, A ≤ (S : Subgroup G) → A ≤ Y := fun hA => hA.trans hSY
  let KY : Subgroup Y := K.subgroupOf Y
  have hKYn : KY.Normal := Subgroup.Normal.subgroupOf hKn Y
  have hKYB : CFSG.Open.fusionIsBenderGroup KY :=
    CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKY).symm hK
  let P : Sylow 2 Y := S.subtype hSY
  have hP : (P : Subgroup Y) = (S : Subgroup G).subgroupOf Y := rfl
  have hKP : KY ⊔ (P : Subgroup Y) = ⊤ := by
    rw [hP, ← Subgroup.subgroupOf_sup hKY hSY, Subgroup.subgroupOf_self]
  have hunion : ∀ y : Y, y ∈ ((A₁.subgroupOf Y : Subgroup Y) : Set Y) ∪
      (A₂.subgroupOf Y : Subgroup Y) ↔ (y : G) ∈ (A₁ : Set G) ∪ A₂ := fun _ => Iff.rfl
  have hcl : ∀ a ∈ ((A₁.subgroupOf Y : Subgroup Y) : Set Y) ∪ (A₂.subgroupOf Y : Subgroup Y),
      ∀ y : Y, y⁻¹ * a * y ∈ (P : Subgroup Y) →
        y⁻¹ * a * y ∈ ((A₁.subgroupOf Y : Subgroup Y) : Set Y) ∪ (A₂.subgroupOf Y) := by
    intro a ha y hy
    rw [hunion] at ha ⊢
    rw [hP, Subgroup.mem_subgroupOf] at hy
    exact m.conj_mem ha hy
  have hC : ∀ x ∈ ((A₁.subgroupOf Y : Subgroup Y) : Set Y) ∪ (A₂.subgroupOf Y),
      x ∈ Subgroup.centralizer (KY : Set Y) → x = 1 := by
    intro x hx hxC
    by_contra hx1
    have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    apply hKH
    intro k hk
    apply m.centralizer_le ((hunion x).mp hx) hx1'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_iff.mp hxC ⟨k, hKY hk⟩ hk
    exact congrArg Subtype.val this
  have hinv : ∀ x ∈ ((A₁.subgroupOf Y : Subgroup Y) : Set Y) ∪ (A₂.subgroupOf Y),
      orderOf x = 2 → x ∈ KY ⊔ Subgroup.centralizer (KY : Set Y) := by
    intro x hx hx2
    have hx2' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
    obtain ⟨y, hyK, hyC⟩ := m.exists_mem_centralizer_of_involution hK
      ⟨T, le_of_eq hT⟩ ((hunion x).mp hx) hx2'
    have hyY : y ∈ Y := hKY hyK
    have hcY : y⁻¹ * (x : G) ∈ Y := Y.mul_mem (Y.inv_mem hyY) x.2
    have hxeq : x = ⟨y, hyY⟩ * ⟨y⁻¹ * x, hcY⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul]
      group)
    rw [hxeq]
    refine Subgroup.mul_mem_sup (show (⟨y, hyY⟩ : Y) ∈ KY from hyK) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC (k : G) hk)
  rcases AschbacherToolkit.bender_extension_strongly_closed_union_nested KY hKYB P hKP
      (A₁.subgroupOf Y) (A₂.subgroupOf Y)
      (fun x hx => by rw [hP]; exact h.le_one hx) (fun x hx => by rw [hP]; exact h.le_two hx)
      (commutator_subgroupOf_eq_bot h.comm Y) hcl hC hinv with hle | hle
  · exact m.not_le₁₂ fun x hx => hle (show (⟨x, hAY h.le_one hx⟩ : Y) ∈ A₁.subgroupOf Y from hx)
  · exact m.not_le₂₁ fun x hx => hle (show (⟨x, hAY h.le_two hx⟩ : Y) ∈ A₂.subgroupOf Y from hx)

end Minimal

theorem statement_all
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity) : ∀ n : ℕ, Statement n := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hX S A₁ A₂ h
    by_cases hle : Nat.card X ≤ n
    · exact ih X hle S A₁ A₂ h
    have IH : Statement (Nat.card X - 1) := fun Y _ _ hY => ih Y (by omega)
    by_contra hcon
    simp only [Concl, not_or] at hcon
    exact (Minimal.false ⟨h, hcon.2.1, hcon.2.2.1, IH, hcon.1, hcon.2.2.2⟩ himp hcov)

end Lemma34

open Lemma34

theorem lemma_3_4_trichotomy
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity)
    {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (A₁ A₂ : Subgroup G)
    (h₁ : A₁ ≤ S) (h₂ : A₂ ≤ S) (hc : ⁅A₁, A₂⁆ = ⊥) (hr₁ : 2 ≤ CFSG.Open.pRank 2 A₁)
    (hr₂ : 2 ≤ CFSG.Open.pRank 2 A₂)
    (hcl : relStronglyClosed (overlapClosure A₁ A₂) ((A₁ : Set G) ∪ A₂)
      (overlapClosure A₁ A₂ ⊓ S))
    (hcl₁ : relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₁ : Set G)))
    (hcl₂ : relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₂ : Set G))) :
    overlapClosure A₁ A₂ = ⊤ ∨
      A₁ ≤ A₂ ∨ A₂ ≤ A₁ ∨
      ((∃ g : G, rightConjugate A₁ g = A₂) ∧
        (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧
        Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) := by
  rcases statement_all himp hcov (Nat.card G) G le_rfl S A₁ A₂
      ⟨h₁, h₂, hc, hr₁, hr₂, hcl, hcl₁, hcl₂⟩ with h | h | h | ⟨⟨a, -, g, -, hg⟩, hd, hcard⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨_, hg⟩, hd, hcard⟩))

end CFSG.ComponentClassification.AschbacherStrongEmbedding

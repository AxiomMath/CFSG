module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin412

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3

open CFSG Subgroup CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Omega

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem conjSubgroup_mono {G : Type*} [Group G] (g : G) {N N' : Subgroup G} (h : N ≤ N') :
    conjSubgroup g N ≤ conjSubgroup g N' :=
  fun _ hx => h hx

theorem isSubnormal_fundamental_of_odd (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    (L.subgroupOf (centralizerΩ Q i)).IsSubnormal := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  have hLC := (IsFundamental.of_frame F).le_centralizerΩ
  have hL'C := (IsFundamental.of_frame_swap F).le_centralizerΩ
  have hconj : ∀ g ∈ centralizerΩ Q (F.La (-1)),
      F.La.range ⊔ F.swap.La.range ≤ conjSubgroup g (F.La.range ⊔ F.swap.La.range) := by
    intro g hg
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q hg.1
    have h1 := conjSubgroup_mono g (le_sup_left : F.La.range ≤ F.La.range ⊔ F.swap.La.range)
    have h3 := conjSubgroup_mono g (le_sup_right : F.swap.La.range ≤ F.La.range ⊔ F.swap.La.range)
    rcases Frame.conjSubgroup_La_range h2 hgO (commute_of_mem_centralizerΩ F hg) with
      ⟨-, hL, hL'⟩ | ⟨-, hL, hL'⟩
    · rw [hL] at h1
      rw [hL'] at h3
      exact sup_le h1 h3
    · rw [hL] at h1
      rw [hL'] at h3
      exact sup_le h3 h1
  have hcomm : ∀ x ∈ F.La.range, ∀ y ∈ F.swap.La.range, x * y = y * x := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact F.La_comm_La_swap A B
  have hnorm : F.La.range ⊔ F.swap.La.range ≤ normalizer (F.La.range : Set (V ≃ₗ[K] V)) := by
    refine sup_le le_normalizer fun y hy => ?_
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hcomm x hx y hy, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 := hcomm _ hx y⁻¹ (inv_mem hy)
      have h4 : x = y⁻¹ * (y * x * y⁻¹) * y := by group
      rw [h4, ← h1, inv_mul_cancel_right]
      exact hx
  have hle : F.La.range.subgroupOf (centralizerΩ Q (F.La (-1))) ≤
      (F.La.range ⊔ F.swap.La.range).subgroupOf (centralizerΩ Q (F.La (-1))) :=
    fun x hx => (le_sup_left : F.La.range ≤ _) hx
  refine Subgroup.IsSubnormal.step _ _ hle (Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩) ?_
  ·
    have h1 := hconj _ (inv_mem g.2) hn
    rw [mem_conjSubgroup, inv_inv] at h1
    exact h1
  ·
    rw [normal_subgroupOf_iff hle]
    intro a b ha hb
    exact (mem_normalizer_iff.mp (hnorm hb) a).mp ha

end Omega

section LongRoot

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {m : ℕ} (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)

omit [Finite K] in
theorem isSubnormal_range_longSL2_of_subnormal
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) (s t : Bool)
    (hΩ : ((F.toFrame hij s t).La.range.subgroupOf
      (centralizerΩ Q ((F.toFrame hij s t).La (-1)))).IsSubnormal) :
    ((F.longSL2 hij s t).range.subgroupOf
      (centralizer {F.longSL2 hij s t (-1)})).IsSubnormal := by
  set ρ := F.longSL2 hij s t with hρ
  set C := centralizer ({ρ (-1)} : Set (spinGroup Q)) with hC
  set fr := F.toFrame hij s t with hfr
  have hθ : ∀ A, spinAction Q (ρ A) = fr.La A := T1.spinAction_longSL2 F hij s t
  have hmapC : ∀ x : C, spinAction Q x ∈ centralizerΩ Q (fr.La (-1)) := by
    intro x
    rw [centralizerΩ, Subgroup.mem_inf]
    refine ⟨hrange ⟨x, rfl⟩, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ rfl
    have hx : ρ (-1) * (x : spinGroup Q) = x * ρ (-1) :=
      (mem_centralizer_iff.mp x.2) _ (Set.mem_singleton _)
    rw [← hθ, ← map_mul, hx, map_mul]
  let φ : C →* centralizerΩ Q (fr.La (-1)) :=
    ((spinAction Q).comp C.subtype).codRestrict _ hmapC
  set H := (fr.La.range.subgroupOf (centralizerΩ Q (fr.La (-1)))).comap φ with hH
  have hHs : H.IsSubnormal := hΩ.comap φ
  have hle : ρ.range.subgroupOf C ≤ H := by
    rintro x ⟨A, hA⟩
    show spinAction Q x ∈ fr.La.range
    exact ⟨A, by rw [← hθ, hA]; rfl⟩
  have hnorm : ((ρ.range.subgroupOf C).subgroupOf H).Normal := by
    rw [normal_subgroupOf_iff hle]
    intro a b ha hb
    obtain ⟨A, hA⟩ : spinAction Q b ∈ fr.La.range := hb
    have hc : (ρ A)⁻¹ * (b : spinGroup Q) ∈ center (spinGroup Q) := by
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, hA, inv_mul_cancel]
    obtain ⟨B, hB⟩ := ha
    have hca : (a : spinGroup Q) * ((ρ A)⁻¹ * (b : spinGroup Q)) =
        ((ρ A)⁻¹ * (b : spinGroup Q)) * a := mem_center_iff.mp hc a
    have hB' : ρ B = (a : spinGroup Q) := hB
    refine ⟨A * B * A⁻¹, ?_⟩
    show ρ (A * B * A⁻¹) = ((b * a * b⁻¹ : C) : spinGroup Q)
    rw [map_mul, map_mul, map_inv, hB', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc ρ A * (a : spinGroup Q) * (ρ A)⁻¹ =
          ρ A * ((a : spinGroup Q) * ((ρ A)⁻¹ * (b : spinGroup Q))) *
            ((ρ A)⁻¹ * (b : spinGroup Q))⁻¹ * (ρ A)⁻¹ := by group
      _ = (b : spinGroup Q) * a * (b : spinGroup Q)⁻¹ := by rw [hca]; group
  exact Subgroup.IsSubnormal.step _ H hle hHs hnorm

theorem isSubnormal_range_longSL2_of_odd (hodd : Odd (Nat.card K))
    (hrange : (spinAction Q).range ≤ elementaryGroup Q) (s t : Bool) :
    ((F.longSL2 hij s t).range.subgroupOf
      (centralizer {F.longSL2 hij s t (-1)})).IsSubnormal :=
  isSubnormal_range_longSL2_of_subnormal F hij hrange s t
    (isSubnormal_fundamental_of_odd hodd (IsFundamental.of_frame _))

end LongRoot

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3

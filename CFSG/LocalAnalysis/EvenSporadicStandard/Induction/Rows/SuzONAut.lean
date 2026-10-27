module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78 Cover
open scoped commutatorElement

structure AutFixFacts {Y : Type} [Group Y] (K : Subgroup Y) (b : ℕ) : Prop where
  solvable : Group.IsSolvable ↥(autFixing K)
  elem : ElemBound b ↥(autFixing K)
  inner : ∀ β ∈ autFixing K, ∃ y : Y, β = MulAut.conj y

theorem autFixFacts_of_top {Y : Type} [Group Y] {K : Subgroup Y} {b : ℕ}
    (hs : Group.IsSolvable ↥(autCentralizer (⊤ : Subgroup Y) K))
    (he : ElemBound b ↥(autCentralizer (⊤ : Subgroup Y) K))
    (hi : ∀ α ∈ autCentralizer (⊤ : Subgroup Y) K,
      ∃ g : ↥(⊤ : Subgroup Y), α = MulAut.conj g) : AutFixFacts K b := by
  let e : MulAut Y ≃* MulAut ↥(⊤ : Subgroup Y) := MulAut.congr (Subgroup.topEquiv (G := Y)).symm
  have happ : ∀ (β : MulAut Y) (k : ↥(⊤ : Subgroup Y)), ((e β k : ↥(⊤ : Subgroup Y)) : Y) = β k :=
    fun β k => rfl
  have hmem : ∀ β ∈ autFixing K, e β ∈ autCentralizer (⊤ : Subgroup Y) K := by
    intro β hβ k hk
    apply Subtype.ext
    rw [happ]
    exact hβ k hk
  let f : ↥(autFixing K) →* ↥(autCentralizer (⊤ : Subgroup Y) K) :=
    (e.toMonoidHom.comp (autFixing K).subtype).codRestrict (autCentralizer (⊤ : Subgroup Y) K)
      (fun β => hmem β β.2)
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (e.injective (congrArg Subtype.val h))
  refine ⟨Group.isSolvable_of_isSolvable_injective hf, he.of_injective hf, fun β hβ => ?_⟩
  · obtain ⟨g, hg⟩ := hi _ (hmem β hβ)
    refine ⟨(g : Y), e.injective ?_⟩
    rw [hg]
    ext z
    rw [happ]
    simp [MulAut.conj_apply]

section Lift

variable {H : Type} [Group H] {L K : Subgroup H}

theorem autCentralizer_elem_of_quotient {b : ℕ} (hLperf : Group.IsPerfect ↥L)
    (hY : ElemBound b ↥(autFixing ((K.subgroupOf L).map (q ↥L)))) :
    ElemBound b ↥(autCentralizer L K) :=
  hY.of_injective (autCentralizerToFixing_injective hLperf)

theorem autCentralizer_twoExp_of_quotient {b : ℕ} (hLperf : Group.IsPerfect ↥L)
    (hY : ∀ A : Subgroup ↥(autFixing ((K.subgroupOf L).map (q ↥L))), IsPGroup 2 A →
      (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ b) :
    ∀ A : Subgroup ↥(autCentralizer L K), IsPGroup 2 A → (∀ x ∈ A, x * x = 1) ∧
      Nat.card A ≤ b := by
  intro A hA
  have hf := autCentralizerToFixing_injective (L := L) (K := K) hLperf
  obtain ⟨h1, h2⟩ := hY (A.map autCentralizerToFixing) (hA.map _)
  refine ⟨fun x hx => hf ?_, ?_⟩
  · have := h1 _ ⟨x, hx, rfl⟩
    rwa [← map_mul, ← map_one autCentralizerToFixing] at this
  · rwa [Subgroup.card_map_of_injective hf] at h2

end Lift

section Cover

variable {H : Type} [Group H] {L K : Subgroup H}

theorem exists_oddCentralCover (hodd : Odd (Nat.card (center ↥L))) (hKL : K ≤ L) :
    ∃ π : ↥K →* ↥((K.subgroupOf L).map (q ↥L)), Function.Surjective π ∧ π.ker ≤ center ↥K ∧
      Odd (Nat.card π.ker) := by
  let e : ↥K ≃* ↥(K.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hKL).symm
  let π : ↥K →* ↥((K.subgroupOf L).map (q ↥L)) :=
    ((q ↥L).subgroupMap (K.subgroupOf L)).comp e.toMonoidHom
  have hπ : ∀ k : ↥K, π k = 1 ↔ q ↥L ⟨(k : H), hKL k.2⟩ = 1 := fun k => by
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have hker : ∀ k : ↥K, k ∈ π.ker → (⟨(k : H), hKL k.2⟩ : ↥L) ∈ center ↥L := fun k hk =>
    q_eq_one_iff.1 ((hπ k).1 (MonoidHom.mem_ker.1 hk))
  refine ⟨π, ((q ↥L).subgroupMap_surjective _).comp e.surjective, ?_, ?_⟩
  · intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 (hker k hk) ⟨(g : H), hKL g.2⟩
    exact Subtype.ext (congrArg (fun x : ↥L => (x : H)) h1)
  · let f : ↥π.ker →* ↥(center ↥L) :=
      { toFun := fun k => ⟨⟨(k : ↥K).1, hKL (k : ↥K).2⟩, hker k k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥(center ↥L) => ((z : ↥L) : H)) h))
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)

end Cover

theorem quotientCenterEquiv_of_centralCover {X D : Type} [Group X] [Group D] (π : X →* D)
    (hs : Function.Surjective π) (hker : π.ker ≤ center X) (hX : Group.IsPerfect X) :
    Nonempty ((X ⧸ center X) ≃* (D ⧸ center D)) := by
  have hX' : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 hX
  let g : X →* D ⧸ center D := (QuotientGroup.mk' (center D)).comp π
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hs
  have hker' : center X = g.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    show x ∈ center X ↔ (π x : D ⧸ center D) = 1
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨y, rfl⟩ := hs d
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    · intro hx
      have hconj : ∀ k : X, ∃ z ∈ center X, x * k * x⁻¹ = z * k := by
        intro k
        refine ⟨(x * k * x⁻¹) * k⁻¹, hker (MonoidHom.mem_ker.2 ?_), by group⟩
        have hc : π x * π k = π k * π x := (Subgroup.mem_center_iff.1 hx (π k)).symm
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        calc π x * π k * (π x)⁻¹ * (π k)⁻¹ = (π k * π x) * (π x)⁻¹ * (π k)⁻¹ := by rw [hc]
          _ = 1 := by group
      have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ centralizer ({x} : Set X) := by
        refine Subgroup.commutator_le.2 fun k₁ _ k₂ _ => ?_
        obtain ⟨z₁, hz₁, h₁⟩ := hconj k₁
        obtain ⟨z₂, hz₂, h₂⟩ := hconj k₂
        rw [mem_centralizer_singleton_iff]
        have hxc : x * ⁅k₁, k₂⁆ * x⁻¹ = ⁅k₁, k₂⁆ := by
          calc x * ⁅k₁, k₂⁆ * x⁻¹ = ⁅x * k₁ * x⁻¹, x * k₂ * x⁻¹⁆ := by
                simp only [commutatorElement_def]; group
            _ = ⁅z₁ * k₁, z₂ * k₂⁆ := by rw [h₁, h₂]
            _ = ⁅k₁, k₂⁆ := commutator_central_mul hz₁ hz₂ k₁ k₂
        calc ⁅k₁, k₂⁆ * x = (x * ⁅k₁, k₂⁆ * x⁻¹) * x := by rw [hxc]
          _ = x * ⁅k₁, k₂⁆ := by group
      rw [hX'] at hcomm
      rw [Subgroup.mem_center_iff]
      intro k
      exact mem_centralizer_singleton_iff.1 (hcomm (Subgroup.mem_top k))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end CFSG.EvenSporadicStandard.Induction

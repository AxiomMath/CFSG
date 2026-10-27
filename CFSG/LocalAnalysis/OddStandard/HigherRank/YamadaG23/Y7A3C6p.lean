module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3NF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2M6c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2KSub
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_comm_conj_mem {C : Subgroup G} {x : G} (hx : ∀ m ∈ C, x * m * x⁻¹ ∈ C) {δ : G}
    (hδ : δ ∈ ⁅C, C⁆) : x * δ * x⁻¹ ∈ ⁅C, C⁆ := by
  rw [Subgroup.commutator_def] at hδ ⊢
  refine Subgroup.closure_induction
    (p := fun δ _ => x * δ * x⁻¹ ∈ Subgroup.closure
      {g | ∃ g₁ ∈ C, ∃ g₂ ∈ C, ⁅g₁, g₂⁆ = g}) ?_ ?_ ?_ ?_ hδ
  · rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    refine Subgroup.subset_closure ⟨x * g₁ * x⁻¹, hx g₁ hg₁, x * g₂ * x⁻¹, hx g₂ hg₂, ?_⟩
    simp only [commutatorElement_def]
    group
  · simpa using Subgroup.one_mem _
  · intro a b _ _ ha hb
    have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem y7a_C6_comm_eq (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) (h3a : ⁅M6 c.e, M6 c.e⁆ = V1 c.e) :
    ⁅C6 c.e, C6 c.e⁆ = AV1 c.e := by
  have h := c.y7acfg hH
  have hC6eq : C6 c.e = M6 c.e ⊔ zpowers c.s.t := h71.2.2.1
  have hM6C6 : M6 c.e ≤ C6 c.e := y7a_M6_le_C6 c
  have htC6 : c.s.t ∈ C6 c.e := hC6eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hC6X : C6 c.e ≤ y7aX c := y7a_C6_le_X c hH hF
  have hF_le : c.s.fr.F ≤ ⁅C6 c.e, C6 c.e⁆ := by
    intro u hu
    have hut : u * c.s.t ∈ conjClass (M3 c.s) c.s.t := by
      rw [hF.2.2.1.1.2.2.1]
      exact ⟨u, hu, rfl⟩
    obtain ⟨m, hmM3, hm_eq⟩ := hut
    have hmC6 : m ∈ C6 c.e := hM6C6 (h71.2.2.2.1 hmM3)
    have hu_eq : ⁅m, c.s.t⁆ = u := by
      rw [commutatorElement_def, ← hm_eq]
      group
    rw [← hu_eq]
    exact Subgroup.commutator_mem_commutator hmC6 htC6
  have hstab : ∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ ⁅C6 c.e, C6 c.e⁆,
      k * x * k⁻¹ ∈ ⁅C6 c.e, C6 c.e⁆ := by
    intro k hk x hx
    have hkX : k ∈ y7aX c := y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH hk)
    exact y7a_comm_conj_mem (fun m hm => y7a_C6_normal c hH hF k hkX m hm) hx
  have hA_le : c.s.fr.A ≤ ⁅C6 c.e, C6 c.e⁆ := y7a_A_le_of_F c hH hstab hF_le
  have hle : ⁅C6 c.e, C6 c.e⁆ ≤ AV1 c.e := by
    refine y7a_comm_le_of_gen (C := C6 c.e) (M := M6 c.e) (N := AV1 c.e) hC6eq ?_ ?_ ?_
    · intro x hx n hn
      exact (y7a_conj_AV h (hC6X hx).1 (hC6X hx).2 n).mp hn
    · intro m hm m' hm'
      exact Subgroup.mem_sup_right
        (y7a_M6_comm_le_V1 c hH hF (Subgroup.commutator_mem_commutator hm hm'))
    · intro m hm
      exact y7a_comm_t_AV c hH m (hC6X (hM6C6 hm))
  have hV_le : V1 c.e ≤ ⁅C6 c.e, C6 c.e⁆ :=
    h3a ▸ Subgroup.commutator_mono hM6C6 hM6C6
  exact le_antisymm hle (sup_le hA_le hV_le)

end CFSG.OddStandard.HigherRank.YamadaG23

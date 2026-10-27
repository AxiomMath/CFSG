module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.IndexTwo

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G}

theorem mul_comm_of_mem_isCyclic {K : Subgroup G} (hK : IsCyclic K) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x * y = y * x := by
  have h := congrArg Subtype.val ((IsCyclic.commGroup (α := K)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact h

theorem commutator_mem_of_mem_sup {L S : Subgroup G} (hS : S ≤ centralizer (L : Set G))
    (hab : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {x y : G} (hx : x ∈ L ⊔ S) (hy : y ∈ L ⊔ S) :
    x * y * x⁻¹ * y⁻¹ ∈ L := by
  obtain ⟨l₁, hl₁, s₁, hs₁, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hS hx
  obtain ⟨l₂, hl₂, s₂, hs₂, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hS hy
  have hsl : ∀ s ∈ S, ∀ l ∈ L, s * l = l * s := fun s hs l hl =>
    (mem_centralizer_iff.mp (hS hs) l hl).symm
  have h12 : s₁ * l₂ = l₂ * s₁ := hsl s₁ hs₁ l₂ hl₂
  have h21 : s₂ * l₁ = l₁ * s₂ := hsl s₂ hs₂ l₁ hl₁
  have hss : s₁ * s₂ = s₂ * s₁ := hab s₁ hs₁ s₂ hs₂
  have hxy : l₁ * s₁ * (l₂ * s₂) = (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * (l₂ * s₂ * (l₁ * s₁)) := by
    calc l₁ * s₁ * (l₂ * s₂) = l₁ * (s₁ * l₂) * s₂ := by group
      _ = l₁ * (l₂ * s₁) * s₂ := by rw [h12]
      _ = l₁ * l₂ * (s₁ * s₂) := by group
      _ = l₁ * l₂ * (s₂ * s₁) := by rw [hss]
      _ = l₁ * l₂ * l₁⁻¹ * (l₁ * s₂) * s₁ := by group
      _ = l₁ * l₂ * l₁⁻¹ * (s₂ * l₁) * s₁ := by rw [h21]
      _ = (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * (l₂ * s₂ * (l₁ * s₁)) := by group
  have : l₁ * s₁ * (l₂ * s₂) * (l₁ * s₁)⁻¹ * (l₂ * s₂)⁻¹ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by
    rw [hxy]; group
  rw [this]
  exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.sq_mem_sup_centralizer [Finite G] (h : StdHyp G L)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    {g : G} (hg : g ∈ normalizer (L : Set G)) : g ^ 2 ∈ L ⊔ centralizer (L : Set G) := by
  have hL : commutator L = ⊤ := h.standard.1.1
  set Inn := (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range with hInn
  have hnorm : Inn.Normal := normal_range_conj (L ⧸ center L)
  set ĝ := normalizerAction L ⟨g, hg⟩ with hĝ
  have hsq : ĝ ^ 2 ∈ Inn := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hout with h1 | h2
    · have := Subgroup.pow_index_mem Inn ĝ
      rw [h1, pow_one] at this
      exact Inn.pow_mem this 2
    · have := Subgroup.pow_index_mem Inn ĝ
      rwa [h2] at this
  have := (normalizerAction_mem_range_conj_iff hL (⟨g, hg⟩ ^ 2)).mp (by rw [map_pow]; exact hsq)
  simpa using this

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.le_of_perfect_of_le_centralizer [Finite G]
    (h : StdHyp G L)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    {c : G} (hc : c ∈ centralizer (L : Set G)) (hc2 : orderOf c = 2) {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) (hPc : P ≤ centralizer ({c} : Set G)) : P ≤ L := by
  classical
  set C := centralizer (L : Set G) with hCdef
  set M := centralizer ({c} : Set G) with hMdef
  have hrel := (h.relIndex_sup_centralizer_dvd hc hc2).trans hout
  obtain ⟨S', hS'cyc, hcS'⟩ := h.exists_cyclic_sylow_mem hc hc2
  have hCM : C ⊓ M = (S' : Subgroup C).map C.subtype :=
    h.centralizer_inf_centralizer_eq_map_sylow hc hc2 S' hS'cyc hcS'
  have hS'cyc' : IsCyclic ((S' : Subgroup C).map C.subtype) :=
    isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hab : ∀ a ∈ C ⊓ M, ∀ b ∈ C ⊓ M, a * b = b * a := fun a ha b hb => by
    rw [hCM] at ha hb
    exact mul_comm_of_mem_isCyclic hS'cyc' ha hb
  have hcomm : ∀ p₁ ∈ M, ∀ p₂ ∈ M, p₁ * p₂ * p₁⁻¹ * p₂⁻¹ ∈ L ⊔ C := by
    intro p₁ hp₁ p₂ hp₂
    rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
    · have : ((L ⊔ C).subgroupOf M).index = 1 := h1
      have htop : (L ⊔ C).subgroupOf M = ⊤ := Subgroup.index_eq_one.mp this
      have hm : (⟨p₁, hp₁⟩ : M) ∈ (L ⊔ C).subgroupOf M := by rw [htop]; trivial
      have hm₂ : (⟨p₂, hp₂⟩ : M) ∈ (L ⊔ C).subgroupOf M := by rw [htop]; trivial
      exact ((L ⊔ C).subgroupOf M).mul_mem (((L ⊔ C).subgroupOf M).mul_mem
        (((L ⊔ C).subgroupOf M).mul_mem hm hm₂) (((L ⊔ C).subgroupOf M).inv_mem hm))
        (((L ⊔ C).subgroupOf M).inv_mem hm₂)
    · have h2' : ((L ⊔ C).subgroupOf M).index = 2 := h2
      have hle := commutator_le_of_index_eq_two h2'
      have hmem : (⟨p₁, hp₁⟩ * ⟨p₂, hp₂⟩ * (⟨p₁, hp₁⟩ : M)⁻¹ * (⟨p₂, hp₂⟩ : M)⁻¹ : M) ∈
          commutator M := commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      exact hle hmem
  have hPD : P ≤ L ⊔ C := by
    conv_lhs => rw [← hP]
    rw [Subgroup.commutator_le]
    intro p₁ hp₁ p₂ hp₂
    exact hcomm p₁ (hPc hp₁) p₂ (hPc hp₂)
  have hPD' : P ≤ L ⊔ (C ⊓ M) := by
    rw [← centralizer_singleton_inf_sup_centralizer hc]
    exact le_inf hPc hPD
  conv_lhs => rw [← hP]
  rw [Subgroup.commutator_le]
  intro p₁ hp₁ p₂ hp₂
  exact commutator_mem_of_mem_sup (inf_le_left : C ⊓ M ≤ C) hab (hPD' hp₁) (hPD' hp₂)

end CFSG.EvenSporadicStandard.HSStd

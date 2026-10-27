module

public import CFSG.LargeExtraspecial.S5Syl
public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_mem_normalizer_conj (H : Hyp4 S g) (C : Cons311 S g) {x m : S.O}
    (hmM : m ∈ S.Mbar) (hx : ∀ l ∈ S.Lbar g, x * l = l * x)
    (hy : ∀ l ∈ S.Lbar g, m * x * m⁻¹ * l = l * (m * x * m⁻¹)) :
    ∃ n ∈ S.Mbar, n ∈ normalizer (S.Lbar g : Set S.O) ∧ m * x * m⁻¹ = n * x * n⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hmM
  set y := S.ρ k * x * (S.ρ k)⁻¹ with hydef
  set K := S.Mbar ⊓ centralizer ({y} : Set S.O) with hK
  have hLK : S.Lbar g ≤ K := fun l hl =>
    ⟨S.Lbar_le_Mbar g hl, mem_centralizer_singleton_iff.mpr (hy l hl).symm⟩
  have hLkK : S.Lbar ((k : G) * g) ≤ K := by
    intro l hl
    rw [mem_Lbar_mul_iff] at hl
    refine Subgroup.mem_inf.mpr ⟨S.Lbar_le_Mbar _ (by rw [mem_Lbar_mul_iff]; exact hl), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hx _ hl
    calc l * y = S.ρ k * ((S.ρ k)⁻¹ * l * S.ρ k * x) * (S.ρ k)⁻¹ := by rw [hydef]; group
      _ = S.ρ k * (x * ((S.ρ k)⁻¹ * l * S.ρ k)) * (S.ρ k)⁻¹ := by rw [h1]
      _ = y * l := by rw [hydef]; group
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge hLK (S4.isPGroup_Lbar S haQ)
  obtain ⟨T', hT', hLT'⟩ := exists_isSylowTwoIn_ge hLkK
    (S4.isPGroup_Lbar S (conj_mem_QG' S k.2 haQ))
  obtain ⟨c, hcK, hc⟩ := hT.exists_conj hT'
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup
      (hT.le.trans inf_le_left) hLT
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp hcK.1
  have hjk : S.Lbar (((j⁻¹ * k : S.M) : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro l hl
    apply hTN
    have hl' : (S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k) ∈ S.Lbar g := (mem_Lbar_mul_iff S _ g).mp hl
    have hmem : S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹ ∈
        S.Lbar ((k : G) * g) := conj_mem_Lbar_mul S k hl'
    have h2 := (hc _).mp (hLT' hmem)
    rw [← hj] at h2
    have e : (S.ρ j)⁻¹ * (S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹) *
        S.ρ j = l := by
      simp only [map_mul, map_inv]
      group
    rw [e] at h2
    exact h2
  have heq := C.weaklyClosed _ (j⁻¹ * k).2 hjk
  refine ⟨S.ρ (j⁻¹ * k), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [Lbar_mul S (j⁻¹ * k)] at heq
    exact mem_normalizer_of_map_conj_eq heq
  · have hcy : c * y = y * c := mem_centralizer_singleton_iff.mp hcK.2
    rw [← hj] at hcy
    simp only [map_mul, map_inv]
    calc S.ρ k * x * (S.ρ k)⁻¹ = (S.ρ j)⁻¹ * (S.ρ j * y) := by rw [hydef]; group
      _ = (S.ρ j)⁻¹ * (y * S.ρ j) := by rw [hcy]
      _ = (S.ρ j)⁻¹ * S.ρ k * x * ((S.ρ j)⁻¹ * S.ρ k)⁻¹ := by rw [hydef]; group

end CFSG.LargeExtraspecial.S5

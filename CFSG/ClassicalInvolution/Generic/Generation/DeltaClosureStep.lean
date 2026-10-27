module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureLayer
import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem isClassicalMember_conj_inv {L : Subgroup G} {z h : G}
    (hL : IsClassicalMember p f L (h * z * h⁻¹)) : IsClassicalMember p f (conjSub h⁻¹ L) z := by
  have := hL.conj h⁻¹
  have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
  rwa [e] at this

theorem le_rankThreeSpan_of_mem_omegaStar (hΩ : InClass p f Ω) (hF : FrameSide p f Ω A S)
    {L : Subgroup G} (hLs : L ∈ omegaStar p f Ω A S) : L ≤ rankThreeSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} := ⟨hconj _ _ hLΩ, le_centralizer hLa'⟩
  have hY : conjSub h⁻¹ L ≤ rankThreeSpan A :=
    (le_centralizingLayer hmem).trans (centralizingLayer_le_rankThreeSpan hconj hF.elem hF.card haA
      (hF.generation a haA ⟨K, hK, hKa⟩))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStar_of_commutes (hΩ : InClass p f Ω) (hF : FrameSide p f Ω A S)
    {L L' : Subgroup G} (hLs : L ∈ omegaStar p f Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStar p f Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hYH := centralizingLayer_le_rankThreeSpan hconj hF.elem hF.card haA
    (hF.generation a haA ⟨K, hKS, hKa⟩)
  have hz₀' : IsClassicalMember p f M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember p f L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

end CFSG.ClassicalInvolution.Generic.DeltaClosure

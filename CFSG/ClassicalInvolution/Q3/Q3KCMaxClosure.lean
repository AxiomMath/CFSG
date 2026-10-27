module

public import CFSG.ClassicalInvolution.Balance.BootstrapClosure
public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Closure

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)} {H : Subgroup G}

@[expose] def omegaStarH (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G))
    (H : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ H, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember3 K z ∧ IsClassicalMember3 L (h * z * h⁻¹)}

theorem le_of_mem_omegaStarH (hΩ : InClass3 Ω)
    (hY : ∀ a ∈ A, IsFrameInvolution3 S a → centralizingLayer Ω {a} ≤ H)
    {L : Subgroup G} (hLs : L ∈ omegaStarH Ω A S H) : L ≤ H := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hconj _ _ hLΩ, isSubnormal_le hLa'.subnormal⟩
  have hYH : conjSub h⁻¹ L ≤ H :=
    (le_centralizingLayer hmem).trans (hY a haA ⟨K, hK, hKa⟩)
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hYH h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarH_of_commutes (hΩ : InClass3 Ω)
    (hY : ∀ a ∈ A, IsFrameInvolution3 S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarH Ω A S H) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarH Ω A S H := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember3_conj_inv hLa
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
    hlink a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hYH := hY a haA ⟨K, hKS, hKa⟩
  have hz₀' : IsClassicalMember3 M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember3 L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem mem_omegaStarH_of_omegaConnected (hΩ : InClass3 Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hY : ∀ a ∈ A, IsFrameInvolution3 S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarH Ω A S H := by
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨z, hzA, hz⟩ := hinv K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarH Ω A S H :=
    ⟨hS hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarH Ω A S H := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarH_of_commutes hΩ hY hlink ih hbc.1 hbc.2
  exact key L (hconn K₀ (hS hK₀) L hLΩ)

theorem eq_top_of_frame3 (hΩ : InClass3 Ω) (hS : S ⊆ Ω) (hne : S.Nonempty)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember3 K z)
    (hY : ∀ a ∈ A, IsFrameInvolution3 S a → centralizingLayer Ω {a} ≤ H)
    (hlink : ∀ a ∈ A, IsFrameInvolution3 S a → InvolutionLink3 Ω A S a)
    (hconn : OmegaConnected Ω) : H = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_of_mem_omegaStarH hΩ hY
    (mem_omegaStarH_of_omegaConnected hΩ hS hne hinv hY hlink hconn hLΩ)

end Closure

end CFSG.ClassicalInvolution.Q3.Q3KC

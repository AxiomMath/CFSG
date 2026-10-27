module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadS3Lift
public import CFSG.ClassicalInvolution.Q3.Q3T8B05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Tri


variable {G : Type} [Group G] [Finite G]

theorem BadStd8.exists_nbr_conj_of_commutes [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) {N₁ N₂ : Subgroup G} (hN₁ : N₁ ∈ omegaNbr Ω K)
    (hN₂ : N₂ ∈ omegaNbr Ω K)
    (hcomm : ∀ a ∈ layerImage Ω K z N₁, ∀ b ∈ layerImage Ω K z N₂, a * b = b * a) :
    ∃ N₃ ∈ omegaNbr Ω K, (N₃ = N₁ ∨ N₃ ∈ omegaNbr Ω N₁) ∧
      layerImage Ω K z N₃ = layerImage Ω K z N₂ := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hYC : nbrLayer Ω K z ≤ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    h.normalizer_eq_centralizer
  obtain ⟨hN₁Ω, hN₁K, T₁, hT₁R, hT₁N₁, hT₁nK⟩ := id hN₁
  obtain ⟨hN₂Ω, hN₂K, T₂, hT₂R, hT₂N₂, hT₂nK⟩ := id hN₂
  have hT₁s : IsSylow2In T₁ N₁ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN₁Ω hT₁R hT₁N₁
  have hT₂s : IsSylow2In T₂ N₂ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN₂Ω hT₂R hT₂N₂
  have hT₁C : T₁ ≤ exactCore3 z N₁ := le_inf hT₁N₁ (hNC ▸ hT₁nK)
  have hT₂C : T₂ ≤ exactCore3 z N₂ := le_inf hT₂N₂ (hNC ▸ hT₂nK)
  have hT₁Y : T₁ ≤ nbrLayer Ω K z := hT₁C.trans (exactCore3_le_nbrLayer hN₁)
  have hT₂Y : T₂ ≤ nbrLayer Ω K z := hT₂C.trans (exactCore3_le_nbrLayer hN₂)
  have hcomm' : ∀ a ∈ T₁, ∀ b ∈ T₂, ⁅a, b⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
    intro a ha b hb
    have haY : a ∈ nbrLayer Ω K z := hT₁Y ha
    have hbY : b ∈ nbrLayer Ω K z := hT₂Y hb
    have ha' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨a, haY⟩ ∈
        layerImage Ω K z N₁ := ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr (hT₁C ha), rfl⟩
    have hb' : QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω K z)) ⟨b, hbY⟩ ∈
        layerImage Ω K z N₂ := ⟨⟨b, hbY⟩, Subgroup.mem_subgroupOf.mpr (hT₂C hb), rfl⟩
    have hc := (mk_comm_eq_iff haY hbY).mp (hcomm _ ha' _ hb')
    rw [commutatorElement_def]
    exact hc
  obtain ⟨p, hpO, hp⟩ := exists_conj_commutes_of_commutator_mem hT₁s.2.1 hT₂s.2.1
    (oddCoreOf_odd_natCard _) (fun y hy => mem_normalizer_oddCoreOf_of_mem (hT₁Y hy))
    (fun y hy => mem_normalizer_oddCoreOf_of_mem (hT₂Y hy)) hcomm'
  have hpY : p ∈ nbrLayer Ω K z := oddCoreOf_le_self _ hpO
  have hpC : p ∈ Subgroup.centralizer ({z} : Set G) := hYC hpY
  have hpK : conjSub p K = K := mem_normalizer_iff_conjSub_eq.mp (hNC ▸ hpC)
  have hN₃K : conjSub p N₂ ∈ omegaNbr Ω K := conjSub_mem_omegaNbr_of_conjSub_eq hΩ hpK hN₂
  have hcore : exactCore3 z (conjSub p N₂) = conjSub p (exactCore3 z N₂) := by
    have e := exactCore3_conjSub p z N₂
    rw [conj_eq_of_mem_centralizer_singleton hpC] at e
    exact e
  have himg : layerImage Ω K z (conjSub p N₂) = layerImage Ω K z N₂ := by
    show Subgroup.map _ ((exactCore3 z (conjSub p N₂)).subgroupOf (nbrLayer Ω K z)) =
      Subgroup.map _ ((exactCore3 z N₂).subgroupOf (nbrLayer Ω K z))
    rw [hcore]
    exact map_mk_subgroupOf_conjSub_oddCore hpO (exactCore3_le_nbrLayer hN₂)
  refine ⟨conjSub p N₂, hN₃K, ?_, himg⟩
  by_cases hEq : conjSub p N₂ = N₁
  · exact Or.inl hEq
  right
  have hT₂p : conjSub p T₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hT₂R p
  have h4 : 4 ≤ Nat.card T₁ := by have := hΩ.eight_le_of_mem_RSet hT₁R; omega
  have hnorm : conjSub p T₂ ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hN₁y : conjSub (p * b * p⁻¹) N₁ ∈ Ω := hΩ.conjInvariant _ N₁ hN₁Ω
    have hT₁y : T₁ ≤ conjSub (p * b * p⁻¹) N₁ := by
      intro x hx
      rw [mem_conjSub_iff]
      have hxy : (p * b * p⁻¹)⁻¹ * x * (p * b * p⁻¹) = x := by
        have := hp x hx b hb
        calc (p * b * p⁻¹)⁻¹ * x * (p * b * p⁻¹) = (p * b * p⁻¹)⁻¹ * (x * (p * b * p⁻¹)) := by
              rw [mul_assoc]
          _ = (p * b * p⁻¹)⁻¹ * ((p * b * p⁻¹) * x) := by rw [this]
          _ = x := by group
      rw [hxy]
      exact hT₁N₁ hx
    exact mem_normalizer_iff_conjSub_eq.mpr
      (hΩ.eq_of_le_of_le hN₁Ω hN₁y hT₁s.2.1 h4 hT₁N₁ hT₁y).symm
  exact ⟨hN₃K.1, hEq, conjSub p T₂, hT₂p, conjSub_mono hT₂N₂, hnorm⟩

theorem BadStd8.false_of_layerImage_commutes [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (h : BadStd8 Ω K J S R T W z t) {N₁ N₂ N₃ : Subgroup G} (hN₁ : N₁ ∈ omegaNbr Ω K)
    (hN₂ : N₂ ∈ omegaNbr Ω K) (hN₃ : N₃ ∈ omegaNbr Ω K)
    (hc₂ : ∀ a ∈ layerImage Ω K z N₁, ∀ b ∈ layerImage Ω K z N₂, a * b = b * a)
    (hc₃ : ∀ a ∈ layerImage Ω K z N₁, ∀ b ∈ layerImage Ω K z N₃, a * b = b * a)
    (h₁₂ : layerImage Ω K z N₂ ≠ layerImage Ω K z N₁)
    (h₁₃ : layerImage Ω K z N₃ ≠ layerImage Ω K z N₁)
    (h₂₃ : layerImage Ω K z N₃ ≠ layerImage Ω K z N₂) : False := by
  classical
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  obtain ⟨N₂', hN₂', hadj₂, himg₂⟩ := BadStd8.exists_nbr_conj_of_commutes h hN₁ hN₂ hc₂
  obtain ⟨N₃', hN₃', hadj₃, himg₃⟩ := BadStd8.exists_nbr_conj_of_commutes h hN₁ hN₃ hc₃
  have hN₂'₁ : N₂' ∈ omegaNbr Ω N₁ := by
    rcases hadj₂ with hEq | hadj
    · exact absurd (by rw [← himg₂, hEq]) h₁₂
    · exact hadj
  have hN₃'₁ : N₃' ∈ omegaNbr Ω N₁ := by
    rcases hadj₃ with hEq | hadj
    · exact absurd (by rw [← himg₃, hEq]) h₁₃
    · exact hadj
  obtain ⟨v₁, hv₁⟩ := hΩ.exists_uniqueInvolution hN₁.1
  obtain ⟨v₂, hv₂⟩ := hΩ.exists_uniqueInvolution hN₂'.1
  obtain ⟨v₃, hv₃⟩ := hΩ.exists_uniqueInvolution hN₃'.1
  obtain ⟨S', R', T', W', hstd'⟩ :=
    c27_setupB hstd.stand (hnt K hstd.stand.mem) hstd.hz hN₁ hv₁
  have e₂ : v₂ = z * v₁ :=
    eq_mul_of_nbr_nbr_of_noFrame hstd' h.not_fuzzyFrame hN₂' hN₂'₁ hv₂
  have e₃ : v₃ = z * v₁ :=
    eq_mul_of_nbr_nbr_of_noFrame hstd' h.not_fuzzyFrame hN₃' hN₃'₁ hv₃
  have hmem : N₃' ∈ twinSet Ω N₂' := ⟨hN₃'.1, v₂, hv₂, by rw [e₂, ← e₃]; exact hv₃⟩
  have h32 : N₃' = N₂' := hnt N₂' hN₂'.1 N₃' hmem
  exact h₂₃ (by rw [← himg₃, ← himg₂, h32])

end Tri

end CFSG.ClassicalInvolution.Q3.Q3AM

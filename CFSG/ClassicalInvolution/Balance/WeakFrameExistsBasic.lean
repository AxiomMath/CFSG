module

public import CFSG.ClassicalInvolution.Generic.StepLayer
public import CFSG.ClassicalInvolution.Generic.StepQuasisimple
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Member

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification
open scoped MatrixGroups

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem isClassicalMember_iff_weakMember {K : Subgroup G} {z : G} :
    IsClassicalMember p f K z ↔ WeakMember (GaloisField p f) K z :=
  ⟨fun h => ⟨h.orderOf_eq_two, h.mem, h.perfect, h.subnormal, h.nonempty_equiv⟩,
   fun h => ⟨h.orderOf_eq_two, h.mem, h.perfect, h.subnormal, h.nonempty_equiv⟩⟩

end Basic

section Dichotomy

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem isComponentOf_map_oddQuotient (hq : 4 ≤ p ^ f) {K : Subgroup Y} {z : Y}
    (hK : IsClassicalMember p f K z) (hKsub : IsSubnormal K ⊤) :
    IsComponentOf (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) ⊤ := by
  set N := classicalInvolutionOddCore Y with hN
  set π := QuotientGroup.mk' N with hπ
  have hO : classicalInvolutionOddCore (Y ⧸ N) = ⊥ := OddCore.quotient_corefree Y
  have hK' := hK.map_oddQuotient
  have hsub' : IsSubnormal (K.map π) ⊤ := by
    have := Components.chain_map π hKsub
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)] at this
  have hKO : classicalInvolutionOddCore (K.map π) = ⊥ :=
    OddCore.subnormal_corefree hO (K.map π) hsub'
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf]; exact hq
  obtain ⟨e⟩ := hK'.nonempty_equiv
  have hqs : CFSG.Open.IsQuasisimple (↥(K.map π) ⧸ classicalInvolutionOddCore (K.map π)) :=
    Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4)
  have equiv : ↥(K.map π) ≃* (↥(K.map π) ⧸ classicalInvolutionOddCore (K.map π)) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (classicalInvolutionOddCore (K.map π)))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hKO]),
        QuotientGroup.mk'_surjective _⟩
  exact ⟨le_top, hsub', Components.quasisimple_of_equiv equiv hqs⟩

theorem dichotomy_oddQuotient (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Λ : Set (Subgroup Y)}
    (hΛ : InClass p f Λ) {K L : Subgroup Y} {z zL : Y} (hK : IsClassicalMember p f K z)
    (hL : IsClassicalMember p f L zL) (hKsub : IsSubnormal K ⊤) :
    Commutes (K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
        (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y))) ∨
      QuotientGroup.mk' (classicalInvolutionOddCore Y) zL =
        QuotientGroup.mk' (classicalInvolutionOddCore Y) z := by
  set N := classicalInvolutionOddCore Y with hN
  set π := QuotientGroup.mk' N with hπ
  have hq4 : 4 ≤ p ^ f := by omega
  have hO : classicalInvolutionOddCore (Y ⧸ N) = ⊥ := OddCore.quotient_corefree Y
  have hlayer : Layer.subgroup (Y ⧸ N) = ⊤ :=
    layer_eq_top l2PrimeBalance hq4 hO (inClass_oddQuotient hΛ)
  have hcomp := isComponentOf_map_oddQuotient hq4 hK hKsub
  have hL' := hL.map_oddQuotient
  rcases hL'.le_or_le_centralizer_of_component hq4 hlayer hcomp with h | h
  · right
    have hK' := hK.map_oddQuotient
    have hsub' : IsSubnormal (K.map π) ⊤ := hcomp.2.1
    have hKO : classicalInvolutionOddCore (K.map π) = ⊥ :=
      OddCore.subnormal_corefree hO (K.map π) hsub'
    obtain ⟨e⟩ := hK'.nonempty_equiv
    have hKO' : componentClassificationOddCore ↥(K.map π) = ⊥ := hKO
    have equiv : ↥(K.map π) ≃* (↥(K.map π) ⧸ classicalInvolutionOddCore (K.map π)) :=
      MulEquiv.ofBijective (QuotientGroup.mk' (classicalInvolutionOddCore (K.map π)))
        ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hKO]),
          QuotientGroup.mk'_surjective _⟩
    let φ : ↥(K.map π) →* SL(2, GaloisField p f) := (equiv.trans e).toMonoidHom
    have hφ : IsChart (GaloisField p f) (K.map π) φ :=
      ⟨(equiv.trans e).surjective, by
        have : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr (equiv.trans e).injective
        rw [this, hKO']⟩
    have hz := (isClassicalMember_iff_weakMember.mp hK').isCentralInvolution
    have hx : π zL ∈ K.map π := h hL'.mem
    have hsq : π zL * π zL = 1 := by
      have h2 : zL * zL = 1 := by
        have := pow_orderOf_eq_one zL
        rw [hL.orderOf_eq_two, pow_two] at this
        exact this
      rw [← map_mul, h2, map_one]
    rcases hφ.eq_one_or_eq_of_sq (odd_natCard_galoisField hp2 hq) hz hx hsq with h1 | h1
    · exfalso
      have h2 : orderOf (π zL) = 2 := orderOf_mk_oddCore_eq_two (X := Y) hL.orderOf_eq_two
      rw [h1] at h2
      simp at h2
    · exact h1
  · left
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (h hb) a ha

end Dichotomy

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem inf_oddCoreIn_le {K Y : Subgroup G} (hKY : K ≤ Y) : K ⊓ oddCoreIn Y ≤ oddCoreIn K := by
  refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : g * x * g⁻¹ ∈ K ↔ x ∈ K := by
      constructor
      · intro h
        have := K.mul_mem (K.mul_mem (K.inv_mem hg) h) hg
        simpa [mul_assoc] using this
      · intro h
        exact K.mul_mem (K.mul_mem hg h) (K.inv_mem hg)
    have h2 : g * x * g⁻¹ ∈ oddCoreIn Y ↔ x ∈ oddCoreIn Y := by
      constructor
      · intro h
        have := conj_mem_oddCoreIn (X := Y) (Y.inv_mem (hKY hg)) h
        simpa [mul_assoc] using this
      · intro h
        exact conj_mem_oddCoreIn (hKY hg) h
    simp only [Subgroup.mem_inf, h1, h2]
  · exact (odd_card_oddCoreIn Y).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

omit [Finite G] in
theorem IsChart.map_eq_one_of_mem_oddCoreIn {F : Type*} [Field F] {K : Subgroup G}
    {φ : ↥K →* SL(2, F)} (hφ : IsChart F K φ) {x : G} (hx : x ∈ K) (hO : x ∈ oddCoreIn K) :
    φ ⟨x, hx⟩ = 1 := by
  have h : (⟨x, hx⟩ : ↥K) ∈ componentClassificationOddCore ↥K :=
    (Subgroup.mem_map_iff_mem K.subtype_injective).mp hO
  rw [← hφ.ker_eq] at h
  exact h

end OddCore

end CFSG.ClassicalInvolution.Balance

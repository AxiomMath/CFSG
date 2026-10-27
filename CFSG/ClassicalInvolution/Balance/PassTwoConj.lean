module

public import CFSG.ClassicalInvolution.Balance.PassTwoP1
public import CFSG.ClassicalInvolution.Generic.StepMember

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Generic.LocalOddCentral.conj (hΩ : ConjInvariant Ω)
    {x : G} (h : LocalOddCentral Ω {x}) (g : G) : LocalOddCentral Ω {g * x * g⁻¹} := by
  have hY : conjSub g (centLayer Ω x) = centLayer Ω (g * x * g⁻¹) := conjSub_centLayer hΩ g x
  let e0 : ↥(centLayer Ω x) ≃* ↥(conjSub g (centLayer Ω x)) :=
    (centLayer Ω x).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let e : ↥(centLayer Ω x) ≃* ↥(centLayer Ω (g * x * g⁻¹)) :=
    e0.trans (MulEquiv.subgroupCongr hY)
  have hO : (componentClassificationOddCore ↥(centLayer Ω x)).map e.toMonoidHom =
      componentClassificationOddCore ↥(centLayer Ω (g * x * g⁻¹)) :=
    OddCore.equiv_invariant e
  intro d' hd'
  have hd'' : d' ∈ (componentClassificationOddCore ↥(centLayer Ω x)).map e.toMonoidHom := by
    rw [hO]
    exact hd'
  obtain ⟨d, hd, rfl⟩ := hd''
  have hmem : e.toMonoidHom d ∈ Subgroup.center ↥(centLayer Ω (g * x * g⁻¹)) := by
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have hc := Subgroup.mem_center_iff.mp (h hd) y
    change e y * e d = e d * e y
    rw [← map_mul, ← map_mul]
    exact congrArg e hc
  exact hmem

end Conj

section Unique

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem _root_.CFSG.ClassicalInvolution.Generic.IsClassicalMember.isCentralInvolution
    {K : Subgroup G} {z : G} (h : IsClassicalMember p f K z) : IsCentralInvolution K z :=
  (⟨h.orderOf_eq_two, h.mem, h.perfect, h.subnormal, h.nonempty_equiv⟩ :
    WeakMember (GaloisField p f) K z).isCentralInvolution

theorem _root_.CFSG.ClassicalInvolution.Generic.IsClassicalMember.eq_of_isCentralInvolution
    (hp2 : p ≠ 2) (hf : 0 < f) {K : Subgroup G} {z z' : G} (h : IsClassicalMember p f K z)
    (hz' : IsCentralInvolution K z') : z' = z := by
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨e⟩ := h.nonempty_equiv
  let φ : ↥K →* SL(2, GaloisField p f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
  have hker : φ.ker = componentClassificationOddCore ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (classicalInvolutionOddCore ↥K) x) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hφ : IsChart (GaloisField p f) K φ :=
    ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), hker⟩
  exact hφ.eq_of_central hodd hz' h.isCentralInvolution

theorem localOddCentral_of_classicalMember (hp2 : p ≠ 2) (hf : 0 < f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω) {z₀ : G} (hz₀ : IsClassicalMember p f K₀ z₀)
    (h : LocalOddCentral Ω {z₀}) :
    ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  intro L hL z hz
  obtain ⟨K, -, hall⟩ := hsingle
  obtain ⟨g₀, hg₀⟩ := hall K₀ hK₀
  obtain ⟨g, hg⟩ := hall L hL
  have hK : K = conjSub g₀⁻¹ K₀ := by rw [hg₀, conjSub_inv_conjSub]
  have hLeq : L = conjSub (g * g₀⁻¹) K₀ := by rw [conjSub_mul, ← hK, hg]
  have hconj := hz₀.conj (g * g₀⁻¹)
  rw [← hLeq] at hconj
  have hzeq : g * g₀⁻¹ * z₀ * (g * g₀⁻¹)⁻¹ = z :=
    hz.eq_of_isCentralInvolution hp2 hf hconj.isCentralInvolution
  rw [← hzeq]
  exact h.conj hΩ.conjInvariant _

end Unique

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem localOddCentral_of_classicalInvolution [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    {F : Type*} [Field F] {S : Set (Subgroup G)} (Fr : WeakToralFrame F Ω E S)
    (h16 : 16 ≤ Nat.card E) (hGen : FusionGenerated E)
    (hlay : ∀ a ∈ E, a ≠ 1 → LayerGenerationAt E a) {K₀ : Subgroup G} (hK₀ : K₀ ∈ S) {z₀ : G}
    (hz₀ : IsCentralInvolution K₀ z₀) (hmeet : FrameMeetsAt Ω E S z₀) :
    ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  obtain ⟨z', hz'⟩ := hΩ.classical K₀ (Fr.subset hK₀)
  have hzz : z₀ = z' := hz'.eq_of_isCentralInvolution hp2 hf hz₀
  subst hzz
  exact localOddCentral_of_classicalMember hp2 hf hΩ hsingle (Fr.subset hK₀) hz'
    (localOddCentral_of_central_involution hnab hp2 h0 hA1 hΩ hIH Fr h16 hGen hlay hK₀ hz₀ hmeet)

end Frame

end CFSG.ClassicalInvolution.Balance

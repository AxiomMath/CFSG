module

public import CFSG.ClassicalInvolution.Q3.TL4VtxDich

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Simple

variable {X : Type} [Group X] [Finite X]

theorem not_tightInO2_of_fstar_simple (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) {z : X} (hz : z ≠ 1) :
    ¬ TightInO2 z := by
  rintro ⟨P, hPn, hP2, hzP⟩
  have hFn := genFittingFStar_normal X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf (genFittingFStar X)) with h | h
  · have hdis : Disjoint P (genFittingFStar X) := Subgroup.subgroupOf_eq_bot.mp h
    have hzc : z ∈ Subgroup.centralizer (genFittingFStar X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : z * y * z⁻¹ * y⁻¹ ∈ P := by
        have := hPn.conj_mem z⁻¹ (P.inv_mem hzP) y
        simpa [mul_assoc] using P.mul_mem hzP this
      have h2 : z * y * z⁻¹ * y⁻¹ ∈ genFittingFStar X :=
        (genFittingFStar X).mul_mem (hFn.conj_mem y hy z) ((genFittingFStar X).inv_mem hy)
      have hc : z * y * z⁻¹ = y := mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdis h1 h2)
      calc y * z = z * y * z⁻¹ * z := by rw [hc]
        _ = z * y := by group
    rw [centralizer_genFittingFStar_eq_bot hnab, Subgroup.mem_bot] at hzc
    exact hz hzc
  · have h2F : IsPGroup 2 ↥(genFittingFStar X) := hP2.to_le (Subgroup.subgroupOf_eq_top.mp h)
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial ↥(genFittingFStar X) :=
      nontrivial_of_ne a 1 fun ha => hab (by rw [ha, one_mul, mul_one])
    have hZ := h2F.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar X)) with
      hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ hc
    · exact hab ((Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b)) a)

theorem center_eq_bot_of_fstar_simple (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) : Subgroup.center X = ⊥ :=
  le_bot_iff.mp ((centralizer_genFittingFStar_eq_bot hnab) ▸
    Subgroup.center_le_centralizer (genFittingFStar X : Set X))

end Simple

section Cit3


variable {n : ℕ} {X : Type} [Group X] [Finite X]

theorem tightLargeHypR_of_class (hA : CIT3Below n) (hb : TightBelowR 3 n) (hX : Nat.card X = n)
    (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hlarge : ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar X)) {K : Subgroup X}
    (hΦ : TypeRFam 3 (CoreAssembly.conjClass K)) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : (⨆ g : X, conjSub g K) = ⊤)
    (hedge : ¬ Disconnected.DEdgeless (CoreAssembly.conjClass K)) {z : X}
    (hz : IsUniqueInvolution K z) (S : Sylow 2 ↥K) :
    TightLargeHypR 3 n X K S z ∧ tightCore K = K := by
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hcore : tightCore K = K := hΦ.closure_twoElts hK
  refine ⟨⟨hA, hb, hX, Vtx.tightDatum_of_mem hΦ hK hz S,
    ⟨Vtx.nonempty_sylow_equiv hΦ hK S, ?_, hO⟩, not_tightInO2_of_fstar_simple hs hnab hz.ne_one,
    isQuasisimple_of_simple_nonabelian' hnab, hlarge, ?_, center_eq_bot_of_fstar_simple hs hnab⟩,
    hcore⟩
  · show (⨆ g : X, conjSub g (tightCore K)) = ⊤
    rw [hcore]
    exact hgen
  · show ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore K))
    rw [hcore]
    exact hedge

theorem tightLargeHypR_of_transitive (hA : CIT3Below n) (hb : TightBelowR 3 n)
    (hX : Nat.card X = n) (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a)
    (hlarge : ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar X)) {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (htr : ∀ L ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g L = M)
    (hedge : ¬ Disconnected.DEdgeless Φ) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (S : Sylow 2 ↥K) :
    TightLargeHypR 3 n X K S z ∧ tightCore K = K ∧ CoreAssembly.conjClass K = Φ := by
  have hcl : CoreAssembly.conjClass K = Φ := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact hΦ.hyp.conjInvariant g K hK
    · intro hM
      exact htr K hK M hM
  subst hcl
  have hgen' : (⨆ g : X, conjSub g K) = ⊤ := by
    rw [← iSup_conjClass_eq]
    exact hgen
  obtain ⟨h1, h2⟩ := tightLargeHypR_of_class hA hb hX hs hnab hlarge hΦ hO hgen' hedge hz S
  exact ⟨h1, h2, rfl⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

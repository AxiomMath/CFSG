module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MExt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open QuadraticMap Module TauCeti.QuadraticMap CFSG.Open
open scoped commutatorElement

noncomputable section

section Quasi

theorem isQuasisimple_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) : CFSG.Open.IsQuasisimple G ∧ Subgroup.center G = ⊥ := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact (hna fun x y => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)).elim
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · refine (hna fun x y => ?_).elim
      have h1 : ⁅x, y⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rwa [commutatorElement_eq_one_iff_mul_comm] at h1
    · exact h
  have e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨⟨hperf, e.isSimpleGroup⟩, hZ⟩

theorem card_quotient_center_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) : Nat.card (G ⧸ Subgroup.center G) = Nat.card G := by
  have hZ := (isQuasisimple_of_simple_nonabelian hna).2
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv

end Quasi

section Comp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {U : Submodule K V}

theorem exists_component (hU : IsCompl U (perpOf Q U)) (hperp : ∃ w ∈ perpOf Q U, w ≠ 0)
    {N : Subgroup (U ≃ₗ[K] U)} (hNO : N ≤ orthogonalGroup (Q.restrict U))
    (hnorm : ∀ g ∈ orthogonalGroup (Q.restrict U), ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hs : IsSimpleGroup N) (hp : Group.IsPerfect N) (hna : ¬ ∀ x y : N, x * y = y * x)
    (h3N : 3 ∣ Nat.card N) :
    ∃ Hv : Subgroup (V ≃ₗ[K] V),
      Hv ≤ ⁅orthogonalGroup Q, orthogonalGroup Q⁆ ∧
      (∀ h ∈ Hv, ∀ f : V ≃ₗ[K] V, f ∈ orthogonalGroup Q → (∀ u ∈ U, f u = u) →
        h * f = f * h) ∧
      (∀ g ∈ orthogonalGroup Q, (∀ u ∈ U, g u ∈ U) → (∀ u ∈ U, g⁻¹ u ∈ U) →
        ∀ h ∈ Hv, g * h * g⁻¹ ∈ Hv) ∧
      CFSG.Open.IsQuasisimple Hv ∧ 3 ∣ Nat.card (Hv ⧸ Subgroup.center Hv) ∧
      (∃ w : V, w ≠ 0 ∧ ∀ h ∈ Hv, h w = w) := by
  let hom : ↥N →* (V ≃ₗ[K] V) :=
    (orthogonalGroup Q).subtype.comp ((extU hU).comp (Subgroup.inclusion hNO))
  have hinj : Function.Injective hom :=
    Subtype.val_injective.comp ((extU_injective hU).comp (Subgroup.inclusion_injective hNO))
  set Hv : Subgroup (V ≃ₗ[K] V) := hom.range with hHv
  let e : ↥N ≃* Hv := MonoidHom.ofInjective hinj
  have hHvO : Hv ≤ orthogonalGroup Q := by
    rintro _ ⟨n, rfl⟩
    exact (extU hU (Subgroup.inclusion hNO n)).2
  haveI : IsSimpleGroup N := hs
  obtain ⟨hq, hZ⟩ := isQuasisimple_of_simple_nonabelian hna
  have hperfHv : Group.IsPerfect Hv := by
    rw [Group.isPerfect_def]
    have := hp.commutator_eq_top
    have hmt : (⊤ : Subgroup ↥N).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
    have h2 : commutator Hv = (commutator ↥N).map e.toMonoidHom := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, hmt]
    rw [h2, this, hmt]
  refine ⟨Hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc Hv = ⁅Hv, Hv⁆ := (Subgroup.isPerfect_iff.1 hperfHv).symm
      _ ≤ ⁅orthogonalGroup Q, orthogonalGroup Q⁆ := Subgroup.commutator_mono hHvO hHvO
  · rintro _ ⟨n, rfl⟩ f hf hfix
    exact extU_commute hU hf hfix (Subgroup.inclusion hNO n)
  · rintro g hg hgU hgU' _ ⟨n, rfl⟩
    have hconj := conj_extU hU hg hgU hgU' (Subgroup.inclusion hNO n)
    set r := resU hg hgU hgU' with hr
    have hmem : ((r * Subgroup.inclusion hNO n * r⁻¹ : orthogonalGroup (Q.restrict U)) :
        U ≃ₗ[K] U) ∈ N := hnorm r.1 r.2 n.1 n.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    show (extU hU (Subgroup.inclusion hNO ⟨_, hmem⟩)).1 =
      g * (extU hU (Subgroup.inclusion hNO n)).1 * g⁻¹
    rw [hconj]
    rfl
  · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv e hq
  · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv e,
      card_quotient_center_of_simple hna]
    exact h3N
  · obtain ⟨w, hw, hw0⟩ := hperp
    refine ⟨w, hw0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact extU_apply_of_mem_perp hU (Subgroup.inclusion hNO n) hw

end Comp

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end

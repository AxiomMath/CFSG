module

public import CFSG.ClassicalInvolution.Asc77.AscC22P12
public import CFSG.ClassicalInvolution.Asc77.AscC22P5

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace C22P

set_option linter.unusedSectionVars false

section Conj

variable {G : Type} [Group G] [Finite G]

theorem FrameData.conj {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G} {R R' : Subgroup G}
    {b b' y : G} (hΩ : ConjInvariant Ω) (hF : FrameData Ω K₃ K₄ z c R R' b b' y) {n : G}
    (hn₃ : conjSub n K₃ = K₃) (hn₄ : conjSub n K₄ = K₄) (hnz : n * z * n⁻¹ = z) :
    FrameData Ω K₃ K₄ z (n * c * n⁻¹) (conjSub n R) (conjSub n R') (n * b * n⁻¹) (n * b' * n⁻¹)
      (n * y * n⁻¹) := by
  have hnz' : n⁻¹ * z * n = z := by
    have := congrArg (fun x => n⁻¹ * x * n) hnz
    simpa [mul_assoc] using this.symm
  have ho : ∀ x : G, orderOf (n * x * n⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  refine ⟨?_, ?_, hF.hRR'.conjSub n, conjSub_le_centralizer_conj n hF.hRc,
    conjSub_le_centralizer_conj n hF.hR'c, conj_mem_conjSub hF.hbR, conj_mem_conjSub hF.hb'R',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn₃]; exact hF.hR.conj n
  · rw [← hn₄]; exact hF.hR'.conj n
  · rw [ho, hF.hb4]
  · rw [ho, hF.hb'4]
  · calc n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ := by group
      _ = z := by rw [hF.hbz, hnz]
  · calc n * b' * n⁻¹ * (n * b' * n⁻¹) = n * (b' * b') * n⁻¹ := by group
      _ = z := by rw [hF.hb'z, hnz]
  · rw [exactLayer_conj hΩ n c]
    exact conj_mem_conjSub hF.hy
  · calc n * y * n⁻¹ * z * (n * y * n⁻¹)⁻¹ = n * y * (n⁻¹ * z * n) * y⁻¹ * n⁻¹ := by group
      _ = n * (y * z * y⁻¹) * n⁻¹ := by rw [hnz']; group
      _ = n * (b * b' * c) * n⁻¹ := by rw [hF.hyz]
      _ = n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹) := by group
  · intro h
    apply hF.htz
    have h2 : b * b' * c = n⁻¹ * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * n := by group
    rw [h2, h, hnz']
  · calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) =
        n * (z * (b * b' * c)) * n⁻¹ := by
          calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹))
              = (n * z * n⁻¹) * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) := by rw [hnz]
            _ = n * (z * (b * b' * c)) * n⁻¹ := by group
      _ = n * ((b * b' * c) * z) * n⁻¹ := by rw [hF.hzt]
      _ = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * z := by
          calc n * ((b * b' * c) * z) * n⁻¹
              = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * (n * z * n⁻¹) := by group
            _ = _ := by rw [hnz]

end Conj

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem frame_at_alpha (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ (R R' : Subgroup G) (b b' y : G), FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y ∧
      y ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨a, a', ha, ha', ha4, ha'4, haa', R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R',
    hb4, hb'4, hbz, hb'z, hy, hyz, htz, hzt, hyα⟩ := fuseFrame_alpha hs hK₄ h41 h42 h43 hμ
  have haz : a * a = z := sq_eq_involution_of_orderOf_four hz ha ha4
  have ha'z : a' * a' = z := sq_eq_involution_of_orderOf_four hz' ha' ha'4
  have haa2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a' a a', ← haa']; group
      _ = 1 := by rw [haz, ha'z]; exact hz.sq
  have hy' : y ∈ exactLayer Ω (a * a') := by
    rw [← rLayer_eq_exactLayer hp hq hΩ haa2]
    exact hy
  have hF : FrameData Ω K₃ K₄ z (a * a') R R' b b' y :=
    ⟨hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy', hyz, htz, hzt⟩
  have hKK' : K ≤ trivialOnQuot K' := T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz hz'
  have hK'K : K' ≤ trivialOnQuot K := T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c, hc, hconj⟩ := T7V.exists_conj_pair hp hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K ha ha'
    hs.hu₁.1 hs.hu₂.1 ha4 ha'4 hs.hu₁.2 hs.hu₂.2 haa' hs.comm₁₂
  have nK₃ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hs.hK₃K.symm hz hz₃
  have nK₃' : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hs.hK₃K'.symm hz' hz₃
  have nK₄ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK₄' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have hc₃ : conjSub c K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₃ nK₃' hc)
  have hc₄ : conjSub c K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₄ nK₄' hc)
  have hcz : c * z * c⁻¹ = z := by
    have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz'.commute_of_mem hx).symm
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    rw [h1]
    group
  have hF' := hF.conj hΩ.conjInvariant hc₃ hc₄ hcz
  rw [hconj] at hF'
  refine ⟨conjSub c R, conjSub c R', c * b * c⁻¹, c * b' * c⁻¹, c * y * c⁻¹, hF', ?_⟩
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))) := by
    have e := T7A.conjSub_closure_pair c (a * a') z
    rw [hcz, hconj] at e
    rw [← e, alphaOf_conjSub]
  rw [hα, mem_normalizer_iff_conjSub_eq]
  have h1 := mem_normalizer_iff_conjSub_eq.mp hyα
  calc conjSub (c * y * c⁻¹) (conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))))
      = conjSub c (conjSub y (conjSub c⁻¹ (conjSub c
          (alphaOf (Subgroup.closure ({a * a', z} : Set G)))))) := by
        rw [conjSub_mul, conjSub_mul]
    _ = conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))) := by
        rw [conjSub_inv_conjSub, h1]

end Frame

end C22P

end CFSG.ClassicalInvolution.Asc77

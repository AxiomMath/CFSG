module

public import CFSG.ClassicalInvolution.Asc77.AscC22P1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace C22P

set_option linter.unusedSectionVars false

section Frame

variable {G : Type} [Group G] [Finite G]

@[expose] def FrameS (Ω : Set (Subgroup G)) (K₃ K₄ : Subgroup G) (z c : G) : Prop :=
  ∃ (R R' : Subgroup G) (b b' y : G), IsSylow2In R K₃ ∧ IsSylow2In R' K₄ ∧ Commutes R R' ∧
    R ≤ Subgroup.centralizer ({c} : Set G) ∧ R' ≤ Subgroup.centralizer ({c} : Set G) ∧
    b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧ orderOf b' = 4 ∧ b * b = z ∧ b' * b' = z ∧
    y ∈ exactLayer Ω c ∧ y * z * y⁻¹ = b * b' * c ∧ b * b' * c ≠ z ∧
    z * (b * b' * c) = (b * b' * c) * z

omit [Finite G] in
theorem conjSub_le_centralizer_conj {R : Subgroup G} {c : G} (n : G)
    (hR : R ≤ Subgroup.centralizer ({c} : Set G)) :
    conjSub n R ≤ Subgroup.centralizer ({n * c * n⁻¹} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hR hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * x := by group

theorem FrameS.conj {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G}
    (hΩ : ConjInvariant Ω) (hF : FrameS Ω K₃ K₄ z c) {n : G} (hn₃ : conjSub n K₃ = K₃)
    (hn₄ : conjSub n K₄ = K₄) (hnz : n * z * n⁻¹ = z) : FrameS Ω K₃ K₄ z (n * c * n⁻¹) := by
  obtain ⟨R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy, hyz,
    hne, hcomm⟩ := hF
  have hnz' : n⁻¹ * z * n = z := by
    have := congrArg (fun x => n⁻¹ * x * n) hnz
    simpa [mul_assoc] using this.symm
  have ho : ∀ x : G, orderOf (n * x * n⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  refine ⟨conjSub n R, conjSub n R', n * b * n⁻¹, n * b' * n⁻¹, n * y * n⁻¹, ?_, ?_,
    hRR'.conjSub n, conjSub_le_centralizer_conj n hRc, conjSub_le_centralizer_conj n hR'c,
    conj_mem_conjSub hbR, conj_mem_conjSub hb'R', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn₃]; exact hR.conj n
  · rw [← hn₄]; exact hR'.conj n
  · rw [ho, hb4]
  · rw [ho, hb'4]
  · calc n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ := by group
      _ = z := by rw [hbz, hnz]
  · calc n * b' * n⁻¹ * (n * b' * n⁻¹) = n * (b' * b') * n⁻¹ := by group
      _ = z := by rw [hb'z, hnz]
  · rw [exactLayer_conj hΩ n c]
    exact conj_mem_conjSub hy
  · calc n * y * n⁻¹ * z * (n * y * n⁻¹)⁻¹ = n * y * (n⁻¹ * z * n) * y⁻¹ * n⁻¹ := by group
      _ = n * (y * z * y⁻¹) * n⁻¹ := by rw [hnz']; group
      _ = n * (b * b' * c) * n⁻¹ := by rw [hyz]
      _ = n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹) := by group
  · intro h
    apply hne
    have h2 : b * b' * c = n⁻¹ * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * n := by group
    rw [h2, h, hnz']
  · calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) =
        n * (z * (b * b' * c)) * n⁻¹ := by
          calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹))
              = (n * z * n⁻¹) * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) := by rw [hnz]
            _ = n * (z * (b * b' * c)) * n⁻¹ := by group
      _ = n * ((b * b' * c) * z) * n⁻¹ := by rw [hcomm]
      _ = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * z := by
          calc n * ((b * b' * c) * z) * n⁻¹
              = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * (n * z * n⁻¹) := by group
            _ = _ := by rw [hnz]

end Frame

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem frame_at (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    FrameS Ω K₃ K₄ z (u₁ * u₂) := by
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
    hb4, hb'4, hbz, hb'z, hy, hyz, htz, hzt⟩ := fuseFrame_S hs hK₄ h41 h42 h43 hμ
  have haz : a * a = z := sq_eq_involution_of_orderOf_four hz ha ha4
  have ha'z : a' * a' = z := sq_eq_involution_of_orderOf_four hz' ha' ha'4
  have haa2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a' a a', ← haa']; group
      _ = 1 := by rw [haz, ha'z]; exact hz.sq
  have hy' : y ∈ exactLayer Ω (a * a') := by
    rw [← rLayer_eq_exactLayer hp hq hΩ haa2]
    exact hy
  have hF : FrameS Ω K₃ K₄ z (a * a') :=
    ⟨R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy', hyz, htz,
      hzt⟩
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
  have := hF.conj hΩ.conjInvariant hc₃ hc₄ hcz
  rw [hconj] at this
  exact this

end Setting

end C22P

end CFSG.ClassicalInvolution.Asc77

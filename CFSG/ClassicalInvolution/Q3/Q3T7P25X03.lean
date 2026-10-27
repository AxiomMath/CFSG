module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25X02
public import CFSG.ClassicalInvolution.Asc77.AscC25Y6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Basic
variable {G : Type} [Group G]
end Basic
section Fusion
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem conjSub_pair_of_central (hs : Hyp23Setting Ω K K' z) {c : G}
    (hc : c * z * c⁻¹ = z) :
    (conjSub c K = K ∧ conjSub c K' = K') ∨ (conjSub c K = K' ∧ conjSub c K' = K) := by
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hKc : conjSub c K = K ∨ conjSub c K = K' := by
    have hmem : conjSub c K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K hs.stand.mem, z, hz, by simpa [hc] using hz.conj c⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hK'c : conjSub c K' = K ∨ conjSub c K' = K' := by
    have hmem : conjSub c K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant c K' hs.hK'.1, z, hz, by simpa [hc] using hz'.conj c⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hne : conjSub c K ≠ conjSub c K' := fun h => hs.hne (conjSub_injective c h).symm
  rcases hKc with h1 | h1 <;> rcases hK'c with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem trivialOnQuot_pair_conj (hs : Hyp23Setting Ω K K' z) {a c : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K') (hc : c * z * c⁻¹ = z) :
    c * a * c⁻¹ ∈ trivialOnQuot K ∧ c * a * c⁻¹ ∈ trivialOnQuot K' := by
  have h1 := trivialOnQuot_conjSub haK c
  have h2 := trivialOnQuot_conjSub haK' c
  rcases conjSub_pair_of_central hs hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h1, h2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h2, h1⟩
variable {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}

theorem conjSub_R_eq_of_mem_normalizer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : s ∈ Subgroup.normalizer (K : Set G)) :
    conjSub s R = R := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  rcases T7T.perm_R_of_hyp hyp hsS (Or.inl rfl : R = R ∨ R = R') with h | h
  · exact h
  · exfalso
    have hsK' : conjSub s K = K := mem_normalizer_iff_conjSub_eq.mp hsK
    have hR'K : R' ≤ K := by
      rw [← h, ← hsK']
      exact conjSub_mono hyp.hR.2.1
    have hR'2 : IsPGroup 2 R' := S.isPGroup'.to_le hyp.hR'.2.2
    have h1 := hΩ.card_le_two_of_le_inf hs.stand.mem hs.hK'.1 hs.hne.symm hR'2 hR'K hyp.hR'.2.1
    have h2 := (hΩ.isQuatSub_of_mem_RSet hyp.hR'.1).eight_le
    omega

theorem conjSub_R'_eq_of_mem_normalizer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : s ∈ Subgroup.normalizer (K' : Set G)) :
    conjSub s R' = R' := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  rcases T7T.perm_R_of_hyp hyp hsS (Or.inr rfl : R' = R ∨ R' = R') with h | h
  · exfalso
    have hsK' : conjSub s K' = K' := mem_normalizer_iff_conjSub_eq.mp hsK
    have hRK' : R ≤ K' := by
      rw [← h, ← hsK']
      exact conjSub_mono hyp.hR'.2.1
    have hR2 : IsPGroup 2 R := S.isPGroup'.to_le hyp.hR.2.2
    have h1 := hΩ.card_le_two_of_le_inf hs.stand.mem hs.hK'.1 hs.hne.symm hR2 hyp.hR.2.1 hRK'
    have h2 := (hΩ.isQuatSub_of_mem_RSet hyp.hR.1).eight_le
    omega
  · exact h

theorem conj_mem_Csub (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a c : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K') (hc : c * z * c⁻¹ = z)
    (hcaS : c * a * c⁻¹ ∈ (S : Subgroup G)) :
    c * a * c⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  obtain ⟨h1, h2⟩ := trivialOnQuot_pair_conj hs haK haK' hc
  refine ⟨hcaS, ?_⟩
  have hR : R ≤ Subgroup.centralizer ({c * a * c⁻¹} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_normalizes_of_trivialOnQuot (S.isPGroup'.to_le hyp.hR.2.2) hyp.hR.2.1 h1
        (conjSub_R_eq_of_mem_normalizer hyp hcaS h1.1) hr).symm
  have hR' : R' ≤ Subgroup.centralizer ({c * a * c⁻¹} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_normalizes_of_trivialOnQuot (S.isPGroup'.to_le hyp.hR'.2.2) hyp.hR'.2.1 h2
        (conjSub_R'_eq_of_mem_normalizer hyp hcaS h2.1) hr).symm
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (sup_le hR hR' hx)
end Fusion
end C25Y
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Swap
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem eq_conj_twin_of_unique (hs : Hyp23Setting Ω K K' z) {h : G} {M : Subgroup G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M (h * z * h⁻¹)) :
    M = conjSub h K ∨ M = conjSub h K' := by
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hM₀ : conjSub h⁻¹ M ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant h⁻¹ M hM, z, hz, ?_⟩
    have := hMt.conj h⁻¹
    simpa [mul_assoc] using this
  rw [hs.twinSet_eq] at hM₀
  have hMeq : M = conjSub h (conjSub h⁻¹ M) := by
    rw [← conjSub_mul]
    simp
  rcases hM₀ with h0 | h0
  · left
    rw [hMeq, h0]
  · right
    rw [hMeq, h0]

theorem not_swap_in_both (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a t' h m : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K')
    (hzt : z ≠ t') (hzc : z * t' * z⁻¹ = t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z)
    (hh : h * z * h⁻¹ = t') (hha : h * a = a * h)
    (hm : m * z * m⁻¹ = t') (hma : m * (a * z) = (a * z) * m) : False := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hJΩ : conjSub h K ∈ Ω := hΩ.conjInvariant h K hs.stand.mem
  have hJt : IsUniqueInvolution (conjSub h K) (h * z * h⁻¹) := hz.conj h
  have hswap : conjSub z (conjSub h K) ≠ conjSub h K :=
    T7G2.not_normalizes_of_nonfused hyp hh hzt hnf
  have hJne : conjSub h K ≠ conjSub h K' := fun e => hs.hne (conjSub_injective h e).symm
  have hzJ : conjSub z (conjSub h K) = conjSub h K' := by
    have hmem : IsUniqueInvolution (conjSub z (conjSub h K)) (h * z * h⁻¹) := by
      have := hJt.conj z
      rw [hh, hzc] at this
      rwa [hh]
    rcases eq_conj_twin_of_unique hs (hΩ.conjInvariant z _ hJΩ) hmem with e | e
    · exact absurd e hswap
    · exact e
  have hJ₂Ω : conjSub m K ∈ Ω := hΩ.conjInvariant m K hs.stand.mem
  have hJ₂t : IsUniqueInvolution (conjSub m K) (h * z * h⁻¹) := by
    have := hz.conj m
    rwa [hm, ← hh] at this
  have hJ₂ : conjSub m K = conjSub h K ∨ conjSub m K = conjSub h K' :=
    eq_conj_twin_of_unique hs hJ₂Ω hJ₂t
  have haKn : conjSub a K = K := mem_normalizer_iff_conjSub_eq.mp haK.1
  have haK'n : conjSub a K' = K' := mem_normalizer_iff_conjSub_eq.mp haK'.1
  have hzKn : conjSub z K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hz.mem)
  have hazKn : conjSub (a * z) K = K := by rw [conjSub_mul, hzKn, haKn]
  have haJ : conjSub a (conjSub h K) = conjSub h K := by
    rw [← conjSub_mul, ← hha, conjSub_mul, haKn]
  have haJ' : conjSub a (conjSub h K') = conjSub h K' := by
    rw [← conjSub_mul, ← hha, conjSub_mul, haK'n]
  have hazJ₂ : conjSub (a * z) (conjSub m K) = conjSub m K := by
    rw [← conjSub_mul, ← hma, conjSub_mul, hazKn]
  have haJ₂ : conjSub a (conjSub m K) = conjSub m K := by
    rcases hJ₂ with e | e <;> rw [e]
    · exact haJ
    · exact haJ'
  have hzJ₂ : conjSub z (conjSub m K) = conjSub m K := by
    have h1 : conjSub a⁻¹ (conjSub m K) = conjSub m K := by
      apply conjSub_injective a
      rw [← conjSub_mul]
      simpa using haJ₂.symm
    calc conjSub z (conjSub m K) = conjSub (a⁻¹ * (a * z)) (conjSub m K) := by
          congr 2; group
      _ = conjSub a⁻¹ (conjSub (a * z) (conjSub m K)) := conjSub_mul _ _ _
      _ = conjSub m K := by rw [hazJ₂, h1]
  rcases hJ₂ with e | e
  · rw [e] at hzJ₂
    exact hswap hzJ₂
  · rw [e] at hzJ₂
    have : conjSub z (conjSub h K) = conjSub z (conjSub h K') := by rw [hzJ, hzJ₂]
    exact hJne (conjSub_injective z this)
end Swap
section Fusion
variable {G : Type} [Group G]
end Fusion
section NotGood
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem not_goodFusion (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z) :
    ¬ GoodFusion z a := by
  intro hGF
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hz : IsUniqueInvolution K z := hs.hz
  have haS : a ∈ (S : Subgroup G) := haA.1
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have haK : a ∈ trivialOnQuot K := hK₂.2
  have haK' : a ∈ trivialOnQuot K' := hK₂'.2
  have hzS := hyp.hzS
  have haz' : a * z = z * a := hzS a haS
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have hRne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  have hzt : z ≠ t' := by
    intro h
    apply hRne
    have h1 : conjSub t' R = R := by
      rw [← h]
      exact T7F2.conjSub_eq_of_centralizes fun r hr => hyp.hzS r (hyp.hR.2.2 hr)
    rw [← ht'R, h1]
  have ht'z : t' * z = z * t' := hzS t' ht'S
  have hzc : z * t' * z⁻¹ = t' := by
    calc z * t' * z⁻¹ = (t' * z) * z⁻¹ := by rw [ht'z]
      _ = t' := by group
  have hat : t' * a = a * t' :=
    T7U.comm_swap_of_normal_four hyp ht'S ht'2 hg hnf haS hconj
  have ht'C : g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [hg]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hat
  obtain ⟨h, hhC, hh⟩ := hGF g ht'C
  rw [hg] at hh
  have hha : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.mp hhC
  by_cases hfused : ∃ g₀ : G, g₀ * a * g₀⁻¹ = a * z
  · obtain ⟨g₀, hg₀⟩ := hfused
    have h1 : z * (a * z) = (a * z) * z := by
      calc z * (a * z) = (z * a) * z := by group
        _ = (a * z) * z := by rw [haz']
    have hcomm₀ : g₀⁻¹ * z * g₀⁻¹⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (g₀⁻¹ * z * g₀⁻¹⁻¹) * a = g₀⁻¹ * (z * (g₀ * a * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * (z * (a * z)) * g₀ := by rw [hg₀]
        _ = g₀⁻¹ * ((a * z) * z) * g₀ := by rw [h1]
        _ = g₀⁻¹ * (g₀ * a * g₀⁻¹) * z * g₀ := by rw [hg₀]; group
        _ = a * (g₀⁻¹ * z * g₀⁻¹⁻¹) := by group
    obtain ⟨h₀, hh₀C, hh₀⟩ := hGF g₀⁻¹ hcomm₀
    have hh₀a : h₀ * a = a * h₀ := Subgroup.mem_centralizer_singleton_iff.mp hh₀C
    have hcz : (g₀ * h₀) * z * (g₀ * h₀)⁻¹ = z := by
      calc (g₀ * h₀) * z * (g₀ * h₀)⁻¹ = g₀ * (h₀ * z * h₀⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [hh₀]
        _ = z := by group
    have hca : (g₀ * h₀) * a * (g₀ * h₀)⁻¹ = a * z := by
      calc (g₀ * h₀) * a * (g₀ * h₀)⁻¹ = g₀ * (h₀ * a) * h₀⁻¹ * g₀⁻¹ := by group
        _ = g₀ * (a * h₀) * h₀⁻¹ * g₀⁻¹ := by rw [hh₀a]
        _ = g₀ * a * g₀⁻¹ := by group
        _ = a * z := hg₀
    set c := g₀ * h₀ with hc
    have hcomm₁ : (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h2 : t' * (a * z) = (a * z) * t' := by
        calc t' * (a * z) = (t' * a) * z := by group
          _ = (a * t') * z := by rw [hat]
          _ = a * (t' * z) := by group
          _ = a * (z * t') := by rw [ht'z]
          _ = (a * z) * t' := by group
      calc (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ * a = c⁻¹ * (g * z * g⁻¹) * c * a := by group
        _ = c⁻¹ * t' * c * a := by rw [hg]
        _ = c⁻¹ * (t' * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * (t' * (a * z)) * c := by rw [hca]
        _ = c⁻¹ * ((a * z) * t') * c := by rw [h2]
        _ = c⁻¹ * ((c * a * c⁻¹) * t') * c := by rw [hca]
        _ = a * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) := by
          calc c⁻¹ * ((c * a * c⁻¹) * t') * c = a * (c⁻¹ * t' * c) := by group
            _ = a * (c⁻¹ * (g * z * g⁻¹) * c) := by rw [hg]
            _ = a * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) := by group
    obtain ⟨h₁, hh₁C, hh₁⟩ := hGF (c⁻¹ * g) hcomm₁
    have hh₁a : h₁ * a = a * h₁ := Subgroup.mem_centralizer_singleton_iff.mp hh₁C
    have hczi : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
        _ = z := by group
    have hm : (c * h₁ * c⁻¹) * z * (c * h₁ * c⁻¹)⁻¹ = t' := by
      calc (c * h₁ * c⁻¹) * z * (c * h₁ * c⁻¹)⁻¹ = c * h₁ * (c⁻¹ * z * c) * h₁⁻¹ * c⁻¹ := by group
        _ = c * (h₁ * z * h₁⁻¹) * c⁻¹ := by rw [hczi]; group
        _ = c * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹) * c⁻¹ := by rw [hh₁]
        _ = g * z * g⁻¹ := by group
        _ = t' := hg
    have hma : (c * h₁ * c⁻¹) * (a * z) = (a * z) * (c * h₁ * c⁻¹) := by
      calc (c * h₁ * c⁻¹) * (a * z) = c * h₁ * (c⁻¹ * (a * z) * c) * c⁻¹ := by group
        _ = c * h₁ * a * c⁻¹ := by
          have : c⁻¹ * (a * z) * c = a := by
            calc c⁻¹ * (a * z) * c = c⁻¹ * (c * a * c⁻¹) * c := by rw [hca]
              _ = a := by group
          rw [this]
        _ = c * (a * h₁) * c⁻¹ := by rw [mul_assoc c h₁ a, hh₁a, ← mul_assoc]
        _ = (c * a * c⁻¹) * (c * h₁ * c⁻¹) := by group
        _ = (a * z) * (c * h₁ * c⁻¹) := by rw [hca]
    exact not_swap_in_both hyp haK haK' hzt hzc hnf hh hha hm hma
  ·
    have hES : Subgroup.zpowers a ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr haS
    have hE1 : Subgroup.zpowers a ≠ ⊥ := by
      intro hbot
      apply ha1
      have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
      rw [hbot] at this
      simpa using this
    have hEab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self a k l).eq
    have hsc : ∀ e ∈ Subgroup.zpowers a, ∀ g' : G, g' * e * g'⁻¹ ∈ (S : Subgroup G) →
        g' * e * g'⁻¹ ∈ Subgroup.zpowers a := by
      intro e he g' hg'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      rcases zpow_eq_one_or_self ha2 k with hk | hk
      · rw [hk]
        simp only [mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [hk] at hg' ⊢
        have hz' : (g' * a * g'⁻¹) * z = z * (g' * a * g'⁻¹) := hzS _ hg'
        have hcomm₂ : g'⁻¹ * z * g'⁻¹⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          calc (g'⁻¹ * z * g'⁻¹⁻¹) * a = g'⁻¹ * (z * (g' * a * g'⁻¹)) * g' := by group
            _ = g'⁻¹ * ((g' * a * g'⁻¹) * z) * g' := by rw [hz']
            _ = a * (g'⁻¹ * z * g'⁻¹⁻¹) := by group
        obtain ⟨h₂, hh₂C, hh₂⟩ := hGF g'⁻¹ hcomm₂
        have hh₂a : h₂ * a = a * h₂ := Subgroup.mem_centralizer_singleton_iff.mp hh₂C
        have hcz : (g' * h₂) * z * (g' * h₂)⁻¹ = z := by
          calc (g' * h₂) * z * (g' * h₂)⁻¹ = g' * (h₂ * z * h₂⁻¹) * g'⁻¹ := by group
            _ = g' * (g'⁻¹ * z * g'⁻¹⁻¹) * g'⁻¹ := by rw [hh₂]
            _ = z := by group
        have hca : (g' * h₂) * a * (g' * h₂)⁻¹ = g' * a * g'⁻¹ := by
          calc (g' * h₂) * a * (g' * h₂)⁻¹ = g' * (h₂ * a) * h₂⁻¹ * g'⁻¹ := by group
            _ = g' * (a * h₂) * h₂⁻¹ * g'⁻¹ := by rw [hh₂a]
            _ = g' * a * g'⁻¹ := by group
        have hmem : g' * a * g'⁻¹ ∈
            (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
          rw [← hca]
          exact conj_mem_Csub hyp haK haK' hcz (by rw [hca]; exact hg')
        rcases hA0 _ hmem with h3 | h3 | h3 | h3
        · exfalso
          apply ha1
          calc a = g'⁻¹ * (g' * a * g'⁻¹) * g' := by group
            _ = g'⁻¹ * 1 * g' := by rw [h3]
            _ = 1 := by group
        · rw [h3]
          exact Subgroup.mem_zpowers a
        · exfalso
          have hconjz : g'⁻¹ * z * g'⁻¹⁻¹ = a := by
            calc g'⁻¹ * z * g'⁻¹⁻¹ = g'⁻¹ * (g' * a * g'⁻¹) * g' := by rw [← h3]; group
              _ = a := by group
          obtain ⟨hu₁R, hu₁4, -⟩ := hyp.hu₁
          have hu₁a : (g'⁻¹ * z * g'⁻¹⁻¹) * u₁ = u₁ * (g'⁻¹ * z * g'⁻¹⁻¹) := by
            rw [hconjz]
            exact haR u₁ hu₁R
          exact T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hs.stand.mem hz
            (by rw [hconjz]; exact haz) (hyp.hR.2.1 hu₁R) hu₁4 hu₁a
        · exfalso
          exact hfused ⟨g', h3⟩
    exact l17_8_of_hyp25 hyp hES hE1 hEab ⟨hES, hsc⟩
end NotGood
end C25Y
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Odd
variable {G : Type} [Group G]
end Odd
section LayerAut
variable {G : Type} [Group G]
end LayerAut
section NC4
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem nc4_lift (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G)) :
    ∀ {J : Subgroup (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))},
      J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) →
      ∀ {y : ↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
          a)},
        y ∈ J → y * y * y * y = 1 → y * y ≠ 1 →
        layerAut (ExactLayer.exactLayer Ω a)
          (ExactLayer.conjSub_exactLayer hyp.std.setting.stand.modU.conjInvariant hbC) y = y →
        ∃ M ∈ ExactLayer.tqMembers Ω a, IsUniqueInvolution M (c * z * c⁻¹) := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  set b := c * z * c⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    have hz2 : z * z = 1 := hzK.sq
    calc b * b = c * (z * z) * c⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [hz2]; group
  have hbY : conjSub b (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hbC
  set Y := ExactLayer.exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  intro J hJ y hyJ hy4 hy2 hfix
  obtain ⟨M₁, hM₁tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
  obtain ⟨g₁, hg₁⟩ := hst.trans M₁ hM₁tq.1
  have hzM₁ : IsUniqueInvolution M₁ (g₁ * z * g₁⁻¹) := by
    rw [← hg₁]
    exact hzK.conj g₁
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  
  obtain ⟨c0, hcmem, hcy⟩ := Subgroup.mem_map.mp hyJ
  have hcM : (c0 : G) ∈ ExactLayer.exactCore a M₁ := Subgroup.mem_subgroupOf.mp hcmem
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c0).ne'
  set c' : ↥Y := c0 ^ m with hc'
  have hc'k : c' ^ (2 ^ k) = 1 := by
    rw [hc', ← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c0
  have hπc' : QuotientGroup.mk' N₀ c' = y ^ m := by
    rw [hc', map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : c' ^ 4 = 1 := by
    have h1 : c' ^ 4 ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (c' ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ Nat.card N₀ := orderOf_dvd_natCard _
    have h3 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show (c' ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card N₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨c' ^ 4, h1⟩ : N₀) = 1 := Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ c' ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : c' ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf c' = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  set y₁ : G := (c' : G) with hy₁
  have hy₁M : y₁ ∈ M₁ :=
    ExactLayer.exactCore_le_left a M₁ ((ExactLayer.exactCore a M₁).pow_mem hcM m)
  have hy₁Y : y₁ ∈ Y := c'.2
  have hy₁4 : orderOf y₁ = 4 := by rw [hy₁, Subgroup.orderOf_coe]; exact hc'_ord
  
  have hfixc : QuotientGroup.mk' N₀ (conjOnSub Y hbY c') = QuotientGroup.mk' N₀ c' := by
    have h1 : layerAut Y hbY (QuotientGroup.mk' N₀ c') =
        QuotientGroup.mk' N₀ (conjOnSub Y hbY c') := layerAut_mk Y hbY c'
    have h2 : layerAut Y hbY (y ^ m) = y ^ m := by rw [map_pow, hfix]
    calc QuotientGroup.mk' N₀ (conjOnSub Y hbY c') = layerAut Y hbY (QuotientGroup.mk' N₀ c') :=
          h1.symm
      _ = layerAut Y hbY (y ^ m) := by rw [hπc']
      _ = y ^ m := h2
      _ = QuotientGroup.mk' N₀ c' := hπc'.symm
  have hcom : ⁅b, y₁⁆ ∈ oddCoreOf Y := by
    have h1 : conjOnSub Y hbY c' * c'⁻¹ ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (conjOnSub Y hbY c' * c'⁻¹) = 1 := by
        rw [map_mul, map_inv, hfixc, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjOnSub,
      commutatorElement_def]
    rw [hy₁]
  
  have hR2 : IsPGroup 2 (Subgroup.zpowers y₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4]; norm_num)
  have hcN : b ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (mem_normalizer_iff_conjSub_eq.mpr hbY)
  have huN : y₁ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁Y)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes hb2 (oddCoreOf_odd_natCard Y) hR2
    (Subgroup.zpowers_le.mpr huN) hcN
    (fun r hr => C25X.comm_mem_of_mem_zpowers huN hcom hr)
  have hnY : n ∈ Y := oddCoreIn_le _ hn
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := ExactLayer.exactLayer_le_centralizer Ω a hnY
  have hyc : (n * y₁ * n⁻¹) * b = b * (n * y₁ * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers y₁)))
  
  have hJ₀Ω : conjSub n M₁ ∈ Ω := hΩ.conjInvariant n M₁ hM₁tq.1
  have hJ₀z : IsUniqueInvolution (conjSub n M₁) (n * (g₁ * z * g₁⁻¹) * n⁻¹) := hzM₁.conj n
  have hyJ' : n * y₁ * n⁻¹ ∈ conjSub n M₁ := conj_mem_conjSub hy₁M
  have hy4' : orderOf (n * y₁ * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) y₁
    simpa [MulAut.conj_apply, hy₁4] using this
  by_cases hbeq : b = n * (g₁ * z * g₁⁻¹) * n⁻¹
  · have hfin : IsUniqueInvolution (conjSub n M₁) b := by
      rw [hbeq]
      exact hJ₀z
    exact ⟨conjSub n M₁, ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hnC hM₁tq, hfin⟩
  · exfalso
    exact T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hbeq hyJ' hy4' hyc.symm
end NC4
section Single
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem exactImg_conjSub_layer {a : G} {M : Subgroup G} (x : ↥(ExactLayer.exactLayer Ω a)) :
    T7H.exactImg Ω a (conjSub (x : G) M) =
      conjSub (QuotientGroup.mk x) (T7H.exactImg Ω a M) := by
  have hnc : (x : G) * a * (x : G)⁻¹ = a := T7H.mem_centralizer_of_mem_exactLayer
  have h1 : ExactLayer.exactCore a (conjSub (x : G) M) = conjSub (x : G) (ExactLayer.exactCore a M)
      := by
    have := ExactLayer.exactCore_conjSub (x : G) a M
    rwa [hnc] at this
  unfold T7H.exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub]
  rfl

theorem exists_centralizer_conj_of_member (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (hzY : z ∈ ExactLayer.exactLayer Ω a) (hK : K ∈ ExactLayer.tqMembers Ω a)
    (D : LieSystemData 3 1 (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))
      (oddQuotientFamily (ExactLayer.exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {M : Subgroup G} (hM : M ∈ ExactLayer.tqMembers Ω a) {b : G} (hb : IsUniqueInvolution M b) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = b := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  
  obtain ⟨i, R₁, hR₁, hKbar⟩ := D.fundamental _ (T7H.exactImg_mem hK)
  obtain ⟨i', R₂, hR₂, hMbar⟩ := D.fundamental _ (T7H.exactImg_mem hM)
  have hii : i' = i := Fin.ext (by have h1 := i.2; have h2 := i'.2; omega)
  subst hii
  obtain ⟨g, hg⟩ := RouteD.Gaps.fundamentalSingleClass_of_ne D i' (hD4 i').1 (hD4 i').2
    R₁ hR₁ R₂ hR₂
  have hMK : T7H.exactImg Ω a M = conjSub (D.hom i' g) (T7H.exactImg Ω a K) := by
    rw [hMbar, hKbar, hg, AscQuot.map_conjSub]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (D.hom i' g)
  have hxC : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := ExactLayer.exactLayer_le_centralizer Ω
      a x.2
  have hK₁ : conjSub (x : G) K ∈ ExactLayer.tqMembers Ω a :=
    ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hxC hK
  have hb₁ : IsUniqueInvolution (conjSub (x : G) K) ((x : G) * z * (x : G)⁻¹) := hz.conj _
  have hb₁Y : (x : G) * z * (x : G)⁻¹ ∈ ExactLayer.exactLayer Ω a :=
    (ExactLayer.exactLayer Ω a).mul_mem ((ExactLayer.exactLayer Ω a).mul_mem x.2 hzY)
        ((ExactLayer.exactLayer Ω a).inv_mem x.2)
  have hbY : b ∈ ExactLayer.exactLayer Ω a :=
    ExactLayer.exactCore_le_exactLayer hM (T7H.isUniqueInvolution_exactCore hΩ hcpg hM hb).mem
  have hbarM := T7H.exactImg_isUnique hΩ hcpg hM hb hbY
  have hbar₁ := T7H.exactImg_isUnique hΩ hcpg hK₁ hb₁ hb₁Y
  have hEq : T7H.exactImg Ω a (conjSub (x : G) K) = T7H.exactImg Ω a M := by
    rw [exactImg_conjSub_layer, hMK, hx]
  rw [hEq] at hbar₁
  have hbb : T7H.toBar Ω a b hbY = T7H.toBar Ω a ((x : G) * z * (x : G)⁻¹) hb₁Y :=
    hbarM.eq hbar₁
  
  set u : ↥(ExactLayer.exactLayer Ω a) := ⟨(x : G) * z * (x : G)⁻¹, hb₁Y⟩ with hu
  set v : ↥(ExactLayer.exactLayer Ω a) := ⟨b, hbY⟩ with hv
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    show ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = 1
    calc ((x : G) * z * (x : G)⁻¹) * ((x : G) * z * (x : G)⁻¹) = (x : G) * (z * z) * (x : G)⁻¹ := by
          group
      _ = 1 := by rw [hz.sq]; group
  have hv2 : v * v = 1 := by
    apply Subtype.ext
    exact hb.sq
  have huv : u * v ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a) := by
    have h1 : u⁻¹ * v ∈ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a) :=
      QuotientGroup.eq.mp hbb.symm
    rwa [inv_eq_of_mul_eq_one_right hu2] at h1
  obtain ⟨n, hn, hnv⟩ := exists_conj_of_involutions_odd
    (CFSG.ComponentClassification.OddCore.odd_card ↥(ExactLayer.exactLayer Ω a)) hu2 hv2 huv
  refine ⟨(n : G) * (x : G), ?_, ?_⟩
  · exact (Subgroup.centralizer ({a} : Set G)).mul_mem
      (ExactLayer.exactLayer_le_centralizer Ω a n.2) hxC
  · have h1 : b = (n : G) * ((x : G) * z * (x : G)⁻¹) * (n : G)⁻¹ := congrArg Subtype.val hnv
    rw [h1]
    group
end Single
end C25Y
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Four
variable {G : Type} [Group G]
end Four
section Model
variable {G : Type} [Group G]
end Model
section ModelFact
end ModelFact
section Six
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem not_layerOrthSix (hM6 : Layer6Cen4 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z) :
    ¬ LayerOrthType Ω a 6 (!piSign 3 1) := by
  classical
  intro hL
  obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := hL
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ :=
    C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have hnGF := not_goodFusion hyp ha2 ha1 haz haA hconj hA0
  unfold GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  have hb2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hs.hz.sq]; group
  have hbY : conjSub (w * z * w⁻¹) (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hwC
  have htag : t' = .PSL ∨ t' = .PSU := by
    rcases hT with ⟨h5, _⟩ | ⟨_, _, ht, _⟩ | ⟨_, _, ht, _⟩ | ⟨h7, _⟩ | ⟨h8, _⟩ | ⟨h8, _⟩
    · omega
    · exact Or.inl ht
    · exact Or.inr ht
    · omega
    · omega
    · omega
  have hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
    subst hi
    rw [hDt]
    rcases htag with rfl | rfl <;> simp
  have hΦ : ∀ J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a), ∀ y : ↥(ExactLayer.exactLayer Ω a) ⧸
      classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a),
      conjSub y J ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← exactImg_conjSub_layer x]
    exact T7H.exactImg_mem (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant
      (ExactLayer.exactLayer_le_centralizer Ω a x.2) hMtq)
  obtain ⟨J, hJ, y, hyJ, hy4, hy2, hβy⟩ := hM6 _ _ D _ _ _ _ _ hD1
    ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw hΦ (layerAut (ExactLayer.exactLayer Ω a) hbY)
    (layerAut_involutive _ hbY hb2)
  obtain ⟨M, hM, hMb⟩ := nc4_lift hyp ha2 hwC hJ hyJ hy4 hy2 hβy
  obtain ⟨h, hhC, hh⟩ := exists_centralizer_conj_of_member hyp ha2 hzY hK₂ D hD1 hD4 hM hMb
  exact hw h hhC hh
end Six
end C25Y
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement
namespace C25Y
open CFSG.ClassicalInvolution.Asc77.C25Y
section Four
variable {G : Type} [Group G]
end Four
section Swap
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}
end Swap
section SwapFusion
variable {G : Type} [Group G]
end SwapFusion
section Assembly

@[expose] def C25_11Ω5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
          (∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
            b = 1 ∨ b = a ∨ b = z ∨ b = a * z) →
          z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
          z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)) →
          LayerOrthType Ω (a * z) 5 true →
            ¬ LayerOrthType Ω a 5 true

theorem c25_11Typed_of_residuals (hnc4 : C25X.NC4Fact) (h9 : C25_9) (hM6 : Layer6Cen4 3 1) (h5 :
    C25_11Ω5) :
    C25X.C25_11Typed := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  obtain ⟨hcard, hex⟩ := h9 G Ω K K' W S R R' z t u₁ u₂ hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have haz' : a * z = z * a := hyp.hzS a haA.1
  obtain ⟨hAeq, hE⟩ := eq_closure_of_card_le_four hcard ha2 hz2 ha1 hz1 haz haz' haA hzA
  have hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z := fun b hb =>
    mem_closure_pair ha2 hz2 haz' (hAeq ▸ hb)
  have hc4 : Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
    rw [hE.1]; norm_num
  obtain ⟨a', hcl, hb1, hb2⟩ := hex hc4
  have ha'A : a' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    rw [← hcl]
    exact Subgroup.subset_closure (by simp)
  have ha'2 : a' * a' = 1 := hE.2 a' ha'A
  have ha'z : a' * z = z * a' := comm_of_forall_sq_eq_one hE.2 ha'A hzA
  have haa' : a = a' ∨ a = a' * z := by
    have hmem : a ∈ Subgroup.closure ({a', z} : Set G) := by rw [hcl]; exact haA
    rcases mem_closure_pair ha'2 hz2 ha'z hmem with h | h | h | h
    · exact absurd h ha1
    · exact Or.inl h
    · exact absurd h haz
    · exact Or.inr h
  have hazz : a' * z * z = a' := by rw [mul_assoc, hz2, mul_one]
  have hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
    rcases haa' with h | h
    · rw [h]; exact hb1
    · rw [h]; exact hb2
  have hbad' : z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)) := by
    rcases haa' with h | h
    · rw [h]; exact hb2
    · rw [h, hazz]; exact hb1
  have haA₂ : a * z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ haA hzA
  have ha₂2 : (a * z) * (a * z) = 1 := hE.2 _ (hAeq ▸ haA₂)
  have ha₂1 : a * z ≠ 1 := by
    intro h
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right hz2]
  have ha₂z : a * z ≠ z := by
    intro h
    apply ha1
    calc a = (a * z) * z⁻¹ := by group
      _ = z * z⁻¹ := by rw [h]
      _ = 1 := by group
  have hazz' : (a * z) * z = a := by rw [mul_assoc, hz2, mul_one]
  have hconj₂ : ∀ s ∈ (S : Subgroup G), s * (a * z) * s⁻¹ = a * z ∨
      s * (a * z) * s⁻¹ = (a * z) * z := by
    intro s hs
    have hszs : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
        _ = z := by group
    have hsa : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * z := by
      calc s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
        _ = (s * a * s⁻¹) * z := by rw [hszs]
    rcases hconj s hs with h | h
    · left; rw [hsa, h]
    · right; rw [hsa, h, hazz']
  have hA0₂ : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a * z ∨ b = z ∨ b = (a * z) * z := by
    intro b hb
    rcases hA0 b hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [hazz', h])))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  have haR₂ : ∀ x ∈ R, (a * z) * x = x * (a * z) := by
    intro x hx
    have hcent := Subgroup.mem_centralizer_iff.mp haA.2
    have h1 : a * x = x * a := (hcent x (Subgroup.mem_sup_left hx)).symm
    have h2 : x * z = z * x := hyp.hzS x (hyp.hR.2.2 hx)
    calc (a * z) * x = a * (z * x) := by group
      _ = a * (x * z) := by rw [h2]
      _ = (a * x) * z := by group
      _ = (x * a) * z := by rw [h1]
      _ = x * (a * z) := by group
  have haR'₂ : ∀ x ∈ R', (a * z) * x = x * (a * z) := by
    intro x hx
    have hcent := Subgroup.mem_centralizer_iff.mp haA.2
    have h1 : a * x = x * a := (hcent x (Subgroup.mem_sup_right hx)).symm
    have h2 : x * z = z * x := hyp.hzS x (hyp.hR'.2.2 hx)
    calc (a * z) * x = a * (z * x) := by group
      _ = a * (x * z) := by rw [h2]
      _ = (a * x) * z := by group
      _ = (x * a) * z := by rw [h1]
      _ = x * (a * z) := by group
  have h5z : LayerOrthType Ω (a * z) 5 true := by
    rcases C25X.layer_a_typed_proved hnc4 hyp ha₂2 ha₂1 haR₂ haR'₂ with h | h | h
    · exact absurd h hbad'
    · exact h
    · exact absurd h (not_layerOrthSix hM6 hyp ha₂2 ha₂1 ha₂z haA₂ hconj₂ hA0₂)
  rintro (hL5 | hL6)
  · exact h5 G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hA0 hbad hbad' h5z hL5
  · exact not_layerOrthSix hM6 hyp ha2 ha1 haz haA hconj hA0 hL6

theorem c25_11_of_residuals (hnc4 : C25X.NC4Fact) (h9 : C25_9) (hM6 : Layer6Cen4 3 1) (h5 :
    C25_11Ω5) :
    C25_11 :=
  C25X.c25_11_of_typed hnc4 (c25_11Typed_of_residuals hnc4 h9 hM6 h5)
end Assembly
end C25Y
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y1
public import CFSG.ClassicalInvolution.Asc77.AscC25X1
public import CFSG.ClassicalInvolution.Asc77.AscT7U11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Swap

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem eq_conj_twin_of_unique (hs : Hyp23Setting p f Ω K K' z) {h : G} {M : Subgroup G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M (h * z * h⁻¹)) :
    M = conjSub h K ∨ M = conjSub h K' := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
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

theorem not_swap_in_both (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a t' h m : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K')
    (hzt : z ≠ t') (hzc : z * t' * z⁻¹ = t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z)
    (hh : h * z * h⁻¹ = t') (hha : h * a = a * h)
    (hm : m * z * m⁻¹ = t') (hma : m * (a * z) = (a * z) * m) : False := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
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

@[expose] def GoodFusion (z a : G) : Prop :=
  ∀ w : G, w * z * w⁻¹ ∈ Subgroup.centralizer ({a} : Set G) →
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = w * z * w⁻¹

end Fusion

section NotGood

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem zpow_eq_one_or_self {a : G} (ha2 : a * a = 1) (k : ℤ) : a ^ k = 1 ∨ a ^ k = a := by
  rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
  · left
    rw [hk, zpow_mul, zpow_two, ha2, one_zpow]
  · right
    rw [hk, zpow_add_one, zpow_mul, zpow_two, ha2, one_zpow, one_mul]

theorem not_goodFusion (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z) :
    ¬ GoodFusion z a := by
  intro hGF
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
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
    exact (l17_8 (p := p) (f := f)) G Ω K hs.stand S _ hES hE1 hEab ⟨hES, hsc⟩

end NotGood

end C25Y

end CFSG.ClassicalInvolution.Asc77

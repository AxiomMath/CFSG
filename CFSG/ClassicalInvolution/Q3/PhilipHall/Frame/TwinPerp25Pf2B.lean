module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25Y2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.ClassicalInvolution.Asc77.C25Y (GoodFusion)
open CFSG.ClassicalInvolution.Asc77.C25H (zpow_eq_one_or_self)
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}



theorem false_of_isolated {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hsc : ∀ g : G, g * a * g⁻¹ ∈ (S : Subgroup G) → g * a * g⁻¹ ∈ Subgroup.zpowers a) : False := by
  have hne1 : ∀ g : G, g * a * g⁻¹ ≠ 1 := fun g h => ha1 (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hiso : ∀ g : G, g * a * g⁻¹ ∈ (S : Subgroup G) → g * a * g⁻¹ = a := by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsc g hg)
    rcases zpow_eq_one_or_self ha2 k with h | h
    · exact absurd (hk.symm.trans h) (hne1 g)
    · exact hk.symm.trans h
  have hzc : ∀ s ∈ (S : Subgroup G), s * a = a * s := by
    intro s hs
    have h1 := hiso s (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs haS) (Subgroup.inv_mem _ hs))
    calc s * a = (s * a * s⁻¹) * s := by group
      _ = a * s := by rw [h1]
  obtain ⟨g, hg, hgne⟩ := T7C.exists_conj_mem_sylow_ne_core S haS hzc ha2 ha1
  apply hgne
  have := hiso g⁻¹ (by simpa using hg)
  simpa using this

theorem comm_of_normalizes_of_trivialOnQuot {M T : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ M)
    {s : G} (hsM : s ∈ trivialOnQuot M) (hsT : conjSub s T = T) {r : G} (hr : r ∈ T) :
    s * r = r * s := by
  have hrT : s * r * s⁻¹ ∈ T := by
    rw [← hsT]
    exact conj_mem_conjSub hr
  have hcomm : ⁅s, r⁆ ∈ T := by
    have : ⁅s, r⁆ = (s * r * s⁻¹) * r⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact T.mul_mem hrT (T.inv_mem hr)
  have hodd : ⁅s, r⁆ ∈ oddCoreIn M := hsM.2 r (hTM hr)
  have h1 := CFSG.ClassicalInvolution.Asc77.C25Y.eq_one_of_mem_isPGroup_of_mem_odd hT2
    (odd_card_oddCoreIn M) hcomm hodd
  have h2 : s * r * s⁻¹ * r⁻¹ = 1 := by
    simpa [commutatorElement_def] using h1
  calc s * r = (s * r * s⁻¹ * r⁻¹) * (r * s) := by group
    _ = r * s := by rw [h2, one_mul]

theorem trivialOnQuot_of_centralizes (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (haR : ∀ x ∈ R, a * x = x * a) : a ∈ trivialOnQuot K := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  refine (Q3.PhilipHall.Frame.TwinLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hyp.std.1.quot2 hcpg
    hs.stand.mem).mpr ⟨R, T7C.isSylow2In_of_mem_RSet_of_le hΩ hs.stand.mem hyp.hR.1 hyp.hR.2.1, ?_⟩
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (haR x hx).symm

theorem trivialOnQuot_of_centralizes' (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (haR : ∀ x ∈ R', a * x = x * a) : a ∈ trivialOnQuot K' := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  refine (Q3.PhilipHall.Frame.TwinLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hyp.std.1.quot2 hcpg
    hs.hK'.1).mpr ⟨R', T7C.isSylow2In_of_mem_RSet_of_le hΩ hs.hK'.1 hyp.hR'.1 hyp.hR'.2.1, ?_⟩
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (haR x hx).symm



theorem conjSub_pair_of_central (hs : Hyp23Setting Ω K K' z) {c : G}
    (hc : c * z * c⁻¹ = z) :
    (conjSub c K = K ∧ conjSub c K' = K') ∨ (conjSub c K = K' ∧ conjSub c K' = K) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
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

theorem conjSub_R_eq_of_mem_normalizer (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsK : s ∈ Subgroup.normalizer (K : Set G)) :
    conjSub s R = R := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  rcases perm_R hyp hsS (Or.inl rfl : R = R ∨ R = R') with h | h
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
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  rcases perm_R hyp hsS (Or.inr rfl : R' = R ∨ R' = R') with h | h
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




theorem eq_conj_twin_of_unique (hs : Hyp23Setting Ω K K' z) {h : G} {M : Subgroup G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M (h * z * h⁻¹)) :
    M = conjSub h K ∨ M = conjSub h K' := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
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
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
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
  have haK : a ∈ trivialOnQuot K := trivialOnQuot_of_centralizes hyp ha2 haR
  have haK' : a ∈ trivialOnQuot K' := trivialOnQuot_of_centralizes' hyp ha2 haR'
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
    comm_swap_of_normal_four hyp ht'S ht'2 hg hnf haS hconj
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
    exact false_of_isolated haS ha2 ha1 (fun g hg => hsc a (Subgroup.mem_zpowers a) g hg)



end CFSG.ClassicalInvolution.Q8P.Asc77.P25S

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

@[expose] def L28RankAt {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  ∀ N : Subgroup Y, N ≤ P → P ≤ Subgroup.normalizer (N : Set Y) →
    ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥N →* CatGroup d), IsCaseTwoIndex 3 d →
      Function.Surjective ψ →
      ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
        E ⊓ Subgroup.centralizer (L : Set Y) = ⊥

@[expose] def L28TwoRankAt {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  ∀ N : Subgroup Y, N ≤ P → P ≤ Subgroup.normalizer (N : Set Y) →
    ∀ (d₁ d₂ : TauCeti.ValidLieTypeIndex) (ψ : ↥N →* CatGroup d₁ × CatGroup d₂),
      IsCaseTwoIndex 3 d₁ → IsCaseTwoIndex 3 d₂ → Function.Surjective ψ →
      3 ≤ Open.pRank 7 L

@[expose] def KFactCompParabL28RankOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → L28RankAt L P

@[expose] def KFactCompParabL28TwoRankOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → L28TwoRankAt L P

theorem kFactCompParabL28Rank_of_families (hA : KFactCompParabL28RankOn (IsLieOf IdxA))
    (h2A : KFactCompParabL28RankOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabL28RankOn (IsLieOf IdxB)) (hD : KFactCompParabL28RankOn (IsLieOf IdxD))
    (h2D : KFactCompParabL28RankOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabL28RankOn (IsLieOf IdxG2))
    (hS : KFactCompParabL28RankOn IsSmallTwoOrG2) : KFactCompParabL28Rank := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

theorem kFactCompParabL28TwoRank_of_families (hA : KFactCompParabL28TwoRankOn (IsLieOf IdxA))
    (h2A : KFactCompParabL28TwoRankOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabL28TwoRankOn (IsLieOf IdxB))
    (hD : KFactCompParabL28TwoRankOn (IsLieOf IdxD))
    (h2D : KFactCompParabL28TwoRankOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabL28TwoRankOn (IsLieOf IdxG2))
    (hS : KFactCompParabL28TwoRankOn IsSmallTwoOrG2) : KFactCompParabL28TwoRank := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

theorem card_mem_of_l28Section {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ) {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯) {N : Subgroup Y} (hNP : N ≤ P)
    (hPN : P ≤ Subgroup.normalizer (N : Set Y)) {d : TauCeti.ValidLieTypeIndex}
    (ψ : ↥N →* CatGroup d) (hd : IsCaseTwoIndex 3 d) (hψ : Function.Surjective ψ) :
    504 ∈ 𝒯 := by
  have hcase : IsCaseTwoGroup 3 (CatGroup d) := ⟨d, hd, ⟨MulEquiv.refl _⟩⟩
  have : IsSimpleGroup (CatGroup d) := isSimpleGroup_of_isCaseTwoGroup_three hcase
  have : Finite (CatGroup d) := Finite.of_surjective ψ hψ
  have hcard := card_of_isCaseTwoGroup_three hcase
  have h := card_mem_of_section (O := (⊥ : Subgroup Y)) (W := N) hPL ρ hρ hQ bot_le
    (by intro x _; rw [Subgroup.mem_normalizer_iff]; intro h; simp) (by simp) hNP
    (by simpa using hPN)
    (ThreeFives.exists_noncomm_of_simple inferInstance (by rw [hcard]; norm_num))
    (by rw [hcard]; norm_num) ψ hψ
  rwa [hcard] at h

theorem isElemAbelian_range_of_pow {G A : Type*} [Group G] [Group A] {p : ℕ}
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (f : A →* G) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]

theorem pi_pow_seven_eq_one {M : Type*} [CommGroup M] (hM : Nat.card M = 7) (r : ℕ)
    (a : Fin r → M) : a ^ 7 = 1 := by
  funext j
  rw [Pi.pow_apply, Pi.one_apply, ← hM]
  exact pow_card_eq_one'

theorem card_fin_pi_eq_seven_pow {M : Type*} [Group M] (hM : Nat.card M = 7) (r : ℕ) :
    Nat.card (Fin r → M) = 7 ^ r := by
  rw [Nat.card_fun, hM, Nat.card_fin]

theorem eq_one_of_mem_centralizer_of_not_dvd {Y : Type} [Group Y] {L : Subgroup Y}
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥L)) {x : Y} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (L : Set Y)) (hx7 : x ^ 7 = 1) : x = 1 := by
  have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC g g.2
  have h1 : orderOf (⟨x, hxL⟩ : ↥L) ∣ 7 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using hx7)
  have h2 : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h1 with h | h
  · have := orderOf_eq_one_iff.1 h
    exact congrArg Subtype.val this
  · exact absurd (h ▸ h2) hZ

theorem l28_E_of_torus {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {M : Type*} [CommGroup M]
    (hM : Nat.card M = 7) (f : (Fin 2 → M) →* Y) (hf : Function.Injective f)
    (hL : f.range ≤ L) (hc : ∀ a, f a ∈ Subgroup.centralizer (L : Set Y) → a = 1) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  refine ⟨f.range, hL, isElemAbelian_range_of_pow (fun a b => mul_comm a b)
    (pi_pow_seven_eq_one hM 2) f, ?_, ?_⟩
  · rw [← card_fin_pi_eq_seven_pow hM 2]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    rw [hc a hxC, map_one]
    exact Subgroup.one_mem _

theorem l28_E_of_torus_of_not_dvd {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {M : Type*}
    [CommGroup M] (hM : Nat.card M = 7) (hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥L))
    (f : (Fin 2 → M) →* Y) (hf : Function.Injective f) (hL : f.range ≤ L) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ :=
  l28_E_of_torus hM f hf hL fun a ha => by
    have h1 : f a = 1 := eq_one_of_mem_centralizer_of_not_dvd hZ (hL ⟨a, rfl⟩) ha
      (by rw [← map_pow, pi_pow_seven_eq_one hM 2 a, map_one])
    exact hf (h1.trans (map_one f).symm)

theorem three_le_pRank_of_torus {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {M : Type*}
    [CommGroup M] (hM : Nat.card M = 7) (f : (Fin 3 → M) →* Y) (hf : Function.Injective f)
    (hL : f.range ≤ L) : 3 ≤ Open.pRank 7 L :=
  CFSG.SectionRank.le_pRank_of_injective (p := 7) (by norm_num) (fun a b => mul_comm a b)
    (pi_pow_seven_eq_one hM 3) (card_fin_pi_eq_seven_pow hM 3) f hf hL

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

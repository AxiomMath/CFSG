module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankAny

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley CFSG.LieType.Steinberg

theorem le_pRank_three_of_central_ker {G Y : Type*} [Group G] [Group Y] [Finite Y] {n : ℕ}
    (π : G →* Y) (hker : ∀ z, π z = 1 → z ∈ Subgroup.center G)
    (Z A : Fin n → G) (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ i, ∀ g ∈ Subgroup.zpowers (Z i), Commute g (A i) → g = 1 := by
    intro i g hg hc
    rcases eq_one_or_of_mem_zpowers_three (h3 i) hg with h | h | h
    · exact h
    · exact absurd (h ▸ hc) (h1 i)
    · exact absurd (h ▸ hc) (h2 i)
  have hcent : ∀ i, ∀ j, i ≠ j → Subgroup.zpowers (Z j) ≤ Subgroup.centralizer {A i} := by
    intro i j hij
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hZA i j hij).eq.symm
  let ϕ : ∀ i, Subgroup.zpowers (Z i) →* Y := fun i => π.comp (Subgroup.zpowers (Z i)).subtype
  have hϕcomm : Pairwise fun i j => ∀ (x : Subgroup.zpowers (Z i)) (y : Subgroup.zpowers (Z j)),
      Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change Commute (π (x : G)) (π (y : G))
    rw [← ha, ← hb]
    exact ((hZZ i j hij).zpow_zpow a b).map π
  have hcenter : ∀ i, ∀ g : G, g ∈ Subgroup.center G → Commute g (A i) := fun i g hg =>
    (Subgroup.mem_center_iff.1 hg (A i)).symm
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change π (x : G) = 1 at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (key i _ x.2 (hcenter i _ (hker _ hx))))
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), (ϕ j).range) ≤
        (Subgroup.centralizer {A i}).map π := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hcent i j (Ne.symm hj) y.2, rfl⟩
    obtain ⟨r, hr, hrx⟩ := hle hg
    change π r = π (x : G) at hrx
    have hrx' : r⁻¹ * (x : G) ∈ Subgroup.center G := hker _ (by rw [map_mul, map_inv, hrx]; group)
    have hxr : (x : G) = r * (r⁻¹ * x) := by group
    have hc : Commute (x : G) (A i) := by
      rw [hxr]
      have hrc : Commute r (A i) := (Subgroup.mem_centralizer_iff.1 hr (A i) rfl).symm
      exact hrc.mul_left (hcenter i _ hrx')
    have := key i _ x.2 hc
    change π (x : G) ∈ (⊥ : Subgroup Y)
    rw [this, map_one]
    exact one_mem _
  have hΦ := MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (hcomm := hϕcomm) hind hϕinj
  have hord : ∀ i, Nat.card (Subgroup.zpowers (Z i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h3 i) fun h => (h1 i) (h ▸ Commute.one_left _)
  refine le_pRank_of_injective (p := 3) (by norm_num) (fun a b => ?_) (fun a => ?_) ?_ _ hΦ
    le_top
  · funext i
    obtain ⟨x, hx⟩ := (a i).2
    obtain ⟨y, hy⟩ := (b i).2
    exact Subtype.ext (by
      change (a i : G) * (b i : G) = (b i : G) * (a i : G)
      rw [← hx, ← hy]
      exact (Commute.zpow_zpow_self _ _ _).eq)
  · funext i
    apply Subtype.ext
    change ((a i : G)) ^ 3 = 1
    obtain ⟨x, hx⟩ := (a i).2
    rw [← hx, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3 i, one_zpow]
  · rw [Nat.card_pi, Finset.prod_congr rfl fun i _ => hord i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]

theorem two_le_pRank_three_of_sl2_pair {G Y : Type*} [Group G] [Group Y] [Finite Y]
    (π : G →* Y) (hker : ∀ z, π z = 1 → z ∈ Subgroup.center G)
    {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (φ₁ : Matrix.SpecialLinearGroup (Fin 2) F₁ →* G)
    (φ₂ : Matrix.SpecialLinearGroup (Fin 2) F₂ →* G)
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂)
    (hc : ∀ s t, Commute (φ₁ s) (φ₂ t)) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  refine le_pRank_three_of_central_ker π hker ![φ₁ (sl2Three (K := F₁)), φ₂ (sl2Three (K := F₂))]
    ![φ₁ (sl2Upper 1), φ₂ (sl2Upper 1)] ?_ ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · change φ₁ (sl2Three (K := F₁)) ^ 3 = 1
      rw [← map_pow, sl2Three_pow_three, map_one]
    · change φ₂ (sl2Three (K := F₂)) ^ 3 = 1
      rw [← map_pow, sl2Three_pow_three, map_one]
  · intro i
    fin_cases i
    · intro h
      apply sl2Three_not_commute (K := F₁)
      have := h.eq
      change φ₁ (sl2Three (K := F₁)) * φ₁ (sl2Upper 1) = φ₁ (sl2Upper 1) * φ₁ (sl2Three (K := F₁)) at this
      rw [← map_mul, ← map_mul] at this
      exact h₁ this
    · intro h
      apply sl2Three_not_commute (K := F₂)
      have := h.eq
      change φ₂ (sl2Three (K := F₂)) * φ₂ (sl2Upper 1) = φ₂ (sl2Upper 1) * φ₂ (sl2Three (K := F₂)) at this
      rw [← map_mul, ← map_mul] at this
      exact h₂ this
  · intro i
    fin_cases i
    · intro h
      apply sl2Three_sq_not_commute (K := F₁)
      have := h.eq
      change φ₁ (sl2Three (K := F₁)) ^ 2 * φ₁ (sl2Upper 1) = φ₁ (sl2Upper 1) * φ₁ (sl2Three (K := F₁)) ^ 2 at this
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact h₁ this
    · intro h
      apply sl2Three_sq_not_commute (K := F₂)
      have := h.eq
      change φ₂ (sl2Three (K := F₂)) ^ 2 * φ₂ (sl2Upper 1) = φ₂ (sl2Upper 1) * φ₂ (sl2Three (K := F₂)) ^ 2 at this
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact h₂ this
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (hc _ _).symm
    · exact hc _ _
    · exact absurd rfl hij
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hc _ _
    · exact (hc _ _).symm
    · exact absurd rfl hij

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

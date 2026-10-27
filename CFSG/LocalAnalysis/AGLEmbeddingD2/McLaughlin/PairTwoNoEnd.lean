module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureAssembly

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem zpowers_inf_eq_bot_of_pow_three {X : Type*} [Group X] {w : X} {Y : Subgroup X}
    (hw3 : w ^ 3 = 1) (hwY : w ∉ Y) : Subgroup.zpowers w ⊓ Y = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu.1
  rw [Subgroup.mem_bot]
  by_contra hne'
  apply hwY
  have hk : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨m, rfl⟩
    apply hne'
    rw [zpow_mul, show w ^ (3 : ℤ) = 1 by exact_mod_cast hw3, one_zpow]
  have hord : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have hcop3 : Int.gcd k 3 = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd Int.prime_three).mpr hk).symm
  have hcop : Int.gcd k (orderOf w) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact_mod_cast hcop3
  exact (Subgroup.zpowers_le.mpr hu.2) (mem_zpowers_zpow_iff.mpr hcop)

theorem pRank_inf_centralizers_eq_zero (h : AGLPair 3 M H R) (h84 : Asc81bEightFour)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hH : Open.pRank 3 H = 2)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L₁ L₂ : Subgroup G} (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁)
    (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂) (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    {Fb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hF : Fb ≤ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Open.pRank 3 Fb = 0 := by
  set L₁b := barM M L₁
  set L₂b := barM M L₂
  set C₁ := Subgroup.centralizer (L₁b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set C₂ := Subgroup.centralizer (L₂b : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set Kb := barM M (Subgroup.normalizer (pCoreOf 2 H : Set G))
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hcomp : ⁅L₁b, L₂b⁆ = ⊥ := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    hL₁.component hL₂.component hne
  have hL₂C₁ : L₂b ≤ C₁ := by
    have hcomp' : ⁅L₂b, L₁b⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomp
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp'
  have hFK : Fb ≤ Kb := fun u hu =>
    h.mem_barM_normalizer_of_centralizes_weakSBlocks h84 h86 hD2 fun L' hL' => by
      rcases hk2 L' hL' with he | he
      · exact he.symm ▸ (hF hu).1
      · exact he.symm ▸ (hF hu).2
  obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ :=
    CFSG.AGLEmbeddingD2.exists_order_three_noncentral hL₁.le (hthree L₁ hL₁) hZ₁
  obtain ⟨y₂, hy₂P, hy₂3, hy₂C⟩ :=
    CFSG.AGLEmbeddingD2.exists_order_three_noncentral hL₂.le (hthree L₂ hL₂) hZ₂
  have hy₁K : y₁ ∈ Kb := barM_mono inf_le_left hy₁P
  have hy₂K : y₂ ∈ Kb := barM_mono inf_le_left hy₂P
  have hy₂L : y₂ ∈ L₂b := barM_mono inf_le_right hy₂P
  have hy₁L : y₁ ∈ L₁b := barM_mono inf_le_right hy₁P
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁C (h1 ▸ Subgroup.one_mem _)
  have hy₂1 : y₂ ≠ 1 := fun h1 => hy₂C (h1 ▸ Subgroup.one_mem _)
  have hrk1 : ∀ w : ↥M ⧸ CFSG.pCore 2 ↥M, w ^ 3 = 1 → w ≠ 1 →
      1 ≤ Open.pRank 3 (Subgroup.zpowers w) := fun w hw3 hw1 =>
    CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3
      (by rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1])
  have hcomm1 : ∀ a ∈ Subgroup.zpowers y₂, ∀ b ∈ Fb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp (hF hb).2 y₂ hy₂L) i).eq
  have hi1 : Subgroup.zpowers y₂ ⊓ Fb = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    have h0 := zpowers_inf_eq_bot_of_pow_three hy₂3 hy₂C
    have : u ∈ Subgroup.zpowers y₂ ⊓ C₂ := ⟨hu.1, (hF hu.2).2⟩
    rw [h0] at this
    exact this
  have hs1 := pRank_add_le_pRank_sup_of_coprime h3 hcomm1 (by rw [hi1]; simp)
  have hYC₁ : Subgroup.zpowers y₂ ⊔ Fb ≤ C₁ :=
    sup_le (Subgroup.zpowers_le.mpr (hL₂C₁ hy₂L)) fun b hb => (hF hb).1
  have hcomm2 : ∀ a ∈ Subgroup.zpowers y₁, ∀ b ∈ Subgroup.zpowers y₂ ⊔ Fb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.mp (hYC₁ hb) y₁ hy₁L) i).eq
  have hi2 : Subgroup.zpowers y₁ ⊓ (Subgroup.zpowers y₂ ⊔ Fb) = ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    have h0 := zpowers_inf_eq_bot_of_pow_three hy₁3 hy₁C
    have : u ∈ Subgroup.zpowers y₁ ⊓ C₁ := ⟨hu.1, hYC₁ hu.2⟩
    rw [h0] at this
    exact this
  have hs2 := pRank_add_le_pRank_sup_of_coprime h3 hcomm2 (by rw [hi2]; simp)
  have hsup : Subgroup.zpowers y₁ ⊔ (Subgroup.zpowers y₂ ⊔ Fb) ≤ Kb :=
    sup_le (Subgroup.zpowers_le.mpr hy₁K) (sup_le (Subgroup.zpowers_le.mpr hy₂K) hFK)
  have hK := (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 hsup).trans
    (h.pRank_barM_normalizer_le h3 (by decide))
  have r1 := hrk1 y₁ hy₁3 hy₁1
  have r2 := hrk1 y₂ hy₂3 hy₂1
  omega

end CFSG.AGLEmbeddingD2.McLaughlin

module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

open CFSG.Open

theorem eq_one_or_of_mem_zpowers_three {G : Type*} [Group G] {z g : G} (hz : z ^ 3 = 1)
    (hg : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z ∨ g = z ^ 2 := by
  obtain ⟨k, rfl⟩ := hg
  change z ^ k = 1 ∨ z ^ k = z ∨ z ^ k = z ^ 2
  have h3 : z ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hz
  have e : z ^ k = z ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rw [e]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left; simp
  · right; left; simp
  · right; right; rw [zpow_ofNat]

theorem le_pRank_three_center_quotient {G : Type*} [Group G] [Finite G] {n : ℕ}
    (Z A : Fin n → G) (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) :
    n ≤ pRank 3 (⊤ : Subgroup (G ⧸ Subgroup.center G)) := by
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
  let ϕ : ∀ i, Subgroup.zpowers (Z i) →* G ⧸ Subgroup.center G := fun i =>
    (QuotientGroup.mk' (Subgroup.center G)).comp (Subgroup.zpowers (Z i)).subtype
  have hϕcomm : Pairwise fun i j => ∀ (x : Subgroup.zpowers (Z i)) (y : Subgroup.zpowers (Z j)),
      Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change Commute (QuotientGroup.mk' _ (x : G)) (QuotientGroup.mk' _ (y : G))
    rw [← ha, ← hb]
    exact ((hZZ i j hij).zpow_zpow a b).map _
  have hcenter : ∀ i, ∀ g : G, g ∈ Subgroup.center G → Commute g (A i) := fun i g hg =>
    (Subgroup.mem_center_iff.1 hg (A i)).symm
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change QuotientGroup.mk' _ (x : G) = 1 at hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (key i _ x.2 (hcenter i _ hx)))
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), (ϕ j).range) ≤
        (Subgroup.centralizer {A i}).map (QuotientGroup.mk' (Subgroup.center G)) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hcent i j (Ne.symm hj) y.2, rfl⟩
    obtain ⟨r, hr, hrx⟩ := hle hg
    change QuotientGroup.mk' _ r = QuotientGroup.mk' _ (x : G) at hrx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrx
    have hxr : (x : G) = r * (r⁻¹ * x) := by group
    have hc : Commute (x : G) (A i) := by
      rw [hxr]
      have hrc : Commute r (A i) := (Subgroup.mem_centralizer_iff.1 hr (A i) rfl).symm
      exact hrc.mul_left (hcenter i _ hrx)
    have := key i _ x.2 hc
    change QuotientGroup.mk' _ (x : G) ∈ (⊥ : Subgroup (G ⧸ Subgroup.center G))
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

end CFSG.SectionRank

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2U5Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I163
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwARigid
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs117

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


section Count

variable {G : Type} [Group G] [Finite G]

theorem rk2_card_le_mul_inf {J B : Subgroup G} {x : G} {q : ℕ}
    (hBJ : B ≤ J ⊔ Subgroup.zpowers x) (hx : x ∈ Subgroup.centralizer (J : Set G))
    (hxq : Nat.card (Subgroup.zpowers x) ≤ q) : Nat.card B ≤ q * Nat.card ↥(J ⊓ B) := by
  have hC : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hx)
  have hJC : J ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer hC
  have h1 := card_sup_mul_card_inf_of_le_normalizer (hBJ.trans hJC)
  have h2 := card_sup_mul_card_inf_of_le_normalizer hC
  have h3 : Nat.card ↥(J ⊔ B) ≤ Nat.card ↥(J ⊔ Subgroup.zpowers x) :=
    Subgroup.card_le_of_le (sup_le le_sup_left hBJ)
  have h4 : Nat.card ↥(J ⊔ Subgroup.zpowers x) ≤ Nat.card J * Nat.card (Subgroup.zpowers x) := by
    rw [← h2]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have h5 : Nat.card J * Nat.card B ≤ Nat.card J * (q * Nat.card ↥(J ⊓ B)) := by
    rw [← h1]
    calc Nat.card ↥(J ⊔ B) * Nat.card ↥(J ⊓ B)
        ≤ (Nat.card J * q) * Nat.card ↥(J ⊓ B) :=
          Nat.mul_le_mul_right _ (h3.trans (h4.trans (Nat.mul_le_mul_left _ hxq)))
      _ = Nat.card J * (q * Nat.card ↥(J ⊓ B)) := by ring
  exact Nat.le_of_mul_le_mul_left h5 hJpos

theorem rk2_le_pRank_top_of_le {J A : Subgroup G} {q j : ℕ} (hq : q.Prime) (hAJ : A ≤ J)
    (hA : IsElemAbelian q A) (hcard : Nat.card A = q ^ j) :
    j ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥J) :=
  CFSG.SectionRank.le_pRank_of_injective hq.one_lt
    (fun a b => Subtype.ext (isElemAbelian_commute hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) hcard (Subgroup.inclusion hAJ)
    (Subgroup.inclusion_injective hAJ) (H := ⊤) le_top

end Count


theorem u5CaseAt_holds (G : Type) [Group G] [Finite G] : U5CaseAt G := by
  intro p q K B' x' J hC he4 n hn hJ
  have hq := hC.prime
  have hq2 := hC.odd
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd : q ∣ 2 ^ n + 1 := by
    rcases hC.seven with h7 | h7
    ·
      have hJcomm : ∀ j ∈ J, x' * j = j * x' := fun j hj =>
        Subgroup.mem_centralizer_iff.1 (hC.comp.1.1 hj).2 x' (Set.mem_singleton _)
      have hxJ : x' ∈ Subgroup.centralizer (J : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun j hj => (hJcomm j hj).symm
      have hxq : x' ^ q = 1 := hC.elem.2 x' hC.mem
      have hxcard : Nat.card (Subgroup.zpowers x') = q := by
        rw [Nat.card_zpowers, orderOf_eq_prime hxq hC.ne_one]
      have hcard := rk2_card_le_mul_inf h7 hxJ hxcard.le
      rw [hC.rank_B, he4] at hcard
      have hA : IsElemAbelian q (J ⊓ B') := isElemAbelian_mono hC.elem inf_le_right
      obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hq hA
      have hj3 : 3 ≤ j := by
        rw [hj] at hcard
        have h1 : q ^ 4 ≤ q ^ (j + 1) := hcard.trans (pow_succ' q j).symm.le
        have := (Nat.pow_le_pow_iff_right hq.one_lt).1 h1
        omega
      have hrank := rk2_le_pRank_top_of_le hq (inf_le_left : J ⊓ B' ≤ J) hA hj
      by_contra hqQ
      have hle := rk2_twA_pRank_le (X := ↥J) (ℓ := 4) (n := n) hJ rfl hq hq2 hqQ
      have : (4 + 1) / 2 = 2 := by norm_num
      omega
    ·
      have hrankK : GLATwoLocalRank q ↥K = 4 := by rw [hC.rank_K, he4]
      have h4 : 4 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥K) := hrankK ▸ rk2_twoLocal_le_pRank hq.one_lt
      have hq5 : q ∣ 2 ^ 2 + 1 := by
        by_contra hqQ
        have hle := rk2_twA_pRank_le (X := ↥K) (ℓ := 5) (n := 2) h7 rfl hq hq2 hqQ
        have : (5 + 1) / 2 = 3 := by norm_num
        omega
      obtain ⟨labJ, hlabJ, hshape⟩ := hC.shape ⟨.twA, 5, 2⟩ h7
      unfold JShape at hshape
      simp at hshape
      obtain ⟨hn2, hsh⟩ := hshape
      have htJ : labJ.tag = .twA := by
        rcases hsh with h | h
        · exact h.2.1
        · exact h.2.1
      have hlab := rk2_twA_rigid hlabJ hJ htJ rfl (by norm_num)
      subst hlab
      have hn2' : n = 2 := hn2
      subst hn2'
      exact hq5
  exact ⟨hqdvd, fun K₀ _ _ hK₀ => rk2_twA4_family hq hq2 hqdvd hK₀⟩

end CFSG.LocalAnalysis.GLTheoremA

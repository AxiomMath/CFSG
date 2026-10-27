module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem prop32 {p : ℕ} (hKM : KMUsedAt) (hDih : DihedralUsed) (hLB : LBalanceAt G p)
    (hc : S3Ctx G p) {B : Subgroup G} (hB : GLAIsBmax p B) :
    ∃ (x : G) (L : Subgroup G), IsSTriple p B x L := by
  by_contra hnot
  push_neg at hnot
  have hp := hc.prime
  have hnc : ∀ (x : G) (L : Subgroup G), IsEssential p B x →
      ¬ GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := fun x L hx hL =>
    hnot x L ⟨hB, hx, hL⟩
  have hS := Star3.of_noComp hc hB hnc
  obtain ⟨E, hEB, hEcard, hE⟩ := lemma35 hKM hDih hc hS
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hB.2.1]
    exact Nat.pow_le_pow_right hp.pos hc.rank_ge
  have hE2 : p ^ 2 ≤ Nat.card E := by
    by_contra h
    push_neg at h
    have h1 : Nat.card E * p ^ 2 < p ^ 2 * p ^ 2 :=
      Nat.mul_lt_mul_of_pos_right h (pow_pos hp.pos 2)
    have h2 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
    omega
  have hEel : IsElemAbelian p E := isElemAbelian_mono hB.1 hEB
  have hEncyc : ¬ IsCyclic E := S3.not_isCyclic_of_card hp hEel hE2
  obtain ⟨N, hN, hBN⟩ := GLAIsBmax.exists_maxTwoLocal hB
  obtain ⟨E₀, hE₀E, hE₀card, hE₀ess, -⟩ := hc.lemma31 B E N hB hEB hEncyc hN hBN
  have hE₀ne : ∃ x ∈ E₀, x ≠ 1 := by
    by_contra h
    push_neg at h
    have hbot : E₀ = ⊥ := Subgroup.eq_bot_iff_forall _ |>.2 h
    rw [hbot, Subgroup.card_bot] at hE₀card
    have : p ^ 2 ≤ p := by omega
    have h3 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨x, hxE₀, hx1⟩ := hE₀ne
  have hxE : x ∈ E := hE₀E hxE₀
  have hxess := hE₀ess x hxE₀ hx1
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := by
    have := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper
      (E := Subgroup.zpowers x) (by rwa [Ne, Subgroup.zpowers_eq_bot])
    rwa [S3.centralizer_zpowers] at this
  have hEX : E ≤ Subgroup.centralizer ({x} : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hEel he hxE
  have hbal := hLB _ E hXK hEX (isPGroup_of_isElemAbelian hEel)
  have hinf : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (E : Set G) =
      Subgroup.centralizer (E : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxE))
  rw [hinf] at hbal
  have hne : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) ≠ ⊥ := fun h =>
    hE (le_bot_iff.1 (h ▸ hbal))
  obtain ⟨L, hL⟩ := (S3.glaPLayer_ne_bot_iff hp).1 hne
  exact hnot x L ⟨hB, hxess, hL⟩

end CFSG.LocalAnalysis.GLTheoremA

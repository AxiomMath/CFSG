module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

private theorem exists_qElement_not_central_barM {M L : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hL : IsTwoPrimeComponent M L)
    (hsimple : IsSimpleGroup (↥L ⧸ pCore 2 ↥L))
    (hdvd : q ∣ Nat.card (↥L ⧸ pCore 2 ↥L)) :
    ∃ y : ↥M ⧸ CFSG.pCore 2 ↥M, y ∈ barM M L ∧
      IsPGroup q (Subgroup.zpowers y) ∧
      ∃ l ∈ barM M L, y * l ≠ l * y := by
  classical
  let Q := ↥L ⧸ pCore 2 ↥L
  have hsimpleQ : IsSimpleGroup Q := hsimple
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
  have hperfQ : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hnt : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd Nat.card_pos hdvd)
  have hnonab : ¬ IsMulCommutative Q := by
    intro hcomm
    have hsolvQ : Group.IsSolvable Q := Group.isSolvable_of_comm hcomm.is_comm.comm
    have hsubQ : Subsingleton Q :=
      CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hsubQ
  have hcenterQ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnonab
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hL.le hL.inf_twoCore
  have hcenterB : Subgroup.center ↥(barM M L) = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hcenterQ, Subgroup.map_bot] at h
    exact h.symm
  have hdvdB : q ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
    have hcard : Nat.card (↥(barM M L)) = Nat.card Q := Nat.card_congr e.toEquiv.symm
    rw [hcenterB, Nat.card_congr (QuotientGroup.quotientBot (G := ↥(barM M L))).toEquiv,
      hcard]
    exact hdvd
  exact CFSG.AGLEmbedding.exists_qElement_not_central hq hdvdB

theorem ncard_le_pRank_jSub {M H : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsimple : ∀ L ∈ weakBlockSet M H, IsSimpleGroup (↥L ⧸ pCore 2 ↥L))
    (hdvd : ∀ L ∈ weakBlockSet M H, q ∣ Nat.card (↥L ⧸ pCore 2 ↥L)) :
    (weakBlockSet M H).ncard ≤ CFSG.Open.pRank q (jSub M H) := by
  classical
  rw [← Nat.card_coe_set_eq]
  let L : ↥(weakBlockSet M H) → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    fun i => barM M (i : Subgroup G)
  have hcomp : ∀ i, IsComponentOf (L i) ⊤ :=
    fun i => i.2.toIsTwoPrimeComponent.component
  have hinj : Function.Injective L := by
    intro i j hij
    exact Subtype.ext ((i.2.toIsTwoPrimeComponent).eq_of_barM_eq
      j.2.toIsTwoPrimeComponent hij)
  have hex : ∀ i : ↥(weakBlockSet M H),
      ∃ y : ↥M ⧸ CFSG.pCore 2 ↥M, y ∈ L i ∧
        IsPGroup q (Subgroup.zpowers y) ∧
        ∃ l ∈ L i, y * l ≠ l * y := by
    rintro ⟨L₀, hL₀⟩
    exact exists_qElement_not_central_barM hq hL₀.toIsTwoPrimeComponent
      (hsimple L₀ hL₀) (hdvd L₀ hL₀)
  choose y hy using hex
  have hyL : ∀ i, y i ∈ L i := fun i => (hy i).1
  have hyq : ∀ i, IsPGroup q (Subgroup.zpowers (y i)) := fun i => (hy i).2.1
  have hyZ : ∀ i, ∃ l ∈ L i, y i * l ≠ l * y i := fun i => (hy i).2.2
  have hyA : ∀ i, y i ∈ barM M (jSub M H) :=
    fun i => barM_mono (le_jSub i.2) (hyL i)
  have hmain : Nat.card ↥(weakBlockSet M H) ≤
      CFSG.Open.pRank q (barM M (jSub M H)) :=
    CFSG.AGLEmbedding.le_pRank_of_components hq L hcomp hinj
      (barM M (jSub M H)) y hyA hyL hyq hyZ
  exact hmain.trans (CFSG.AGLEmbedding.pRank_barM_le hq hq2 M (jSub M H) (jSub_le M H))

private theorem three_dvd_card_of_isL3TwoPow_of_odd {X : Type} [Group X] {n : ℕ}
    (hn : Odd n) (hX : IsL3TwoPow n X) : 3 ∣ Nat.card X := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  unfold IsL3TwoPow CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPSLType at hX
  obtain ⟨e⟩ := hX
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hmod : 2 ^ n % 3 = 2 := CFSG.two_pow_mod_three_of_odd hn
  have hnot : ¬ 3 ∣ 2 ^ n - 1 := by
    intro h
    have h0 : (2 ^ n - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    have hrepr : 2 ^ n = 3 * (2 ^ n / 3) + 2 := by
      have h := Nat.div_add_mod (2 ^ n) 3
      rw [hmod] at h
      omega
    have h1 : 2 ^ n - 1 = 3 * (2 ^ n / 3) + 1 := by omega
    rw [h1, Nat.mul_add_mod_self_left] at h0
    norm_num at h0
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot)
  have hcard := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear
    (GaloisField 2 n) 3 (by norm_num)
  rw [Nat.card_congr e.toEquiv, hcard, hF, hg, Nat.div_one]
  rw [show 3 * (3 - 1) / 2 = 3 by norm_num]
  simp only [Finset.prod_Icc_succ_top (by norm_num : 1 + 1 ≤ 3), Finset.Icc_self,
    Finset.prod_singleton]
  have hdvd : 3 ∣ (2 ^ n) ^ 2 - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by
      rw [Nat.pow_mod, hmod]))
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hdvd _) _

theorem hr3_of_hL3 {M H : Subgroup G}
    (hL3 : ∀ L ∈ weakBlockSet M H, ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H) := by
  refine ncard_le_pRank_jSub (q := 3) Nat.prime_three (by norm_num) ?_ ?_
  · intro L hL
    obtain ⟨n, -, hL3n⟩ := hL3 L hL
    exact hL3n.isSimpleGroup
  · intro L hL
    obtain ⟨n, hn, hL3n⟩ := hL3 L hL
    exact three_dvd_card_of_isL3TwoPow_of_odd hn hL3n

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end

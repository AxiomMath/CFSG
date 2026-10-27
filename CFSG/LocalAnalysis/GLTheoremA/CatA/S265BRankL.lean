module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LinUni
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42STorus
import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRank
import CFSG.HardMathSupport.Timmesfeld.Proving.TwoLocalAttain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BRank

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem lieModel_of_tyUnTwo {S : Type} [Group S] {n : ℕ} (h : catalogIs S (tyUnTwo n)) :
    CFSG.Models.LieModel S .PSU n 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      obtain ⟨hr, h2⟩ : r + 1 = n ∧ q.card = 2 := hi
      obtain ⟨h1, h1'⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
        (h2.trans (by norm_num))
      have hm := lieModel_twistedA' r q hv e
      rwa [h1, h1', hr] at hm
    | _ => exact hi.elim
  | _ => exact hi.elim

private theorem pRank_le_of_card_le {G : Type} [Group G] [Finite G] (H : Subgroup G) {t : ℕ}
    (h : Nat.card H ≤ 3 ^ t) : CFSG.Open.pRank 3 H ≤ t :=
  CFSG.SectionRank.pRank_le (by norm_num) fun _ hE _ => (Subgroup.card_le_of_le hE).trans h

private theorem twoLocal_of_pos {L : Type} [Group L] [Finite L] (h : 0 < GLATwoLocalRank 3 L) :
    S8.L84.I1430TwoLocal L (GLATwoLocalRank 3 L) := by
  have hT : ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T := by
    by_contra hne
    unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank at h
    have he : {k | ∃ H : Subgroup L, IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun k hk => by
        obtain ⟨_, ⟨P, hP, hP2, _⟩, _⟩ := hk
        exact hne ⟨P, hP, hP2⟩
    rw [he] at h
    simp at h
  obtain ⟨T, hT0, hT2, E, hEN, hE, hEc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_twoLocal_attaining_GLATwoLocalRank
      Nat.prime_three hT
  exact ⟨T, E, hT0, hT2, hEN, hE, hEc⟩

private theorem le_twoLocalRank_of_simple {L : Type} [Group L] [Finite L] {n : ℕ} (hn5 : 5 ≤ n)
    {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    (e : L ≃* StatedProj (StatedSU n (2 ^ 1) K₀)) :
    n - 3 ≤ GLATwoLocalRank 3 L ∧ (¬ 3 ∣ n → n - 2 ≤ GLATwoLocalRank 3 L) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K₀ :=
    ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
  haveI : CharP K₀ 2 := hU.charP
  have key : ∀ k, k + 2 < n → (k + 3 < n ∨ ¬ 3 ∣ n) → k + 1 ≤ GLATwoLocalRank 3 L := by
    intro k hk hc
    have hloc := CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := k) (n := n)
      Nat.prime_three (by norm_num) hk hc
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three] at hloc
    exact hloc
  exact ⟨by have := key (n - 4) (by omega) (Or.inl (by omega)); omega,
    fun h3 => by have := key (n - 3) (by omega) (Or.inr h3); omega⟩

private theorem le_twoLocalRank_of_injective {L : Type} [Group L] [Finite L] {n : ℕ}
    (hn5 : 5 ≤ n) {K₀ : Type} [Field K₀] [Finite K₀] (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    {α : StatedSU n (2 ^ 1) K₀ →* L} (hα : Function.Injective α) :
    n - 2 ≤ GLATwoLocalRank 3 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K₀ :=
    ⟨Nat.prime_two, le_rfl, by rw [hK₀]; norm_num⟩
  haveI : CharP K₀ 2 := hU.charP
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := K₀ˣ) 3
    (by norm_num [Nat.card_units, hK₀])
  have h33 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  obtain ⟨E, t, k, hk, hk2, hcomm, hpow, hEt, ht2, htc, hdetE, hdett, hunit⟩ :=
    YS04G.exists_torus (F := K₀) (n := n) (by omega) Nat.prime_three hω
  obtain ⟨hunitE, hunitt⟩ := hunit (2 ^ 1) (by norm_num)
    (orderOf_dvd_iff_pow_eq_one.1 (hω ▸ h33)) (neg_one_pow_char_pow K₀ (p := 2) (n := 1))
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK₀ (n := n) (by omega)).1
  have hmem : ∀ a : GL (Fin n) K₀, (a : Matrix (Fin n) (Fin n) K₀).det = 1 →
      ((a : Matrix (Fin n) (Fin n) K₀).map (· ^ 2 ^ 1)).transpose *
        (a : Matrix (Fin n) (Fin n) K₀) = 1 → a ∈ (StatedSU n (2 ^ 1) K₀).subtype.range :=
      fun a h1 h2 => by
    rw [Subgroup.range_subtype, ← SetLike.mem_coe, hset]
    exact ⟨h1, h2⟩
  obtain ⟨E', t', ht', hk', hE', hEt', ht2'⟩ := YS04G.transfer_torus _
    (StatedSU n (2 ^ 1) K₀).subtype_injective E (fun a ha => hmem a (hdetE a ha) (hunitE a ha))
    t (hmem t hdett hunitt) hk hcomm hpow hEt ht2
  have hαt : α t' ≠ 1 := fun h => htc (by
    rw [← ht', hα (h.trans (map_one α).symm), map_one]
    exact Subgroup.one_mem _)
  have h := YS04G.rank_le_of_hom Nat.prime_three α hE' hk' ht2' hαt hEt' (c := 0)
    (le_of_eq (by rw [(MonoidHom.ker_eq_bot_iff α).2 hα, inf_bot_eq, Subgroup.card_bot, pow_zero]))
  omega


private theorem center_of_cover {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (hZ : IsPGroup 3 (Subgroup.center L)) {n : ℕ} (hn5 : 5 ≤ n) {K₀ : Type} [Field K₀]
    (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (2 ^ 1) K₀)) :
    Nat.card (Subgroup.center L) ∣ Nat.gcd n 3 ∧ (Nat.card (Subgroup.center L) = 3 →
      ∃ α : StatedSU n (2 ^ 1) K₀ →* L, Function.Injective α) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect L := Group.isPerfect_def.2 hL.1
  have hker := CFSG.LieType.Steinberg.ker_comp_mk' (Subgroup.center L) e
  have hmq : (n, 2 ^ 1) ≠ (3, 2) := fun h => by
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hs := e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ
  have hd := CFSG.SeitzReduction.SeitzQ2.card_ker_dvd_psu hK₀ (by omega) hmq
    (η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) hs hker.le
    (by rw [hker, hk]; exact Odd.pow (by decide))
  rw [hker] at hd
  refine ⟨hd, fun h3 => ?_⟩
  obtain ⟨α, -, hαs, -⟩ := CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_psu hK₀ (by omega)
    hmq (η := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) hs hker.le
    (by rw [hker, h3]; decide)
  refine ⟨α, (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.card_eq_one.1 ?_)⟩
  rw [h3] at hd
  set N := (StatedScalars (Fin n) K₀).subgroupOf (StatedSU n (2 ^ 1) K₀)
  have hN : Nat.card N = 3 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK₀ (n := n) (by omega)).2.2]
    exact Nat.gcd_eq_right (hd.trans (Nat.gcd_dvd_left n 3))
  have hP : Nat.card (L ⧸ Subgroup.center L) = Nat.card (↥(StatedSU n (2 ^ 1) K₀) ⧸ N) :=
    Nat.card_congr e.toEquiv
  have hSU : Nat.card (StatedSU n (2 ^ 1) K₀) = Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hN,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L), h3, hP]
  have h1 := Subgroup.card_ker_mul_card_range α
  rw [MonoidHom.range_eq_top.2 hαs, Subgroup.card_top, hSU] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (one_mul _).symm)

theorem exists_twoLocal_of_cover {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZ : IsPGroup 3 (Subgroup.center L)) {n : ℕ} (hn5 : 5 ≤ n)
    (hcat : catalogIs (L ⧸ Subgroup.center L) (tyUnTwo n)) :
    ∃ r, S8.L84.I1430TwoLocal L r ∧ n + CFSG.Open.pRank 3 (Subgroup.center L) ≤ r + 3 ∧
      (¬ 3 ∣ n → n + CFSG.Open.pRank 3 (Subgroup.center L) ≤ r + 2) := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := (lieModel_of_tyUnTwo hcat).statedClassicalModel (by decide)
  obtain ⟨hd, hinj⟩ := center_of_cover hL hZ hn5 hK₀ e
  rcases (Nat.dvd_prime Nat.prime_three).1 (hd.trans (Nat.gcd_dvd_right n 3)) with h1 | h3
  · have hbot : Subgroup.center L = ⊥ := Subgroup.card_eq_one.1 h1
    obtain ⟨hr1, hr2⟩ := le_twoLocalRank_of_simple hn5 hK₀
      (((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans e)
    have h0 := pRank_le_of_card_le (t := 0) (Subgroup.center L) (h1.le.trans (by norm_num))
    exact ⟨_, twoLocal_of_pos (by omega), by omega, fun h3 => by have := hr2 h3; omega⟩
  · rw [h3] at hd
    have hn3 : 3 ∣ n := hd.trans (Nat.gcd_dvd_left n 3)
    obtain ⟨α, hα⟩ := hinj h3
    have hr := le_twoLocalRank_of_injective hn5 hK₀ hα
    have h0 := pRank_le_of_card_le (t := 1) (Subgroup.center L) (h3.le.trans (by norm_num))
    exact ⟨_, twoLocal_of_pos (by omega), by omega, fun h => absurd hn3 h⟩

theorem exists_elem_of_cover {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) (hZ : IsPGroup 3 (Subgroup.center L)) {n : ℕ} (hn5 : 5 ≤ n)
    (hn6 : n ≤ 6) (hcat : catalogIs (L ⧸ Subgroup.center L) (tyUnTwo n)) :
    ∃ Eb : Subgroup L, IsElemAbelian 3 Eb ∧ 3 ^ 4 * Nat.card (Subgroup.center L) ≤ Nat.card Eb := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := (lieModel_of_tyUnTwo hcat).statedClassicalModel (by decide)
  obtain ⟨hd, hinj⟩ := center_of_cover hL hZ hn5 hK₀ e
  rcases (Nat.dvd_prime Nat.prime_three).1 (hd.trans (Nat.gcd_dvd_right n 3)) with h1 | h3
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hr := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K₀) (p := 2)
      (f := 1) (n := n) (r := 3) Nat.prime_two (by omega) (by norm_num)
      (H := StatedSU n (2 ^ 1) K₀) (Or.inr ⟨hK₀, rfl, by norm_num⟩)
      ((StatedScalars (Fin n) K₀).subgroupOf (StatedSU n (2 ^ 1) K₀)) le_rfl
    have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (2 ^ 1) K₀))) := by
      rcases (by omega : n = 5 ∨ n = 6) with rfl | rfl
      · refine hr.2 ?_
        rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK₀ (n := 5) (by norm_num)).2.2]
        decide
      · exact hr.1
    obtain ⟨Eb, -, hEb, hcard⟩ :=
      CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup L)
    refine ⟨Eb, hEb, ?_⟩
    rw [h1, mul_one, hcard,
      CFSG.ClassicalGroups.SpecialLinear.pRank_top_eq_of_mulEquiv_center_quotient Nat.prime_three e
        (by rw [h1]; norm_num)]
    exact Nat.pow_le_pow_right (by norm_num) h4
  · rw [h3] at hd
    have hn : n = 6 := by have := hd.trans (Nat.gcd_dvd_left n 3); omega
    subst hn
    obtain ⟨α, hα⟩ := hinj h3
    have hK4 : Nat.card K₀ = 4 := hK₀.trans (by norm_num)
    refine ⟨(CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S.W6 hK4).map α,
      (CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S.W6_isElemAbelian hK4).map α, ?_⟩
    rw [Subgroup.card_map_of_injective hα, CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S.card_W6 hK4,
      h3]
    norm_num

end CFSG.LocalAnalysis.GLTheoremA.S265.BRank

end

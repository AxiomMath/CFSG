module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs117
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Rank
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U6Mult
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcEven
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

theorem u6_twoLocal_le_pRank_top {G : Type} [Group G] [Finite G] :
    CFSG.Open.twoLocalPrimeRank 3 G ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  unfold CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, -, rfl⟩
  exact u6_pRank_le (fun _ ⟨E, _, hel, hc⟩ => ⟨E, le_top, hel, hc⟩)
theorem u6_core {L K : Type} [Group L] [Group K] [Finite L] [Finite K]
    (hLp : commutator L = ⊤) (hKp : commutator K = ⊤)
    (e : L ⧸ Subgroup.center L ≃* K ⧸ Subgroup.center K)
    (hX2 : 2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (K ⧸ Subgroup.center K))
    {m : ℕ} (hm : m = 1 ∨ m = 4)
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) = 3 * m)
    (hcX : commutator (K ⧸ Subgroup.center K) = ⊤)
    (h3L : 3 ∣ Nat.card (Subgroup.center L)) (h3K : 3 ∣ Nat.card (Subgroup.center K)) :
    CFSG.Open.GLATwoLocalRank 3 L + 1 + CFSG.Open.pRank 3 (Subgroup.center K) ≤
      CFSG.Open.GLATwoLocalRank 3 K + CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) := ⟨hcX⟩
  haveI : Group.IsPerfect L := ⟨hLp⟩
  haveI : Group.IsPerfect K := ⟨hKp⟩
  let qL : L →* K ⧸ Subgroup.center K := centralQuotientMap e
  let qK : K →* K ⧸ Subgroup.center K := centralQuotientMap (MulEquiv.refl _)
  have hqL : Function.Surjective qL := centralQuotientMap_surjective e
  have hqK : Function.Surjective qK := centralQuotientMap_surjective (MulEquiv.refl _)
  have hkL : qL.ker = Subgroup.center L := centralQuotientMap_ker e
  have hkK : qK.ker = Subgroup.center K := centralQuotientMap_ker (MulEquiv.refl _)
  have hM' : Nat.card (hopfMultiplier (K ⧸ Subgroup.center K)) = 3 * m := by
    rw [← hM]; exact (Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv).symm
  have hm' : ¬ 3 ∣ m := by rcases hm with rfl | rfl <;> norm_num
  have hle := u6_pRank_le_of_covers qL hqL hkL qK hqK hkK hM' hm' (hkL ▸ h3L) h3K
  have hd : Nat.card (Subgroup.center K) ∣ 3 * m := by
    rw [← hM']; exact Dvd.intro _ (u6_card_mul_ker qK hqK hkK)
  have h12 : Nat.card (Subgroup.center K) ∣ 12 := by
    rcases hm with rfl | rfl
    · have h := hd
      norm_num at h
      exact h.trans (by norm_num)
    · norm_num at hd
      exact hd
  have hpZ : CFSG.Open.pRank 3 (Subgroup.center K) = 1 :=
    u6_pRank_center h3K (fun h9 => by have := h9.trans h12; norm_num at this)
  obtain ⟨P, E, j, hP, hP2, hE, hEc, hj, hEN⟩ := u6_witness_of_two_le hX2
  have hK2 : 2 ≤ CFSG.Open.GLATwoLocalRank 3 K :=
    u6_two_le_of_cover qK hqK hkK h3K h12 hP hP2 hE hj hEc hEN
  have hL2 : CFSG.Open.GLATwoLocalRank 3 L ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) :=
    u6_twoLocal_le_pRank_top
  omega
section Certs

theorem u6_two_le_localRank_PSU {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.LieModel X .PSU 6 2 n) :
    2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  rcases hX with ⟨-, hX⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := CFSG.SectionRank.charP_of_natCard_eq_pow (p := 2) (f := 2 * n) (by
      rw [hK, ← pow_mul, mul_comm])
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
      ⟨Nat.prime_two, hn.pos, by rw [hK, ← pow_mul, mul_comm]⟩
    have h := CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (r := 3) (k := 1)
      (n := 6) Nat.prime_three (u6_three_dvd_two_pow_add_one hn) (by norm_num)
      (Or.inl (by norm_num))
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
    exact h
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
  · exact absurd h0 (by norm_num)
theorem u6_two_le_localRank_twE6 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 2 n) :
    2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 X := by
  rcases hX with ⟨hX, -⟩ | ⟨-, -, hX⟩ | ⟨-, hX, -⟩ | ⟨-, hX, -⟩
  · exact absurd hX (by decide)
  · have h := CFSG.SectionRank.QTK.three_le_localRank_of_twistedE6Model_two (f := n) hn.pos
      hX.2
    omega
  · exact absurd hX (by decide)
  · exact absurd hX (by decide)
theorem u6_marking_facts {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (h : CFSG.Assembly.LargeEvenMarking K fun lab' _ _ _ _ _ => lab' = lab) :
    commutator K = ⊤ ∧ 1 ≤ lab.n ∧ CFSG.Open.IsQuasisimple K ∧
      CFSG.StandardType.MarkedModel lab (K ⧸ Subgroup.center K) := by
  obtain ⟨hcomm, lab', hlam, R, _, I, F, θ, hs, -, ⟨rfl, hm⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.StandardType.Canonical.largeEvenMarking_markedModel h)
  haveI := hs
  exact ⟨hcomm, hlam.1, ⟨hcomm, θ.isSimpleGroup⟩,
    CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩
theorem u6_griess_of_PSU (X : Type) [Group X] {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.LieModel X .PSU 6 2 n) :
    commutator X = ⊤ ∧ ∃ m : ℕ, (m = 1 ∨ m = 4) ∧
      Nat.card (griessHopfMultiplier X) = 3 * m := by
  obtain ⟨hc, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X .PSU 6 2 n hX
  refine ⟨hc, if n = 1 then 4 else 1, ?_, ?_⟩
  · split_ifs <;> simp
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    change Nat.card (Multiplicative (ZMod (Nat.gcd 6 (2 ^ n + 1))) × Multiplicative (ZMod 1)) *
      Nat.card (Multiplicative (ZMod (exceptionalOrders .PSU 6 2 n).1) ×
        Multiplicative (ZMod (exceptionalOrders .PSU 6 2 n).2)) = _
    rw [Nat.card_prod, Nat.card_prod]
    simp only [u6_card_mult_zmod]
    rw [u6_gcd_six hn]
    by_cases h1 : n = 1
    · subst h1
      rw [u6_exc_PSU_one]
      norm_num
    · rw [u6_exc_PSU_ne h1]
      simp only [if_neg h1]
theorem u6_griess_of_twE6 (X : Type) [Group X] {n : ℕ} (hn : Odd n)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 2 n) :
    commutator X = ⊤ ∧ ∃ m : ℕ, (m = 1 ∨ m = 4) ∧
      Nat.card (griessHopfMultiplier X) = 3 * m := by
  obtain ⟨hc, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X .twistedE6 0 2 n hX
  refine ⟨hc, if n = 1 then 4 else 1, ?_, ?_⟩
  · split_ifs <;> simp
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    change Nat.card (Multiplicative (ZMod (Nat.gcd 3 (2 ^ n + 1))) × Multiplicative (ZMod 1)) *
      Nat.card (Multiplicative (ZMod (exceptionalOrders .twistedE6 0 2 n).1) ×
        Multiplicative (ZMod (exceptionalOrders .twistedE6 0 2 n).2)) = _
    rw [Nat.card_prod, Nat.card_prod]
    simp only [u6_card_mult_zmod]
    rw [u6_gcd_three hn]
    by_cases h1 : n = 1
    · subst h1
      rw [u6_exc_twE6_one]
      norm_num
    · rw [u6_exc_twE6_ne h1]
      simp only [if_neg h1]
theorem u6_iso_of_twE6 {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hX : CFSG.Blueprint.LieModel X .twistedE6 0 2 n) (hY : CFSG.Blueprint.LieModel Y .twistedE6 0 2 n) :
    Nonempty (X ≃* Y) := by
  rcases hX with ⟨hX, -⟩ | ⟨-, -, hX⟩ | ⟨-, hX, -⟩ | ⟨-, hX, -⟩
  · exact absurd hX (by decide)
  · rcases hY with ⟨hY, -⟩ | ⟨-, -, hY⟩ | ⟨-, hY, -⟩ | ⟨-, hY, -⟩
    · exact absurd hY (by decide)
    · exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique hX hY
    · exact absurd hY (by decide)
    · exact absurd hY (by decide)
  · exact absurd hX (by decide)
  · exact absurd hX (by decide)

theorem u6CaseAt_holds (G : Type) [Group G] [Finite G] : U6CaseAt G := by
  intro L lab hL hodd hty h3L K₀ _ _ hK h3K
  obtain ⟨hcL, -, -, hML⟩ := u6_marking_facts hL
  obtain ⟨hcK, -, -, hMK⟩ := u6_marking_facts hK
  rcases hty with ⟨ht, hr⟩ | ht
  · have hLM := u6_model_PSU ht hr hML
    have hKM := u6_model_PSU ht hr hMK
    obtain ⟨e⟩ := u6_iso_of_PSU hLM hKM
    obtain ⟨hcX, m, hm, hM⟩ := u6_griess_of_PSU _ hodd hKM
    exact u6_core hcL hcK e (u6_two_le_localRank_PSU hodd hKM) hm hM hcX h3L h3K
  · have hLM := u6_model_twE6 ht hML
    have hKM := u6_model_twE6 ht hMK
    obtain ⟨e⟩ := u6_iso_of_twE6 hLM hKM
    obtain ⟨hcX, m, hm, hM⟩ := u6_griess_of_twE6 _ hodd hKM
    exact u6_core hcL hcK e (u6_two_le_localRank_twE6 hodd hKM) hm hM hcX h3L h3K
end Certs

end CFSG.LocalAnalysis.GLTheoremA
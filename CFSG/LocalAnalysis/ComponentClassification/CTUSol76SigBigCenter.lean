module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigGammaCore
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem sylow_two_card_le_two_of_not_four_dvd {M : Type*} [Group M] [Finite M]
    (h : ¬ 4 ∣ Nat.card M) (S : Sylow 2 M) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 S.isPGroup'
  have hdvd : Nat.card S ∣ Nat.card M := S.toSubgroup.card_subgroup_dvd_card
  rw [hk] at hdvd ⊢
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · exact absurd ((pow_dvd_pow 2 (by omega : 2 ≤ k + 2)).trans hdvd) (by simpa using h)

theorem sylow_center_card_le_two_of_dvd_six {X : Type} [Group X]
    (hM : Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 6)
    {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (e : Nonempty ((L ⧸ center L) ≃* X)) (S : Sylow 2 (center L)) : Nat.card S ≤ 2 := by
  have hM0 : Nat.card (CFSG.Open.griessHopfMultiplier X) ≠ 0 := by
    rintro h0
    rw [h0] at hM
    norm_num at hM
  have : Finite (CFSG.Open.griessHopfMultiplier X) := Nat.finite_of_card_ne_zero hM0
  refine (CFSG.RankThree.PerfectCover.hopf_central_cover_consequences X).1
    (fun S' => sylow_two_card_le_two_of_not_four_dvd ?_ S') L hL e S
  exact fun h4 => absurd (h4.trans hM) (by norm_num)

theorem card_multiplicative_zmod_prod (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem card_sylow_center_eq_of_pPrimeCore {J : Type*} [Group J] [Finite J]
    (hO : pPrimeCore 2 J = ⊥) (P : Sylow 2 (center J)) : Nat.card P = Nat.card (center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (center J) := by
    intro g
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨k, ?_⟩
    set c : center J := g ^ (2 ^ k) with hc
    have hcm : orderOf c ∣ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [hc, ← pow_mul, ← hkm, pow_orderOf_eq_one]
    have hN : (zpowers (c : J)).Normal := ⟨fun x hx y => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      have hz : ((c : J) ^ i) ∈ center J := zpow_mem c.2 i
      rw [show y * (c : J) ^ i * y⁻¹ = (c : J) ^ i by
        rw [(Subgroup.mem_center_iff.mp hz y)]
        group]
      exact zpow_mem_zpowers _ i⟩
    have hodd : Nat.Coprime 2 (Nat.card (zpowers (c : J))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe]
      exact Nat.coprime_two_left.2 (hm.of_dvd_nat hcm)
    have hle : zpowers (c : J) ≤ pPrimeCore 2 J := le_sSup ⟨hN, hodd⟩
    rw [hO, le_bot_iff, zpowers_eq_bot] at hle
    exact Subtype.ext hle
  have htop : (⊤ : Subgroup (center J)) = P.toSubgroup := P.is_maximal' (hp.to_subgroup ⊤) le_top
  rw [← Subgroup.card_top (G := center J), htop]

theorem card_griess_of_lieModel
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hm : Blueprint.LieModel X t n p f) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X t n p f hm
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_multiplicative_zmod_prod,
    card_multiplicative_zmod_prod]

theorem card_griess_dvd_six_PSL_two
    {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel X .PSL 2 p f) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 6 := by
  obtain ⟨hp, hf, -⟩ := hm.1
  rw [card_griess_of_lieModel (.inl ⟨by decide, hm⟩),
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSL hp (by omega)]
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq4 : p ^ f ≠ 4 := fun h => by rw [h] at hq; exact absurd hq (by decide)
  have hg : (genericOrders .PSL 2 p f).1 * (genericOrders .PSL 2 p f).2 ∣ 2 := by
    simp only [genericOrders, mul_one]
    exact Nat.gcd_dvd_left 2 _
  have he : (CFSG.Open.griessPSLExceptional 2 (p ^ f)).1 *
      (CFSG.Open.griessPSLExceptional 2 (p ^ f)).2 ∣ 3 := by
    unfold CFSG.Open.griessPSLExceptional
    split_ifs <;> simp_all
  exact (Nat.mul_dvd_mul hg he).trans (by norm_num)

theorem card_griess_dvd_six_PSL_three
    {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : StatedClassicalModel X .PSL 3 p f) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 6 := by
  obtain ⟨hp, hf, -⟩ := hm.1
  rw [card_griess_of_lieModel (.inl ⟨by decide, hm⟩),
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSL hp (by omega)]
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq2 : p ^ f ≠ 2 := fun h => by rw [h] at hq; exact absurd hq (by decide)
  have hq4 : p ^ f ≠ 4 := fun h => by rw [h] at hq; exact absurd hq (by decide)
  have hg : (genericOrders .PSL 3 p f).1 * (genericOrders .PSL 3 p f).2 ∣ 3 := by
    simp only [genericOrders, mul_one]
    exact Nat.gcd_dvd_left 3 _
  have he : (CFSG.Open.griessPSLExceptional 3 (p ^ f)).1 *
      (CFSG.Open.griessPSLExceptional 3 (p ^ f)).2 = 1 := by
    unfold CFSG.Open.griessPSLExceptional
    split_ifs <;> simp_all
  rw [he, mul_one]
  exact hg.trans (by norm_num)

theorem card_griess_dvd_six_PSU_three
    {X : Type} [Group X] {p f : ℕ}
    (hpf : p ≠ 2 ∨ (p = 2 ∧ f = 2)) (hm : StatedClassicalModel X .PSU 3 p f) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 6 := by
  rw [card_griess_of_lieModel (.inl ⟨by decide, hm⟩)]
  have hg : (genericOrders .PSU 3 p f).1 * (genericOrders .PSU 3 p f).2 ∣ 3 := by
    simp only [genericOrders, mul_one]
    exact Nat.gcd_dvd_left 3 _
  have he : exceptionalOrders .PSU 3 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [he]
  exact (Nat.mul_dvd_mul hg (dvd_refl 1)).trans (by norm_num)

theorem card_griess_alternating_seven :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 7))) = 6 := by
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  have h := (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput 7 (by norm_num)).2
  simpa using h

theorem card_griess_M11 :
    Nat.card (CFSG.Open.griessHopfMultiplier ↥Blueprint.NativeSporadic.M11) = 1 := by
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M11

theorem quasisimpleBigCenterRankThree_holds
    : QuasisimpleBigCenterRankThree := by
  intro J _ _ hJ hO _ hZ4
  by_contra h3
  rw [not_le] at h3
  have hSs : IsSimpleGroup (J ⧸ center J) := hJ.2.1
  obtain ⟨a, b, hab⟩ := hJ.2.2
  have heven : Even (Nat.card (J ⧸ center J)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd) a b)
  have h2 : CFSG.Open.twoRank (J ⧸ center J) = 2 :=
    le_antisymm (by omega) (CFSG.Walter.two_le_twoRank _ ⟨a, b, hab⟩ heven)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (center J)) := inferInstance
  have hP4 : 4 ≤ Nat.card P := by rw [card_sylow_center_eq_of_pPrimeCore hO P]; exact hZ4
  have hP2 : Nat.card P ≤ 2 := by
    rcases CFSG.Milestones.lr_rank_two_isomorphism_types (J ⧸ center J) ⟨a, b, hab⟩ h2 with
      ⟨p, f, -, hp2, -, hm⟩ | ⟨p, f, -, hp2, -, hm⟩ | ⟨p, f, -, hp2, -, hm⟩ | hm | e | e
    · exact sylow_center_card_le_two_of_dvd_six (card_griess_dvd_six_PSL_two hp2 hm) hJ
        ⟨MulEquiv.refl _⟩ P
    · exact sylow_center_card_le_two_of_dvd_six (card_griess_dvd_six_PSL_three hp2 hm) hJ
        ⟨MulEquiv.refl _⟩ P
    · exact sylow_center_card_le_two_of_dvd_six (card_griess_dvd_six_PSU_three (.inl hp2) hm) hJ
        ⟨MulEquiv.refl _⟩ P
    · exact sylow_center_card_le_two_of_dvd_six
        (card_griess_dvd_six_PSU_three (.inr ⟨rfl, rfl⟩) hm) hJ ⟨MulEquiv.refl _⟩ P
    · exact sylow_center_card_le_two_of_dvd_six (by rw [card_griess_alternating_seven]) hJ e P
    · exact sylow_center_card_le_two_of_dvd_six (by rw [card_griess_M11]; norm_num) hJ
        (e.map fun e => e.trans (MulEquiv.subgroupCongr
          CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)) P
  omega


end CFSG.ComponentClassification.Sol76.Sig

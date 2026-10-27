module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psu

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.SectionRank
open CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def SU165EngineTwA : Prop :=
  ∀ (ℓ n p q : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
    Nat.card F = (2 ^ n) ^ 2 → 1 ≤ n → 2 ≤ ℓ → rk2Ord p n ≠ 2 →
    p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → q ∣ 2 ^ n + 1 →
    ∀ A : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F), IsElemAbelian p A →
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) ≤
        CFSG.Open.pRank p A →
      3 ≤ CFSG.Open.pRank p A →
      Concl165Avoid (StatedSU (ℓ + 1) (2 ^ n) F) p q A
        ((StatedScalars (Fin (ℓ + 1)) F).subgroupOf (StatedSU (ℓ + 1) (2 ^ n) F))

private theorem rk2Ord_three_one : rk2Ord 3 1 = 2 :=
  (rk2Ord_eq_two_iff (by norm_num) (by norm_num)).2 (by norm_num)

private theorem exceptionalOrders_PSU_eq_one_of_seven_le {N : ℕ} (hN : 7 ≤ N) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU N 2 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

private theorem card_center_statedSU_dvd_two_pow_add_one {N n : ℕ} {F : Type} [Field F]
    [Finite F] (hcard : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN3 : 3 ≤ N)
    (hnq : (N, 2 ^ n) ≠ (3, 2)) :
    Nat.card (Subgroup.center (StatedSU N (2 ^ n) F)) ∣ 2 ^ n + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (StatedSU N (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard hN3 hnq
  have hsimple : IsSimpleGroup (StatedProj (StatedSU N (2 ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hcard N hN3 hnq
  rw [(CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple).2]
  exact (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_scalars_statedSU_dvd
    (K := F) (f := n) (n := N) hcard (by omega)).2

section Certificate

theorem exists_mulEquiv_statedSU_quot_of_isLabel_of_one
    (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twA) (hn : lab.n = 1)
    (hN : 7 ≤ lab.rank + 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (C : Subgroup (StatedSU (lab.rank + 1) (2 ^ lab.n) F)) (_ : C.Normal),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧
      C ≤ Subgroup.center (StatedSU (lab.rank + 1) (2 ^ lab.n) F) ∧
      Nonempty (K ≃* (StatedSU (lab.rank + 1) (2 ^ lab.n) F ⧸ C)) := by
  classical
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at htag hn
  subst htag
  subst hn
  have hN' : 7 ≤ ℓ + 1 := hN
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (ℓ + 1) 2 1 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.statedClassicalModel (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hFcard
  have hperfK : Group.IsPerfect K := Group.isPerfect_def.mpr hQ.1
  have hℓ : 2 ≤ ℓ := hlab.2.1
  have hd3 : 3 ≤ ℓ + 1 := by omega
  have hne : (ℓ + 1, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h3 : ℓ + 1 = 3 := congrArg Prod.fst h
    omega
  have hperfSU : Group.IsPerfect (StatedSU (ℓ + 1) (2 ^ 1) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hd3 hne
  set D : Subgroup (StatedSU (ℓ + 1) (2 ^ 1) F) :=
    (StatedScalars (Fin (ℓ + 1)) F).subgroupOf (StatedSU (ℓ + 1) (2 ^ 1) F)
    with hDdef
  have hDcen : D ≤ Subgroup.center (StatedSU (ℓ + 1) (2 ^ 1) F) :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  let ρ : K →* StatedProj (StatedSU (ℓ + 1) (2 ^ 1) F) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (ℓ + 1) 2 1 = (1, 1) :=
    exceptionalOrders_PSU_eq_one_of_seven_le hN' 
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    have hdvd : Nat.card (Subgroup.center K) ∣ Nat.gcd (ℓ + 1) (2 ^ 1 + 1) :=
      CFSG.LocalAnalysis.GLTheoremA.rk2_card_center_dvd_twA hK hex
    have hq : Odd (2 ^ 1 + 1) := by norm_num
    exact Odd.of_dvd_nat hq (hdvd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨k, hMk⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.card_hopfMultiplier_psu_char_two hG
      (l := ℓ) (f := 1) (q := 2 ^ 1) rfl hFcard hM'.admissible
  obtain ⟨C, hCn, hCD, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_mulEquiv_quot_of_odd_center hperfSU hperfK D hDcen ρ
      hρ hρk hMk hodd
  exact ⟨F, hFld, hFin, inferInstance, C, hCn, hFcard, hCD.trans hDcen, ⟨e⟩⟩

private theorem not_dvd_two_pow_add_one_of_rk2Ord_ne_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : rk2Ord p n ≠ 2) : ¬ p ∣ 2 ^ n + 1 :=
  fun hd => h ((rk2Ord_eq_two_iff hp hp2).2 hd)
private theorem four_le_eM_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm0ne : rk2Ord p 1 ≠ 2) : 4 ≤ eM 2 p := by
  by_contra hlt
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < eM 2 p := by
    unfold eM
    refine orderOf_pos_iff.mpr ?_
    rw [isOfFinOrder_iff_pow_eq_one]
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h0)
    refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    exact ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr h2)
  have hle : eM 2 p ≤ 3 := by omega
  interval_cases h : eM 2 p
  · have hx : (-(2 : ZMod p)) ^ (eM 2 p) = 1 := pow_orderOf_eq_one _
    rw [h, pow_one] at hx
    have h2 : ((2 : ℕ) : ZMod p) = -1 := by linear_combination -hx
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by linear_combination h2
    have h3' : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3'
    exact hm0ne (by rw [hp3]; exact rk2Ord_three_one)
  · have hx : (-(2 : ZMod p)) ^ (eM 2 p) = 1 := pow_orderOf_eq_one _
    have hx4 : (-(2 : ZMod p)) ^ 2 = 1 := by simpa [h] using hx
    have h4 : ((4 : ℕ) : ZMod p) = 1 := by
      have := hx4
      ring_nf at this
      linear_combination this
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by linear_combination h4
    have h3' : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3'
    exact hm0ne (by rw [hp3]; exact rk2Ord_three_one)
  · have hx : (-(2 : ZMod p)) ^ (eM 2 p) = 1 := pow_orderOf_eq_one _
    have hx8 : (-(2 : ZMod p)) ^ 3 = 1 := by simpa [h] using hx
    have h8 : ((8 : ℕ) : ZMod p) = -1 := by
      have := hx8
      ring_nf at this
      linear_combination -this
    have h9 : ((9 : ℕ) : ZMod p) = 0 := by linear_combination h8
    have h9' : p ∣ 9 := (ZMod.natCast_eq_zero_iff 9 p).mp h9
    have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (by simpa using h9' : p ∣ 3 ^ 2)
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h3
    exact hm0ne (by rw [hp3]; exact rk2Ord_three_one)

private theorem dvd_two_pow_add_one_of_famTwA {K : Type} [Group K] [Finite K]
    {ℓ n q : ℕ} (hK : Rk2IsLabel K ⟨.twA, ℓ, n⟩) (hq : q.Prime) (hq2 : q ≠ 2)
    (h3 : 3 ≤ GLATwoLocalRank q K) (he : evenRank K = GLATwoLocalRank q K)
    (hm4K : 4 ≤ evenRank K) : q ∣ 2 ^ n + 1 := by
  obtain ⟨lab', hlab', hs⟩ :=
    rk2_split16_of_tables_holds hq hq2 (hasLabel_mono (fun _ _ => trivial) hK) h3 he.symm
  exact dvd_two_pow_add_one_of_hasLabel_of_exists_split16 hm4K hK
    ⟨lab', hlab', hs⟩ (Or.inl rfl)

private theorem twelve_le_rank_add_one_of_famTwA_one {K : Type} [Group K] [Finite K]
    {ℓ p : ℕ} (hK : Rk2IsLabel K ⟨.twA, ℓ, 1⟩) (hp : p.Prime) (hp2 : p ≠ 2)
    (hm0ne : rk2Ord p 1 ≠ 2) (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) :
    12 ≤ ℓ + 1 := by
  have hC' : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hprank : CFSG.Open.pRank p (⊤ : Subgroup K) =
      rk2Chev ⟨.twA, ℓ, 1⟩ p (Nat.card (Subgroup.center K)) := by
    refine rk2_pRank_eq_of_isLabel_classical hC' hK hp hp2 ?_ ?_ ?_ ?_ ?_ ?_
    · exact Or.inr (Or.inl rfl)
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by simp)
  have heM4 : 4 ≤ eM 2 p := four_le_eM_two hp hp2 hm0ne
  have hneM1 : eM 2 p ≠ 1 := by omega
  have hdiv : rk2Chev ⟨.twA, ℓ, 1⟩ p (Nat.card (Subgroup.center K)) =
      (ℓ + 1) / eM 2 p := by
    simp [rk2Chev, rkLin, hneM1]
  have h3lin : 3 ≤ (ℓ + 1) / eM 2 p := by
    rw [← hdiv, ← hprank]
    exact h3
  have hmul : 3 * eM 2 p ≤ ℓ + 1 :=
    (Nat.le_div_iff_mul_le (by omega)).1 h3lin
  omega

private theorem exists_statedSU_cover {K : Type} [Group K] [Finite K] {ℓ n : ℕ}
    (hK : Rk2IsLabel K ⟨.twA, ℓ, n⟩) (hn1 : 1 ≤ n) (hN12 : n = 1 → 12 ≤ ℓ + 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (C : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) (_ : C.Normal),
      Nat.card F = (2 ^ n) ^ 2 ∧
      C ≤ Subgroup.center (StatedSU (ℓ + 1) (2 ^ n) F) ∧
      Nonempty (K ≃* (StatedSU (ℓ + 1) (2 ^ n) F ⧸ C)) := by
  by_cases hn2 : 2 ≤ n
  · exact exists_mulEquiv_statedSU_quot_of_isLabel
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hK rfl hn2
  · have hn1' : n = 1 := by omega
    exact exists_mulEquiv_statedSU_quot_of_isLabel_of_one
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hK rfl hn1'
      (by have := hN12 hn1'; show 7 ≤ ℓ + 1; omega)

private theorem concl165Avoid_of_engine (hE : SU165EngineTwA) {ℓ n p q : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hFcard : Nat.card F = (2 ^ n) ^ 2) (hn1 : 1 ≤ n)
    (hl2 : 2 ≤ ℓ) (hm0ne : rk2Ord p n ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hqdiv : q ∣ 2 ^ n + 1)
    (C : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F))
    (hCcen : C ≤ Subgroup.center (StatedSU (ℓ + 1) (2 ^ n) F))
    (hnq : (ℓ + 1, 2 ^ n) ≠ (3, 2)) :
    ∀ Ã : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F), IsElemAbelian p Ã →
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) ≤
        CFSG.Open.pRank p Ã →
      3 ≤ CFSG.Open.pRank p Ã → Concl165Avoid (StatedSU (ℓ + 1) (2 ^ n) F) p q Ã C := by
  intro Ã hÃe hÃmax hÃ3
  obtain ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, hFZ⟩ :=
    hE ℓ n p q F hFcard hn1 hl2 hm0ne hp hp2 hq hq2 hqp hqdiv Ã hÃe hÃmax hÃ3
  refine ⟨D, E, F', J, hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3, ?_⟩
  have hperf : Group.IsPerfect (StatedSU (ℓ + 1) (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard (by omega) hnq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSU (ℓ + 1) (2 ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hFcard
      (ℓ + 1) (by omega) hnq
  have hcenter := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU hperf hsimple).2
  have hCscalar : C ≤ (StatedScalars (Fin (ℓ + 1)) F).subgroupOf
      (StatedSU (ℓ + 1) (2 ^ n) F) := by
    rw [← hcenter]
    exact hCcen
  exact le_bot_iff.mp ((inf_le_inf_left F' hCscalar).trans (le_of_eq hFZ))

private theorem pRank_eq_pRank_map_of_isPGroup {H K : Type} [Group H] [Finite H] [Group K]
    [Finite K] {p : ℕ} (hp : p.Prime) {π : H →* K} (hpk : ¬ p ∣ Nat.card π.ker)
    {R : Subgroup H} (hRp : IsPGroup p R) :
    CFSG.Open.pRank p R = CFSG.Open.pRank p (R.map π) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : ((x : H)) ∈ R ⊓ π.ker := ⟨x.2, hx⟩
    rw [CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hpk hRp,
      Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have htop : (⊤ : Subgroup R).map (π.comp R.subtype) = R.map π := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← htop, pRank_eq_pRank_top_subgroup R]
  exact (CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
    (π.comp R.subtype) hinj ⊤).symm

theorem i165On_famTwA_of_engine (hE : SU165EngineTwA) : I165On i165FamTwA := by
  intro K _ _ lab p q hK hP hp hp2 hq hq2 hqp hns hZ A hAe hSC h12 hmax hb he hm1 hm4
  obtain ⟨t, ℓ, n⟩ := lab
  obtain ⟨htag, hm0ne⟩ := hP
  subst htag
  have hm3 : 3 ≤ CFSG.Open.pRank p A := by omega
  have hm4K : 4 ≤ evenRank K := le_trans hm4 hm1
  have hqdiv : q ∣ 2 ^ n + 1 :=
    dvd_two_pow_add_one_of_famTwA hK hq hq2 (by omega) he hm4K
  have hpq1 : ¬ p ∣ 2 ^ n + 1 :=
    not_dvd_two_pow_add_one_of_rk2Ord_ne_two hp hp2 hm0ne
  obtain ⟨-, hlab, -⟩ := CFSG.LocalAnalysis.GLTheoremA.rk2_model_of_isLabel hK
  have hn1 : 1 ≤ n := hlab.1
  have hl2 : 2 ≤ ℓ := hlab.2.1
  have hN12 : n = 1 → 12 ≤ ℓ + 1 := by
    intro hn1'
    subst hn1'
    exact twelve_le_rank_add_one_of_famTwA_one hK hp hp2 hm0ne
      (by have := pRank_mono hp.one_lt (le_top : A ≤ (⊤ : Subgroup K)); omega)
  obtain ⟨F, hFld, hFin, hChar, C, hCn, hFcard, hCcen, ⟨e⟩⟩ :=
    exists_statedSU_cover hK hn1 hN12
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  haveI : C.Normal := hCn
  have hnq : (ℓ + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : ℓ + 1 = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1' : n = 1 := by omega
      have := hN12 hn1'
      omega
    · have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
      omega
  have hdvd : Nat.card (Subgroup.center (StatedSU (ℓ + 1) (2 ^ n) F)) ∣ 2 ^ n + 1 :=
    card_center_statedSU_dvd_two_pow_add_one hFcard hn1 (by omega) hnq
  have hpC : ¬ p ∣ Nat.card C := fun h =>
    hpq1 (h.trans (Subgroup.card_dvd_of_le hCcen |>.trans hdvd))
  let π : StatedSU (ℓ + 1) (2 ^ n) F →* K :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' C)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective C)
  have hπker : π.ker = C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, QuotientGroup.ker_mk']
  have hker : π.ker ≤ Subgroup.center (StatedSU (ℓ + 1) (2 ^ n) F) := by
    rw [hπker]; exact hCcen
  have hpk : ¬ p ∣ Nat.card π.ker := by rw [hπker]; exact hpC
  have hconcl := concl165Avoid_of_engine hE hFcard hn1 hl2 hm0ne hp hp2 hq hq2 hqp hqdiv
    C hCcen hnq
  obtain ⟨R, -, hRe, hRmap, -⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.exists_elemAbelian_lift hp hpk
      (Subgroup.map_comap_eq_self_of_surjective hπ A) hAe
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) :=
    CFSG.SectionRank.pRank_quotient_eq π.ker hpk
  have hiso : CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F ⧸ π.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hRankH : CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) =
      CFSG.Open.pRank p (⊤ : Subgroup K) := hquot.symm.trans hiso
  have hRankR : CFSG.Open.pRank p R = CFSG.Open.pRank p A := by
    have hRp : IsPGroup p R :=
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.isPGroup_of_pow_eq_one hRe.2
    rw [pRank_eq_pRank_map_of_isPGroup hp hpk hRp, hRmap]
  have hRmax : CFSG.Open.pRank p (⊤ : Subgroup (StatedSU (ℓ + 1) (2 ^ n) F)) ≤
      CFSG.Open.pRank p R := by
    rw [hRankH, hRankR]
    exact hmax
  have hR3 : 3 ≤ CFSG.Open.pRank p R := by rw [hRankR]; exact hm3
  have hconcl' : Concl165Avoid (StatedSU (ℓ + 1) (2 ^ n) F) p q R π.ker := by
    rw [hπker]; exact hconcl R hRe hRmax hR3
  have hA' : Concl165 K p q (R.map π) :=
    concl165_map_of_central hp hq π hπ hker hpk hconcl'
  rw [hRmap] at hA'
  simpa only [Concl165] using hA'

end Certificate

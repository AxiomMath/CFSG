module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDL227SporRows
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Two
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagL2
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem prime_mul_card_pSimple_dvd_cent {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    {k : S} (hk : orderOf k = p) {J : Subgroup S}
    (hJ : J ≤ Subgroup.centralizer ({k} : Set S)) :
    p * Nat.card (PSimple p J) ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hkc : ∀ g ∈ J, g * k = k * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hJ hg)
  by_cases hkJ : k ∈ J
  · set k' : ↥J := ⟨k, hkJ⟩
    set kb : PQuot p J := (QuotientGroup.mk k' : PQuot p J) with hkb
    have hZ : kb ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [hkb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hkc g g.2)
    have hk'3 : orderOf k' = p := by
      rw [← Subgroup.orderOf_coe]
      exact hk
    have hkb1 : kb ≠ 1 := by
      intro h
      have hmem : k' ∈ GLAPPrimeCore p ↥J := (QuotientGroup.eq_one_iff k').1 h
      have h3 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hk'3] at h3
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore hp ↥J
      exact hp.one_lt.ne' ((Nat.coprime_self p).1 (Nat.Coprime.coprime_dvd_right h3 hcop))
    have hkb3 : orderOf kb = p := by
      refine orderOf_eq_prime ?_ hkb1
      rw [hkb, ← QuotientGroup.mk_pow, ← hk'3, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h3Z := Subgroup.orderOf_dvd_natCard _ hZ
    rw [hkb3] at h3Z
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot p J))
    have h2 : Nat.card (PQuot p J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card J ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) :=
      Subgroup.card_dvd_of_le hJ
    refine Dvd.dvd.trans ?_ (h2.trans h3)
    rw [h1, mul_comm]
    exact Nat.mul_dvd_mul_left _ h3Z
  · have hN : Subgroup.zpowers k ≤ Subgroup.normalizer (J : Set S) := by
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have : k * g * k⁻¹ = g := by rw [← hkc g hg]; group
        rw [this]; exact hg
      · intro hg
        have hg' : k⁻¹ * (k * g * k⁻¹) * k ∈ J := by
          have hx := hkc _ hg
          have : k⁻¹ * (k * g * k⁻¹) * k = k * g * k⁻¹ := by
            calc k⁻¹ * (k * g * k⁻¹) * k = k⁻¹ * ((k * g * k⁻¹) * k) := by group
              _ = k⁻¹ * (k * (k * g * k⁻¹)) := by rw [hx]
              _ = k * g * k⁻¹ := by group
          rw [this]; exact hg
        have : k⁻¹ * (k * g * k⁻¹) * k = g := by group
        rwa [this] at hg'
    have hb : Subgroup.zpowers k ⊓ J = ⊥ := by
      have hd : Nat.card ↥(Subgroup.zpowers k ⊓ J) ∣ p := by
        rw [← hk, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).1 hd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exfalso
        have heq : Subgroup.zpowers k ⊓ J = Subgroup.zpowers k :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hk, h])
        exact hkJ ((heq ▸ inf_le_right : Subgroup.zpowers k ≤ J) (Subgroup.mem_zpowers k))
    have hc := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.card_sup_of_inf_bot hN hb
    rw [Nat.card_zpowers, hk] at hc
    calc p * Nat.card (PSimple p J) ∣ p * Nat.card J :=
        Nat.mul_dvd_mul_left p (KDL227Rows.card_pSimple_dvd p J)
      _ = Nat.card ↥(Subgroup.zpowers k ⊔ J) := hc.symm
      _ ∣ Nat.card (Subgroup.centralizer ({k} : Set S)) :=
        Subgroup.card_dvd_of_le (sup_le (Subgroup.zpowers_le.2
          (Subgroup.mem_centralizer_singleton_iff.2 rfl)) hJ)

theorem card_eq_168_of_dvd {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 168) : Nat.card T = 168 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 84 ∨ Nat.card T = 168 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc1 : c ≤ 2 := by
      by_contra h
      have : Nat.card T * 3 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  rcases hcases with h84 | h168
  · exfalso
    obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
    have hn1 : Nat.card (Sylow 7 T) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 T
    have hnidx : Nat.card (Sylow 7 T) = (Subgroup.normalizer ((P : Subgroup T) : Set T)).index :=
      Sylow.card_eq_index_normalizer P
    have hidx : (Subgroup.normalizer ((P : Subgroup T) : Set T)).index ∣ (P : Subgroup T).index :=
      Subgroup.index_dvd_of_le Subgroup.le_normalizer
    have hidx12 : (P : Subgroup T).index ∣ 12 := by
      have h1 : (P : Subgroup T).index ∣ 84 := h84 ▸ Subgroup.index_dvd_card _
      have h2 : ¬ 7 ∣ (P : Subgroup T).index := P.not_dvd_index
      have hcop : Nat.Coprime (P : Subgroup T).index 7 :=
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h2).symm
      exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
    have hn12 : Nat.card (Sylow 7 T) ∣ 12 := hnidx ▸ hidx.trans hidx12
    have hn : Nat.card (Sylow 7 T) = 1 := by
      have hle := Nat.le_of_dvd (by norm_num) hn12
      have h1 : Nat.card (Sylow 7 T) % 7 = 1 := hn1
      have hpos : 0 < Nat.card (Sylow 7 T) := Nat.card_pos
      interval_cases h : Nat.card (Sylow 7 T) <;> omega
    have hN : Subgroup.normalizer ((P : Subgroup T) : Set T) = ⊤ := by
      rw [← Subgroup.index_eq_one, ← hnidx, hn]
    have hPn : (P : Subgroup T).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    have h7 : 7 ∣ Nat.card T := by rw [h84]; norm_num
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup T) with hb | ht
    · have := P.dvd_card_of_dvd_card h7
      rw [hb, Subgroup.card_bot] at this
      norm_num at this
    · apply hns
      have hp : IsPGroup 7 T := by
        have := P.isPGroup'
        rw [ht] at this
        exact this.of_equiv Subgroup.topEquiv
      haveI := hp.isNilpotent
      infer_instance
  · exact h168

theorem orderOf_mul_pow_six {G : Type*} [Group G] {x y : G} (hc : Commute x y) (hx : x ^ 7 = 1)
    (hy : y ^ 7 = 1) (hpow : ∀ k < 7, y ≠ x ^ k) : orderOf (x * y ^ 6) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [(hc.pow_right 6).mul_pow, hx, one_mul, ← pow_mul, show 6 * 7 = 7 * 6 by norm_num,
      pow_mul, hy, one_pow]
  · intro h1
    apply hpow 1 (by norm_num)
    have hy6 : y ^ 6 = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hyinv : y⁻¹ = y ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hy])
    rw [pow_one, ← inv_inv y, hyinv, hy6, inv_inv]

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

variable {G : Type*} [Group G]

theorem exists_conj_eq_of_pair [Finite G] {p : ℕ} [hp : Fact p.Prime] {x y z : G}
    (hcomm : x * y = y * x) (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hpow : ∀ k < p, y ≠ x ^ k) (hfac : (Nat.card G).factorization p = 2)
    (hconj : ∀ i j : ℕ, i < p → j < p → i + j ≠ 0 → ∃ m : G, m * (x ^ i * y ^ j) = z * m)
    {s : G} (hs : orderOf s = p) : ∃ c : G, c * s * c⁻¹ = z := by
  have hG : ¬ p ^ 3 ∣ Nat.card G := by
    intro h
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have := (hp.out.pow_dvd_iff_le_factorization h0).1 h
    omega
  have hQ := card_closure_pair_eq_sq hcomm hx hy hx1 hpow hG
  have hQfull : Nat.card (Subgroup.closure ({x, y} : Set G)) =
      p ^ (Nat.card (⊤ : Subgroup G)).factorization p := by
    rw [hQ, Subgroup.card_top, hfac]
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨i, hi, j, hj, hw⟩ := exists_pow_mul_pow_of_mem hp.out.pos hcomm hx hy hgQ
  have hwo : orderOf (g⁻¹ * s * g) = p := by rw [orderOf_inv_mul_mul, hs]
  have hij : i + j ≠ 0 := by
    intro h0
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    rw [hi0, hj0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  obtain ⟨m, hm⟩ := hconj i j hi hj hij
  refine ⟨m * g⁻¹, ?_⟩
  rw [← hw] at hm
  calc (m * g⁻¹) * s * (m * g⁻¹)⁻¹ = (m * (g⁻¹ * s * g)) * m⁻¹ := by group
    _ = z := by rw [hm]; group

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremB
  CFSG.Yardstones.Md0ec50421ce4

set_option maxRecDepth 100000 in
theorem card_centralizer_z7 :
    Nat.card (Subgroup.centralizer ({slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6} : Set J)) = 1176 :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven.thSeven_complete.2

set_option maxRecDepth 100000 in
theorem orderOf_z7 : orderOf (slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6) = 7 := by
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  exact orderOf_mul_pow_six (matJ_injective (by simp only [matJ_mul]; exact hcomm)) h7x h7y hpow

set_option maxRecDepth 100000 in
theorem compOK_z7 : CompOK 7 (slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6) := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  intro I hI
  obtain ⟨hs, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab hp7 hI
  haveI := hs
  have hd : 7 * Nat.card (PSimple 7 I) ∣ 1176 :=
    card_centralizer_z7 ▸ prime_mul_card_pSimple_dvd_cent hp7 orderOf_z7 hI.1
  have hd168 : Nat.card (PSimple 7 I) ∣ 168 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))
  have hc := card_eq_168_of_dvd hnab hd168
  exact fun _ h49 _ => absurd h49 (not_sq_seven_dvd_card_mulAut_of_card_168 hc)

set_option maxRecDepth 100000 in
theorem compOK_seven_J (k : J) (hk : orderOf k = 7) : CompOK 7 k := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨h7x, h7y, hcomm, hx1, hpow⟩ := thSeven_pair
  obtain ⟨c, hc⟩ := exists_conj_eq_of_pair (z := slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6)
    (matJ_injective (by simp only [matJ_mul]; exact hcomm)) h7x h7y hx1 hpow
    (by rw [CFSG.Sporadic.Th.Max3.natCard_J,
      show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num,
      factorization_pow_mul Nat.prime_seven 2 _ (by norm_num)])
    (fun i j hi hj hij => by
      obtain ⟨m, hm⟩ := thSeven_conj hi hj hij
      refine ⟨m, matJ_injective ?_⟩
      simp only [matJ_mul, matJ_pow] at hm ⊢
      exact hm) hk
  have := CompOK.of_mulEquiv hp7 (MulAut.conj c⁻¹) compOK_z7
  rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
  exact this

set_option maxRecDepth 20000 in
theorem row_Th_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    I1416SporRow .Th 7 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Th.J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hnc : ∃ a c : ↥CFSG.Sporadic.Th.J, a * c ≠ c * a := by
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts
    have hcC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
      CFSG.RankThree.OddKernel.card_Th_eq
    obtain ⟨a, c, hac⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (S := CFSG.Blueprint.NativeSporadic.Carrier .Th) (by rw [hcC]; norm_num)
    refine ⟨e a, e c, fun h => hac ?_⟩
    exact e.injective ((e.map_mul a c).trans (h.trans (e.map_mul c a).symm))
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (hbr .Th).some
  exact @row_of_model .Th 7 ↥CFSG.Sporadic.Th.J _ hfin hs hOut b hnc compOK_seven_J

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven

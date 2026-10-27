module

public import CFSG.CGT.Hall82.Setting
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenTI
public import CFSG.Quasithin.Vol2.Ch10SecQ4A15
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_zpowers_eq_centralizer_singleton (w : G) :
    Subgroup.centralizer (Subgroup.zpowers w : Set G) = Subgroup.centralizer ({w} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem commutator_mul_mem_abelian {A : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x : G}
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) {a w : G} (ha : a ∈ A) (hw : w ∈ A) :
    ⁅a, w * x⁆ = ⁅a, x⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have haw : ⁅a, w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hAcomm a ha w hw)
  rw [haw, one_mul]
  have hxA' : ⁅a, x⁆ ∈ A := by
    have e : ⁅a, x⁆ = a * (x * a * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem ha (A.inv_mem (hxA a ha))
  rw [hAcomm w hw ⁅a, x⁆ hxA']
  group

theorem commutator_zpowers_eq_closure {A : Subgroup G} {z : G} (hzord : orderOf z = 3)
    (hzA : ∀ a ∈ A, z * a * z⁻¹ ∈ A) :
    ⁅A, Subgroup.zpowers z⁆ = Subgroup.closure {w | ∃ a ∈ A, ⁅a, z⁆ = w} := by
  classical
  apply le_antisymm
  · refine Subgroup.commutator_le.mpr ?_
    intro a ha k hk
    have hk' : k ∈ (Finset.range (orderOf z)).image (z ^ ·) :=
      (mem_zpowers_iff_mem_range_orderOf (x := z) (y := k)).mp hk
    rw [hzord] at hk'
    simp only [Finset.mem_image, Finset.mem_range] at hk'
    obtain ⟨i, hi, hik⟩ := hk'
    rw [← hik]
    interval_cases i
    · simp
    · simpa using Subgroup.subset_closure
        (k := {w | ∃ a ∈ A, ⁅a, z⁆ = w}) ⟨a, ha, rfl⟩
    · have e : ⁅a, z ^ 2⁆ = ⁅a, z⁆ * (z * ⁅a, z⁆ * z⁻¹) := by
        rw [pow_two, commutatorElement_mul_right_eq_mul_conj]
        group
      rw [e]
      refine (Subgroup.closure _).mul_mem (Subgroup.subset_closure
        (k := {w | ∃ a ∈ A, ⁅a, z⁆ = w}) ⟨a, ha, rfl⟩) ?_
      have e2 : z * ⁅a, z⁆ * z⁻¹ = ⁅z * a * z⁻¹, z⁆ := by
        simpa using conjugate_commutatorElement (g₁ := a) (g₂ := z) (g₃ := z)
      rw [e2]
      exact Subgroup.subset_closure
        (k := {w | ∃ a ∈ A, ⁅a, z⁆ = w})
        ⟨z * a * z⁻¹, hzA a ha, rfl⟩
  · rw [Subgroup.closure_le]
    rintro w ⟨a, ha, rfl⟩
    exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers z)

theorem commutator_zpowers_mul_eq {A : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {w z : G} (hw : w ∈ A)
    (hzord : orderOf z = 3) (hwzord : orderOf (w * z) = 3)
    (hzA : ∀ a ∈ A, z * a * z⁻¹ ∈ A) (hwzA : ∀ a ∈ A, (w * z) * a * (w * z)⁻¹ ∈ A) :
    ⁅A, Subgroup.zpowers (w * z)⁆ = ⁅A, Subgroup.zpowers z⁆ := by
  rw [commutator_zpowers_eq_closure hzord hzA, commutator_zpowers_eq_closure hwzord hwzA]
  congr 1
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (commutator_mul_mem_abelian hAcomm hzA ha hw).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, commutator_mul_mem_abelian hAcomm hzA ha hw⟩


private def blockFix (L : Subgroup G) (z : G) : Subgroup G :=
  blockU L ⊓ Subgroup.centralizer ({z} : Set G)

private def blockComm (L : Subgroup G) (z : G) : Subgroup G :=
  ⁅blockU L, Subgroup.zpowers z⁆

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} (S : Setting G M L)
include S

theorem blockU_le_blockQ : blockU L ≤ blockQ L := fun _ hw => (S.short.blockU_le_center hw).1

theorem blockQ_comm_blockU {a b : G} (ha : a ∈ blockQ L) (hb : b ∈ blockU L) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.mp (S.short.blockU_le_center hb).2 a ha

theorem blockU_comm {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L) : a * b = b * a := by
  have h := S.elemU.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

theorem blockU_sq {v : G} (hv : v ∈ blockU L) : v ^ 2 = 1 := S.elemU.2 v hv

theorem blockQ_isPGroup : IsPGroup 2 (blockQ L) :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L

theorem le_normalizer_blockQ : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L

theorem commutator_blockU : ⁅blockU L, L⁆ = blockU L :=
  SimsTheoremC.commutator_commutator_eq_of_twoResidual S.short.eq_twoResidual
    S.blockQ_isPGroup S.le_normalizer_blockQ

theorem exists_order_three_data :
    ∃ (α : ↥L →* alternatingGroup (Fin 6)) (z : ↥L),
      Function.Surjective α ∧ CFSG.pCore 2 ↥L ≤ α.ker ∧
      Nat.card α.ker = 3 * Nat.card (CFSG.pCore 2 ↥L) ∧ z ∈ α.ker ∧
      orderOf (z : G) = 3 ∧ (z : G) ∉ blockQ L ∧
      (∀ y ∈ L, y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ blockQ L) ∧
      (∀ p ∈ blockQ L, ⁅(z : G), p⁆ ∈ blockU L) := by
  obtain ⟨⟨α, hαsurj, hPle, hcardker⟩, -⟩ := S.type
  set P0 : Subgroup ↥L := CFSG.pCore 2 ↥L with hP0
  have h3dvd : 3 ∣ Nat.card α.ker := by
    rw [hcardker]
    exact dvd_mul_right 3 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set z : G := (((k : α.ker) : ↥L) : G) with hz
  have hzL : z ∈ L := ((k : α.ker) : ↥L).2
  have hzord : orderOf z = 3 := by
    rw [hz]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hk
  have hzP : z ∉ blockQ L := by
    intro hzQ
    obtain ⟨n, hn⟩ := S.blockQ_isPGroup ⟨z, hzQ⟩
    have hdvd : orderOf (⟨z, hzQ⟩ : blockQ L) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have h3 : orderOf (⟨z, hzQ⟩ : blockQ L) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨z, hzQ⟩ : blockQ L)]
      exact hzord
    rw [h3] at hdvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
  let ab : (↥L ⧸ P0) →* alternatingGroup (Fin 6) := QuotientGroup.lift P0 α hPle
  have habsurj : Function.Surjective ab := by
    intro σ
    obtain ⟨x, rfl⟩ := hαsurj σ
    exact ⟨QuotientGroup.mk x, rfl⟩
  have habker : Nat.card ab.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ab.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ab habsurj).toEquiv,
      CFSG.EvenSporadicStandard.M24Std.DRes.card_alt6, S.card_quot] at h1
    omega
  have hkerne : ab.ker ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ab.ker = Nat.card (⊤ : Subgroup (↥L ⧸ P0)) := by rw [htop]
    rw [Subgroup.card_top, S.card_quot] at h1
    omega
  have hker_center : ab.ker ≤ Subgroup.center (↥L ⧸ P0) := by
    rcases CFSG.Quasithin.Vol2.Ch10.SecF.C10E4.normal_le_center_or_eq_top' S.quasisimple
      ab.ker with h | h
    · exact h
    · exact absurd h hkerne
  have hzker : QuotientGroup.mk' P0 ⟨z, hzL⟩ ∈ ab.ker := by
    rw [MonoidHom.mem_ker]
    show α ⟨z, hzL⟩ = 1
    exact (k : α.ker).2
  have hzcenter : QuotientGroup.mk' P0 ⟨z, hzL⟩ ∈ Subgroup.center (↥L ⧸ P0) :=
    hker_center hzker
  have hzPcomm : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ blockQ L := by
    intro y hy
    set y' : ↥L := ⟨y, hy⟩ with hy'
    have hq : QuotientGroup.mk' P0 (y' * ⟨z, hzL⟩ * y'⁻¹ * ⟨z, hzL⟩⁻¹) = 1 := by
      have e : QuotientGroup.mk' P0 (y' * ⟨z, hzL⟩ * y'⁻¹ * ⟨z, hzL⟩⁻¹) =
          QuotientGroup.mk' P0 y' * QuotientGroup.mk' P0 ⟨z, hzL⟩ *
            (QuotientGroup.mk' P0 y')⁻¹ * (QuotientGroup.mk' P0 ⟨z, hzL⟩)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [e, Subgroup.mem_center_iff.mp hzcenter (QuotientGroup.mk' P0 y')]
      group
    have hmem : y' * ⟨z, hzL⟩ * y'⁻¹ * ⟨z, hzL⟩⁻¹ ∈ P0 :=
      (QuotientGroup.eq_one_iff _).mp hq
    have hcoe : ((y' * ⟨z, hzL⟩ * y'⁻¹ * ⟨z, hzL⟩⁻¹ : ↥L) : G) = y * z * y⁻¹ * z⁻¹ := rfl
    rw [← hcoe]
    exact (CFSG.RankThree.PartTwo.Sec19.SolSeven.mem_pCore_iff _).mp hmem
  have hcommV : ∀ p ∈ blockQ L, ⁅z, p⁆ ∈ blockU L := by
    intro p hpP
    have h : ⁅p, z⁆ ∈ blockU L := Subgroup.commutator_mem_commutator hpP hzL
    simpa only [commutatorElement_inv] using (blockU L).inv_mem h
  exact ⟨α, ⟨z, hzL⟩, hαsurj, hPle, hcardker, (k : α.ker).2, hzord, hzP, hzPcomm, hcommV⟩

theorem mem_blockU_of_conj {z : G} (hzL : z ∈ L) (hzord : orderOf z = 3)
    (hzV : ∀ q ∈ blockQ L, ⁅z, q⁆ ∈ blockU L)
    (hzPcomm : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ blockQ L) {y : G} (hy : y ∈ L) :
    y * z * y⁻¹ * z⁻¹ ∈ blockU L := by
  set p : G := y * z * y⁻¹ * z⁻¹ with hp
  have hpP : p ∈ blockQ L := hzPcomm y hy
  set v1 : G := ⁅z, p⁆ with hv1
  have hv1V : v1 ∈ blockU L := hzV p hpP
  set v2 : G := z * v1 * z⁻¹ with hv2
  have hv2V : v2 ∈ blockU L := CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU hzL hv1V
  have hzp : z * p * z⁻¹ = v1 * p := by
    rw [hv1, commutatorElement_def]
    group
  have hz2p : z * (z * p * z⁻¹) * z⁻¹ = v2 * (v1 * p) := by
    calc z * (z * p * z⁻¹) * z⁻¹ = z * (v1 * p) * z⁻¹ := by rw [hzp]
      _ = (z * v1 * z⁻¹) * (z * p * z⁻¹) := by group
      _ = (z * v1 * z⁻¹) * (v1 * p) := by rw [hzp]
      _ = v2 * (v1 * p) := by rw [← hv2]
  have hpz : p * z = y * z * y⁻¹ := by rw [hp]; group
  have hz3 : z ^ 3 = 1 := by
    rw [← hzord]; exact pow_orderOf_eq_one z
  have hpz3 : (p * z) ^ 3 = 1 := by
    rw [hpz]
    have e : (y * z * y⁻¹) ^ 3 = y * z ^ 3 * y⁻¹ := by
      rw [pow_three', pow_three']
      group
    rw [e, hz3]
    group
  have hexp : (p * z) ^ 3 = p ^ 3 * v2 := by
    have e : (p * z) ^ 3 =
        p * (z * p * z⁻¹) * (z * (z * p * z⁻¹) * z⁻¹) * z ^ 3 := by
      rw [pow_three', pow_three']
      group
    rw [e, hz2p, hzp, hz3, mul_one]
    have e1 : v1 * p = p * v1 :=
      (S.blockQ_comm_blockU (a := p) (b := v1) hpP hv1V).symm
    have e2 : v2 * p = p * v2 :=
      (S.blockQ_comm_blockU (a := p) (b := v2) hpP hv2V).symm
    have e3 : v1 * v2 = v2 * v1 := S.blockU_comm hv1V hv2V
    have e4 : v1 * v1 = 1 := by rw [← pow_two]; exact S.blockU_sq hv1V
    calc p * (v1 * p) * (v2 * (v1 * p))
        = p * (p * v1) * (v2 * (p * v1)) := by rw [e1]
      _ = p * p * v1 * (v2 * p) * v1 := by group
      _ = p * p * v1 * (p * v2) * v1 := by rw [e2]
      _ = p * p * (v1 * p) * v2 * v1 := by group
      _ = p * p * (p * v1) * v2 * v1 := by rw [e1]
      _ = p * p * p * (v1 * v2) * v1 := by group
      _ = p * p * p * (v2 * v1) * v1 := by rw [e3]
      _ = p * p * p * v2 * (v1 * v1) := by group
      _ = p ^ 3 * v2 := by rw [e4, mul_one, pow_three']
  have hp3 : p ^ 3 = v2 := by
    have h : p ^ 3 * v2 = 1 := by rw [← hexp, hpz3]
    have h2 : p ^ 3 = v2⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have hv2sq : v2 * v2 = 1 := by rw [← pow_two]; exact S.blockU_sq hv2V
    have hv2inv : v2⁻¹ = v2 := by
      calc v2⁻¹ = v2⁻¹ * 1 := (mul_one _).symm
        _ = v2⁻¹ * (v2 * v2) := by rw [hv2sq]
        _ = v2 := by group
    rwa [hv2inv] at h2
  obtain ⟨n, hn⟩ := S.blockQ_isPGroup ⟨p, hpP⟩
  have hpn : p ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hdvd2 : orderOf p ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hpn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have h6 : p ^ 6 = 1 := by
    calc p ^ 6 = (p ^ 3) ^ 2 := by group
      _ = v2 ^ 2 := by rw [hp3]
      _ = 1 := S.blockU_sq hv2V
  have hdvd6 : orderOf p ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hk2 : 2 ^ k ∣ 2 := by
    have hd : 2 ^ k ∣ 6 := hk ▸ hdvd6
    have hle : 2 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hk3 : k ≤ 2 := by
      by_contra h
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    · norm_num
    · norm_num
    · exfalso
      revert hd
      norm_num
  have hp2 : p ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hk ▸ hk2)
  have hpV : p ∈ blockU L := by
    have e : p ^ 3 = p := by
      calc p ^ 3 = p ^ 2 * p := by group
        _ = p := by rw [hp2, one_mul]
    rw [← e, hp3]
    exact hv2V
  rwa [hp] at hpV

theorem exists_order_three_data' :
    ∃ (α : ↥L →* alternatingGroup (Fin 6)) (z : ↥L),
      Function.Surjective α ∧ CFSG.pCore 2 ↥L ≤ α.ker ∧
      Nat.card α.ker = 3 * Nat.card (CFSG.pCore 2 ↥L) ∧ z ∈ α.ker ∧
      orderOf (z : G) = 3 ∧ (z : G) ∉ blockQ L ∧
      (∀ y ∈ L, y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ blockU L) ∧
      (∀ q ∈ blockQ L, ⁅(z : G), q⁆ ∈ blockU L) := by
  obtain ⟨α, z, hαsurj, hPle, hcardker, hzker, hzord, hzP, hzPcomm, hzV⟩ :=
    exists_order_three_data S
  exact ⟨α, z, hαsurj, hPle, hcardker, hzker, hzord, hzP,
    fun y hy => mem_blockU_of_conj S z.2 hzord hzV hzPcomm hy, hzV⟩


private noncomputable def blockAut (L : Subgroup G) (z : G) : Subgroup (MulAut ↥(blockU L)) :=
  CFSG.Quasithin.autOn (Subgroup.zpowers z) (blockU L)

private theorem blockFix_bot_and_fpf {z : G} (hzL : z ∈ L) (hzord : orderOf z = 3)
    (hzP : z ∉ blockQ L)
    (hzW : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ blockU L)
    (hzPcomm : ∀ p ∈ blockQ L, ⁅z, p⁆ ∈ blockU L) :
    blockFix L z = ⊥ ∧ (∀ v ∈ blockU L, z * v * z⁻¹ = v → v = 1) := by
  have hmemFix : ∀ {w : G}, w ∈ blockFix L z ↔ w ∈ blockU L ∧ z * w = w * z := by
    intro w
    rw [blockFix, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  have hFixLe : blockFix L z ≤ blockU L := inf_le_left
  have hCommLe : blockComm L z ≤ blockU L := by
    rw [blockComm, Subgroup.commutator_le]
    intro a ha k hk
    have h := Subgroup.commutator_mem_commutator ha (Subgroup.zpowers_le.mpr hzL hk)
    rwa [S.commutator_blockU] at h
  have hZle : blockZ L ≤ blockFix L z := by
    intro w hw
    rw [hmemFix]
    exact ⟨hw.1, Subgroup.mem_centralizer_iff.mp hw.2 z hzL⟩
  have hconjFix : ∀ {y : G}, y ∈ L → ∀ {w : G}, w ∈ blockFix L z →
      y * w * y⁻¹ ∈ blockFix L z := by
    intro y hy w hw
    rw [hmemFix] at hw ⊢
    obtain ⟨hwV, hwz⟩ := hw
    refine ⟨CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU hy hwV, ?_⟩
    have hv1 : y⁻¹ * z * y * z⁻¹ ∈ blockU L := by
      simpa using hzW y⁻¹ (L.inv_mem hy)
    have hv1eq : y⁻¹ * z * y = (y⁻¹ * z * y * z⁻¹) * z := by group
    have hwv1 : (y⁻¹ * z * y * z⁻¹) * w = w * (y⁻¹ * z * y * z⁻¹) :=
      S.blockU_comm hv1 hwV
    have hcomm : w * (y⁻¹ * z * y) = (y⁻¹ * z * y) * w := by
      rw [hv1eq]
      calc w * ((y⁻¹ * z * y * z⁻¹) * z) = (w * (y⁻¹ * z * y * z⁻¹)) * z := by group
        _ = ((y⁻¹ * z * y * z⁻¹) * w) * z := by rw [hwv1]
        _ = (y⁻¹ * z * y * z⁻¹) * (w * z) := by group
        _ = (y⁻¹ * z * y * z⁻¹) * (z * w) := by rw [hwz]
        _ = ((y⁻¹ * z * y * z⁻¹) * z) * w := by group
    calc z * (y * w * y⁻¹) = y * (y⁻¹ * z * y) * w * y⁻¹ := by group
      _ = y * (w * (y⁻¹ * z * y)) * y⁻¹ := by rw [hcomm]; group
      _ = (y * w * y⁻¹) * z := by group
  have hFixNorm : L ≤ Subgroup.normalizer (blockFix L z : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    exact ⟨fun hw => hconjFix hy hw, fun hw => by
      have h1 : y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ ∈ blockFix L z :=
        hconjFix (y := y⁻¹) (L.inv_mem hy) hw
      rw [show y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ = w by group] at h1
      exact h1⟩
  have hCommNorm : L ≤ Subgroup.normalizer (blockComm L z : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj y)) (blockComm L z) = blockComm L z
    have hVmap : (blockU L).map (MulAut.conj y).toMonoidHom = blockU L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.normalizer_commutator_ge_right (blockQ L) L hy)
    have hmap : (blockComm L z).map (MulAut.conj y).toMonoidHom
        = ⁅blockU L, Subgroup.zpowers (y * z * y⁻¹)⁆ := by
      rw [blockComm, Subgroup.map_commutator, MonoidHom.map_zpowers, hVmap]
      rfl
    rw [hmap]
    have hv0 : y * z * y⁻¹ * z⁻¹ ∈ blockU L := hzW y hy
    have hv0eq : (y * z * y⁻¹ * z⁻¹) * z = y * z * y⁻¹ := by group
    rw [← hv0eq]
    have hv0zord : orderOf ((y * z * y⁻¹ * z⁻¹) * z) = 3 := by
      rw [hv0eq]
      have e : y * z * y⁻¹ = (MulAut.conj y) z := rfl
      rw [e, (MulAut.conj y).orderOf_eq z, hzord]
    have hVnorm : ∀ a ∈ blockU L, z * a * z⁻¹ ∈ blockU L :=
      fun a ha => CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU hzL ha
    have hv0norm : ∀ a ∈ blockU L, ((y * z * y⁻¹ * z⁻¹) * z) * a *
        ((y * z * y⁻¹ * z⁻¹) * z)⁻¹ ∈ blockU L := by
      intro a ha
      rw [hv0eq]
      exact CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU
        (L.mul_mem (L.mul_mem hy hzL) (L.inv_mem hy)) ha
    exact commutator_zpowers_mul_eq (fun a ha b hb => S.blockU_comm ha hb)
      hv0 hzord hv0zord hVnorm hv0norm
  let _ : CommGroup ↥(blockU L) := commGroupOfElemAbelian S.elemU
  have hodd : Odd (Nat.card (blockAut L z)) := by
    have hcard : Nat.card (blockAut L z) ∣ 3 := by
      have h := CFSG.Quasithin.AutOn.card_autOn_dvd (Subgroup.zpowers z) (blockU L)
      rw [blockAut]
      rwa [Nat.card_zpowers, hzord] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h1 | h3
    · rw [h1]; exact ⟨0, by norm_num⟩
    · rw [h3]; exact ⟨1, by norm_num⟩
  have hcompl : IsCompl (fixV (blockAut L z)) (commV (blockAut L z)) := by
    refine isCompl_fixV_commV_of_odd (blockAut L z) hodd ?_
    intro v
    exact Subtype.ext (S.blockU_sq v.2)
  have hLnormW : Subgroup.zpowers z ≤ Subgroup.normalizer (blockU L : Set G) :=
    (Subgroup.zpowers_le.mpr hzL).trans
      (Subgroup.normalizer_commutator_ge_right (blockQ L) L)
  have hfixA : (fixV (blockAut L z)).map (blockU L).subtype = blockFix L z := by
    rw [blockAut, CFSG.Quasithin.AutOn.fixV_autOn_eq hLnormW,
      Subgroup.subgroupOf_map_subtype, centralizer_zpowers_eq_centralizer_singleton, blockFix,
      inf_comm]
  have hcommA : (commV (blockAut L z)).map (blockU L).subtype = blockComm L z := by
    rw [blockAut, CFSG.Quasithin.AutOn.commV_autOn_eq hLnormW,
      Subgroup.subgroupOf_map_subtype, blockComm]
    exact inf_eq_left.mpr hCommLe
  have hsup : blockFix L z ⊔ blockComm L z = blockU L := by
    have h := congrArg (Subgroup.map (blockU L).subtype) hcompl.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, hfixA, hcommA] at h
    exact h
  have hinf : blockFix L z ⊓ blockComm L z = ⊥ := by
    have h := congrArg (Subgroup.map (blockU L).subtype) hcompl.inf_eq_bot
    rw [Subgroup.map_inf _ _ _ (blockU L).subtype_injective, Subgroup.map_bot,
      hfixA, hcommA] at h
    exact h
  have hdecomp : ∀ {v : G}, v ∈ blockU L →
      ∃ w ∈ blockFix L z, ∃ c ∈ blockComm L z, w * c = v := by
    intro v hv
    have hv' : (⟨v, hv⟩ : ↥(blockU L)) ∈ fixV (blockAut L z) ⊔ commV (blockAut L z) := by
      rw [hcompl.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, c, hc, hwc⟩ := Subgroup.mem_sup.mp hv'
    refine ⟨(w : G), ?_, (c : G), ?_, ?_⟩
    · rw [← hfixA]
      exact Subgroup.mem_map_of_mem (blockU L).subtype hw
    · rw [← hcommA]
      exact Subgroup.mem_map_of_mem (blockU L).subtype hc
    · exact congrArg Subtype.val hwc
  rcases S.short.irreducible (blockFix L z) hZle hFixLe hFixNorm with hW | hW
  · have hFixBot : blockFix L z = ⊥ := by
      have hsub : blockU L ≤ blockComm L z := by
        rw [← S.commutator_blockU]
        refine Subgroup.commutator_le.mpr ?_
        intro v hv y hy
        obtain ⟨w, hwFix, c, hcComm, hwc⟩ := hdecomp hv
        have hwZ : w ∈ blockZ L := hW ▸ hwFix
        have hwcY : w * y = y * w := (Subgroup.mem_centralizer_iff.mp hwZ.2 y hy).symm
        have hwy : ⁅w, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hwcY
        have hcV : c ∈ blockU L := hCommLe hcComm
        have hcy : ⁅c, y⁆ ∈ blockU L := by
          have h1 := Subgroup.commutator_mem_commutator hcV hy
          rwa [S.commutator_blockU] at h1
        have hwc' : w * ⁅c, y⁆ * w⁻¹ = ⁅c, y⁆ := by
          rw [S.blockU_comm (hFixLe hwFix) hcy]
          group
        have e : ⁅v, y⁆ = ⁅c, y⁆ := by
          rw [← hwc, commutatorElement_mul_left_eq_conj_mul, hwy, mul_one, hwc']
        rw [e]
        have hycy : y * c * y⁻¹ ∈ blockComm L z :=
          (Subgroup.mem_normalizer_iff.mp (hCommNorm hy) c).mp hcComm
        have e2 : ⁅c, y⁆ = c * (y * c * y⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e2]
        exact (blockComm L z).mul_mem hcComm ((blockComm L z).inv_mem hycy)
      have hCommTop : blockComm L z = blockU L := le_antisymm hCommLe hsub
      have hle' : blockFix L z ≤ blockComm L z := hCommTop ▸ hFixLe
      calc blockFix L z = blockFix L z ⊓ blockComm L z := (inf_eq_left.mpr hle').symm
        _ = ⊥ := hinf
    refine ⟨hFixBot, ?_⟩
    intro v hv hfix
    have hmem : v ∈ blockFix L z := by
      rw [hmemFix]
      exact ⟨hv, by
        calc z * v = (z * v * z⁻¹) * z := by group
          _ = v * z := by rw [hfix]⟩
    rw [hFixBot, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hzVcent : ∀ v ∈ blockU L, z * v = v * z := by
      intro v hv
      have hmem : v ∈ blockFix L z := hW ▸ hv
      exact (hmemFix.mp hmem).2
    have hz3 : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    have hzPcent : ∀ p ∈ blockQ L, z * p * z⁻¹ = p := by
      intro p hp
      have hv : ⁅z, p⁆ ∈ blockU L := hzPcomm p hp
      have hfix : z * ⁅z, p⁆ * z⁻¹ = ⁅z, p⁆ := by
        have h := hzVcent ⁅z, p⁆ hv
        rw [h]
        group
      have hstep1 : z * p * z⁻¹ = ⁅z, p⁆ * p := by
        rw [commutatorElement_def]
        group
      have hstep2 : z * (z * p * z⁻¹) * z⁻¹ = p := by
        rw [hstep1]
        calc z * (⁅z, p⁆ * p) * z⁻¹ = (z * ⁅z, p⁆ * z⁻¹) * (z * p * z⁻¹) := by group
          _ = ⁅z, p⁆ * (⁅z, p⁆ * p) := by rw [hfix, hstep1]
          _ = p := by
            rw [← mul_assoc, ← pow_two, S.blockU_sq hv, one_mul]
      calc z * p * z⁻¹ = z * (z * (z * p * z⁻¹) * z⁻¹) * z⁻¹ := by rw [hstep2]
        _ = p := by
          have hz3' : z * z * z = 1 := by rw [← pow_three', hz3]
          have hzinv : z⁻¹ * z⁻¹ * z⁻¹ = 1 := by
            have h := congrArg Inv.inv hz3'
            simpa [mul_inv_rev, mul_assoc] using h
          calc z * (z * (z * p * z⁻¹) * z⁻¹) * z⁻¹
              = (z * z * z) * p * (z⁻¹ * z⁻¹ * z⁻¹) := by group
            _ = 1 * p * 1 := by rw [hz3', hzinv]
            _ = p := by group
    have hzmem : z ∈ blockQ L :=
      CFSG.RankThree.PartTwo.Sec19.SolSeven.inf_centralizer_le_of_fitting
        (G := G) (Y := L) S.short.generalizedFitting_eq
        ⟨hzL, Subgroup.mem_centralizer_iff.mpr fun p hp => by
          have h := hzPcent p hp
          calc p * z = (z * p * z⁻¹) * z := by rw [h]
            _ = z * p := by group⟩
    exact hzP hzmem


theorem isElementaryAbelian_tildeU : CFSG.IsElementaryAbelian 2 (tildeU L) := by
  have hcomm : ∀ a b : tildeU L, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (S.blockU_comm a.2 b.2)
  refine { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      exact S.blockU_sq a.2)
    rw [h2]
    rfl

theorem blockZ_eq_bot : blockZ L = ⊥ := by
  obtain ⟨α, z, -, -, -, -, hzord, hzP, hzW, hzPcomm⟩ := exists_order_three_data' S
  have h := (blockFix_bot_and_fpf S z.2 hzord hzP hzW hzPcomm).1
  have hZle : blockZ L ≤ blockFix L (z : G) := by
    intro w hw
    rw [blockFix, Subgroup.mem_inf]
    refine ⟨hw.1, ?_⟩
    exact Subgroup.centralizer_le (s := ({(z : G)} : Set G)) (t := (L : Set G))
      (fun x hx => hx ▸ z.2) hw.2
  rw [h] at hZle
  exact le_bot_iff.mp hZle

theorem exists_fpf :
    ∃ z ∈ L, orderOf z = 3 ∧ z ∉ blockQ L ∧
      (∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ blockU L) ∧
      ∀ v ∈ blockU L, z * v * z⁻¹ = v → v = 1 := by
  obtain ⟨α, z, -, -, -, -, hzord, hzP, hzW, hzPcomm⟩ := exists_order_three_data' S
  refine ⟨(z : G), z.2, hzord, hzP, hzW, ?_⟩
  exact (blockFix_bot_and_fpf S z.2 hzord hzP hzW hzPcomm).2

theorem card_blockU : Nat.card (blockU L) = 64 := by
  haveI := isElementaryAbelian_tildeU S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 (tildeU L)).exists_card_eq
  have hrank : CFSG.pRank 2 (tildeU L) = n := CFSG.pRank_eq_of_card_eq_pow (by norm_num) hn
  have hn6 : n = 6 := by rw [← hrank]; exact S.type.2
  have hcard : Nat.card (tildeU L) = 64 := by rw [hn, hn6]; norm_num
  have hZ : Nat.card ↥(blockZ L) = 1 := by rw [blockZ_eq_bot S]; exact Subgroup.card_bot
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((blockZ L).subgroupOf (blockU L))
  rw [show Nat.card (↥(blockU L) ⧸ (blockZ L).subgroupOf (blockU L)) =
      Nat.card (tildeU L) from rfl, hcard,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (blockZ_le_blockU L)).toEquiv, hZ] at h
  omega


theorem mem_blockQ_of_forall_conj_eq {y : G} (hy : y ∈ L)
    (hc : ∀ v ∈ blockU L, y * v * y⁻¹ = v) : y ∈ blockQ L := by
  obtain ⟨α, z, hαsurj, hPle, hcardker, hzker, hzord, hzP, hzW, hzPcomm⟩ :=
    exists_order_three_data' S
  set P0 : Subgroup ↥L := CFSG.pCore 2 ↥L with hP0
  set K : Subgroup ↥L := α.ker with hK
  set N : Subgroup ↥L := (Subgroup.centralizer (blockU L : Set G)).comap L.subtype with hN
  have hNnormal : N.Normal := by
    refine ⟨fun x hx l => ?_⟩
    show l * x * l⁻¹ ∈ N
    rw [hN, Subgroup.mem_comap] at hx ⊢
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hvl : (l : G)⁻¹ * v * (l : G) ∈ blockU L := by
      simpa using CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU
        (L.inv_mem l.2) hv
    have h1 := hx ((l : G)⁻¹ * v * (l : G)) hvl
    show v * ((l : G) * (x : G) * (l : G)⁻¹) = ((l : G) * (x : G) * (l : G)⁻¹) * v
    calc v * ((l : G) * (x : G) * (l : G)⁻¹)
        = (l : G) * (((l : G)⁻¹ * v * (l : G)) * (x : G)) * (l : G)⁻¹ := by group
      _ = (l : G) * ((x : G) * ((l : G)⁻¹ * v * (l : G))) * (l : G)⁻¹ := by
        rw [show (l : G)⁻¹ * v * (l : G) * (x : G) =
          (x : G) * ((l : G)⁻¹ * v * (l : G)) from h1]
      _ = ((l : G) * (x : G) * (l : G)⁻¹) * v := by group
  have hP0N : P0 ≤ N := by
    intro x hx
    rw [hN, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro v hv
    have hxQ : (x : G) ∈ blockQ L :=
      (CFSG.RankThree.PartTwo.Sec19.SolSeven.mem_pCore_iff x).mp hx
    exact (S.blockQ_comm_blockU hxQ hv).symm
  have hyN : (⟨y, hy⟩ : ↥L) ∈ N := by
    rw [hN, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro v hv
    show v * y = y * v
    calc v * y = (y * v * y⁻¹) * y := by rw [hc v hv]
      _ = y * v := by group
  set q : ↥L →* (↥L ⧸ P0) := QuotientGroup.mk' P0 with hq
  have hNbarNormal : (N.map q).Normal :=
    hNnormal.map q (QuotientGroup.mk'_surjective P0)
  have hNbar_ne_top : N.map q ≠ ⊤ := by
    intro htop
    have hcomap := Subgroup.comap_map_eq (f := q) N
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
    have hNtop : N = ⊤ := by
      rw [sup_eq_left.mpr hP0N] at hcomap
      exact hcomap.symm
    have hVbot : blockU L = ⊥ := by
      have hle : ⁅blockU L, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro l hl
        have hlN : (⟨l, hl⟩ : ↥L) ∈ N := hNtop ▸ Subgroup.mem_top _
        rw [hN, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hlN
        exact hlN
      rw [← S.commutator_blockU, hle]
    have hcard1 : Nat.card ↥(blockU L) = 1 := by rw [hVbot, Subgroup.card_bot]
    have h64 := card_blockU S
    rw [h64] at hcard1
    omega
  have hNbar_center : N.map q ≤ Subgroup.center (↥L ⧸ P0) := by
    rcases CFSG.Quasithin.Vol2.Ch10.SecF.C10E4.normal_le_center_or_eq_top' S.quasisimple
      (N.map q) with h | h
    · exact h
    · exact absurd h hNbar_ne_top
  let ab : (↥L ⧸ P0) →* alternatingGroup (Fin 6) := QuotientGroup.lift P0 α hPle
  have habsurj : Function.Surjective ab := by
    intro σ
    obtain ⟨x, rfl⟩ := hαsurj σ
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hab_center :
      (Subgroup.center (↥L ⧸ P0)).map ab ≤ Subgroup.center (alternatingGroup (Fin 6)) := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ha
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨d, rfl⟩ := habsurj b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc d]
  have hcenter_alt : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hNbar_le_ker : N.map q ≤ ab.ker := by
    have h1 : (N.map q).map ab ≤ Subgroup.center (alternatingGroup (Fin 6)) :=
      (Subgroup.map_mono hNbar_center).trans hab_center
    rw [hcenter_alt, Subgroup.map_le_iff_le_comap] at h1
    simpa using h1
  have hNK : N ≤ K := by
    intro x hx
    have hxbar : q x ∈ N.map q := Subgroup.mem_map_of_mem q hx
    have hxker : ab (q x) = 1 := MonoidHom.mem_ker.mp (hNbar_le_ker hxbar)
    rw [hK, MonoidHom.mem_ker]
    exact hxker
  have hNK_eq : N = P0 ∨ N = K := by
    have hP0dvdN : Nat.card P0 ∣ Nat.card N := Subgroup.card_dvd_of_le hP0N
    have hNdvdK : Nat.card N ∣ Nat.card K := Subgroup.card_dvd_of_le hNK
    obtain ⟨t, ht⟩ := hP0dvdN
    have ht3 : t ∣ 3 := by
      have h1 : Nat.card P0 * t ∣ Nat.card P0 * 3 := by
        have hNK' : Nat.card N ∣ 3 * Nat.card P0 := hcardker ▸ hNdvdK
        rw [ht] at hNK'
        rwa [mul_comm 3 (Nat.card P0)] at hNK'
      exact Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos) h1
    rcases (Nat.dvd_prime Nat.prime_three).mp ht3 with ht1 | ht3'
    · left
      have hcardN : Nat.card N = Nat.card P0 := by rw [ht, ht1, mul_one]
      exact (Subgroup.eq_of_le_of_card_ge hP0N (by rw [hcardN])).symm
    · right
      have hcardN : Nat.card N = Nat.card K := by
        rw [ht, ht3', hcardker, Nat.mul_comm]
      exact Subgroup.eq_of_le_of_card_ge hNK (by rw [hcardN])
  rcases hNK_eq with hNP0 | hNKtop
  · have hyP0 : (⟨y, hy⟩ : ↥L) ∈ P0 := hNP0 ▸ hyN
    exact (CFSG.RankThree.PartTwo.Sec19.SolSeven.mem_pCore_iff ⟨y, hy⟩).mp hyP0
  · exfalso
    have hzN : z ∈ N := hNKtop ▸ hzker
    have hzcent : ∀ v ∈ blockU L, (z : G) * v = v * (z : G) := by
      intro v hv
      have hzN' : (z : G) ∈ Subgroup.centralizer (blockU L : Set G) :=
        Subgroup.mem_comap.mp hzN
      exact (Subgroup.mem_centralizer_iff.mp hzN' v hv).symm
    have hfpf := (blockFix_bot_and_fpf S z.2 hzord hzP hzW hzPcomm).2
    have hVnt : blockU L ≠ ⊥ := by
      intro hbot
      have h64 := card_blockU S
      rw [hbot, Subgroup.card_bot] at h64
      omega
    haveI : Nontrivial ↥(blockU L) := (Subgroup.nontrivial_iff_ne_bot (blockU L)).mpr hVnt
    obtain ⟨v, hv, hv1⟩ := Subgroup.exists_ne_one_of_nontrivial (blockU L)
    exact hv1 (hfpf v hv (by rw [hzcent v hv]; group))


theorem exists_mul_of_mem_blockQ {p : G} (hp : p ∈ blockQ L) :
    ∃ c ∈ blockQ L ⊓ Subgroup.centralizer (L : Set G), ∃ v ∈ blockU L, p = c * v := by
  obtain ⟨α, zL, hαsurj, hPle, hcardker, hzker, hzord, hzP, hzW, hzPcomm⟩ :=
    exists_order_three_data' S
  set z : G := (zL : G) with hz
  have hfpf := (blockFix_bot_and_fpf S zL.2 hzord hzP hzW hzPcomm).2
  let _ : CommGroup ↥(blockU L) := commGroupOfElemAbelian S.elemU
  have hPL : blockQ L ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hpL : p ∈ L := hPL hp
  let σ : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun v => ⟨z * (v : G) * z⁻¹,
        CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU zL.2 v.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, zpow_neg_one]
        group }
  let ψ : ↥(blockU L) → ↥(blockU L) := fun v => v⁻¹ * σ v
  have hψinj : Function.Injective ψ := by
    intro v1 v2 h
    have hσ : σ v2 = v2 * v1⁻¹ * σ v1 := by
      have := congrArg (fun t => v2 * t) h
      simpa [ψ, mul_assoc] using this.symm
    have h2 : σ (v2 * v1⁻¹) = v2 * v1⁻¹ := by
      rw [map_mul, map_inv, hσ]
      group
    have hfix : z * ((v2 * v1⁻¹ : ↥(blockU L)) : G) * z⁻¹ =
        ((v2 * v1⁻¹ : ↥(blockU L)) : G) := congrArg Subtype.val h2
    have hw1 : ((v2 * v1⁻¹ : ↥(blockU L)) : G) = 1 :=
      hfpf _ ((blockU L).mul_mem v2.2 ((blockU L).inv_mem v1.2)) hfix
    have hthis : v2 * v1⁻¹ = 1 := Subtype.ext hw1
    exact (mul_inv_eq_one.mp hthis).symm
  have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
  set θ : G := p⁻¹ * (z * p * z⁻¹) with hθ
  have hθV : θ ∈ blockU L := by
    have h1 : ⁅z, p⁆ ∈ blockU L := hzPcomm p hp
    have e : θ = p⁻¹ * ⁅z, p⁆ * p := by
      rw [hθ, commutatorElement_def]
      group
    rw [e]
    simpa using CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU
      (L.inv_mem hpL) h1
  obtain ⟨v, hv⟩ := hψsurj ⟨θ⁻¹, (blockU L).inv_mem hθV⟩
  have hθpv : (p * (v : G))⁻¹ * (z * (p * (v : G)) * z⁻¹) = 1 := by
    have hvval : ((ψ v : ↥(blockU L)) : G) = θ⁻¹ := congrArg Subtype.val hv
    have hvval' : (v : G)⁻¹ * (z * (v : G) * z⁻¹) = θ⁻¹ := by
      simpa [ψ, σ] using hvval
    calc (p * (v : G))⁻¹ * (z * (p * (v : G)) * z⁻¹)
        = (v : G)⁻¹ * (p⁻¹ * (z * p * z⁻¹)) * (z * (v : G) * z⁻¹) := by group
      _ = (v : G)⁻¹ * (z * (v : G) * z⁻¹) * θ := by
          rw [← hθ]
          have hvz : z * (v : G) * z⁻¹ ∈ blockU L :=
            CFSG.RankThree.PartTwo.Sec19.SolSeven.conj_mem_blockU zL.2 v.2
          calc (v : G)⁻¹ * θ * (z * (v : G) * z⁻¹)
              = (v : G)⁻¹ * (θ * (z * (v : G) * z⁻¹)) := by group
            _ = (v : G)⁻¹ * ((z * (v : G) * z⁻¹) * θ) := by rw [S.blockU_comm hθV hvz]
            _ = (v : G)⁻¹ * (z * (v : G) * z⁻¹) * θ := by group
      _ = θ⁻¹ * θ := by rw [hvval']
      _ = 1 := inv_mul_cancel θ
  set c : G := p * (v : G) with hc
  have hcP : c ∈ blockQ L := (blockQ L).mul_mem hp (S.blockU_le_blockQ v.2)
  have hcZ : z * c * z⁻¹ = c := by
    have h := hθpv
    rw [hc]
    calc z * (p * (v : G)) * z⁻¹ = (p * (v : G)) * ((p * (v : G))⁻¹ *
        (z * (p * (v : G)) * z⁻¹)) := by group
      _ = p * (v : G) := by rw [h]; group
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcyV : ⁅c, y⁆ ∈ blockU L := Subgroup.commutator_mem_commutator hcP hy
    have hcyfix : z * ⁅c, y⁆ * z⁻¹ = ⁅c, y⁆ := by
      have hv1 : y⁻¹ * z * y * z⁻¹ ∈ blockU L := by
        simpa using hzW y⁻¹ (L.inv_mem hy)
      have hzy : z * y * z⁻¹ = y * (y⁻¹ * z * y * z⁻¹) := by group
      have hcv1 : ⁅c, y⁻¹ * z * y * z⁻¹⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (S.blockQ_comm_blockU hcP hv1)
      calc z * ⁅c, y⁆ * z⁻¹ = ⁅z * c * z⁻¹, z * y * z⁻¹⁆ := by
            simpa using conjugate_commutatorElement (g₁ := c) (g₂ := y) (g₃ := z)
        _ = ⁅c, y * (y⁻¹ * z * y * z⁻¹)⁆ := by rw [hcZ, hzy]
        _ = ⁅c, y⁆ := by
            rw [commutatorElement_mul_right_eq_mul_conj, hcv1]
            group
    have hcy1 : ⁅c, y⁆ = 1 := hfpf ⁅c, y⁆ hcyV hcyfix
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcy1).symm
  refine ⟨c, ⟨hcP, hcL⟩, (v : G)⁻¹, (blockU L).inv_mem v.2, ?_⟩
  rw [hc]
  group


theorem blockQ_comm {a b : G} (ha : a ∈ blockQ L) (hb : b ∈ blockQ L) : a * b = b * a := by
  obtain ⟨ca, ⟨hcaP, hcaL⟩, va, hva, rfl⟩ := exists_mul_of_mem_blockQ S ha
  obtain ⟨cb, ⟨hcbP, hcbL⟩, vb, hvb, rfl⟩ := exists_mul_of_mem_blockQ S hb
  have hPL : blockQ L ≤ L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hVL : blockU L ≤ L := fun v hv => hPL (S.blockU_le_blockQ hv)
  have e1 : ca * cb = cb * ca :=
    (Subgroup.mem_centralizer_iff.mp hcaL cb (hPL hcbP)).symm
  have e2 : ca * vb = vb * ca :=
    (Subgroup.mem_centralizer_iff.mp hcaL vb (hVL hvb)).symm
  have e3 : va * cb = cb * va :=
    (S.blockQ_comm_blockU hcbP hva).symm
  have e4 : va * vb = vb * va := S.blockU_comm hva hvb
  calc ca * va * (cb * vb)
      = ca * (va * cb) * vb := by group
    _ = ca * (cb * va) * vb := by rw [e3]
    _ = ca * cb * (va * vb) := by group
    _ = cb * ca * (vb * va) := by rw [e1, e4]
    _ = cb * (ca * vb) * va := by group
    _ = cb * (vb * ca) * va := by rw [e2]
    _ = cb * vb * (ca * va) := by group

end CFSG.CGT.Hall82.Setting

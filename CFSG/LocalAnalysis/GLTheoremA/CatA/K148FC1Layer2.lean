module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148FTwoGlue
import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
import CFSG.RankThree.PartTwo.Sec19.SimsC198G2
import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagL2
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.RankThree.PartTwo.Sec4.Ronan148SBasic
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148FC1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem k148fc1_sl2_eq_one_of_commute {F : Type*} [Field F] [CharP F 2]
    {A B : Matrix.SpecialLinearGroup (Fin 2) F} (hA3 : A ^ 3 = 1) (hB2 : B ^ 2 = 1) (hB1 : B ≠ 1)
    (hAB : A * B = B * A) : A = 1 := by
  by_contra hA1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, b, c, d, hAm⟩ : ∃ a b c d : F, (A : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨e, g, h, k, hBm⟩ : ∃ e g h k : F, (B : Matrix (Fin 2) (Fin 2) F) = !![e, g; h, k] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdetA : a * d - b * c = 1 := by
    have := A.2
    rw [hAm, Matrix.det_fin_two_of] at this
    exact this
  have hA3m : !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] = 1 := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hA3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
    rw [← hAm, ← this, pow_three']
  have hA1m : !![a, b; c, d] ≠ 1 := by
    intro hm
    apply hA1
    ext i j
    rw [hAm, hm, Matrix.SpecialLinearGroup.coe_one]
  have htr := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.trace_eq_neg_one_of_pow_three hdetA hA3m hA1m
  have hB2m : !![e, g; h, k] * !![e, g; h, k] = 1 := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hB2
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
    rw [← hBm, ← this, pow_two]
  have hABm : !![a, b; c, d] * !![e, g; h, k] = !![e, g; h, k] * !![a, b; c, d] := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) hAB
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rw [← hAm, ← hBm]
    exact this
  have b00 := congrFun (congrFun hB2m 0) 0
  have b01 := congrFun (congrFun hB2m 0) 1
  have b10 := congrFun (congrFun hB2m 1) 0
  have b11 := congrFun (congrFun hB2m 1) 1
  have c01 := congrFun (congrFun hABm 0) 1
  have c10 := congrFun (congrFun hABm 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at b00 b01 b10 b11 c01 c10
  have hfin : a = d → False := by
    intro had
    have : (1 : F) = 0 := by linear_combination htr + had - a * h2
    exact one_ne_zero this
  by_cases hg : g = 0
  · by_cases hh : h = 0
    · apply hB1
      subst hg hh
      have he : e = 1 := by
        have : (e - 1) ^ 2 = 0 := by linear_combination b00 + (1 - e) * h2
        exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
      have hk : k = 1 := by
        have : (k - 1) ^ 2 = 0 := by linear_combination b11 + (1 - k) * h2
        exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)
      subst he hk
      ext i j
      rw [hBm, Matrix.SpecialLinearGroup.coe_one]
      fin_cases i <;> fin_cases j <;> simp
    ·
      have hke : e + k = 0 := by
        have : h * (e + k) = 0 := by linear_combination b10
        exact (mul_eq_zero.1 this).resolve_left hh
      have hke' : k = e := by linear_combination hke - e * h2
      subst hke'
      apply hfin
      have : h * (d - a) = 0 := by linear_combination c10
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hh)).symm
  ·
    have hke : e + k = 0 := by
      have : g * (e + k) = 0 := by linear_combination b01
      exact (mul_eq_zero.1 this).resolve_left hg
    have hke' : k = e := by linear_combination hke - e * h2
    subst hke'
    apply hfin
    have : g * (a - d) = 0 := by linear_combination c01
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hg)

theorem k148fc1_sl2_nonabelian (F : Type*) [Field F] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro h
  have h00 : (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 0) h
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h00
  norm_num at h00
  have : (1 : F) = 0 := by linear_combination h00
  exact one_ne_zero this

theorem k148fc1_center_eq_bot {X : Type*} [Group X] [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem k148fc1_commutator_self {P : Type*} [Group P] {H : Subgroup P} [IsSimpleGroup ↥H]
    (hna : ∃ a b : ↥H, a * b ≠ b * a) : ⁅H, H⁆ = H := by
  have htop : commutator ↥H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥H) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  have hm := Subgroup.map_commutator (⊤ : Subgroup ↥H) ⊤ H.subtype
  rw [← commutator_def, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
  exact hm.symm

theorem k148fc1_map_centralizer {A P : Type*} [Group A] [Group P] {F : Subgroup P} (e : A ≃* ↥F) (z : A) :
    (Subgroup.centralizer ({z} : Set A)).map (F.subtype.comp e.toMonoidHom) =
      F ⊓ Subgroup.centralizer ({((e z : ↥F) : P)} : Set P) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ha
    refine ⟨(e a).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    show ((e a : ↥F) : P) * (e z : ↥F) = (e z : ↥F) * (e a : ↥F)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ha]
  · intro hx'
    obtain ⟨hxF, hx⟩ := Subgroup.mem_inf.1 hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨e.symm ⟨x, hxF⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hx
    · show ((e (e.symm ⟨x, hxF⟩) : ↥F) : P) = x
      rw [MulEquiv.apply_symm_apply]

private theorem k148fc1_pquot_not_comm {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hM : GLAPComponent 3 X M) (hc : ∀ a b : PQuot 3 M, a * b = b * a) : False := by
  obtain ⟨hcQ, hsQ⟩ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hM
  haveI := hsQ.toNontrivial
  haveI : Nontrivial (PQuot 3 M) :=
    CFSG.LocalAnalysis.GLTheoremA.K148FTwo.nontrivial_of_quotient (Subgroup.center (PQuot 3 M))
  have h : commutator (PQuot 3 M) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hc y x
  rw [hcQ] at h
  exact top_ne_bot h

private theorem k148fc1_card_psimple_of_simple {G : Type} [Group G] [Finite G] {X N M : Subgroup G}
    (hNX : N ≤ X) (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ N) (hN : IsSimpleGroup ↥N)
    (h3 : 3 ∣ Nat.card N) (hM : GLAPComponent 3 X M) : Nat.card (PSimple 3 M) = Nat.card N := by
  classical
  have hQ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hM
  obtain ⟨hMX, hIS, -, -⟩ := id hM
  have hNM : N ≤ M := by
    have hsub := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.isSubnormal_inf N hIS
    rw [inf_eq_right.2 hNX] at hsub
    haveI := hN
    rcases CFSG.LocalAnalysis.GLTheoremA.K148FTwo.subnormal_eq_bot_or_top_of_simple N hsub rfl with h0 | h1
    · exfalso
      refine k148fc1_pquot_not_comm hM fun x y => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ M ⊓ N :=
        ⟨M.mul_mem (M.mul_mem (M.mul_mem a.2 b.2) (M.inv_mem a.2)) (M.inv_mem b.2),
          hcomm a (hMX a.2) b (hMX b.2)⟩
      rw [h0, Subgroup.mem_bot] at hc
      have hab : a * b = b * a := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        calc (a : G) * b = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ * (b * a) := by group
          _ = b * a := by rw [hc, one_mul]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab]
    · calc N = M ⊓ N := h1.symm
        _ ≤ M := inf_le_left
  set φ : ↥N →* PQuot 3 M := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (Subgroup.inclusion hNM)
    with hφ
  have hsurj : Function.Surjective φ := by
    have hle : commutator (PQuot 3 M) ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨⟨(a : G) * b * (a : G)⁻¹ * (b : G)⁻¹, hcomm a (hMX a.2) b (hMX b.2)⟩, ?_⟩
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, commutatorElement_def,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
    rw [hQ.1] at hle
    exact MonoidHom.range_eq_top.1 (top_le_iff.1 hle)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hle : (⊤ : Subgroup ↥N).map (Subgroup.inclusion hNM) ≤ GLAPPrimeCore 3 ↥M := by
        rintro _ ⟨n, -, rfl⟩
        have hn : n ∈ φ.ker := h ▸ Subgroup.mem_top n
        rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hn
        exact (QuotientGroup.eq_one_iff _).1 hn
      have hcard := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hNM), Subgroup.card_top] at hcard
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop (h3.trans hcard)
  let e₁ : ↥N ≃* PQuot 3 M := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI : IsSimpleGroup (PQuot 3 M) := e₁.symm.isSimpleGroup
  have hZ : Subgroup.center (PQuot 3 M) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PQuot 3 M)) with h | h
    · exact h
    · exfalso
      refine k148fc1_pquot_not_comm hM fun a b => ?_
      have hb : b ∈ Subgroup.center (PQuot 3 M) := h ▸ Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
  show Nat.card (PQuot 3 M ⧸ Subgroup.center (PQuot 3 M)) = Nat.card ↥N
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv,
    Nat.card_congr e₁.symm.toEquiv]

private theorem k148fc1_card_psimple_of_quasisimple {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hXq : CFSG.IsQuasisimple ↥X) (hZ : IsPGroup 3 (Subgroup.center ↥X)) (h3 : 3 ∣ Nat.card X)
    (hM : GLAPComponent 3 X M) : Nat.card (PSimple 3 M) * Nat.card (Subgroup.center ↥X) = Nat.card X := by
  classical
  have hO : GLAPPrimeCore 3 ↥X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.pPrimeCore_three_eq_bot_of_isQuasisimple hXq h3 hZ
  obtain ⟨hMX, hIS, hMq⟩ := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.pComp_facts hO hM
  have hsub : (M.subgroupOf X).IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hMX).1 hIS
  have hMeq : M = X := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hXq hsub with h | h
    · exact le_antisymm hMX fun x hx => by
        have : (⟨x, hx⟩ : ↥X) ∈ M.subgroupOf X := h ▸ Subgroup.mem_top _
        exact this
    · exfalso
      obtain ⟨hcM, hsM⟩ := hMq
      haveI := hsM.toNontrivial
      haveI : Nontrivial ↥M :=
        CFSG.LocalAnalysis.GLTheoremA.K148FTwo.nontrivial_of_quotient (Subgroup.center ↥M)
      have hc : commutator ↥M = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        have hb : (⟨(b : G), hMX b.2⟩ : ↥X) ∈ Subgroup.center ↥X :=
          h (Subgroup.mem_subgroupOf.2 b.2)
        have := Subgroup.mem_center_iff.1 hb ⟨(a : G), hMX a.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      rw [hcM] at hc
      exact top_ne_bot hc
  subst hMeq
  let eP : PQuot 3 M ≃* ↥M := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  let eS : PSimple 3 M ≃* ↥M ⧸ Subgroup.center ↥M :=
    QuotientGroup.congr (Subgroup.center (PQuot 3 M)) (Subgroup.center ↥M) eP
      (by rw [← Subgroup.map_center_eq eP])
  rw [Nat.card_congr eS.toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥M)).symm

private theorem k148fc1_g2_order_ne {a : ℕ} (ha : 1 ≤ a) :
    CFSG.Open.ordG2 (2 ^ a) ≠ 60 ∧ ∀ n : ℕ, 1 ≤ n → CFSG.Open.ordG2 (2 ^ a) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hodd : Odd (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) :=
    (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one ha (by norm_num)).mul
      (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one ha (by norm_num))
  have heq : CFSG.Open.ordG2 (2 ^ a) = 2 ^ (6 * a) * (((2 ^ a) ^ 6 - 1) * ((2 ^ a) ^ 2 - 1)) := by
    unfold CFSG.Open.ordG2
    rw [show 2 ^ (6 * a) = (2 ^ a) ^ 6 by rw [mul_comm, pow_mul], mul_assoc]
  refine ⟨fun h => ?_, fun n hn h => ?_⟩
  · rw [heq] at h
    have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h60] at h
    have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd (by decide) h).1
    omega
  · rw [heq] at h
    have hodd' : Odd ((2 ^ n) ^ 2 - 1) :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd hodd' h
    subst h1
    obtain ⟨r, hr⟩ : ∃ r : ℕ, r = (2 ^ a) ^ 2 := ⟨_, rfl⟩
    have hr4 : 4 ≤ r := by
      rw [hr, ← pow_mul]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : (2 ^ a) ^ 6 = r ^ 3 := by rw [hr]; ring
    have e2 : (2 ^ (6 * a)) ^ 2 = r ^ 6 := by rw [hr, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    rw [e1, ← hr, e2] at h2
    have h3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by omega)
    have hz : ((r : ℤ) ^ 3 - 1) * ((r : ℤ) - 1) = (r : ℤ) ^ 6 - 1 := by
      have := congrArg (fun x : ℕ => (x : ℤ)) h2
      push_cast [Nat.cast_sub h3, Nat.cast_sub h6, Nat.cast_sub (show 1 ≤ r by omega)] at this
      linarith
    have hr' : (4 : ℤ) ≤ r := by exact_mod_cast hr4
    nlinarith [sq_nonneg ((r : ℤ) ^ 2), sq_nonneg ((r : ℤ))]

private theorem k148fc1_sl3_card_ne {f : ℕ} (hf : 2 ≤ f) {X z P : ℕ} (ε : Bool)
    (hX : X = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1))
    (hz : Odd z) (hP : P * z = X) : P ≠ 60 ∧ ∀ n : ℕ, 1 ≤ n → P ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hf1 : 1 ≤ f := by omega
  have hoddX : Odd (((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    refine (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf1 (by norm_num)).mul ?_
    cases ε
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_add_one hf1 (by norm_num)
    · exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hf1 (by norm_num)
  have hX' : X = 2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1)) := by
    rw [hX, show 2 ^ (3 * f) = (2 ^ f) ^ 3 by rw [mul_comm, pow_mul], mul_assoc]
  refine ⟨fun h => ?_, fun n hn h => ?_⟩
  · rw [h, hX'] at hP
    have e : 60 * z = 2 ^ 2 * (15 * z) := by ring
    rw [e] at hP
    have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj ((by decide : Odd 15).mul hz)
      hoddX hP).1
    omega
  · rw [h, hX'] at hP
    have hodd' : Odd ((2 ^ n) ^ 2 - 1) :=
      CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one hn (by norm_num)
    have e : 2 ^ n * ((2 ^ n) ^ 2 - 1) * z = 2 ^ n * (((2 ^ n) ^ 2 - 1) * z) := by ring
    rw [e] at hP
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj (hodd'.mul hz) hoddX hP
    subst h1
    set q := 2 ^ f with hq
    have hq4 : 4 ≤ q := by
      rw [hq]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have e6 : (2 ^ (3 * f)) ^ 2 = q ^ 6 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
    rw [e6] at h2
    have hz1 : 1 ≤ z := hz.pos
    have hle : ((q ^ 2 - 1) * cond ε (q ^ 3 - 1) (q ^ 3 + 1)) ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := by
      apply Nat.mul_le_mul_left
      cases ε <;> simp <;> omega
    have hlt : (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 6 - 1 := by
      have h2 : 16 ≤ q ^ 2 := by nlinarith
      have h3 : 64 ≤ q ^ 3 := by nlinarith
      have e : q ^ 6 = q ^ 3 * q ^ 3 := by ring
      have e2 : q ^ 3 = q * q ^ 2 := by ring
      zify [show 1 ≤ q ^ 2 by omega, show 1 ≤ q ^ 6 by nlinarith]
      push_cast
      nlinarith
    have hge : q ^ 6 - 1 ≤ (q ^ 6 - 1) * z := Nat.le_mul_of_pos_right _ hz1
    omega

private theorem k148fc1_three_dvd_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f

private theorem k148fc1_layer {P : Type} [Group P] [Finite P] {X M₀ : Subgroup P} [IsSimpleGroup ↥M₀]
    (hna : ∃ a b : ↥M₀, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥M₀) (hle : M₀ ≤ X) (hcomm : ⁅X, X⁆ ≤ M₀) :
    GLAPComponent 3 X M₀ ∧ (∀ M : Subgroup P, GLAPComponent 3 X M → M = M₀) ∧ M₀ = ⁅X, X⁆ := by
  have hnorm : (M₀.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : P) * n * (g : P)⁻¹ * (n : P)⁻¹ ∈ M₀ := by
      have := Subgroup.commutator_mem_commutator g.2 n.2
      rw [commutatorElement_def] at this
      exact hcomm this
    have he : ((g * n * g⁻¹ : ↥X) : P) = ((g : P) * n * (g : P)⁻¹ * (n : P)⁻¹) * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [he]
    exact M₀.mul_mem hc hn
  have hq : CFSG.Open.IsQuasisimple ↥M₀ := GL83.PiGen.isQuasisimple_of_simple_nonabelian hna
  refine ⟨GL83.PiGen.glaPComponent_of_normal_simple Nat.prime_three hle hnorm hna h3,
    fun M hM => CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.eq_of_glaPComponent_of_commutator_le hle hq hcomm hM,
    ?_⟩
  refine le_antisymm ?_ hcomm
  calc M₀ = ⁅M₀, M₀⁆ := (k148fc1_commutator_self hna).symm
    _ ≤ ⁅X, X⁆ := Subgroup.commutator_mono hle hle

private theorem k148fc1_not_inner {P : Type} [Group P] [Finite P] {M₀ : Subgroup P} [IsSimpleGroup ↥M₀]
    (hna : ∃ a b : ↥M₀, a * b ≠ b * a) (hO : GLAPPrimeCore 3 ↥M₀ = ⊥)
    {F : Type} [Field F] [CharP F 2] (eSLM : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥M₀)
    (ψ : ↥M₀ ≃* ↥M₀) (hψ3 : ψ ^ 3 = 1) (φ : MulAut (PQuot 3 M₀))
    (hφmk : ∀ m : ↥M₀, φ (QuotientGroup.mk m) = QuotientGroup.mk (ψ m))
    (hfix : (∀ m : ↥M₀, ψ m = m) → False)
    (s : ↥M₀) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hψs : ψ s = s) :
    ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ := by
  rintro ⟨y, hy⟩
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : Function.Injective (QuotientGroup.mk : ↥M₀ → PQuot 3 M₀) := by
    intro a b hab
    rw [QuotientGroup.eq, hO, Subgroup.mem_bot] at hab
    exact inv_mul_eq_one.1 hab
  have hψ : ∀ m : ↥M₀, ψ m = y' * m * y'⁻¹ := by
    intro m
    apply hmk
    rw [← hφmk, ← hy, MulAut.conj_apply]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  by_cases hy1 : y' = 1
  · apply hfix
    intro m
    rw [hψ, hy1]
    group
  · have hy3 : y' ^ 3 = 1 := by
      have hc : ∀ m : ↥M₀, y' ^ 3 * m * (y' ^ 3)⁻¹ = m := by
        intro m
        have h := congrArg (fun α : MulAut ↥M₀ => α m) hψ3
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
        rw [hψ, hψ, hψ] at h
        calc y' ^ 3 * m * (y' ^ 3)⁻¹ = y' * (y' * (y' * m * y'⁻¹) * y'⁻¹) * y'⁻¹ := by
              simp only [pow_three, mul_inv_rev, mul_assoc]
          _ = m := h
      have hZ := k148fc1_center_eq_bot hna
      have hmem : y' ^ 3 ∈ Subgroup.center ↥M₀ := Subgroup.mem_center_iff.2 fun m => by
        calc m * y' ^ 3 = y' ^ 3 * m * (y' ^ 3)⁻¹ * y' ^ 3 := by rw [hc m]
          _ = y' ^ 3 * m := by rw [inv_mul_cancel_right]
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    have hcomm : y' * s = s * y' := by
      have h := hψ s
      rw [hψs] at h
      calc y' * s = y' * s * y'⁻¹ * y' := by group
        _ = s * y' := by rw [← h]
    apply hy1
    have hA := k148fc1_sl2_eq_one_of_commute (A := eSLM.symm y') (B := eSLM.symm s)
      (by rw [← map_pow, hy3, map_one]) (by rw [← map_pow, hs2, map_one])
      (fun h => hs1 (by rw [← eSLM.apply_symm_apply s, h, map_one]))
      (by rw [← map_mul, ← map_mul, hcomm])
    rw [← eSLM.apply_symm_apply y', hA, map_one]

private theorem k148fc1_sl2_proj {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F)) ∧
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
        CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) := by
  haveI := CFSG.SeitzReduction.LinearPilot.isSimpleGroup_specialLinearGroup_two h4
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    k148fc1_center_eq_bot (k148fc1_sl2_nonabelian F)
  let e₁ : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let e₂ := e₁.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F)
  refine ⟨⟨e₂⟩, ?_⟩
  have key : ∀ {H₁ H₂ : Subgroup (GL (Fin 2) F)}, H₁ = H₂ → Nonempty (StatedProj H₁ ≃* StatedProj H₂) := by
    intro H₁ H₂ h
    subst h
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨e₃⟩ := key (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := F) 2).symm
  exact ⟨e₂.trans e₃⟩

private theorem k148fc1_l2_card_ne {f : ℕ} (hf : 2 ≤ f) :
    (2 ^ (3 * f) * ((2 ^ (3 * f)) ^ 2 - 1) : ℕ) ≠ 60 ∧
      (2 ^ (3 * f) * ((2 ^ (3 * f)) ^ 2 - 1) : ℕ) ≠ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hodd1 : Odd ((2 ^ (3 * f)) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (by omega) (by norm_num)
  have hodd2 : Odd ((2 ^ f) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (by omega) (by norm_num)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num] at h
    have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd1 (by decide) h).1
    omega
  · have := (CFSG.LocalAnalysis.GLTheoremA.CatDistinct.two_pow_mul_odd_inj hodd1 hodd2 h).1
    omega

section FieldAut


theorem k148fc1_fieldAut {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m)
    {Q : Type} [Group Q] [IsSimpleGroup Q] (hna : ∃ a b : Q, a * b ≠ b * a)
    (θ₀ : Q ≃* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F))
    (φ : MulAut Q) (hφ3 : φ ^ 3 = 1) (hφi : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ) :
    K148FFieldAut 3 Q φ := by
  classical
  have hZ : Subgroup.center Q = ⊥ := k148fc1_center_eq_bot hna
  have hQ : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  let eZ : Q ⧸ Subgroup.center Q ≃* Q := (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have heZ : ∀ l : Q, eZ (QuotientGroup.mk l) = l := fun l => rfl
  let θ : Q ⧸ Subgroup.center Q ≃* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F) :=
    eZ.trans θ₀
  have hθ : ∀ l : Q, θ (QuotientGroup.mk l) = θ₀ l := fun l => by
    show θ₀ (eZ (QuotientGroup.mk l)) = θ₀ l
    rw [heZ]
  let ψ : MulAut (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) := MulAut.congr θ₀ φ
  have hψ : ∀ l : Q, ψ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (φ l)) := fun l => by
    rw [hθ, hθ]
    show θ₀ (φ (θ₀.symm (θ₀ l))) = θ₀ (φ l)
    rw [MulEquiv.symm_apply_apply]
  have hψ3 : ψ ^ 3 = 1 := by
    show (MulAut.congr θ₀ φ) ^ 3 = 1
    rw [← map_pow, hφ3, map_one]
  have hψI : ψ ∉ CFSG.Assembly.LargeEvenMatConjImage
      (CFSG.Assembly.LargeEvenProjMk (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) Set.univ := by
    intro hmem
    obtain ⟨r, hr⟩ := CFSG.LocalAnalysis.GLTheoremA.i112d_conj_of_mem_conjImage (m := m) (by omega) hF hmem
    apply hφi
    refine ⟨θ₀.symm r, MulEquiv.ext fun l => ?_⟩
    apply θ₀.injective
    have h := congrArg (fun α : MulAut (CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSLGroup (Fin 2) F)) => α (θ₀ l)) hr
    simp only [MulAut.conj_apply] at h
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h]
    show θ₀ (φ (θ₀.symm (θ₀ l))) = θ₀ (φ l)
    rw [MulEquiv.symm_apply_apply]
  have hlab : CFSG.Assembly.LargeEvenInLambda2 ⟨.A, 1, m⟩ :=
    ⟨show 1 ≤ m by omega, le_rfl, fun _ => hm⟩
  have hD : CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, m⟩ fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ' : Q ⧸ Subgroup.center Q ≃* R, ∃ ψ' : MulAut R,
        (∀ l : Q, ψ' (θ' (QuotientGroup.mk l)) = θ' (QuotientGroup.mk (φ l))) ∧ ψ' ∉ I ∧ ψ' ^ 3 = 1 := by
    refine (CFSG.LocalAnalysis.GLTheoremA.i112d_rawDatum_A_iff 1 m _).2 ⟨F, inferInstance, inferInstance, hF, ?_⟩
    refine ⟨θ₀.symm.isSimpleGroup, ?_, θ, ψ, hψ, hψI, hψ3⟩
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨θ₀ a, θ₀ b, fun h => hab (θ₀.injective (by rw [map_mul, map_mul, h]))⟩
  have hA := CFSG.LocalAnalysis.GLTheoremA.FP.canonOddAut (p := 3) Nat.prime_three (by norm_num) hlab
    (by simp)
  have hB := CFSG.LocalAnalysis.GLTheoremA.FP.canonRawFieldConj (p := 3) Nat.prime_three (by norm_num) hlab
    (by simp)
  have hD' := hB _ (hA _ hD)
  refine ⟨hQ, ⟨.A, 1, m⟩, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hD'⟩
  rintro R _ I F' ⟨⟨⟨hs, hna', θ', ψ', hψ', hψ'I, hψ'3⟩, hodd⟩, hconj⟩
  obtain ⟨u, hu, f, hf, huf⟩ := hodd hs hna' ψ' hψ'3
  have hnot : u * f ∉ I := huf ▸ hψ'I
  have hpow : (u * f) ^ 3 = 1 := huf ▸ hψ'3
  obtain ⟨f', hf', u', hu', hord, heq⟩ := hconj hs hna' u hu f hf hnot hpow
  refine ⟨hs, hna', θ', Or.inl (by simp), f', hf', u', hu', hord, ?_⟩
  intro l l' hll'
  rw [← heq, ← huf, hψ', hll']

end FieldAut

section Certified


private theorem k148fc1_card_l2n {S : Type} [Group S] [Finite S] {n : ℕ} (h : catalogIs S (isL2n n)) :
    (n = 2 ∧ Nat.card S = 60) ∨ (1 ≤ n ∧ Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | alternating m hm =>
    obtain ⟨hn, rfl⟩ : n = 2 ∧ m = 5 := hi
    left
    refine ⟨hn, ?_⟩
    rw [CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hm e]
    decide
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact (show False from hi).elim
      · obtain ⟨hp, hn⟩ : q.p = 2 ∧ q.exponent = n := hi
        right
        refine ⟨hn ▸ q.exponent_pos, ?_⟩
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 1 q, hv⟩ S ⟨e⟩]
        show CFSG.Open.orderA 1 q.card = _
        rw [TauCeti.PrimePower.card_def, hp, hn]
        exact CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderA_one_eq (hn ▸ q.exponent_pos)
      · exact (show False from hi).elim
    | _ => exact (show False from hi).elim

private theorem k148fc1_g2_long {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {z : CFSG.Blueprint.Chevalley.adjointGroup .G2 F} (hz3 : z ^ 3 = 1)
    {M : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)}
    (hM : GLAPComponent 3 (Subgroup.centralizer ({z} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) M)
    {n : ℕ} (hL : catalogIs (PSimple 3 M) (isL2n n)) :
    z ≠ 1 ∧ ∃ g : CFSG.Blueprint.Chevalley.adjointGroup .G2 F,
      g * z * g⁻¹ ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 F := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hf1 : 1 ≤ f := by omega
  have h3G : ∀ a : ℕ, 3 ∣ CFSG.Open.ordG2 (2 ^ a) := fun a => by
    unfold CFSG.Open.ordG2
    exact Dvd.dvd.mul_left (k148fc1_three_dvd_sq_sub_one a) _
  by_cases hz1 : z = 1
  ·
    exfalso
    subst hz1
    have hXtop : Subgroup.centralizer ({(1 : CFSG.Blueprint.Chevalley.adjointGroup .G2 F)} :
        Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) = ⊤ :=
      Subgroup.ext fun x => by simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hXtop] at hM
    haveI : IsSimpleGroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
      CFSG.QuasithinUnique.Id2519.isSimpleGroup_adjointGroup_g2 (by omega)
    have hN : IsSimpleGroup ↥(⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
      Subgroup.topEquiv.isSimpleGroup
    have hcardG : Nat.card ↥(⊤ : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) =
        CFSG.Open.ordG2 (2 ^ f) := by
      rw [Subgroup.card_top, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    have hPS := k148fc1_card_psimple_of_simple le_rfl (fun a _ b _ => Subgroup.mem_top _) hN
      (by rw [hcardG]; exact h3G f) hM
    rw [hcardG] at hPS
    obtain ⟨h60, hL2⟩ := k148fc1_g2_order_ne hf1
    rcases k148fc1_card_l2n hL with ⟨-, h⟩ | ⟨hn, h⟩
    · exact h60 (hPS.symm.trans h)
    · exact hL2 n hn (hPS.symm.trans h)
  refine ⟨hz1, ?_⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds F hchar3 h4 z hz3 hz1
  rcases hg with hS | hLg
  ·
    exfalso
    have hιinj : Function.Injective ((MulAut.conj g : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 F →* CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
      (MulAut.conj g).injective
    have hCmap : (Subgroup.centralizer ({z} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))).map
        ((MulAut.conj g : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :
          CFSG.Blueprint.Chevalley.adjointGroup .G2 F →* CFSG.Blueprint.Chevalley.adjointGroup .G2 F) =
        Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
      CFSG.RankThree.PartTwo.Sec4.Ronan148S.map_centralizer_singleton_equiv (MulAut.conj g) z
    have hM' := (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hιinj 3 _ _).2 hM
    rw [hCmap] at hM'
    have hL' := (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff hιinj 3 M _).2 hL
    have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, ← map_pow, hz3, map_one]
    have hz'1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : MulAut.conj g z = MulAut.conj g 1 := by rw [map_one]; exact h
      exact (MulAut.conj g).injective this
    obtain ⟨-, ⟨K', _, _, hK'⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec12.Hering129L.g2_centralizer_threeA hchar3 h4 hS hz'3 hz'1
    obtain ⟨hq, -⟩ := CFSG.RankThree.PartTwo.Sec19.SimsC198.G2.centralizer_threeA hchar h4 hS hz'3 hz'1
    obtain ⟨ε, hcardC, hzC⟩ : ∃ ε : Bool,
        Nat.card ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) =
          (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * cond ε ((2 ^ f) ^ 3 - 1) ((2 ^ f) ^ 3 + 1) ∧
        Nat.card (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)))) = 3 := by
      rcases hK' with ⟨hK'c, hq1, ⟨e⟩⟩ | ⟨hK'c, hq2, ⟨e⟩⟩
      · refine ⟨true, ?_, ?_⟩
        · rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hK'c, hF]
          simp only [cond_true, mul_assoc]
        · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
          exact CFSG.Open.StatedCenterThree.card_center_statedSL_three (by rw [hK'c]; omega)
      · refine ⟨false, ?_, ?_⟩
        · rw [Nat.card_congr e.toEquiv,
            CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK'c, hF]
          simp only [cond_false]
        · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
          exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hK'c (by omega)
    have hZ3 : IsPGroup 3 (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)))) :=
      IsPGroup.of_card (n := 1) (by rw [hzC, pow_one])
    have h3C : 3 ∣ Nat.card ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) :=
      hzC ▸ Subgroup.card_subgroup_dvd_card _
    have hPS := k148fc1_card_psimple_of_quasisimple hq hZ3 h3C hM'
    have hodd : Odd (Nat.card (Subgroup.center ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))))) := by
      rw [hzC]; decide
    obtain ⟨h60, hL2⟩ := k148fc1_sl3_card_ne hf ε hcardC hodd hPS
    rcases k148fc1_card_l2n hL' with ⟨-, h⟩ | ⟨hn, h⟩
    · exact h60 h
    · exact hL2 n hn h
  · exact ⟨g, hLg⟩

private theorem k148fc1_g2_perfect {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {w g : CFSG.Blueprint.Chevalley.adjointGroup .G2 F} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hS : g * w * g⁻¹ ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2ShortSL2 F) :
    commutator ↥(Subgroup.centralizer ({w} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF
  have hchar : ringChar F = 2 := ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hw'3 : (g * w * g⁻¹) ^ 3 = 1 := by
    rw [show g * w * g⁻¹ = MulAut.conj g w from rfl, ← map_pow, hw3, map_one]
  have hw'1 : g * w * g⁻¹ ≠ 1 := by
    intro h
    apply hw1
    have : MulAut.conj g w = MulAut.conj g 1 := by rw [map_one]; exact h
    exact (MulAut.conj g).injective this
  obtain ⟨⟨hperf, -⟩, -⟩ := CFSG.RankThree.PartTwo.Sec19.SimsC198.G2.centralizer_threeA hchar h4 hS hw'3 hw'1
  have hCmap : (Subgroup.centralizer ({w} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))).map
      ((MulAut.conj g : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 F →* CFSG.Blueprint.Chevalley.adjointGroup .G2 F) =
      Subgroup.centralizer ({g * w * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148S.map_centralizer_singleton_equiv (MulAut.conj g) w
  let e : ↥(Subgroup.centralizer ({w} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) ≃*
      ↥(Subgroup.centralizer ({g * w * g⁻¹} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) :=
    (MulEquiv.subgroupMap (MulAut.conj g) _).trans (MulEquiv.subgroupCongr hCmap)
  have h1 : commutator ↥(Subgroup.centralizer ({g * w * g⁻¹} :
      Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F))) = ⊤ := hperf.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥(Subgroup.centralizer ({g * w * g⁻¹} :
      Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)))) ⊤ e.symm.toMonoidHom
  rw [← commutator_def, h1, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.symm.surjective] at h2
  rw [commutator_def]
  exact h2.symm

private theorem k148fc1_three_ne_zero (F : Type*) [Field F] [CharP F 2] : (3 : F) ≠ 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) = 1 := by linear_combination h2
  rw [h3]
  exact one_ne_zero

private theorem k148fc1_fusion {P : Type} [Group P] [Finite P] {f : ℕ} (hf : 2 ≤ f)
    {F : Subgroup P} (hFG2 : catalogIs ↥F (isG2n f)) {c t₀ : P} (hcF : c ∈ F) (hc3 : c ^ 3 = 1)
    {S' : Subgroup P} (hS' : GLAPComponent 3 (F ⊓ Subgroup.centralizer ({c} : Set P)) S') {n : ℕ}
    (hS'L : catalogIs (PSimple 3 S') (isL2n n))
    (ht₀F : t₀ ∈ F) (ht₀3 : t₀ ^ 3 = 1) (ht₀1 : t₀ ≠ 1)
    (ht₀np : commutator ↥(F ⊓ Subgroup.centralizer ({t₀} : Set P)) ≠ ⊤) :
    ∃ x ∈ F, c = x * t₀ * x⁻¹ := by
  classical
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.T266.G2Holds.g2_adjoint_equiv hFG2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₂ : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : CharP (GaloisField 2 f) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hK₂
  have hchar3 : ringChar (GaloisField 2 f) ≠ 3 := by rw [ringChar.eq (GaloisField 2 f) 2]; norm_num
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK₂]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let ι : CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f) →* P := F.subtype.comp e.toMonoidHom
  have hιapp : ∀ a, ι a = ((e a : ↥F) : P) := fun a => rfl
  have hιinj : Function.Injective ι := F.subtype_injective.comp e.injective
  have hιrange : ι.range = F := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      rw [hιapp, MulEquiv.apply_symm_apply]
  obtain ⟨z, hz⟩ : ∃ z, z = e.symm ⟨c, hcF⟩ := ⟨_, rfl⟩
  have hιz : ι z = c := by rw [hιapp, hz, MulEquiv.apply_symm_apply]
  have hz3 : z ^ 3 = 1 := hιinj (by rw [map_pow, hιz, hc3, map_one])
  have hmapz := k148fc1_map_centralizer e z
  rw [← hιapp, hιz] at hmapz
  have hS'le : S' ≤ ι.range := hιrange ▸ hS'.1.trans inf_le_left
  obtain ⟨M, rfl⟩ : ∃ M : Subgroup (CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)),
      M.map ι = S' := ⟨_, Subgroup.map_comap_eq_self hS'le⟩
  rw [← hmapz] at hS'
  have hM := (CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hιinj 3 _ _).1 hS'
  have hML := (CFSG.LocalAnalysis.GLTheoremA.T123C.catalogIs_pSimple_map_iff hιinj 3 M _).1 hS'L
  obtain ⟨hz1, g₁, hg₁⟩ := k148fc1_g2_long hK₂ hf hz3 hM hML
  obtain ⟨w, hw⟩ : ∃ w, w = e.symm ⟨t₀, ht₀F⟩ := ⟨_, rfl⟩
  have hιw : ι w = t₀ := by rw [hιapp, hw, MulEquiv.apply_symm_apply]
  have hw3 : w ^ 3 = 1 := hιinj (by rw [map_pow, hιw, ht₀3, map_one])
  have hw1 : w ≠ 1 := fun h => ht₀1 (by rw [← hιw, h, map_one])
  obtain ⟨g₂, hg₂⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds (GaloisField 2 f)
    hchar3 h4 w hw3 hw1
  rcases hg₂ with hS | hL
  ·
    exfalso
    apply ht₀np
    have hperf := k148fc1_g2_perfect hK₂ hf hw3 hw1 hS
    have hmapw := k148fc1_map_centralizer e w
    rw [← hιapp, hιw] at hmapw
    let eW : ↥(Subgroup.centralizer ({w} : Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)))) ≃*
        ↥(F ⊓ Subgroup.centralizer ({t₀} : Set P)) :=
      (Subgroup.equivMapOfInjective _ ι hιinj).trans (MulEquiv.subgroupCongr hmapw)
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥(Subgroup.centralizer ({w} :
      Set (CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f))))) ⊤ eW.toMonoidHom
    rw [← commutator_def, hperf, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 eW.surjective] at h2
    rw [commutator_def]
    exact h2.symm
  ·
    obtain ⟨eL⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := GaloisField 2 f)
    have hc3' : ∀ (g y : CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)), y ^ 3 = 1 →
        (g * y * g⁻¹) ^ 3 = 1 := fun g y hy => by rw [conj_pow, hy, mul_one, mul_inv_cancel]
    have hc1' : ∀ (g y : CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)), y ≠ 1 →
        g * y * g⁻¹ ≠ 1 := fun g y hy h => hy (by
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group)
    obtain ⟨B, hB⟩ : ∃ B, B = eL.symm ⟨g₂ * w * g₂⁻¹, hL⟩ := ⟨_, rfl⟩
    obtain ⟨B', hB'⟩ : ∃ B', B' = eL.symm ⟨g₁ * z * g₁⁻¹, hg₁⟩ := ⟨_, rfl⟩
    have heB : ((eL B : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) = g₂ * w * g₂⁻¹ := by
      rw [hB, MulEquiv.apply_symm_apply]
    have heB' : ((eL B' : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) = g₁ * z * g₁⁻¹ := by
      rw [hB', MulEquiv.apply_symm_apply]
    have hpow : ∀ X : CFSG.LieType.Chevalley.SL2 (GaloisField 2 f),
        ((eL X : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
          CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) ^ 3 = 1 → X ^ 3 = 1 := by
      intro X hX
      apply eL.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hX)
    have hne : ∀ X : CFSG.LieType.Chevalley.SL2 (GaloisField 2 f),
        ((eL X : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
          CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) ≠ 1 → X ≠ 1 := by
      intro X hX h
      apply hX
      rw [h, map_one]
      rfl
    have hB3 : B ^ 3 = 1 := hpow B (by rw [heB]; exact hc3' g₂ w hw3)
    have hB1 : B ≠ 1 := hne B (by rw [heB]; exact hc1' g₂ w hw1)
    have hB'3 : B' ^ 3 = 1 := hpow B' (by rw [heB']; exact hc3' g₁ z hz3)
    have hB'1 : B' ≠ 1 := hne B' (by rw [heB']; exact hc1' g₁ z hz1)
    obtain ⟨A, hA⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three
      (k148fc1_three_ne_zero (GaloisField 2 f)) hB3 hB1 hB'3 hB'1
    have hhw : ((eL A : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) * (g₂ * w * g₂⁻¹) *
          ((eL A : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
            CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f))⁻¹ = g₁ * z * g₁⁻¹ := by
      rw [← heB, ← heB', ← hA, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
    refine ⟨ι (g₁⁻¹ * ((eL A : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
      CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) * g₂), (e _).2, ?_⟩
    have hzk : z = (g₁⁻¹ * ((eL A : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
        CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) * g₂) * w *
        (g₁⁻¹ * ((eL A : ↥(CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.g2LongSL2 (GaloisField 2 f))) :
          CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField 2 f)) * g₂)⁻¹ := by
      calc z = g₁⁻¹ * (g₁ * z * g₁⁻¹) * g₁ := by group
        _ = _ := by rw [← hhw]; group
    rw [← hιz, hzk, map_mul, map_mul, map_inv, hιw]

theorem k148fc1_core {P : Type} [Group P] [Finite P] {f : ℕ} (hf : 2 ≤ f)
    (τ : MulAut P) (hτ3 : τ ^ 3 = 1)
    (hFG2 : catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) (isG2n f))
    {S : Subgroup P} {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = 2 ^ (3 * f))
    (eSL : Matrix.SpecialLinearGroup (Fin 2) F' ≃* ↥S)
    {t₀ : P} (ht₀S : t₀ ∈ Subgroup.centralizer (S : Set P)) (ht₀τ : τ t₀ = t₀) (ht₀3 : t₀ ^ 3 = 1)
    (ht₀1 : t₀ ≠ 1)
    (hB : ∀ t ∈ Subgroup.centralizer (S : Set P), t ^ 3 = 1 → t ≠ 1 →
      ∀ x ∈ Subgroup.centralizer ({t} : Set P), ∀ y ∈ Subgroup.centralizer ({t} : Set P),
        x * y * x⁻¹ * y⁻¹ ∈ S)
    (c : P) (hc3 : c ^ 3 = 1) (hτc : τ c = c)
    (hS' : ∃ S' : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓
        Subgroup.centralizer ({c} : Set P)) S' ∧ catalogIs (PSimple 3 S') (isL2n f)) :
    ∃ M₀ : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M₀ ∧
      (∀ M : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M → M = M₀) ∧
      catalogIs (PSimple 3 M₀) (isL2n (3 * f)) ∧ (∀ m ∈ M₀, τ m ∈ M₀) ∧
      ∃ φ : MulAut (PQuot 3 M₀), φ ^ 3 = 1 ∧ ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ ∧
        (∀ m : M₀, ∃ m' : M₀, (m' : P) = τ⁻¹ m ∧ φ (QuotientGroup.mk m) = QuotientGroup.mk m') ∧
        K148FFieldAut 3 (PQuot 3 M₀) φ := by
  classical
  obtain ⟨S', hS'c, hS'L⟩ := hS'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hF'
  have h4F' : 4 ≤ Nat.card F' := by
    rw [hF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F') :=
    CFSG.SeitzReduction.LinearPilot.isSimpleGroup_specialLinearGroup_two h4F'
  haveI : IsSimpleGroup ↥S := eSL.symm.isSimpleGroup
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := k148fc1_sl2_nonabelian F'
    exact ⟨eSL a, eSL b, fun h => hab (eSL.injective (by rw [map_mul, map_mul, h]))⟩
  have hcardS : Nat.card ↥S = 2 ^ (3 * f) * ((2 ^ (3 * f)) ^ 2 - 1) := by
    rw [← Nat.card_congr eSL.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF',
      show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton]
    norm_num
  have ht₀nS : t₀ ∉ S := by
    intro hmem
    have hZ := k148fc1_center_eq_bot hSna
    have hc : (⟨t₀, hmem⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun s =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 ht₀S s s.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact ht₀1 (congrArg Subtype.val hc)
  have hcommt : ⁅Subgroup.centralizer ({t₀} : Set P), Subgroup.centralizer ({t₀} : Set P)⁆ ≤ S :=
    Subgroup.commutator_le.2 fun x hx y hy => by
      rw [commutatorElement_def]
      exact hB t₀ ht₀S ht₀3 ht₀1 x hx y hy
  have ht₀np : commutator ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓ Subgroup.centralizer ({t₀} : Set P)) ≠ ⊤ := by
    intro htop
    apply ht₀nS
    have hmem : t₀ ∈ CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓ Subgroup.centralizer ({t₀} : Set P) :=
      ⟨CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 ht₀τ, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    have h1 : (⟨t₀, hmem⟩ : ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓
        Subgroup.centralizer ({t₀} : Set P))) ∈
        commutator ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓ Subgroup.centralizer ({t₀} : Set P)) :=
      htop ▸ Subgroup.mem_top _
    have h2 := Subgroup.mem_map_of_mem (CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓
      Subgroup.centralizer ({t₀} : Set P)).subtype h1
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact hcommt (Subgroup.commutator_mono inf_le_right inf_le_right h2)
  obtain ⟨x, -, hcx⟩ := k148fc1_fusion hf hFG2 (CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 hτc) hc3 hS'c hS'L
    (CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 ht₀τ) ht₀3 ht₀1 ht₀np
  have hCc : (Subgroup.centralizer ({t₀} : Set P)).map ((MulAut.conj x : MulAut P) : P →* P) =
      Subgroup.centralizer ({c} : Set P) := by
    rw [CFSG.RankThree.PartTwo.Sec4.Ronan148S.map_centralizer_singleton_equiv (MulAut.conj x) t₀,
      MulAut.conj_apply, ← hcx]
  have hSle : S ≤ Subgroup.centralizer ({t₀} : Set P) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 ht₀S s hs)
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : Subgroup P, M₀ = S.map ((MulAut.conj x : MulAut P) : P →* P) := ⟨_, rfl⟩
  have hM₀le : M₀ ≤ Subgroup.centralizer ({c} : Set P) := by
    rw [hM₀, ← hCc]
    exact Subgroup.map_mono hSle
  have hcommc : ⁅Subgroup.centralizer ({c} : Set P), Subgroup.centralizer ({c} : Set P)⁆ ≤ M₀ := by
    rw [hM₀, ← hCc, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcommt
  let eM : ↥S ≃* ↥M₀ := (MulEquiv.subgroupMap (MulAut.conj x) S).trans (MulEquiv.subgroupCongr hM₀.symm)
  haveI : IsSimpleGroup ↥M₀ := eM.symm.isSimpleGroup
  have hM₀na : ∃ a b : ↥M₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSna
    exact ⟨eM a, eM b, fun h => hab (eM.injective (by rw [map_mul, map_mul, h]))⟩
  have hcardM₀ : Nat.card ↥M₀ = 2 ^ (3 * f) * ((2 ^ (3 * f)) ^ 2 - 1) := by
    rw [← Nat.card_congr eM.toEquiv, hcardS]
  have h3M₀ : 3 ∣ Nat.card ↥M₀ := by
    rw [hcardM₀]
    exact Dvd.dvd.mul_left (k148fc1_three_dvd_sq_sub_one _) _
  obtain ⟨hM₀comp, hM₀uniq, hM₀eq⟩ := k148fc1_layer hM₀na h3M₀ hM₀le hcommc
  have hO : GLAPPrimeCore 3 ↥M₀ = ⊥ := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.gLAPPrimeCore_eq_bot_of_simple ↥M₀ h3M₀
  have hZM₀ : Subgroup.center ↥M₀ = ⊥ := k148fc1_center_eq_bot hM₀na
  have hαM : ∀ α : MulAut P, α c = c → ∀ m ∈ M₀, α m ∈ M₀ := by
    intro α hα m hm
    have hXα : (Subgroup.centralizer ({c} : Set P)).map (α : P →* P) ≤ Subgroup.centralizer ({c} : Set P) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      show α y * c = c * α y
      calc α y * c = α y * α c := by rw [hα]
        _ = α (y * c) := (map_mul α y c).symm
        _ = α (c * y) := by rw [hy]
        _ = α c * α y := map_mul α c y
        _ = c * α y := by rw [hα]
    have hmap : (⁅Subgroup.centralizer ({c} : Set P), Subgroup.centralizer ({c} : Set P)⁆).map (α : P →* P) ≤
        ⁅Subgroup.centralizer ({c} : Set P), Subgroup.centralizer ({c} : Set P)⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hXα hXα
    rw [hM₀eq] at hm ⊢
    exact hmap (Subgroup.mem_map_of_mem _ hm)
  have hτM : ∀ m ∈ M₀, τ m ∈ M₀ := hαM τ hτc
  have hτiM : ∀ m ∈ M₀, τ⁻¹ m ∈ M₀ := hαM τ⁻¹ (by
    calc τ⁻¹ c = τ⁻¹ (τ c) := by rw [hτc]
      _ = c := MulAut.inv_apply_self P τ c)
  let ψ : ↥M₀ ≃* ↥M₀ :=
    { toFun := fun m => ⟨τ⁻¹ m, hτiM m m.2⟩
      invFun := fun m => ⟨τ m, hτM m m.2⟩
      left_inv := fun m => Subtype.ext (MulAut.apply_inv_self P τ m)
      right_inv := fun m => Subtype.ext (MulAut.inv_apply_self P τ m)
      map_mul' := fun a b => Subtype.ext (map_mul τ⁻¹ (a : P) b) }
  have hψapp : ∀ m : ↥M₀, ((ψ m : ↥M₀) : P) = τ⁻¹ m := fun m => rfl
  have hψ3 : ψ ^ 3 = 1 := by
    refine MulEquiv.ext fun m => Subtype.ext ?_
    have h := congrArg (fun α : MulAut P => α (m : P)) (show τ⁻¹ ^ 3 = 1 by rw [inv_pow, hτ3, inv_one])
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h ⊢
    rw [hψapp, hψapp, hψapp]
    exact h
  let φ : MulAut (PQuot 3 M₀) :=
    QuotientGroup.congr (GLAPPrimeCore 3 ↥M₀) (GLAPPrimeCore 3 ↥M₀) ψ (by rw [hO, Subgroup.map_bot])
  have hφmk : ∀ m : ↥M₀, φ (QuotientGroup.mk m) = QuotientGroup.mk (ψ m) := fun m =>
    QuotientGroup.congr_mk _ _ _ _ m
  have hφ3 : φ ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have h := congrArg (fun α : MulAut ↥M₀ => α m) hψ3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h ⊢
    rw [hφmk, hφmk, hφmk, h]
  have hS'X : S' ≤ Subgroup.centralizer ({c} : Set P) := hS'c.1.trans inf_le_right
  have hS'F : ∀ s ∈ S', τ s = s := fun s hs =>
    CFSG.RankThree.PartTwo.Sec4.mem_autFix.1 ((hS'c.1.trans inf_le_left) hs)
  have hS'M₀ : S' ≤ M₀ := by
    rw [← CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hS'c]
    exact (Subgroup.commutator_mono hS'X hS'X).trans hcommc
  have hS'even : 2 ∣ Nat.card ↥S' := by
    have hdvd : Nat.card (PSimple 3 S') ∣ Nat.card ↥S' :=
      (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
    refine dvd_trans ?_ hdvd
    rcases k148fc1_card_l2n hS'L with ⟨-, h⟩ | ⟨hn, h⟩
    · rw [h]; norm_num
    · rw [h]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥S') 2 hS'even
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hfix : (∀ m : ↥M₀, ψ m = m) → False := by
    intro hid
    have hM₀F : M₀ ≤ CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓ Subgroup.centralizer ({c} : Set P) := by
      intro m hm
      refine ⟨CFSG.RankThree.PartTwo.Sec4.mem_autFix.2 ?_, hM₀le hm⟩
      have h := congrArg Subtype.val (hid ⟨m, hm⟩)
      rw [hψapp] at h
      calc τ m = τ (τ⁻¹ m) := by rw [h]
        _ = m := MulAut.apply_inv_self P τ m
    have hsub := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.isSubnormal_inf M₀ hS'c.2.1
    rw [inf_eq_left.2 hS'M₀, inf_eq_right.2 hM₀F] at hsub
    rcases CFSG.LocalAnalysis.GLTheoremA.K148FTwo.subnormal_eq_bot_or_top_of_simple M₀ hsub rfl with h0 | h1
    · rw [h0, Subgroup.card_bot] at hS'even
      norm_num at hS'even
    · subst h1
      obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.psimple_nonempty_mulEquiv S' hO hZM₀
      rw [← Nat.card_congr eP.toEquiv] at hcardM₀
      obtain ⟨h60, hL2⟩ := k148fc1_l2_card_ne hf
      rcases k148fc1_card_l2n hS'L with ⟨-, h⟩ | ⟨-, h⟩
      · exact h60 (hcardM₀.symm.trans h)
      · exact hL2 (hcardM₀.symm.trans h)
  have hφi : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ :=
    k148fc1_not_inner hM₀na hO (eSL.trans eM) ψ hψ3 φ hφmk hfix ⟨s, hS'M₀ s.2⟩
      (Subtype.ext (by simpa using congrArg Subtype.val hs2))
      (fun h => hs1 (Subtype.ext (by simpa using congrArg Subtype.val h)))
      (Subtype.ext (by
        rw [hψapp]
        calc τ⁻¹ (s : P) = τ⁻¹ (τ s) := by rw [hS'F s s.2]
          _ = s := MulAut.inv_apply_self P τ s))
  obtain ⟨⟨eSt⟩, ⟨eLE⟩⟩ := k148fc1_sl2_proj (F := F') h4F'
  let eP : PQuot 3 M₀ ≃* ↥M₀ := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  obtain ⟨ePS⟩ := CFSG.LocalAnalysis.GLTheoremA.K148FTwo.psimple_nonempty_mulEquiv M₀ hO hZM₀
  have hcat : catalogIs (PSimple 3 M₀) (isL2n (3 * f)) :=
    CFSG.LocalAnalysis.GLTheoremA.l2c_catalog_of_iso (by omega) hF'
      (ePS.trans (eM.symm.trans (eSL.symm.trans eSt)))
  haveI : IsSimpleGroup (PQuot 3 M₀) := eP.isSimpleGroup
  have hQna : ∃ a b : PQuot 3 M₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hM₀na
    exact ⟨eP.symm a, eP.symm b, fun h => hab (eP.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hFA : K148FFieldAut 3 (PQuot 3 M₀) φ :=
    k148fc1_fieldAut (m := 3 * f) (by omega) hF' hQna (eP.trans (eM.symm.trans (eSL.symm.trans eLE)))
      φ hφ3 hφi
  exact ⟨M₀, hM₀comp, hM₀uniq, hcat, hτM, φ, hφ3, hφi, fun m => ⟨ψ m, hψapp m, hφmk m⟩, hFA⟩

end Certified

end CFSG.LocalAnalysis.GLTheoremA.K148FC1

end

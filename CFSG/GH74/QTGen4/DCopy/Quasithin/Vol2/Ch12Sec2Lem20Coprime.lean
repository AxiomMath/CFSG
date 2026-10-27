module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Coprime
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem20Pick
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

open Lem20Coprime Lem20Pick in

theorem coprimePick_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h325 : Stmt3_2_5_F4) (h1216 : Stmt12_2_16_F4) (h12218 : Stmt12_2_18_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) : CoprimePick_F4 := by
  intro G _ _ T L V H P p hyp hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2

  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hinv2 : ∀ {y : G}, y ^ 2 = 1 → y⁻¹ = y := fun hy =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy])
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv2 (hV2 _ (V.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv2 (hV2 y hy), hinv2 (hV2 x hx)]
  have hcV : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩
  have hVe : IsElemAbelian 2 V := ⟨hcV, hV2⟩
  have hTH : T ≤ H := hHs.1.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes

  have hZ : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p := by
    obtain ⟨q, -, -, hZq⟩ :=
      (Lem7.minParabolic_F4 h331 hyp hHs).subgroupOf.exists_odd_prime_of_solvable hsolv
    have hP1 : P ≠ ⊥ := by
      intro h0
      apply hHs.2.1
      rw [hHPT, h0, bot_sup_eq]
      exact hTM
    have hpH : p ∣ Nat.card H := by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := hPp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hP1 (Subgroup.eq_bot_of_card_eq P hk)
      have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
      rw [hk] at h1
      exact (dvd_pow_self p hk0).trans h1
    have hpq : p = q := (hZq p hp hpH).resolve_left hp2
    intro r hr hrH
    rw [hpq]
    exact hZq r hr hrH

  obtain ⟨v₀, hv₀V, hv₀O⟩ := IsConcreteLE.not_le_iff_exists.mp (h12218 G T L V hyp hNE H hHs)
  have hv₀H : v₀ ∈ H := hTH (hVT hv₀V)
  have hv₀1 : v₀ ≠ 1 := fun h0 => hv₀O (h0 ▸ Subgroup.one_mem _)
  obtain ⟨y, hyH, hy1, hyodd, hyinv⟩ :
      ∃ y ∈ H, y ≠ 1 ∧ Odd (orderOf y) ∧ v₀ * y * v₀⁻¹ = y⁻¹ := by
    set w : ↥H := ⟨v₀, hv₀H⟩
    have hw2 : w ^ 2 = 1 := Subtype.ext (by simpa using hV2 v₀ hv₀V)
    have hw1 : w ≠ 1 := fun h0 => hv₀1 (congrArg Subtype.val h0)
    have hcard : Nat.card (Subgroup.zpowers w) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1]
    have hnot : ¬ Subgroup.zpowers w ≤ CFSG.Open.pCore 2 ↥H := fun hle =>
      hv₀O ⟨w, hle (Subgroup.mem_zpowers w), rfl⟩
    obtain ⟨y, hy1, hyo, hyi⟩ := baer_suzuki_involution hcard hnot
    refine ⟨y, y.2, fun h0 => hy1 (Subtype.ext h0), by rwa [Subgroup.orderOf_coe], ?_⟩
    simpa using congrArg Subtype.val (hyi w (Subgroup.mem_zpowers w) hw1)
  have hpy : p ∣ orderOf y := by
    have hy1' : orderOf y ≠ 1 := fun h0 => hy1 (orderOf_eq_one_iff.mp h0)
    have hdvd : orderOf y ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hyH
    rcases hZ _ (Nat.minFac_prime hy1') ((Nat.minFac_dvd _).trans hdvd) with h2 | h2
    · exfalso
      have h2y : 2 ∣ orderOf y := by
        rw [← h2]
        exact Nat.minFac_dvd _
      exact Nat.not_even_iff_odd.mpr hyodd (even_iff_two_dvd.mpr h2y)
    · rw [← h2]
      exact Nat.minFac_dvd _
  set h₀ := y ^ (orderOf y / p) with hh₀
  have hoh₀ : orderOf h₀ = p := orderOf_pow_orderOf_div (orderOf_pos y).ne' hpy
  have hh₀H : h₀ ∈ H := H.pow_mem hyH _
  have hh₀p : h₀ ^ p = 1 := by
    rw [← hoh₀]
    exact pow_orderOf_eq_one h₀
  have hh₀inv : v₀ * h₀ * v₀⁻¹ = h₀⁻¹ := by rw [hh₀, ← conj_pow, hyinv, inv_pow]

  have hTi : ¬ 2 ∣ T.relIndex H := (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH).2.2
  obtain ⟨t, htT, htP⟩ :=
    exists_conj_mem_of_pi hp hp2 hZ hPp hPH hPi hyp.sylow.1 hTH hTi hh₀H hh₀p
  set h := t⁻¹ * h₀ * t with hh
  set v := t⁻¹ * v₀ * t with hv
  have hvV : v ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) v₀).mp hv₀V
    simpa using this
  have hhH : h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hTH htT)) hh₀H) (hTH htT)
  have hhp : h ^ p = 1 := by rw [hh, inv_conj_pow, hh₀p, mul_one, inv_mul_cancel]
  have hh1 : h ≠ 1 := by
    intro h0
    have h0' : h₀ = 1 := by
      have e : h₀ = t * h * t⁻¹ := by rw [hh]; group
      rw [e, h0, mul_one, mul_inv_cancel]
    rw [h0', orderOf_one] at hoh₀
    exact hp.one_lt.ne hoh₀
  have hvh : v * h * v⁻¹ = h⁻¹ := by
    calc v * h * v⁻¹ = t⁻¹ * (v₀ * h₀ * v₀⁻¹) * t := by rw [hv, hh]; group
      _ = h⁻¹ := by rw [hh₀inv, hh]; group
  have hv2 : v ^ 2 = 1 := hV2 v hvV
  have hvinv : v⁻¹ = v := hinv2 hv2
  have hvh' : v * h⁻¹ * v = h := by
    calc v * h⁻¹ * v = v * h⁻¹ * v⁻¹ := by rw [hvinv]
      _ = (v * h * v⁻¹)⁻¹ := by group
      _ = h := by rw [hvh, inv_inv]

  have hhN : h ∉ Subgroup.normalizer (V : Set G) := by
    intro hN
    have h1 : h * v⁻¹ * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN _).mp (V.inv_mem hvV)
    have h2 : v * (h * v⁻¹ * h⁻¹) ∈ V := V.mul_mem hvV h1
    have e : v * (h * v⁻¹ * h⁻¹) = h⁻¹ * h⁻¹ := by
      calc v * (h * v⁻¹ * h⁻¹) = (v * h * v⁻¹) * h⁻¹ := by group
        _ = h⁻¹ * h⁻¹ := by rw [hvh]
    rw [e] at h2
    have h3 := hV2 _ h2
    apply hh1
    refine eq_one_of_pow_four hp hp2 hhp ?_
    have h4 : (h ^ 4)⁻¹ = 1 := by
      rw [← h3]
      group
    simpa using h4

  have hhM : h ∉ Subgroup.normalizer (L : Set G) := by
    intro hhM'
    obtain ⟨-, ⟨hcomm, -⟩, -⟩ := h325 G T L V hyp.fsu hyp.conjClosure_eq.symm
    have hVT0 : conjClosure V T = V :=
      le_antisymm (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTV ht) l).1 hl)
        (le_conjClosure V T)
    rw [hVT0] at hcomm
    have hvVM : v ∈ conjClosure V (Subgroup.normalizer (L : Set G)) :=
      le_conjClosure V _ hvV
    have hv'VM : h⁻¹ * v * h ∈ conjClosure V (Subgroup.normalizer (L : Set G)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V _ (Subgroup.inv_mem _ hhM')) v).mp hvVM
      simpa using h1
    have hc : Commute v (h⁻¹ * v * h) := by
      have := congrArg Subtype.val (hcomm.is_comm.comm ⟨v, hvVM⟩ ⟨_, hv'VM⟩)
      exact this
    have e : v * (h⁻¹ * v * h) = h ^ 2 := by
      calc v * (h⁻¹ * v * h) = (v * h⁻¹ * v) * h := by group
        _ = h ^ 2 := by rw [hvh', pow_two]
    have hw2 : (h⁻¹ * v * h) ^ 2 = 1 := by rw [inv_conj_pow, hv2, mul_one, inv_mul_cancel]
    have h4 : h ^ 4 = 1 := by
      calc h ^ 4 = (v * (h⁻¹ * v * h)) ^ 2 := by rw [e, ← pow_mul]
        _ = v ^ 2 * (h⁻¹ * v * h) ^ 2 := hc.mul_pow 2
        _ = 1 := by rw [hv2, hw2, one_mul]
    exact hh1 (eq_one_of_pow_four hp hp2 hhp h4)

  have hvN : v ∉ Subgroup.normalizer (CFSG.conjugate V h : Set G) := by
    rw [mem_normalizer_conjugate_iff]
    intro hN
    have hv' : h * v = v * h⁻¹ := by
      have e1 : v⁻¹ * h * v = v * h * v⁻¹ := by rw [hvinv]
      calc h * v = v * (v⁻¹ * h * v) := by group
        _ = v * h⁻¹ := by rw [e1, hvh]
    have e : h * v * h⁻¹ = v * h⁻¹ ^ 2 := by
      rw [hv', mul_assoc, ← pow_two]
    rw [e] at hN
    have h2 : h⁻¹ ^ 2 ∈ Subgroup.normalizer (V : Set G) := by
      have := (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).inv_mem (Subgroup.le_normalizer hvV)) hN
      simpa using this
    have h3 : h⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mem_of_sq_mem hpodd (by rw [inv_pow, hhp, inv_one]) h2
    exact hhN (by simpa using (Subgroup.normalizer (V : Set G)).inv_mem h3)

  set A := CFSG.conjugate V h with hAdef
  have hAmem : ∀ y : G, y ∈ A ↔ h * y * h⁻¹ ∈ V := fun y => Lem21Post.mem_conjugate_iff

  have hU0ne : ASInputs.tiU V A ≠ ⊥ := by
    have hZV := Lem7.omegaOneCenter_inf_ne_bot hyp.sylow.1 hVT hTV hyp.irrPlus.2.1 hV2
    obtain ⟨⟨z, hzZ, hzV⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZV
    have hz1 : z ≠ 1 := fun h0 => hz1' (Subtype.ext h0)
    have hzc : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
      ((Subgroup.closure_le _).mpr fun _ hz => hz.1) hzZ
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.sylow
    have hOT : pCoreOf 2 H ≤ T := by
      rw [← hS]
      exact pCoreOf_two_le_sylow H S (by rw [hS]; exact hTH)
    have hzO : z ∈ pCoreOf 2 H := by
      refine charTwo_of_inH' hyp.qtke hyp.sylow hHs.1 (Subgroup.mem_inf.mpr ⟨hTH hzc.1, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp hzc.2 x (hOT hx)
    have hzN : z ∈ Subgroup.normalizer (A : Set G) := by
      rw [hAdef, mem_normalizer_conjugate_iff]
      have h1 : h * z * h⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hhH) z).mp hzO
      exact hTV (hOT h1)
    intro h0
    apply hz1
    have : z ∈ ASInputs.tiU V A := ⟨hzV, hzN⟩
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hU0lt : ASInputs.tiU V A < V := by
    refine lt_of_le_of_ne inf_le_left fun h0 => hvN ?_
    have : v ∈ ASInputs.tiU V A := by rw [h0]; exact hvV
    exact this.2

  have hA2 : ∀ y ∈ A, y ^ 2 = 1 := fun y hy => by
    have := hV2 _ ((hAmem y).mp hy)
    rw [conj_pow] at this
    simpa using this
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h1 := hVc _ ((hAmem x).mp hx) _ ((hAmem y).mp hy)
    have h2 : h * (x * y) * h⁻¹ = h * (y * x) * h⁻¹ := by
      calc h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = (h * y * h⁻¹) * (h * x * h⁻¹) := h1
        _ = h * (y * x) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hAe : IsElemAbelian 2 A := ⟨⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩, hA2⟩
  have hcard : Nat.card V = Nat.card A :=
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm
  have hTI := h1216 G T L V hyp hNE
  have hTIV : IsTISetIn V ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rcases hTI g with h1 | h1
    · exact absurd (Lem20Pick.mem_normalizer_of_conjugate_eq h1) hg
    · exact h1
  have hAV : A ≠ V := fun h1 => hvN (h1 ▸ Subgroup.le_normalizer hvV)
  have hVA : V ⊓ A = ⊥ := (hTI h).resolve_left hAV
  have hTIA : IsTISetIn A ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSubgroup_iff] at hx2
    have hy1 : h * x * h⁻¹ ∈ V := (hAmem x).mp hx1
    have hy2 : h * (g * x * g⁻¹) * h⁻¹ ∈ V := (hAmem _).mp hx2
    have hk : ∀ y : G, (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ =
        h * (g * y * g⁻¹) * h⁻¹ := fun y => by group
    have hy2' : h * x * h⁻¹ ∈ CFSG.conjugate V (h * g * h⁻¹) := by
      rw [Lem21Post.mem_conjugate_iff, hk]
      exact hy2
    rcases hTI (h * g * h⁻¹) with h1 | h1
    · exfalso
      apply hg
      have hkN := Lem20Pick.mem_normalizer_of_conjugate_eq h1
      rw [Subgroup.mem_normalizer_iff] at hkN ⊢
      intro y
      rw [hAmem, hAmem, ← hk]
      exact hkN _
    · have : h * x * h⁻¹ ∈ V ⊓ CFSG.conjugate V (h * g * h⁻¹) := ⟨hy1, hy2'⟩
      rw [h1, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (by simpa using this)
  have hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥ := by
    intro g hne
    have e : conjSubgroup A g = CFSG.conjugate V (h * g) := conjSubgroup_conjSubgroup V h g
    rw [e, inf_comm]
    exact (hTI (h * g)).resolve_left fun h1 => hne (e.trans h1).symm

  obtain ⟨⟨-, -, hXN, hYv⟩, hYn, hcases⟩ :=
    hI62 G V A hVe hAe hcard hTIV hTIA hcross hU0ne hU0lt
  set U₀ := ASInputs.tiU V A with hU₀
  set Y := ASInputs.tiY V A with hY
  set X := ASInputs.tiX V A with hX
  have hU₀V : U₀ ≤ V := inf_le_left
  have hVX : V ≤ X := le_sup_left
  have hvU₀ : v ∉ U₀ := fun h0 => hvN h0.2
  obtain ⟨hU₀Y, -⟩ := hYv v hvV hvU₀
  have hVY : ∀ y ∈ V, y ∈ Y → y ∈ U₀ := by
    intro y hyV hyY
    have : y ∈ Y ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨hyY, Subgroup.mem_centralizer_singleton_iff.mpr (hVc y hyV v hvV)⟩
    rwa [← hU₀Y] at this

  have hAH : A ≤ H := fun y hy => by
    have h1 : h * y * h⁻¹ ∈ V := (hAmem y).mp hy
    have e : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hhH) (hTH (hVT h1))) hhH
  have hXH : X ≤ H := sup_le (hVT.trans hTH) hAH
  have hZX : ∀ r : ℕ, r.Prime → r ∣ Nat.card (↥X ⧸ Y.subgroupOf X) → r = 2 ∨ r = p :=
    fun r hr hrd => hZ r hr (hrd.trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hXH)))

  set f : ↥V →* ↥X ⧸ Y.subgroupOf X :=
    (QuotientGroup.mk' (Y.subgroupOf X)).comp (Subgroup.inclusion hVX) with hf
  have hker : f.ker = U₀.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h1 => hVY x x.2 h1, fun h1 => Subgroup.mem_sup_left h1⟩
  have hidxf : U₀.relIndex V = Nat.card f.range := by
    show (U₀.subgroupOf V).index = _
    rw [← hker, Subgroup.index_ker]
  have hfp : IsPGroup 2 ↥f.range := by
    rintro ⟨_, x, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hV2' x, map_one]
  obtain ⟨j, hj⟩ := hfp.exists_card_eq
  have hrange : Nat.card f.range ∣ Nat.card (↥X ⧸ Y.subgroupOf X) :=
    Subgroup.card_subgroup_dvd_card _
  have hne1 : U₀.relIndex V ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact (lt_irrefl _ (lt_of_lt_of_le hU0lt h1))
  rcases hcases with ⟨m, hmodd, ⟨e⟩⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  ·
    have hXc : Nat.card (↥X ⧸ Y.subgroupOf X) = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have h4 : 2 ^ 2 ∣ 2 * m := by
        have h5 := hrange
        rw [hj, hXc] at h5
        exact (pow_dvd_pow 2 (by omega)).trans h5
      have h6 : 2 ∣ m := by omega
      exact Nat.not_even_iff_odd.mpr hmodd (even_iff_two_dvd.mpr h6)
    refine ⟨h, v, htP, hhM, hhp, hvV, hvh, hvN, ?_⟩
    rw [hidxf, hj]
    interval_cases j
    · exact absurd (by rw [hidxf, hj]; rfl) hne1
    · rfl
  · exact (false_of_isPSL_two_two hn hZX).elim
  · exact (false_of_isSz hn hZX).elim

theorem lem12220PickFull_of_coprime_F4 (h331 : Stmt3_3_1_F4)
    (h1222 : Stmt12_2_2_F4) (h325 : Stmt3_2_5_F4) (h1216 : Stmt12_2_16_F4) (h12218 : Stmt12_2_18_F4)
    (hI62 : ASInputs.AS_I_6_2_twoCases) : Lem12220PickFull_F4 :=
  lem12220PickFull_of_pick_F4 h331 h1222 h1216 hI62
    (coprimePick_of_F4 h331 h1222 h325 h1216 h12218 hI62)

end CFSG.Quasithin.H13

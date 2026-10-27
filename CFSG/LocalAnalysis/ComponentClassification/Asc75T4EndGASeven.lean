module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGQuot
public import CFSG.Walter.PSL2Facts.Odd
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.GorensteinWalter

theorem perm_fin_seven_orderOf_ne_fifteen (σ : Equiv.Perm (Fin 7)) : orderOf σ ≠ 15 := by
  intro h
  have hlcm := σ.lcm_cycleType
  have hsum : σ.cycleType.sum ≤ 7 := by
    rw [σ.sum_cycleType]
    simpa using Finset.card_le_univ σ.support
  have hmem : ∀ c ∈ σ.cycleType, c = 3 ∨ c = 5 := by
    intro c hc
    have h1 : c ∣ 15 := h ▸ σ.dvd_of_mem_cycleType hc
    have h2 : c ≤ 7 := (Multiset.le_sum_of_mem hc).trans hsum
    have h3 := σ.two_le_of_mem_cycleType hc
    interval_cases c <;> simp_all
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun c hc => by
      rcases hmem c hc with rfl | rfl
      · exact absurd hc h3
      · exact dvd_rfl
    rw [hlcm, h] at this
    norm_num at this
  have h5 : 5 ∈ σ.cycleType := by
    by_contra h5
    have : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun c hc => by
      rcases hmem c hc with rfl | rfl
      · exact dvd_rfl
      · exact absurd hc h5
    rw [hlcm, h] at this
    norm_num at this
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h3
  rw [ht] at h5 hsum
  rw [Multiset.sum_cons] at hsum
  have h5' : 5 ∈ t := (Multiset.mem_cons.mp h5).resolve_left (by norm_num)
  have := Multiset.le_sum_of_mem h5'
  omega

theorem aSeven_exists_three_commute {A : Type} [Group A]
    (e : A ≃* alternatingGroup (Fin 7)) {z : A} (hz : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ y : A, orderOf y = 3 ∧ y * z = z * y := by
  have ha7t : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution a7t := by
    unfold CFSG.BenderSuzuki.PFAppendixIII.IsInvolution
    constructor <;> decide
  obtain ⟨g, hg⟩ := aSeven_involutions_conjugate a7t (e z) ha7t
    ⟨fun h => hz1 (e.injective (h.trans (map_one e).symm)), by rw [← map_pow, hz, map_one]⟩
  have ha3 : a7a ^ 3 = 1 := by decide
  have ha1 : a7a ≠ 1 := by decide
  have hat : a7a * a7t = a7t * a7a := by decide
  refine ⟨e.symm (g * a7a * g⁻¹), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime ha3 ha1
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    rw [← hg]
    calc g * a7a * g⁻¹ * (g * a7t * g⁻¹) = g * (a7a * a7t) * g⁻¹ := by group
      _ = g * (a7t * a7a) * g⁻¹ := by rw [hat]
      _ = g * a7t * g⁻¹ * (g * a7a * g⁻¹) := by group

theorem card_dvd_factorial_index_of_isSimpleGroup {X : Type*} [Group X] [Finite X]
    (hs : IsSimpleGroup X) {M : Subgroup X} (hM : M ≠ ⊤) : Nat.card X ∣ M.index.factorial := by
  have hcore : M.normalCore = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ M.normalCore_le)) hM
  have h := M.index_normalCore_dvd_factorial_index
  rwa [hcore, Subgroup.index_bot] at h

theorem aSeven_arith {q x i : ℕ} (hq3 : 3 < q) (hqo : Odd q) (hdvd : q * (q ^ 2 - 1) ∣ x)
    (hmul : i * x = 2520) (hfac : 2520 ∣ i.factorial) : q = 5 ∧ (x = 120 ∨ x = 360) := by
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hmul)
  have hi7 : 7 ≤ i := by
    by_contra h
    push Not at h
    interval_cases i <;> first | omega | norm_num [Nat.factorial] at hfac
  have hx360 : x ≤ 360 := by nlinarith
  have hle : q * (q ^ 2 - 1) ≤ 360 := (Nat.le_of_dvd hx0 hdvd).trans hx360
  have hq7 : q ≤ 7 := by
    by_contra h
    push Not at h
    have h8 : 8 ≤ q := h
    have : 8 * (8 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
    omega
  obtain ⟨k, rfl⟩ := hqo
  have hk : k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | rfl
  · refine ⟨rfl, ?_⟩
    obtain ⟨c, rfl⟩ := hdvd
    norm_num at hmul hx360 ⊢
    have : c ≤ 3 := by omega
    interval_cases c <;> omega
  · exfalso
    obtain ⟨c, rfl⟩ := hdvd
    norm_num at hmul hx360
    have : c ≤ 1 := by omega
    interval_cases c <;> omega

theorem commute_of_conj_mem_zpowers {X : Type*} [Group X] {x y : X} (hx5 : x ^ 5 = 1)
    (hy3 : orderOf y = 3) (hc : x * y * x⁻¹ ∈ zpowers y) : Commute x y := by
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hc
  have hk' : y ^ (k % 3) = x * y * x⁻¹ := by
    have h := zpow_mod_orderOf y k
    rw [hy3] at h
    rw [← hk, ← h]
    norm_num
  have h2 : x ^ 2 * y * (x ^ 2)⁻¹ = y := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk'
      have : y = 1 := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = 1 := by rw [← hk']; group
      rw [this, orderOf_one] at hy3
      omega
    · rw [h1, zpow_one] at hk'
      calc x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = y := by rw [← hk', ← hk']
    · rw [h2] at hk'
      have hk2 : y ^ 2 = x * y * x⁻¹ := by rw [← hk']; norm_cast
      calc x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = x * y ^ 2 * x⁻¹ := by rw [hk2]
        _ = (x * y * x⁻¹) ^ 2 := by simp only [pow_two, mul_assoc, inv_mul_cancel_left]
        _ = (y ^ 2) ^ 2 := by rw [hk2]
        _ = y ^ 3 * y := by group
        _ = y := by rw [hy3', one_mul]
  have hcomm2 : Commute (x ^ 2) y := by
    show x ^ 2 * y = y * x ^ 2
    calc x ^ 2 * y = x ^ 2 * y * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = y * x ^ 2 := by rw [h2]
  have hx6 : x = (x ^ 2) ^ 3 := by
    rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, hx5, one_mul]
  rw [hx6]
  exact hcomm2.pow_left 3

section FieldFive

variable {F : Type} [Field F] [Finite F]

theorem pGammaL2PGLRange_eq_top_of_card_eq_five (hF : Nat.card F = 5) :
    pGammaL2PGLRange F = ⊤ := by
  have h1 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (p := 5) (n := 1)
    Nat.prime_five F (by rw [hF, pow_one])).1
  have : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.mp h1).1
  rw [eq_top_iff]
  intro x _
  rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom_eq_right]
  exact Subsingleton.elim _ _

theorem false_of_commute_three (hF : Nat.card F = 5) {a b : PGammaL2 F}
    (ha : a ∈ pGammaL2PGLRange F) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb : b ∈ pGammaL2PSLRange F) (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    False := by
  have hF' : IsOddPrimePower (Nat.card F) := ⟨5, 1, Nat.prime_five, by decide, le_rfl, by
    rw [hF, pow_one]⟩
  have haP : a ∈ pGammaL2PSLRange F := by
    by_contra haP
    have hidx := pGammaL2_psl_range_relIndex_pgl_eq_two F hF'
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a, ha⟩ : pGammaL2PGLRange F))
      (b := ⟨a, ha⟩)).mpr ⟨fun h => absurd h haP, fun h => absurd h haP⟩
    have h2 : a * a ∈ pGammaL2PSLRange F := h
    apply haP
    have h3 : a = (a * a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_three, ha3]
    rw [h3]
    exact inv_mem h2
  obtain ⟨w, rfl⟩ := (mem_pGammaL2PSLRange_iff F a).mp haP
  obtain ⟨w', rfl⟩ := (mem_pGammaL2PSLRange_iff F b).mp hb
  let ι : PSL2 F →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))
  have hι : Function.Injective ι := fun x y h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (SemidirectProduct.inl_injective h)
  have hw3 : w ^ 3 = 1 := hι (by rw [map_pow, map_one]; exact ha3)
  have hw1 : w ≠ 1 := fun h => ha1 (by rw [h, map_one, map_one])
  have hw'2 : w' ^ 2 = 1 := hι (by rw [map_pow, map_one]; exact hb2)
  have hw'1 : w' ≠ 1 := fun h => hb1 (by rw [h, map_one, map_one])
  have hww' : w * w' = w' * w := hι (by rw [map_mul, map_mul]; exact hab)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard := (CFSG.Walter.psl2_centralizer_involution F (p := 5) (f := 1) (by rw [hF, pow_one])
    (by decide) one_pos (orderOf_eq_prime hw'2 hw'1)).1 (by norm_num)
  have hmem : w ∈ centralizer ({w'} : Set (PSL2 F)) := mem_centralizer_singleton_iff.mpr hww'
  have h1 := orderOf_dvd_natCard (⟨w, hmem⟩ : centralizer ({w'} : Set (PSL2 F)))
  rw [Subgroup.orderOf_mk, orderOf_eq_prime hw3 hw1, hcard.1] at h1
  norm_num at h1

end FieldFive

variable {G : Type} [Group G] [Finite G]

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem false_of_aSeven
    (e : (G ⧸ pPrimeCore 2 G) ≃* alternatingGroup (Fin 7)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M⟩ := hE.nonempty_pslModel
  set O := pPrimeCore 2 G with hO
  set π := QuotientGroup.mk' O with hπ
  set H := normalizer (Q : Set G) with hH
  have hOodd : Odd (Nat.card O) := odd_card_pPrimeCore
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hGs : IsSimpleGroup (G ⧸ O) := e.isSimpleGroup
  have hcard : Nat.card (G ⧸ O) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hdvd := M.card_pgl_dvd hE (N := (⊤ : Subgroup (G ⧸ O))) (by rw [index_top]; exact odd_one)
  rw [comap_top, top_inf_eq] at hdvd
  rw [Nat.card_congr (pGammaL2PGLRangeEquiv M.F).symm.toEquiv, pgl2_card_formula] at hdvd
  have hfac := card_dvd_factorial_index_of_isSimpleGroup hGs hE.map_normalizer_ne_top
  have hmul := (H.map π).index_mul_card
  rw [hcard] at hfac hmul
  have hqo : Odd (Nat.card M.F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := M.hF
    rw [hq]
    exact hpodd.pow
  obtain ⟨hq5, hX⟩ := aSeven_arith M.h3 hqo hdvd hmul hfac
  replace hX : Nat.card (H.map π) = 120 ∨ Nat.card (H.map π) = 360 := hX
  have htop := pGammaL2PGLRange_eq_top_of_card_eq_five hq5
  let Φ : H →* PGammaL2 M.F := M.psi.comp (toBar Q)
  let ρ : H →* G ⧸ O := π.comp H.subtype
  have hρr : ρ.range = H.map π := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ρ.ker ≤ Φ.ker := fun y hy => by
    rw [MonoidHom.mem_ker] at hy ⊢
    exact M.psi_toBar_eq_one hE ((QuotientGroup.eq_one_iff _).mp hy)
  obtain ⟨t, ht⟩ := hE.exists_isOverlapInv
  obtain ⟨hpgl, hpsl⟩ := M.outerDiagonal hE ht
  have hΦr : Φ.range = pGammaL2PGLRange M.F := by
    refine le_antisymm (htop ▸ le_top) fun x hx => ?_
    obtain ⟨b, hb⟩ := M.pglRange_le_range ht hpgl hpsl hx
    obtain ⟨h, rfl⟩ := toBar_surjective Q b
    exact ⟨h, hb⟩
  have hΦc : Nat.card Φ.range = 120 := by
    rw [hΦr, Nat.card_congr (pGammaL2PGLRangeEquiv M.F).symm.toEquiv, pgl2_card_formula, hq5]
    norm_num
  have hr := Subgroup.relIndex_mul_index hker
  rw [Subgroup.index_ker, Subgroup.index_ker, hΦc, hρr] at hr
  rcases hX with hX | hX
  ·
    rw [hX] at hr
    have hle : Φ.ker ≤ ρ.ker := Subgroup.relIndex_eq_one.mp (by omega)
    obtain ⟨E, hEK, hE2, hE4⟩ := hE.main.four
    obtain ⟨z, hzE, hz1⟩ : ∃ z ∈ E, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : E = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx)
      rw [this, card_bot] at hE4
      omega
    have hzK : z ∈ twoPrimeLayerIn Q := hEK hzE
    have hzQ : z ∈ Q := twoPrimeLayerIn_le Q hzK
    have hz2 : z ^ 2 = 1 := hE2 z hzE
    have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hπz : π z ≠ 1 := fun h => hz1 (eq_one_of_pow_two_pow_eq_one hOodd
      ((QuotientGroup.eq_one_iff z).mp h) (k := 1) (by simpa using hz2))
    obtain ⟨yb, hy3, hyz⟩ := aSeven_exists_three_commute e (z := π z)
      (by rw [← map_pow, hz2, map_one]) hπz
    have hyC : yb ∈ centralizer ({π z} : Set (G ⧸ O)) := mem_centralizer_singleton_iff.mpr hyz
    rw [AschbacherToolkit.centralizer_quotient_odd O hOodd z hzo] at hyC
    obtain ⟨y, hyCz, rfl⟩ := hyC
    have hyH : y ∈ H := centralizer_le_of_involution hE.main.tight hzQ hzo hyCz
    have hzH : z ∈ H := le_normalizer hzQ
    have hyz' : y * z = z * y := mem_centralizer_singleton_iff.mp hyCz
    have ha3 : Φ ⟨y, hyH⟩ ^ 3 = 1 := by
      rw [← map_pow]
      apply hker
      rw [MonoidHom.mem_ker]
      change π (y ^ 3) = 1
      rw [map_pow, ← hy3]
      exact pow_orderOf_eq_one _
    have ha1 : Φ ⟨y, hyH⟩ ≠ 1 := fun h => by
      have h1 : ρ ⟨y, hyH⟩ = 1 := hle h
      change π y = 1 at h1
      rw [h1, orderOf_one] at hy3
      omega
    have hzL : toBar Q ⟨z, hzH⟩ ∈ bar Q (twoPrimeLayerIn Q) := toBar_mem_bar Q hzK
    have hb : Φ ⟨z, hzH⟩ ∈ pGammaL2PSLRange M.F :=
      (M.mem_sup_centralizer_iff _).mp (mem_sup_left hzL)
    have hb2 : Φ ⟨z, hzH⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨z, hzH⟩ : H) ^ 2 = 1 from Subtype.ext hz2, map_one]
    have hb1 : Φ ⟨z, hzH⟩ ≠ 1 := by
      intro h
      have h1 : M.psi ((⟨_, hzL⟩ : bar Q (twoPrimeLayerIn Q)) : Bar Q) = 1 := h
      rw [M.psi_apply_of_mem] at h1
      have h2 : M.e ⟨_, hzL⟩ = 1 := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
        (SemidirectProduct.inl_injective (h1.trans (map_one _).symm) |>.trans (map_one _).symm)
      have h3 : (⟨_, hzL⟩ : bar Q (twoPrimeLayerIn Q)) = 1 :=
        M.e.injective (h2.trans (map_one _).symm)
      have h4 : toBar Q ⟨z, hzH⟩ = toBar Q 1 := by
        rw [map_one]
        exact congrArg Subtype.val h3
      have h5 := toBar_injOn_of_isPGroup (isPGroup_zpowers_of_pow_eq_one (k := 1)
        (by simpa using hz2)) (mem_zpowers z) (one_mem _) h4
      exact hz1 (congrArg Subtype.val h5)
    have hab : Φ ⟨y, hyH⟩ * Φ ⟨z, hzH⟩ = Φ ⟨z, hzH⟩ * Φ ⟨y, hyH⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg Φ (Subtype.ext hyz')
    exact false_of_commute_three hq5 (hΦr ▸ ⟨_, rfl⟩) ha3 ha1 hb hb2 hb1 hab
  ·
    rw [hX] at hr
    have hN3 : Nat.card (Φ.ker.map ρ) = 3 := by
      rw [← Subgroup.relIndex_ker]
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨yb, hyb⟩ := exists_prime_orderOf_dvd_card' (G := Φ.ker.map ρ) 3 (by rw [hN3])
    obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' (G := H.map π) 5 (by rw [hX]; norm_num)
    set y' : G ⧸ O := (yb : G ⧸ O) with hy'
    set x' : G ⧸ O := (xb : G ⧸ O) with hx'
    have hy'3 : orderOf y' = 3 := by rw [hy', Subgroup.orderOf_coe, hyb]
    have hx'5 : orderOf x' = 5 := by rw [hx', Subgroup.orderOf_coe, hxb]
    have hNy : Φ.ker.map ρ = zpowers y' := by
      refine (Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr yb.2) ?_).symm
      rw [hN3, Nat.card_zpowers, hy'3]
    obtain ⟨h, hhH, hhx⟩ := xb.2
    have hc : x' * y' * x'⁻¹ ∈ zpowers y' := by
      rw [← hNy]
      obtain ⟨k, hk, hky⟩ := yb.2
      refine ⟨⟨h, hhH⟩ * k * ⟨h, hhH⟩⁻¹, Φ.normal_ker.conj_mem k hk _, ?_⟩
      rw [map_mul, map_mul, map_inv, hky]
      change π h * y' * (π h)⁻¹ = x' * y' * x'⁻¹
      rw [hhx]
    have hx'5' : x' ^ 5 = 1 := by rw [← hx'5]; exact pow_orderOf_eq_one x'
    have hcomm := commute_of_conj_mem_zpowers hx'5' hy'3 hc
    have h15 : orderOf (x' * y') = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx'5, hy'3]; norm_num), hx'5, hy'3]
    apply perm_fin_seven_orderOf_ne_fifteen (e (x' * y'))
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, h15]

end EndSetting

end CFSG.ComponentClassification.Asc75T4

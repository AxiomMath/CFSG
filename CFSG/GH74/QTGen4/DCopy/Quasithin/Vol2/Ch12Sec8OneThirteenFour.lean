module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneThirteenZ
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L128P

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_of_pow_three_pow_eq_one_F4 (h1228 : Stmt12_2_8_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : 4 ≤ n) {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (hx : x ^ 3 ^ k = 1) : x ∈ L := by
  obtain ⟨e⟩ := h.quot
  have hn5 : n ≤ 5 := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  have hcard : 20160 ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Nat.card_congr e.toEquiv]
    interval_cases n
    · rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_four]
      norm_num
    · rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_five]
      norm_num
  rcases h1228 G T L V h.hyp with h1 | h2 | ⟨⟨m, -, -, hZ, -⟩, -⟩
  · rw [← h1]
    exact Subgroup.subset_closure ⟨hxM, k, hx⟩
  · exfalso
    rcases h2 with hf | hlie
    · obtain ⟨f⟩ := hf
      rw [Nat.card_congr f.toEquiv, SteinbergCB.nat_card_alternating_five] at hcard
      omega
    · obtain ⟨f⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hlie
      rw [Nat.card_congr f.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two] at hcard
      omega
  · exfalso
    obtain ⟨hsimple, a, b, hab⟩ := isSimpleGroup_sl_zmod_two (m := n) (by omega)
    have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with hb | ht
    · rw [hb, Subgroup.card_bot] at hZ
      omega
    · apply hab
      have hmem : e.symm b ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [ht]
        exact Subgroup.mem_top _
      have h3 := Subgroup.mem_center_iff.1 hmem (e.symm a)
      have h4 := congrArg e h3
      simpa using h4

theorem lOne_le_closure_three_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (hn : 4 ≤ n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    lOne L V₁ ≤ Subgroup.closure {x | x ∈ lOne L V₁ ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := lOne L V₁ with hL₁
  set N := Subgroup.closure {x | x ∈ L₁ ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} with hNdef
  obtain ⟨e⟩ := lOne_quotient_mulEquiv_F4 h1222 h (by omega) hV₁
  have hn5 : n ≤ 5 := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨hsimple, -⟩ := isSimpleGroup_sl_zmod_two (m := n - 1) (by omega)
  have hsL : IsSimpleGroup (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := e.isSimpleGroup
  have hNL : N ≤ L₁ := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hLN : L₁ ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    have key : N ≤ N.comap (MulAut.conj l).toMonoidHom := by
      refine (Subgroup.closure_le _).2 fun y hy => ?_
      obtain ⟨hyL, k, hyk⟩ := hy
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ⟨?_, k, ?_⟩
      · show l * y * l⁻¹ ∈ L₁
        exact L₁.mul_mem (L₁.mul_mem hl hyL) (L₁.inv_mem hl)
      · show (l * y * l⁻¹) ^ 3 ^ k = 1
        rw [conj_pow, hyk]
        group
    exact key hx
  rcases L1297.le_pCoreOf_or_le_sup hsL hNL hLN with h1 | h1
  ·
    exfalso
    have h3 : 3 ∣ Nat.card L₁ := by
      have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L₁)
      rw [Nat.card_congr e.toEquiv] at hc
      rw [hc]
      apply Dvd.dvd.mul_right
      interval_cases n
      · rw [show 4 - 1 = 3 from rfl, Matrix.card_SL_field, ZMod.card, Fin.prod_univ_three]
        norm_num
      · rw [show 5 - 1 = 4 from rfl, Matrix.card_SL_field, ZMod.card, Fin.prod_univ_four]
        norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx3 : (x : G) ^ 3 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      rw [← hx]
      exact pow_orderOf_eq_one _
    have hxN : (x : G) ∈ N := Subgroup.subset_closure ⟨x.2, 1, by rw [pow_one]; exact hx3⟩
    obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 L₁ ⟨x, h1 hxN⟩
    have hj' : (x : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd := orderOf_dvd_of_pow_eq_one hj'
    rw [Subgroup.orderOf_coe, hx] at hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hdvd)
    omega
  ·
    have hO2N : pCoreOf 2 L₁ ≤ Subgroup.normalizer (N : Set G) := (pCoreOf_le 2 L₁).trans hLN
    show oTwoUpper _ ≤ N
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_pow_mem_oTwoUpper _ hx
    obtain ⟨j, hj⟩ := exists_two_pow_mem_of_le_sup (pCoreOf_isPGroup 2 L₁) hO2N h1 hi
    exact ⟨i + j, by rw [pow_add, pow_mul]; exact hj⟩

theorem thirteen_four_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h1228 : Stmt12_2_8_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h5 : Lemma12_8_8_five_F4)
    {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V n V₁ V₂)
    (hn : 4 ≤ n) {g : G} (hg : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (hZ : V₁ < zU128 V V₁) :
    ¬ CFSG.conjugate (zU128 V V₁) g ≤
      centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) := by
  intro hle
  have hyp := hs.hyp
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hyp hs.v1 hg hgN
  obtain ⟨-, hTZ⟩ := T_le_normalizer_w128_F4 h1222 h12213 hs
  rw [hkY _ hTZ] at hle
  have S := setting128A_F4 h1222 h12213 hs
  have hUeq := uA_eq_F4 h1222 hs
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  have hUT : u128 V V₁ ≤ T := (hs.almostSpecial_F4 h1222 h12213).G22_three.1

  have hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁ := by
    intro z hz
    have hz' : k⁻¹ * z * k ∈ rconj (zU128 V V₁) k := by
      rw [mem_rconj]
      have e : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
      rw [e]
      exact hz
    have h1 := hle hz'
    have h2 : k⁻¹ * z * k ∈ centralizerMod (centerOf (L128A.uA V₂ V₁))
        (rconj (L128A.wA V₂ V₁) k) (L128A.uA V₂ V₁) := by
      refine ⟨L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k ?_, ?_, ?_⟩
      · rw [hUeq]
        exact hz'
      · rw [hUeq]
        exact h1.2.1
      · rw [hUeq]
        exact h1.2.2
    rw [(S.nine_five hgood).1] at h2
    exact hUeq ▸ h2.1.1

  obtain ⟨hZJ, -, -, hLTJ⟩ := sup_le_normalizer_centerOf_i128_F4 h1222 h12213 hs hk hkN hkZ
  have hL₁C := lOne_le_centralizer_centerOf_F4 h1222 h12213 hs hk hkN hkZ
  set J := centerOf (i128 T L V V₁) with hJdef
  have hZJ' : zU128 V V₁ = J ⊔ V₁ := hZJ
  have hJZ : J ≤ zU128 V V₁ := hZJ' ▸ le_sup_left
  have hJne : J ≠ ⊥ := by
    intro hb
    rw [hb, bot_sup_eq] at hZJ'
    exact hZ.ne hZJ'.symm
  have hZU : zU128 V V₁ ≤ u128 V V₁ := fun z hz => hz.1
  have hJ2 : IsPGroup 2 J := hyp.hyp.sylow.1.to_le (hJZ.trans (hZU.trans hUT))
  have hNJ : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    L1297.normalizer_le_of_sup_le h37 h38 h39 hyp.hyp hJne hJ2 hLTJ
  have hCM : Subgroup.centralizer (zU128 V V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro c hc
    apply hNJ
    exact mem_normalizer_of_conj_mem_of_finite fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.1 hc w (hJZ hw), mul_inv_cancel_right]
      exact hw

  have hNZ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    (le_normalizer_conjClosure V _).trans (normalizer_le_normalizer_centerOf _)
  have hgen := lOne_le_closure_three_F4 h1222 hyp hn hs.v1
  have hHL₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (lOne L V₁ : Set G) := by
    intro h hh
    refine mem_normalizer_of_conj_mem_of_finite fun y hy => ?_
    have key : ∀ x ∈ Subgroup.closure {x | x ∈ lOne L V₁ ∧ ∃ k : ℕ, x ^ 3 ^ k = 1},
        h * x * h⁻¹ ∈ lOne L V₁ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨hxL, j, hxj⟩ := hx
        have hxC : h * x * h⁻¹ ∈ Subgroup.centralizer (zU128 V V₁ : Set G) :=
          (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer'' _ (hNZ hh))
            x).1 (hL₁C hxL)
        have hx3 : (h * x * h⁻¹) ^ 3 ^ j = 1 := by
          rw [conj_pow, hxj]
          group
        have hxLL := mem_of_pow_three_pow_eq_one_F4 h1228 hyp hn (hCM hxC) hx3
        have hxN' : x ∈ Subgroup.normalizer (V₁ : Set G) :=
          ((oTwoUpper_le _).trans inf_le_right) hxL
        have hxN : h * x * h⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hxN') (Subgroup.inv_mem _ hh)
        exact mem_oTwoUpper_of_odd ⟨hxLL, hxN⟩
          (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hx3))
      | one => simp
      | mul a b _ _ iha ihb =>
        have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ iha ihb
      | inv a _ iha =>
        have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ iha
    exact key y (hgen hy)
  have hn3 := h5 G T L V n V₁ V₂ hs hHL₁
  omega

end L128P

end CFSG.Quasithin.H13

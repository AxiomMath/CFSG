module

public import Certificates.Data.Kernel.GammaUSylowK
public import CFSG.Certificates.Kernel.GammaUSigmaSound
public import CFSG.GF2Type.Smith1979.GammaU.SylowFacts
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KC.GUY

open CFSG.KC.IF4C CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.SigmaP

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem minN_eq_min (a b : Nat) : minN a b = min a b := by
  unfold minN
  cases hb : Nat.ble a b
  · have : ¬ a ≤ b := fun h => by simp [Nat.ble_eq_true_of_le h] at hb
    simp only [cond_false]
    omega
  · have : a ≤ b := Nat.le_of_ble_eq_true hb
    simp only [cond_true]
    omega

theorem keyK_eq_min (z : Nat) : keyK z =
    min z (min (mulP z z) (min (mulP z (mulP z z)) (mulP z (mulP z (mulP z z))))) := by
  unfold keyK key3 key4
  simp only [minN_eq_min]

@[expose] def Can (m : Nat) : Prop := ∃ g h, m = mulP g h

theorem can_mulP (g h : Nat) : Can (mulP g h) := ⟨g, h, rfl⟩

theorem eq_of_can {U : GL} {m m' : Nat} (hm : Can m) (hm' : Can m') (h : IsP U m)
    (h' : IsP U m') : m = m' := by
  obtain ⟨g, g', rfl⟩ := hm
  obtain ⟨k, k', rfl⟩ := hm'
  exact mulP_eq_of_linP fun v => (h v).symm.trans (h' v)

theorem keyK_le {Z W : GL} {z w : Nat} (hz : IsP Z z) (cz : Can z) (hw : IsP W w) (cw : Can w)
    (hZ5 : Z ^ 5 = 1) (hZ1 : Z ≠ 1) (hW : W ∈ Subgroup.zpowers Z) (hW1 : W ≠ 1) :
    keyK z ≤ w := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf Z = 5 := orderOf_eq_prime hZ5 hZ1
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hW
  obtain ⟨j, hj, rfl⟩ := hW
  rw [Finset.mem_range] at hj
  rw [keyK_eq_min]
  interval_cases j
  · exact absurd (pow_zero Z) hW1
  · have := eq_of_can cw cz hw (by rw [pow_one]; exact hz)
    omega
  · have := eq_of_can cw (can_mulP _ _) hw (by rw [pow_two]; exact hz.mul hz)
    omega
  · have := eq_of_can cw (can_mulP _ _) hw
      (by rw [pow_succ', pow_two]; exact hz.mul (hz.mul hz))
    omega
  · have := eq_of_can cw (can_mulP _ _) hw
      (by rw [pow_succ', pow_succ', pow_two]; exact hz.mul (hz.mul (hz.mul hz)))
    omega

theorem keyK_le_keyK {Z W : GL} {z w : Nat} (hz : IsP Z z) (cz : Can z) (hw : IsP W w)
    (cw : Can w) (hZ5 : Z ^ 5 = 1) (hZ1 : Z ≠ 1) (hW5 : W ^ 5 = 1) (hW1 : W ≠ 1)
    (h : Subgroup.zpowers W ≤ Subgroup.zpowers Z) : keyK z ≤ keyK w := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf W = 5 := orderOf_eq_prime hW5 hW1
  have hne : ∀ j, 0 < j → j < 5 → W ^ j ≠ 1 := fun j h0 h5 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; exact h5)
  have hm : ∀ j : ℕ, W ^ j ∈ Subgroup.zpowers Z := fun j => h (Subgroup.npow_mem_zpowers W j)
  have h1 := keyK_le hz cz hw cw hZ5 hZ1 (by simpa using hm 1) (by simpa using hne 1 (by omega) (by omega))
  have h2 := keyK_le hz cz (hw.mul hw) (can_mulP _ _) hZ5 hZ1
    (by rw [← pow_two]; exact hm 2) (by rw [← pow_two]; exact hne 2 (by omega) (by omega))
  have h3 := keyK_le hz cz (hw.mul (hw.mul hw)) (can_mulP _ _) hZ5 hZ1
    (by rw [← pow_two, ← pow_succ']; exact hm 3)
    (by rw [← pow_two, ← pow_succ']; exact hne 3 (by omega) (by omega))
  have h4 := keyK_le hz cz (hw.mul (hw.mul (hw.mul hw))) (can_mulP _ _) hZ5 hZ1
    (by rw [← pow_two, ← pow_succ', ← pow_succ']; exact hm 4)
    (by rw [← pow_two, ← pow_succ', ← pow_succ']; exact hne 4 (by omega) (by omega))
  rw [keyK_eq_min w]
  omega

theorem keyK_eq {Z W : GL} {z w : Nat} (hz : IsP Z z) (cz : Can z) (hw : IsP W w)
    (cw : Can w) (hZ5 : Z ^ 5 = 1) (hZ1 : Z ≠ 1) (hW5 : W ^ 5 = 1) (hW1 : W ≠ 1)
    (h : Subgroup.zpowers Z = Subgroup.zpowers W) : keyK z = keyK w :=
  le_antisymm (keyK_le_keyK hz cz hw cw hZ5 hZ1 hW5 hW1 h.ge)
    (keyK_le_keyK hw cw hz cz hW5 hW1 hZ5 hZ1 h.le)

section Conj

variable {SP SI Y ZP DP n : Nat}

theorem conjRecs_spec : ∀ {es : List (List Nat)} {x prev : Nat},
    conjRecs SP SI Y ZP DP n es x prev = true →
    ∀ p < es.length, conjStep SP SI Y ZP DP n (x + p) (es.getD p []) = true ∧
      (p = 0 → prev < keyK (look ZP x)) ∧
      ∀ q, p = q + 1 → keyK (look ZP (x + q)) < keyK (look ZP (x + q + 1))
  | [], _, _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | e :: es, x, prev, h, p, hp => by
    change conjAt SP SI Y ZP DP n x e prev (keyK (look ZP x))
      (conjRecs SP SI Y ZP DP n es) = true at h
    unfold conjAt at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases p with
    | zero => exact ⟨by simpa using h2, fun _ => h1, fun q hq => absurd hq (by omega)⟩
    | succ p =>
      have ih := conjRecs_spec h3 p (by simpa using hp)
      have hx : x + (p + 1) = x.succ + p := by omega
      refine ⟨by rw [hx]; simpa only [List.getD_cons_succ] using ih.1, fun h0 => absurd h0 (by omega),
        fun q hq => ?_⟩
      obtain rfl : q = p := by omega
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · simpa using ih.2.1 rfl
      · obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        have := ih.2.2 r rfl
        have e1 : x.succ + r = x + (r + 1) := by omega
        rw [e1] at this
        exact this

theorem conjOK_spec {E : List (List Nat)} (h : conjOK SP SI Y ZP DP n E = true) :
    E.length = n ∧ (∀ x < n, conjStep SP SI Y ZP DP n x (E.getD x []) = true) ∧
      ∀ x, x + 1 < n → keyK (look ZP x) < keyK (look ZP (x + 1)) := by
  unfold conjOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  obtain ⟨hl, h⟩ := h
  have hs := conjRecs_spec h
  refine ⟨hl, fun x hx => by simpa using (hs x (by omega)).1, fun x hx => ?_⟩
  simpa using (hs (x + 1) (by omega)).2.2 x rfl

theorem conjStep_spec {x : Nat} {e : List Nat} (h : conjStep SP SI Y ZP DP n x e = true) :
    (fld DP x = 0 ∧ look ZP x = mulP Y idP) ∨
      (e.getD 0 0 < n ∧ fld DP (e.getD 0 0) < fld DP x ∧ e.getD 1 0 < 4 ∧
        look ZP x = mulP (letG SP SI (e.getD 1 0)) (mulP (look ZP (e.getD 0 0))
          (letV SP SI (e.getD 1 0)))) := by
  unfold conjStep at h
  cases hd : Nat.beq (fld DP x) 0
  · rw [hd, cond_false] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq] at h
    exact Or.inr ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · rw [hd, cond_true, Nat.beq_eq] at h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true hd, h⟩

theorem strict_of_succ {g : Nat → Nat} (h : ∀ x, x + 1 < n → g x < g (x + 1)) :
    ∀ a b, a < b → b < n → g a < g b := by
  intro a b
  induction b with
  | zero => intro hab; omega
  | succ b ih =>
    intro hab hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact (ih hab (by omega)).trans (h b hb)
    · exact h a hb

variable {T O PS B : List Nat} {TL WD : List (List Nat)} {TR R : List (List (List Nat))} {k m : Nat}

theorem letter (hC : ChainHyp SP SI T O PS B TL WD TR R k 2 m) {l : Nat} (hl : l < 4) :
    ∃ G ∈ lvlGrp SP TL 0, IsP G (letG SP SI l) ∧ IsP G⁻¹ (letV SP SI l) := by
  have hm := hC.toTreeHyp.j0_le
  have gen : ∀ g < 2, ∃ U ∈ lvlGrp SP TL 0, IsP U (look SP g) ∧ IsP U⁻¹ (look SI g) := by
    intro g hg
    have hi := invOK_spec SP SI hC.inv g (by omega)
    obtain ⟨U, hU⟩ := IsP.exists_of_mul hi
    refine ⟨U, Subgroup.subset_closure ⟨g, ?_, hU⟩, hU, hU.inv hi⟩
    rw [hC.tl0, List.mem_range]
    exact hg
  unfold letG letV
  by_cases h2 : l < 2
  · have hb : Nat.blt l 2 = true := by simp [Nat.blt_eq, h2]
    rw [hb, cond_true, cond_true]
    exact gen l h2
  · have hb : Nat.blt l 2 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h2
    rw [hb, cond_false, cond_false]
    obtain ⟨U, hU, h1, h2⟩ := gen (l - 2) (by omega)
    exact ⟨U⁻¹, Subgroup.inv_mem _ hU, h2, by rw [inv_inv]; exact h1⟩

theorem conj_spec (hC : ChainHyp SP SI T O PS B TL WD TR R k 2 m)
    (hY : ∃ U ∈ lvlGrp SP TL 0, IsP U Y) (hord : ordOK Y = true) {E : List (List Nat)}
    (hconj : conjOK SP SI Y ZP DP n E = true) :
    ∀ x < n, ∃ Z ∈ lvlGrp SP TL 0, IsP Z (look ZP x) ∧ Can (look ZP x) ∧ Z ^ 5 = 1 ∧ Z ≠ 1 := by
  obtain ⟨-, hrec, -⟩ := conjOK_spec hconj
  obtain ⟨Yg, hYg, hYP⟩ := hY
  unfold ordOK at hord
  simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hord
  obtain ⟨h5, h1⟩ := hord
  have key : ∀ d, ∀ x < n, fld DP x = d →
      ∃ Z ∈ lvlGrp SP TL 0, IsP Z (look ZP x) ∧ Can (look ZP x) ∧ Z ^ 5 = 1 ∧ Z ≠ 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x hx hd
      rcases conjStep_spec (hrec x hx) with ⟨-, he⟩ | ⟨hp, hpd, hl, he⟩
      · refine ⟨Yg, hYg, ?_, ⟨_, _, he⟩, ?_, fun h => ?_⟩
        · rw [he]
          simpa using hYP.mul IsP.one
        · have hp5 := hYP.mul (hYP.mul (hYP.mul (hYP.mul hYP)))
          rw [h5] at hp5
          have : Yg * (Yg * (Yg * (Yg * Yg))) = 1 := hp5.inj IsP.one
          rw [← this]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        · have ha : IsP 1 (mulP Y idP) := by simpa [h] using hYP.mul IsP.one
          have hb : IsP 1 (mulP idP idP) := by simpa using IsP.one.mul IsP.one
          have := eq_of_can (can_mulP _ _) (can_mulP _ _) ha hb
          rw [this] at h1
          simp at h1
      · obtain ⟨Zp, hZp, hZpP, -, hZp5, hZp1⟩ := ih _ (hd ▸ hpd) _ hp rfl
        obtain ⟨G, hG, hGP, hGI⟩ := letter hC hl
        refine ⟨G * (Zp * G⁻¹), Subgroup.mul_mem _ hG (Subgroup.mul_mem _ hZp
          (Subgroup.inv_mem _ hG)), ?_, ⟨_, _, he⟩, ?_, fun h => hZp1 ?_⟩
        · rw [he]
          exact hGP.mul (hZpP.mul hGI)
        · rw [← mul_assoc, conj_pow, hZp5, mul_one, mul_inv_cancel]
        · have := congrArg (fun t => G⁻¹ * t * G) h
          simpa only [mul_assoc, inv_mul_cancel_left, mul_one, one_mul, inv_mul_cancel] using this
  exact fun x hx => key _ x hx rfl

end Conj

theorem factorization_five_eq_one {n m : ℕ} (h : n = 5 * m) (hm : ¬ 5 ∣ m) :
    n.factorization 5 = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 5)
  rw [h, show 5 * m = 5 ^ 1 * m by ring, Nat.factorization_mul (by norm_num) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm]

theorem card_normalizer_dvd_of {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 17280)
    (f : Fin 576 → Subgroup G) (hf : Function.Injective f) (hf5 : ∀ x, Nat.card (f x) = 5)
    (F : Subgroup G) (hF : Nat.card F = 5) :
    Nat.card (Subgroup.normalizer (F : Set G)) ∣ 30 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (Nat.card G).factorization 5 = 1 :=
    factorization_five_eq_one (m := 3456) (hG.trans (by norm_num)) (by norm_num)
  have hc : ∀ H : Subgroup G, Nat.card H = 5 → Nat.card H = 5 ^ (Nat.card G).factorization 5 :=
    fun H hH => by rw [hH, h5, pow_one]
  let S : Fin 576 → Sylow 5 G := fun x => Sylow.ofCard (f x) (hc _ (hf5 x))
  have hS : Function.Injective S := fun a b hab => hf (by
    have := congrArg (fun P : Sylow 5 G => (P : Subgroup G)) hab
    simpa [S, Sylow.coe_ofCard] using this)
  have hcard : 576 ≤ Nat.card (Sylow 5 G) := by
    have := Nat.card_le_card_of_injective S hS
    simpa using this
  have hidx := Sylow.card_eq_index_normalizer (Sylow.ofCard F (hc F hF))
  replace hidx : Nat.card (Sylow 5 G) = (Subgroup.normalizer (F : Set G)).index := hidx
  have hmod := card_sylow_modEq_one 5 G
  have hmod' : (Subgroup.normalizer (F : Set G)).index % 5 = 1 := by
    rw [← hidx]
    exact hmod
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer (F : Set G))
  rw [hG] at hmul
  have h5d : 5 ∣ Nat.card (Subgroup.normalizer (F : Set G)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := F))
    rwa [hF] at this
  rw [← hidx] at hmul hmod'
  have hle : Nat.card (Subgroup.normalizer (F : Set G)) ≤ 30 := by
    by_contra hgt
    have : 31 * 576 ≤ Nat.card (Subgroup.normalizer (F : Set G)) * Nat.card (Sylow 5 G) :=
      Nat.mul_le_mul (by omega) hcard
    omega
  generalize Nat.card (Subgroup.normalizer (F : Set G)) = c at hmul h5d hle ⊢
  generalize Nat.card (Sylow 5 G) = s at hmul hmod' hcard
  interval_cases c <;> omega

section Facts

variable {i : ℕ} {SP SI : Nat} {T O PS B : List Nat} {TL WD QS : List (List Nat)}
  {TR R : List (List (List Nat))} {k n : Nat}
  {ASP ASI : Nat} {AT AO APS AB : List Nat} {ATL AWD : List (List Nat)}
  {ATR AR : List (List (List Nat))} {ka na : Nat} {Y ZP DP : Nat} {E : List (List Nat)}

theorem linP_theta (v : V12) : linP (CFSG.KC.IF4R.packR thetaRows) v = theta0 v := by
  rw [linP_eq_of_rowsP (rowsP_packR rowsOK_thetaRows), linOfRows_thetaRows]

theorem centOK_spec {t : Nat} {gs : List Nat} (h : centOK t gs = true) :
    ∀ g ∈ gs, mulP g t = mulP t g := by
  unfold centOK at h
  simp only [List.all_eq_true, Nat.beq_eq] at h
  exact h

theorem sylowFacts_of (hC : ChainHyp SP SI T O PS B TL WD TR R k 2 n) (hO : O.prod = 17280)
    (hP0 : lvlGrp SP TL 0 = genGrp (pGens i))
    (hA : ChainHyp ASP ASI AT AO APS AB ATL AWD ATR AR ka 2 na) (hAO : AO.prod = 27)
    (hsift : CFSG.KC.IF4R.recsOK T O 1 (fun _ => idP) [look ASP 0, look ASP 1, Y] QS = true)
    (hconj : conjOK SP SI Y ZP DP 576 E = true) (hord : ordOK Y = true)
    (hnc : ncP (look ASP 0) (look ASP 1) = true)
    (hcent : centOK (CFSG.KC.IF4R.packR thetaRows) [look SP 0, look SP 1] = true) :
    SylowFacts i := by
  have hmemT : ∀ r ∈ [look ASP 0, look ASP 1, Y], ∃ U ∈ lvlGrp SP TL 0, IsP U r := by
    intro r hr
    obtain ⟨x, -, as, hpath, heq⟩ := CFSG.KC.IF4R.recsOK_spec hsift r hr
    obtain ⟨P, hP, hPP⟩ := CFSG.KC.IF4M.ChainHyp.path0 hC as 0 (by simpa using hpath)
    rw [List.drop_zero] at hPP
    exact ⟨P * 1, Subgroup.mul_mem _ hP (Subgroup.one_mem _), heq ▸ hPP.mul IsP.one⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [← hP0]
    have hc := centOK_spec hcent
    have hgen : ∀ g < 2, ∀ U, IsP U (look SP g) → ∀ v, U (theta0 v) = theta0 (U v) := by
      intro g hg U hU v
      have h := congrArg (fun m => linP m v) (hc (look SP g) (by interval_cases g <;> simp))
      simp only [linP_mulP, linP_theta] at h
      rw [hU, hU]
      exact h
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem U hU =>
      obtain ⟨g, hg, hUg⟩ := hU
      rw [hC.tl0, List.mem_range] at hg
      exact hgen g hg U hUg
    | one => intro v; rfl
    | mul U V _ _ hU hV => intro v; rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hV, hU]
    | inv U _ hU =>
      intro v
      have := hU (U⁻¹ v)
      rw [apply_inv_apply] at this
      rw [← this, inv_apply_apply]
  ·
    rw [← hP0]
    obtain ⟨U0, -, hU0⟩ := hmemT (look ASP 0) (by simp)
    obtain ⟨U1, -, hU1⟩ := hmemT (look ASP 1) (by simp)
    refine ⟨lvlGrp ASP ATL 0, ?_, hA.card_zero.trans hAO, U0, ?_, U1, ?_, fun heq => ?_⟩
    · rw [lvlGrp, Subgroup.closure_le]
      rintro U ⟨g, hg, hUg⟩
      rw [hA.tl0, List.mem_range] at hg
      obtain ⟨V, hV, hVg⟩ := hmemT (look ASP g) (by interval_cases g <;> simp)
      exact hUg.inj hVg ▸ hV
    · exact Subgroup.subset_closure ⟨0, by rw [hA.tl0]; simp, hU0⟩
    · exact Subgroup.subset_closure ⟨1, by rw [hA.tl0]; simp, hU1⟩
    · have h1 := hU0.mul hU1
      have h2 := hU1.mul hU0
      rw [heq] at h1
      have := mulP_eq_of_linP fun v => (h1 v).symm.trans (h2 v)
      unfold ncP at hnc
      rw [this] at hnc
      simp at hnc
  ·
    intro F hF
    have hYm := hmemT Y (by simp)
    have hZ := conj_spec hC hYm hord hconj
    have hlt := strict_of_succ (conjOK_spec hconj).2.2
    choose! Z hZP hZI hZC hZ5 hZ1 using hZ
    have hPfin : Finite (genGrp (pGens i)) := inferInstance
    have hcardP : Nat.card (genGrp (pGens i)) = 17280 := by rw [← hP0, hC.card_zero, hO]
    have hZle : ∀ x < 576, Subgroup.zpowers (Z x) ≤ genGrp (pGens i) := fun x hx =>
      (Subgroup.zpowers_le).2 (hP0 ▸ hZP x hx)
    refine card_normalizer_dvd_of hcardP
      (fun x => (Subgroup.zpowers (Z x)).subgroupOf (genGrp (pGens i))) ?_ (fun x => ?_) F hF
    · intro a b hab
      have hab' : Subgroup.zpowers (Z a) = Subgroup.zpowers (Z b) := by
        have := (Subgroup.subgroupOf_inj).1 hab
        rwa [inf_of_le_left (hZle a a.2), inf_of_le_left (hZle b b.2)] at this
      have he := keyK_eq (hZI a a.2) (hZC a a.2) (hZI b b.2) (hZC b b.2) (hZ5 a a.2) (hZ1 a a.2)
        (hZ5 b b.2) (hZ1 b b.2) hab'
      apply Fin.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact absurd he (hlt _ _ h b.2).ne
      · exact absurd he (hlt _ _ h a.2).ne'
    · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZle x x.2)).toEquiv, Nat.card_zpowers,
        orderOf_eq_prime (hZ5 x x.2) (hZ1 x x.2)]

end Facts

end CFSG.KC.GUY

end

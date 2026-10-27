module

public import CFSG.Certificates.Kernel.S1277KArithSound
public import CFSG.Certificates.Kernel.S1277KVlSound
public import Certificates.Data.S1277Facts

public section

namespace CFSG.KS.S1277Facts

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Fr
  CFSG.KC.S1277Ar CFSG.KC.S1277Vl CFSG.KC.S1277Sv CFSG.KC.S1277Gm CFSG.KS.S1277Lat
  CFSG.KS.S1277Mod CFSG.KS.S1277Sig CFSG.KS.S1277Cand CFSG.KS.S1277Fr CFSG.KS.S1277Ar
  CFSG.KS.S1277Vl CFSG.KS.S1277Sv CFSG.KS.S1277Gm CFSG.Quasithin.H13.I1277
  Certificates.Data.S1277Sig Certificates.Data.S1277Surv Certificates.Data.S1277Facts CFSG.Open

@[expose] def uF (u : List ℕ) : Fin 3 → ℕ := fun i => u.getD i 0

theorem comb_eq_cmb (u : List ℕ) (c : Fin 3 → ZMod 2) :
    comb (uF u) c = cmb u ((c 0).val + 2 * (c 1).val + 4 * (c 2).val) := by
  have h0 := ZMod.val_lt (c 0)
  have h1 := ZMod.val_lt (c 1)
  have h2 := ZMod.val_lt (c 2)
  simp only [comb, cmb, uF, Nat.shiftRight_eq_div_pow, Fin.val_zero, Fin.val_one, Fin.val_two]
  congr 3 <;> omega

theorem comb_dec (u : List ℕ) (e : ℕ) :
    comb (uF u) ![(e % 2 : ℕ), (e / 2 % 2 : ℕ), (e / 4 % 2 : ℕ)] = cmb u e := by
  simp only [comb, cmb, uF, Nat.shiftRight_eq_div_pow, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ZMod.val_natCast, Nat.mod_mod,
    Fin.val_zero, Fin.val_one, Fin.val_two]

theorem comb_single (u : Fin 3 → ℕ) (i : Fin 3) : comb u (Pi.single i 1) = u i := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  fin_cases i <;> simp [comb, Pi.single_apply, h1]

theorem inSpan_iff {u : List ℕ} {x : ℕ} : InSpan (uF u) x ↔ inSp u x = true := by
  rw [inSp_iff]
  unfold InSpan
  constructor
  · rintro ⟨c, rfl⟩
    have h0 := ZMod.val_lt (c 0)
    have h1 := ZMod.val_lt (c 1)
    have h2 := ZMod.val_lt (c 2)
    exact ⟨_, by omega, (comb_eq_cmb u c).symm⟩
  · rintro ⟨e, -, rfl⟩
    exact ⟨_, comb_dec u e⟩

theorem basis3_of {u : List ℕ} (hu : indChk u = true) : Basis3 (uF u) := by
  unfold Basis3
  refine ⟨fun i => ?_, fun c c' h => ?_⟩
  · rw [← comb_single (uF u) i, comb_eq_cmb]
    exact cmb_lt hu _
  · rw [comb_eq_cmb, comb_eq_cmb] at h
    have a0 := ZMod.val_lt (c 0)
    have a1 := ZMod.val_lt (c 1)
    have a2 := ZMod.val_lt (c 2)
    have b0 := ZMod.val_lt (c' 0)
    have b1 := ZMod.val_lt (c' 1)
    have b2 := ZMod.val_lt (c' 2)
    rw [indChk] at hu
    simp only [Bool.and_eq_true] at hu
    have h1 := (allLt_iff.1 ((allLt_iff.1 hu.2) ((c 0).val + 2 * (c 1).val + 4 * (c 2).val)
      (by omega))) ((c' 0).val + 2 * (c' 1).val + 4 * (c' 2).val) (by omega)
    rw [Bool.or_eq_true] at h1
    have he : (c 0).val + 2 * (c 1).val + 4 * (c 2).val =
        (c' 0).val + 2 * (c' 1).val + 4 * (c' 2).val := by
      rcases h1 with h1 | h1
      · exact Nat.eq_of_beq_eq_true h1
      · rw [h, Nat.beq_refl] at h1
        exact absurd h1 (by simp)
    funext i
    apply ZMod.val_injective
    fin_cases i <;> simp <;> omega

section Facts

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem codQ_of (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e0 : ℕ}
    (hN : nodeChk M kg m gs ts e0 = true) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {p TP d : ℕ} {pg pr pt ws : List ℕ}
    (hfr : frChk M m gs ts p pg pr pt TP d ws = true) :
    CodQ Q (fun g => rd6 TP (κ g)) d := by
  obtain ⟨f1, f2, f3, f4, -⟩ := fr_sound hκ hN hQK hQN hfr
  unfold CodQ
  exact ⟨f1, f2, f3, f4⟩

theorem labInv_of (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e0 : ℕ}
    (hN : nodeChk M kg m gs ts e0 = true) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {p TP d : ℕ} {pg pr pt ws : List ℕ}
    (hfr : frChk M m gs ts p pg pr pt TP d ws = true) {z : G} (hzK : z ∈ K)
    (hzH : ∀ h ∈ H, h * z * h⁻¹ = z) (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q) {typ L : ℕ}
    (hl : labChk M (κ z) ts pg TP typ L = true) :
    LabInv H Q (fun g => rd6 TP (κ g)) (φL L) := by
  unfold LabInv
  intro h hh x hx
  refine φL_eq_iff.2 ?_
  obtain ⟨a0, a1, a2⟩ := lab_sound hκ hN hQK hQN hfr hzK hl (hQn h hh x hx)
  obtain ⟨b0, b1, b2⟩ := lab_sound hκ hN hQK hQN hfr hzK hl hx
  obtain ⟨c0, c1, c2⟩ := lab_conj (Q := Q) hzH hQn hh x
  rw [Bool.eq_iff_iff]
  by_cases h0 : typ = 0
  · rw [a0 h0, b0 h0, c0]
  · by_cases h1 : typ = 1
    · rw [a1 h1, b1 h1, c1]
    · rw [a2 h0 h1, b2 h0 h1, c2]

theorem sigFacts_of_tables (hQK : Q ≤ K) (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q)
    (hκ : MCod K M κ) {z : G} (hzH : ∀ h ∈ H, h * z * h⁻¹ = z) (hzK : z ∈ K)
    {kg kt nm nxs : List ℕ} {ngs nts : List (List ℕ)}
    (hgen : genChk M kg kt = true) (hnodes : nodesChk M kg nm ngs nts nxs = true)
    {is ps cs ds ys ls : List ℕ} {pgs prs pts wss : List (List ℕ)}
    (hfr : frAll M (κ z) nm ngs nts is ps pgs prs pts cs ds wss ys ls = true)
    {sd sl : List ℕ} {sb : List (List ℕ)} {sT : List (List (List (List ℕ)))}
    (hsig : sigAll sd sl sb sT = true) {ol xi sv : ℕ} {tx ab ak : List ℕ}
    (har : arAll M.nb ol xi sv nxs is ds ls tx sd sl sT ab ak = true) {xu : ℕ}
    {xt : List (List ℕ)} (hx : xChk (sd.getD xi 0) (sl.getD xi 0) xu xt = true)
    (hol : ol < nm.length) {j : ℕ} (hj : j < is.length) (hi : is.getD j 0 < nm.length)
    (hsv : is.getD j 0 ≠ sv)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ (nm.getD (is.getD j 0) 0).testBit n = true) :
    SigFacts H K Q := by
  obtain ⟨hfrj, hlj⟩ := frAll_spec hfr hj
  rw [arAll, Bool.and_eq_true] at har
  have hc := (allL_iff.1 har.2) j (List.mem_range.2 hj)
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact absurd (Nat.eq_of_beq_eq_true hc) hsv
  rw [arChk] at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨ht, hd⟩, hL⟩, -⟩, hord⟩, hbr⟩ := hc
  have hd' := Nat.eq_of_beq_eq_true hd
  have hL' := Nat.eq_of_beq_eq_true hL
  have hsigt := (allL_iff.1 hsig) _ (List.mem_range.2 ht)
  rw [← hd', ← hL'] at hsigt
  have hN := nodesChk_spec hnodes _ hi
  have hQc := card_of_node hκ hgen hnodes hi hQK hQN
  unfold SigFacts
  refine ⟨ds.getD j 0, fun g => rd6 (cs.getD j 0) (κ g), φL (ls.getD j 0), ab.getD j 0,
    ak.getD j 0, codQ_of hκ hN hQK hQN hfrj, labInv_of hκ hN hQK hQN hfrj hzK hzH hQn hlj, ?_, ?_⟩
  · rw [card_Sig_of_chk hsigt, card_K hκ, hQc]
    have h := Nat.eq_of_beq_eq_true hord
    rw [← hd'] at h
    exact h
  rcases hbr with ⟨h3, hle⟩ | ⟨⟨h7, hbk⟩, hxi⟩
  · obtain ⟨O, hOK, hOn, hO2, -, hOc⟩ := node_subgroupG hκ hgen hnodes hol
    refine Or.inl ⟨Nat.eq_of_beq_eq_true h3, O, hOK, hOn, hO2, ?_⟩
    rw [hOc, hQc]
    calc 4 * 2 ^ nxs.getD (is.getD j 0) 0 = 2 ^ (nxs.getD (is.getD j 0) 0 + 2) := by
          rw [pow_add]; ring
      _ ≤ 2 ^ nxs.getD ol 0 := Nat.pow_le_pow_right (by norm_num) hle
  · refine Or.inr ⟨Nat.eq_of_beq_eq_true h7, hbk, ?_⟩
    rw [hd', hL', Nat.eq_of_beq_eq_true hxi]
    exact x_sound hx

theorem imFacts_of (hκ : MCod K M κ) {kg gs ts : List ℕ} {m e0 : ℕ}
    (hN : nodeChk M kg m gs ts e0 = true) (hQK : Q ≤ K)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {TP : ℕ}
    (D : FrData H Q (Phi' Q) 6) (hD : ∀ x, D.wc x = rd6 TP (κ x)) {φ : ℕ → ℕ}
    (hR : D.rho.range ≤ Sig 6 φ) {a u v : List ℕ} (hnd : a.Nodup) (hlen : a.length = 168)
    (hS : ∀ y, pkSet D.rho.range y ↔ y ∈ a) (hv : vlChk a u v = true)
    (habu : abChk M ts TP u = true) (habv : abChk M ts TP v = true) :
    ImFacts Q (fun g => rd6 TP (κ g)) D.rho.range := by
  classical
  obtain ⟨hu, hv', hclu, hclv, hint, hcov, hinvu, hinvv, hker⟩ := vlChk_spec hv
  have hconj : ∀ h (hh : h ∈ H), ∀ x ∈ Q,
      D.wc (h * x * h⁻¹) = appP (pk (D.rho ⟨h, hh⟩)) (D.wc x) := by
    intro h hh x hx
    rw [← D.rho_of_mem ⟨h, hh⟩ hx]
    exact val_eq_appP (hR ⟨⟨h, hh⟩, rfl⟩) _
  have hmemS : ∀ h (hh : h ∈ H), pk (D.rho ⟨h, hh⟩) ∈ a := fun h hh =>
    (hS _).1 ⟨D.rho ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
  have hpre : ∀ {b : List ℕ},
      (∀ x y, inSp b x = true → inSp b y = true → inSp b (x ^^^ y) = true) →
      abChk M ts TP b = true → (∀ s ∈ a, ∀ x, inSp b x = true → inSp b (appP s x) = true) →
      PreFacts Q (fun g => rd6 TP (κ g)) (uF b) := by
    intro b hcl hab hinv
    obtain ⟨A, hA, ⟨hAc, hAe⟩, hA16, -⟩ := sub_sound hκ hN hQK hQN D hD hcl hab
      fun h hh x hx hxN => by rw [hconj h hh x hx]; exact hinv _ (hmemS h hh) _ hxN
    have hmA : ∀ x ∈ Q, InSpan (uF b) (rd6 TP (κ x)) → x ∈ A := fun x hx hxs =>
      (hA x).2 ⟨hx, by rw [hD]; exact inSpan_iff.1 hxs⟩
    unfold PreFacts
    refine ⟨fun x hx y hy hxs hys => ⟨?_, ?_⟩, ?_⟩
    · have hc := hAc.is_comm.comm (⟨x, hmA x hx hxs⟩ : A) ⟨y, hmA y hy hys⟩
      exact congrArg Subtype.val hc
    · have h2 := hAe x (hmA x hx hxs)
      rwa [pow_two] at h2
    · have e : {x | x ∈ Q ∧ InSpan (uF b) (rd6 TP (κ x))} = (A : Set G) := by
        ext x
        rw [Set.mem_setOf_eq, SetLike.mem_coe, hA, hD, inSpan_iff]
      rw [e, ← Nat.card_coe_set_eq]
      exact hA16
  have hspan : ∀ {b : List ℕ}, (∀ s ∈ a, ∀ x, inSp b x = true → inSp b (appP s x) = true) →
      SpanInv D.rho.range (uF b) := by
    intro b hinv
    unfold SpanInv
    intro σ hσ x hx hxs
    rw [inSpan_iff] at hxs ⊢
    rw [val_eq_appP (hR hσ)]
    exact hinv _ ((hS _).1 ⟨σ, hσ, rfl⟩) _ hxs
  unfold ImFacts
  refine ⟨by rw [card_range_eq_of_pkSet hR hnd hS, hlen], uF u, uF v, basis3_of hu, basis3_of hv',
    fun x hxu hxv => hint x (inSpan_iff.1 hxu) (inSpan_iff.1 hxv), fun c hc => ?_, hspan hinvu,
    hspan hinvv, fun σ hσ hfix => ?_, hpre hclu habu hinvu, hpre hclv habv hinvv⟩
  · obtain ⟨x, h1, h2⟩ := hcov c (by simpa using hc)
    exact ⟨x, inSpan_iff.2 h1, inSpan_iff.2 h2⟩
  · have hfix' : ∀ i < 3, appP (pk σ) (u.getD i 0) = u.getD i 0 := by
      intro i hi
      have hlt : u.getD i 0 < 2 ^ 6 := (basis3_of hu).1 ⟨i, hi⟩
      have h1 := hfix ⟨i, hi⟩ hlt
      rw [val_eq_appP (hR hσ)] at h1
      exact h1
    have h2 := hker _ ((hS _).1 ⟨σ, hσ, rfl⟩) hfix'
    rw [oneQ_eq, ← pk_one] at h2
    exact pk_injective (hR hσ) (Sig 6 φ).one_mem h2

end Facts

end CFSG.KS.S1277Facts

end

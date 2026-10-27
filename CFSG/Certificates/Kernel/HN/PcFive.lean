module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Cover
public import Certificates.Data.Kernel.HN.PcFiveE3
public import CFSG.RankThree.PartOne.KS.HNFiveMatrix
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporWit
public import CFSG.LocalAnalysis.AGLEmbedding.CoverCore
public import CFSG.RankThree.PartOne.KS.HNFiveBasic

public section

namespace CFSG.KC.HN.PcFive

open CFSG.KC.BM.PcFive CFSG.RankThree.PartOne.KS.HNFive Subgroup
open CFSG.Monster.B.Pinned (bcomm)
open CFSG.LocalAnalysis.RankFourTheoremC (RankThreeWitness)

variable {G : Type} [Group G]

section Rel

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ}

theorem swap_of_bcomm {a b c : G} (h : bcomm b a = c) : b * a = a * b * c := by
  rw [← h]
  unfold bcomm
  group

theorem swap_of_rel (hR : Rel q z x r Mm XU cx BU cr) (i j : Fin 4) {n : ℕ}
    (hn : (Mm j i).val = n) : q j * q i = q i * q j * z ^ n := by
  rw [← hn]
  exact swap_of_bcomm (hR.commData.bcomm_q j i)

theorem z5_of_rel (hR : Rel q z x r Mm XU cx BU cr) : z ^ 5 = 1 := by
  rw [← hR.commData.orderOf_z]
  exact pow_orderOf_eq_one z

theorem z_ne_one_of_rel (hR : Rel q z x r Mm XU cx BU cr) : z ≠ 1 := by
  intro h
  have := hR.commData.orderOf_z
  rw [h, orderOf_one] at this
  omega

theorem qRel_of_rel (hR : Rel q z x r Mm XU cx BU cr) : QRel cmHN q z where
  z5 := z5_of_rel hR
  q5 := hR.commData.pow_q
  zc i := (hR.commData.comm_z i).symm
  s01 := swap_of_rel hR 0 1 rfl
  s02 := swap_of_rel hR 0 2 rfl
  s03 := swap_of_rel hR 0 3 rfl
  s12 := swap_of_rel hR 1 2 rfl
  s13 := swap_of_rel hR 1 3 rfl
  s23 := swap_of_rel hR 2 3 rfl

theorem xu_val (a j : Fin 4) :
    (((XU : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) a j).val = exX a j := by
  revert a j
  decide

theorem conjX_rel (hR : Rel q z x r Mm XU cx BU cr) (a : Fin 4) :
    x⁻¹ * q a * x = q 0 ^ exX a 0 * q 1 ^ exX a 1 * q 2 ^ exX a 2 * q 3 ^ exX a 3 * z ^ cx a := by
  rw [hR.conj_x a]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, xu_val,
    mul_assoc]
  simp [Fin.succ]

theorem conjZ_rel (hR : Rel q z x r Mm XU cx BU cr) : x⁻¹ * z * x = nfQ q z xActHN.rz := by
  rw [mul_assoc, ← hR.comm_x, inv_mul_cancel_left]
  simp [nfQ, xActHN]

theorem conj_x_nfQ (hR : Rel q z x r Mm XU cx BU cr) (a : QV) :
    x⁻¹ * nfQ q z a * x = nfQ q z (applyQ cmHN xActHN a) := by
  refine conj_nfQ (qRel_of_rel hR) ?_ ?_ ?_ ?_ (conjZ_rel hR) a
  · rw [conjX_rel hR]
    simp [nfQ, xActHN, exX, cx]
  · rw [conjX_rel hR]
    simp [nfQ, xActHN, exX, cx]
  · rw [conjX_rel hR]
    simp [nfQ, xActHN, exX, cx]
  · rw [conjX_rel hR]
    simp [nfQ, xActHN, exX, cx]

end Rel

section Gens

variable {m : CM} {q : Fin 4 → G} {z : G}

@[expose] def qP (q : Fin 4 → G) (z : G) : Fin 4 → G :=
  ![nfQ q z qHN.r0, nfQ q z qHN.r1, nfQ q z qHN.r2, nfQ q z qHN.r3]

theorem zpow_nfQ (h : QRel m q z) (n : ℕ) : z ^ n = nfQ q z (powQ m ⟨0, 0, 0, 0, 1⟩ n) := by
  rw [← nfQ_pow h]
  simp [nfQ]

theorem nfQ_qP (h : QRel m q z) (b : QV) : nfQ (qP q z) z b = nfQ q z (applyQ m qHN b) := by
  have ez : nfQ q z qHN.rz = z := by simp [nfQ, qHN]
  unfold applyQ
  rw [← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_mul h, ← nfQ_pow h, ← nfQ_pow h, ← nfQ_pow h,
    ← nfQ_pow h, ← nfQ_pow h, ez]
  rfl

theorem mul_eq_of (h : QRel m q z) {a b c d e : QV}
    (hv : mulQ m a b = mulQ m (mulQ m c d) e) :
    nfQ q z a * nfQ q z b = nfQ q z c * nfQ q z d * nfQ q z e := by
  rw [nfQ_mul h, nfQ_mul h, nfQ_mul h, hv]

theorem swapP (h : QRel cmHN q z) {a b : QV} (n : ℕ)
    (hv : mulQ cmHN b a = mulQ cmHN (mulQ cmHN a b) (powQ cmHN ⟨0, 0, 0, 0, 1⟩ n)) :
    nfQ q z b * nfQ q z a = nfQ q z a * nfQ q z b * z ^ n := by
  rw [zpow_nfQ h]
  exact mul_eq_of h hv

theorem zcP (h : QRel cmHN q z) {a : QV}
    (hv : mulQ cmHN ⟨0, 0, 0, 0, 1⟩ a = mulQ cmHN a ⟨0, 0, 0, 0, 1⟩) :
    z * nfQ q z a = nfQ q z a * z := by
  have ez : nfQ q z ⟨0, 0, 0, 0, 1⟩ = z := by simp [nfQ]
  calc z * nfQ q z a = nfQ q z ⟨0, 0, 0, 0, 1⟩ * nfQ q z a := by rw [ez]
    _ = nfQ q z a * nfQ q z ⟨0, 0, 0, 0, 1⟩ := by rw [nfQ_mul h, nfQ_mul h, hv]
    _ = nfQ q z a * z := by rw [ez]

theorem powP (h : QRel cmHN q z) {a : QV} (hv : powQ cmHN a 5 = QV.one) : nfQ q z a ^ 5 = 1 := by
  rw [nfQ_pow h, hv, nfQ_one]

theorem qRel_qP (h : QRel cmHN q z) : QRel cmFive (qP q z) z where
  z5 := h.z5
  q5 i := by
    fin_cases i
    · exact powP h rfl
    · exact powP h rfl
    · exact powP h rfl
    · exact powP h rfl
  zc i := by
    fin_cases i
    · exact zcP h rfl
    · exact zcP h rfl
    · exact zcP h rfl
    · exact zcP h rfl
  s01 := swapP h _ rfl
  s02 := swapP h _ rfl
  s03 := swapP h _ rfl
  s12 := swapP h _ rfl
  s13 := swapP h _ rfl
  s23 := swapP h _ rfl

end Gens

section Hyp

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ}

theorem conjP (hR : Rel q z x r Mm XU cx BU cr) {a b : QV}
    (hv : applyQ cmHN xActHN a = applyQ cmHN qHN b) :
    x⁻¹ * nfQ q z a * x = nfQ (qP q z) z b := by
  rw [conj_x_nfQ hR, nfQ_qP (qRel_of_rel hR), hv]

theorem pcHyp_of_rel (hR : Rel q z x r Mm XU cx BU cr) : PcHyp x (qP q z) z where
  rel := qRel_qP (qRel_of_rel hR)
  x5 := hR.x_pow
  x0 := conjP hR rfl
  x1 := conjP hR rfl
  x2 := conjP hR rfl
  x3 := conjP hR rfl
  xz := by
    rw [nfQ_qP (qRel_of_rel hR), show applyQ cmHN qHN xAct.rz = ⟨0, 0, 0, 0, 1⟩ from rfl,
      mul_assoc, ← hR.comm_x, inv_mul_cancel_left]
    simp [nfQ]

end Hyp

section Triple

variable {x : G} {q : Fin 4 → G} {z : G}

theorem psi_eq_one [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) (hz : z ≠ 1) {v : V6}
    (hv : v.red) (h : psi x q z v = 1) : v.isOne = true := by
  have e0 : psi x q z (dec 0) = 1 := by simp [psi, nfQ, dec, decQ]
  rw [← dec_enc hv, ← e0] at h
  have := psi_dec_inj H hφ hz (enc_lt hv) (by norm_num) h
  unfold V6.isOne
  rw [← dec_enc hv, this]
  exact V6.beq_self _

theorem indepV_spec {t a b : V6} (h : indepV t a b = true) {i j l : ℕ} (hi : i < 5) (hj : j < 5)
    (hl : l < 5) (h1 : (mulV (mulV (powV t i) (powV a j)) (powV b l)).isOne = true) :
    i = 0 ∧ j = 0 ∧ l = 0 := by
  have e := allBelow_spec (allBelow_spec (allBelow_spec h i hi) j hj) l hl
  simp only [h1, Bool.not_true, Bool.or_false, Bool.and_eq_true, Nat.beq_eq] at e
  exact ⟨e.1.1, e.1.2, e.2⟩

theorem rankThreeWitness_of_tripV [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true)
    (hz : z ≠ 1) {t a b : V6} (ht : t.red) (ha : a.red) (hb : b.red) (h : tripV t a b = true) :
    RankThreeWitness 5 (psi x q z t) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  unfold tripV at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hta, htb⟩, hab⟩, ht5⟩, ha5⟩, hb5⟩, hind⟩ := h
  have hcomm : ∀ {u v : V6}, u.red → v.red → (mulV u v).beq (mulV v u) = true →
      psi x q z u * psi x q z v = psi x q z v * psi x q z u := by
    intro u v hu hv huv
    rw [H.psi_mul hφ hu hv, H.psi_mul hφ hv hu, V6.beq_eq huv]
  have hpow : ∀ {u : V6}, u.red → ord5 u = true → psi x q z u ^ 5 = 1 := by
    intro u hu hu5
    rw [H.psi_pow hφ hu, ord5_spec hu5, psi_one]
  let D : CFSG.AGLEmbedding.ModuleSpec G 5 :=
    { n := 3, m := 0, a := ![psi x q z t, psi x q z a, psi x q z b], g := fun j => j.elim0,
      M := fun j => j.elim0
      comm := by
        intro i j
        fin_cases i <;> fin_cases j
        · rfl
        · exact hcomm ht ha hta
        · exact hcomm ht hb htb
        · exact (hcomm ht ha hta).symm
        · rfl
        · exact hcomm ha hb hab
        · exact (hcomm ht hb htb).symm
        · exact (hcomm ha hb hab).symm
        · rfl
      pow := by
        intro i
        fin_cases i
        · exact hpow ht ht5
        · exact hpow ha ha5
        · exact hpow hb hb5
      indep := by
        intro c hc
        simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one] at hc
        simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue, Matrix.head_cons,
          Matrix.cons_val_succ, Matrix.tail_cons] at hc
        have hi := ZMod.val_lt (c 0)
        have hj := ZMod.val_lt (c 1)
        have hl := ZMod.val_lt (c 2)
        rw [← mul_assoc, H.psi_pow hφ ht, H.psi_pow hφ ha, H.psi_pow hφ hb,
          H.psi_mul hφ (powV_red _ _) (powV_red _ _),
          H.psi_mul hφ (mulV_red _ _) (powV_red _ _)] at hc
        obtain ⟨e0, e1, e2⟩ := indepV_spec hind hi hj hl (psi_eq_one H hφ hz (mulV_red _ _) hc)
        funext k
        fin_cases k
        · exact (ZMod.val_eq_zero _).1 e0
        · exact (ZMod.val_eq_zero _).1 e1
        · exact (ZMod.val_eq_zero _).1 e2
      act := fun j => j.elim0 }
  have hEA : CFSG.Open.IsElemAbelian 5 D.span :=
    ⟨inferInstance, fun x hx => D.pow_eq_one_of_mem hx⟩
  exact Or.inr (Or.inr ⟨D.span, hEA, D.card_span hp, Subgroup.subset_closure ⟨(0 : Fin 3), rfl⟩⟩)

end Triple

section Cover

variable {x : G} {q : Fin 4 → G} {z : G}

theorem rankThreeWitness_of_census [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true)
    (hz : z ≠ 1) {rep ea eb D : ℕ → ℕ} {nc : ℕ} (hE : ∀ i < 15625, elemOK rep nc i (D i) = true)
    (h3 : e3OK rep ea eb nc = true) {m : ℕ} (hcard : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m) :
    ∀ s : G, orderOf s = 5 → RankThreeWitness 5 s := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro s hs
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow.exists_conj_into_range
    (by norm_num) (PSub x q).subtype Subtype.val_injective (card_P H hz) hcard hm hs
  rw [Subgroup.range_subtype] at hg
  obtain ⟨i, hi, hie⟩ := mem_P_psi H hφ hg
  have hs5 : s ^ 5 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have h5 : psi x q z (dec i) ^ 5 = 1 := by
    have e := conj_pow (a := g⁻¹) (b := s) (i := 5)
    rw [inv_inv] at e
    rw [hie, e, hs5]
    group
  have hord : ord5 (dec i) = true := by
    rw [H.psi_pow hφ (dec_red _)] at h5
    exact psi_eq_one H hφ hz (powV_red _ _) h5
  have hi0 : i ≠ 0 := by
    rintro rfl
    have e : psi x q z (dec 0) = 1 := by simp [psi, nfQ, dec, decQ]
    rw [e] at hie
    have : s = 1 := by
      have e2 : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [e2, ← hie]
      group
    rw [this, orderOf_one] at hs
    norm_num at hs
  obtain ⟨hl, hw⟩ := elemOK_spec (hE i hi) hi0 hord
  set w := dec (D i % 15625)
  set c := D i / 15625
  have hr := rankThreeWitness_of_tripV H hφ hz (dec_red (rep c)) (dec_red (ea c)) (dec_red (eb c))
    (allBelow_spec h3 c hl)
  have e1 := H.psi_mul hφ (v := w) (w := dec i) (dec_red _) (dec_red i)
  have e2 := H.psi_mul hφ (v := dec (rep c)) (w := w) (dec_red (rep c)) (dec_red _)
  rw [hw, ← e2] at e1
  have hc : (psi x q z w)⁻¹ * psi x q z (dec (rep c)) * (psi x q z w)⁻¹⁻¹ = psi x q z (dec i) := by
    rw [inv_inv, mul_assoc, ← e1]
    group
  have h1 := hr.conj_eq _ hc
  rw [hie] at h1
  exact h1.conj_eq g (by group)

theorem rankThreeWitness_of_rel [Finite G] {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G}
    {BU : Fin k → GL (Fin 4) (ZMod 5)} {cr : Fin k → Fin 4 → ℕ}
    (hR : Rel q z x r Mm XU cx BU cr) (hφ : phiOK () = true) {rep ea eb D : ℕ → ℕ} {nc : ℕ}
    (hE : ∀ i < 15625, elemOK rep nc i (D i) = true) (h3 : e3OK rep ea eb nc = true) {m : ℕ}
    (hcard : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m) :
    ∀ s : G, orderOf s = 5 → RankThreeWitness 5 s :=
  rankThreeWitness_of_census (pcHyp_of_rel hR) hφ (z_ne_one_of_rel hR) hE h3 hcard hm

end Cover

end CFSG.KC.HN.PcFive

end

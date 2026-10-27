module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Class
public import Certificates.Certificate17473
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWit
public import Certificates.Certificate136201
public import Certificates.Certificate136202
public import Certificates.Certificate136203
public import Certificates.Certificate136204
public import Certificates.Certificate136205
public import Certificates.Certificate136206
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
  CFSG.Monster.B.Pinned CFSG.Monster.Existence CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Dickson.Sec6.BM2
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget B0 LA LM nfD cubeE zconjE WT
  fibreOK fibreFull fibreAffs fibreGensOK fibreGenOK fT fLam fGenWords fRootV repD tD adOf
  ptOf fpt unpack pack nPts affOf affApply adMat meq sigW eOf adPow ofDigits3 tMats matOf mone)

@[expose] def GoodC (x : Gmat) : Prop := InvertedByTwoA x ∨ IsConj x tbw

theorem goodC_conj {x : Gmat} (h : GoodC x) (c : Gmat) : GoodC (c * x * c⁻¹) :=
  h.imp (fun h => invertedByTwoA_conj h c) (fun h => (isConj_iff.2 ⟨c, rfl⟩).symm.trans h)

theorem goodC_iff_conj (x c : Gmat) : GoodC (c * x * c⁻¹) ↔ GoodC x := by
  refine ⟨fun h => ?_, fun h => goodC_conj h c⟩
  have := goodC_conj h c⁻¹
  simpa [mul_assoc] using this

section Roots

theorem goodC_of_same_data
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {R y : Gmat} {D : ActD 12} (hR : R ∈ tbL) (hRD : IsAct tbSys R D) (hD : D ≠ idD 12)
    (hR3 : R ^ 3 = 1) (hgood : ∀ e < 3, GoodC (R * tbw ^ e)) (hy : y ∈ tbL)
    (hyD : IsAct tbSys y D) (hy3 : y ^ 3 = 1) : GoodC y := by
  obtain ⟨b, e, he, hb⟩ :=
    exists_conj_of_same_data hP hR hRD hD (by rw [hR3]; exact one_mem _) hy hyD hy3
  have h := hgood e he
  rw [← hb] at h
  exact (goodC_iff_conj y b).1 h

theorem goodC_of_idData
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {y : Gmat} (hy : y ∈ tbL) (hyD : IsAct tbSys y (idD 12)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hw : GoodC tbw) : GoodC y := by
  have hyC : y ∈ CQ := ⟨mem_centralizer_of_isAct hyD, hy⟩
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hyw := hP _ ((Subgroup.zpowers_le).2 hyC) hyp (Subgroup.mem_zpowers y)
  obtain ⟨e, he, rfl⟩ := exists_pow_eq_of_mem_zpowers hyw
  interval_cases e
  · exact absurd (pow_zero tbw) hy1
  · rwa [pow_one]
  · have h2 : tbb₁⁻¹ * tbw * tbb₁ = tbw ^ 2 := isAct_b₁.2
    rw [← h2]
    have := goodC_conj hw tbb₁⁻¹
    rwa [inv_inv] at this

theorem goodC_mul_pow_of_collapse {R u : Gmat} (hu : u ∈ QQ) (hc : u⁻¹ * R * u = R * tbw)
    (hR : GoodC R) : ∀ e, GoodC (R * tbw ^ e)
  | 0 => by rwa [pow_zero, mul_one]
  | e + 1 => by
    have ih := goodC_mul_pow_of_collapse hu hc hR e
    have hw : u * tbw ^ e = tbw ^ e * u :=
      tbCommData.commute_of_mem hu (Subgroup.pow_mem _ (Subgroup.mem_zpowers tbw) e)
    have h := goodC_conj ih u⁻¹
    rw [inv_inv] at h
    have e1 : u⁻¹ * (R * tbw ^ e) * u = R * tbw ^ (e + 1) := by
      calc u⁻¹ * (R * tbw ^ e) * u = u⁻¹ * R * (tbw ^ e * u) := by group
        _ = u⁻¹ * R * u * tbw ^ e := by rw [← hw]; group
        _ = R * tbw ^ (e + 1) := by rw [hc, pow_succ']; group
    rwa [e1] at h

@[expose] def RootGoodC (c : ℕ × List ℕ × ℕ × List ℕ) : Prop :=
  if c.2.2.1 = 0 ∨ c.2.2.1 = 1 then True
  else if c.2.2.1 = 3 then GoodC (repG c.1 c.2.1)
  else if c.2.2.1 = 4 then GoodC tbw
  else ∀ e < 3, GoodC (repG c.1 c.2.1 * tbw ^ e)

theorem goodC_of_claim (hinv : letterInvCheck () = true)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {c : ℕ × List ℕ × ℕ × List ℕ} (ht3 : tG c.1 ^ 3 = 1) (hok : rootOK c = true)
    (hgood : RootGoodC c) {y : Gmat} (hy : y ∈ tbL) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyD : IsAct tbSys y (toD (repD c.1 c.2.1))) : GoodC y := by
  obtain ⟨k, v, s, yv⟩ := c
  simp only at ht3 hyD
  have hRD := isAct_repG hinv k v
  unfold rootOK at hok
  unfold RootGoodC at hgood
  simp only at hok hgood
  by_cases hs0 : s = 0
  · rw [ite_eq_left hs0] at hok
    exact (false_of_adPow hyD hy3 (by simpa using hok)).elim
  by_cases hs4 : s = 4
  · rw [ite_eq_right hs0, ite_eq_left hs4] at hok
    have hid : toD (repD k v) = idD 12 := by rw [adEq_sound hok, toD_adOne]
    rw [hid] at hyD
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs4] at hgood
    exact goodC_of_idData hP hy hyD hy3 hy1 hgood
  rw [ite_eq_right hs0, ite_eq_right hs4] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hnid, hcube⟩, hcol⟩ := hok
  have hD : toD (repD k v) ≠ idD 12 := by
    intro h
    rw [← toD_adOne] at h
    rw [adEq_complete h] at hnid
    simp at hnid
  have hcu := cube_eq (isAct_tG hinv k) ht3 (eOf v 0)
  by_cases hs1 : s = 1
  · rw [ite_eq_left hs1] at hcube
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcube
    obtain ⟨hc0, hc1⟩ := hcube
    have hR3 : repG k v ^ 3 = tbw ^ (toZ (cubeE (B0 ()) (tDk k) (eOf v 0)).2).val := by
      rw [repG, hcu, ← eeq_sound hc0, toE_zero_pair, tbSys_nf_zero]
    refine (false_of_same_data hP (repG_mem k v) hRD hD ?_ ?_ hy hyD hy3).elim
    · rw [hR3]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers tbw) _
    · rw [hR3]
      refine pow_ne_one_of_lt_orderOf ?_ ?_
      · rw [toZ_val]
        intro h0
        exact hc1 (Fin.ext h0)
      · rw [orderOf_tbw, toZ_val]
        exact Fin.isLt _
  rw [ite_eq_right hs1] at hcube
  have hR3 : repG k v ^ 3 = 1 := by
    rw [repG, hcu, eeq_sound hcube, toE_eone, Sys.nf_eone]
  by_cases hs3 : s = 3
  · rw [hs3] at hcol
    simp only [bne_self_eq_false, Bool.false_or] at hcol
    rw [ite_eq_right (by omega), ite_eq_left hs3] at hgood
    have hz := zconj_eq (isAct_tG hinv k) (eOf v 0) (eOf yv 0)
    rw [eeq_sound hcol, toE_emul, toE_zero_pair, ← tbSys_B, ← Sys.nf_mul tbSys_good,
      tbSys_nf_zero, toZ_one, ZMod.val_one, pow_one] at hz
    refine goodC_of_same_data hP (repG_mem k v) hRD hD hR3
      (fun e _ => goodC_mul_pow_of_collapse (u := tbSys.nf (toE (eOf yv 0))) (tbSys_nf_mem _) ?_
        hgood e) hy hyD hy3
    unfold repG
    rw [hz, mul_assoc]
  · rw [ite_eq_right (by omega), ite_eq_right hs3, ite_eq_right hs4] at hgood
    exact goodC_of_same_data hP (repG_mem k v) hRD hD hR3 hgood hy hyD hy3

theorem goodC_of_fibre (hinv : letterInvCheck () = true)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    (hroots : rootsOK () = true) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGoodC c) {k : ℕ} (hk4 : k < 4) (hk : FibreRoots k)
    {p : ℕ} (hp : p < nPts) {x : Gmat} (hx : x ∈ tbL) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxD : IsAct tbSys x (toD (fpt (fT k) (fLam k) (unpack p)))) : GoodC x := by
  obtain ⟨g, hg, v, hv, hgx⟩ := hk p hp x hxD
  obtain ⟨c, hc, hck, hcv⟩ := rootClaims_cover k hk4 v hv
  have hok : rootOK c = true := List.all_eq_true.1 hroots c hc
  have hyL : g⁻¹ * x * g ∈ tbL := tbL.mul_mem (tbL.mul_mem (tbL.inv_mem hg) hx) hg
  have hy3 : (g⁻¹ * x * g) ^ 3 = 1 := by rw [conj_pow_inv, hx3]; group
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hy := goodC_of_claim hinv hP (c := c) (by rw [hck]; exact ht3 k hk4) hok (hgood c hc) hyL hy3
    hy1 (by rw [hck, hcv]; exact hgx)
  have := goodC_conj hy g
  simpa [mul_assoc] using this

theorem goodC_tbw_sq (hw : GoodC tbw) : GoodC (tbw ^ 2) := by
  have h2 : tbb₁⁻¹ * tbw * tbb₁ = tbw ^ 2 := isAct_b₁.2
  rw [← h2]
  have := goodC_conj hw tbb₁⁻¹
  rwa [inv_inv] at this

theorem goodC_of_conj_pow {c r : Gmat} {z : ℕ} (h : c⁻¹ * r * c = tbw ^ z) (hw : GoodC (tbw ^ z)) :
    GoodC r := by
  rw [← h] at hw
  have := goodC_conj hw c
  simpa [mul_assoc] using this

theorem t3_classes (ht : IsTwoA (gw tstdW)) (htk : gw (tkW 3) = tG 3)
    (hX : agreeAll m3bT3Eqs = true) :
    InvertedByTwoA (tG 3) ∧ IsConj (tG 3 * tbw) tbw ∧ IsConj (tG 3 * tbw ^ 2) tbw := by
  simp only [m3bT3Eqs, agreeAll_append_iff, and_assoc] at hX
  obtain ⟨hl0, hinv, hl12, hc1, hc2⟩ := hX
  have e0 := agreeAll_sound hl0 (m3bT3R0Word, tkW 3) (by simp)
  have e1 := agreeAll_sound hl12 (m3bT3R1Word, tbW ++ m3bT3R0Word) (by simp)
  have e2 := agreeAll_sound hl12 (m3bT3R2Word, powL 2 tbW ++ m3bT3R0Word) (by simp)
  simp only [gw_append, tb_gw_powL] at e0 e1 e2
  have hw : gw tbW = tbw := rfl
  rw [hw] at e1 e2
  rw [htk] at e0
  refine ⟨?_, ?_, ?_⟩
  · have := invEqs_sound ht hinv
    rwa [e0] at this
  · have h := conjEqs_sound hc1
    rw [e1, e0] at h
    rw [pow_one] at h
    exact isConj_iff.2 ⟨(gw m3bT3C1Word)⁻¹, by simpa using h⟩
  · have h := conjEqs_sound hc2
    rw [e2, e0] at h
    rw [pow_one] at h
    exact isConj_iff.2 ⟨(gw m3bT3C2Word)⁻¹, by simpa using h⟩

theorem rootGoodC_of_eqs (ht : IsTwoA tGmat) (hE : agreeAll m3bEqs = true)
    (hX : agreeAll m3bT3Eqs = true) : ∀ c ∈ rootClaims, RootGoodC c := by
  unfold m3bEqs at hE
  rw [agreeAll_append_iff] at hE
  obtain ⟨hB, hC⟩ := hE
  obtain ⟨hb1, hb2, htk, -, hstd⟩ := base_facts hB
  have hT : IsTwoA (gw tstdW) := ht.of_isConj hstd
  simp only [m3bClassEqs, agreeAll_append_iff, and_assoc] at hC
  obtain ⟨-, iq1, cq0, c1, i1a, i1b, c1d, i20, i21, i22, -, c3h, i3g⟩ := hC
  obtain ⟨hI3, hC31, hC32⟩ := t3_classes hT (htk 3 (by norm_num) le_rfl) hX
  have hw : GoodC tbw := Or.inr (IsConj.refl _)
  have hw2 := goodC_tbw_sq hw
  have hw1 : GoodC (tbw ^ 1) := by rw [pow_one]; exact hw
  have ht1 := htk 1 le_rfl (by norm_num)
  have ht2 := htk 2 (by norm_num) (by norm_num)
  have ht3 := htk 3 (by norm_num) le_rfl
  intro c hc
  simp only [rootClaims, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    exact hw
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    rw [repG_eq, show tG 0 = 1 from ite_eq_left rfl, one_mul,
      nf_vecL_single 1 (by funext i; fin_cases i <;> simp [vecL])]
    exact Or.inl (invEqs_sound hT iq1)
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    rw [repG_eq, show tG 0 = 1 from ite_eq_left rfl, one_mul,
      nf_vecL_single 0 (by funext i; fin_cases i <;> simp [vecL])]
    exact goodC_of_conj_pow (conjEqs_sound cq0) hw2
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e he
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    rw [repG_eq, hv]
    interval_cases e
    · have h := conjEqs_sound c1
      rw [gw_repW ht1] at h
      exact goodC_of_conj_pow h hw1
    · have h := invEqs_sound hT i1a
      rw [gw_repW ht1] at h
      exact Or.inl h
    · have h := invEqs_sound hT i1b
      rw [gw_repW ht1] at h
      exact Or.inl h
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have hv : vecL [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [0, 0, 0, 1] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    have h := conjEqs_sound c1d
    rw [gw_repW ht1, pow_zero, mul_one] at h
    rw [repG_eq, hv]
    exact goodC_of_conj_pow h hw1
  ·
    unfold RootGoodC
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e he
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    rw [repG_eq, hv]
    interval_cases e
    · have h := invEqs_sound hT i20
      rw [gw_repW ht2] at h
      exact Or.inl h
    · have h := invEqs_sound hT i21
      rw [gw_repW ht2] at h
      exact Or.inl h
    · have h := invEqs_sound hT i22
      rw [gw_repW ht2] at h
      exact Or.inl h
  ·
    unfold RootGoodC
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    intro e he
    have hv : vecL [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 0 := by
      funext i; fin_cases i <;> simp [vecL]
    rw [repG_eq, nf_vecL_zero hv, mul_one]
    interval_cases e
    · rw [pow_zero, mul_one]
      exact Or.inl hI3
    · rw [pow_one]
      exact Or.inr hC31
    · exact Or.inr hC32
  ·
    unfold RootGoodC
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGoodC
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have h := conjEqs_sound c3h
    rw [gw_repW ht3, pow_zero, mul_one] at h
    rw [repG_eq]
    exact goodC_of_conj_pow h hw1
  ·
    unfold RootGoodC
    rw [ite_eq_left (by decide)]
    trivial
  ·
    unfold RootGoodC
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    have hv : vecL [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] = vecL [0, 1, 0, 1] :=
      vecL_eq fun i hi => by interval_cases i <;> simp
    have h := invEqs_sound hT i3g
    rw [gw_repW ht3, pow_zero, mul_one] at h
    rw [repG_eq, hv]
    exact Or.inl h

end Roots

section Final

theorem goodC_of_mem_tbL (hinv : letterInvCheck () = true) (hsyl : SylFact)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    (hroots : rootsOK () = true) (hfib : ∀ k < 4, FibreRoots k) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGoodC c) {x : Gmat} (hx : x ∈ tbL) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : GoodC x := by
  by_cases hρ : CommData.actMat 3 tbq tbw tbM x = 1
  · obtain ⟨D, hD⟩ := exists_isAct hx
    have hl := lam_eq_one hD hx3
    have hm : (Matrix.of fun i => (D.1 i).1) = toMatrix (fT 0) := by
      rw [← actMat_of_isAct hD, hρ]
      unfold fT
      rw [ite_eq_left rfl, toMatrix_mone]
    have hT : ∀ i, (D.1 i).1 = toMat (fT 0) i := fun i => congrFun hm i
    have hL : D.2 = toZ (fLam 0) := by
      unfold fLam
      rw [ite_eq_left rfl, hl, toZ_one]
    obtain ⟨p, hp, hxp⟩ := exists_fpt_of_isAct hD hT hL
    exact goodC_of_fibre hinv hP hroots ht3 hgood (k := 0) (by norm_num) (hfib 0 (by norm_num))
      hp hx hx3 hx1 hxp
  · obtain ⟨g, hg, j, hj, hgx⟩ := exists_conj_tMats hsyl hx hx3 hρ
    obtain ⟨y, hydef⟩ : ∃ y, y = g⁻¹ * x * g := ⟨_, rfl⟩
    rw [← hydef] at hgx
    have hy : y ∈ tbL := by
      rw [hydef]; exact tbL.mul_mem (tbL.mul_mem (tbL.inv_mem hg) hx) hg
    have hy3 : y ^ 3 = 1 := by rw [hydef, conj_pow_inv, hx3]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [← hydef, h]; group
    obtain ⟨D, hD⟩ := exists_isAct hy
    have hl := lam_eq_one hD hy3
    have htD := isAct_evalG hinv sigW[j]!
    have ht3' : evalG letterG sigW[j]! ^ 3 = 1 := by
      have := ht3 (j + 1) (by omega)
      unfold tG at this
      rwa [ite_eq_right (by omega), Nat.add_sub_cancel] at this
    have hm : (Matrix.of fun i => (D.1 i).1) =
        Matrix.of fun i => ((toD (adOf (B0 ()) (LA ()) sigW[j]!)).1 i).1 := by
      rw [← actMat_of_isAct hD, hgx, tMats_get hj, ← actMat_evalG, actMat_of_isAct htD]
    have hfT : fT (j + 1) = adMat (tD (j + 1)) := by
      unfold fT; rw [ite_eq_right (by omega)]
    have hT : ∀ i, (D.1 i).1 = toMat (fT (j + 1)) i := by
      intro i
      rw [hfT, toMat_adMat_row, tD_succ]
      exact congrFun hm i
    have hL : D.2 = toZ (fLam (j + 1)) := by
      have h2 : fLam (j + 1) = (tD (j + 1)).2 := by
        unfold fLam; rw [ite_eq_right (by omega)]
      rw [h2, hl, tD_succ]
      exact (lam_eq_one htD ht3').symm
    obtain ⟨p, hp, hyp⟩ := exists_fpt_of_isAct hD hT hL
    have hyg := goodC_of_fibre hinv hP hroots ht3 hgood (k := j + 1) (by omega)
      (hfib _ (by omega)) hp hy hy3 hy1 hyp
    rw [hydef] at hyg
    have := goodC_conj hyg g
    simpa [mul_assoc] using this

theorem goodC_of_pow_three (hinv : letterInvCheck () = true) (hsyl : SylFact)
    (hroots : rootsOK () = true) (hfib : ∀ k < 4, FibreRoots k) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGoodC c) {x : Gmat} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    GoodC x := by
  have : Finite Gmat := finite_Gmat
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨g, hg⟩ := exists_conj_mem_tbL hsyl hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h := goodC_of_mem_tbL hinv hsyl (le_zpowers_of_le_CQ hsyl) hroots hfib ht3 hgood hg hy3
    hy1
  exact (goodC_iff_conj x g).1 h

end Final

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

namespace CFSG.HardMathSupport.Dickson.Sec6.BM2

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
  CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
  CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.HardMathSupport.Dickson.Sec6.BM

theorem m3bT3Eqs_all : agreeAll m3bT3Eqs = true :=
  Certificates.certificate17473

section Class

theorem m3bClass_holds : M3BClass := by
  have hE := m3bEqs_all
  have hX := m3bT3Eqs_all
  have ht : IsTwoA tGmat := ⟨CFSG.Monster.Tri.orderOf_tGmat, natCard_centralizer_tStar⟩
  have hE' : agreeAll (m3bBaseEqs ++ m3bClassEqs) = true := hE
  obtain ⟨-, -, -, ht3, -⟩ := base_facts (agreeAll_append_iff.1 hE').1
  intro x hx hxi
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hg := goodC_of_pow_three Certificates.certificate136200
    Certificates.certificate136201 Certificates.certificate136202
    (fun k hk => ?_) ht3 (rootGoodC_of_eqs ht hE hX) hx3 hx1
  · exact hg.resolve_left hxi
  · interval_cases k
    · exact Certificates.certificate136203
    · exact Certificates.certificate136204
    · exact Certificates.certificate136205
    · exact Certificates.certificate136206

end Class

end CFSG.HardMathSupport.Dickson.Sec6.BM2

module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBElem
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterGood
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFibreFact
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCoset
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFibre
public import CFSG.Sporadic.Suz.Simple

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget B0 LA nfD cubeE zconjE WT
  fibreOK fibreFull fibreAffs fibreGensOK fibreGenOK fT fLam fGenWords fRootV repD tD adOf
  ptOf fpt unpack pack nPts affOf affApply adMat meq sigW eOf adPow ofDigits3)

section Good

variable {G : Type} [Group G]

@[expose] def KleinData (x : G) : Prop :=
  ∃ a b : G, a ∈ Subgroup.centralizer ({x} : Set G) ∧ b ∈ Subgroup.centralizer ({x} : Set G) ∧
    orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b ∧
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({a * b} : Set G)) = 2 * monsterBabyOrder

@[expose] def GoodK (x : G) : Prop := InvertedByTwoA x ∨ KleinData x

theorem kleinData_conj {x : G} (h : KleinData x) (c : G) : KleinData (c * x * c⁻¹) := by
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb, hcab⟩ := h
  have hconj : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      c * z * c⁻¹ ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hz]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group
  have hmul : c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
  refine ⟨c * a * c⁻¹, c * b * c⁻¹, hconj a haC, hconj b hbC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ha]; exact MulEquiv.orderOf_eq (MulAut.conj c) a
  · rw [← hb]; exact MulEquiv.orderOf_eq (MulAut.conj c) b
  · rw [hmul]
    calc c * (a * b) * c⁻¹ = c * (b * a) * c⁻¹ := by rw [hab]
      _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
  · intro h
    apply hne
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  · rw [natCard_centralizer_conj']; exact hca
  · rw [natCard_centralizer_conj']; exact hcb
  · rw [hmul, natCard_centralizer_conj']; exact hcab

theorem goodK_conj {x : G} (h : GoodK x) (c : G) : GoodK (c * x * c⁻¹) :=
  h.imp (fun h => invertedByTwoA_conj h c) (fun h => kleinData_conj h c)

theorem goodK_iff_conj (x c : G) : GoodK (c * x * c⁻¹) ↔ GoodK x := by
  refine ⟨fun h => ?_, fun h => goodK_conj h c⟩
  have := goodK_conj h c⁻¹
  simpa [mul_assoc] using this

end Good

theorem ofDigits3_lt : ∀ ds : List ℕ, (∀ d ∈ ds, d < 3) → ofDigits3 ds < 3 ^ ds.length
  | [], _ => by simp [ofDigits3]
  | d :: ds, h => by
    have hd := h d List.mem_cons_self
    have ih := ofDigits3_lt ds (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [ofDigits3, List.foldr_cons, List.length_cons, pow_succ] at ih ⊢
    omega

theorem pack_lt (c : Vec) : pack c < nPts := by
  have h := ofDigits3_lt (List.ofFn fun i : Fin 12 => (vget c i).val) (fun d hd => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
    exact (vget c j).isLt)
  simpa [pack, nPts] using h

@[expose] def ofZ (a : ZMod 3) : F3 := a

theorem exists_fpt_of_isAct {g : Gmat} {D : ActD 12} {T : Mat} {lam : F3}
    (h : IsAct tbSys g D) (hT : ∀ i, (D.1 i).1 = toMat T i) (hl : D.2 = toZ lam) :
    ∃ p < nPts, IsAct tbSys g (toD (fpt T lam (unpack p))) := by
  refine ⟨pack (vofFn fun i => ofZ (D.1 i).2), pack_lt _, ?_⟩
  have e : toD (fpt T lam (unpack (pack (vofFn fun i => ofZ (D.1 i).2)))) = D := by
    rw [toD_fpt, vfun_unpack_pack, vfun_vofFn]
    refine Prod.ext (funext fun i => Prod.ext (hT i).symm rfl) hl.symm
  rw [e]
  exact h

section Fibre

theorem letterG_zero : letterG 0 = tbb₁ := by
  unfold letterG; rw [ite_eq_left rfl]

theorem letterG_one : letterG 1 = tbb₂ := by
  unfold letterG; rw [ite_eq_right (by decide), ite_eq_left rfl]

theorem letterG_two : letterG 2 = tbb₁⁻¹ := by
  unfold letterG; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem letterG_three : letterG 3 = tbb₂⁻¹ := by
  unfold letterG
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left rfl]

end Fibre

section Roots

theorem exists_pow_eq_of_mem_zpowers {z : Gmat} (hz : z ∈ Subgroup.zpowers tbw) :
    ∃ e < 3, z = tbw ^ e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h := zpow_mod_orderOf tbw k
  rw [orderOf_tbw] at h
  push_cast at h
  rw [← zpow_natCast, Int.toNat_of_nonneg h0, h]

theorem commute_tbw_of_isAct {R : Gmat} {D : ActD 12} (h : IsAct tbSys R D) (hl : D.2 = 1) :
    R * tbw = tbw * R := by
  have h2 : R⁻¹ * tbw * R = tbw := by
    have := h.2
    rw [hl, ZMod.val_one, pow_one] at this
    exact this
  calc R * tbw = R * (R⁻¹ * tbw * R) := by rw [h2]
    _ = tbw * R := by group

theorem not_mem_CQ_of_isAct {R : Gmat} {D : ActD 12} (h : IsAct tbSys R D) (hD : D ≠ idD 12) :
    R ∉ CQ := fun hR => hD (isAct_unique h (isAct_of_mem_centralizer hR.1))

theorem exists_conj_of_same_data
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {R y : Gmat} {D : ActD 12} (hR : R ∈ tbL) (hRD : IsAct tbSys R D) (hD : D ≠ idD 12)
    (hR3 : R ^ 3 ∈ Subgroup.zpowers tbw) (hy : y ∈ tbL) (hyD : IsAct tbSys y D)
    (hy3 : y ^ 3 = 1) : ∃ b : Gmat, ∃ e < 3, b * y * b⁻¹ = R * tbw ^ e := by
  have hRw := commute_tbw_of_isAct hRD (lam_eq_one hyD hy3)
  have hcC : y * R⁻¹ ∈ CQ :=
    ⟨mul_inv_mem_centralizer hyD hRD, tbL.mul_mem hy (tbL.inv_mem hR)⟩
  have hyc : y = y * R⁻¹ * R := (inv_mul_cancel_right y R).symm
  obtain ⟨b, z, hz, hb⟩ := exists_conj_eq_mul_zpowers (C := CQ) orderOf_tbw tbw_mem_CQ hRw
    (fun x hx => mul_tbw_of_mem_CQ hx) hP (fun x hx => conj_mem_CQ hR hx) hR3
    (not_mem_CQ_of_isAct hRD hD) hcC (by rw [← hyc]; exact hy3)
  obtain ⟨e, he, rfl⟩ := exists_pow_eq_of_mem_zpowers hz
  exact ⟨b, e, he, by rw [hyc]; exact hb⟩

theorem goodK_of_same_data
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {R y : Gmat} {D : ActD 12} (hR : R ∈ tbL) (hRD : IsAct tbSys R D) (hD : D ≠ idD 12)
    (hR3 : R ^ 3 = 1) (hgood : ∀ e < 3, GoodK (R * tbw ^ e)) (hy : y ∈ tbL)
    (hyD : IsAct tbSys y D) (hy3 : y ^ 3 = 1) : GoodK y := by
  obtain ⟨b, e, he, hb⟩ :=
    exists_conj_of_same_data hP hR hRD hD (by rw [hR3]; exact one_mem _) hy hyD hy3
  have h := hgood e he
  rw [← hb] at h
  exact (goodK_iff_conj y b).1 h

theorem false_of_same_data
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {R y : Gmat} {D : ActD 12} (hR : R ∈ tbL) (hRD : IsAct tbSys R D) (hD : D ≠ idD 12)
    (hR3 : R ^ 3 ∈ Subgroup.zpowers tbw) (hR3' : R ^ 3 ≠ 1) (hy : y ∈ tbL)
    (hyD : IsAct tbSys y D) (hy3 : y ^ 3 = 1) : False := by
  obtain ⟨b, e, -, hb⟩ := exists_conj_of_same_data hP hR hRD hD hR3 hy hyD hy3
  have hRw : Commute R (tbw ^ e) :=
    (Commute.pow_right (commute_tbw_of_isAct hRD (lam_eq_one hyD hy3)) e)
  have h1 : (b * y * b⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
  rw [hb, hRw.mul_pow, ← pow_mul, mul_comm e 3, pow_mul, tbw_pow_three, one_pow, mul_one] at h1
  exact hR3' h1

theorem false_of_adPow {y : Gmat} {D : AD} (hyD : IsAct tbSys y (toD D)) (hy3 : y ^ 3 = 1)
    (h : _root_.Timmesfeld.M3B.adEq (adPow (B0 ()) D 3) _root_.Timmesfeld.M3B.adOne = false) :
    False := by
  have h1 := isAct_adPow hyD 3
  rw [hy3] at h1
  rw [adEq_complete (isAct_unique h1 isAct_adOne)] at h
  exact Bool.false_ne_true h.symm

theorem goodK_of_idData
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {y : Gmat} (hy : y ∈ tbL) (hyD : IsAct tbSys y (idD 12)) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hw : GoodK tbw) : GoodK y := by
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
    have := goodK_conj hw tbb₁⁻¹
    rwa [inv_inv] at this

theorem goodK_mul_pow_of_collapse {R u : Gmat} (hu : u ∈ QQ) (hc : u⁻¹ * R * u = R * tbw)
    (hR : GoodK R) : ∀ e, GoodK (R * tbw ^ e)
  | 0 => by rwa [pow_zero, mul_one]
  | e + 1 => by
    have ih := goodK_mul_pow_of_collapse hu hc hR e
    have hw : u * tbw ^ e = tbw ^ e * u :=
      tbCommData.commute_of_mem hu (Subgroup.pow_mem _ (Subgroup.mem_zpowers tbw) e)
    have h := goodK_conj ih u⁻¹
    rw [inv_inv] at h
    have e1 : u⁻¹ * (R * tbw ^ e) * u = R * tbw ^ (e + 1) := by
      calc u⁻¹ * (R * tbw ^ e) * u = u⁻¹ * R * (tbw ^ e * u) := by group
        _ = u⁻¹ * R * u * tbw ^ e := by rw [← hw]; group
        _ = R * tbw ^ (e + 1) := by rw [hc, pow_succ']; group
    rwa [e1] at h

@[expose] noncomputable def tG (k : ℕ) : Gmat := if k = 0 then 1 else evalG letterG sigW[k - 1]!

@[expose] noncomputable def repG (k : ℕ) (v : List ℕ) : Gmat := tG k * tbSys.nf (toE (eOf v 0))

theorem tG_mem (k : ℕ) : tG k ∈ tbL := by
  unfold tG
  split_ifs
  · exact tbL.one_mem
  · exact tbL_mem_evalG _

theorem repG_mem (k : ℕ) (v : List ℕ) : repG k v ∈ tbL :=
  tbL.mul_mem (tG_mem k) (QQ_le_tbL (tbSys_nf_mem _))

theorem isAct_tG (hinv : letterInvCheck () = true) (k : ℕ) : IsAct tbSys (tG k) (toD (tDk k)) := by
  unfold tG tDk
  split_ifs
  · exact isAct_adOne
  · exact isAct_evalG hinv _

theorem isAct_repG (hinv : letterInvCheck () = true) (k : ℕ) (v : List ℕ) :
    IsAct tbSys (repG k v) (toD (repD k v)) := by
  unfold repG repD
  by_cases hk : k = 0
  · simp only [hk, ite_true]
    rw [show tG 0 = 1 from ite_eq_left rfl, one_mul]
    exact isAct_nf _
  · simp only [hk, ite_false]
    rw [toD_comp, ← tbSys_B]
    have h := isAct_tG hinv k
    unfold tDk at h
    rw [ite_eq_right hk] at h
    exact h.mul tbSys_good (isAct_nf _)

@[expose] def RootGood (c : ℕ × List ℕ × ℕ × List ℕ) : Prop :=
  if c.2.2.1 = 0 ∨ c.2.2.1 = 1 then True
  else if c.2.2.1 = 3 then GoodK (repG c.1 c.2.1)
  else if c.2.2.1 = 4 then GoodK tbw
  else ∀ e < 3, GoodK (repG c.1 c.2.1 * tbw ^ e)

theorem goodK_of_claim (hinv : letterInvCheck () = true)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    {c : ℕ × List ℕ × ℕ × List ℕ} (ht3 : tG c.1 ^ 3 = 1) (hok : rootOK c = true)
    (hgood : RootGood c) {y : Gmat} (hy : y ∈ tbL) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyD : IsAct tbSys y (toD (repD c.1 c.2.1))) : GoodK y := by
  obtain ⟨k, v, s, yv⟩ := c
  simp only at ht3 hyD
  have hRD := isAct_repG hinv k v
  unfold rootOK at hok
  unfold RootGood at hgood
  simp only at hok hgood
  by_cases hs0 : s = 0
  · rw [ite_eq_left hs0] at hok
    exact (false_of_adPow hyD hy3 (by simpa using hok)).elim
  by_cases hs4 : s = 4
  · rw [ite_eq_right hs0, ite_eq_left hs4] at hok
    have hid : toD (repD k v) = idD 12 := by rw [adEq_sound hok, toD_adOne]
    rw [hid] at hyD
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hs4] at hgood
    exact goodK_of_idData hP hy hyD hy3 hy1 hgood
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
    refine goodK_of_same_data hP (repG_mem k v) hRD hD hR3
      (fun e _ => goodK_mul_pow_of_collapse (u := tbSys.nf (toE (eOf yv 0))) (tbSys_nf_mem _) ?_
        hgood e) hy hyD hy3
    unfold repG
    rw [hz, mul_assoc]
  · rw [ite_eq_right (by omega), ite_eq_right hs3, ite_eq_right hs4] at hgood
    exact goodK_of_same_data hP (repG_mem k v) hRD hD hR3 hgood hy hyD hy3

theorem rootClaims_cover :
    ∀ k < 4, ∀ v ∈ fRootV k, ∃ c ∈ rootClaims, c.1 = k ∧ c.2.1 = v := by
  decide

theorem goodK_of_fibre (hinv : letterInvCheck () = true)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    (hroots : rootsOK () = true) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGood c) {k : ℕ} (hk4 : k < 4) (hk : FibreRoots k)
    {p : ℕ} (hp : p < nPts) {x : Gmat} (hx : x ∈ tbL) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxD : IsAct tbSys x (toD (fpt (fT k) (fLam k) (unpack p)))) : GoodK x := by
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
  have hy := goodK_of_claim hinv hP (c := c) (by rw [hck]; exact ht3 k hk4) hok (hgood c hc) hyL hy3
    hy1 (by rw [hck, hcv]; exact hgx)
  have := goodK_conj hy g
  simpa [mul_assoc] using this

end Roots

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

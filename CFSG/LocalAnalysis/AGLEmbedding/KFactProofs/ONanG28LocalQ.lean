module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.RankThree.PartTwo.Sec5.Tools

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers

section Q

attribute [local irreducible] txL tU tZ tO tzc


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

instance instFiniteMulAutX : Finite (MulAut (adjointGroup .G2 K)) := by
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  exact MulEquiv.finite_left

instance instFiniteX : Finite (adjointGroup .G2 K) := Subtype.finite

variable {bi yi : ℕ} (hq : qOK txL tzc bi yi = true)

@[expose] noncomputable def bE (bi : ℕ) : adjointGroup .G2 K := txElt M bi

theorem rho_bE (hbi : bi < 243) : M.rho (bE M bi) = decode txL[bi]! := rho_txElt M hbi

theorem bE_mem_TX (hbi : bi < 243) : bE M bi ∈ TX M := txElt_mem M hbi

include hq in
theorem bE_pow_three : bE M bi ^ 3 = 1 := by
  obtain ⟨hbi, -, -, -, -, h4, -⟩ := qOK_spec hq
  have h1 : M.rho (bE M bi ^ 3) = decode (powCode txL[bi]! 3) :=
    (M.rho_pow (bE M bi) (valid_txL hbi) (rho_bE M hbi) 3).2
  exact (M.eq_one_iff_code (valid_powCode (valid_txL hbi) 3) h1).2 h4

include hq in
theorem zE_comm_bE : zE M * bE M bi = bE M bi * zE M := by
  obtain ⟨hbi, -, -, -, -, -, h5, -⟩ := qOK_spec hq
  exact (M.eq_iff_codes (valid_mulCode valid_tzc (valid_txL hbi))
    (valid_mulCode (valid_txL hbi) valid_tzc)
    (M.rho_mul_code valid_tzc (valid_txL hbi) (rho_zE M) (rho_bE M hbi))
    (M.rho_mul_code (valid_txL hbi) valid_tzc (rho_bE M hbi) (rho_zE M))).2 h5

include hq in
theorem bE_notMem_zpowers : bE M bi ∉ Subgroup.zpowers (zE M) := by
  obtain ⟨hbi, -, h1, h2, h3, -⟩ := qOK_spec hq
  intro h
  rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers (zE_pow_three M) h with h | h | h
  · exact h1 ((M.eq_one_iff_code (valid_txL hbi) (rho_bE M hbi)).1 h)
  · exact h2 ((M.eq_iff_codes (valid_txL hbi) valid_tzc (rho_bE M hbi) (rho_zE M)).1 h)
  · exact h3 ((M.eq_iff_codes (valid_txL hbi) (valid_mulCode valid_tzc valid_tzc) (rho_bE M hbi)
      (M.rho_mul_code valid_tzc valid_tzc (rho_zE M) (rho_zE M))).1 h)

@[expose] noncomputable def QX (bi : ℕ) : Subgroup (adjointGroup .G2 K) :=
  Subgroup.zpowers (zE M) ⊔ Subgroup.zpowers (bE M bi)

include hq in
theorem QX_spec : CFSG.Assembly.IsElemAbelian 3 (QX M bi) ∧ Nat.card (QX M bi) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, h2⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (isElemAbelian_zpowers' (zE_pow_three M)) (bE_notMem_zpowers M hq) (bE_pow_three M hq)
    (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (zE_comm_bE M hq) k).eq)
  refine ⟨h1, ?_⟩
  rw [QX, h2, Nat.card_zpowers, orderOf_zE]

include hq in
theorem QX_le_TX (hbi : bi < 243) : QX M bi ≤ TX M :=
  sup_le (Subgroup.zpowers_le.mpr (zE_mem_TX M)) (Subgroup.zpowers_le.mpr (bE_mem_TX M hbi))

@[expose] noncomputable def QA (bi : ℕ) : Subgroup (MulAut (adjointGroup .G2 K)) :=
  (QX M bi).map (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))

include hq in
theorem QA_spec : IsElemAbelian 3 (QA M bi) ∧ Nat.card (QA M bi) = 9 := by
  obtain ⟨h1, h2⟩ := QX_spec M hq
  refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ h1, ?_⟩
  rw [QA, Subgroup.card_map_of_injective (conj_injective_X (K := K)), h2]

include hq in
theorem QA_le_T0 (hK : Nat.card K = 8) (hbi : bi < 243) : QA M bi ≤ T0 M hK := by
  rintro _ ⟨q, hq', rfl⟩
  exact conj_mem_T0 M hK (QX_le_TX M hq hbi hq')

@[expose] noncomputable def yA (yi : ℕ) : MulAut (adjointGroup .G2 K) := mk (txElt M yi) 1

theorem isEl_yA (hyi : yi < 243) : IsEl M (yA M yi) (txL[yi]!, 1) :=
  ⟨txElt M yi, rho_txElt M hyi, rfl⟩

theorem yA_mem_T0 (hK : Nat.card K = 8) (hyi : yi < 243) : yA M yi ∈ T0 M hK :=
  mk_mem_T0 M hK (txElt_mem M hyi) (by norm_num)

theorem isEl_one : IsEl M (1 : MulAut (adjointGroup .G2 K)) semiOne :=
  ⟨1, by simp [semiOne, decode_idCode], by simp [semiOne, mk]⟩

include hq in
theorem yA_pow_three (hK : Nat.card K = 8) : yA M yi ^ 3 = 1 := by
  obtain ⟨-, hyi, -, -, -, -, -, h6, -⟩ := qOK_spec hq
  have hv := valid_txL hyi
  have e1 := IsEl.mul hK (p := (txL[yi]!, 1)) (q := (txL[yi]!, 1)) hv hv (isEl_yA M hyi)
    (isEl_yA M hyi)
  have e2 := IsEl.mul hK (p := (txL[yi]!, 1)) (q := semi (txL[yi]!, 1) (txL[yi]!, 1)) hv
    (valid_semi hv hv) (isEl_yA M hyi) e1
  have := (IsEl.inj hK (valid_semi hv (valid_semi hv hv)) (valid_idCode)
    (Nat.mod_lt _ (by norm_num)) (by simp [semiOne]) e2 (isEl_one M)).2 h6
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', pow_two]
  exact this

include hq in
theorem yA_comm_conj_zE (hK : Nat.card K = 8) :
    yA M yi * MulAut.conj (zE M) = MulAut.conj (zE M) * yA M yi := by
  obtain ⟨-, hyi, -, -, -, -, -, -, h7, -⟩ := qOK_spec hq
  have hv := valid_txL hyi
  have e1 := IsEl.mul hK (p := (txL[yi]!, 1)) (q := (tzc, 0)) hv valid_tzc (isEl_yA M hyi)
    (isEl_conj (rho_zE M))
  have e2 := IsEl.mul hK (p := (tzc, 0)) (q := (txL[yi]!, 1)) valid_tzc hv
    (isEl_conj (rho_zE M)) (isEl_yA M hyi)
  exact (IsEl.inj hK (valid_semi hv valid_tzc) (valid_semi valid_tzc hv)
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) e1 e2).2 h7

include hq in
theorem yA_comm_conj_bE (hK : Nat.card K = 8) :
    yA M yi * MulAut.conj (bE M bi) = MulAut.conj (bE M bi) * yA M yi := by
  obtain ⟨hbi, hyi, -, -, -, -, -, -, -, h8⟩ := qOK_spec hq
  have hv := valid_txL hyi
  have hb := valid_txL hbi
  have e1 := IsEl.mul hK (p := (txL[yi]!, 1)) (q := (txL[bi]!, 0)) hv hb (isEl_yA M hyi)
    (isEl_conj (rho_bE M hbi))
  have e2 := IsEl.mul hK (p := (txL[bi]!, 0)) (q := (txL[yi]!, 1)) hb hv
    (isEl_conj (rho_bE M hbi)) (isEl_yA M hyi)
  exact (IsEl.inj hK (valid_semi hv hb) (valid_semi hb hv)
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) e1 e2).2 h8

include hq in
theorem yA_comm_QA (hK : Nat.card K = 8) : ∀ a ∈ QA M bi, a * yA M yi = yA M yi * a := by
  have hle : QA M bi ≤ Subgroup.centralizer ({yA M yi} : Set (MulAut (adjointGroup .G2 K))) := by
    rw [QA, QX, Subgroup.map_sup, sup_le_iff, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.zpowers_le, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨(yA_comm_conj_zE M hq hK).symm, (yA_comm_conj_bE M hq hK).symm⟩
  intro a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha))

include hq in
theorem yA_notMem_QA (hK : Nat.card K = 8) : yA M yi ∉ QA M bi := by
  rintro ⟨q, -, hqy⟩
  have : (mk q 0 : MulAut (adjointGroup .G2 K)) = mk (txElt M yi) 1 := by
    simpa [mk, yA] using hqy
  exact absurd (mk_inj hK (by norm_num) (by norm_num) this).2 (by norm_num)

@[expose] noncomputable def EA (bi yi : ℕ) : Subgroup (MulAut (adjointGroup .G2 K)) :=
  QA M bi ⊔ Subgroup.zpowers (yA M yi)

include hq in
theorem EA_spec (hK : Nat.card K = 8) (hbi : bi < 243) (hyi : yi < 243) :
    EA M bi yi ≤ T0 M hK ∧ QA M bi ≤ EA M bi yi ∧ IsElemAbelian 3 (EA M bi yi) ∧
      Nat.card (EA M bi yi) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, h2⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers (p := 3)
    (QA_spec M hq).1 (yA_notMem_QA M hq hK) (yA_pow_three M hq hK) (yA_comm_QA M hq hK)
  refine ⟨sup_le (QA_le_T0 M hq hK hbi) (Subgroup.zpowers_le.mpr (yA_mem_T0 M hK hyi)),
    le_sup_left, h1, ?_⟩
  rw [EA, h2, (QA_spec M hq).2]

include hq in
theorem yA_mem_normalizer_QA (hK : Nat.card K = 8) :
    yA M yi ∈ Subgroup.normalizer (QA M bi : Set (MulAut (adjointGroup .G2 K))) :=
  mem_normalizer_of_conj_le fun x hx => by
    rw [← yA_comm_QA M hq hK x hx, mul_inv_cancel_right]
    exact hx

include hq in
theorem normalizer_QA_le_weakCore (hK : Nat.card K = 8) (hbi : bi < 243) (hyi : yi < 243) :
    Subgroup.normalizer (QA M bi : Set (MulAut (adjointGroup .G2 K))) ≤
      GLBWeakCore 3 (T0 M hK : Subgroup (MulAut (adjointGroup .G2 K))) := by
  obtain ⟨hEP, hQE, hEab, hE27⟩ := EA_spec M hq hK hbi hyi
  exact normalizer_le_weakCore_of_commutative_overgroup 3 Nat.prime_three hEP hQE hEab.1
    (two_le_pRank_of_card_9 le_rfl (QA_spec M hq).1 (QA_spec M hq).2)
    (three_le_pRank_of_card_27 le_rfl hEab hE27)

end Q

end CFSG.AGLEmbedding.KFactProofs.G28

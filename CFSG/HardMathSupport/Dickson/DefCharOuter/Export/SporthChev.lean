module

public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.Adapters.StatedSmallProjOrders
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports CFSG.ClassicalModels
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4

section Orders

theorem pow_four_dvd_card {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
      (t = .POmegaMinus ∧ 4 ≤ n)) :
    p ^ 4 ∣ Nat.card G := by
  have hf : 1 ≤ f := h.1.2.1
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical h]
  have hmin : CFSG.EvenSmallLie.CatalogOrders.lieMin t ≤ n := by
    rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
      simpa [CFSG.EvenSmallLie.CatalogOrders.lieMin] using hn
  have hexp : 4 ≤ CFSG.EvenSmallLie.CatalogOrders.lieExp t n := by
    rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
      simp only [CFSG.EvenSmallLie.CatalogOrders.lieExp]
    · nlinarith
    · nlinarith
    · exact (show 4 ≤ 4 * 3 by norm_num).trans (Nat.mul_le_mul hn (by omega))
    · exact (show 4 ≤ 4 * 3 by norm_num).trans (Nat.mul_le_mul hn (by omega))
  refine dvd_trans ?_ (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd hmin (p ^ f))
  calc p ^ 4 ∣ p ^ (f * CFSG.EvenSmallLie.CatalogOrders.lieExp t n) :=
        pow_dvd_pow p (by nlinarith)
    _ = (p ^ f) ^ CFSG.EvenSmallLie.CatalogOrders.lieExp t n := by rw [pow_mul]

theorem dvd_card {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
      (t = .POmegaMinus ∧ 4 ≤ n)) : p ∣ Nat.card G :=
  (dvd_pow_self p (by norm_num)).trans (pow_four_dvd_card h ht)

theorem card_of_isLTwoTwentySeven {X : Type} [Group X] (h : IsLTwoTwentySeven X) :
    Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num

theorem not_prime_pow_four_dvd_9828 {p : ℕ} (hp : p.Prime) : ¬ p ^ 4 ∣ 9828 := by
  intro h
  have hle : p ^ 4 ≤ 9828 := Nat.le_of_dvd (by norm_num) h
  have hp9 : p ≤ 9 := by
    by_contra hlt
    have : 10 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  have hp2 := hp.two_le
  interval_cases p <;> first | exact absurd h (by decide) | exact absurd hp (by decide)

theorem not_isLTwoTwentySeven {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
      (t = .POmegaMinus ∧ 4 ≤ n)) : ¬ IsLTwoTwentySeven G := by
  intro hL
  have h1 := pow_four_dvd_card h ht
  rw [card_of_isLTwoTwentySeven hL] at h1
  exact not_prime_pow_four_dvd_9828 h.1.1 h1

theorem exists_noncomm_of_simple_of_sq_dvd {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ Nat.card G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  have hprime : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  have hpd : p ∣ Nat.card G := (dvd_pow_self p (by norm_num)).trans h
  rcases (Nat.dvd_prime hprime).1 hpd with h1 | h1
  · exact hp.one_lt.ne' h1
  · rw [← h1] at h
    have h2 := Nat.le_of_dvd hp.pos h
    have h3 := hp.two_le
    nlinarith

theorem finite_simple_nonab_of_model {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f)
    (ht : (t = .PSp ∧ 2 ≤ n) ∨ (t = .POmegaOdd ∧ 3 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨
      (t = .POmegaMinus ∧ 4 ≤ n)) :
    Finite G ∧ IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨hfin, -, hsimp⟩ := CFSG.LieType.Simplicity.fam_classical_converse G ⟨t, n, p, f, h⟩
  haveI := hfin
  haveI := hsimp
  refine ⟨hfin, hsimp, exists_noncomm_of_simple_of_sq_dvd h.1.1 ?_⟩
  exact (pow_dvd_pow p (by norm_num : 2 ≤ 4)).trans (pow_four_dvd_card h ht)

end Orders

section Chev

theorem nonempty_equiv_of_fixedField_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (K : Type) → [Field K] → Subgroup (GL ι K))
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    (d : ValidLieTypeIndex) (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) : Nonempty (G ≃* (CFSGIndex.lie d).Group) := by
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField d K hK
  exact ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans eT.symm⟩

theorem nonempty_equiv_twistedA_three {G : Type} [Group G]
    (h : StatedClassicalModel G .PSU 4 2 1) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 2 ∧
      Nonempty (G ≃* (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hp : (2 : ℕ).Prime := hadm.1
  have hf : 1 ≤ 1 := hadm.2.1
  have hv := unitaryCatalog_index_valid 4 2 1 hadm
  let _ : Fact (2 : ℕ).Prime := ⟨hp⟩
  let q : PrimePower := ⟨2, 1, hp, by omega⟩
  let L := GaloisField 2 (2 * 1)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * 1) (by omega)]
    norm_num
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 4) φ) (glCongr_statedSU φ 4 (2 ^ 1))
    (glCongr_statedScalars φ)
  have hv' : (LieTypeIndex.twistedA 3 q).Valid := by simpa using hv
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv'
  exact ⟨q, hv', by simp [q, PrimePower.card_def], ⟨(e.trans e1).trans eT.symm⟩⟩

theorem isChevSimple_of_psp {G : Type} [Group G] {r p f : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel G .PSp r p f) : IsChevSimple p G := by
  have h0 := h
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h0
  let _ := hfield
  let _ := hfinite
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  let _ : Fintype K := Fintype.ofFinite K
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hn3
  · by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := eq_three_one_of_pow_eq_three hp hf h3
      obtain ⟨q', hv', hq'card, ⟨e⟩⟩ :=
        nonempty_equiv_twistedA_three (statedClassicalModel_PSU_four_two_of_PSp_two_three h)
      exact Or.inr ⟨.lie ⟨.twistedA 3 q', hv'⟩, ⟨hq'card, rfl⟩, ⟨e⟩⟩
    · have hq2 : p ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
      have hv : (LieTypeIndex.B 2 q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        simp only [PrimePower.card_def, true_and, le_refl]
        exact ⟨hq2, h3⟩
      let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
      have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
      let _ : Fintype Fd := Fintype.ofFinite Fd
      have hcard : Fintype.card K = Fintype.card Fd := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
          ValidLieTypeIndex.card_fixedField]
        simp [ValidLieTypeIndex.fieldOrder, q]
      let φ : K ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
      let e1 := CFSG.ComponentClassification.ClassicalModelStatedBridge.statedProjCongr
        (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) φ)
        (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSp 2 φ)
        (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedScalars φ)
      let eT := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
      exact Or.inl ⟨.lie ⟨.B 2 q, hv⟩, LieTypeIndex.characteristic_B 2 q,
        ⟨(θ.trans e1).trans eT.symm⟩⟩
  · have hv : (LieTypeIndex.C r q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨hn3, hp2⟩, not_false⟩
    let Fd := ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩)
    have _ : Finite Fd := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    let _ : Fintype Fd := Fintype.ofFinite Fd
    have hcard : Fintype.card K = Fintype.card Fd := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        ValidLieTypeIndex.card_fixedField]
      simp [ValidLieTypeIndex.fieldOrder, q]
    let φ : K ≃+* Fd := FiniteField.ringEquivOfCardEq hcard
    let e1 := CFSG.ComponentClassification.ClassicalModelStatedBridge.statedProjCongr
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedSp r φ)
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.map_statedScalars φ)
    let eT := CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv
    exact Or.inl ⟨.lie ⟨.C r q, hv⟩, LieTypeIndex.characteristic_C r q,
      ⟨(θ.trans e1).trans eT.symm⟩⟩

theorem isChevSimple_of_pomegaOdd {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n p f) : IsChevSimple p G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn, hp2⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.B n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
  obtain ⟨e⟩ := nonempty_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadOdd n K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadOdd_comp φ)) ⟨.B n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q hv hp2 hn) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact Or.inl ⟨.lie ⟨.B n q, hv⟩, LieTypeIndex.characteristic_B n q, ⟨e⟩⟩

theorem isChevSimple_of_pomegaPlus {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n p f) : IsChevSimple p G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨e⟩ := nonempty_equiv_of_fixedField_model (fun K _ => StatedOmega (StatedQuadPlus n K))
    (fun φ => CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) ⟨.D n q, hv⟩
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv) (by
      simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  exact Or.inl ⟨.lie ⟨.D n q, hv⟩, LieTypeIndex.characteristic_D n q, ⟨e⟩⟩

theorem isChevSimple_of_pomegaMinus {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n p f) : IsChevSimple p G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : PrimePower := ⟨p, f, hp, by omega⟩
  have hv : (LieTypeIndex.twistedD n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField ⟨.twistedD n q, hv⟩ K (by
    simp [ValidLieTypeIndex.fieldOrder, q, hK])
  have _ : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  exact Or.inl ⟨.lie ⟨.twistedD n q, hv⟩, LieTypeIndex.characteristic_twistedD n q,
    ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

end Chev

section LieModel

theorem statedClassicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Models.LieModel G t n p f)
    (ht : t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    StatedClassicalModel G t n p f :=
  h.2.resolve_right fun ⟨_, d, hd, _⟩ => by
    obtain ⟨d, hv⟩ := d
    rcases ht with rfl | rfl | rfl | rfl <;> cases d <;> exact hd

end LieModel

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth

module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c2
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Gen
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot)

open CFSG.LocalAnalysis.ComponentInitial

section SLCover

theorem false_of_sl_cover_alt5 {m : ℕ} (hm : 2 ≤ m) {E : Type} [Field E] [Finite E] [CharP E 2]
    (hbig : 3 ≤ m ∨ 8 ≤ Nat.card E) {J : Type} [Group J] [Finite J]
    (f : Matrix.SpecialLinearGroup (Fin m) E →* J) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center _) (h60 : Nat.card (J ⧸ Subgroup.center J) = 60) : False := by
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨e, -, hEe⟩ := FiniteField.card E 2
  have hE : Nat.card E = 2 ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hEe]
  have he1 : 1 ≤ (e : ℕ) := e.pos
  have hexp : 3 ≤ (e : ℕ) * (m * (m - 1) / 2) := by
    rcases hbig with h | h
    · have h6 : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul h (by omega)
      have h3 : 3 ≤ m * (m - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h6
      calc 3 ≤ m * (m - 1) / 2 := h3
        _ ≤ (e : ℕ) * (m * (m - 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
    · rw [hE] at h
      have he3 : 3 ≤ (e : ℕ) := by
        by_contra h'
        have : 2 ^ (e : ℕ) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h2 : 2 * 1 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
      have h1 : 1 ≤ m * (m - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
      calc 3 ≤ (e : ℕ) := he3
        _ ≤ (e : ℕ) * (m * (m - 1) / 2) := Nat.le_mul_of_pos_right _ (by omega)
  have h8SL : 8 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) E) := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear E m (by omega)]
    apply Dvd.dvd.mul_right
    rw [hE, ← pow_mul]
    exact (pow_dvd_pow 2 hexp : 2 ^ 3 ∣ _)
  have hodd : Odd (Nat.card E - 1) := by
    rw [hE]
    have h2 : 2 ∣ 2 ^ (e : ℕ) := dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := h2
    have hpos : 0 < 2 ^ (e : ℕ) := by positivity
    exact ⟨c - 1, by omega⟩
  have hZodd : Odd (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E))) := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center E m (by omega)]
    exact Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)
  have hkerodd : Odd (Nat.card f.ker) := Odd.of_dvd_nat hZodd (Subgroup.card_dvd_of_le hker)
  have hcardJ : Nat.card (Matrix.SpecialLinearGroup (Fin m) E) = Nat.card J * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have h8J : 8 ∣ Nat.card J := by
    have h1 : 8 ∣ Nat.card J * Nat.card f.ker := hcardJ ▸ h8SL
    have hcop : Nat.Coprime 8 (Nat.card f.ker) := by
      have : Nat.Coprime (2 ^ 3) (Nat.card f.ker) :=
        Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hkerodd)
      simpa using this
    exact hcop.dvd_of_dvd_mul_right h1
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm
      (by rcases hbig with h | h; exacts [Or.inl h, Or.inr (by omega)])).1.1
  have hZJ : Odd (Nat.card (Subgroup.center J)) :=
    Odd.of_dvd_nat hZodd
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.card_center_dvd_of_surjective hperf f hf hker)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  rw [h60] at h1
  rw [h1] at h8J
  obtain ⟨t, ht⟩ := hZJ
  rw [ht] at h8J
  omega

theorem card_center_quot_of_isAltType {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hJ : GLAPComponent 3 C J) (hJc : IsComponentOf J C) (hJ5 : IsAltType 5 (PSimple 3 J)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 60 := by
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.rf4_pSimple_equiv_center Nat.prime_three hJ hJc.2.2
  obtain ⟨e₂⟩ := hJ5
  rw [← Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, Inputs256b.card_alt5]

theorem nonempty_pSimple_congr {G G' : Type} [Group G] [Group G'] {J : Subgroup G} {J' : Subgroup G'}
    (f : ↥J ≃* ↥J') : Nonempty (PSimple 3 J ≃* PSimple 3 J') := by
  have hO : (GLAPPrimeCore 3 ↥J).map f.toMonoidHom = GLAPPrimeCore 3 ↥J' := glaPPrimeCore_map_iso 3 f
  let e₁ : PQuot 3 J ≃* PQuot 3 J' := QuotientGroup.congr _ _ f hO
  exact ⟨QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)⟩

end SLCover

section Linear

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (glA specialFactor IsGoodFactor
  squarefree_minpoly_glA)

open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryMultiplicity irreducible_of_mem_primaryFactors)

open Polynomial

theorem exists_surjective_map_proj {n : ℕ} {k : Type} [Field k] {G : Type*} [Group G]
    {S : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)} (e : G ≃* S) :
    ∃ f : G →* ↥(S.map (LinearFlag.proj n k)), Function.Surjective f ∧ f.ker ≤ Subgroup.center G := by
  refine ⟨((LinearFlag.proj n k).subgroupMap S).comp e.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ S).comp e.surjective, fun g hg => ?_⟩
  have h1 : LinearFlag.proj n k (e g : Matrix.SpecialLinearGroup (Fin n) k) = 1 :=
    congrArg Subtype.val hg
  have h2 : (e g : Matrix.SpecialLinearGroup (Fin n) k) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
    LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.1 h1)
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y))

theorem false_of_linear_alt5 {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk8 : 8 ≤ Nat.card k) (h64 : n = 2 → Nat.card k ≠ 64)
    (β : MulAut (LinearFlag.projectiveSL n k)) (hβ : β ^ 3 = 1)
    {J : Subgroup (LinearFlag.projectiveSL n k)} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJ5 : IsAltType 5 (PSimple 3 J)) : False := by
  have hcases : (∃ (A : GL (Fin n) k) (c : kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n k A) ∨
      (∃ (h : MulAut (LinearFlag.projectiveSL n k)) (σ : k ≃+* k), orderOf σ = 3 ∧
        β = h * LinearFlag.fieldAut n k σ * h⁻¹) := by
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      exact Inputs141c.projectiveSL_cases_two β hβ
    · refine Inputs141c.projectiveSL_cases_of_three_le hn3 ?_ β hβ
      rw [ringChar.eq k 2]
      norm_num
  rcases hcases with ⟨A, c, hA, rfl⟩ | ⟨h, σ, hσ, rfl⟩
  ·
    have h3 : ((3 : ℕ) : k) ≠ 0 := Inputs141c.three_ne_zero_of_charTwo
    have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut h3 hA J hJ.1
      (glaPComponent_perfect hJ)
    obtain ⟨hJc, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hlay
    have h60 := card_center_quot_of_isAltType hJ hJc hJ5
    obtain ⟨⟨⟨b, hb⟩, hgood⟩, rfl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components h3 hA J hJc
    have hsq := squarefree_minpoly_glA h3 hA
    haveI : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors hb⟩
    haveI : Finite (AdjoinRoot b) := Module.finite_of_finite k
    haveI : CharP (AdjoinRoot b) 2 :=
      charP_of_injective_algebraMap (algebraMap k (AdjoinRoot b)).injective 2
    obtain ⟨eF⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq hb
    obtain ⟨f, hf, hker⟩ := exists_surjective_map_proj eF
    have hkE : Nat.card k ≤ Nat.card (AdjoinRoot b) :=
      Nat.card_le_card_of_injective _ (algebraMap k (AdjoinRoot b)).injective
    have hgood' : IsGoodFactor A b := hgood
    have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) b := by
      rcases hgood' with h | ⟨h, -⟩ <;> omega
    exact false_of_sl_cover_alt5 hm2 (by
      rcases hgood' with h | ⟨-, -⟩
      · exact Or.inl h
      · exact Or.inr (hk8.trans hkE)) f hf hker h60
  ·
    have hc : MulAut.congr h⁻¹ (h * LinearFlag.fieldAut n k σ * h⁻¹) = LinearFlag.fieldAut n k σ := by
      ext z
      simp [MulAut.congr_apply]
    have hJ₀ : GLAPComponent 3 (fixSubgroup (LinearFlag.fieldAut n k σ)) (J.map (h⁻¹ : MulAut _).toMonoidHom) := by
      have := Inputs141c.glaPComponent_congr (h⁻¹ : MulAut _) hJ
      rwa [hc] at this
    obtain ⟨eP⟩ := nonempty_pSimple_congr (J.equivMapOfInjective (h⁻¹ : MulAut _).toMonoidHom
      (h⁻¹ : MulAut _).injective)
    have hJ₀5 : IsAltType 5 (PSimple 3 (J.map (h⁻¹ : MulAut _).toMonoidHom)) := by
      obtain ⟨e5⟩ := hJ5
      exact ⟨eP.symm.trans e5⟩
    have hlay : J.map (h⁻¹ : MulAut _).toMonoidHom ≤ GLALayer (fixSubgroup (LinearFlag.fieldAut n k σ)) := by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · obtain rfl : n = 2 := by omega
        exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut_two σ _ hJ₀.1
          (glaPComponent_perfect hJ₀)
      · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_fieldAut hn3
          Nat.prime_three (by norm_num) σ hσ _ hJ₀.1 (glaPComponent_perfect hJ₀)
    obtain ⟨hJ₀c, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ₀ hlay
    have h60 := card_center_quot_of_isAltType hJ₀ hJ₀c hJ₀5
    obtain ⟨hperfc, f, hf, hker⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linearFieldAut_components hn σ _ hJ₀c
    haveI : CharP (CFSG.GH74.GLS.IVK.fixedField σ) 2 := Subfield.charP _ 2
    have hpow := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ] at hpow
    refine false_of_sl_cover_alt5 hn ?_ f hf hker h60
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      right
      have h4 : 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) := by
        rcases hperfc with h | h
        · omega
        · exact h
      have hne4 : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ≠ 4 := by
        intro h4'
        rw [h4'] at hpow
        exact h64 rfl (by rw [← hpow]; norm_num)
      have : Fintype (CFSG.GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
      obtain ⟨j, -, hj⟩ := FiniteField.card (CFSG.GH74.GLS.IVK.fixedField σ) 2
      rw [Nat.card_eq_fintype_card, hj] at h4 hne4 ⊢
      have hj3 : 3 ≤ (j : ℕ) := by
        by_contra h'
        have : (j : ℕ) ≤ 2 := by omega
        interval_cases (j : ℕ) <;> revert h4 hne4 <;> norm_num
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (j : ℕ) := Nat.pow_le_pow_right (by norm_num) hj3
    · exact Or.inl hn3

end Linear

section Big

open CFSG.LieType.SeitzGeneration (IsLinearIndex)


theorem noA5On_linear :
    NoA5On fun d => IsLinearIndex d.1 ∧ Inputs256c.defField d.1 ≠ 2 ∧ Inputs256c.defField d.1 ≠ 4 ∧
      ¬ Inputs256c.IsL2Sixtyfour d := by
  intro S _ _ _ _ _ d hd2 hP he β hβ J hJ hJ5
  obtain ⟨⟨r, q, hdq⟩, hf2, hf4, h64⟩ := hP
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  dsimp only at hdq
  subst hdq
  have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_A r q]; exact hd2
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP (GaloisField q.p q.exponent) 2 := hq2 ▸ inferInstance
  have hk : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2]
  have hdf : Inputs256c.defField (TauCeti.LieTypeIndex.A r q) = 2 ^ q.exponent := by
    show q.card = _
    rw [TauCeti.PrimePower.card_def, hq2]
  rw [hdf] at hf2 hf4
  have he3 : 3 ≤ q.exponent := by
    have h1 := q.exponent_pos
    by_contra h
    have : q.exponent = 1 ∨ q.exponent = 2 := by omega
    rcases this with h' | h' <;> rw [h'] at hf2 hf4 <;> revert hf2 hf4 <;> norm_num
  have hk8 : 8 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he3
  have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  obtain ⟨e⟩ := he
  let eS : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  obtain ⟨eP⟩ := nonempty_pSimple_congr (J.equivMapOfInjective eS.toMonoidHom eS.injective)
  obtain ⟨e5⟩ := hJ5
  refine false_of_linear_alt5 (n := r + 1) (by omega) hk8 ?_ (MulAut.congr eS β)
    (by rw [← map_pow, hβ, map_one]) (Inputs141c.glaPComponent_congr eS hJ) ⟨eP.symm.trans e5⟩
  intro hr1 h64'
  apply h64
  refine ⟨q, ?_, ?_⟩
  · show TauCeti.LieTypeIndex.A r q = TauCeti.LieTypeIndex.A 1 q
    rw [show r = 1 by omega]
  · rw [TauCeti.PrimePower.card_def, ← GaloisField.card q.p q.exponent q.exponent_pos.ne']
    exact h64'

theorem noA5On_suzuki :
    NoA5On fun d => ∃ m, d.1 = TauCeti.LieTypeIndex.suzuki m := by
  intro S _ _ _ _ _ d _ hd he β _ J hJ _
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨m, hdm⟩ := hd
  dsimp only at hdm
  subst hdm
  obtain ⟨e⟩ := he
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : 3 ∣ Nat.card S := (three_dvd_card_of_glaPComponent hJ).trans
    ((Subgroup.card_dvd_of_le hJ.1).trans (Subgroup.card_subgroup_dvd_card _))
  rw [Nat.card_congr (e.trans θ).toEquiv, CFSG.LieType.Ree.suzuki_order hK] at h3
  exact Inputs141c.not_three_dvd_suzuki_order' a h3

theorem noA5On_tits :
    NoA5On fun d => d.1 = TauCeti.LieTypeIndex.tits := by
  intro S _ _ hs hnc _ d _ hd he β hβ J hJ hJ5
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  dsimp only at hd
  subst hd
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  have hZ : Subgroup.center CFSG.Sporadic.Schreier.Tits.titsD = ⊥ := by
    rw [← Subgroup.map_center_eq e, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc,
      Subgroup.map_bot]
  haveI : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD := e.symm.isSimpleGroup
  have hJ' := Inputs141c.glaPComponent_congr e hJ
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  by_cases hβ1 : MulAut.congr e β = 1
  ·
    rw [hβ1] at hJ'
    have hfix : fixSubgroup (1 : MulAut CFSG.Sporadic.Schreier.Tits.titsD) = ⊤ := by
      ext z
      simp [mem_fixSubgroup]
    rw [hfix] at hJ'
    haveI : IsSimpleGroup ↥(⊤ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) ≃* _).isSimpleGroup
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJ'.2.1 inferInstance with h | h
    · exact Input183.glaPComponent_ne_bot' hJ' h
    · obtain ⟨eP⟩ := nonempty_pSimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)
      obtain ⟨e5⟩ := hJ5
      have hnc' : ∃ a b : ↥(⊤ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD), a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnc
        exact ⟨⟨e a, trivial⟩, ⟨e b, trivial⟩, fun h' => hab (e.injective (by
          simpa using congrArg Subtype.val h'))⟩
      have h3 : 3 ∣ Nat.card ↥(⊤ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) := by
        rw [Subgroup.card_top, CFSG.Sporadic.Schreier.Tits.card_titsD]
        norm_num
      obtain ⟨eT⟩ := CFSG.LocalAnalysis.GLTheoremA.rf4_pSimple_equiv_of_simple Nat.prime_three
        (⊤ : Subgroup CFSG.Sporadic.Schreier.Tits.titsD) hnc' h3
      rw [h] at eP
      have hcard := Nat.card_congr ((eT.symm.trans eP.symm).trans e5).toEquiv
      rw [Subgroup.card_top, CFSG.Sporadic.Schreier.Tits.card_titsD, Inputs256b.card_alt5] at hcard
      norm_num at hcard
  ·
    have hinner : MulAut.congr e β ∈ (MulAut.conj : CFSG.Sporadic.Schreier.Tits.titsD →* _).range := by
      obtain ⟨hO, -⟩ := CFSG.Sporadic.Schreier.Tits.AT_Tits_derived_group_Schreier
      obtain ⟨k, hk⟩ := hO (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner CFSG.Sporadic.Schreier.Tits.titsD)
        (MulAut.congr e β))
      have h1 : orderOf (QuotientGroup.mk'
          (CFSG.ComponentClassification.OuterAutomorphisms.inner CFSG.Sporadic.Schreier.Tits.titsD)
          (MulAut.congr e β)) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ', map_one])
      have h2 : orderOf (QuotientGroup.mk'
          (CFSG.ComponentClassification.OuterAutomorphisms.inner CFSG.Sporadic.Schreier.Tits.titsD)
          (MulAut.congr e β)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h3)
    obtain ⟨x, hxβ, hx3, hx1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ hinner hβ' hβ1
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    obtain ⟨a, b, hcard, -⟩ := CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_card_centralizer_of_titsD hxo
    haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Schreier.Tits.titsD))
    have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set CFSG.Sporadic.Schreier.Tits.titsD)) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3) (a := a)
        (b := b) Nat.prime_two Nat.prime_three (by norm_num) (by rw [Nat.card_eq_fintype_card] at hcard; exact hcard)
    rw [hxβ, CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj] at hJ'
    exact Inputs141c.false_of_glaPComponent_of_isSolvable hsolv hJ'

section ReeF4

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem sixty_dvd_card_of_pSimple {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJ5 : IsAltType 5 (PSimple 3 J)) : 60 ∣ Nat.card ↥J := by
  obtain ⟨e5⟩ := hJ5
  have h1 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have h2 : Nat.card (PQuot 3 J) ∣ Nat.card ↥J := Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr e5.toEquiv, Inputs256b.card_alt5] at h1
  exact h1.trans h2

theorem not_five_dvd_card_su3 (a : ℕ) :
    ¬ 5 ∣ 2 ^ (3 * (2 * a + 1)) * (((2 ^ (2 * a + 1)) ^ 2 - 1) * ((2 ^ (2 * a + 1)) ^ 3 + 1)) := by
  have h5 : Nat.Prime 5 := by norm_num
  have hq : 2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3 := by
    induction a with
    | zero => left; norm_num
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  intro h
  rcases (Nat.Prime.dvd_mul h5).1 h with h | h
  · have := (Nat.prime_dvd_prime_iff_eq h5 Nat.prime_two).1 (h5.dvd_of_dvd_pow h)
    omega
  · generalize 2 ^ (2 * a + 1) = q at hq h
    have h2 : q ^ 2 % 5 = 4 := by
      rcases hq with h' | h' <;> rw [Nat.pow_mod, h']
    have h3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
      rcases hq with h' | h' <;> rw [Nat.pow_mod, h'] <;> norm_num
    generalize q ^ 2 = s at h2 h
    generalize q ^ 3 = t at h3 h
    rcases (Nat.Prime.dvd_mul h5).1 h with h | h <;> omega

theorem card_eq_sixty_of_subnormal_simple {G : Type} [Group G] [Finite G] {X J C : Subgroup G}
    (hJ : GLAPComponent 3 X J) (hJ5 : IsAltType 5 (PSimple 3 J)) (hC : IsSimpleGroup ↥C)
    (hsn : CFSG.Open.IsSubnormal J C) : Nat.card ↥C = 60 := by
  rcases hsn.eq_bot_or_eq_of_isSimpleGroup hC with h | h
  · exact absurd h (Input183.glaPComponent_ne_bot' hJ)
  · subst h
    haveI := hC
    have hperf := Inputs141c.commutator_eq_top_of_glaPComponent hJ
    have hnc : ∃ x y : ↥J, x * y ≠ y * x := by
      by_contra hab
      push Not at hab
      have hc : commutator ↥J = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hperf] at hc
      apply Input183.glaPComponent_ne_bot' hJ
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥J) ∈ (⊥ : Subgroup ↥J) := hc ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
    have h3 : 3 ∣ Nat.card ↥J := (by norm_num : 3 ∣ 60).trans (sixty_dvd_card_of_pSimple hJ5)
    obtain ⟨eT⟩ := CFSG.LocalAnalysis.GLTheoremA.rf4_pSimple_equiv_of_simple Nat.prime_three J hnc h3
    obtain ⟨e5⟩ := hJ5
    rw [← Nat.card_congr eT.toEquiv, Nat.card_congr e5.toEquiv, Inputs256b.card_alt5]

theorem false_of_fieldAut_reeGamma_alt5
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {J : Subgroup (ReeTag.F4.reeGamma K a)}
    (hJ : GLAPComponent 3 (fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) J)
    (hJ5 : IsAltType 5 (PSimple 3 J)) : False := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK Nat.prime_three (by norm_num) σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  let eC : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃* ReeTag.F4.reeGamma (fixSubfield σ) b :=
    (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  ·
    subst hb0
    have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
    haveI : Fact (Nat.card (fixSubfield σ) = 2) := ⟨hk2⟩
    set C := fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) with hCdef
    let E : ↥C ≃* reeFixed ReeTag.F4 (fixSubfield σ) 0 :=
      eC.trans (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm
    let T : Subgroup (ReeTag.F4.reeGamma K a) :=
      ((commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)).map E.symm.toMonoidHom).map C.subtype
    have hTC : T ≤ C := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have hJT : J ≤ T := by
      intro x hx
      let φ : ↥J →* reeFixed ReeTag.F4 (fixSubfield σ) 0 := E.toMonoidHom.comp (Subgroup.inclusion hJ.1)
      have hperf := Inputs141c.commutator_eq_top_of_glaPComponent hJ
      have hle : φ.range ≤ commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := by
        rw [MonoidHom.range_eq_map, ← hperf]
        calc (commutator ↥J).map φ = ⁅(⊤ : Subgroup ↥J).map φ, (⊤ : Subgroup ↥J).map φ⁆ := by
              rw [commutator_def, Subgroup.map_commutator]
          _ ≤ ⁅(⊤ : Subgroup (reeFixed ReeTag.F4 (fixSubfield σ) 0)), ⊤⁆ :=
              Subgroup.commutator_mono le_top le_top
          _ = commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := (commutator_def _).symm
      have h1 : φ ⟨x, hx⟩ ∈ commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := hle ⟨⟨x, hx⟩, rfl⟩
      refine ⟨⟨x, hJ.1 hx⟩, ⟨φ ⟨x, hx⟩, h1, ?_⟩, rfl⟩
      exact E.symm_apply_apply _
    let eT : ↥T ≃* CFSG.Sporadic.Schreier.Tits.titsD :=
      (((((commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)).map E.symm.toMonoidHom).equivMapOfInjective
        C.subtype C.subtype_injective).symm).trans
        (((commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)).equivMapOfInjective E.symm.toMonoidHom
          E.symm.injective).symm)).trans (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := fixSubfield σ))
    haveI : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD := CFSG.Sporadic.Schreier.Tits.titsD_simple
    have hT : IsSimpleGroup ↥T := eT.isSimpleGroup
    have hsn : CFSG.Open.IsSubnormal J T := by
      have := hJ.2.1.inf_of_le hTC
      rwa [inf_eq_left.2 hJT] at this
    have h60 := card_eq_sixty_of_subnormal_simple hJ hJ5 hT hsn
    rw [Nat.card_congr eT.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD] at h60
    norm_num at h60
  ·
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
    have hC : IsSimpleGroup ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := eC.isSimpleGroup
    have h60 := card_eq_sixty_of_subnormal_simple hJ hJ5 hC hJ.2.1
    rw [Nat.card_congr eC.toEquiv] at h60
    have := CFSG.RankThree.PartTwo.Sec8.Item812Res2.card_reeGamma_ge (k := fixSubfield σ) hkcard
    omega

theorem false_of_reeGamma_alt5
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : MulAut (ReeTag.F4.reeGamma K a)}
    (hβ : β ^ 3 = 1) {J : Subgroup (ReeTag.F4.reeGamma K a)} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJ5 : IsAltType 5 (PSimple 3 J)) : False := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hβ1 : β = 1
  · subst hβ1
    have hfix : fixSubgroup (1 : MulAut (ReeTag.F4.reeGamma K a)) = ⊤ := by
      ext z
      simp [mem_fixSubgroup]
    rw [hfix] at hJ
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma K a) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 ha hK
    have hs : IsSimpleGroup ↥(⊤ : Subgroup (ReeTag.F4.reeGamma K a)) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (ReeTag.F4.reeGamma K a)) ≃* _).isSimpleGroup
    have h60 := card_eq_sixty_of_subnormal_simple hJ hJ5 hs hJ.2.1
    rw [Subgroup.card_top] at h60
    have := CFSG.RankThree.PartTwo.Sec8.Item812Res2.card_reeGamma_ge (k := K) hK
    omega
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field ha hK Nat.prime_three hβ hβ1 with
    ⟨y, rfl, hy3, hy1⟩ | ⟨σ, g, hσ, hg⟩
  ·
    obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y
      (orderOf_eq_prime hy3 hy1)
    have hF : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
    have hJC : J ≤ Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) := by
      rw [← CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
      exact hJ.1
    have hdvd : Nat.card ↥J ∣ 2 ^ (3 * (2 * a + 1)) *
        (((2 ^ (2 * a + 1)) ^ 2 - 1) * ((2 ^ (2 * a + 1)) ^ 3 + 1)) := by
      have h1 := Subgroup.card_dvd_of_le hJC
      rw [Nat.card_congr eC.toEquiv] at h1
      rwa [show (↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
          (GaloisField 2 (2 * (2 * a + 1))) 3) : Type) =
          ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) from rfl,
        CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hF] at h1
    exact not_five_dvd_card_su3 a (((by norm_num : 5 ∣ 60).trans (sixty_dvd_card_of_pSimple hJ5)).trans hdvd)
  ·
    set φ : MulAut (ReeTag.F4.reeGamma K a) := MulAut.conj g with hφ
    have hc : MulAut.congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) β = ReeTag.F4.reeGammaFieldAut K a σ := by
      have e1 : MulAut.congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) β = φ⁻¹ * β * φ⁻¹⁻¹ := by
        ext y
        rfl
      rw [e1, hg]
      group
    have hJ' := Inputs141c.glaPComponent_congr (φ⁻¹ : MulAut (ReeTag.F4.reeGamma K a)) hJ
    rw [hc] at hJ'
    obtain ⟨eP⟩ := nonempty_pSimple_congr (J.equivMapOfInjective (φ⁻¹ : MulAut _).toMonoidHom
      (φ⁻¹ : MulAut _).injective)
    obtain ⟨e5⟩ := hJ5
    exact false_of_fieldAut_reeGamma_alt5 hK σ hσ hJ' ⟨eP.symm.trans e5⟩

theorem noA5On_reeF4 :
    NoA5On fun d => ∃ m, d.1 = TauCeti.LieTypeIndex.reeF4 m := by
  intro S _ _ _ _ _ d _ hd he β hβ J hJ hJ5
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨m, hdm⟩ := hd
  dsimp only at hdm
  subst hdm
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  obtain ⟨eP⟩ := nonempty_pSimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)
  obtain ⟨e5⟩ := hJ5
  exact false_of_reeGamma_alt5 ha hK (by rw [← map_pow, hβ, map_one]) (Inputs141c.glaPComponent_congr e hJ)
    ⟨eP.symm.trans e5⟩

end ReeF4

@[expose] def Chev2BigRest : Prop :=
  NoA5On fun d => Inputs256c.defField d.1 ≠ 2 ∧ Inputs256c.defField d.1 ≠ 4 ∧ ¬ IsLinearIndex d.1 ∧
    (¬ ∃ m, d.1 = TauCeti.LieTypeIndex.suzuki m) ∧ ¬ ∃ m, d.1 = TauCeti.LieTypeIndex.reeF4 m

theorem chev2Big_of_rest
    (h : Chev2BigRest) : Inputs256c.Chev2Big := by
  refine chev2On_of_noA5On
    ((NoA5On.or (NoA5On.or (NoA5On.or noA5On_linear noA5On_suzuki) noA5On_reeF4) h).mono ?_)
  rintro d ⟨h2, h4, h64⟩
  by_cases hl : IsLinearIndex d.1
  · exact Or.inl (Or.inl (Or.inl ⟨hl, h2, h4, h64⟩))
  · by_cases hs : ∃ m, d.1 = TauCeti.LieTypeIndex.suzuki m
    · exact Or.inl (Or.inl (Or.inr hs))
    · by_cases hr : ∃ m, d.1 = TauCeti.LieTypeIndex.reeF4 m
      · exact Or.inl (Or.inr hr)
      · exact Or.inr ⟨h2, h4, hl, hs, hr⟩

@[expose] def Chev2GF2Rest : Prop :=
  NoA5On fun d => Inputs256c.defField d.1 = 2 ∧ ¬ IsLinearIndex d.1 ∧ d.1 ≠ TauCeti.LieTypeIndex.tits

theorem chev2GF2_of_rest
    (h : Chev2GF2Rest) : Inputs256c.Chev2GF2 := by
  refine chev2On_of_noA5On ((NoA5On.or noA5On_tits h).mono ?_)
  rintro d ⟨h2, hl⟩
  by_cases ht : d.1 = TauCeti.LieTypeIndex.tits
  · exact Or.inl ht
  · exact Or.inr ⟨h2, hl, ht⟩

end Big

section Subnormal

theorem center_eq_bot_of_simple_nonab {Q : Type*} [Group Q] [IsSimpleGroup Q] {a b : Q} (h : a * b ≠ b * a) :
    Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
  · exact h0
  · exact absurd (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top a) b).symm h

theorem le_of_isSubnormal_of_sixty_dvd {G : Type} [Group G] [Finite G] {J : Subgroup G} [IsSimpleGroup ↥J]
    (hJ60 : Nat.card J = 60) {Y M : Subgroup G} (hY : CFSG.Open.IsSubnormal Y M) :
    J ≤ M → ¬ 25 ∣ Nat.card M → 60 ∣ Nat.card Y → J ≤ Y := by
  induction hY with
  | refl => exact fun h _ _ => h
  | @step H M' K hHM' hn hM'K ih =>
    intro hJK h25 hH60
    have hJM' : J ≤ M' := ih hJK h25 (hH60.trans (Subgroup.card_dvd_of_le hHM'))
    have hnorm : J ≤ Subgroup.normalizer (H : Set G) :=
      hJM'.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM').1 hn)
    have hnJ : (H.subgroupOf J).Normal := by
      constructor
      intro z hz g
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hnorm g.2) (z : G)).1 hz
    haveI := hnJ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf J) with h | h
    · exfalso
      have hdisj : Disjoint H J := Subgroup.subgroupOf_eq_bot.1 h
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer H J hnorm hdisj
      have hle : H ⊔ J ≤ K := sup_le (hHM'.trans hM'K.le) hJK
      have h3600 : 25 ∣ Nat.card ↥(H ⊔ J) := by
        rw [hcard, hJ60]
        exact (show (25 : ℕ) ∣ 60 * 60 by norm_num).trans (Nat.mul_dvd_mul_right hH60 60)
      exact h25 (h3600.trans (Subgroup.card_dvd_of_le hle))
    · exact Subgroup.subgroupOf_eq_top.1 h

theorem not_alt5_of_subnormal_sup {G : Type} [Group G] [Finite G] {L J : Subgroup G}
    (eJ : ↥J ≃* alternatingGroup (Fin 5)) {y : G} (hyL : y ∈ L) (hy : orderOf y = 3)
    (hyJ : ∀ j ∈ J, y * j = j * y) (hL60 : 60 ∣ Nat.card L) (h25 : ¬ 25 ∣ Nat.card ↥(L ⊔ J))
    {Y : Subgroup G} (hY : CFSG.Open.IsSubnormal Y (L ⊔ J)) (hLY : L ≤ Y) : ¬ IsAltType 5 (barOf 3 Y) := by
  rintro ⟨eY⟩
  haveI : IsSimpleGroup ↥J := (MulEquiv.isSimpleGroup_congr eJ).mpr inferInstance
  have hJ60 : Nat.card J = 60 := (Nat.card_congr eJ.toEquiv).trans Inputs256b.card_alt5
  have hY60 : 60 ∣ Nat.card Y := hL60.trans (Subgroup.card_dvd_of_le hLY)
  have hJY : J ≤ Y := le_of_isSubnormal_of_sixty_dvd hJ60 hY le_sup_right h25 hY60
  set π : ↥Y →* barOf 3 Y := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) with hπ
  set ι : ↥J →* barOf 3 Y := π.comp (Subgroup.inclusion hJY) with hι
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥Y)) := CFSG.pPrimeCore_coprime_card
  have hker : ι.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ι.ker with h | h
    · exact h
    · exfalso
      have h3J : 3 ∣ Nat.card ↥J := by rw [hJ60]; norm_num
      obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 3 h3J
      have hjk : j ∈ ι.ker := h ▸ Subgroup.mem_top j
      have hjO : Subgroup.inclusion hJY j ∈ GLAPPrimeCore 3 ↥Y := (QuotientGroup.eq_one_iff _).1 hjk
      have hdvd : orderOf (⟨Subgroup.inclusion hJY j, hjO⟩ : ↥(GLAPPrimeCore 3 ↥Y)) ∣
          Nat.card (GLAPPrimeCore 3 ↥Y) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hJY), hj] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hdvd
  have hιinj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).1 hker
  have hιsurj : Function.Surjective ι := by
    have hcard : Nat.card ↥J = Nat.card (barOf 3 Y) := by
      rw [hJ60, Nat.card_congr eY.toEquiv, Inputs256b.card_alt5]
    exact (Function.Injective.bijective_of_nat_card_le hιinj hcard.ge).2
  have hyY : y ∈ Y := hLY hyL
  have hcent : π ⟨y, hyY⟩ ∈ Subgroup.center (barOf 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨j, rfl⟩ := hιsurj z
    rw [hι, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyJ j j.2).symm
  haveI : IsSimpleGroup (barOf 3 Y) := (MulEquiv.isSimpleGroup_congr eY).mpr inferInstance
  obtain ⟨a, b, hab⟩ := Inputs256b.alt5_noncomm
  have hZ : Subgroup.center (barOf 3 Y) = ⊥ :=
    center_eq_bot_of_simple_nonab (a := eY.symm a) (b := eY.symm b)
      (fun h => hab (by simpa using congrArg eY h))
  rw [hZ, Subgroup.mem_bot] at hcent
  have hyO : (⟨y, hyY⟩ : ↥Y) ∈ GLAPPrimeCore 3 ↥Y := (QuotientGroup.eq_one_iff _).1 hcent
  have hdvd : orderOf (⟨⟨y, hyY⟩, hyO⟩ : ↥(GLAPPrimeCore 3 ↥Y)) ∣ Nat.card (GLAPPrimeCore 3 ↥Y) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hy] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hdvd

end Subnormal

section GF2Poly

open Polynomial

variable {k : Type} [Field k] [Fintype k]

noncomputable abbrev muPoly (k : Type) [Field k] : k[X] := X ^ 2 + X + 1

theorem muPoly_natDegree : (muPoly k).natDegree = 2 := by
  unfold muPoly
  compute_degree!

theorem muPoly_monic : (muPoly k).Monic := by
  unfold muPoly
  monicity!

theorem X_sub_one_mul_muPoly : (X - C 1) * muPoly k = X ^ 3 - 1 := by
  rw [map_one]
  ring

theorem sq_eq_self_of_card_two (hk : Fintype.card k = 2) (a : k) : a ^ 2 = a := by
  have h := FiniteField.pow_card a
  rwa [hk] at h

theorem muPoly_irreducible [CharP k 2] (hk : Fintype.card k = 2) : Irreducible (muPoly k) := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [muPoly_natDegree])
    (by rw [muPoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [Polynomial.mem_roots muPoly_monic.ne_zero, IsRoot, muPoly] at ha
  simp only [eval_add, eval_pow, eval_X, eval_one] at ha
  rw [sq_eq_self_of_card_two hk, ← two_mul, CharTwo.two_eq_zero, zero_mul, zero_add] at ha
  exact one_ne_zero ha

theorem X_sub_one_irreducible : Irreducible (X - C (1 : k)) := irreducible_X_sub_C 1

theorem eq_of_irreducible_dvd [CharP k 2] (hk : Fintype.card k = 2) {j : k[X]} (hj : Irreducible j)
    (hjm : j.Monic) (hdvd : j ∣ X ^ 3 - 1) : j = X - C 1 ∨ j = muPoly k := by
  rw [← X_sub_one_mul_muPoly] at hdvd
  rcases hj.prime.dvd_or_dvd hdvd with h | h
  · left
    exact eq_of_monic_of_associated hjm (monic_X_sub_C 1)
      (hj.associated_of_dvd X_sub_one_irreducible h)
  · right
    exact eq_of_monic_of_associated hjm muPoly_monic
      (hj.associated_of_dvd (muPoly_irreducible hk) h)

theorem eq_one_of_mulVec_eq_self {E : Type*} [Field E] [CharP E 2] {M : Matrix (Fin 2) (Fin 2) E}
    (hdet : M.det = 1) (h3 : M ^ 3 = 1) {v : Fin 2 → E} (hv : v ≠ 0) (hMv : M.mulVec v = v) : M = 1 := by
  have h0 : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hMv, Matrix.one_mulVec, sub_self]⟩
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : E, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hsub : (!![a, b; c, d] - 1 : Matrix (Fin 2) (Fin 2) E) = !![a - 1, b; c, d - 1] := by
    rw [Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hsub, Matrix.det_fin_two_of] at h0
  have hsq : !![a, b; c, d] ^ 2 = 1 := by
    rw [sq, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (a - a * d + b * c) * h2 - a * h0 + (a + 1) * hdet
    · linear_combination b * h2 - b * h0 + b * hdet
    · linear_combination c * h2 - c * h0 + c * hdet
    · linear_combination (d - a * d + b * c) * h2 - d * h0 + (d + 1) * hdet
  calc !![a, b; c, d] = !![a, b; c, d] ^ 2 * !![a, b; c, d] := by rw [hsq, one_mul]
    _ = !![a, b; c, d] ^ 3 := (pow_succ _ 2).symm
    _ = 1 := h3

end GF2Poly

section GF2Model

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (glA specialFactor IsGoodFactor
  squarefree_minpoly_glA specialFactor_le_fixSubgroup conj_mem_specialFactor mem_fixSubgroup_slConjugation_iff)

open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryMultiplicity primaryComponent mem_primaryFactors
  irreducible_of_mem_primaryFactors mem_primaryComponent apply_mem_primaryComponent primarySum_primaryCoords
  primarySum_apply primaryCoords finrank_primaryComponent)

open CFSG.RankThree.PartOne.KCUnitary (gl_centralizer mem_gl_centralizer)

open CFSG.RankThree.CALinearPrimary (linearSpecialBlock linearSpecialBlockRestrict slGL slGL_injective
  coe_linearSpecialBlockRestrict linearSpecialBlockRestrict_injective)

open Polynomial

variable {k : Type} [Field k] [Fintype k] [CharP k 2]

theorem minpoly_dvd_of_pow_three {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {f : Module.End k V} (hf : f ^ 3 = 1) : minpoly k f ∣ X ^ 3 - 1 :=
  minpoly.dvd k f (by simp [hf])

theorem primaryFactor_cases (hk : Fintype.card k = 2) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {f : Module.End k V} (hf : f ^ 3 = 1) {j : k[X]} (hj : j ∈ primaryFactors f) :
    j = X - C 1 ∨ j = muPoly k := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.1 hj
  exact eq_of_irreducible_dvd hk hirr hmon (hdvd.trans (minpoly_dvd_of_pow_three hf))

theorem mem_sup_primaryComponent (hk : Fintype.card k = 2) {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {f : Module.End k V} (hf : f ^ 3 = 1) (hsq : Squarefree (minpoly k f)) (v : V) :
    v ∈ primaryComponent f (X - C 1) ⊔ primaryComponent f (muPoly k) := by
  rw [← primarySum_primaryCoords hsq v, primarySum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  have key : ∀ z : V, z ∈ primaryComponent f (b : k[X]) →
      z ∈ primaryComponent f (X - C 1) ⊔ primaryComponent f (muPoly k) := by
    intro z hz
    rcases primaryFactor_cases hk hf b.2 with h | h
    · rw [h] at hz
      exact Submodule.mem_sup_left hz
    · rw [h] at hz
      exact Submodule.mem_sup_right hz
  exact key _ (primaryCoords f hsq v b).2

theorem card_adjoinRoot (hk : Fintype.card k = 2) {b : k[X]} [Fact (Irreducible b)] :
    Nat.card (AdjoinRoot b) = 2 ^ b.natDegree := by
  haveI : Module.Finite k (AdjoinRoot b) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible b).ne_zero).finite
  rw [Module.natCard_eq_pow_finrank (K := k), (AdjoinRoot.powerBasis (Fact.out : Irreducible b).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, Nat.card_eq_fintype_card, hk]

theorem gf2_comp_shape {n : ℕ} (hk : Fintype.card k = 2) {A : GL (Fin n) k} (hA : A ^ 3 = 1)
    {L : Subgroup (LinearFlag.projectiveSL n k)} (hL : GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut n k A)) L)
    (hL5 : IsAltType 5 (PSimple 3 L)) :
    muPoly k ∈ primaryFactors (glA A : Module.End k (Fin n → k)) ∧
      primaryMultiplicity (glA A : Module.End k (Fin n → k)) (muPoly k) = 2 ∧
      L = (specialFactor A (muPoly k)).map (LinearFlag.proj n k) := by
  have h3 : ((3 : ℕ) : k) ≠ 0 := Inputs141c.three_ne_zero_of_charTwo
  have hA' : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (1 : kˣ) := by rw [hA, map_one]
  have ha3 : (glA A : Module.End k (Fin n → k)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hA, map_one, Units.val_one]
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conjAut h3 hA' L hL.1
    (glaPComponent_perfect hL)
  obtain ⟨hLc, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hL hlay
  have h60 := card_center_quot_of_isAltType hL hLc hL5
  obtain ⟨⟨⟨b, hb⟩, hgood⟩, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components h3 hA' L hLc
  have hsq := squarefree_minpoly_glA h3 hA'
  haveI : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors hb⟩
  haveI : Finite (AdjoinRoot b) := Module.finite_of_finite k
  haveI : CharP (AdjoinRoot b) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot b)).injective 2
  obtain ⟨eF⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq hb
  obtain ⟨f, hf, hker⟩ := exists_surjective_map_proj eF
  have hgood' : IsGoodFactor A b := hgood
  have hcardE := card_adjoinRoot hk (b := b)
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) b := by
    rcases hgood' with h | ⟨h, -⟩ <;> omega
  have hsmall : ¬ (3 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) b ∨
      8 ≤ Nat.card (AdjoinRoot b)) := fun hbig => false_of_sl_cover_alt5 hm2 hbig f hf hker h60
  push Not at hsmall
  have hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) b = 2 := by omega
  have h4 : 4 ≤ Nat.card (AdjoinRoot b) := by
    rcases hgood' with h | ⟨-, h⟩
    · omega
    · exact h
  have hdeg : b.natDegree = 2 := by
    rw [hcardE] at h4 hsmall
    rcases Nat.lt_or_ge b.natDegree 2 with h | h
    · have : 2 ^ b.natDegree ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rcases Nat.lt_or_ge b.natDegree 3 with h' | h'
      · omega
      · have : 2 ^ 3 ≤ 2 ^ b.natDegree := Nat.pow_le_pow_right (by norm_num) h'
        omega
  have hbmu : b = muPoly k := by
    rcases primaryFactor_cases hk ha3 hb with h | h
    · rw [h, natDegree_X_sub_C] at hdeg
      omega
    · exact h
  subst hbmu
  exact ⟨hb, hm, rfl⟩

theorem gf2_fpf {n : ℕ} {A : GL (Fin n) k} (hsq : Squarefree (minpoly k (glA A : Module.End k (Fin n → k))))
    [Fact (Irreducible (muPoly k))]
    (hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) (muPoly k) = 2)
    {Y : Matrix.SpecialLinearGroup (Fin n) k} (hY : Y ∈ specialFactor A (muPoly k)) (hY3 : Y ^ 3 = 1)
    (hY1 : Y ≠ 1) {w : Fin n → k} (hw : w ∈ primaryComponent (glA A : Module.End k (Fin n → k)) (muPoly k))
    (hfw : (slGL n k Y : Module.End k (Fin n → k)) w = w) : w = 0 := by
  set g : linearSpecialBlock (glA A) (muPoly k) := ⟨slGL n k Y, hY⟩ with hgdef
  set u := linearSpecialBlockRestrict (glA A) (muPoly k) g with hudef
  have hg3 : g ^ 3 = 1 := Subtype.ext (by
    change (slGL n k Y) ^ 3 = 1
    rw [← map_pow, hY3, map_one])
  have hu3 : u ^ 3 = 1 := by rw [hudef, ← map_pow, hg3, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply hY1
    have hg1 : g = 1 := linearSpecialBlockRestrict_injective hsq (h.trans (map_one _).symm)
    apply slGL_injective
    rw [map_one]
    exact congrArg Subtype.val hg1
  by_contra hw0
  haveI : CharP (AdjoinRoot (muPoly k)) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot (muPoly k))).injective 2
  let b₂ := Module.finBasisOfFinrankEq (AdjoinRoot (muPoly k))
    (primaryComponent (glA A : Module.End k (Fin n → k)) (muPoly k)) hm
  set f : Module.End (AdjoinRoot (muPoly k)) (primaryComponent (glA A : Module.End k (Fin n → k)) (muPoly k)) :=
    ((u : _root_.SpecialLinearGroup _ _) : _ ≃ₗ[AdjoinRoot (muPoly k)] _).toLinearMap with hfdef
  have hfu : ∀ z, f z = u.1 z := fun z => rfl
  have hf3 : f ^ 3 = 1 := by
    have h1 : ∀ z, u.1 (u.1 (u.1 z)) = z := by
      intro z
      have h2 : (u ^ 3).1 z = z := by rw [hu3]; rfl
      rw [SpecialLinearGroup.coe_pow, LinearEquiv.pow_apply] at h2
      exact h2
    refine LinearMap.ext fun z => ?_
    show f (f (f z)) = z
    exact h1 z
  have hdet : (LinearMap.toMatrix b₂ b₂ f).det = 1 := by
    rw [LinearMap.det_toMatrix, hfdef, ← LinearEquiv.coe_det]
    have := (u : _root_.SpecialLinearGroup _ _).2
    rw [this, Units.val_one]
  have hM3 : (LinearMap.toMatrix b₂ b₂ f) ^ 3 = 1 := by
    have h1 : LinearMap.toMatrix b₂ b₂ (f ^ 3) = (LinearMap.toMatrix b₂ b₂ f) ^ 3 :=
      map_pow (LinearMap.toMatrixAlgEquiv b₂) f 3
    rw [← h1, hf3, LinearMap.toMatrix_one]
  have hfix : f ⟨w, hw⟩ = ⟨w, hw⟩ := Subtype.ext (by
    rw [hfu]
    exact (coe_linearSpecialBlockRestrict g ⟨w, hw⟩).trans hfw)
  have hrep : (LinearMap.toMatrix b₂ b₂ f).mulVec (b₂.repr ⟨w, hw⟩) = b₂.repr ⟨w, hw⟩ := by
    rw [LinearMap.toMatrix_mulVec_repr, hfix]
  have hrep0 : (b₂.repr ⟨w, hw⟩ : Fin 2 → AdjoinRoot (muPoly k)) ≠ 0 := by
    intro h0
    have h1 : b₂.repr ⟨w, hw⟩ = b₂.repr 0 := by
      rw [map_zero]
      exact Finsupp.ext fun i => congrFun h0 i
    exact hw0 (congrArg Subtype.val (b₂.repr.injective h1))
  have hM1 := eq_one_of_mulVec_eq_self hdet hM3 hrep0 hrep
  have hf1 : f = 1 := (LinearMap.toMatrix b₂ b₂).injective (by rw [hM1, LinearMap.toMatrix_one])
  apply hu1
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have h1 : f z = z := by rw [hf1]; rfl
  exact h1

theorem X_sub_one_mem_primaryFactors {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {f : Module.End k V} {v : V} (hv : v ≠ 0) (hfv : f v = v) : X - C 1 ∈ primaryFactors f := by
  refine mem_primaryFactors.2 ⟨irreducible_X_sub_C 1, monic_X_sub_C 1, ?_⟩
  rw [dvd_iff_isRoot, ← Module.End.hasEigenvalue_iff_isRoot]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (by rw [hfv, one_smul]), hv⟩)

theorem mem_primaryComponent_X_sub_one {V : Type*} [AddCommGroup V] [Module k V] {f : Module.End k V} {v : V} :
    v ∈ primaryComponent f (X - C 1) ↔ f v = v := by
  rw [mem_primaryComponent]
  simp [sub_eq_zero]

theorem aeval_muPoly {V : Type*} [AddCommGroup V] [Module k V] (f : Module.End k V) (v : V) :
    aeval f (muPoly k) v = f (f v) + f v + v := by
  simp [muPoly, pow_two, Module.End.mul_apply]

theorem X_sub_one_ne_muPoly : (X - C (1 : k)) ≠ muPoly k := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_sub_C, muPoly_natDegree] at this
  omega

theorem gf2_Y_facts {n : ℕ} (hk : Fintype.card k = 2) {A : GL (Fin n) k} (hA : A ^ 3 = 1)
    (hX1 : X - C 1 ∈ primaryFactors (glA A : Module.End k (Fin n → k)))
    (hU : primaryComponent (glA A : Module.End k (Fin n → k)) (X - C 1) ≠ ⊥)
    (hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) (muPoly k) = 2)
    {Y : Matrix.SpecialLinearGroup (Fin n) k} (hY : Y ∈ specialFactor A (muPoly k)) (hY3 : Y ^ 3 = 1)
    (hY1 : Y ≠ 1) :
    (∀ v ∈ primaryComponent (glA A : Module.End k (Fin n → k)) (X - C 1),
        (slGL n k Y : Module.End k (Fin n → k)) v = v) ∧
      primaryComponent (slGL n k Y : Module.End k (Fin n → k)) (muPoly k) =
        primaryComponent (glA A : Module.End k (Fin n → k)) (muPoly k) ∧
      X - C 1 ∈ primaryFactors (slGL n k Y : Module.End k (Fin n → k)) ∧
      muPoly k ∈ primaryFactors (slGL n k Y : Module.End k (Fin n → k)) ∧
      primaryMultiplicity (slGL n k Y : Module.End k (Fin n → k)) (muPoly k) = 2 := by
  haveI : Fact (Irreducible (muPoly k)) := ⟨muPoly_irreducible hk⟩
  have h3 : ((3 : ℕ) : k) ≠ 0 := Inputs141c.three_ne_zero_of_charTwo
  have hA' : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (1 : kˣ) := by rw [hA, map_one]
  have hsq := squarefree_minpoly_glA h3 hA'
  have ha3 : (glA A : Module.End k (Fin n → k)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hA, map_one, Units.val_one]
  set a : Module.End k (Fin n → k) := (glA A : Module.End k (Fin n → k)) with hadef
  set f : Module.End k (Fin n → k) := (slGL n k Y : Module.End k (Fin n → k)) with hfdef
  have hY' := hY
  obtain ⟨hc, htriv, -⟩ := hY'
  have hcomm : Commute f a := mem_gl_centralizer.1 hc
  have hfU : ∀ v ∈ primaryComponent a (X - C 1), f v = v := fun v hv =>
    htriv _ hX1 X_sub_one_ne_muPoly v hv
  have hfW : ∀ w ∈ primaryComponent a (muPoly k), f w ∈ primaryComponent a (muPoly k) := fun w hw =>
    apply_mem_primaryComponent hcomm hw
  have hf3 : f ^ 3 = 1 := by
    rw [hfdef, ← Units.val_pow_eq_pow_val, ← map_pow, hY3, map_one, Units.val_one]
  have hf1 : f ≠ 1 := by
    intro h
    apply hY1
    apply slGL_injective
    rw [map_one]
    exact Units.ext h
  have hfpf : ∀ w ∈ primaryComponent a (muPoly k), f w = w → w = 0 := fun w hw hfw =>
    gf2_fpf hsq hm hY hY3 hY1 hw hfw
  have heq : primaryComponent f (muPoly k) = primaryComponent a (muPoly k) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (mem_sup_primaryComponent hk ha3 hsq v)
      have hv' := mem_primaryComponent.1 hv
      rw [map_add, aeval_muPoly f u, hfU u hu, hfU u hu] at hv'
      have hw0 : aeval f (muPoly k) w = 0 := by
        rw [aeval_muPoly]
        refine hfpf _ (Submodule.add_mem _ (Submodule.add_mem _ (hfW _ (hfW _ hw)) (hfW _ hw)) hw) ?_
        have h1 : f (f (f w)) = w := by
          have := congrArg (fun φ : Module.End k (Fin n → k) => φ w) hf3
          simpa [pow_succ, Module.End.mul_apply] using this
        rw [map_add, map_add, h1]
        abel
      rw [hw0, add_zero] at hv'
      have hu0 : u = 0 := by
        have h2 : (u + u + u : Fin n → k) = u := by
          have : (2 : k) • u = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
          rw [two_smul] at this
          rw [this, zero_add]
        rw [h2] at hv'
        exact hv'
      rw [hu0, zero_add]
      exact hw
    · intro hw
      rw [mem_primaryComponent, aeval_muPoly]
      refine hfpf _ (Submodule.add_mem _ (Submodule.add_mem _ (hfW _ (hfW _ hw)) (hfW _ hw)) hw) ?_
      have h1 : f (f (f v)) = v := by
        have := congrArg (fun φ : Module.End k (Fin n → k) => φ v) hf3
        simpa [pow_succ, Module.End.mul_apply] using this
      rw [map_add, map_add, h1]
      abel
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hX1f : X - C 1 ∈ primaryFactors f := X_sub_one_mem_primaryFactors hu₀0 (hfU u₀ hu₀)
  have hμf : muPoly k ∈ primaryFactors f := by
    refine mem_primaryFactors.2 ⟨muPoly_irreducible hk, muPoly_monic, ?_⟩
    by_contra hnd
    have hcop : IsCoprime (minpoly k f) (muPoly k) :=
      ((muPoly_irreducible hk).coprime_iff_not_dvd.2 hnd).symm
    have hdvd : minpoly k f ∣ (X - C 1) * muPoly k := by
      rw [X_sub_one_mul_muPoly]
      exact minpoly_dvd_of_pow_three hf3
    have h1 := hcop.dvd_of_dvd_mul_right hdvd
    rw [minpoly.dvd_iff] at h1
    apply hf1
    have h2 : aeval f (X - C (1 : k)) = f - 1 := by simp
    rw [h2, sub_eq_zero] at h1
    exact h1
  have hmf : primaryMultiplicity f (muPoly k) = 2 := by
    have h1 := finrank_primaryComponent f (muPoly k)
    have h2 := finrank_primaryComponent a (muPoly k)
    have hfin : Module.finrank k ↥(primaryComponent f (muPoly k)) =
        Module.finrank k ↥(primaryComponent a (muPoly k)) := by rw [heq]
    rw [muPoly_natDegree] at h1 h2
    have h3' : primaryMultiplicity a (muPoly k) = 2 := hm
    change Module.finrank k _ = 2 * primaryMultiplicity f (muPoly k) at h1
    change Module.finrank k _ = 2 * primaryMultiplicity a (muPoly k) at h2
    omega
  exact ⟨hfU, heq, hX1f, hμf, hmf⟩

theorem slGL_mul_apply {n : ℕ} (g h : Matrix.SpecialLinearGroup (Fin n) k) (v : Fin n → k) :
    (slGL n k (g * h) : Module.End k (Fin n → k)) v =
      (slGL n k g : Module.End k (Fin n → k)) ((slGL n k h : Module.End k (Fin n → k)) v) := by
  rw [map_mul, Units.val_mul, Module.End.mul_apply]

theorem slGL_one_apply {n : ℕ} (v : Fin n → k) :
    (slGL n k 1 : Module.End k (Fin n → k)) v = v := by
  rw [map_one, Units.val_one, Module.End.one_apply]

@[expose] def stabUW {n : ℕ} (U W : Submodule k (Fin n → k)) : Subgroup (Matrix.SpecialLinearGroup (Fin n) k) where
  carrier := {g | (∀ v ∈ U, (slGL n k g : Module.End k (Fin n → k)) v = v) ∧
    (∀ w ∈ W, (slGL n k g : Module.End k (Fin n → k)) w ∈ W) ∧
    (∀ w ∈ W, (slGL n k g⁻¹ : Module.End k (Fin n → k)) w ∈ W)}
  one_mem' := ⟨fun v _ => slGL_one_apply v, fun w hw => by rw [slGL_one_apply]; exact hw,
    fun w hw => by rw [inv_one, slGL_one_apply]; exact hw⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun v hv => ?_, fun w hw => ?_, fun w hw => ?_⟩
    · rw [slGL_mul_apply, hh1 v hv, hg1 v hv]
    · rw [slGL_mul_apply]
      exact hg2 _ (hh2 w hw)
    · rw [mul_inv_rev, slGL_mul_apply]
      exact hh3 _ (hg3 w hw)
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    refine ⟨fun v hv => ?_, hg3, fun w hw => by rw [inv_inv]; exact hg2 w hw⟩
    calc (slGL n k g⁻¹ : Module.End k (Fin n → k)) v =
        (slGL n k g⁻¹ : Module.End k (Fin n → k)) ((slGL n k g : Module.End k (Fin n → k)) v) := by
          rw [hg1 v hv]
      _ = v := by rw [← slGL_mul_apply, inv_mul_cancel, slGL_one_apply]

theorem card_stabUW_dvd {n : ℕ} {U W : Submodule k (Fin n → k)} (hUW : ∀ v, v ∈ U ⊔ W) :
    Nat.card (stabUW U W) ∣ Nat.card (LinearMap.GeneralLinearGroup k W) := by
  let r : stabUW U W → (W →ₗ[k] W) := fun g =>
    (slGL n k (g : Matrix.SpecialLinearGroup (Fin n) k) : Module.End k (Fin n → k)).restrict g.2.2.1
  have hr : ∀ (g : stabUW U W) (w : W), (r g w : Fin n → k) =
      (slGL n k (g : Matrix.SpecialLinearGroup (Fin n) k) : Module.End k (Fin n → k)) w := fun _ _ => rfl
  have hrmul : ∀ g h : stabUW U W, r (g * h) = r g * r h := by
    intro g h
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hr, Module.End.mul_apply, hr, hr]
    exact slGL_mul_apply _ _ _
  have hrone : r 1 = 1 := LinearMap.ext fun w => Subtype.ext (slGL_one_apply _)
  let ρ : stabUW U W →* LinearMap.GeneralLinearGroup k W :=
    { toFun := fun g => ⟨r g, r g⁻¹, by rw [← hrmul, mul_inv_cancel, hrone],
        by rw [← hrmul, inv_mul_cancel, hrone]⟩
      map_one' := Units.ext hrone
      map_mul' := fun g h => Units.ext (hrmul g h) }
  refine Subgroup.card_dvd_of_injective ρ fun g h hgh => ?_
  have hrgh : r g = r h := congrArg Units.val hgh
  apply Subtype.ext
  apply slGL_injective
  apply Units.ext
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hUW v)
  rw [map_add, map_add, g.2.1 u hu, h.2.1 u hu]
  congr 1
  have := congrArg (fun φ : W →ₗ[k] W => (φ ⟨w, hw⟩ : Fin n → k)) hrgh
  exact this

theorem card_generalLinearGroup_four (hk : Fintype.card k = 2) {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (hW : Module.finrank k W = 4) :
    Nat.card (LinearMap.GeneralLinearGroup k W) = 20160 := by
  let b := Module.finBasisOfFinrankEq k W hW
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field, hk]
  decide

theorem proj_injective_of_card_two {n : ℕ} (hk : Fintype.card k = 2) :
    Function.Injective (LinearFlag.proj n k) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj, eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  have hc : c = 1 := by
    haveI : Subsingleton kˣ := by
      rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_units, hk]
    exact Subsingleton.elim _ _
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hA, hc, Units.val_one, map_one]
  rfl

theorem mem_fixSubgroup_slConjugation_toGL {n : ℕ} {Y g : Matrix.SpecialLinearGroup (Fin n) k} :
    g ∈ fixSubgroup (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n k
      (Matrix.SpecialLinearGroup.toGL Y)) ↔ g * Y = Y * g := by
  rw [mem_fixSubgroup_slConjugation_iff, mem_gl_centralizer, commute_iff_eq]
  constructor
  · intro h
    apply slGL_injective
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    exact h
  · intro h
    have := congrArg (fun z => (slGL n k z : Module.End k (Fin n → k))) h
    simp only [map_mul, Units.val_mul] at this
    exact this

theorem glaPComponent_of_alt5 {G : Type} [Group G] [Finite G] {X J : Subgroup G} (hJX : J ≤ X)
    (hn : (J.subgroupOf X).Normal) (e : ↥J ≃* alternatingGroup (Fin 5)) :
    GLAPComponent 3 X J ∧ IsAltType 5 (barOf 3 J) := by
  haveI : IsSimpleGroup ↥J := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have h60 : Nat.card ↥J = 60 := (Nat.card_congr e.toEquiv).trans Inputs256b.card_alt5
  have hnc : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := Inputs256b.alt5_noncomm
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have h3 : 3 ∣ Nat.card ↥J := by rw [h60]; norm_num
  refine ⟨Claims126.glaPComponent_of_simple_normal Nat.prime_three hJX hn inferInstance hnc h3, ?_⟩
  have hO : GLAPPrimeCore 3 ↥J = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup Nat.prime_three h3
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩

theorem gf2_model {n : ℕ} (hn : 5 ≤ n) (hk : Fintype.card k = 2) {A : GL (Fin n) k} (hA : A ^ 3 = 1)
    {L : Subgroup (LinearFlag.projectiveSL n k)} (hL : GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut n k A)) L)
    (hL5 : IsAltType 5 (PSimple 3 L)) {y : LinearFlag.projectiveSL n k} (hyL : y ∈ L) (hy : orderOf y = 3) :
    ∃ J : Subgroup (LinearFlag.projectiveSL n k), GLAPComponent 3 (fixSubgroup (MulAut.conj y)) J ∧
      Nonempty (↥J ≃* alternatingGroup (Fin 5)) ∧ ¬ 25 ∣ Nat.card ↥(L ⊔ J) := by
  haveI : Fact (Irreducible (muPoly k)) := ⟨muPoly_irreducible hk⟩
  have h3 : ((3 : ℕ) : k) ≠ 0 := Inputs141c.three_ne_zero_of_charTwo
  have hA' : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (1 : kˣ) := by rw [hA, map_one]
  have hsq := squarefree_minpoly_glA h3 hA'
  have ha3 : (glA A : Module.End k (Fin n → k)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hA, map_one, Units.val_one]
  obtain ⟨hμ, hm, rfl⟩ := gf2_comp_shape hk hA hL hL5
  set a : Module.End k (Fin n → k) := (glA A : Module.End k (Fin n → k)) with hadef
  set U := primaryComponent a (X - C 1) with hUdef
  set W := primaryComponent a (muPoly k) with hWdef
  have hUW : ∀ v, v ∈ U ⊔ W := mem_sup_primaryComponent hk ha3 hsq
  have hW4 : Module.finrank k W = 4 := by
    rw [hWdef, finrank_primaryComponent, muPoly_natDegree]
    change 2 * primaryMultiplicity a (muPoly k) = 4
    rw [hm]
  have hU : U ≠ ⊥ := by
    intro hU0
    have htop : (⊤ : Submodule k (Fin n → k)) ≤ W := by
      intro v _
      have h1 := hUW v
      rwa [hU0, bot_sup_eq] at h1
    have h1 := Submodule.finrank_mono htop
    rw [finrank_top, Module.finrank_fin_fun, hW4] at h1
    omega
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hX1 : X - C 1 ∈ primaryFactors a :=
    X_sub_one_mem_primaryFactors hu₀0 (mem_primaryComponent_X_sub_one.1 hu₀)
  have hproj := proj_injective_of_card_two (n := n) hk
  obtain ⟨Y, hY, rfl⟩ := hyL
  have hYo : orderOf Y = 3 := by rw [← hy, orderOf_injective _ hproj]
  have hY3 : Y ^ 3 = 1 := by rw [← hYo]; exact pow_orderOf_eq_one Y
  have hY1 : Y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hYo
    norm_num at hYo
  obtain ⟨hfU, heq, hX1f, hμf, hmf⟩ := gf2_Y_facts hk hA hX1 hU hm hY hY3 hY1
  set A' : GL (Fin n) k := Matrix.SpecialLinearGroup.toGL Y with hA'def
  have hA'3 : A' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (1 : kˣ) := by
    rw [hA'def, ← map_pow, hY3, map_one, map_one]
  have hsq' := squarefree_minpoly_glA h3 hA'3
  have hμf' : muPoly k ∈ primaryFactors (glA A' : Module.End k (Fin n → k)) := hμf
  have hmf' : primaryMultiplicity (glA A' : Module.End k (Fin n → k)) (muPoly k) = 2 := hmf
  set Jt := specialFactor A' (muPoly k) with hJtdef
  set J := Jt.map (LinearFlag.proj n k) with hJdef
  have eJ : Nonempty (↥J ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨eF⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq' hμf'
    rw [hmf'] at eF
    haveI : Finite (AdjoinRoot (muPoly k)) := Module.finite_of_finite k
    have : Fintype (AdjoinRoot (muPoly k)) := Fintype.ofFinite _
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hcard : Fintype.card (AdjoinRoot (muPoly k)) = Fintype.card (GaloisField 2 2) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_adjoinRoot hk, muPoly_natDegree,
        GaloisField.card 2 2 (by norm_num)]
    obtain ⟨e5⟩ := CFSG.Glauberman.Dickson.nonempty_psl2_galoisField_four_mulEquiv
    let eK := FiniteField.ringEquivOfCardEq hcard
    let eSL : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot (muPoly k)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
      { toFun := Matrix.SpecialLinearGroup.map eK.toRingHom
        invFun := Matrix.SpecialLinearGroup.map eK.symm.toRingHom
        left_inv := fun A => by
          ext i j
          simp [Matrix.SpecialLinearGroup.map_apply_coe]
        right_inv := fun A => by
          ext i j
          simp [Matrix.SpecialLinearGroup.map_apply_coe]
        map_mul' := fun A B => map_mul _ A B }
    exact ⟨((Jt.equivMapOfInjective _ hproj).symm.trans eF.symm).trans
      (eSL.trans
        ((CFSG.HardMathSupport.Solomon.Coordinator.L2Plane.slEquivPsl2 (GaloisField 2 2)).trans e5))⟩
  obtain ⟨eJ⟩ := eJ
  have hJC : J ≤ fixSubgroup (MulAut.conj (LinearFlag.proj n k Y)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_fixSubgroup, MulAut.conj_apply]
    have hgY : g * Y = Y * g :=
      mem_fixSubgroup_slConjugation_toGL.1 (specialFactor_le_fixSubgroup A' (muPoly k) hg)
    rw [← map_mul, ← map_inv, ← map_mul, ← hgY, mul_inv_cancel_right]
  have hJn : (J.subgroupOf (fixSubgroup (MulAut.conj (LinearFlag.proj n k Y)))).Normal := by
    constructor
    rintro ⟨z, hz⟩ hzJ ⟨c, hc⟩
    rw [Subgroup.mem_subgroupOf] at hzJ ⊢
    obtain ⟨g, hg, rfl⟩ := hzJ
    obtain ⟨g₀, rfl⟩ := LinearFlag.proj_surjective n k c
    have hc' : (LinearFlag.proj n k) (Y * g₀ * Y⁻¹) = LinearFlag.proj n k g₀ := by
      have := mem_fixSubgroup.1 hc
      rw [MulAut.conj_apply] at this
      rw [map_mul, map_mul, map_inv]
      exact this
    have hg₀Y : g₀ * Y = Y * g₀ := by
      have h1 := hproj hc'
      calc g₀ * Y = Y * g₀ * Y⁻¹ * Y := by rw [h1]
        _ = Y * g₀ := by group
    have hmem := conj_mem_specialFactor (mem_fixSubgroup_slConjugation_toGL.2 hg₀Y) hg
    exact ⟨g₀ * g * g₀⁻¹, hmem, by simp only [map_mul, map_inv]; rfl⟩
  obtain ⟨hJcomp, -⟩ := glaPComponent_of_alt5 hJC hJn eJ
  refine ⟨J, hJcomp, ⟨eJ⟩, ?_⟩
  have hFT : ∀ g ∈ specialFactor A (muPoly k), (∀ v ∈ U, (slGL n k g : Module.End k (Fin n → k)) v = v) ∧
      ∀ w ∈ W, (slGL n k g : Module.End k (Fin n → k)) w ∈ W := by
    intro g hg
    obtain ⟨hc, htriv, -⟩ := hg
    exact ⟨fun v hv => htriv _ hX1 X_sub_one_ne_muPoly v hv,
      fun w hw => apply_mem_primaryComponent (mem_gl_centralizer.1 hc) hw⟩
  have hLT : specialFactor A (muPoly k) ≤ stabUW U W := fun g hg =>
    ⟨(hFT g hg).1, (hFT g hg).2, (hFT g⁻¹ ((specialFactor A (muPoly k)).inv_mem hg)).2⟩
  have hJt : ∀ g ∈ Jt, (∀ v ∈ U, (slGL n k g : Module.End k (Fin n → k)) v = v) ∧
      ∀ w ∈ W, (slGL n k g : Module.End k (Fin n → k)) w ∈ W := by
    intro g hg
    obtain ⟨hc, htriv, -⟩ := hg
    refine ⟨fun v hv => htriv _ hX1f X_sub_one_ne_muPoly v
      (mem_primaryComponent_X_sub_one.2 (hfU v hv)), fun w hw => ?_⟩
    have hw' : w ∈ primaryComponent (glA A' : Module.End k (Fin n → k)) (muPoly k) := by
      change w ∈ primaryComponent (slGL n k Y : Module.End k (Fin n → k)) (muPoly k)
      rw [heq]
      exact hw
    have h1 := apply_mem_primaryComponent (mem_gl_centralizer.1 hc) hw'
    change _ ∈ primaryComponent (slGL n k Y : Module.End k (Fin n → k)) (muPoly k) at h1
    rw [heq] at h1
    exact h1
  have hJT : Jt ≤ stabUW U W := fun g hg =>
    ⟨(hJt g hg).1, (hJt g hg).2, (hJt g⁻¹ (Jt.inv_mem hg)).2⟩
  have hle : (specialFactor A (muPoly k)).map (LinearFlag.proj n k) ⊔ J ≤
      (stabUW U W).map (LinearFlag.proj n k) :=
    sup_le (Subgroup.map_mono hLT) (Subgroup.map_mono hJT)
  have hdvd : Nat.card ↥((specialFactor A (muPoly k)).map (LinearFlag.proj n k) ⊔ J) ∣ 20160 := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Subgroup.card_map_of_injective hproj, ← card_generalLinearGroup_four hk hW4]
    exact card_stabUW_dvd hUW
  intro h25
  have := h25.trans hdvd
  norm_num at this

end GF2Model

section GF2Lin

open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound center_torsion_le lieModel_typeA)

open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

open CFSG.Assembly.LowTwoRank (StatedLieTag)


theorem torsBound_psl_two (n : ℕ) : torsBound 3 .PSL n 2 1 = 1 := by
  have hg : (genericOrders .PSL n 2 1).1 ∣ 4 ∧ (genericOrders .PSL n 2 1).2 ∣ 4 := by
    simp [genericOrders]
  have he : (exceptionalOrders .PSL n 2 1).1 ∣ 4 ∧ (exceptionalOrders .PSL n 2 1).2 ∣ 4 := by
    unfold exceptionalOrders
    split <;> simp_all
  simp only [torsBound, SchurFacts.tors_eq_one_of_dvd_four Nat.prime_three (by norm_num) hg.1,
    SchurFacts.tors_eq_one_of_dvd_four Nat.prime_three (by norm_num) hg.2,
    SchurFacts.tors_eq_one_of_dvd_four Nat.prime_three (by norm_num) he.1,
    SchurFacts.tors_eq_one_of_dvd_four Nat.prime_three (by norm_num) he.2]

theorem center_eq_bot_of_psl_two (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 3 K = ⊥) {X : Type} [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) {n : ℕ} (hm : CFSG.Models.LieModel X .PSL n 2 1) :
    Subgroup.center K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := center_torsion_le hGA hq e hm Nat.prime_three
  rw [torsBound_psl_two n] at hle
  by_contra hne
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3
    (SchurFacts.prime_dvd_card_of_isPGroup Nat.prime_three
      (SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot Nat.prime_three hO) hne)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    norm_num at hz
  have hzp : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have h2 : 1 < Nat.card {w : Subgroup.center K // w ^ 3 = 1} := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨1, one_pow 3⟩, ⟨z, hzp⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
  omega

theorem isAltType_barOf_of_equiv {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (e : ↥J ≃* alternatingGroup (Fin 5)) : IsAltType 5 (barOf 3 J) := by
  haveI : IsSimpleGroup ↥J := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  have h3 : 3 ∣ Nat.card ↥J := by
    rw [(Nat.card_congr e.toEquiv).trans Inputs256b.card_alt5]
    norm_num
  have hO : GLAPPrimeCore 3 ↥J = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup Nat.prime_three h3
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans e⟩

theorem chev2GF2Lin_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : Inputs256c.Chev2GF2Lin := by
  intro K _ _ hK hcore _ _ d hd2 hP hθ x hx L hL hL5 y hyL hy
  obtain ⟨hf2, ⟨r, q, hdq⟩⟩ := hP
  obtain ⟨θ⟩ := hθ
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  dsimp only at hdq
  subst hdq
  have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_A r q]; exact hd2
  have hcard : q.p ^ q.exponent = 2 := by
    have : Inputs256c.defField (TauCeti.LieTypeIndex.A r q) = q.card := rfl
    rw [this, TauCeti.PrimePower.card_def] at hf2
    exact hf2
  have hqe : q.exponent = 1 := by
    rw [hq2] at hcard
    have h1 : 2 ^ q.exponent = 2 ^ 1 := by rw [hcard, pow_one]
    exact Nat.pow_right_injective le_rfl h1
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hkN : Nat.card (GaloisField q.p q.exponent) = 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hcard]
  haveI : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  have hk : Fintype.card (GaloisField q.p q.exponent) = 2 := by
    rw [← Nat.card_eq_fintype_card, hkN]
  haveI : CharP (GaloisField q.p q.exponent) 2 := hq2 ▸ inferInstance
  have hqc : q.card = 2 := by rw [TauCeti.PrimePower.card_def]; exact hcard
  have hr : 4 ≤ r := by
    have hv' := (TauCeti.LieTypeIndex.valid_iff _).mp hv
    have h1 := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp hv'.1
    have h2 : ¬ (TauCeti.LieTypeIndex.A r q).IsDuplicateRepresentative := hv'.2
    have h3 : ¬ (r = 2 ∧ q.card = 2) := fun h =>
      h2 ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inl h)))
    have h4 : ¬ (r = 3 ∧ q.card = 2) := fun h =>
      h2 ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inr h)))
    have h5 : r ≠ 1 := fun h => by
      have := h1.2 h
      omega
    have h6 : 1 ≤ r := h1.1
    rw [hqc] at h3 h4
    omega
  have hm := lieModel_typeA r q hv
  rw [hq2, hqe] at hm
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_psl_two hGA hK.1 hcore θ hm
  let e : K ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    (((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))).trans θ).trans
      ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hβ3 : (MulAut.congr e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨A, hA, hβA⟩ : ∃ A : GL (Fin (r + 1)) (GaloisField q.p q.exponent), A ^ 3 = 1 ∧
      MulAut.congr e x = LinearFlag.conjAut (r + 1) (GaloisField q.p q.exponent) A := by
    rcases Inputs141c.projectiveSL_cases_of_three_le (n := r + 1) (by omega)
      (by rw [ringChar.eq (GaloisField q.p q.exponent) 2]; norm_num) _ hβ3 with
      ⟨A, c, hA, hβA⟩ | ⟨h, σ, hσ, -⟩
    · refine ⟨A, ?_, hβA⟩
      have hc : c = 1 := by
        haveI : Subsingleton (GaloisField q.p q.exponent)ˣ := by
          rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units, hkN]
        exact Subsingleton.elim _ _
      rw [hA, hc, map_one]
    · exfalso
      have h1 := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
      rw [hσ, hkN] at h1
      have h2 := CFSG.GH74.GLS.IVK.one_lt_card_fixedField σ
      have h3 : 2 ^ 3 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ^ 3 := Nat.pow_le_pow_left h2 3
      omega
  have hL' : GLAPComponent 3 (fixSubgroup x) L := by rwa [Inputs256b.fixedSub_eq] at hL
  have hLm : GLAPComponent 3 (fixSubgroup (LinearFlag.conjAut (r + 1) (GaloisField q.p q.exponent) A))
      (L.map e.toMonoidHom) := by
    rw [← hβA]
    exact Inputs141c.glaPComponent_congr e hL'
  have hLm5 : IsAltType 5 (PSimple 3 (L.map e.toMonoidHom)) := by
    obtain ⟨eP⟩ := nonempty_pSimple_congr (L.equivMapOfInjective e.toMonoidHom e.injective)
    obtain ⟨e5⟩ := Inputs256b.isAltType_pSimple hL5
    exact ⟨eP.symm.trans e5⟩
  have hyo : orderOf (e y) = 3 := by rw [MulEquiv.orderOf_eq, hy]
  obtain ⟨J', hJ'c, ⟨eJ'⟩, h25'⟩ :=
    gf2_model (n := r + 1) (by omega) hk hA hLm hLm5 (Subgroup.mem_map_of_mem _ hyL) hyo
  set J : Subgroup K := J'.map e.symm.toMonoidHom with hJdef
  have hcy : MulAut.congr e.symm (MulAut.conj (e y)) = MulAut.conj y := by
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hJc : GLAPComponent 3 (fixSubgroup (MulAut.conj y)) J := by
    rw [← hcy]
    exact Inputs141c.glaPComponent_congr e.symm hJ'c
  have eJ : ↥J ≃* alternatingGroup (Fin 5) :=
    (J'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eJ'
  have h25 : ¬ 25 ∣ Nat.card ↥(L ⊔ J) := by
    have hmap : (L ⊔ J).map e.toMonoidHom = L.map e.toMonoidHom ⊔ J' := by
      rw [Subgroup.map_sup, hJdef, Subgroup.map_map]
      congr 1
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
        ext z
        simp
      rw [this, Subgroup.map_id]
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
    exact h25'
  have hyJ : ∀ j ∈ J, y * j = j * y := by
    intro j hj
    have h1 : MulAut.conj y j = j := mem_fixSubgroup.1 (hJc.1 hj)
    rw [MulAut.conj_apply] at h1
    calc y * j = y * j * y⁻¹ * y := by group
      _ = j * y := by rw [h1]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hy1 : MulAut.conj y ≠ 1 := by
    intro h
    have hyZ : y ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut K => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * y = y * g * y⁻¹ * y := by rw [h1]
        _ = y * g := by group
    rw [hZ, Subgroup.mem_bot] at hyZ
    rw [hyZ, orderOf_one] at hy
    norm_num at hy
  have hxA : x ∈ Prop1310a5b.Agrp x y := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyA : MulAut.conj y ∈ Prop1310a5b.Agrp x y :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let S : MulAut K → Set (Subgroup K) := fun a => {J'' | (a = x ∧ J'' = L) ∨ (a = MulAut.conj y ∧ J'' = J)}
  have hLS : L ∈ S x := Or.inl ⟨rfl, rfl⟩
  have hJS : J ∈ S (MulAut.conj y) := Or.inr ⟨rfl, rfl⟩
  have hKstar : Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S = L ⊔ J := by
    refine le_antisymm ?_ (sup_le (Inputs256c.le_kstar hxA hx1 hLS) (Inputs256c.le_kstar hyA hy1 hJS))
    refine iSup₂_le fun a _ => iSup₂_le fun M hM => ?_
    rcases hM with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · rintro a - - M (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hL
    · rw [Inputs256b.fixedSub_eq]
      exact hJc
  · intro Y hY hLY
    rw [hKstar] at hY
    exact not_alt5_of_subnormal_sup eJ hyL hy hyJ (sixty_dvd_card_of_isAltType hL5) h25 hY hLY
  · rintro a - - M (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl hL5
    · exact Or.inl (isAltType_barOf_of_equiv eJ)
  · exact le_iSup₂_of_le (f := fun (M : Subgroup K) (_ : M ∈ S x) => M) L hLS le_rfl

end GF2Lin

theorem input25_6A5Chev2_of_residuals
    (hGA : CFSG.Open.GriessAllModelsStatement) (hBig : Chev2BigRest) (h4 : Inputs256c.Chev2GF4)
    (h2 : Chev2GF2Rest) : Inputs256b.Input25_6A5Chev2 :=
  Inputs256c.input25_6A5Chev2_of_families chev2Field64_holds (chev2Big_of_rest hBig) h4
    (chev2GF2Lin_of_griess hGA) (chev2GF2_of_rest h2)

theorem input25_6A5Rest2_of_residuals
    (hGen5 : Inputs256b.InputGen2311Five) (hGA : CFSG.Open.GriessAllModelsStatement) (hBig : Chev2BigRest)
    (h4 : Inputs256c.Chev2GF4) (h2 : Chev2GF2Rest) : Inputs256c.Input25_6A5Rest2 :=
  ⟨hGen5, input25_6A5Chev2_of_residuals hGA hBig h4 h2⟩

@[expose] def Input25_6A5Rest3 : Prop :=
  Inputs256b.InputGen2311Five ∧ Chev2BigRest ∧ Inputs256c.Chev2GF4 ∧ Chev2GF2Rest

theorem input25_6A5Rest2_of_rest3
    (hGA : CFSG.Open.GriessAllModelsStatement) (h : Input25_6A5Rest3) : Inputs256c.Input25_6A5Rest2 :=
  input25_6A5Rest2_of_residuals h.1 hGA h.2.1 h.2.2.1 h.2.2.2

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256d

end

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryInner
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

variable {p f t s ε : ℕ} {K : Type} [Field K]

theorem odd_relIndex_hypSU_hypUnitary (h : UnitaryFieldData 2 f K) (r ε : ℕ) :
    Odd ((hypSU h r ε).relIndex (hypUnitary h r ε)) := by
  have hodd : Odd (2 ^ f + 1) :=
    ((Nat.even_pow' (by have := h.one_le; omega)).2 even_two).add_one
  rcases Nat.eq_zero_or_pos (2 * r + ε) with hdim | hdim
  · obtain ⟨rfl, rfl⟩ : r = 0 ∧ ε = 0 := by omega
    haveI : Subsingleton (GL (HypIndex 0 0) K) := inferInstance
    rw [Subgroup.eq_bot_of_subsingleton (hypSU h 0 0),
      Subgroup.eq_bot_of_subsingleton (hypUnitary h 0 0), Subgroup.relIndex_bot_left,
      Subgroup.card_bot]
    exact odd_one
  · have hcard := CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.card_hypUnitary h hdim
    have hmul := Subgroup.relIndex_mul_card (hypSU h r ε) (hypUnitary h r ε)
    rw [inf_eq_left.mpr (hypSU_le_hypUnitary h), hcard] at hmul
    have hpos : 0 < Nat.card ↥(hypSU h r ε) := Nat.card_pos
    have h1 : (hypSU h r ε).relIndex (hypUnitary h r ε) = 2 ^ f + 1 :=
      Nat.eq_of_mul_eq_mul_right hpos hmul
    rw [h1]
    exact hodd

theorem uniLeviHom_none_mem_hypUnitary (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {I : Finset ℕ}
    {t s : ℕ} (hI : LeviBlock.IsTopCut I t)
    (y : ↥(flagStabilizer h (t + s) ε ↑I)) :
    LeviBlock.uniLeviHom h hε hI y none ∈ hypUnitary h s ε :=
  mem_hypUnitary.mpr (LeviBlock.resBlock_gram h hε (Finset.mem_coe.mpr hI.mem) y)

theorem uniBlockSub_some_eq_bot_or_isWBlock (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {t s : ℕ} {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t) (b : ↥I) :
    LeviBlock.uniBlockSub (s := s) (ε := ε) h I (some b) = ⊥ ∨
      IsWBlock ↥(LeviBlock.uniBlockSub (s := s) (ε := ε) h I (some b)) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have h4 := LeviBlock.four_le_card_of_unitaryFieldData_two h
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.range_toGL_cases (K := K)
    (b.1 - LeviBlock.predCut I b.1) with hbot | hsmall | hq
  · exact Or.inl hbot
  · exact absurd hsmall.1 (by omega)
  · exact Or.inr (Or.inl hq)

theorem hypSU_one_zero_two_isSymThree (h : UnitaryFieldData 2 1 K) :
    IsSymThreeOrSUThreeTwo ↥(hypSU h 1 0) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := LeviBlock.exists_hypSU_one_zero_mulEquiv h
  letI : Field F := hFfield
  haveI : Finite F := hFfin
  letI : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 2 := by simpa using hFcard
  have : CharP F 2 := by
    apply charP_of_card_eq_prime_pow (f := 1)
    rw [← Nat.card_eq_fintype_card]
    simpa using hF
  obtain ⟨e2⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm hF
  exact Or.inl ⟨e.trans e2⟩

theorem hypSU_one_one_two_isSUThreeTwo (h : UnitaryFieldData 2 1 K) :
    IsSymThreeOrSUThreeTwo ↥(hypSU h 1 1) := by
  have : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  refine Or.inr ⟨K, inferInstance, inferInstance, ?_, ⟨hypTransport h hR⟩⟩
  rw [h.card]
  norm_num

theorem center_hypSU_one_zero_eq_bot (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    Subgroup.center (hypSU h 1 0) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := LeviBlock.exists_hypSU_one_zero_mulEquiv h
  letI : Field F := hFfield
  haveI : Finite F := hFfin
  letI : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := by
    apply charP_of_card_eq_prime_pow (f := f)
    rw [← Nat.card_eq_fintype_card]
    exact hFcard
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  haveI : Subsingleton ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot F]
    infer_instance
  have h1 : (Subgroup.centerCongr e) (⟨x, hx⟩ : ↥(Subgroup.center (hypSU h 1 0))) =
      (Subgroup.centerCongr e) 1 := by
    rw [map_one]
    exact Subsingleton.elim _ _
  have h2 : (⟨x, hx⟩ : ↥(Subgroup.center (hypSU h 1 0))) = 1 :=
    (Subgroup.centerCongr e).injective h1
  simpa using congrArg Subtype.val h2

theorem center_hypSU_eq_hypScalars_of_three_le (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {s : ℕ} (hm : 3 ≤ 2 * s + ε) (hmq : (2 * s + ε, 2 ^ f) ≠ (3, 2)) :
    Subgroup.center (hypSU h s ε) = hypScalars h s ε := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := s) (ε := ε) h
  refine le_antisymm ?_ (normOneScalars_le_center h _ _)
  intro z hz
  refine (mem_hypScalars_iff_transport hR z).mpr ?_
  have hst := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f)
    hF hm hmq).2
  have hz' : hypTransport h hR z ∈ Subgroup.center (unitarySU 2 f K (2 * s + ε)) := by
    rw [← Subgroup.map_center_eq (hypTransport h hR)]
    exact Subgroup.mem_map_of_mem _ hz
  rw [show Subgroup.center (unitarySU 2 f K (2 * s + ε)) =
      (CFSG.Open.StatedScalars (Fin (2 * s + ε)) K).subgroupOf
        (unitarySU 2 f K (2 * s + ε)) from hst] at hz'
  rwa [CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by omega : 1 ≤ 2 * s + ε)]

theorem hypSU_eq_bot_or_isWBlock (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (s : ℕ) :
    hypSU h s ε = ⊥ ∨ IsWBlock ↥(hypSU h s ε) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hodd : Odd (2 ^ f + 1) :=
    ((Nat.even_pow' (by have := h.one_le; omega)).2 even_two).add_one
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · haveI := LeviBlock.subsingleton_hypSU_zero h hε
    exact Or.inl (Subgroup.eq_bot_of_subsingleton _)
  by_cases hm3 : 3 ≤ 2 * s + ε
  · by_cases hmq : (2 * s + ε, 2 ^ f) = (3, 2)
    · rw [Prod.mk.injEq] at hmq
      obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 1 := by omega
      obtain rfl : f = 1 :=
        Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using hmq.2)
      exact Or.inr (Or.inr (hypSU_one_one_two_isSUThreeTwo h))
    · obtain ⟨hq, -⟩ := LeviBlock.hypSU_facts_of_three_le h hm3 hmq
      refine Or.inr (Or.inl ⟨hq, ?_⟩)
      rw [center_hypSU_eq_hypScalars_of_three_le h hε hm3 hmq,
        CFSG.ClassicalGroups.UnitaryFlag.card_hypScalars h (by omega)]
      exact Odd.of_dvd_nat hodd (Nat.gcd_dvd_right _ _)
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    rcases Nat.lt_or_ge f 2 with hf | hf
    · obtain rfl : f = 1 := by have := h.one_le; omega
      exact Or.inr (Or.inr (hypSU_one_zero_two_isSymThree h))
    · obtain ⟨hq, -⟩ := LeviBlock.hypSU_facts_two h hf
      refine Or.inr (Or.inl ⟨hq, ?_⟩)
      rw [center_hypSU_one_zero_eq_bot h hf, Subgroup.card_bot]
      exact odd_one

theorem uniLeviHom_some_eq_scalar (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {t s : ℕ} {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t)
    (y : ↥(flagStabilizer h (t + s) ε ↑I)) (b : ↥I) {c : Kˣ}
    (hc : ((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) =
      Matrix.GeneralLinearGroup.scalar (HypIndex (t + s) ε) c) :
    LeviBlock.uniLeviHom h hε hI y (some b) =
      Matrix.GeneralLinearGroup.scalar (Fin (b.1 - LeviBlock.predCut I b.1)) c := by
  have hcm : (((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) =
      Matrix.scalar (HypIndex (t + s) ε) (c : K) := by
    simpa only [Matrix.GeneralLinearGroup.coe_scalar] using congrArg
      (fun g : GL (HypIndex (t + s) ε) K =>
        (g : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) hc
  rw [LeviBlock.uniLeviHom_some]
  apply Units.ext
  rw [LeviBlock.coe_eBlockHom, hcm, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.submatrix_diagonal _ _ (LeviBlock.eIdx_injective _)]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply]

theorem eq_one_of_mem_hypScalars_of_some_eq_one (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {t s : ℕ} {I : Finset ℕ} (hI : LeviBlock.IsTopCut I t)
    (y : ↥(flagStabilizer h (t + s) ε ↑I))
    (hy : (y : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε)
    (hone : ∀ b : ↥I, LeviBlock.uniLeviHom h hε hI y (some b) = 1) : y = 1 := by
  obtain ⟨c, -, -, hc⟩ := hy
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hm : 0 < t - LeviBlock.predCut I t :=
    Nat.sub_pos_of_lt (LeviBlock.predCut_lt (I := I) ht1)
  have hsc := uniLeviHom_some_eq_scalar h hε hI y ⟨t, hI.mem⟩ hc
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin (t - LeviBlock.predCut I t)) c :
      GL (Fin (t - LeviBlock.predCut I t)) K) = 1 :=
    hsc.symm.trans (hone ⟨t, hI.mem⟩)
  have hc1 : (c : K) = 1 := by
    have := congrArg (fun g : GL (Fin (t - LeviBlock.predCut I t)) K =>
      (g : Matrix (Fin (t - LeviBlock.predCut I t)) (Fin (t - LeviBlock.predCut I t)) K)
        ⟨0, hm⟩ ⟨0, hm⟩) h1
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  have hmat : (((y : hypSU h (t + s) ε) : GL (HypIndex (t + s) ε) K) :
      Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K) = 1 := by
    have hcm := congrArg (fun g : GL (HypIndex (t + s) ε) K =>
      (g : Matrix (HypIndex (t + s) ε) (HypIndex (t + s) ε) K)) hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc1] at hcm
    rw [hcm]
    simp [Matrix.scalar_apply]
  exact Subtype.ext (Subtype.ext (Units.ext hmat))



theorem hasLeviCensus_idxTwistedA {X : Type} [Group X] [Finite X] {L J : Subgroup X}
    (hCP : CompParab L J) (h : IsLieOf IdxTwistedA (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  unfold IsLieOf at h
  obtain ⟨d, hd, ⟨eL⟩⟩ := h
  obtain ⟨K, _, f, t, s, ε, hU, ρ, I, g, hε, hI, -, hρ, hZfib, hJ⟩ :=
    CFSG.AGLEmbedding.exists_uniFlag_dim_of_compParab hCP d hd eL
  have : Finite K := hU.finite
  haveI : CharP K 2 := hU.charP
  let C := hypSU hU (t + s) ε
  let J' : Subgroup C := (J.subgroupOf L).comap ρ
  let e := LeviBlock.stabMulEquiv g hJ
  let S : ∀ j : Option ↥I, Subgroup (LeviBlock.uniBlockGroup K s ε I j) :=
    LeviBlock.uniBlockSub (s := s) (ε := ε) hU I
  let β : ↥J' →* ∀ j : Option ↥I, LeviBlock.uniBlockGroup K s ε I j :=
    (LeviBlock.uniLeviHom hU hε hI).comp e.toMonoidHom
  have hrange : β.range = (LeviBlock.uniLeviHom hU hε hI).range := by
    rw [show β = (LeviBlock.uniLeviHom hU hε hI).comp e.toMonoidHom from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_map (e.toMonoidHom),
      Subgroup.map_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map]
  have hdim : 1 ≤ 2 * (t + s) + ε := by
    have := (hI.le t hI.mem).1
    omega
  have hker : ρ.ker ≤ hypScalars hU (t + s) ε := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    exact (hZfib y).mp (hy ▸ Subgroup.one_mem _)
  have hc : ρ.ker ≤ Subgroup.center C :=
    hker.trans (normOneScalars_le_center hU _ _)
  have ho : Odd (Nat.card ↥ρ.ker) := by
    have hdvd : Nat.card ↥ρ.ker ∣ Nat.card ↥(hypScalars hU (t + s) ε) :=
      Subgroup.card_dvd_of_le hker
    rw [CFSG.ClassicalGroups.UnitaryFlag.card_hypScalars hU hdim] at hdvd
    have hodd : Odd (2 ^ f + 1) :=
      ((Nat.even_pow' (by have := hU.one_le; omega)).2 even_two).add_one
    exact Odd.of_dvd_nat hodd (hdvd.trans (Nat.gcd_dvd_right _ _))
  have hβgrp : IsPGroup 2 β.ker := by
    have := (LeviBlock.isPGroup_ker_uniLeviHom hU hε hI).comap_of_injective
      e.toMonoidHom e.injective
    exact this
  have hle : Subgroup.pi Set.univ S ≤ β.range := by
    rw [hrange]
    exact LeviBlock.pi_uniBlockSub_le_range hU hε hI
  have hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S := by
    rw [hrange]
    exact LeviBlock.commutator_range_le_pi hU hε hI
  have hn : β.range ≤ Subgroup.normalizer (Subgroup.pi Set.univ S :
      Set (∀ j, LeviBlock.uniBlockGroup K s ε I j)) :=
    le_normalizer_of_commutator_le hle hcomm
  have hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range := by
    let T : ∀ j : Option ↥I, Subgroup (LeviBlock.uniBlockGroup K s ε I j) := fun j =>
      match j with
      | none => hypUnitary hU s ε
      | some _ => ⊤
    refine not_two_dvd_relIndex_pi_of_finite (S := S) (T := T) ?_ hle ?_ ?_
    · intro j
      cases j with
      | none => exact hypSU_le_hypUnitary hU
      | some b => exact le_top
    · rw [hrange]
      rintro _ ⟨z, rfl⟩
      rw [Subgroup.mem_pi]
      intro j _
      cases j with
      | none => exact uniLeviHom_none_mem_hypUnitary hU hε hI z
      | some b => exact Subgroup.mem_top _
    · intro j
      cases j with
      | none => exact (odd_relIndex_hypSU_hypUnitary hU s ε).not_two_dvd_nat
      | some b =>
        change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (b.1 - LeviBlock.predCut I b.1)) K →*
            GL (Fin (b.1 - LeviBlock.predCut I b.1)) K).range).relIndex ⊤
        rw [Subgroup.relIndex_top_right]
        exact CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.not_two_dvd_index_range_toGL _
  have hSw : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := by
    intro j
    cases j with
    | none => exact hypSU_eq_bot_or_isWBlock hU hε s
    | some b => exact uniBlockSub_some_eq_bot_or_isWBlock hU hε hI b
  have hZw : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z : ↥J', ρ ↑z = 1 →
      β z ∈ (S j).map (MonoidHom.mulSingle (LeviBlock.uniBlockGroup K s ε I) j) →
        β z = 1 := by
    intro j hq z hz hmem
    cases j with
    | some b =>
      have hbot : S (some b) = ⊥ := by
        have h4 := LeviBlock.four_le_card_of_unitaryFieldData_two hU
        rcases CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.range_toGL_cases
          (K := K) (b.1 - LeviBlock.predCut I b.1) with h1 | h2 | h3
        · exact h1
        · exact absurd h2.1 (by omega)
        · exact absurd h3.1 hq
      rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at hmem
      exact hmem
    | none =>
      have hzscal : (↑z : C) ∈ hypScalars hU (t + s) ε := by
        exact (hZfib ↑z).mp (by rw [hz]; exact Subgroup.one_mem _)
      have hzcenter : ∀ x : C, x * (↑z : C) = (↑z : C) * x :=
        Subgroup.mem_center_iff.mp (normOneScalars_le_center hU _ _ hzscal)
      have heval : (↑(e z) : C) = ↑z := by
        calc g⁻¹ * (↑z : C) * g = g⁻¹ * ((↑z : C) * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * ↑z) := by rw [← hzcenter g]
          _ = ↑z := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      have hescal : (↑(e z) : C) ∈ hypScalars hU (t + s) ε := heval ▸ hzscal
      have hone : ∀ b : ↥I, LeviBlock.uniLeviHom hU hε hI (e z) (some b) = 1 := by
        intro b
        obtain ⟨x, -, hxeq⟩ := Subgroup.mem_map.mp hmem
        have hcoord : β z (some b) = 1 := by
          have h1 := congrFun hxeq (some b)
          have h2 : (MonoidHom.mulSingle (LeviBlock.uniBlockGroup K s ε I) none x)
              (some b) = 1 := Pi.mulSingle_eq_of_ne (Option.some_ne_none b) x
          rw [h2] at h1
          exact h1.symm
        simpa [β, MonoidHom.comp_apply] using hcoord
      have hez1 : e z = 1 :=
        eq_one_of_mem_hypScalars_of_some_eq_one hU hε hI (e z) hescal hone
      rw [show z = 1 from e.injective (by rw [hez1, map_one]), map_one]
  exact hasLeviCensus_of_cover_of_finite hCP.parab.1 ρ hρ hc ho β hβgrp hle hn hi hSw hZw


end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

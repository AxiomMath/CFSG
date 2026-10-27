
module

public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase

public import Certificates.Data.Kernel.GammaUSigmaK
public import CFSG.Certificates.Kernel.IdxFourCosetSound
public import CFSG.Certificates.Kernel.IdxFourSiftSound
public import CFSG.GF2Type.Smith1979.GammaU.SigmaFacts
public import CFSG.GF2Type.Smith1979.GammaU.SigmaBase

public section

namespace CFSG.KC.GUS

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.GammaU.ResPair CFSG.GF2Type.Smith1979.GammaU.SigmaP Module
open scoped commutatorElement

section Facts

variable {i : ℕ} {NG PG PI TG : List Nat} {NI C CG : Nat}
  {SP SI : Nat} {T O PS B OL : List Nat} {TL WD OT RW DW QP : List (List Nat)}
  {TR R : List (List (List Nat))} {k n : Nat}

local notation "GL" => V12 ≃ₗ[ZMod 2] V12

theorem sigmaFacts_of (hC : ChainHyp SP SI T O PS B TL WD TR R k 2 n) (hO : O.prod = 17280)
    (hNG : NG = (n2Gens i).map CFSG.KC.IF4R.packR) (hPG : PG = pgP NG NI (commPairs i))
    (hPI : PI = pgI NG NI (commPairs i))
    (hTG : TG = targets NG NI (commPairs i) (CFSG.KC.IF4R.packR thetaRows) C)
    (hrows : ((n2Gens i).all fun r => rowsOK r.toList) = true)
    (hpairs : (pairsOK (commPairs i) (lenN NG) && pairsOK (perfPairs i) (lenN PG)) = true)
    (hinv : invsOK NG NI = true)
    (hsift : CFSG.KC.IF4R.recsOK T O 1 (fun _ => idP) TG QP = true)
    (hrw : wordsG PG RW [look SP 0, look SP 1] = true)
    (hdw : wordsG (dgP PG PI (perfPairs i)) DW PG = true)
    (hstab : (memN a0 (s45 i) && stabOK (NG ++ unpack NI (lenN NG)) (s45 i)) = true)
    (hreach : reachOK NG a0 OL OT (s45 i) = true)
    (hsigma : sigmaOK (s45 i) (sigmaBasis i) (spanList (sigmaBasis i)) = true)
    (hoval : ovalOK (outPts i) = true)
    (hCG : CG < (commPairs i).length) (hnc : ncOK C (sigmaBasis i) (nthD 0 PG CG) = true) :
    SigmaFacts i ∧ lvlGrp SP TL 0 = genGrp (pGens i) := by
  have hlenNG : NG.length = (n2Gens i).length := by rw [hNG, List.length_map]
  have hrow : ∀ l < (n2Gens i).length, rowsOK (n2Gens i)[l]!.toList = true := fun l hl => by
    rw [getElem!_pos _ l hl]
    simp only [List.all_eq_true] at hrows
    exact hrows _ (List.getElem_mem hl)
  have hNGl : ∀ l < (n2Gens i).length, nthD 0 NG l = CFSG.KC.IF4R.packR (n2Gens i)[l]! := by
    intro l hl
    rw [hNG, nthD_map _ _ _ #[] hl, getD_of_lt _ hl, getElem!_pos _ l hl]
  have hgen : ∀ l < (n2Gens i).length, ∃ U ∈ genGrp (n2Gens i), IsP U (nthD 0 NG l) ∧
      IsP U⁻¹ (look NI l) ∧ ∀ v, U v = linOfRows (n2Gens i)[l]! v := by
    intro l hl
    obtain ⟨h1, -⟩ := invsOK_spec hinv l (hlenNG ▸ hl)
    obtain ⟨U, hU⟩ := IsP.exists_of_mul h1
    have hUr : ∀ v, U v = linOfRows (n2Gens i)[l]! v :=
      (isP_packR (hrow l hl) U).1 (hNGl l hl ▸ hU)
    refine ⟨U, Subgroup.subset_closure ⟨_, ?_, hUr⟩, hU, hU.inv h1, hUr⟩
    rw [getElem!_pos _ l hl]
    exact List.getElem_mem hl
  choose! Ug hUgN hUgP hUgI hUgR using hgen
  have hgenSet : ∀ U ∈ GenSet (n2Gens i), ∃ l < (n2Gens i).length, U = Ug l := by
    rintro U ⟨r, hr, hUr⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hr
    refine ⟨l, hl, LinearEquiv.ext fun v => ?_⟩
    rw [hUr, hUgR l hl, getElem!_pos _ l hl]
  have hcomm : ∀ a < (n2Gens i).length, ∀ b < (n2Gens i).length,
      IsP ⁅Ug a, Ug b⁆ (cmP (nthD 0 NG a) (look NI a) (nthD 0 NG b) (look NI b)) ∧
      ∀ v, ⁅Ug a, Ug b⁆ v = linOfRows (commR (n2Gens i)[a]! (n2Gens i)[b]!) v := by
    intro a ha b hb
    have he : ⁅Ug a, Ug b⁆ = Ug a * (Ug b * ((Ug a)⁻¹ * (Ug b)⁻¹)) := by
      rw [commutatorElement_def]
      group
    refine ⟨he ▸ (hUgP a ha).mul ((hUgP b hb).mul ((hUgI a ha).mul (hUgI b hb))), fun v => ?_⟩
    simp only [commutatorElement_def, LinearEquiv.mul_apply, commR, linOfRows_mulR]
    rw [linOfRows_invR (rows_lt (hrow b hb)) (hUgR b hb),
      linOfRows_invR (rows_lt (hrow a ha)) (hUgR a ha), ← hUgR b hb, ← hUgR a ha]
  simp only [Bool.and_eq_true] at hpairs
  have hcp : ∀ p ∈ commPairs i, p.1 < (n2Gens i).length ∧ p.2 < (n2Gens i).length := by
    intro p hp
    have := pairsOK_spec hpairs.1 p hp
    rwa [lenN_eq, hlenNG] at this
  have hlenPG : PG.length = (commPairs i).length := by rw [hPG, pgP, List.length_map]
  have hPGa : ∀ a < (commPairs i).length,
      (commPairs i).getD a (0, 0) ∈ commPairs i ∧
      nthD 0 PG a = cmP (nthD 0 NG ((commPairs i).getD a (0, 0)).1)
        (look NI ((commPairs i).getD a (0, 0)).1) (nthD 0 NG ((commPairs i).getD a (0, 0)).2)
        (look NI ((commPairs i).getD a (0, 0)).2) ∧
      nthD 0 PI a = cmP (nthD 0 NG ((commPairs i).getD a (0, 0)).2)
        (look NI ((commPairs i).getD a (0, 0)).2) (nthD 0 NG ((commPairs i).getD a (0, 0)).1)
        (look NI ((commPairs i).getD a (0, 0)).1) := by
    intro a ha
    refine ⟨?_, ?_, ?_⟩
    · rw [getD_of_lt _ ha]
      exact List.getElem_mem ha
    · rw [hPG, pgP, nthD_map _ _ _ (0, 0) ha]
    · rw [hPI, pgI, nthD_map _ _ _ (0, 0) ha]
  have hPmem : ∀ p ∈ commPairs i, ⁅Ug p.1, Ug p.2⁆ ∈ genGrp (pGens i) := fun p hp =>
    Subgroup.subset_closure ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩,
      (hcomm _ (hcp p hp).1 _ (hcp p hp).2).2⟩
  have hGenP : ∀ U ∈ GenSet (pGens i), ∃ p ∈ commPairs i, U = ⁅Ug p.1, Ug p.2⁆ := by
    rintro U ⟨r, hr, hUr⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    refine ⟨p, hp, LinearEquiv.ext fun v => ?_⟩
    rw [hUr, (hcomm _ (hcp p hp).1 _ (hcp p hp).2).2]
  have hPGisP : ∀ a < PG.length, ∃ U ∈ genGrp (pGens i), IsP U (nthD 0 PG a) ∧
      IsP U⁻¹ (nthD 0 PI a) := by
    intro a ha
    rw [hlenPG] at ha
    obtain ⟨hp, h1, h2⟩ := hPGa a ha
    set p := (commPairs i).getD a (0, 0)
    have hc := hcomm _ (hcp p hp).1 _ (hcp p hp).2
    have hc' := hcomm _ (hcp p hp).2 _ (hcp p hp).1
    refine ⟨_, hPmem p hp, h1 ▸ hc.1, ?_⟩
    rw [commutatorElement_inv, h2]
    exact hc'.1
  have hTG' : TG = pgP NG NI (commPairs i) ++ (List.range (lenN NG)).flatMap (fun a =>
      (List.range (lenN NG)).map fun b =>
        cmP (nthD 0 NG a) (look NI a) (nthD 0 NG b) (look NI b)) ++
      (List.range (lenN NG)).flatMap (fun a => (pgP NG NI (commPairs i)).map fun p =>
        mulP (nthD 0 NG a) (mulP p (look NI a))) ++
      [CFSG.KC.IF4R.packR thetaRows, C] := by
    rw [hTG]
    rfl
  have hmemT : ∀ r ∈ TG, ∃ U ∈ lvlGrp SP TL 0, IsP U r := by
    intro r hr
    obtain ⟨x, -, as, hpath, heq⟩ := CFSG.KC.IF4R.recsOK_spec hsift r hr
    obtain ⟨P, hP, hPP⟩ := CFSG.KC.IF4M.ChainHyp.path0 hC as 0 (by simpa using hpath)
    rw [List.drop_zero] at hPP
    exact ⟨P * 1, Subgroup.mul_mem _ hP (Subgroup.one_mem _), heq ▸ hPP.mul IsP.one⟩
  have hmemT1 : ∀ r ∈ TG, ∀ U, IsP U r → U ∈ lvlGrp SP TL 0 := by
    intro r hr U hU
    obtain ⟨V, hV, hVP⟩ := hmemT r hr
    exact hU.inj hVP ▸ hV
  have hP0 : lvlGrp SP TL 0 = genGrp (pGens i) := by
    apply le_antisymm
    · rw [lvlGrp, Subgroup.closure_le]
      rintro U ⟨g, hg, hUg⟩
      rw [hC.tl0, List.mem_range] at hg
      obtain ⟨-, hw⟩ := wordsG_spec hrw
      obtain ⟨hlt, hweq⟩ := hw g (by simpa using hg)
      obtain ⟨V, hV, hVP⟩ := wordG_isP (K := genGrp (pGens i))
        (fun a ha => (hPGisP a ha).imp fun U h => ⟨h.1, h.2.1⟩) _ hlt
      have hg' : [look SP 0, look SP 1].getD g 0 = look SP g := by
        interval_cases g <;> rfl
      rw [hweq, hg'] at hVP
      exact hUg.inj hVP ▸ hV
    · rw [genGrp, Subgroup.closure_le]
      intro U hU
      obtain ⟨p, hp, rfl⟩ := hGenP U hU
      refine hmemT1 _ ?_ _ (hcomm _ (hcp p hp).1 _ (hcp p hp).2).1
      rw [hTG']
      simp only [List.mem_append]
      refine Or.inl (Or.inl (Or.inl ?_))
      exact List.mem_map.2 ⟨p, hp, rfl⟩
  simp only [Bool.and_eq_true, memN_iff] at hstab
  obtain ⟨ha0, hst⟩ := hstab
  have hst' := stabOK_spec hst
  have horbit : ∀ U ∈ genGrp (n2Gens i), (∀ x ∈ s45 i, ∃ y ∈ s45 i, U (vecOf x) = vecOf y) ∧
      ∀ x ∈ s45 i, ∃ y ∈ s45 i, U⁻¹ (vecOf x) = vecOf y := by
    intro U hU
    induction hU using Subgroup.closure_induction with
    | mem U hU =>
      obtain ⟨l, hl, rfl⟩ := hgenSet U hU
      refine ⟨fun x hx => ⟨_, hst' x hx _ ?_, (hUgP l hl).apply_code x⟩,
        fun x hx => ⟨_, hst' x hx _ ?_, (hUgI l hl).apply_code x⟩⟩
      · exact List.mem_append_left _ (nthD_mem 0 (hlenNG ▸ hl))
      · refine List.mem_append_right _ (List.mem_map.2 ⟨l, ?_, rfl⟩)
        rw [List.mem_range, lenN_eq, hlenNG]
        exact hl
    | one => exact ⟨fun x hx => ⟨x, hx, rfl⟩, fun x hx => ⟨x, hx, rfl⟩⟩
    | mul U V _ _ hU hV =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨y, hy, hxy⟩ := hV.1 x hx
        obtain ⟨w, hw, hyw⟩ := hU.1 y hy
        exact ⟨w, hw, by rw [LinearEquiv.mul_apply, hxy, hyw]⟩
      · obtain ⟨y, hy, hxy⟩ := hU.2 x hx
        obtain ⟨w, hw, hyw⟩ := hV.2 y hy
        exact ⟨w, hw, by rw [mul_inv_rev, LinearEquiv.mul_apply, hxy, hyw]⟩
    | inv U _ hU => exact ⟨fun x hx => hU.2 x hx, fun x hx => by rw [inv_inv]; exact hU.1 x hx⟩
  obtain ⟨hOL0, hOLlen, hSOL, htree⟩ := reachOK_spec hreach
  have hreachOL : ∀ x < OL.length, ∃ U ∈ genGrp (n2Gens i), U (vecOf a0) = vecOf (OL.getD x 0) := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · exact ⟨1, Subgroup.one_mem _, by rw [hOL0]; rfl⟩
      · obtain ⟨p, rfl⟩ : ∃ p, x = 1 + p := ⟨x - 1, by omega⟩
        obtain ⟨hq, hl, heq⟩ := htree p (by omega)
        obtain ⟨V, hV, hVa⟩ := ih _ hq (by omega)
        set l := (OT.getD p []).getD 1 0
        have hl' : l < (n2Gens i).length := hlenNG ▸ hl
        refine ⟨Ug l * V, Subgroup.mul_mem _ (hUgN l hl') hV, ?_⟩
        rw [LinearEquiv.mul_apply, hVa, (hUgP l hl').apply_code, ← heq, nthD_eq]
  have hsig := hsigma
  simp only [sigmaOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.not_eq_true', beq_iff_eq] at hsig
  obtain ⟨⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩ := hsig
  have hbl := sigmaBasis_lt i
  have hov := hoval
  simp only [ovalOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hov
  have houtlt : ∀ x ∈ outPts i, x < 4096 := fun x hx => by
    simp only [outPts, List.mem_filter] at hx
    exact spanList_lt hbl x hx.1
  obtain ⟨hfix, hne⟩ := ncOK_spec hnc
  refine ⟨
    { orbit_subset := fun U hU => (horbit U hU).1 a0 ha0
      orbit_reach := fun x hx => ?_
      finrank_sigma := by
        rw [finrank_of_indepCheck hbl hs5, hs6]
      orbit_mem_sigma := fun x hx => mem_spanOf_of_mem_spanList hbl (hs2 x hx)
      sigma_le_span := Submodule.span_le.2 fun _ ⟨b, hb, hbv⟩ =>
        Submodule.subset_span ⟨b, hs1 b hb, hbv⟩
      q0_sigma := fun v hv => by
        have h := hs3 _ (codeOf_mem_spanList hbl hv)
        rw [← vecOf_codeOf v, q0_vecOf, h]
        rfl
      theta0_sigma := ?_
      outPts_length := hov.1
      outPts_not_collinear := ?_
      card_p2 := by rw [← hP0, hC.card_zero, hO]
      commutator_n2 := ?_
      commutator_p2 := ?_
      theta0_mem_p2 := ?_
      exists_noncentral := ?_ }, hP0⟩
  · obtain ⟨y, hy, hyx⟩ := List.mem_iff_getElem.1 (hSOL x hx)
    obtain ⟨U, hU, hUa⟩ := hreachOL y hy
    exact ⟨U, hU, by rw [hUa, getD_of_lt _ hy, hyx]⟩
  · have hle : spanOf (sigmaBasis i) ≤ (spanOf (sigmaBasis i)).comap theta0 :=
      Submodule.span_le.2 fun _ ⟨b, hb, hbv⟩ => by
        rw [← hbv]
        change theta0 (vecOf b) ∈ spanOf (sigmaBasis i)
        rw [← vecOf_theta0N (hbl b hb)]
        exact mem_spanOf_of_mem_spanList hbl (hs4 b hb)
    exact fun v hv => hle hv
  · intro x hx y hy w hw hxy hxw hyw hm
    have hxl := houtlt x hx
    have hyl := houtlt y hy
    have hwl := houtlt w hw
    have h : inF4Span x y w = false := by
      rcases hov.2 x hx y hy w hw with h' | h'
      · simp only [f4Indep_of hxl hyl hxy, f4Indep_of hxl hwl hxw, f4Indep_of hyl hwl hyw,
          Bool.and_self] at h'
        exact absurd h' (by decide)
      · exact h'
    have hlt : ∀ v ∈ [x, theta0N x, y, theta0N y], v < 4096 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact hxl
      · exact theta0N_lt hxl
      · exact hyl
      · exact theta0N_lt hyl
    rw [← mem_spanList_iff hlt hwl, ← List.contains_iff_mem] at hm
    rw [inF4Span, hm] at h
    exact Bool.noConfusion h
  ·
    apply le_antisymm
    · have hnorm : Subgroup.closure (GenSet (n2Gens i)) ≤
          Subgroup.normalizer (genGrp (pGens i) : Set GL) := by
        rw [Subgroup.closure_le]
        intro U hU
        obtain ⟨l, hl, rfl⟩ := hgenSet U hU
        refine mem_normalizer_of_conj fun x hx => ?_
        rw [genGrp] at hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨p, hp, rfl⟩ := hGenP x hx
          rw [← hP0]
          refine hmemT1 _ ?_ _ (by
            rw [mul_assoc]
            exact (hUgP l hl).mul ((hcomm _ (hcp p hp).1 _ (hcp p hp).2).1.mul (hUgI l hl)))
          rw [hTG']
          simp only [List.mem_append]
          refine Or.inl (Or.inr (List.mem_flatMap.2 ⟨l, ?_, List.mem_map.2 ⟨_, ?_, rfl⟩⟩))
          · rw [List.mem_range, lenN_eq, hlenNG]
            exact hl
          · exact List.mem_map.2 ⟨p, hp, rfl⟩
        | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
        | mul x y _ _ hx hy =>
          have : Ug l * (x * y) * (Ug l)⁻¹ = (Ug l * x * (Ug l)⁻¹) * (Ug l * y * (Ug l)⁻¹) := by
            group
          rw [this]
          exact Subgroup.mul_mem _ hx hy
        | inv x _ hx =>
          have : Ug l * x⁻¹ * (Ug l)⁻¹ = (Ug l * x * (Ug l)⁻¹)⁻¹ := by group
          rw [this]
          exact Subgroup.inv_mem _ hx
      refine commutator_le_of_gens hnorm fun a ha b hb => ?_
      obtain ⟨l, hl, rfl⟩ := hgenSet a ha
      obtain ⟨m, hm, rfl⟩ := hgenSet b hb
      rw [← hP0]
      refine hmemT1 _ ?_ _ (hcomm l hl m hm).1
      rw [hTG']
      simp only [List.mem_append]
      refine Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨l, ?_, List.mem_map.2 ⟨m, ?_, rfl⟩⟩)))
      · rw [List.mem_range, lenN_eq, hlenNG]
        exact hl
      · rw [List.mem_range, lenN_eq, hlenNG]
        exact hm
    · rw [genGrp, Subgroup.closure_le]
      intro U hU
      obtain ⟨p, hp, rfl⟩ := hGenP U hU
      exact Subgroup.commutator_mem_commutator (hUgN _ (hcp p hp).1) (hUgN _ (hcp p hp).2)
  ·
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · have hpp : ∀ q ∈ perfPairs i, q.1 < PG.length ∧ q.2 < PG.length := by
        intro q hq
        have := pairsOK_spec hpairs.2 q hq
        rwa [lenN_eq] at this
      have hDG : ∀ l < (dgP PG PI (perfPairs i)).length,
          ∃ U ∈ ⁅genGrp (pGens i), genGrp (pGens i)⁆,
            IsP U (nthD 0 (dgP PG PI (perfPairs i)) l) := by
        intro l hl
        unfold dgP at hl ⊢
        obtain ⟨q, hq, hql⟩ := List.mem_map.1 (nthD_mem 0 hl)
        rw [← hql]
        obtain ⟨A, hA, hAP, hAI⟩ := hPGisP _ (hpp q hq).1
        obtain ⟨B, hB, hBP, hBI⟩ := hPGisP _ (hpp q hq).2
        have he : ⁅A, B⁆ = A * (B * (A⁻¹ * B⁻¹)) := by
          rw [commutatorElement_def]
          group
        exact ⟨⁅A, B⁆, Subgroup.commutator_mem_commutator hA hB,
          he ▸ hAP.mul (hBP.mul (hAI.mul hBI))⟩
      obtain ⟨-, hw⟩ := wordsG_spec hdw
      rw [genGrp, Subgroup.closure_le]
      intro U hU
      obtain ⟨p, hp, rfl⟩ := hGenP U hU
      obtain ⟨a, ha, hpa⟩ := List.mem_iff_getElem.1 hp
      obtain ⟨hlt, hweq⟩ := hw a (hlenPG ▸ ha)
      obtain ⟨V, hV, hVP⟩ := wordG_isP hDG _ hlt
      obtain ⟨-, h1, -⟩ := hPGa a ha
      rw [hweq, ← nthD_eq, h1, getD_of_lt _ ha, hpa] at hVP
      exact ((hcomm _ (hcp p hp).1 _ (hcp p hp).2).1.inj hVP) ▸ hV
  ·
    have hmem : CFSG.KC.IF4R.packR thetaRows ∈ TG := by
      rw [hTG']
      simp
    obtain ⟨U, hU, hUP⟩ := hmemT _ hmem
    refine ⟨U, hP0 ▸ hU, fun v => ?_⟩
    rw [(isP_packR rowsOK_thetaRows U).1 hUP v, linOfRows_thetaRows]
  ·
    have hmem : C ∈ TG := by
      rw [hTG']
      simp
    obtain ⟨Cc, hCc, hCcP⟩ := hmemT _ hmem
    obtain ⟨Pk, hPk, hPkP, -⟩ := hPGisP CG (hlenPG ▸ hCG)
    refine ⟨Cc, hP0 ▸ hCc, fun v hv => ?_, Pk, hPk, fun heq => hne ?_⟩
    · have hle : spanOf (sigmaBasis i) ≤
          LinearMap.ker ((Cc : V12 →ₗ[ZMod 2] V12) - LinearMap.id) :=
        Submodule.span_le.2 fun _ ⟨b, hb, hbv⟩ => by
          rw [← hbv, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
            sub_eq_zero]
          change Cc (vecOf b) = vecOf b
          rw [hCcP.apply_code, hfix b hb]
      have := hle hv
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    · have h1 := hCcP.mul hPkP
      have h2 := hPkP.mul hCcP
      rw [heq] at h1
      exact mulP_eq_of_linP fun v => (h1 v).symm.trans (h2 v)

end Facts

end CFSG.KC.GUS

end

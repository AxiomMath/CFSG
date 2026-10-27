module

public import Certificates.Certificate15086
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.HeldB.InnerRestrict

public section

namespace CFSG.ComponentClassification.AS81.HePres

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.CosetTable
open CFSG.ComponentClassification.AS81.HePres.Native

theorem rep_wordArrW {k n : ℕ} {gens invs : Array (Array ℕ)} {g : Fin k → Equiv.Perm (Fin n)}
    (hg : ∀ i : Fin k, Rep n (gens.getD i.val #[]) (g i))
    (hgi : ∀ i : Fin k, Rep n (invs.getD i.val #[]) (g i)⁻¹) (w : List (Fin k × Bool)) :
    Rep n (wordArrW n gens invs w) (FreeGroup.lift g (FreeGroup.mk w)) := by
  induction w with
  | nil => exact rep_idA
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [e, map_mul]
    refine rep_compA ?_ ih
    obtain ⟨i, b⟩ := l
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      exact hg i
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      exact hgi i

theorem lift_eq_one_of_modelCheck {k n : ℕ} {gens : Array (Array ℕ)}
    {rels : List (List (Fin k × Bool))} (h : modelCheck n gens rels = true) :
    ∀ r ∈ rels, FreeGroup.lift (fun i : Fin k => permOfArr n (gens.getD i.val #[]))
      (FreeGroup.mk r) = 1 := by
  simp only [modelCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hinv, hrel⟩ := h
  have hrep : ∀ i : Fin k, Rep n (gens.getD i.val #[]) (permOfArr n (gens.getD i.val #[])) ∧
      Rep n ((gens.map (invCand n)).getD i.val #[]) (permOfArr n (gens.getD i.val #[]))⁻¹ :=
    fun i => rep_permOfArr (hinv i.val i.2)
  intro r hr
  rw [relArrCheck, List.all_eq_true] at hrel
  exact eq_of_eqA (rep_wordArrW (fun i => (hrep i).1) (fun i => (hrep i).2) r) rep_idA
    (hrel r hr)

noncomputable def abG (l : ℤ) : CFSG.Sporadic.He.J :=
  if l = 1 ∨ l = -1 then CFSG.Sporadic.He.a else if l = 2 then CFSG.Sporadic.He.b
  else CFSG.Sporadic.He.b⁻¹

noncomputable def heGen (gw : List (List ℤ)) (i : Fin 8) :
    CFSG.Sporadic.He.J :=
  CFSG.Sporadic.Th.wordG abG (gw.getD i.val [])

theorem mat_inv (g : CFSG.Sporadic.He.J) :
    CFSG.Sporadic.He.mat g⁻¹ = (CFSG.Sporadic.He.mat g)⁻¹ := by
  change ((g⁻¹ : CFSG.Sporadic.He.J) : GL (Fin 50) (ZMod 7)).val = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem mat_list_prod (l : List CFSG.Sporadic.He.J) :
    CFSG.Sporadic.He.mat l.prod = (l.map CFSG.Sporadic.He.mat).prod := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.prod_cons, CFSG.Sporadic.He.mat_mul, ih, List.map_cons, List.prod_cons]

theorem mat_abG (l : ℤ) :
    CFSG.Sporadic.He.mat (abG l) = heSeedMat l := by
  unfold abG heSeedMat
  split_ifs
  · exact CFSG.Sporadic.He.mat_a
  · exact CFSG.Sporadic.He.mat_b
  · rw [mat_inv, CFSG.Sporadic.He.mat_b]

theorem mat_wordG (w : List ℤ) :
    CFSG.Sporadic.He.mat (CFSG.Sporadic.Th.wordG abG w) = heWordMat w := by
  rw [CFSG.Sporadic.Th.wordG, mat_list_prod, heWordMat, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => mat_abG l

theorem mat_lift_heGen (gw : List (List ℤ))
    (r : List (Fin 8 × Bool)) :
    CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk r)) =
      (r.map (hePiLetMat gw)).prod := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    have e : FreeGroup.mk (l :: r) = FreeGroup.mk [l] * FreeGroup.mk r := rfl
    have key : CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk [l])) =
        hePiLetMat gw l := by
      obtain ⟨i, s⟩ := l
      cases s
      · have h1 : FreeGroup.lift (heGen gw) (FreeGroup.mk [(i, false)]) = (heGen gw i)⁻¹ := by
          rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
            FreeGroup.lift_apply_of]
        have h2 : hePiLetMat gw (i, false) = (heWordMat (gw.getD i.val []))⁻¹ := by
          simp [hePiLetMat]
        rw [h1, mat_inv, heGen, mat_wordG, h2]
      · have h1 : FreeGroup.lift (heGen gw) (FreeGroup.mk [(i, true)]) = heGen gw i := by
          rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
        have h2 : hePiLetMat gw (i, true) = heWordMat (gw.getD i.val []) := by
          simp [hePiLetMat]
        rw [h1, heGen, mat_wordG, h2]
    calc CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk (l :: r)))
        = CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk [l]) *
            FreeGroup.lift (heGen gw) (FreeGroup.mk r)) := by rw [e, map_mul]
      _ = CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk [l])) *
            CFSG.Sporadic.He.mat (FreeGroup.lift (heGen gw) (FreeGroup.mk r)) :=
          CFSG.Sporadic.He.mat_mul _ _
      _ = hePiLetMat gw l * (r.map (hePiLetMat gw)).prod := by rw [key, ih]
      _ = ((l :: r).map (hePiLetMat gw)).prod := by rw [List.map_cons, List.prod_cons]

theorem heImage_of_facts (h : HePiImageFacts) :
    (∀ r ∈ hePiRels, FreeGroup.lift (heGen hePiHeWords) (FreeGroup.mk r) = 1) ∧
      FreeGroup.lift (heGen hePiHeWords) (FreeGroup.mk hePiAWord) = CFSG.Sporadic.He.a ∧
      FreeGroup.lift (heGen hePiHeWords) (FreeGroup.mk hePiBWord) = CFSG.Sporadic.He.b ∧
      FreeGroup.lift (heGen hePiHeWords) (FreeGroup.mk hePiZWord) =
        CFSG.Sporadic.Th.wordG abG heT1Letters := by
  obtain ⟨-, -, hrel, ha, hb, hz⟩ := h
  refine ⟨fun r hr => CFSG.Sporadic.He.mat_injective ?_, CFSG.Sporadic.He.mat_injective ?_,
    CFSG.Sporadic.He.mat_injective ?_, CFSG.Sporadic.He.mat_injective ?_⟩
  · rw [mat_lift_heGen, hrel r hr, CFSG.Sporadic.He.mat_one]
  · rw [mat_lift_heGen, ha, CFSG.Sporadic.He.mat_a]
  · rw [mat_lift_heGen, hb, CFSG.Sporadic.He.mat_b]
  · rw [mat_lift_heGen, hz, mat_wordG]

abbrev HePi : Type := PG 8 hePiRels

@[expose] def hePiZ : HePi :=
  PresentedGroup.of 1 * PresentedGroup.of 2 * PresentedGroup.of 1 * PresentedGroup.of 2

theorem hePiZ_eq : hePiZ = PresentedGroup.mk _ (FreeGroup.mk hePiZWord) := rfl

@[expose] def hePiLift {G : Type*} [Group G] (g : Fin 8 → G)
    (hg : ∀ r ∈ hePiRels, FreeGroup.lift g (FreeGroup.mk r) = 1) : HePi →* G :=
  PresentedGroup.toGroup (f := g) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hg w hw

theorem hePiLift_of {G : Type*} [Group G] {g : Fin 8 → G}
    (hg : ∀ r ∈ hePiRels, FreeGroup.lift g (FreeGroup.mk r) = 1) (i : Fin 8) :
    hePiLift g hg (PresentedGroup.of i) = g i :=
  PresentedGroup.toGroup.of _

theorem hePiLift_mk {G : Type*} [Group G] {g : Fin 8 → G}
    (hg : ∀ r ∈ hePiRels, FreeGroup.lift g (FreeGroup.mk r) = 1) (w : List (Fin 8 × Bool)) :
    hePiLift g hg (PresentedGroup.mk _ (FreeGroup.mk w)) = FreeGroup.lift g (FreeGroup.mk w) :=
  rfl

theorem hePiLift_z {G : Type*} [Group G] {g : Fin 8 → G}
    (hg : ∀ r ∈ hePiRels, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    hePiLift g hg hePiZ = g 1 * g 2 * g 1 * g 2 := by
  simp only [hePiZ, map_mul, hePiLift_of]

theorem hePiRels_mem : ∀ r ∈ hePiRels, r ∈ hePiRelsC ∨ r ∈ hePiRelsE ∨ r ∈ hePiRelsF := by
  intro r hr
  simp only [hePiRels, hePiRelsC, hePiRelsE, hePiRelsF, hePiRelsCodes, hePiRelsCCodes,
    hePiRelsECodes, hePiRelsFCodes, List.map_append, List.mem_append] at hr ⊢
  tauto

theorem hePiRelsC_letters : ∀ r ∈ hePiRelsC, ∀ l ∈ r, l.1 ≠ 6 ∧ l.1 ≠ 7 := by
  decide +kernel

theorem hePiRelsE_letters : ∀ r ∈ hePiRelsE, ∀ l ∈ r, l.1 ≠ 5 := by
  decide +kernel

theorem hePiRelsF_letters : ∀ r ∈ hePiRelsF, ∀ l ∈ r, l.1 ≠ 4 := by
  decide +kernel

theorem lift_mk_congr {G : Type*} [Group G] {k : ℕ} {g g' : Fin k → G}
    {w : List (Fin k × Bool)} (h : ∀ l ∈ w, g l.1 = g' l.1) :
    FreeGroup.lift g (FreeGroup.mk w) = FreeGroup.lift g' (FreeGroup.mk w) := by
  rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  rw [h l hl]

theorem card_hePi :
    Finite HePi ∧ Nat.card HePi ≤ 4030387200 :=
  Certificates.certificate15086.1

theorem hePiC_rels (s : Bool) :
    ∀ r ∈ hePiRelsC, FreeGroup.lift (fun i : Fin 8 => permOfArr 32 ((hePiCArrs s).getD i.val #[]))
      (FreeGroup.mk r) = 1 := by
  obtain ⟨-, -, h0, h1, -, -⟩ := Certificates.certificate15086
  cases s
  · exact lift_eq_one_of_modelCheck h0
  · exact lift_eq_one_of_modelCheck h1

theorem hePiE_rels :
    ∀ r ∈ hePiRelsE, FreeGroup.lift (fun i : Fin 8 => permOfArr 64 (hePiEArrs.getD i.val #[]))
      (FreeGroup.mk r) = 1 :=
  lift_eq_one_of_modelCheck Certificates.certificate15086.2.2.2.2.1

theorem hePiF_rels :
    ∀ r ∈ hePiRelsF, FreeGroup.lift (fun i : Fin 8 => permOfArr 64 (hePiFArrs.getD i.val #[]))
      (FreeGroup.mk r) = 1 :=
  lift_eq_one_of_modelCheck Certificates.certificate15086.2.2.2.2.2

theorem hePiHeWords_lettersOK :
    ∀ w ∈ hePiHeWords, lettersOK 2 w = true :=
  Certificates.certificate15086.2.1.2.1

noncomputable def hePiToJ :
    HePi →* CFSG.Sporadic.He.J :=
  hePiLift (heGen hePiHeWords) (heImage_of_facts Certificates.certificate15086.2.1).1

theorem hePiToJ_bijective :
    Function.Bijective hePiToJ := by
  have hi := heImage_of_facts Certificates.certificate15086.2.1
  have hsurj : Function.Surjective hePiToJ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← CFSG.Sporadic.He.closure_ab,
      Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨_, (hePiLift_mk _ hePiAWord).trans hi.2.1⟩
    · exact ⟨_, (hePiLift_mk _ hePiBWord).trans hi.2.2.1⟩
  have := card_hePi.1
  exact hsurj.bijective_of_nat_card_le (card_hePi.2.trans CFSG.Sporadic.He.card_J.ge)

noncomputable def hePiEquivJ :
    HePi ≃* CFSG.Sporadic.He.J :=
  MulEquiv.ofBijective hePiToJ hePiToJ_bijective

noncomputable def hePiEquivHe :
    HePi ≃* Blueprint.NativeSporadic.He :=
  hePiEquivJ.trans CFSG.Sporadic.He.heEquivJ.symm

noncomputable def hePiEquivP :
    HePi ≃* CFSG.Sporadic.HeldB.heP :=
  hePiEquivJ.trans CFSG.Sporadic.HeldB.heJEquivP

theorem hePi_simple :
    IsSimpleGroup HePi :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HeldB.heP_simple hePiEquivP

theorem evalSignedWord_cons {n : ℕ} {gs : List (Equiv.Perm (Fin n))} {l : ℤ} {w : List ℤ}
    (hl : l ≠ 0 ∧ l.natAbs ≤ gs.length) (hw : lettersOK gs.length w = true) :
    CFSG.Sporadic.HeldB.evalSignedWord gs (l :: w) =
      (if 0 < l then gs.getD (l.natAbs - 1) 1 else (gs.getD (l.natAbs - 1) 1)⁻¹) *
        CFSG.Sporadic.HeldB.evalSignedWord gs w := by
  have hlw : lettersOK gs.length (l :: w) = true := by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw ⊢
    exact ⟨hl, hw⟩
  rw [CFSG.Sporadic.HeldB.evalSignedWord, ite_eq_left hlw, CFSG.Sporadic.HeldB.evalSignedWord,
    ite_eq_left hw]
  have hcons : toLetters gs.length (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
      toLetters gs.length w := by
    simp [toLetters, hl.1, hl.2]
  rw [hcons, Quiver.SchreierGraph.evalWord, Quiver.SchreierGraph.evalWord,
    show FreeGroup.mk ((⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: toLetters gs.length w) =
      FreeGroup.mk [(⟨l.natAbs - 1, by omega⟩, decide (0 < l))] *
        FreeGroup.mk (toLetters gs.length w) from rfl, map_mul]
  congr 1
  have hget : gs.get ⟨l.natAbs - 1, by omega⟩ = gs.getD (l.natAbs - 1) 1 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    rfl
  by_cases hpos : 0 < l
  · rw [ite_eq_left hpos, decide_eq_true hpos,
      show FreeGroup.mk [((⟨l.natAbs - 1, by omega⟩ : Fin gs.length), true)] =
        FreeGroup.of ⟨l.natAbs - 1, by omega⟩ from rfl, FreeGroup.lift_apply_of, hget]
  · rw [ite_eq_right hpos, decide_eq_false hpos,
      show FreeGroup.mk [((⟨l.natAbs - 1, by omega⟩ : Fin gs.length), false)] =
        (FreeGroup.of ⟨l.natAbs - 1, by omega⟩)⁻¹ from rfl, map_inv, FreeGroup.lift_apply_of,
      hget]

theorem map_wordG_eq_evalSignedWord {H : Type*} [Group H] {n : ℕ}
    (φ : H →* Equiv.Perm (Fin n)) {f : ℤ → H} {g₀ g₁ : Equiv.Perm (Fin n)}
    (h1 : φ (f 1) = g₀) (hm1 : φ (f (-1)) = g₀⁻¹) (h2 : φ (f 2) = g₁)
    (hm2 : φ (f (-2)) = g₁⁻¹) (w : List ℤ) (hw : lettersOK 2 w = true) :
    φ (CFSG.Sporadic.Th.wordG f w) = CFSG.Sporadic.HeldB.evalSignedWord [g₀, g₁] w := by
  induction w with
  | nil =>
    rw [CFSG.Sporadic.HeldB.evalSignedWord, ite_eq_left (by rfl)]
    simp [CFSG.Sporadic.Th.wordG, toLetters, Quiver.SchreierGraph.evalWord]
  | cons l w ih =>
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨hl, hw⟩ := hw
    have hw' : lettersOK 2 w = true := by simpa [lettersOK, List.all_eq_true] using hw
    rw [evalSignedWord_cons (gs := [g₀, g₁]) hl hw', ← ih hw', CFSG.Sporadic.Th.wordG,
      List.map_cons, List.prod_cons, map_mul, ← CFSG.Sporadic.Th.wordG]
    congr 1
    obtain ⟨hl0, hl2⟩ := hl
    have : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simpa using h1
    · simpa using hm1
    · simpa using h2
    · simpa using hm2

theorem heJToP_wordG
    (w : List ℤ) (hw : lettersOK 2 w = true) :
    CFSG.Sporadic.HeldB.heJToP (CFSG.Sporadic.Th.wordG abG w) =
      CFSG.Sporadic.HeldB.evalSignedWord
        [CFSG.Sporadic.HeldB.heGenPerm 0, CFSG.Sporadic.HeldB.heGenPerm 1] w := by
  have ha : abG 1 = CFSG.Sporadic.He.a := by simp [abG]
  have ha' : abG (-1) = CFSG.Sporadic.He.a := by simp [abG]
  have hb : abG 2 = CFSG.Sporadic.He.b := by simp [abG]
  have hb' : abG (-2) = CFSG.Sporadic.He.b⁻¹ := by simp [abG]
  refine map_wordG_eq_evalSignedWord _ ?_ ?_ ?_ ?_ w hw
  · rw [ha, CFSG.Sporadic.HeldB.heJToP_a]
  · rw [ha', ← CFSG.Sporadic.He.a_inv, map_inv, CFSG.Sporadic.HeldB.heJToP_a]
  · rw [hb, CFSG.Sporadic.HeldB.heJToP_b]
  · rw [hb', map_inv, CFSG.Sporadic.HeldB.heJToP_b]

theorem lettersOK_getD {gw : List (List ℤ)} (h : ∀ w ∈ gw, lettersOK 2 w = true) (i : ℕ) :
    lettersOK 2 (gw.getD i []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : gw[i]? with
  | none => rfl
  | some w => exact h w (List.mem_of_getElem? hi)

theorem hePiEquivP_of
    (i : Fin 8) :
    (hePiEquivP (PresentedGroup.of i) : Equiv.Perm (Fin 8330)) =
      CFSG.Sporadic.HeldB.evalSignedWord
        [CFSG.Sporadic.HeldB.heGenPerm 0, CFSG.Sporadic.HeldB.heGenPerm 1]
        (hePiHeWords.getD i.val []) := by
  change CFSG.Sporadic.HeldB.heJToP (hePiToJ (PresentedGroup.of i)) = _
  rw [hePiToJ, hePiLift_of, heGen]
  exact heJToP_wordG _ (lettersOK_getD hePiHeWords_lettersOK _)

theorem heT1Letters_eq : heT1Letters = CFSG.Sporadic.HeldB.heT1Word := rfl

theorem hePiEquivP_z :
    (hePiEquivP hePiZ : Equiv.Perm (Fin 8330)) = CFSG.Sporadic.HeldB.heT1P := by
  change CFSG.Sporadic.HeldB.heJToP (hePiToJ hePiZ) = _
  rw [hePiZ_eq, hePiToJ, hePiLift_mk,
    (heImage_of_facts Certificates.certificate15086.2.1).2.2.2,
    heJToP_wordG _ (by decide), CFSG.Sporadic.HeldB.heT1P, heT1Letters_eq]

end CFSG.ComponentClassification.AS81.HePres

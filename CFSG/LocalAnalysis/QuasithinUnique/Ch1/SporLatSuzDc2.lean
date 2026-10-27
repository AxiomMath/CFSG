module

public import Certificates.Certificate10502
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatSeq
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import CFSG.Sporadic.SuzOddCore.CertChain
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.SuzK

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SuzOddCore CFSG.KC.E64F
open CFSG.KD.SuzDc2 (L C D shapeOK letOK wOK sbOK)

@[expose] noncomputable def E0 : Array ↥suzP := #[1, 1, 1, 1, 1, 1, suzA0P, suzA1P]

@[expose] noncomputable def X : ↥suzP := evalElt E0 [6, 7]

@[expose] noncomputable def Y : ↥suzP := evalElt E0 [6, 7, 7]

@[expose] noncomputable def E1 : Array ↥suzP := #[1, 1, 1, 1, 1, 1, suzA0P, suzA1P, X, Y]

@[expose] noncomputable def sg (i : ℕ) : ↥suzP := evalElt E1 (CFSG.KD.SuzDc2.LT.sgw.getD i [])

@[expose] noncomputable def E2 : Array ↥suzP := #[sg 0, sg 1, sg 2, sg 3, 1, 1, suzA0P, suzA1P]

@[expose] noncomputable def hh : ↥suzP := evalElt E2 CFSG.KD.SuzDc2.LT.hw

@[expose] noncomputable def els : List ↥suzP :=
  [sg 0, sg 1, sg 2, sg 3, (sg 3)⁻¹, hh, suzA0P, suzA1P]

private theorem good_congr {t : Array ℕ} {f g : ℕ → ℕ} (h : Good 22880 t f)
    (e : ∀ p < 22880, f p = g p) : Good 22880 t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

theorem hodd : ¬ 2 ∣ C.N1 * C.N2 := by
  change ¬ 2 ∣ 405405 * 135
  decide

section Order


theorem sep0 :
    ∀ g : ↥suzP, (∀ p ∈ [0, 1, 2, 3, 4, 5], act 22880 g p = p) → g = 1 := by
  intro g hg
  have hF := CFSG.Sporadic.Schreier.baseFaithful_of_valid certChain_valid
  have eb : certChain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5] := by
    rw [certChain_base_toList]
    rfl
  rw [certChain_originalSubgroup, eb] at hF
  have h1 := hF _ g.2 fun x hx => by
    have e := hg x.val hx
    rw [act_eq, Subgroup.smul_def, Equiv.Perm.smul_def] at e
    exact Fin.ext e
  exact Subtype.ext h1

theorem hN : Nat.card ↥suzP = C.N1 * C.N2 * 2 ^ C.k := by
  change Nat.card ↥suzP = 405405 * 135 * 2 ^ 13
  rw [suzP_card]
  norm_num

end Order

section Facts


theorem facts : CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 22880, (certArr l)[p]! = L (Nat.add 6 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 3, 4, 5] ∧ sbOK = true ∧
    CFSG.KD.SuzDc2.SB.C.flatten.length = 8192 :=
  Certificates.certificate10502

theorem shape_parts : (∀ i < 4, ∀ l ∈ CFSG.KD.SuzDc2.LT.sgw.getD i [], 5 < l ∧ l < 10) ∧
    ∀ l ∈ CFSG.KD.SuzDc2.LT.hw, (l < 4 ∨ l = 6) ∨ l = 7 := by
  have h := facts.2.2.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi l hl => ?_, h3⟩
  rw [List.getD_eq_getElem _ _ (by omega)] at hl
  exact h2 _ (List.getElem_mem _) l hl

theorem let_parts : (∀ p < 22880, L 8 p = wordF L [6, 7] p) ∧
    (∀ p < 22880, L 9 p = wordF L [6, 7, 7] p) ∧
    (∀ i < 4, ∀ p < 22880, L i p = wordF L (CFSG.KD.SuzDc2.LT.sgw.getD i []) p) ∧
    (∀ p < 22880, L 5 p = wordF L CFSG.KD.SuzDc2.LT.hw p) ∧
    ∀ p < 22880, L 4 (L 3 p) = p := by
  have h := facts.2.2.2.1
  unfold letOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h8, h9⟩, h0⟩, h1⟩, h2⟩, h3⟩, h5⟩, hi⟩ := h
  have wk : ∀ {l : ℕ} {w : List ℕ}, wOK l w = true → ∀ p < 22880, L l p = wordF L w p :=
    fun {l w} hw p hp => by
      unfold wOK at hw
      exact Nat.eq_of_beq_eq_true (CFSG.KC.SLOm.all_range hw p hp)
  refine ⟨wk h8, wk h9, fun i hi p hp => ?_, wk h5, fun p hp => ?_⟩
  · interval_cases i
    · exact wk h0 p hp
    · exact wk h1 p hp
    · exact wk h2 p hp
    · exact wk h3 p hp
  · exact Nat.eq_of_beq_eq_true (CFSG.KC.SLOm.all_range hi p hp)

end Facts

section Letters


theorem good_gen {l : ℕ} (hl : l < 2) {g : ↥suzP}
    (hg : (g : Equiv.Perm (Fin 22880)) = permC 22880 (certArr l)) :
    Good 22880 (tab 22880 g).toArray (L (Nat.add 6 l)) := by
  have hr : ∀ p (hp : p < 22880), (certArr l)[p]! = ((permC 22880 (certArr l)) ⟨p, hp⟩ : ℕ) :=
    fun p hp => rep_certArr (by omega) ⟨p, hp⟩
  have ha : ∀ p (hp : p < 22880), act 22880 g p = ((permC 22880 (certArr l)) ⟨p, hp⟩ : ℕ) := by
    intro p hp
    have e := act_eq g ⟨p, hp⟩
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, hg] at e
    exact e
  refine ⟨tabA_size g, fun p hp => ⟨?_, ?_⟩⟩
  · rw [tabA_getD, ha p hp, ← hr p hp, facts.2.1 l hl p hp]
  · rw [← facts.2.1 l hl p hp, hr p hp]
    exact Fin.isLt _

theorem good_E0 {l : ℕ} (hl : l = 6 ∨ l = 7) :
    Good 22880 (tab 22880 (E0.getD l 1)).toArray (L l) := by
  rcases hl with rfl | rfl
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl

theorem good_X : Good 22880 (tab 22880 X).toArray (L 8) :=
  good_congr (good_evalElt E0 L fun l hl => good_E0 (by simpa using hl))
    fun p hp => (let_parts.1 p hp).symm

theorem good_Y : Good 22880 (tab 22880 Y).toArray (L 9) :=
  good_congr (good_evalElt E0 L fun l hl => good_E0 (by simpa using hl))
    fun p hp => (let_parts.2.1 p hp).symm

theorem good_E1 {l : ℕ} (hl : 5 < l ∧ l < 10) :
    Good 22880 (tab 22880 (E1.getD l 1)).toArray (L l) := by
  obtain ⟨h1, h2⟩ := hl
  interval_cases l
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl
  · exact good_X
  · exact good_Y

theorem good_sg {i : ℕ} (hi : i < 4) : Good 22880 (tab 22880 (sg i)).toArray (L i) :=
  good_congr (good_evalElt E1 L fun l hl => good_E1 (shape_parts.1 i hi l hl))
    fun p hp => (let_parts.2.2.1 i hi p hp).symm

theorem good_E2 {l : ℕ} (hl : (l < 4 ∨ l = 6) ∨ l = 7) :
    Good 22880 (tab 22880 (E2.getD l 1)).toArray (L l) := by
  rcases hl with (hl | rfl) | rfl
  · interval_cases l
    · exact good_sg (i := 0) (by norm_num)
    · exact good_sg (i := 1) (by norm_num)
    · exact good_sg (i := 2) (by norm_num)
    · exact good_sg (i := 3) (by norm_num)
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl

theorem good_hh : Good 22880 (tab 22880 hh).toArray (L 5) :=
  good_congr (good_evalElt E2 L fun l hl => good_E2 (shape_parts.2 l hl))
    fun p hp => (let_parts.2.2.2.1 p hp).symm

theorem hL : ∀ l < C.nl, Good 22880 (tab 22880 (els.getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  interval_cases l
  · exact good_sg (i := 0) (by norm_num)
  · exact good_sg (i := 1) (by norm_num)
  · exact good_sg (i := 2) (by norm_num)
  · exact good_sg (i := 3) (by norm_num)
  · exact good_tab_inv (good_sg (i := 3) (by norm_num)) let_parts.2.2.2.2
  · exact good_hh
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl

end Letters

section Sylow


theorem hsep : ∀ g : ↥suzP, (∀ p ∈ D.sep, act 22880 g p = p) → g = 1 := by
  rw [facts.2.2.2.2.1]
  exact sep0

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k := by
  have hS : ∀ l < (els.take C.ns).length,
      Good 22880 (tab 22880 ((els.take C.ns).getD l 1)).toArray (L l) := by
    intro l hl
    have hl' : l < 5 := by simpa [els, C] using hl
    interval_cases l
    · exact hL 0 (by decide)
    · exact hL 1 (by decide)
    · exact hL 2 (by decide)
    · exact hL 3 (by decide)
    · exact hL 4 (by decide)
  have hlen : (els.take C.ns).length = 5 := rfl
  have h := card_closure_of_omC (els.take C.ns) L hS (x0 := [0, 1, 2, 3, 4, 5]) (by decide) sep0
    (by rw [hlen]; exact facts.2.2.2.2.2.1)
  rw [h, facts.2.2.2.2.2.2]
  rfl

end Sylow

end CFSG.QuasithinUnique.Ch1.SporLat.SuzK

end

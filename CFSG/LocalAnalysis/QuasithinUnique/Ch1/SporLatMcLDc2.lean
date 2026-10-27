module

public import Certificates.Certificate10504
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatSeq
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import CFSG.Sporadic.Schreier.PairMcLOrder
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.McLK

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.Schreier CFSG.KC.E64F
open CFSG.KD.McLDc2 (L C D shapeOK letOK wOK sbOK)

@[expose] noncomputable def ga : ↥mclP := ⟨mclGen 0, mclGen_mem_P 0 (by norm_num)⟩

@[expose] noncomputable def gb : ↥mclP := ⟨mclGen 1, mclGen_mem_P 1 (by norm_num)⟩

@[expose] noncomputable def E0 : Array ↥mclP := #[1, 1, 1, 1, 1, ga, gb]

@[expose] noncomputable def hh (i : ℕ) : ↥mclP := evalElt E0 (CFSG.KD.McLDc2.LT.hw.getD i [])

@[expose] noncomputable def E1 : Array ↥mclP := #[1, 1, 1, 1, hh 0, 1, 1, hh 1]

@[expose] noncomputable def sg (i : ℕ) : ↥mclP := evalElt E1 (CFSG.KD.McLDc2.LT.sgw.getD i [])

@[expose] noncomputable def els : List ↥mclP := [sg 0, sg 1, sg 2, (sg 1)⁻¹, hh 0, ga, gb, hh 1]

theorem good_congr' {t : Array ℕ} {f g : ℕ → ℕ} (h : Good 275 t f) (e : ∀ p < 275, f p = g p) :
    Good 275 t g :=
  ⟨h.1, fun p hp => by rw [← e p hp]; exact h.2 p hp⟩

theorem hodd : ¬ 2 ∣ C.N1 * C.N2 := by
  change ¬ 2 ∣ 22275 * 315
  decide

section Order


theorem sep0 : ∀ g : ↥mclP, (∀ p ∈ [0, 1, 2, 3, 4], act 275 g p = p) → g = 1 := by
  intro g hg
  have hmem : (g : Equiv.Perm (Fin 275)) ∈ mclChain.originalSubgroup := by
    rw [← mclP_eq_original]
    exact g.2
  have h1 := mcl_baseFaithful _ hmem fun x hx => by
    have e := hg x.val hx
    rw [act_eq, Subgroup.smul_def, Equiv.Perm.smul_def] at e
    exact Fin.ext e
  exact Subtype.ext h1

theorem hN : Nat.card ↥mclP = C.N1 * C.N2 * 2 ^ C.k := by
  change Nat.card ↥mclP = 22275 * 315 * 2 ^ 7
  rw [card_mclP]
  norm_num

end Order

section Facts


theorem facts : CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 275, (mclStrongArrs[l]!)[p]! = L (Nat.add 5 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 3, 4] ∧ sbOK = true ∧
    CFSG.KD.McLDc2.SB.C.flatten.length = 128 :=
  Certificates.certificate10504

theorem shape_parts : (∀ i < 2, ∀ l ∈ CFSG.KD.McLDc2.LT.hw.getD i [], l = 5 ∨ l = 6) ∧
    ∀ i < 3, ∀ l ∈ CFSG.KD.McLDc2.LT.sgw.getD i [], l = 4 ∨ l = 7 := by
  have h := facts.2.2.1
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := Nat.eq_of_beq_eq_true h1
  have e3 := Nat.eq_of_beq_eq_true h3
  refine ⟨fun i hi l hl => ?_, fun i hi l hl => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)] at hl
    rcases h2 _ (List.getElem_mem _) l hl with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (Nat.eq_of_beq_eq_true e)
  · rw [List.getD_eq_getElem _ _ (by omega)] at hl
    rcases h4 _ (List.getElem_mem _) l hl with e | e
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
    · exact Or.inr (Nat.eq_of_beq_eq_true e)

theorem let_parts : (∀ p < 275, L 4 p = wordF L (CFSG.KD.McLDc2.LT.hw.getD 0 []) p) ∧
    (∀ p < 275, L 7 p = wordF L (CFSG.KD.McLDc2.LT.hw.getD 1 []) p) ∧
    (∀ i < 3, ∀ p < 275, L i p = wordF L (CFSG.KD.McLDc2.LT.sgw.getD i []) p) ∧
    ∀ p < 275, L 3 (L 1 p) = p := by
  have h := facts.2.2.2.1
  unfold letOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h4, h7⟩, h0⟩, h1⟩, h2⟩, hi⟩ := h
  have wk : ∀ {l : ℕ} {w : List ℕ}, wOK l w = true → ∀ p < 275, L l p = wordF L w p :=
    fun {l w} hw p hp => by
      unfold wOK at hw
      exact Nat.eq_of_beq_eq_true (CFSG.KC.SLOm.all_range hw p hp)
  refine ⟨wk h4, wk h7, fun i hi p hp => ?_, fun p hp => ?_⟩
  · interval_cases i
    · exact wk h0 p hp
    · exact wk h1 p hp
    · exact wk h2 p hp
  · exact Nat.eq_of_beq_eq_true (CFSG.KC.SLOm.all_range hi p hp)

end Facts

section Letters


theorem good_gen {l : ℕ} (hl : l < 2) {g : ↥mclP} (hg : (g : Equiv.Perm (Fin 275)) = mclGen l) :
    Good 275 (tab 275 g).toArray (L (Nat.add 5 l)) := by
  have hr : ∀ p (hp : p < 275), (mclStrongArrs[l]!)[p]! = ((mclStrongPerm l) ⟨p, hp⟩ : ℕ) :=
    fun p hp => rep_mclStrongPerm (by omega) ⟨p, hp⟩
  have ha : ∀ p (hp : p < 275), act 275 g p = ((mclStrongPerm l) ⟨p, hp⟩ : ℕ) := by
    intro p hp
    have e := act_eq g ⟨p, hp⟩
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, hg] at e
    exact e
  refine ⟨tabA_size g, fun p hp => ⟨?_, ?_⟩⟩
  · rw [tabA_getD, ha p hp, ← hr p hp, facts.2.1 l hl p hp]
  · rw [← facts.2.1 l hl p hp, hr p hp]
    exact Fin.isLt _

theorem good_E0 {l : ℕ} (hl : l = 5 ∨ l = 6) : Good 275 (tab 275 (E0.getD l 1)).toArray (L l) := by
  rcases hl with rfl | rfl
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl

theorem good_hh0 : Good 275 (tab 275 (hh 0)).toArray (L 4) :=
  good_congr' (good_evalElt E0 L fun l hl => good_E0 (shape_parts.1 0 (by norm_num) l hl))
    fun p hp => (let_parts.1 p hp).symm

theorem good_hh1 : Good 275 (tab 275 (hh 1)).toArray (L 7) :=
  good_congr' (good_evalElt E0 L fun l hl => good_E0 (shape_parts.1 1 (by norm_num) l hl))
    fun p hp => (let_parts.2.1 p hp).symm

theorem good_E1 {l : ℕ} (hl : l = 4 ∨ l = 7) : Good 275 (tab 275 (E1.getD l 1)).toArray (L l) := by
  rcases hl with rfl | rfl
  · exact good_hh0
  · exact good_hh1

theorem good_sg {i : ℕ} (hi : i < 3) : Good 275 (tab 275 (sg i)).toArray (L i) :=
  good_congr' (good_evalElt E1 L fun l hl => good_E1 (shape_parts.2 i hi l hl))
    fun p hp => (let_parts.2.2.1 i hi p hp).symm

theorem hL : ∀ l < C.nl, Good 275 (tab 275 (els.getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  interval_cases l
  · exact good_sg (i := 0) (by norm_num)
  · exact good_sg (i := 1) (by norm_num)
  · exact good_sg (i := 2) (by norm_num)
  · exact good_tab_inv (good_sg (i := 1) (by norm_num)) let_parts.2.2.2
  · exact good_hh0
  · exact good_gen (l := 0) (by norm_num) rfl
  · exact good_gen (l := 1) (by norm_num) rfl
  · exact good_hh1

end Letters

section Sylow


theorem hsep : ∀ g : ↥mclP, (∀ p ∈ D.sep, act 275 g p = p) → g = 1 := by
  rw [facts.2.2.2.2.1]
  exact sep0

theorem card_S : Nat.card (Subgroup.closure {x | x ∈ els.take C.ns}) = 2 ^ C.k := by
  have hS : ∀ l < (els.take C.ns).length,
      Good 275 (tab 275 ((els.take C.ns).getD l 1)).toArray (L l) := by
    intro l hl
    have hl' : l < 4 := by simpa [els, C] using hl
    interval_cases l
    · exact hL 0 (by decide)
    · exact hL 1 (by decide)
    · exact hL 2 (by decide)
    · exact hL 3 (by decide)
  have hlen : (els.take C.ns).length = 4 := rfl
  have h := card_closure_of_omC (els.take C.ns) L hS (x0 := [0, 1, 2, 3, 4]) (by decide) sep0
    (by rw [hlen]; exact facts.2.2.2.2.2.1)
  rw [h, facts.2.2.2.2.2.2]
  rfl

end Sylow

end CFSG.QuasithinUnique.Ch1.SporLat.McLK

end

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bE16
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bVA

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

private def extWordA : List ℕ := [2, 3, 2, 0, 3, 1, 1]
private def extWordB : List ℕ := [0, 1, 1, 3, 2, 0, 3, 1, 1, 3, 2]

private def extGen (k : ℕ) : Ah :=
  if k = 0 then ⟨wordAP extWordA, wordAP_mem _⟩
  else ⟨wordAP extWordB, wordAP_mem _⟩

private def extGenL (k : ℕ) : PL := evalAL (if k = 0 then extWordA else extWordB)

private def extProd (w : List ℕ) : Ah := (w.map extGen).prod
private def extEval (w : List ℕ) : PL := w.foldr (fun k acc => comp (extGenL k) acc) idL
private def extWords : List (List ℕ) := [[], [0], [1], [0, 0], [0, 1], [1, 0], [0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0], [1, 0, 1], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [0, 1, 0, 1], [1, 0, 0, 0], [1, 0, 0, 1], [1, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [1, 0, 0, 0, 0], [1, 0, 0, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1], [1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 0, 1], [1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 0, 1], [1, 0, 1, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]]
private def extLists (_ : Unit := ()) : List PL := extWords.map extEval
private def extComplement (_ : Unit := ()) : Subgroup Ah :=
  Subgroup.closure ({extGen 0, extGen 1} : Set Ah)

private theorem rep_extGen (k : ℕ) : RepL (extGenL k) ((extGen k : Ah) : P45) := by
  unfold extGen extGenL
  split_ifs <;> exact repL_wordAP _

private theorem rep_extProd (w : List ℕ) : RepL (extEval w) ((extProd w : Ah) : P45) := by
  induction w with
  | nil => exact repL_one 45
  | cons k w ih => exact repL_mul (rep_extGen k) ih

private theorem extChecks :
    idL ∈ extLists ∧
    (∀ l ∈ extLists, comp l (extGenL 0) ∈ extLists) ∧
    (∀ l ∈ extLists, comp l (extGenL 1) ∈ extLists) ∧
    (extLists ()).Nodup ∧ (extLists ()).length = 120 ∧
    (∀ l ∈ extLists, l ∈ Vl → l = idL) ∧
    sameSet (imgSet (extGenL 0) L0) L0 = true ∧
    sameSet (imgSet (extGenL 1) L0) L0 = true := by
  decide +kernel

private theorem mem_extComplement_iff (g : Ah) :
    g ∈ extComplement ↔ ∃ l ∈ extLists, RepL l (g : P45) := by
  constructor
  · intro hg
    have key : ((extComplement () : Subgroup Ah) : Set Ah) ⊆
        {g : Ah | ∃ l ∈ extLists, RepL l (g : P45)} := by
      refine closure_subset_of_right_closed (S := ({extGen 0, extGen 1} : Set Ah)) ?_ ?_ ?_
      · intro s _
        obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
        exact ⟨n, hn, h⟩
      · exact ⟨idL, extChecks.1, repL_one 45⟩
      · rintro p ⟨l, hl, hp⟩ s (rfl | rfl)
        · exact ⟨comp l (extGenL 0), extChecks.2.1 l hl, repL_mul hp (rep_extGen 0)⟩
        · exact ⟨comp l (extGenL 1), extChecks.2.2.1 l hl, repL_mul hp (rep_extGen 1)⟩
    exact key hg
  · rintro ⟨l, hl, hrep⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
    have hwmem : extProd w ∈ extComplement := by
      apply Subgroup.list_prod_mem
      intro s hs
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hs
      apply Subgroup.subset_closure
      by_cases hk : k = 0
      · simp [extGen, hk]
      · right
        simp [extGen, hk]
    have heq : g = extProd w := Subtype.ext (eq_of_repL hrep (rep_extProd w))
    rwa [heq]

private theorem ext_card_VA :
    Nat.card VA = 16 := by
  have h1 := card_VA_ge
  have h2 := card_le_length_of_reps VA (F := Vl) fun s hs => (mem_VA_iff s).mp hs
  rw [Vl_length] at h2
  omega

theorem exists_complement_P2h :
    ∃ A : Subgroup Ah, A ≤ P2h ∧ A ⊓ VA = ⊥ ∧ VA ⊔ A = P2h := by
  have hAP : extComplement () ≤ P2h := by
    rw [extComplement, Subgroup.closure_le]
    rintro s (rfl | rfl)
    · exact mem_P2h_of_repL (rep_extGen 0) extChecks.2.2.2.2.2.2.1
    · exact mem_P2h_of_repL (rep_extGen 1) extChecks.2.2.2.2.2.2.2
  have hAV : extComplement () ⊓ VA = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    obtain ⟨l, hl, hrep⟩ := (mem_extComplement_iff g).mp hg.1
    obtain ⟨v, hv, hvrep⟩ := (mem_VA_iff g).mp hg.2
    have heq : l = v := repL_unique hrep hvrep
    have hid : l = idL := extChecks.2.2.2.2.2.1 l hl (heq ▸ hv)
    exact Subgroup.mem_bot.mpr (Subtype.ext (eq_of_repL hrep (hid ▸ repL_one 45)))
  have hcard : 120 ≤ Nat.card (extComplement ()) := by
    have h := length_le_card_of_nodup (extComplement ()) extChecks.2.2.2.1 (fun l hl => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hl
      refine ⟨extProd w, ?_, rep_extProd w⟩
      exact (mem_extComplement_iff _).mpr ⟨extEval w, List.mem_map.mpr ⟨w, hw, rfl⟩, rep_extProd w⟩)
    rwa [extChecks.2.2.2.2.1] at h
  have hnorm : extComplement () ≤ Subgroup.normalizer (VA : Set Ah) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff.mpr fun v => ⟨P2h_conj_VA (hAP hg), fun hv => by
      have := P2h_conj_VA (P2h.inv_mem (hAP hg)) hv
      simpa [mul_assoc] using this⟩
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [inf_comm VA, hAV, Subgroup.card_bot, mul_one, ext_card_VA] at hprod
  have hsup : VA ⊔ extComplement () = P2h := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le VA_le_P2h hAP)
    rw [card_P2h, hprod]
    omega
  exact ⟨extComplement (), hAP, hAV, hsup⟩

end CFSG.GH74.QTGen4.U42

module

public import CFSG.Certificates.Kernel.U62PairGrp
public import CFSG.Certificates.Kernel.U6Sound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Facts

public section

namespace CFSG.KC.U62P.Snd

open CFSG.Fischer Matrix CFSG.KC.F4M CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.F4M.Aux
open CFSG.ComponentClassification.RankTwoHypIICover.U62
open CFSG.Sporadic.Schreier (evalCodes)
open CFSG.F4.Native (tvGens uPts)
open CFSG.KC.U6 (decA)
open CFSG.LargeExtraspecial.SMod20.Aut (frob4 fieldPerm fvec)

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

@[expose] noncomputable def tvSUat (k : ℕ) : SU0 :=
  ⟨tvGL (vecOfCode tvGens[k]!) (tvGens_get_iso k), tvGL_mem_SU0 (tvGens_get_iso k)⟩


theorem t46G_eq (z : ℤ) : t46G z = piSU (tvSUat (z.natAbs - 1)) := rfl

theorem tvSUat_mul_self (k : ℕ) : tvSUat k * tvSUat k = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact tvM_mul_self (tvGens_get_iso k)

theorem piSU_tvSUat_inv (k : ℕ) : (piSU (tvSUat k))⁻¹ = piSU (tvSUat k) := by
  have h : (tvSUat k)⁻¹ = tvSUat k := inv_eq_of_mul_eq_one_right (tvSUat_mul_self k)
  rw [← map_inv, h]

theorem u62Let_getD (n : ℕ) (hn : n < 46) : u62Let.getD n 1 = t46G ((n : ℤ) + 1) := by
  have hl : n < u62Let.length := by simp [u62Let, hn]
  rw [List.getD_eq_getElem _ _ hl]
  simp [u62Let]


theorem evalCodes_u62Let : ∀ w : List ℤ, (∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ 46) →
    evalCodes u62Let w = (w.map fun z => piSU (tvSUat (z.natAbs - 1))).prod
  | [], _ => rfl
  | z :: w, h => by
    rw [evalCodes, List.map_cons, List.prod_cons,
      evalCodes_u62Let w (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    congr 1
    obtain ⟨h1, h2⟩ := h z (List.mem_cons_self ..)
    split_ifs with hz
    · rw [u62Let_getD _ (by omega)]
      have : (((z.toNat - 1 : ℕ) : ℤ) + 1) = z := by omega
      rw [this, t46G_eq]
    · rw [u62Let_getD _ (by omega)]
      have : ((((-z).toNat - 1 : ℕ) : ℤ) + 1) = -z := by omega
      rw [this, t46G_eq, Int.natAbs_neg, piSU_tvSUat_inv]


theorem u62SbWords_length : u62SbWords.length = 13 := rfl

theorem u62RWords_length : u62RWords.length = 43 := rfl

theorem u62SbG_length : u62SbG.length = 13 := by
  simp [u62SbG, u62SbWords_length]

theorem u62SbWords_letters : ∀ w ∈ u62SbWords, ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ 46 := by decide

theorem u62RWords_letters : ∀ w ∈ u62RWords, ∀ z ∈ w, 1 ≤ z ∧ z ≤ 13 := by decide

theorem hTV_get {TV : ℕ} (hTV : decA TV 12 46 = tvGens) {k : ℕ} (hk : k < 46) :
    fget TV k 12 = tvGens[k]! := by
  rw [← hTV]
  exact (CFSG.KC.U6.Snd.decA_get TV 12 46 k hk).symm

theorem RepSU_tvK_at {TV : ℕ} (hTV : decA TV 12 46 = tvGens) {k : ℕ} (hk : k < 46) :
    RepSU (tvK (fget TV k 12)) (tvSUat k) := by
  unfold RepSU
  rw [decM_tvK, hTV_get hTV hk]
  rfl


theorem getD_map_list {α β : Type*} (f : α → β) (l : List α) (k : ℕ) (hk : k < l.length) (d : α) :
    (l.map f).getD k (f d) = f (l.getD k d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]

theorem genRep {TV GV : ℕ} (hTV : decA TV 12 46 = tvGens)
    (hgen : ∀ k < 13, genAt TV GV (u62SbWords.map (List.map fun z => z.natAbs - 1)) k = true) :
    ∃ gen : ℕ → SU0, ∀ k < 13, RepSU (f72 GV k) (gen k) ∧ piSU (gen k) = u62SbG.getD k 1 := by
  refine ⟨fun k => (((u62SbWords.getD k []).map (fun z => z.natAbs - 1)).map tvSUat).prod, ?_⟩
  intro k hk
  have hk' : k < u62SbWords.length := by rw [u62SbWords_length]; exact hk
  have hmem : u62SbWords.getD k [] ∈ u62SbWords := by
    rw [List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  have hlet := u62SbWords_letters _ hmem
  have hSW : (u62SbWords.map (List.map fun z => z.natAbs - 1)).getD k [] =
      (u62SbWords.getD k []).map (fun z => z.natAbs - 1) :=
    getD_map_list (List.map fun z : ℤ => z.natAbs - 1) u62SbWords k hk' []
  constructor
  · have h := hgen k hk
    unfold genAt at h
    rw [Nat.beq_eq, hSW] at h
    rw [h]
    refine RepSU_wordK _ ?_
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact RepSU_tvK_at hTV (by have := hlet y hy; omega)
  · have e1 : u62SbG.getD k 1 = evalCodes u62Let (u62SbWords.getD k []) :=
      getD_map_list (evalCodes u62Let) u62SbWords k hk' []
    rw [e1, evalCodes_u62Let _ hlet, map_list_prod, List.map_map, List.map_map]
    rfl


theorem bAnd_eq_true {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem notB_eq_true {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

theorem evalCodes_u62SbG : ∀ w : List ℤ, (∀ z ∈ w, 1 ≤ z ∧ z ≤ 13) →
    evalCodes u62SbG w = (w.map fun z => u62SbG.getD (z.toNat - 1) 1).prod
  | [], _ => rfl
  | z :: w, h => by
    rw [evalCodes, List.map_cons, List.prod_cons,
      evalCodes_u62SbG w (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      if_pos (by have := (h z (List.mem_cons_self ..)).1; omega)]

theorem repRep {GV RV : ℕ} {gen : ℕ → SU0}
    (hg : ∀ k < 13, RepSU (f72 GV k) (gen k) ∧ piSU (gen k) = u62SbG.getD k 1)
    (hrep : ∀ j < 43, repAt GV RV (u62RWords.map (List.map fun z => z.natAbs - 1)) j = true) :
    ∀ j < 43, ∃ ρ : SU0, RepSU (f72 RV j) ρ ∧ piSU ρ = u62R j ∧
      isScal (mulK (f72 RV j) (f72 RV j)) = true ∧ isScal (f72 RV j) = false := by
  intro j hj
  have hj' : j < u62RWords.length := by rw [u62RWords_length]; exact hj
  have hmem : u62RWords.getD j [] ∈ u62RWords := by
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have hlet := u62RWords_letters _ hmem
  have hRW : (u62RWords.map (List.map fun z => z.natAbs - 1)).getD j [] =
      (u62RWords.getD j []).map (fun z => z.natAbs - 1) :=
    getD_map_list (List.map fun z : ℤ => z.natAbs - 1) u62RWords j hj' []
  have h := hrep j hj
  unfold repAt at h
  rw [strictB_eq, bAnd_eq_true, bAnd_eq_true, notB_eq_true, Nat.beq_eq, hRW] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(((u62RWords.getD j []).map (fun z => z.natAbs - 1)).map gen).prod, ?_, ?_, h2, h3⟩
  · rw [h1]
    refine RepSU_wordK _ ?_
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact (hg _ (by have := hlet y hy; omega)).1
  · rw [map_list_prod, List.map_map, u62R, evalCodes_u62SbG _ hlet, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y hy
    have := hlet y hy
    rw [Function.comp_apply, Function.comp_apply, (hg _ (by omega)).2]
    congr 1
    omega


theorem u62SbG_getD_mem {l : ℕ} (hl : l < 13) : u62SbG.getD l 1 ∈ u62Sb := by
  have hl' : l < u62SbG.length := by rw [u62SbG_length]; exact hl
  rw [List.getD_eq_getElem _ _ hl']
  exact Subgroup.subset_closure (List.getElem_mem hl')

theorem lstRep {GV LV PT LB : ℕ} {gen : ℕ → SU0}
    (hg : ∀ k < 13, RepSU (f72 GV k) (gen k) ∧ piSU (gen k) = u62SbG.getD k 1)
    (htree : ∀ i < 32768, treeAt GV LV PT LB i = true) :
    ∀ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ piSU ℓ ∈ u62Sb := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have h := htree i hi
    unfold treeAt at h
    by_cases h0 : i = 0
    · subst h0
      have h' : Nat.beq (f72 LV 0) ONE = true := h
      rw [Nat.beq_eq] at h'
      refine ⟨1, ?_, by rw [map_one]; exact one_mem _⟩
      unfold RepSU
      rw [h', decM_ONE]
      rfl
    · have hb : Nat.beq i 0 = false := by
        cases hh : Nat.beq i 0
        · rfl
        · rw [Nat.beq_eq] at hh
          exact absurd hh h0
      rw [hb] at h
      have h' : (strictB (f16 PT i) fun p => strictB (f8 LB i) fun l =>
          bAnd(Nat.blt p i, bAnd(Nat.blt l 13,
            Nat.beq (mulK (f72 LV p) (f72 GV l)) (f72 LV i)))) = true := h
      rw [strictB_eq, strictB_eq, bAnd_eq_true, bAnd_eq_true, Nat.blt_eq, Nat.blt_eq,
        Nat.beq_eq] at h'
      obtain ⟨hp, hl, he⟩ := h'
      obtain ⟨ℓp, hℓp, hmem⟩ := ih _ hp (by omega)
      refine ⟨ℓp * gen (f8 LB i), ?_, ?_⟩
      · rw [← he]
        exact RepSU_mul hℓp (hg _ hl).1
      · rw [map_mul, (hg _ hl).2]
        exact mul_mem hmem (u62SbG_getD_mem hl)

theorem sortAt_spec {LV SO n i : ℕ} (h : sortAt LV SO n i = true) :
    f16 SO i < n ∧ (i + 1 < n → f16 SO (i + 1) < n ∧
      keyK (f72 LV (f16 SO i)) < keyK (f72 LV (f16 SO (i + 1)))) := by
  unfold sortAt at h
  rw [strictB_eq, bAnd_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun hi => ?_⟩
  have hb : Nat.blt (Nat.succ i) n = true := by rw [Nat.blt_eq]; exact hi
  rw [hb] at h2
  have h3 : (strictB (f16 SO (Nat.succ i)) fun b => bAnd(Nat.blt b n,
      Nat.blt (keyK (f72 LV (f16 SO i))) (keyK (f72 LV b)))) = true := h2
  rw [strictB_eq, bAnd_eq_true, Nat.blt_eq, Nat.blt_eq] at h3
  exact h3


theorem sbEnum {LV SO : ℕ} (hcard : Nat.card u62Sb = 32768)
    (hl : ∀ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ piSU ℓ ∈ u62Sb)
    (hsort : ∀ i < 32768, sortAt LV SO 32768 i = true) :
    ∀ s ∈ u62Sb, ∃ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ s = piSU ℓ := by
  choose! ℓ hℓ using hl
  have hSO : ∀ i < 32768, f16 SO i < 32768 := fun i hi => (sortAt_spec (hsort i hi)).1
  have hkey1 : ∀ i, i + 1 < 32768 →
      keyK (f72 LV (f16 SO i)) < keyK (f72 LV (f16 SO (i + 1))) := fun i hi =>
    (sortAt_spec (hsort i (by omega))).2 hi |>.2
  have hkey : ∀ i i', i < i' → i' < 32768 →
      keyK (f72 LV (f16 SO i)) < keyK (f72 LV (f16 SO i')) := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base => intro h; exact hkey1 i h
    | succ m hm ih =>
      intro hm2
      exact lt_trans (ih (by omega)) (hkey1 m hm2)
  let F : Fin 32768 → u62Sb := fun i =>
    ⟨piSU (ℓ (f16 SO i)), (hℓ _ (hSO _ i.2)).2⟩
  have hinj : Function.Injective F := by
    intro i i' h
    have h1 : piSU (ℓ (f16 SO i)) = piSU (ℓ (f16 SO i')) := congrArg Subtype.val h
    have h2 := keyK_class (f72_lt _ _) (f72_lt _ _)
      ((piSU_eq_iff (hℓ _ (hSO _ i.2)).1 (hℓ _ (hSO _ i'.2)).1).1 h1)
    apply Fin.ext
    rcases lt_trichotomy i.1 i'.1 with hlt | heq | hgt
    · exact absurd h2 (ne_of_lt (hkey _ _ hlt i'.2))
    · exact heq
    · exact absurd h2.symm (ne_of_lt (hkey _ _ hgt i.2))
  have hcard' : Nat.card u62Sb ≤ Nat.card (Fin 32768) := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro s hs
  obtain ⟨⟨i, hi⟩, hF⟩ := (hinj.bijective_of_nat_card_le hcard').2 ⟨s, hs⟩
  refine ⟨f16 SO i, hSO i hi, ℓ (f16 SO i), (hℓ _ (hSO _ hi)).1, ?_⟩
  exact (congrArg Subtype.val hF).symm


theorem allN_eq_true {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (allN n f) = true ↔ _
    rw [CFSG.KC.U6.Snd.andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

theorem anyN_eq_true {n : ℕ} {f : ℕ → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => Bool.noConfusion h, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    change CFSG.KLie.CT.orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem vecOfCode_UP {UP : ℕ} (hUP : decA UP 12 693 = uPts) {p : ℕ} (hp : p < 693) :
    vecOfCode (fget UP p 12) = uVec p := by
  have h : fget UP p 12 = uPts[p]! := by
    rw [← hUP]
    exact (CFSG.KC.U6.Snd.decA_get UP 12 693 p hp).symm
  rw [h]
  unfold uVec
  rfl

theorem UP_lt {UP : ℕ} (p : ℕ) : fget UP p 12 < 2 ^ 12 := by
  rw [CFSG.KC.U6.Snd.fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 12)


theorem vecOfCode_barV_UP {UP : ℕ} (hUP : decA UP 12 693 = uPts) {p : ℕ} (hp : p < 693) :
    vecOfCode (barV (fget UP p 12)) = fvec frob4 (uVec p) := by
  rw [vecOfCode_barV, vecOfCode_UP hUP hp]
  rfl

theorem phi_not_mem {UP LV XP NXP : ℕ}
    (hUP : decA UP 12 693 = uPts)
    (henum : ∀ s ∈ u62Sb, ∃ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ s = piSU ℓ)
    (hphi : ∀ i < 32768, phiAt LV UP XP NXP i = true) : fieldPerm frob4 ∉ u62Sb := by
  intro hmem
  obtain ⟨i, hi, ℓ, hℓ, hΦ⟩ := henum _ hmem
  have h := hphi i hi
  unfold phiAt at h
  rw [strictB_eq, anyN_eq_true] at h
  obtain ⟨k, -, hk⟩ := h
  rw [strictB_eq, strictB_eq, CFSG.KC.U6.Snd.andB_iff, CFSG.KC.U6.Snd.notB_iff, Nat.blt_eq] at hk
  obtain ⟨hp, hfalse⟩ := hk
  have hpt : piSU ℓ ⟨f16 XP k, hp⟩ = fieldPerm frob4 ⟨f16 XP k, hp⟩ := by rw [hΦ]
  obtain ⟨c, hc, hcv⟩ := (piSU_eq_phi_iff ℓ ⟨f16 XP k, hp⟩).1 hpt
  have htrue : eqV (mvK (f72 LV i) (fget UP (f16 XP k) 12)) (barV (fget UP (f16 XP k) 12)) = true := by
    apply eqV_complete (mvK_lt _ _) (barV_lt _)
    refine ⟨c, hc, ?_⟩
    rw [vecOfCode_mvK, vecOfCode_barV_UP hUP hp, vecOfCode_UP hUP hp, ← hℓ]
    exact hcv
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse


theorem mem_u62SbG {g : Equiv.Perm (Fin 693)} (hg : g ∈ u62SbG) :
    ∃ k < 13, g = u62SbG.getD k 1 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  have hk' : k < 13 := by rw [← u62SbG_length]; exact hk
  exact ⟨k, hk', by rw [List.getD_eq_getElem _ _ hk]⟩

theorem eqV_fix_iff {UP : ℕ} (hUP : decA UP 12 693 = uPts) {M : ℕ} {g : SU0} (hg : RepSU M g)
    (q : Fin 693) : eqV (mvK M (fget UP q 12)) (fget UP q 12) = true ↔ piSU g q = q := by
  rw [piSU_fix_iff]
  constructor
  · intro h
    obtain ⟨c, hc, hcv⟩ := eqV_sound h
    refine ⟨c, hc, ?_⟩
    rw [vecOfCode_mvK, vecOfCode_UP hUP q.2, ← hg] at hcv
    exact hcv
  · rintro ⟨c, hc, hcv⟩
    apply eqV_complete (mvK_lt _ _) (UP_lt _)
    refine ⟨c, hc, ?_⟩
    rw [vecOfCode_mvK, vecOfCode_UP hUP q.2, ← hg]
    exact hcv

theorem fixed_point_iff {GV UP : ℕ} {gen : ℕ → SU0} (hUP : decA UP 12 693 = uPts)
    (hg : ∀ k < 13, RepSU (f72 GV k) (gen k) ∧ piSU (gen k) = u62SbG.getD k 1)
    (hfix : ∀ q < 693, fixAt GV UP q = true) :
    ∀ q : Fin 693, (∀ g ∈ u62SbG, g q = q) ↔ q = 0 := by
  intro q
  have h := hfix q.1 q.2
  unfold fixAt at h
  rw [strictB_eq] at h
  have key : ∀ k < 13, eqV (mvK (f72 GV k) (fget UP q 12)) (fget UP q 12) = true ↔
      piSU (gen k) q = q := fun k hk => eqV_fix_iff hUP (hg k hk).1 q
  constructor
  · intro hall
    by_contra hq0
    have hq : Nat.beq q.1 0 = false := by
      cases hh : Nat.beq q.1 0
      · rfl
      · rw [Nat.beq_eq] at hh
        exact absurd (Fin.ext hh) hq0
    rw [hq] at h
    have h' : CFSG.KLie.CT.notB (allN 13 fun k => eqV (mvK (f72 GV k) (fget UP q 12)) (fget UP q 12)) = true := h
    rw [CFSG.KC.U6.Snd.notB_iff] at h'
    have : allN 13 (fun k => eqV (mvK (f72 GV k) (fget UP q 12)) (fget UP q 12)) = true := by
      rw [allN_eq_true]
      intro k hk
      rw [key k hk, (hg k hk).2]
      exact hall _ (by
        have hk' : k < u62SbG.length := by rw [u62SbG_length]; exact hk
        rw [List.getD_eq_getElem _ _ hk']
        exact List.getElem_mem hk')
    rw [this] at h'
    exact Bool.noConfusion h'
  · intro hq0 g hgmem
    subst hq0
    obtain ⟨k, hk, rfl⟩ := mem_u62SbG hgmem
    have hq : Nat.beq (0 : Fin 693).1 0 = true := rfl
    rw [hq] at h
    have h' : allN 13 (fun k => eqV (mvK (f72 GV k) (fget UP (0 : Fin 693) 12)) (fget UP (0 : Fin 693) 12)) = true := h
    rw [allN_eq_true] at h'
    rw [← (hg k hk).2]
    exact (key k hk).1 (h' k hk)


theorem norm_mem {GV LV NI : ℕ} {gen : ℕ → SU0}
    (hg : ∀ k < 13, RepSU (f72 GV k) (gen k) ∧ piSU (gen k) = u62SbG.getD k 1)
    (hl : ∀ i < 32768, ∃ ℓ : SU0, RepSU (f72 LV i) ℓ ∧ piSU ℓ ∈ u62Sb)
    (hnorm : ∀ k < 13, normAt GV LV NI 32768 k = true) :
    ∀ g ∈ u62SbG, fieldPerm frob4 * g * (fieldPerm frob4)⁻¹ ∈ u62Sb := by
  intro g hgm
  obtain ⟨k, hk, rfl⟩ := mem_u62SbG hgm
  have h := hnorm k hk
  unfold normAt at h
  rw [strictB_eq, bAnd_eq_true, Nat.blt_eq] at h
  obtain ⟨hi, he⟩ := h
  obtain ⟨ℓ, hℓ, hmem⟩ := hl _ hi
  rw [← (hg k hk).2, conj_frSU, piSU_eq_of_eqP (RepSU_barK (hg k hk).1) hℓ he]
  exact hmem

end CFSG.KC.U62P.Snd

end

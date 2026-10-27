module

public import Certificates.Data.Kernel.Census.PackedBase
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW

public section

namespace CFSG.KC.Census.Base

open Subgroup CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open scoped commutatorElement

variable {n : ℕ} {w h : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

@[expose] def wordPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (x : List ℕ) : Equiv.Perm (Fin n) :=
  (x.map ℓ).prod

structure Letters (n w h : ℕ) (L : ℕ → ℕ) (ℓ : ℕ → Equiv.Perm (Fin n)) : Prop where
  at_eq : ∀ k < 2 * h, ∀ p (hp : p < n), at' w (L k) p = (ℓ k ⟨p, hp⟩ : ℕ)
  inv_eq : ∀ k < h, ℓ (h + k) = (ℓ k)⁻¹

@[expose] def BaseOf (P : Subgroup (Equiv.Perm (Fin n))) (bs : List ℕ) : Prop :=
  (∀ b ∈ bs, b < n) ∧ ∀ g ∈ P, (∀ b (hb : b < n), b ∈ bs → g ⟨b, hb⟩ = ⟨b, hb⟩) → g = 1

@[expose] def WordOK (h : ℕ) (x : List ℕ) : Prop := ∀ k ∈ x, k < 2 * h

variable (H : Letters n w h L ℓ)
include H

omit H in
theorem lsw_eq (h k : ℕ) : lsw h k = if k < h then h + k else k - h := by
  unfold lsw
  by_cases hk : k < h
  · have hb : Nat.blt k h = true := Nat.blt_eq.mpr hk
    rw [if_pos hk, hb]
    rfl
  · have hb : Nat.blt k h = false := by
      cases h' : Nat.blt k h
      · rfl
      · exact absurd (Nat.blt_eq.mp h') hk
    rw [if_neg hk, hb]
    rfl

omit H in
theorem lsw_lt {k : ℕ} (hk : k < 2 * h) : lsw h k < 2 * h := by
  rw [lsw_eq]
  split_ifs <;> omega

theorem ℓ_lsw {k : ℕ} (hk : k < 2 * h) : ℓ (lsw h k) = (ℓ k)⁻¹ := by
  rw [lsw_eq]
  split_ifs with hkh
  · exact H.inv_eq k hkh
  · have e := H.inv_eq (k - h) (by omega)
    have e2 : h + (k - h) = k := by omega
    rw [e2] at e
    rw [e, inv_inv]

theorem wPt_eq : ∀ (x : List ℕ), WordOK h x → ∀ p (hp : p < n),
    wPt w L x p = (wordPerm ℓ x ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | k :: l, hx, p, hp => by
    have ih := wPt_eq l (fun j hj => hx j (List.mem_cons_of_mem _ hj)) p hp
    have hlt : (wordPerm ℓ l ⟨p, hp⟩ : ℕ) < n := (wordPerm ℓ l ⟨p, hp⟩).2
    change at' w (L k) (wPt w L l p) = _
    rw [ih, H.at_eq k (hx k List.mem_cons_self) _ hlt]
    simp [wordPerm, Equiv.Perm.mul_apply]

theorem wInvPt_eq : ∀ (x : List ℕ), WordOK h x → ∀ p (hp : p < n),
    wInvPt w h L x p = ((wordPerm ℓ x)⁻¹ ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => by simp [wInvPt, wordPerm]
  | k :: l, hx, p, hp => by
    have hk := hx k List.mem_cons_self
    have h1 := H.at_eq (lsw h k) (lsw_lt hk) p hp
    rw [ℓ_lsw H hk] at h1
    have hlt : ((ℓ k)⁻¹ ⟨p, hp⟩ : ℕ) < n := ((ℓ k)⁻¹ ⟨p, hp⟩).2
    change wInvPt w h L l (at' w (L (lsw h k)) p) = _
    rw [h1, wInvPt_eq l (fun j hj => hx j (List.mem_cons_of_mem _ hj)) _ hlt]
    simp [wordPerm, Equiv.Perm.mul_apply, mul_inv_rev]

theorem pcwPt_eq : ∀ (xw : List (List ℕ)), (∀ x ∈ xw, WordOK h x) → ∀ (m p : ℕ) (hp : p < n),
    pcwPt w L xw m p = (pcG (xw.map (wordPerm ℓ)) m ⟨p, hp⟩ : ℕ)
  | [], _, _, p, _ => rfl
  | x :: l, hx, m, p, hp => by
    have ih := pcwPt_eq l (fun y hy => hx y (List.mem_cons_of_mem _ hy)) (m / 2) p hp
    have hlt := (pcG (l.map (wordPerm ℓ)) (m / 2) ⟨p, hp⟩).2
    change (bif Nat.beq (Nat.mod m 2) 1 then wPt w L x (pcwPt w L l (Nat.div m 2) p)
      else pcwPt w L l (Nat.div m 2) p) = _
    rw [List.map_cons, pcG, Equiv.Perm.mul_apply]
    have e1 : Nat.div m 2 = m / 2 := rfl
    rw [e1, ih]
    by_cases hm : m % 2 = 1
    · have hb : Nat.beq (Nat.mod m 2) 1 = true := by
        change Nat.beq (m % 2) 1 = true
        rw [hm]
        rfl
      rw [hb, if_pos hm, cond_true, wPt_eq H x (hx x List.mem_cons_self) _ hlt]
    · have hb : Nat.beq (Nat.mod m 2) 1 = false := by
        change Nat.beq (m % 2) 1 = false
        cases h' : Nat.beq (m % 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hm
      rw [hb, if_neg hm, cond_false]
      rfl

theorem pcwInvPt_eq : ∀ (xw : List (List ℕ)), (∀ x ∈ xw, WordOK h x) → ∀ (m p : ℕ) (hp : p < n),
    pcwInvPt w h L xw m p = ((pcG (xw.map (wordPerm ℓ)) m)⁻¹ ⟨p, hp⟩ : ℕ)
  | [], _, _, p, _ => by simp [pcwInvPt, pcG]
  | x :: l, hx, m, p, hp => by
    have hxw := hx x List.mem_cons_self
    have hl : ∀ y ∈ l, WordOK h y := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    change pcwInvPt w h L l (Nat.div m 2)
      (bif Nat.beq (Nat.mod m 2) 1 then wInvPt w h L x p else p) = _
    rw [List.map_cons, pcG, mul_inv_rev, Equiv.Perm.mul_apply]
    have e1 : Nat.div m 2 = m / 2 := rfl
    by_cases hm : m % 2 = 1
    · have hb : Nat.beq (Nat.mod m 2) 1 = true := by
        change Nat.beq (m % 2) 1 = true
        rw [hm]
        rfl
      rw [hb, cond_true, if_pos hm, wInvPt_eq H x hxw p hp, e1,
        pcwInvPt_eq l hl _ _ ((wordPerm ℓ x)⁻¹ ⟨p, hp⟩).2]
    · have hb : Nat.beq (Nat.mod m 2) 1 = false := by
        change Nat.beq (m % 2) 1 = false
        cases h' : Nat.beq (m % 2) 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hm
      rw [hb, cond_false, if_neg hm, inv_one, Equiv.Perm.one_apply, e1, pcwInvPt_eq l hl _ _ hp]

omit H in
theorem iterPt_eq {f : ℕ → ℕ} {g : Equiv.Perm (Fin n)} (hf : ∀ p (hp : p < n), f p = (g ⟨p, hp⟩ : ℕ)) :
    ∀ k p (hp : p < n), iterPt f k p = ((g ^ k) ⟨p, hp⟩ : ℕ)
  | 0, p, _ => rfl
  | k + 1, p, hp => by
    change f (iterPt f k p) = _
    rw [iterPt_eq hf k p hp, hf _ ((g ^ k) ⟨p, hp⟩).2, pow_succ', Equiv.Perm.mul_apply]

theorem commPt_eq {c₁ c₂ : List ℕ} (h₁ : WordOK h c₁) (h₂ : WordOK h c₂) (p : ℕ) (hp : p < n) :
    commPt w h L c₁ c₂ p = (⁅wordPerm ℓ c₁, wordPerm ℓ c₂⁆ ⟨p, hp⟩ : ℕ) := by
  unfold commPt
  rw [wInvPt_eq H c₂ h₂ p hp, wInvPt_eq H c₁ h₁ _ (Fin.isLt _), wPt_eq H c₂ h₂ _ (Fin.isLt _),
    wPt_eq H c₁ h₁ _ (Fin.isLt _), commutatorElement_def]
  simp only [Equiv.Perm.mul_apply, Fin.eta]

@[expose] def FacOK (h : ℕ) (gs : List (ℕ × List ℕ × List ℕ)) : Prop :=
  ∀ f ∈ gs, WordOK h f.2.1 ∧ WordOK h f.2.2

@[expose] def gamPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (gs : List (ℕ × List ℕ × List ℕ)) :
    Equiv.Perm (Fin n) :=
  (gs.map fun f => ⁅wordPerm ℓ f.2.1, wordPerm ℓ f.2.2⁆).prod

theorem gamPt_eq : ∀ (gs : List (ℕ × List ℕ × List ℕ)), FacOK h gs → ∀ p (hp : p < n),
    gamPt w h L gs p = (gamPerm ℓ gs ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | f :: l, hg, p, hp => by
    have hf := hg f List.mem_cons_self
    change commPt w h L f.2.1 f.2.2 (gamPt w h L l p) = _
    rw [gamPt_eq l (fun f' hf' => hg f' (List.mem_cons_of_mem _ hf')) p hp,
      commPt_eq H hf.1 hf.2 _ (Fin.isLt _)]
    simp [gamPerm, Equiv.Perm.mul_apply]

theorem gamInvPt_eq : ∀ (gs : List (ℕ × List ℕ × List ℕ)), FacOK h gs → ∀ p (hp : p < n),
    gamInvPt w h L gs p = ((gamPerm ℓ gs)⁻¹ ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => by simp [gamInvPt, gamPerm]
  | f :: l, hg, p, hp => by
    have hf := hg f List.mem_cons_self
    change gamInvPt w h L l (commPt w h L f.2.2 f.2.1 p) = _
    rw [commPt_eq H hf.2 hf.1 p hp,
      gamInvPt_eq l (fun f' hf' => hg f' (List.mem_cons_of_mem _ hf')) _ (Fin.isLt _)]
    simp [gamPerm, Equiv.Perm.mul_apply, mul_inv_rev, commutatorElement_inv]

theorem wcPt_eq {xw : List (List ℕ)} (hx : ∀ x ∈ xw, WordOK h x) (me : ℕ)
    {gs : List (ℕ × List ℕ × List ℕ)} (hg : FacOK h gs) (p : ℕ) (hp : p < n) :
    wcPt w h L xw me gs p =
      (⁅pcG (xw.map (wordPerm ℓ)) me, gamPerm ℓ gs⁆ ⟨p, hp⟩ : ℕ) := by
  unfold wcPt
  rw [gamInvPt_eq H gs hg p hp, pcwInvPt_eq H xw hx me _ (Fin.isLt _),
    gamPt_eq H gs hg _ (Fin.isLt _), pcwPt_eq H xw hx me _ (Fin.isLt _), commutatorElement_def]
  simp only [Equiv.Perm.mul_apply, Fin.eta]

section BaseEq

variable {P : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

omit H in
theorem eq_of_base (hB : BaseOf P bs) {g g' : Equiv.Perm (Fin n)} (hg : g ∈ P) (hg' : g' ∈ P)
    (h : ∀ b (hb : b < n), b ∈ bs → (g ⟨b, hb⟩ : ℕ) = (g' ⟨b, hb⟩ : ℕ)) : g = g' := by
  have h1 := hB.2 (g'⁻¹ * g) (P.mul_mem (P.inv_mem hg') hg) fun b hb hbs => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h b hb hbs)
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem wordPerm_mem (hℓ : ∀ k < 2 * h, ℓ k ∈ P) {x : List ℕ} (hx : WordOK h x) :
    wordPerm ℓ x ∈ P :=
  P.list_prod_mem fun g hg => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
    exact hℓ k (hx k hk)

omit H in
theorem pcG_mem_of {l : List (Equiv.Perm (Fin n))} (hl : ∀ g ∈ l, g ∈ P) :
    ∀ m, pcG l m ∈ P := by
  intro m
  exact (closure_le P).2 (fun g hg => hl g hg) (pcG_mem l m)

theorem pcRel_of_pcRelB (hB : BaseOf P bs) (hℓ : ∀ k < 2 * h, ℓ k ∈ P) :
    ∀ (xw : List (List ℕ)) (rs : List ℕ) (cs : List (List ℕ)), (∀ x ∈ xw, WordOK h x) →
      pcRelB w L bs xw rs cs = true → PcRel (xw.map (wordPerm ℓ))
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, hc => by simp [pcRelB] at hc
  | _ :: _, _ :: _, [], _, hc => by simp [pcRelB] at hc
  | x :: l, r :: rs, cl :: cs, hx, hc => by
    unfold pcRelB at hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨⟨hlen, hsq⟩, hcj⟩, hrest⟩ := hc
    have hxw := hx x List.mem_cons_self
    have hl : ∀ y ∈ l, WordOK h y := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    have hxP := wordPerm_mem H hℓ hxw
    have hlP : ∀ g ∈ l.map (wordPerm ℓ), g ∈ P := fun g hg => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      exact wordPerm_mem H hℓ (hl y hy)
    refine ⟨⟨r, ?_⟩, fun g hg => ?_, pcRel_of_pcRelB hB hℓ l rs cs hl hrest⟩
    · refine eq_of_base hB (P.mul_mem hxP hxP) (pcG_mem_of hlP r) fun b hb hbs => ?_
      have e := Nat.eq_of_beq_eq_true (hsq b hbs)
      rw [wPt_eq H x hxw b hb, wPt_eq H x hxw _ (Fin.isLt _), pcwPt_eq H l hl r b hb] at e
      simpa [Equiv.Perm.mul_apply] using e
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hi' : i < cl.length := by
        have := Nat.eq_of_beq_eq_true hlen
        omega
      have hyc := hcj (l[i], cl[i]) (mem_zip_of_lt hi hi')
      refine ⟨cl[i], eq_of_base hB (P.mul_mem (wordPerm_mem H hℓ (hl _ hy)) hxP)
        (P.mul_mem hxP (pcG_mem_of hlP _)) fun b hb hbs => ?_⟩
      have e := Nat.eq_of_beq_eq_true (hyc b hbs)
      rw [wPt_eq H x hxw b hb, wPt_eq H _ (hl _ hy) _ (Fin.isLt _), pcwPt_eq H l hl _ b hb,
        wPt_eq H x hxw _ (Fin.isLt _)] at e
      simpa [Equiv.Perm.mul_apply] using e

theorem exists_order4_of_witB (hB : BaseOf P bs) (hℓ : ∀ k < 2 * h, ℓ k ∈ P)
    {xw : List (List ℕ)} (hx : ∀ x ∈ xw, WordOK h x) {me : ℕ}
    {gs : List (ℕ × List ℕ × List ℕ)} (hg : FacOK h gs) {k : ℕ}
    (hw : witB w h L bs xw me gs k = true) :
    ∃ y ∈ nE P (closure (insert (pcG (xw.map (wordPerm ℓ)) me)
      ((gs.map fun f => pcG (xw.map (wordPerm ℓ)) f.1).toFinset : Set (Equiv.Perm (Fin n))))),
      orderOf y = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := pcG (xw.map (wordPerm ℓ)) me
  set E := closure (insert e ((gs.map fun f => pcG (xw.map (wordPerm ℓ)) f.1).toFinset :
    Set (Equiv.Perm (Fin n))))
  have hxP : ∀ g ∈ xw.map (wordPerm ℓ), g ∈ P := fun g hg => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
    exact wordPerm_mem H hℓ (hx y hy)
  have hbn : ∀ b ∈ bs, b < n := hB.1
  unfold witB at hw
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨hfs, ⟨b₀, hb₀, hy2⟩⟩, hy4⟩ := hw
  have hfac : ∀ f ∈ gs, ⁅wordPerm ℓ f.2.1, wordPerm ℓ f.2.2⁆ ∈ gammaE P E := by
    intro f hf
    obtain ⟨⟨hmv, hc1⟩, hc2⟩ := hfs f hf
    obtain ⟨b, hb, hbm⟩ := hmv
    set t := pcG (xw.map (wordPerm ℓ)) f.1
    have htE : t ∈ E := subset_closure (Set.mem_insert_of_mem _ (by
      simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map]
      exact ⟨f, hf, rfl⟩))
    have ht1 : t ≠ 1 := by
      intro h1
      have e := pcwPt_eq H xw hx f.1 b (hbn b hb)
      have h1' : pcG (xw.map (wordPerm ℓ)) f.1 = 1 := h1
      rw [h1'] at e
      simp only [Equiv.Perm.one_apply] at e
      rw [e, Nat.beq_refl] at hbm
      exact Bool.noConfusion hbm
    have hcomm : ∀ c, WordOK h c → (∀ b ∈ bs, Nat.beq (wPt w L c (pcwPt w L xw f.1 b))
        (pcwPt w L xw f.1 (wPt w L c b)) = true) → wordPerm ℓ c ∈ P ⊓ centralizer {t} := by
      intro c hc hcb
      refine ⟨wordPerm_mem H hℓ hc, mem_centralizer_singleton_iff.2 ?_⟩
      refine eq_of_base hB (P.mul_mem (wordPerm_mem H hℓ hc) (pcG_mem_of hxP _))
        (P.mul_mem (pcG_mem_of hxP _) (wordPerm_mem H hℓ hc)) fun b hb hbs => ?_
      have e := Nat.eq_of_beq_eq_true (hcb b hbs)
      rw [pcwPt_eq H xw hx f.1 b hb, wPt_eq H c hc _ (Fin.isLt _), wPt_eq H c hc b hb,
        pcwPt_eq H xw hx f.1 _ (Fin.isLt _)] at e
      simpa [Equiv.Perm.mul_apply] using e
    have h1 := hcomm _ (hg f hf).1 hc1
    have h2 := hcomm _ (hg f hf).2 hc2
    have hmem : ⁅wordPerm ℓ f.2.1, wordPerm ℓ f.2.2⁆ ∈ centDer P t :=
      commutator_mem_commutator h1 h2
    exact (le_iSup₂_of_le t htE (le_iSup_of_le ht1 le_rfl) : centDer P t ≤ gammaE P E) hmem
  have hγ : gamPerm ℓ gs ∈ gammaE P E := (gammaE P E).list_prod_mem fun g hgm => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hgm
    exact hfac f hf
  have hγP : gamPerm ℓ gs ∈ P := P.list_prod_mem fun g hgm => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hgm
    exact P.mul_mem (P.mul_mem (P.mul_mem (wordPerm_mem H hℓ (hg f hf).1)
      (wordPerm_mem H hℓ (hg f hf).2)) (P.inv_mem (wordPerm_mem H hℓ (hg f hf).1)))
      (P.inv_mem (wordPerm_mem H hℓ (hg f hf).2))
  set x := ⁅e, gamPerm ℓ gs⁆
  have hxN : x ∈ nE P E := commutator_mem_commutator (subset_closure (Set.mem_insert _ _)) hγ
  have heP : e ∈ P := pcG_mem_of hxP me
  have hxPm : x ∈ P := by
    simp only [x, commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem heP hγP) (P.inv_mem heP)) (P.inv_mem hγP)
  have hit : ∀ p (hp : p < n), iterPt (wcPt w h L xw me gs) k p = ((x ^ k) ⟨p, hp⟩ : ℕ) :=
    iterPt_eq (wcPt_eq H hx me hg) k
  refine ⟨x ^ k, (nE P E).pow_mem hxN k, ?_⟩
  have hb0 := hbn b₀ hb₀
  have hy2' : ¬ (x ^ k) ^ 2 ^ 1 = 1 := by
    intro h1
    rw [hit b₀ hb0, hit _ (Fin.isLt _)] at hy2
    have e : (x ^ k) ((x ^ k) ⟨b₀, hb0⟩) = ⟨b₀, hb0⟩ := by
      rw [← Equiv.Perm.mul_apply, ← pow_two, ← pow_one 2, h1, Equiv.Perm.one_apply]
    simp only [Fin.eta, e, Nat.beq_refl] at hy2
    exact Bool.noConfusion hy2
  have hy4' : (x ^ k) ^ 2 ^ (1 + 1) = 1 := by
    refine hB.2 _ (P.pow_mem (P.pow_mem hxPm k) _) fun b hb hbs => Fin.ext ?_
    have e := Nat.eq_of_beq_eq_true (hy4 b hbs)
    rw [hit b hb, hit _ (Fin.isLt _), hit _ (Fin.isLt _), hit _ (Fin.isLt _)] at e
    simpa [Fin.eta, pow_succ, Equiv.Perm.mul_apply] using e
  have := orderOf_eq_prime_pow hy2' hy4'
  rw [this]
  norm_num

end BaseEq

end CFSG.KC.Census.Base

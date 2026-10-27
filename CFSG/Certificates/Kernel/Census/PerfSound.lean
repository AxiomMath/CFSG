module

public import Certificates.Data.Kernel.Census.PackedRootR
public import CFSG.Certificates.Kernel.Census.BaseSound

public section

namespace CFSG.KC.Census.Base

open Subgroup CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open scoped commutatorElement

variable {n : ℕ} {w h : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

@[expose] def GenOK (h : ℕ) (pc : List (List ℕ × List ℕ)) : Prop :=
  ∀ t < pc.length, WordOK h (pc.getD t ([], [])).1 ∧ WordOK h (pc.getD t ([], [])).2

@[expose] def genPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (pc : List (List ℕ × List ℕ)) (t : ℕ) :
    Equiv.Perm (Fin n) :=
  if t < pc.length then
    ⁅wordPerm ℓ (pc.getD t ([], [])).1, wordPerm ℓ (pc.getD t ([], [])).2⁆
  else ⁅wordPerm ℓ (pc.getD (t - pc.length) ([], [])).2,
    wordPerm ℓ (pc.getD (t - pc.length) ([], [])).1⁆

@[expose] def gwPerm (ℓ : ℕ → Equiv.Perm (Fin n)) (pc : List (List ℕ × List ℕ)) (u : List ℕ) :
    Equiv.Perm (Fin n) :=
  (u.map (genPerm ℓ pc)).prod

@[expose] def GWordOK (r : ℕ) (u : List ℕ) : Prop := ∀ t ∈ u, t < 2 * r

variable (H : Letters n w h L ℓ)
include H

theorem gPt_eq {pc : List (List ℕ × List ℕ)} (hpc : GenOK h pc) {t : ℕ} (ht : t < 2 * pc.length)
    (p : ℕ) (hp : p < n) : gPt w h L pc t p = (genPerm ℓ pc t ⟨p, hp⟩ : ℕ) := by
  unfold gPt genPerm
  by_cases htr : t < pc.length
  · have hb : Nat.blt t pc.length = true := Nat.blt_eq.mpr htr
    rw [hb, cond_true, if_pos htr]
    exact commPt_eq H (hpc t htr).1 (hpc t htr).2 p hp
  · have hb : Nat.blt t pc.length = false := by
      cases h' : Nat.blt t pc.length
      · rfl
      · exact absurd (Nat.blt_eq.mp h') htr
    rw [hb, cond_false, if_neg htr]
    have e : Nat.sub t pc.length = t - pc.length := rfl
    rw [e]
    exact commPt_eq H (hpc _ (by omega)).2 (hpc _ (by omega)).1 p hp

omit H in
theorem genPerm_lsw (pc : List (List ℕ × List ℕ)) {t : ℕ} (ht : t < 2 * pc.length) :
    genPerm ℓ pc (lsw pc.length t) = (genPerm ℓ pc t)⁻¹ := by
  rw [lsw_eq]
  unfold genPerm
  split_ifs with h1 h2 h3
  · omega
  · rw [show pc.length + t - pc.length = t by omega, commutatorElement_inv]
  · rw [commutatorElement_inv]
  · omega

theorem gwPt_eq {pc : List (List ℕ × List ℕ)} (hpc : GenOK h pc) :
    ∀ (u : List ℕ), GWordOK pc.length u → ∀ p (hp : p < n),
      gwPt w h L pc u p = (gwPerm ℓ pc u ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | t :: l, hu, p, hp => by
    have ih := gwPt_eq hpc l (fun j hj => hu j (List.mem_cons_of_mem _ hj)) p hp
    change gPt w h L pc t (gwPt w h L pc l p) = _
    rw [ih, gPt_eq H hpc (hu t List.mem_cons_self) _ (Fin.isLt _)]
    simp [gwPerm, Equiv.Perm.mul_apply]

theorem gwInvPt_eq {pc : List (List ℕ × List ℕ)} (hpc : GenOK h pc) :
    ∀ (u : List ℕ), GWordOK pc.length u → ∀ p (hp : p < n),
      gwInvPt w h L pc u p = ((gwPerm ℓ pc u)⁻¹ ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => by simp [gwInvPt, gwPerm]
  | t :: l, hu, p, hp => by
    have ht := hu t List.mem_cons_self
    have h1 := gPt_eq H hpc (lsw_lt ht) p hp
    rw [genPerm_lsw pc ht] at h1
    change gwInvPt w h L pc l (gPt w h L pc (lsw pc.length t) p) = _
    rw [h1, gwInvPt_eq hpc l (fun j hj => hu j (List.mem_cons_of_mem _ hj)) _ (Fin.isLt _)]
    simp [gwPerm, Equiv.Perm.mul_apply, mul_inv_rev]

theorem cgPt_eq {pc : List (List ℕ × List ℕ)} (hpc : GenOK h pc) :
    ∀ (l : List (List ℕ × List ℕ)), (∀ uv ∈ l, GWordOK pc.length uv.1 ∧ GWordOK pc.length uv.2) →
      ∀ p (hp : p < n), cgPt w h L pc l p =
        ((l.map fun uv => ⁅gwPerm ℓ pc uv.1, gwPerm ℓ pc uv.2⁆).prod ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | uv :: l, hl, p, hp => by
    have huv := hl uv List.mem_cons_self
    have ih := cgPt_eq hpc l (fun x hx => hl x (List.mem_cons_of_mem _ hx)) p hp
    change gwPt w h L pc uv.1 (gwPt w h L pc uv.2
      (gwInvPt w h L pc uv.1 (gwInvPt w h L pc uv.2 (cgPt w h L pc l p)))) = _
    rw [ih, gwInvPt_eq H hpc _ huv.2 _ (Fin.isLt _), gwInvPt_eq H hpc _ huv.1 _ (Fin.isLt _),
      gwPt_eq H hpc _ huv.2 _ (Fin.isLt _), gwPt_eq H hpc _ huv.1 _ (Fin.isLt _)]
    simp [commutatorElement_def, Equiv.Perm.mul_apply]

theorem cjPt_eq {pc : List (List ℕ × List ℕ)} (hpc : GenOK h pc) {y : List ℕ}
    (hy : GWordOK pc.length y) :
    ∀ (l : List (List ℕ)), (∀ q ∈ l, GWordOK pc.length q) → ∀ p (hp : p < n),
      cjPt w h L pc y l p = ((l.map fun q => gwPerm ℓ pc q * gwPerm ℓ pc y ^ 2 *
        (gwPerm ℓ pc q)⁻¹).prod ⟨p, hp⟩ : ℕ)
  | [], _, p, _ => rfl
  | q :: l, hl, p, hp => by
    have hq := hl q List.mem_cons_self
    have ih := cjPt_eq hpc hy l (fun x hx => hl x (List.mem_cons_of_mem _ hx)) p hp
    change gwPt w h L pc q (gwPt w h L pc y (gwPt w h L pc y
      (gwInvPt w h L pc q (cjPt w h L pc y l p)))) = _
    rw [ih, gwInvPt_eq H hpc _ hq _ (Fin.isLt _), gwPt_eq H hpc _ hy _ (Fin.isLt _),
      gwPt_eq H hpc _ hy _ (Fin.isLt _), gwPt_eq H hpc _ hq _ (Fin.isLt _)]
    simp [sq, Equiv.Perm.mul_apply]

section BaseEq

variable {P : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

theorem pWitness_of_perfB (hB : BaseOf P bs) (hℓ : ∀ k < 2 * h, ℓ k ∈ P)
    {xw : List (List ℕ)} (hx : ∀ x ∈ xw, WordOK h x) {mx me : ℕ}
    {E : Subgroup (Equiv.Perm (Fin n))} (hxE : pcG (xw.map (wordPerm ℓ)) mx ∈ E)
    (hx1 : bs.any (fun b => !(Nat.beq (pcwPt w L xw mx b) b)) = true)
    (hmeE : pcG (xw.map (wordPerm ℓ)) me ∈ E)
    {pc : List (List ℕ × List ℕ)} {prel : List (List (List ℕ × List ℕ))} {py : List ℕ} {pk : ℕ}
    {pcj : List (List (List ℕ))} (hp : perfB w h L bs xw mx pc prel py pk pcj = true) {t : ℕ}
    (ht : t < pc.length)
    (hnc : bs.any (fun b => !(Nat.beq (pcwPt w L xw me (gPt w h L pc t b))
      (gPt w h L pc t (pcwPt w L xw me b)))) = true) :
    PWitness P E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbn : ∀ b ∈ bs, b < n := hB.1
  unfold perfB at hp
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hrl⟩, hjl⟩, hrw⟩, hyw⟩, hjw⟩, hrel⟩, hy⟩, hcj⟩ := hp
  have hxP : ∀ g ∈ xw.map (wordPerm ℓ), g ∈ P := fun g hg => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
    exact wordPerm_mem H hℓ (hx y hy)
  set X := pcG (xw.map (wordPerm ℓ)) mx with hXdef
  have hXP : X ∈ P := pcG_mem_of hxP mx
  have hcget : ∀ s < pc.length, pc.getD s ([], []) ∈ pc := fun s hs => by
    rw [List.getD_eq_getElem _ _ hs]
    exact List.getElem_mem hs
  have hpc : GenOK h pc := fun s hs => by
    have := hc _ (hcget s hs)
    exact ⟨fun k hk => Nat.blt_eq.mp (this.1.1.1 k hk),
      fun k hk => Nat.blt_eq.mp (this.1.1.2 k hk)⟩
  have hgw : ∀ u : List ℕ, (∀ t ∈ u, Nat.blt t (2 * pc.length) = true) →
      GWordOK pc.length u := fun u hu t ht => Nat.blt_eq.mp (hu t ht)
  have hX1 : X ≠ 1 := by
    intro h1
    obtain ⟨b, hb, hbm⟩ := List.any_eq_true.1 hx1
    have e := pcwPt_eq H xw hx mx b (hbn b hb)
    rw [← hXdef, h1, Equiv.Perm.one_apply] at e
    rw [e, Nat.beq_refl] at hbm
    exact Bool.noConfusion hbm
  have hcent : ∀ s < pc.length, wordPerm ℓ (pc.getD s ([], [])).1 ∈ P ⊓ centralizer {X} ∧
      wordPerm ℓ (pc.getD s ([], [])).2 ∈ P ⊓ centralizer {X} := by
    intro s hs
    have hcs := hc _ (hcget s hs)
    have key : ∀ c, WordOK h c → (∀ b ∈ bs, Nat.beq (wPt w L c (pcwPt w L xw mx b))
        (pcwPt w L xw mx (wPt w L c b)) = true) → wordPerm ℓ c ∈ P ⊓ centralizer {X} := by
      intro c hcw hcb
      refine ⟨wordPerm_mem H hℓ hcw, mem_centralizer_singleton_iff.2 ?_⟩
      refine eq_of_base hB (P.mul_mem (wordPerm_mem H hℓ hcw) hXP)
        (P.mul_mem hXP (wordPerm_mem H hℓ hcw)) fun b hb hbs => ?_
      have e := Nat.eq_of_beq_eq_true (hcb b hbs)
      rw [pcwPt_eq H xw hx mx b hb, wPt_eq H c hcw _ (Fin.isLt _), wPt_eq H c hcw b hb,
        pcwPt_eq H xw hx mx _ (Fin.isLt _)] at e
      simpa [Equiv.Perm.mul_apply] using e
    exact ⟨key _ (hpc s hs).1 hcs.1.2, key _ (hpc s hs).2 hcs.2⟩
  set Q := closure (Set.range fun s : Fin pc.length => genPerm ℓ pc s) with hQdef
  have hgenQ : ∀ s < 2 * pc.length, genPerm ℓ pc s ∈ Q := by
    intro s hs
    by_cases hsr : s < pc.length
    · exact subset_closure ⟨⟨s, hsr⟩, rfl⟩
    · have e : genPerm ℓ pc s = (genPerm ℓ pc (s - pc.length))⁻¹ := by
        have := genPerm_lsw (ℓ := ℓ) pc (t := s - pc.length) (by omega)
        rw [lsw_eq, if_pos (by omega), show pc.length + (s - pc.length) = s by omega] at this
        exact this
      rw [e]
      exact Q.inv_mem (subset_closure ⟨⟨s - pc.length, by omega⟩, rfl⟩)
  have hgwQ : ∀ u, GWordOK pc.length u → gwPerm ℓ pc u ∈ Q := fun u hu =>
    Q.list_prod_mem fun g hg => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact hgenQ s (hu s hs)
  have hgenP : ∀ s < 2 * pc.length, genPerm ℓ pc s ∈ P := by
    intro s hs
    unfold genPerm
    split_ifs with hsr
    · rw [commutatorElement_def]
      have h1 := (hcent s hsr).1.1
      have h2 := (hcent s hsr).2.1
      exact P.mul_mem (P.mul_mem (P.mul_mem h1 h2) (P.inv_mem h1)) (P.inv_mem h2)
    · rw [commutatorElement_def]
      have h1 := (hcent (s - pc.length) (by omega)).2.1
      have h2 := (hcent (s - pc.length) (by omega)).1.1
      exact P.mul_mem (P.mul_mem (P.mul_mem h1 h2) (P.inv_mem h1)) (P.inv_mem h2)
  have hQP : Q ≤ P := by
    rw [hQdef, closure_le]
    rintro _ ⟨s, rfl⟩
    exact hgenP s (by omega)
  have hgwP : ∀ u, GWordOK pc.length u → gwPerm ℓ pc u ∈ P := fun u hu => hQP (hgwQ u hu)
  have hgP : ∀ s, s < pc.length → genPerm ℓ pc s = ⁅wordPerm ℓ (pc.getD s ([], [])).1,
      wordPerm ℓ (pc.getD s ([], [])).2⁆ := fun s hs => by
    unfold genPerm
    rw [if_pos hs]
  refine ⟨Q, ?_, le_antisymm ?_ ?_, ?_, gwPerm ℓ pc py, hgwQ _ (hgw _ hyw), ?_, ?_⟩
  ·
    have hΓ : centDer P X ≤ gammaE P E := le_iSup₂_of_le X hxE (le_iSup_of_le hX1 le_rfl)
    rw [hQdef, closure_le]
    rintro _ ⟨s, rfl⟩
    dsimp only
    rw [hgP s s.2]
    exact hΓ (commutator_mem_commutator (hcent s s.2).1 (hcent s s.2).2)
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  ·
    rw [hQdef, closure_le]
    rintro _ ⟨s, rfl⟩
    dsimp only
    have hrs : ∀ uv ∈ prel.getD s [], GWordOK pc.length uv.1 ∧ GWordOK pc.length uv.2 := by
      intro uv huv
      have hmem : prel.getD s [] ∈ prel := by
        rw [List.getD_eq_getElem _ _ (by have := Nat.eq_of_beq_eq_true hrl; omega)]
        exact List.getElem_mem _
      have := hrw _ hmem uv huv
      exact ⟨hgw _ this.1, hgw _ this.2⟩
    have heq : genPerm ℓ pc s =
        ((prel.getD s []).map fun uv => ⁅gwPerm ℓ pc uv.1, gwPerm ℓ pc uv.2⁆).prod := by
      refine eq_of_base hB (hgenP s (by omega)) (P.list_prod_mem fun g hg => ?_) fun b hb hbs => ?_
      · obtain ⟨uv, huv, rfl⟩ := List.mem_map.1 hg
        rw [commutatorElement_def]
        have h1 := hgwP _ (hrs uv huv).1
        have h2 := hgwP _ (hrs uv huv).2
        exact P.mul_mem (P.mul_mem (P.mul_mem h1 h2) (P.inv_mem h1)) (P.inv_mem h2)
      · have e := Nat.eq_of_beq_eq_true (hrel s s.2 b hbs)
        rw [gPt_eq H hpc (by omega) b hb, cgPt_eq H hpc _ hrs b hb] at e
        exact e
    rw [SetLike.mem_coe, heq]
    exact Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨uv, huv, rfl⟩ := List.mem_map.1 hg
      exact commutator_mem_commutator (hgwQ _ (hrs uv huv).1) (hgwQ _ (hrs uv huv).2)
  ·
    intro hEC
    obtain ⟨b, hb, hbm⟩ := List.any_eq_true.1 hnc
    have hcomm := mem_centralizer_iff.mp (hEC hmeE) _ (hgenQ t (by omega))
    have hb' := hbn b hb
    have htt : t < 2 * pc.length := by omega
    have hL : pcwPt w L xw me (gPt w h L pc t b) =
        ((pcG (xw.map (wordPerm ℓ)) me) (genPerm ℓ pc t ⟨b, hb'⟩) : ℕ) := by
      rw [gPt_eq H hpc htt b hb', pcwPt_eq H xw hx me _ (Fin.isLt _)]
    have hR : gPt w h L pc t (pcwPt w L xw me b) =
        ((genPerm ℓ pc t) (pcG (xw.map (wordPerm ℓ)) me ⟨b, hb'⟩) : ℕ) := by
      rw [pcwPt_eq H xw hx me b hb', gPt_eq H hpc htt _ (Fin.isLt _)]
    have e : (pcG (xw.map (wordPerm ℓ)) me) (genPerm ℓ pc t ⟨b, hb'⟩) =
        genPerm ℓ pc t (pcG (xw.map (wordPerm ℓ)) me ⟨b, hb'⟩) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, hcomm]
    rw [hL, hR, e, Nat.beq_refl, Bool.not_true] at hbm
    exact Bool.noConfusion hbm
  ·
    have hpow : gwPerm ℓ pc py ^ 2 ^ pk = 1 := by
      refine hB.2 _ (P.pow_mem (hgwP _ (hgw _ hyw)) _) fun b hb hbs => Fin.ext ?_
      have e := Nat.eq_of_beq_eq_true (hy b hbs)
      rw [iterPt_eq (gwPt_eq H hpc _ (hgw _ hyw)) _ b hb] at e
      exact e
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  ·
    rw [hQdef, closure_le]
    rintro _ ⟨s, rfl⟩
    dsimp only
    have hqs : ∀ q ∈ pcj.getD s [], GWordOK pc.length q := by
      intro q hq
      have hmem : pcj.getD s [] ∈ pcj := by
        rw [List.getD_eq_getElem _ _ (by have := Nat.eq_of_beq_eq_true hjl; omega)]
        exact List.getElem_mem _
      exact hgw _ (hjw _ hmem q hq)
    have hyP := hgwP _ (hgw _ hyw)
    have heq : genPerm ℓ pc s = ((pcj.getD s []).map fun q => gwPerm ℓ pc q *
        gwPerm ℓ pc py ^ 2 * (gwPerm ℓ pc q)⁻¹).prod := by
      refine eq_of_base hB (hgenP s (by omega)) (P.list_prod_mem fun g hg => ?_) fun b hb hbs => ?_
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
        have h1 := hgwP _ (hqs q hq)
        exact P.mul_mem (P.mul_mem h1 (P.pow_mem hyP 2)) (P.inv_mem h1)
      · have e := Nat.eq_of_beq_eq_true (hcj s s.2 b hbs)
        rw [gPt_eq H hpc (by omega) b hb, cjPt_eq H hpc (hgw _ hyw) _ hqs b hb] at e
        exact e
    rw [SetLike.mem_coe, heq]
    exact Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
      exact subset_closure ⟨_, hgwQ _ (hqs q hq), rfl⟩

end BaseEq

end CFSG.KC.Census.Base

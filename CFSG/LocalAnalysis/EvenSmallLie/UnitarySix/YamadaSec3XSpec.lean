module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DTools
import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XFacts

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement
open CFSG.RankThree.Native.F2 (validA_of_rep)

@[expose] def pe : Equiv.Perm (Fin 693) := wP [4, 17]

@[expose] def pg : Equiv.Perm (Fin 693) := wP [16, 17, 16]

theorem rep_ae : Rep 693 ae pe := rep_wA tabs_check _ (by decide)

theorem rep_ag232 : Rep 693 ag232 pg := rep_wA tabs_check _ (by decide)

theorem rep_aj₀sq : Rep 693 aj₀sq (pj₀ * pj₀) := by
  have := rep_wA tabs_check [15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1] (by decide)
  rwa [show [15, 1, 15, 0, 1, 15, 1, 15, 1, 15, 0, 1, 15, 1] =
    [15, 1, 15, 0, 1, 15, 1] ++ [15, 1, 15, 0, 1, 15, 1] from rfl, wP_append] at this

theorem uA_valid : validA 693 ae = true ∧ validA 693 aj₀sq = true ∧ validA 693 ag232 = true ∧
    (∀ x ∈ chLam.O, validA 693 x = true) ∧ (∀ x ∈ chSig.O, validA 693 x = true) ∧
    (∀ x ∈ chA1.O, validA 693 x = true) ∧ (∀ x ∈ chX1.O, validA 693 x = true) ∧
    ∀ a ∈ nativeA, validA 693 a = true ∧ siftA 693 lvA2 chA2.B 0 a = true := by
  have h := uA_check
  unfold uACheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem valid_wA_of_O {c : ChainData} (h : ∀ x ∈ c.O, validA 693 x = true) {w : List ℕ}
    (hw : w ∈ c.gens) : validA 693 (wA w) = true :=
  all_O_spec (p := validA 693) (Array.all_eq_true'.2 h) w hw

theorem comm_of_eqA {a b : Array ℕ} {X Y : Equiv.Perm (Fin 693)} (hX : Rep 693 a X)
    (hY : Rep 693 b Y) : eqA 693 (compA 693 a b) (compA 693 b a) = true ↔ X * Y = Y * X :=
  eqA_iff (rep_compA hX hY) (rep_compA hY hX)

theorem rep_comm {a b : Array ℕ} {X Y : Equiv.Perm (Fin 693)} (ha : validA 693 a = true)
    (hb : validA 693 b = true) (hX : Rep 693 a X) (hY : Rep 693 b Y) :
    Rep 693 (commutatorA 693 a b) ⁅X, Y⁆ := by
  have h := rep_commutatorA ha hb
  rwa [permOfArr_eq_of_rep hX, permOfArr_eq_of_rep hY] at h

theorem all_O_of_forall {c : ChainData} {p : Array ℕ → Bool} (h : ∀ w ∈ c.gens, p (wA w) = true) :
    c.O.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < c.gens.length := by rwa [ChainData.O_size] at hi
  have e1 : c.O[i] = wA c.gens[i] := by simp [ChainData.O]
  rw [e1]
  exact h _ (List.getElem_mem hi')

theorem all_comm_iff {c : ChainData} (hc : c.GensOK) {a : Array ℕ} {X : Equiv.Perm (Fin 693)}
    (hX : Rep 693 a X) :
    (c.O.all fun s => eqA 693 (compA 693 a s) (compA 693 s a)) = true ↔
      ∀ w ∈ c.gens, X * wP w = wP w * X := by
  constructor
  · intro h w hw
    exact (comm_of_eqA hX (rep_wA_gens hc hw)).1
      (all_O_spec (p := fun s => eqA 693 (compA 693 a s) (compA 693 s a)) h w hw)
  · intro h
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < c.gens.length := by rwa [ChainData.O_size] at hi
    have e1 : c.O[i] = wA c.gens[i] := by simp [ChainData.O]
    rw [e1]
    exact (comm_of_eqA hX (rep_wA_gens hc (List.getElem_mem hi'))).2
      (h _ (List.getElem_mem hi'))

theorem all_conj_iff {c : ChainData} (hc : c.GensOK) {lv : Array Level}
    (hmem : ∀ {a : Array ℕ} {Y : Equiv.Perm (Fin 693)}, Rep 693 a Y →
      (Y ∈ c.grp ↔ siftA 693 lv c.B 0 a = true))
    {a : Array ℕ} {X : Equiv.Perm (Fin 693)} (ha : validA 693 a = true) (hX : Rep 693 a X)
    (h : (c.O.all fun s => siftA 693 lv c.B 0 (conjA 693 a s)) = true) :
    ∀ w ∈ c.gens, X * wP w * X⁻¹ ∈ c.grp := by
  intro w hw
  exact (hmem (rep_conj ha hX (rep_wA_gens hc hw))).2
    (all_O_spec (p := fun s => siftA 693 lv c.B 0 (conjA 693 a s)) h w hw)

theorem commFail_false {a s : Array ℕ} {X S : Equiv.Perm (Fin 693)} (hX : Rep 693 a X)
    (hS : Rep 693 s S) (hc : X * S = S * X) : commFail a s = false := by
  unfold commFail
  rw [List.any_eq_false]
  intro p hp
  have hp' : p < 693 := by
    simp only [commPts, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  have e := congrArg (fun g : Equiv.Perm (Fin 693) => (g ⟨p, hp'⟩ : ℕ)) hc
  simp only [Equiv.Perm.mul_apply] at e
  rw [hS.apply hp', hX.apply (S ⟨p, hp'⟩).2, hX.apply hp', hS.apply (X ⟨p, hp'⟩).2]
  simp [e]

theorem any_commFail_false {c : ChainData} (hc : c.GensOK) {a : Array ℕ}
    {X : Equiv.Perm (Fin 693)} (hX : Rep 693 a X) (h : ∀ w ∈ c.gens, X * wP w = wP w * X) :
    (c.O.any fun s => commFail a s) = false := by
  refine Bool.eq_false_iff.2 fun hany => ?_
  rw [Array.any_eq_true] at hany
  obtain ⟨i, hi, hf⟩ := hany
  have hi' : i < c.gens.length := by rwa [ChainData.O_size] at hi
  rw [O_getElem' c hi, commFail_false hX (rep_wA_gens hc (List.getElem_mem hi'))
    (h _ (List.getElem_mem hi'))] at hf
  exact Bool.false_ne_true hf

theorem zS_spec : ∀ a ∈ chA2.grp, (∀ w ∈ chS.gens, a * wP w = wP w * a) → a ∈ chZ.grp := by
  intro x hx
  obtain ⟨a, hX, h⟩ := zS_check x hx
  unfold zSAt commA at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  intro hc
  rcases h with h | h
  · rw [(all_comm_iff gensOK_chS hX).2 hc] at h
    exact absurd h (by decide)
  · exact (mem_chZ_iff hX).2 h

theorem zA3_spec : ∀ a ∈ chA3.grp, ((∀ w ∈ chA3.gens, a * wP w = wP w * a) → a ∈ chA4.grp) ∧
    (a * pe = pe * a → a ∈ chA4.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := zA3_check x hx
  unfold zA3At commA at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rcases h1 with h | h | h
    · rw [any_commFail_false gensOK_chA3 hX hc] at h
      exact absurd h (by decide)
    · rw [(all_comm_iff gensOK_chA3 hX).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chA4_iff hX).2 h
  · rcases h2 with h | h | h
    · rw [commFail_false hX rep_ae hc] at h
      exact absurd h (by decide)
    · rw [(comm_of_eqA hX rep_ae).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chA4_iff hX).2 h

theorem a1Gen_spec : (∀ w ∈ chA1.gens, wP w * wP w ∈ chZ.grp) ∧
    ∀ w ∈ chA1.gens, ∀ v ∈ chA1.gens, ⁅wP w, wP v⁆ ∈ chZ.grp := by
  have h := a1Gen_check
  unfold a1GenCheck at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun w hw => ?_, fun w hw v hv => ?_⟩
  · have hr := rep_wA_gens gensOK_chA1 hw
    exact (mem_chZ_iff (rep_compA hr hr)).2
      (all_O_spec (p := fun s => siftA 693 lvZ chZ.B 0 (compA 693 s s)) h.1 w hw)
  · have h2 := all_O_spec (p := fun s => chA1.O.all fun t =>
      siftA 693 lvZ chZ.B 0 (commutatorA 693 s t)) h.2 w hw
    exact (mem_chZ_iff (rep_comm (valid_wA_of_O uA_valid.2.2.2.2.2.1 hw)
      (valid_wA_of_O uA_valid.2.2.2.2.2.1 hv) (rep_wA_gens gensOK_chA1 hw)
      (rep_wA_gens gensOK_chA1 hv))).2
      (all_O_spec (p := fun t => siftA 693 lvZ chZ.B 0 (commutatorA 693 (wA w) t)) h2 v hv)

theorem mem_centralizer_grp {c : ChainData} {x : Equiv.Perm (Fin 693)}
    (h : ∀ w ∈ c.gens, x * wP w = wP w * x) :
    x ∈ centralizer (c.grp : Set (Equiv.Perm (Fin 693))) := by
  have := closure_le_centralizer (s := {x}) (t := {G | ∃ w ∈ c.gens, G = wP w}) (by
    rintro a rfl _ ⟨w, hw, rfl⟩
    exact h w hw)
  exact this (subset_closure rfl)

theorem xComm_spec :
    chA2.grp ≤ centralizer (chA2.grp : Set (Equiv.Perm (Fin 693))) ∧
    chA3.grp ≤ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    pe ∈ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    chSig.grp ≤ centralizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    chLam.grp ≤ centralizer (chSig.grp : Set (Equiv.Perm (Fin 693))) ∧
    chK1.grp ≤ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) ∧
    chS.grp ≤ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) ∧
    chA1.grp ≤ centralizer (chZ.grp : Set (Equiv.Perm (Fin 693))) := by
  have h := xComm_check
  unfold xCommCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have v : ∀ {c : ChainData}, c.GensOK → ∀ a ∈ c.gens, ∀ k ∈ a, k < 18 := fun hc a ha => hc a ha
  have v1 : ∀ a ∈ [[4, 17]], ∀ k ∈ a, k < 18 := by decide
  have vz : ∀ a ∈ [[14]], ∀ k ∈ a, k < 18 := by decide
  have ez : chZ.gens = [[14]] := rfl
  refine ⟨grp_le_centralizer (commCheck_spec h1 (v gensOK_chA2) (v gensOK_chA2)),
    grp_le_centralizer (commCheck_spec h2 (v gensOK_chA3) (v gensOK_chA4)),
    mem_centralizer_grp fun w hw => commCheck_spec h3 v1 (v gensOK_chA4) _ (by simp) w hw,
    grp_le_centralizer (commCheck_spec h4 (v gensOK_chSig) (v gensOK_chA4)),
    grp_le_centralizer (commCheck_spec h5 (v gensOK_chLam) (v gensOK_chSig)),
    grp_le_centralizer fun a ha b hb => ?_, grp_le_centralizer fun a ha b hb => ?_,
    grp_le_centralizer fun a ha b hb => ?_⟩
  · rw [ez] at hb
    exact commCheck_spec h6 (v gensOK_chK1) vz a ha b hb
  · rw [ez] at hb
    exact (commCheck_spec h7 (v gensOK_chS) vz a ha b hb)
  · rw [ez] at hb
    exact (commCheck_spec h8 (v gensOK_chA1) vz a ha b hb)

theorem a1_quot : ∀ a ∈ chA1.grp, a * a ∈ chZ.grp ∧ ∀ b ∈ chA1.grp, ⁅a, b⁆ ∈ chZ.grp := by
  have hcen : ∀ b ∈ chA1.grp, ∀ y ∈ chZ.grp, b * y * b⁻¹ = y := fun b hb y hy => by
    have := mem_centralizer_iff.1 (xComm_spec.2.2.2.2.2.2.2 hb) y hy
    rw [← this, mul_inv_cancel_right]
  have hgen : ∀ w ∈ chA1.gens, ∀ b ∈ chA1.grp, ⁅wP w, b⁆ ∈ chZ.grp := by
    intro w hw b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb' =>
      obtain ⟨v, hv, rfl⟩ := hb'
      exact a1Gen_spec.2 w hw v hv
    | one => rw [commutatorElement_one_right]; exact chZ.grp.one_mem
    | mul b1 b2 hb1 hb2 ih1 ih2 =>
      have e : ⁅wP w, b1 * b2⁆ = ⁅wP w, b1⁆ * (b1 * ⁅wP w, b2⁆ * b1⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e, hcen b1 hb1 _ ih2]
      exact chZ.grp.mul_mem ih1 ih2
    | inv b hb ih =>
      have e : ⁅wP w, b⁻¹⁆ = b⁻¹ * ⁅wP w, b⁆⁻¹ * b⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, hcen b⁻¹ (chA1.grp.inv_mem hb) _ (chZ.grp.inv_mem ih)]
      exact chZ.grp.inv_mem ih
  have hall : ∀ a ∈ chA1.grp, ∀ b ∈ chA1.grp, ⁅a, b⁆ ∈ chZ.grp := by
    intro a ha b hb
    induction ha using Subgroup.closure_induction with
    | mem a ha' =>
      obtain ⟨w, hw, rfl⟩ := ha'
      exact hgen w hw b hb
    | one => rw [commutatorElement_one_left]; exact chZ.grp.one_mem
    | mul a1 a2 ha1 ha2 ih1 ih2 =>
      have e : ⁅a1 * a2, b⁆ = a1 * ⁅a2, b⁆ * a1⁻¹ * ⁅a1, b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e, hcen a1 ha1 _ ih2]
      exact chZ.grp.mul_mem ih2 ih1
    | inv a ha ih =>
      have e : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, hcen a⁻¹ (chA1.grp.inv_mem ha) _ (chZ.grp.inv_mem ih)]
      exact chZ.grp.inv_mem ih
  intro a ha
  refine ⟨?_, fun b hb => hall a ha b hb⟩
  induction ha using Subgroup.closure_induction with
  | mem a ha' =>
    obtain ⟨w, hw, rfl⟩ := ha'
    exact a1Gen_spec.1 w hw
  | one => rw [mul_one]; exact chZ.grp.one_mem
  | mul a1 a2 ha1 ha2 ih1 ih2 =>
    have e : a1 * a2 * (a1 * a2) = a1 * a1 * ⁅a1⁻¹, a2⁆ * (a2 * a2) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact chZ.grp.mul_mem (chZ.grp.mul_mem ih1 (hall _ (chA1.grp.inv_mem ha1) _ ha2)) ih2
  | inv a ha ih =>
    rw [← mul_inv_rev]
    exact chZ.grp.inv_mem ih

theorem a1_spec : ∀ a ∈ chA1.grp, ((∀ w ∈ chA1.gens, a * wP w = wP w * a) → a ∈ chZ.grp) ∧
    a * a ∈ chZ.grp ∧ (∀ w ∈ chA1.gens, ⁅a, wP w⁆ ∈ chZ.grp) ∧
    (a * pe = pe * a → a ∈ chX1Z.grp) ∧
    ((∀ w ∈ chX6Z.gens, a * wP w = wP w * a) → a ∈ chA2.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := a1_check x hx
  unfold a1At commA at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h4⟩, h5⟩ := h
  refine ⟨fun hc => ?_, (a1_quot x hx).1, fun w hw => (a1_quot x hx).2 _ (wP_mem_grp hw),
    fun hc => ?_, fun hc => ?_⟩
  · rcases h1 with h | h
    · rw [(all_comm_iff gensOK_chA1 hX).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chZ_iff hX).2 h
  · rcases h4 with h | h
    · rw [(comm_of_eqA hX rep_ae).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chX1Z_iff hX).2 h
  · rcases h5 with h | h
    · rw [(all_comm_iff gensOK_chX6Z hX).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chA2_iff hX).2 h

theorem a2_spec : ∀ a ∈ chA2.grp, a ∈ chA1.grp → a ∈ chX6Z.grp := by
  intro x hx
  obtain ⟨a, hX, h⟩ := a2_check x hx
  unfold a2At at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  intro ha
  rcases h with h | h
  · rw [(mem_chA1_iff hX).1 ha] at h
    exact absurd h (by decide)
  · exact (mem_chX6Z_iff hX).2 h

theorem labA3_inv : ∀ y ∈ chA3.grp, ∀ p : Fin 693, labA3[(y p : ℕ)]! = labA3[(p : ℕ)]! := by
  have h := labA3_check
  unfold labA3Check at h
  simp only [Bool.and_eq_true] at h
  let H : Subgroup (Equiv.Perm (Fin 693)) :=
    { carrier := {y | ∀ p : Fin 693, labA3[(y p : ℕ)]! = labA3[(p : ℕ)]!}
      mul_mem' := fun {a b} ha hb p => by rw [Equiv.Perm.mul_apply, ha, hb]
      one_mem' := fun p => rfl
      inv_mem' := fun {a} ha p => by rw [← ha (a⁻¹ p), perm_apply_inv'] }
  have hle : chA3.grp ≤ H := grp_le fun w hw p => by
    have h3 := allLt_spec (all_O_spec h.2 w hw) p.2
    rw [beq_iff_eq, (rep_wA_gens gensOK_chA3 hw) p] at h3
    exact h3
  exact fun y hy => hle hy

theorem p2_spec : ∀ k ∈ chK1.grp, (∀ w ∈ chA3.gens, k * wP w * k⁻¹ ∈ chA3.grp) →
    k ∈ chP2.grp := by
  intro x hx hn
  obtain ⟨a, hX, h⟩ := p2_check x hx
  have hv := validA_of_rep hX
  unfold p2At at h
  have hT : (chA3.O.all fun s => labA3[a[s[2]!]!]! == labA3[a[2]!]!) = true :=
    all_O_of_forall fun w hw => by
      rw [beq_iff_eq, (rep_wA_gens gensOK_chA3 hw).apply (by norm_num), hX.apply (Fin.isLt _),
        hX.apply (by norm_num)]
      have := labA3_inv _ (hn w hw) (x 2)
      simp only [Equiv.Perm.mul_apply, perm_inv_apply'] at this
      simpa using this
  have hall : (chA3.O.all fun s => siftA 693 lvA3 chA3.B 0 (conjA 693 a s)) = true :=
    all_O_of_forall fun w hw =>
      (mem_chA3_iff (rep_conj hv hX (rep_wA_gens gensOK_chA3 hw))).1 (hn w hw)
  rw [hT, hall] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem_chP2_iff hX).2 h

theorem a4_spec : ∀ a ∈ chA4.grp, ((∀ w ∈ chX1.gens, a * wP w = wP w * a) → a ∈ chZ.grp) ∧
    (a ∈ chA1.grp → a ∈ chZ2S.grp) ∧ ⁅a, pj₀⁆ ∈ chX8.grp ∧ ⁅a, pj₀ * pj₀⁆ ∈ chX8.grp ∧
    ∀ y ∈ chX1.grp, y ≠ 1 → ⁅y, a⁆ ∈ chZ.grp → a ∈ chZ2S.grp := by
  intro x hx
  obtain ⟨a, hX, h⟩ := a4_check x hx
  have hv := validA_of_rep hX
  unfold a4At commA at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun hc => ?_, fun ha => ?_, ?_, ?_, ?_⟩
  · rcases h1 with h | h
    · rw [(all_comm_iff gensOK_chX1 hX).2 hc] at h
      exact absurd h (by decide)
    · exact (mem_chZ_iff hX).2 h
  · rcases h2 with h | h
    · rw [(mem_chA1_iff hX).1 ha] at h
      exact absurd h (by decide)
    · exact (mem_chZ2S_iff hX).2 h
  · exact (mem_chX8_iff (rep_comm hv valid_spec.2.2.2.1 hX rep_aj₀)).2 h3
  · exact (mem_chX8_iff (rep_comm hv uA_valid.2.1 hX rep_aj₀sq)).2 h4
  · intro y hy' hy hyz
    obtain ⟨b, a', hY, hX', h5j⟩ := a4Pair_check x hx y hy'
    unfold a4PairAt at h5j
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h5j
    rcases h5j with (h | h) | h
    · exact absurd (eq_one_of_eqA hY h) hy
    · rw [(mem_chZ_iff (rep_comm (validA_of_rep hY) (validA_of_rep hX') hY hX')).1 hyz] at h
      exact absurd h (by decide)
    · exact (mem_chZ2S_iff hX').2 h

theorem z2s_spec : ∀ b ∈ chZ2S.grp, (∀ y ∈ chX1.grp, ⁅y, b⁆ ∈ chZ.grp) ∧
    (gP 16 * b * (gP 16)⁻¹ ∈ chZ2S.grp → b ∈ chZ.grp) ∧
    (pg * b * pg⁻¹ ∈ chZ2S.grp → b ∈ chZ.grp) := by
  intro x hx
  obtain ⟨a, hX, h⟩ := z2s_check x hx
  unfold z2sAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h2, h3⟩ := h
  refine ⟨fun y hy => ?_, fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨b, a', hY, hX', h1⟩ := z2sPair_check x hx y hy
    unfold z2sPairAt at h1
    exact (mem_chZ_iff (rep_comm (validA_of_rep hY) (validA_of_rep hX') hY hX')).2 h1
  · rcases h2 with h | h
    · rw [(mem_chZ2S_iff (rep_conj (tabs_spec tabs_check (by norm_num : 16 < 18)).2
        (rep_gA tabs_check (by norm_num)) hX)).1 hc] at h
      exact absurd h (by decide)
    · exact (mem_chZ_iff hX).2 h
  · rcases h3 with h | h
    · rw [(mem_chZ2S_iff (rep_conj uA_valid.2.2.1 rep_ag232 hX)).1 hc] at h
      exact absurd h (by decide)
    · exact (mem_chZ_iff hX).2 h

theorem xNorm_spec : chLam.grp ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) ∧
    chLam.grp ≤ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ∧
    chSig.grp ≤ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ∧
    pe ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ∧
    pj₀ ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) := by
  have h := xNorm_check
  unfold xNormCheck at h
  simp only [Bool.and_eq_true, Array.all_append] at h
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := h
  have h4' : ∀ x ∈ #[ae, aj₀], (chA3.O.all fun a => siftA 693 lvA3 chA3.B 0 (conjA 693 x a)) =
      true := Array.all_eq_true'.1 h4
  have hA4 := fun {a : Array ℕ} {Y : Equiv.Perm (Fin 693)} (hY : Rep 693 a Y) => mem_chA4_iff hY
  have hA3 := fun {a : Array ℕ} {Y : Equiv.Perm (Fin 693)} (hY : Rep 693 a Y) => mem_chA3_iff hY
  refine ⟨grp_le fun w hw => mem_normalizer_grp (all_conj_iff gensOK_chA4 hA4
      (valid_wA_of_O uA_valid.2.2.2.1 hw) (rep_wA_gens gensOK_chLam hw)
      (all_O_spec (p := fun x => chA4.O.all fun a => siftA 693 lvA4 chA4.B 0 (conjA 693 x a))
        h1 w hw)),
    grp_le fun w hw => mem_normalizer_grp (all_conj_iff gensOK_chA3 hA3
      (valid_wA_of_O uA_valid.2.2.2.1 hw) (rep_wA_gens gensOK_chLam hw)
      (all_O_spec (p := fun x => chA3.O.all fun a => siftA 693 lvA3 chA3.B 0 (conjA 693 x a))
        h2 w hw)),
    grp_le fun w hw => mem_normalizer_grp (all_conj_iff gensOK_chA3 hA3
      (valid_wA_of_O uA_valid.2.2.2.2.1 hw) (rep_wA_gens gensOK_chSig hw)
      (all_O_spec (p := fun x => chA3.O.all fun a => siftA 693 lvA3 chA3.B 0 (conjA 693 x a))
        h3 w hw)),
    mem_normalizer_grp (all_conj_iff gensOK_chA3 hA3 uA_valid.1 rep_ae (h4' ae (by simp))),
    mem_normalizer_grp (all_conj_iff gensOK_chA3 hA3 valid_spec.2.2.2.1 rep_aj₀
      (h4' aj₀ (by simp)))⟩

theorem xFix_spec : (∀ p : Fin 693, (∀ w ∈ chA3.gens, wP w p = p) ↔ (p : ℕ) ∈ fixF) ∧
    ∀ p : Fin 693, (p : ℕ) ∈ fixF → ∃ q ∈ qF, wP q p = 0 := by
  have h := xFix_check
  unfold xFixCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun p => ?_, fun p hi => ?_⟩
  · have hp := allLt_spec h1 p.2
    simp only [beq_iff_eq] at hp
    rw [← List.elem_iff, List.elem_eq_contains, hp]
    constructor
    · intro hw
      exact all_O_of_forall fun w hw' => by
        have := (rep_wA_gens gensOK_chA3 hw').apply p.2
        simp only [beq_iff_eq]
        rw [this, hw w hw']
    · intro hall w hw
      have := all_O_spec (p := fun a => a[(p : ℕ)]! == (p : ℕ)) hall w hw
      simp only [beq_iff_eq] at this
      rw [(rep_wA_gens gensOK_chA3 hw).apply p.2] at this
      exact Fin.ext this
  · obtain ⟨j, hj, hjp⟩ := List.mem_iff_getElem.1 hi
    have hj5 : j < 5 := hj
    have hq := h2 j hj5
    have hok : ∀ k ∈ qF[j]!, k < 18 := by interval_cases j <;> decide
    have hmem : qF[j]! ∈ qF := by interval_cases j <;> decide
    refine ⟨qF[j]!, hmem, ?_⟩
    have e1 : fixF[j]! = (p : ℕ) := by rw [getElem!_pos fixF j hj, hjp]
    have := (rep_wA tabs_check _ hok) p
    rw [← e1, hq] at this
    exact Fin.ext this.symm

theorem xWit_spec : prodCheck cwW a4cData = true ∧ prodCheck cjW a4aData = true ∧
    prodCheck cjW a4zData = true ∧ prodCheck cwW a4jData = true ∧
    prodCheck cwW k1pData = true ∧ prodCheck cjW a1cData = true ∧
    prodCheck cjW a2cData = true ∧ prodCheck cwW a12cData = true ∧
    ∀ p ∈ a3eData, eqA 693 (wA [p.1]) (wA (cwW p.2.1 [4, 17] ++ p.2.2)) = true := by
  have h := xWit_check
  unfold xWitCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

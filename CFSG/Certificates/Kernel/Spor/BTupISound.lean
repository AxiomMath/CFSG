module

public import Certificates.Data.Kernel.Spor.BTupI
public import CFSG.Certificates.Kernel.Spor.BTupMSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btCntN_succ (n : Nat) (f : Nat → Bool) :
    btCntN (n + 1) f = if f n = true then btCntN n f + 1 else btCntN n f := by
  change strictN (btCntN n f) (fun a => nIf(f n, Nat.succ a, a)) = _
  rw [CFSG.KS.Raw.Orb.strictN_eq, CFSG.KS.Raw.Orb.nIf_eq]

theorem btCntN_eq (f : Nat → Bool) :
    ∀ n, btCntN n f = ((Finset.range n).filter (fun i => f i = true)).card := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [btCntN_succ, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · rw [Finset.card_insert_of_notMem (fun h => by simp at h)]
    · rfl

theorem not_beq_iff (a b : Nat) : Bool.not (Nat.beq a b) = true ↔ a ≠ b := by
  constructor
  · intro h e
    rw [Nat.beq_eq.mpr e] at h
    exact Bool.false_ne_true h
  · intro h
    cases e : Nat.beq a b
    · rfl
    · exact absurd (Nat.beq_eq.mp e) h

theorem btInvP_iff {k kw km cntL : Nat} {K R RT KL : Nat → Nat} {i : Nat} :
    btInvP k kw km cntL K R RT KL i = true ↔ btDep (btRec R i) ≠ 0 ∧
      btDep (btRec R (btMul k R RT i i)) = 0 ∧ ∀ p < cntL, btKey kw km K i ≠ btKey kw km KL p := by
  unfold btInvP
  rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.allN_iff, not_beq_iff, Nat.beq_eq]
  simp only [not_beq_iff]

theorem dep0_exists {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat}
    (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true) :
    ∀ D i, i < cnt → btDep (btRec R i) = D → ∃ i₀ < cnt, btDep (btRec R i₀) = 0 := by
  intro D
  induction D with
  | zero => exact fun i hi hD => ⟨i, hi, hD⟩
  | succ D ih =>
    intro i hi hD
    obtain ⟨hpar, -, hdep, -⟩ := (ptFacts (hp i hi)).tree (by omega)
    exact ih _ hpar (by omega)

section Inv

variable {n w d kw km k cnt base : Nat} {G K R POS S RT : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n}
  (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
  (hfix : ∀ h ∈ genSub n k gp, (∀ t, h (b t) = b t) → h = 1)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)

include hp hfix hb in
theorem dep0_iff (hw : 0 < w) (hc : btHdK cnt = true) {i : Nat} (hi : i < cnt)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ genSub n k gp)
    (he : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = x (b t)) :
    btDep (btRec R i) = 0 ↔ x = 1 := by
  constructor
  · intro h0
    refine hfix x hx fun t => Fin.ext ?_
    rw [← he t, (ptFacts (hp i hi)).root h0, hb t]
  · rintro rfl
    obtain ⟨i₀, hi₀, h0⟩ := dep0_exists hp _ 0 (Nat.blt_eq.mp hc) rfl
    have e : i = i₀ := btKey_inj hw hp hi hi₀ fun t => by
      rw [he t, (ptFacts (hp i₀ hi₀)).root h0, hb t]
      rfl
    rw [e]
    exact h0

variable (hS : ∀ j < k, ∀ t : Fin d, pg w (mask w) (btKey kw km K (S j)) t = gp j (b t))
  (hr : ∀ i < cnt, btRtK k k cnt S R POS RT i = true)
include hg hp hfix hb hS hr

theorem btInvP_iff_el {cntL : Nat} {KL : Nat → Nat} {L : Subgroup (Equiv.Perm (Fin n))}
    (hw : 0 < w) (hc : btHdK cnt = true)
    (hL : ∀ q < cntL, ∃ l ∈ L, ∀ t : Fin d, pg w (mask w) (btKey kw km KL q) t = l (b t))
    (hLcov : ∀ l ∈ L, l ∈ genSub n k gp →
      ∃ q < cntL, ∀ t : Fin d, pg w (mask w) (btKey kw km KL q) t = l (b t))
    (hLcan : ∀ q < cntL, btKey kw km KL q >>> (d * w) = 0)
    (hext : ∀ x ∈ genSub n k gp, ∀ l ∈ L, (∀ t, x (b t) = l (b t)) → x = l)
    {i : Nat} (hi : i < cnt) {x : Equiv.Perm (Fin n)} (hx : x ∈ genSub n k gp)
    (he : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = x (b t)) :
    btInvP k kw km cntL K R RT KL i = true ↔ x * x = 1 ∧ x ≠ 1 ∧ x ∉ L := by
  rw [btInvP_iff]
  obtain ⟨hm, km'⟩ := btMul_spec hg hp hfix hb hS hr hi hi hx he hx he
  have h1 := dep0_iff hp hfix hb hw hc hi hx he
  have h2 := dep0_iff hp hfix hb hw hc hm (Subgroup.mul_mem _ hx hx) km'
  have h3 : (∀ p < cntL, btKey kw km K i ≠ btKey kw km KL p) ↔ x ∉ L := by
    constructor
    · intro hne hxL
      obtain ⟨q, hq, hqe⟩ := hLcov x hxL hx
      exact hne q hq (CFSG.KS.PF.eq_of_fields hw (ptFacts (hp i hi)).canon (hLcan q hq)
        fun t ht => by rw [he ⟨t, ht⟩, hqe ⟨t, ht⟩])
    · intro hxL p hp' e
      obtain ⟨l, hl, hle⟩ := hL p hp'
      refine hxL ?_
      rw [hext x hx l hl fun t => Fin.ext (by rw [← he t, e, hle t])]
      exact hl
  rw [ne_eq, h1, h2, h3]
  tauto

theorem card_inv_of_btInvP {cntL : Nat} {KL : Nat → Nat} {L : Subgroup (Equiv.Perm (Fin n))}
    (hw : 0 < w) (hc : btHdK cnt = true)
    (hL : ∀ q < cntL, ∃ l ∈ L, ∀ t : Fin d, pg w (mask w) (btKey kw km KL q) t = l (b t))
    (hLcov : ∀ l ∈ L, l ∈ genSub n k gp →
      ∃ q < cntL, ∀ t : Fin d, pg w (mask w) (btKey kw km KL q) t = l (b t))
    (hLcan : ∀ q < cntL, btKey kw km KL q >>> (d * w) = 0)
    (hext : ∀ x ∈ genSub n k gp, ∀ l ∈ L, (∀ t, x (b t) = l (b t)) → x = l) :
    Nat.card {x : genSub n k gp // x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin n)) ∉ L} =
      btCntN cnt (btInvP k kw km cntL K R RT KL) := by
  rw [btCntN_eq]
  set T := (Finset.range cnt).filter (fun i => btInvP k kw km cntL K R RT KL i = true)
  have hT : T.card = Nat.card {i : Nat // i ∈ T} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hT]
  choose! el hel hkey using fun i (hi : i < cnt) => btKey_mem hg hb hp (kw := kw) (km := km) hi
  have hmemT : ∀ i ∈ T, i < cnt ∧ btInvP k kw km cntL K R RT KL i = true := fun i hi => by
    rw [Finset.mem_filter, Finset.mem_range] at hi
    exact hi
  have hP : ∀ i (hi : i ∈ T), el i * el i = 1 ∧ el i ≠ 1 ∧ el i ∉ L := fun i hi =>
    (btInvP_iff_el hg hp hfix hb hS hr hw hc hL hLcov hLcan hext (hmemT i hi).1
      (hel i (hmemT i hi).1) (hkey i (hmemT i hi).1)).1 (hmemT i hi).2
  let φ : {i : Nat // i ∈ T} →
      {x : genSub n k gp // x * x = 1 ∧ x ≠ 1 ∧ (x : Equiv.Perm (Fin n)) ∉ L} := fun i =>
    ⟨⟨el i.1, hel i.1 (hmemT i.1 i.2).1⟩, by
      refine ⟨Subtype.ext (hP i.1 i.2).1, fun h => (hP i.1 i.2).2.1 ?_, (hP i.1 i.2).2.2⟩
      exact congrArg Subtype.val h⟩
  have hbij : Function.Bijective φ := by
    refine ⟨fun i j e => Subtype.ext (btKey_inj hw hp (hmemT i.1 i.2).1 (hmemT j.1 j.2).1
      fun t => ?_), fun x => ?_⟩
    · have ev : el i.1 = el j.1 := congrArg (fun y => (y.1 : Equiv.Perm (Fin n))) e
      rw [hkey _ (hmemT i.1 i.2).1, hkey _ (hmemT j.1 j.2).1, ev]
    · obtain ⟨⟨x, hx⟩, hxx, hx1, hxL⟩ := x
      obtain ⟨i, hi, he⟩ := btKey_cover hg hb hp hc hx
      have hxe : el i = x := ext_of_base hfix (hel i hi) hx fun t => Fin.ext (by
        rw [← hkey i hi t, he t])
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hxx' : x * x = 1 := congrArg Subtype.val hxx
      have hiT : i ∈ T := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, (btInvP_iff_el hg hp hfix hb hS hr hw hc hL hLcov hLcan hext hi hx he).2
          ⟨hxx', hx1', hxL⟩⟩
      exact ⟨⟨i, hiT⟩, Subtype.ext (Subtype.ext hxe)⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

end Inv

end CFSG.KS.BTup

end

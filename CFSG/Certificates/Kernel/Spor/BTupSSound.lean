module

public import Certificates.Data.Kernel.Spor.BTupS
public import CFSG.Certificates.Kernel.Spor.BTupOSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btSh_succ (w d : Nat) (f : Nat → Nat) :
    btSh w (d + 1) f = btSh w d f + f d <<< (w * d) := rfl

theorem btSh_congr {w d : Nat} {f g : Nat → Nat} (h : ∀ t < d, f t = g t) :
    btSh w d f = btSh w d g := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [btSh_succ, btSh_succ, ih fun t ht => h t (by omega), h d (by omega)]

@[expose] noncomputable def btKf {n d : Nat} (w : Nat) (b : Fin d → Fin n) (y : Equiv.Perm (Fin n)) :
    Nat :=
  btSh w d fun t => if h : t < d then (y (b ⟨t, h⟩) : Nat) else 0

theorem btCjSum_eq (w m d cnt : Nat) (G R PRE : Nat → Nat) (c j : Nat) :
    btCjSum w m d cnt G R PRE c j = ∑ s ∈ Finset.range cnt, btCjKy w m d G R PRE c j s := by
  induction cnt with
  | zero => rfl
  | succ cnt ih =>
    change strictN (btCjSum w m d cnt G R PRE c j)
      (fun a => Nat.add a (btCjKy w m d G R PRE c j cnt)) = _
    rw [CFSG.KS.Raw.Orb.strictN_eq, Finset.sum_range_succ, ← ih]
    rfl

theorem btInc_spec {cnt : Nat} {SV : Nat → Nat} (h : btIncK cnt SV = true) {i j : Nat}
    (hij : i < j) (hj : j < cnt) : btSv SV i < btSv SV j := by
  have step : ∀ a, a + 1 < cnt → btSv SV a < btSv SV (a + 1) := fun a ha => by
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h a (by omega)
    rw [CFSG.KS.Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr ha)] at h1
    exact Nat.blt_eq.mp h1
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (by omega)) (step j hj)
    · subst h'
      exact step i hj

section Walk

variable {n w d kw km k cnt base : Nat} {G K R POS : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n}
  (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
  (hfix : ∀ h ∈ genSub n k gp, (∀ t, h (b t) = b t) → h = 1)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
include hg hp hfix hb

theorem btCjPt {c : Nat} {γ : Equiv.Perm (Fin n)} (hc : ∀ x : Fin n, pg w (mask w) c x = γ x)
    {PRE : Nat → Nat} {j : Nat}
    (hpre : ∀ t : Fin d, ∃ hl : btPre PRE d j t < n, γ ⟨_, hl⟩ = b t)
    {s : Nat} (hs : s < cnt) {y : Equiv.Perm (Fin n)} (hy : y ∈ genSub n k gp)
    (hk : ∀ t : Fin d, pg w (mask w) (btKey kw km K s) t = y (b t)) (t : Fin d) :
    pg w (mask w) c (btWalk w (mask w) G R s (btPre PRE d j t)) = ((γ * y * γ⁻¹) (b t) : Nat) := by
  obtain ⟨hl, he⟩ := hpre t
  have e2 : γ⁻¹ (b t) = ⟨_, hl⟩ := by
    rw [← he, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  rw [btWalk_spec hg hp hfix hb hs hy hk ⟨_, hl⟩, hc]
  simp only [Equiv.Perm.mul_apply]
  rw [e2]

theorem btSg_spec {ws ms c j : Nat} {S : Nat} {PRE : Nat → Nat} {γ : Equiv.Perm (Fin n)}
    (hc : ∀ x : Fin n, pg w (mask w) c x = γ x)
    (hpre : ∀ t : Fin d, ∃ hl : btPre PRE d j t < n, γ ⟨_, hl⟩ = b t)
    (h : btSgK w (mask w) d kw km cnt ws ms G K R PRE S c j = true) {s : Nat} (hs : s < cnt)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ genSub n k gp)
    (hk : ∀ t : Fin d, pg w (mask w) (btKey kw km K s) t = y (b t)) :
    pg ws ms S s < cnt ∧ ∀ t : Fin d,
      pg w (mask w) (btKey kw km K (pg ws ms S s)) t = (γ * y * γ⁻¹) (b t) := by
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h s hs
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
  refine ⟨Nat.blt_eq.mp h1.1, fun t => ?_⟩
  rw [Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 h1.2 t t.2)]
  exact btCjPt hg hp hfix hb hc hpre hs hy hk t

theorem btCjKy_eq {c : Nat} {γ : Equiv.Perm (Fin n)} (hc : ∀ x : Fin n, pg w (mask w) c x = γ x)
    {PRE : Nat → Nat} {j : Nat}
    (hpre : ∀ t : Fin d, ∃ hl : btPre PRE d j t < n, γ ⟨_, hl⟩ = b t)
    {s : Nat} (hs : s < cnt) {y : Equiv.Perm (Fin n)} (hy : y ∈ genSub n k gp)
    (hk : ∀ t : Fin d, pg w (mask w) (btKey kw km K s) t = y (b t)) :
    btCjKy w (mask w) d G R PRE c j s = btKf w b (γ * y * γ⁻¹) := by
  unfold btCjKy btKf
  exact btSh_congr fun t ht => by
    rw [dif_pos ht]
    exact btCjPt hg hp hfix hb hc hpre hs hy hk ⟨t, ht⟩

theorem btCjSK_spec {B c j : Nat} {PRE SV : Nat → Nat} {γ : Equiv.Perm (Fin n)}
    (hc : ∀ x : Fin n, pg w (mask w) c x = γ x) (hB : ∀ t : Fin d, pg w (mask w) B t = b t)
    (h : btCjSK n w (mask w) d cnt B G R PRE SV c j = true) {y : Nat → Equiv.Perm (Fin n)}
    (hy : ∀ s < cnt, y s ∈ genSub n k gp)
    (hk : ∀ s < cnt, ∀ t : Fin d, pg w (mask w) (btKey kw km K s) t = y s (b t)) :
    (∀ t : Fin d, ∃ hl : btPre PRE d j t < n, γ ⟨_, hl⟩ = b t) ∧
      ∑ s ∈ Finset.range cnt, btKf w b (γ * y s * γ⁻¹) = btSv SV j := by
  unfold btCjSK at h
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have hpre : ∀ t : Fin d, ∃ hl : btPre PRE d j t < n, γ ⟨_, hl⟩ = b t := fun t => by
    have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h.1 t t.2
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
    refine ⟨Nat.blt_eq.mp h1.1, Fin.ext ?_⟩
    rw [← hc, Nat.beq_eq.mp h1.2, hB t]
  refine ⟨hpre, ?_⟩
  rw [← Nat.beq_eq.mp h.2, btCjSum_eq]
  exact Finset.sum_congr rfl fun s hs =>
    (btCjKy_eq hg hp hfix hb hc hpre (Finset.mem_range.1 hs) (hy s (Finset.mem_range.1 hs))
      (hk s (Finset.mem_range.1 hs))).symm

end Walk

end CFSG.KS.BTup

end

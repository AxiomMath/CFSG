module

public import Certificates.Data.Kernel.D43.Twin
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.ONVecLib
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KC.Misc.HexFlat

theorem hexTable_row {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (h : hexFlat cs d n w N F = true) {m k p : Nat} (hp : p < n * m) (hk : m * k + p / n < N) :
    (CFSG.Monster.B.Co2.Native.hexTable d (n * m) (n * m * k) (String.ofList cs))[p]! =
      CFSG.KC.Enum.pg w (mask w) (F (m * k + p / n)) (p % n) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp
  have e := congrArg (fun a : Array Nat => a[p % n]!) (hexTable_sound h _ hk)
  simp only [CFSG.Monster.B.Co2.Native.hexTable, CFSG.KS.Raw.unpack] at e ⊢
  rw [getElem!_pos _ _ (by simpa using Nat.mod_lt p hn), Array.getElem_ofFn,
    getElem!_pos _ _ (by simpa using Nat.mod_lt p hn), Array.getElem_ofFn] at e
  rw [getElem!_pos _ _ (by simpa using hp), Array.getElem_ofFn, ← e]
  have key : n * (m * k + p / n) + p % n = n * m * k + p := by
    have := Nat.div_add_mod p n
    rw [Nat.mul_add, ← Nat.mul_assoc]
    omega
  simp only [Fin.val_mk, key]

theorem keyChk_spec {KT : Nat → Nat} {L : List Nat} {T : Nat → Nat} {p : Nat}
    (h : keyChk KT L T p = true) :
    T p < 26572 ∧ (mv L (key KT p) = key KT (T p) ∨ mv L (key KT p) = vneg (key KT (T p))) := by
  unfold keyChk at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.blt_eq.mp h1, ?_⟩
  cases h3 : Nat.beq (mv L (key KT p)) (key KT (T p)) <;> rw [h3] at h2
  · exact Or.inr (Nat.eq_of_beq_eq_true h2)
  · exact Or.inl (Nat.eq_of_beq_eq_true h3)

theorem keyChunk_spec {KT : Nat → Nat} {L : List Nat} {T : Nat → Nat} {c : Nat}
    (h : keyChunk KT L T c = true) {p : Nat} (h1 : 256 * c ≤ p) (h2 : p < 256 * c + 256)
    (h3 : p < 26572) : keyChk KT L T p = true := by
  have := allBlk_spec h (p - 256 * c) (by change p - 256 * c < 256; omega)
  have e : Nat.add (Nat.mul 256 c) (p - 256 * c) = p := by
    change 256 * c + (p - 256 * c) = p
    omega
  rw [e] at this
  have hb : Nat.blt p 26572 = true := Nat.blt_eq.mpr h3
  change Bool.rec (motive := fun _ => Bool) true (keyChk KT L T p) (Nat.blt p 26572) = true at this
  rwa [hb] at this

theorem keyChunks_spec {KT : Nat → Nat} {L : List Nat} {T : Nat → Nat}
    (h : ∀ c < 104, keyChunk KT L T c = true) {p : Nat} (hp : p < 26572) :
    T p < 26572 ∧ (mv L (key KT p) = key KT (T p) ∨ mv L (key KT p) = vneg (key KT (T p))) :=
  keyChk_spec (keyChunk_spec (h (p / 256) (by omega)) (by omega) (by omega) hp)

theorem ordChk_spec {KT O : Nat → Nat} {t : Nat} (h : ordChk KT O t = true) :
    O t < 26572 ∧ wf84 (key KT (O t)) = true ∧
      (t < 26571 → canonPk (key KT (O t)) < canonPk (key KT (O (t + 1)))) := by
  unfold ordChk at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, h2, fun ht => ?_⟩
  have hb : Nat.blt t 26571 = true := Nat.blt_eq.mpr ht
  rw [hb] at h3
  exact Nat.blt_eq.mp h3

theorem ordChunk_spec {KT O : Nat → Nat} {c : Nat} (h : ordChunk KT O c = true) {t : Nat}
    (h1 : 2048 * c ≤ t) (h2 : t < 2048 * c + 2048) (h3 : t < 26572) : ordChk KT O t = true := by
  have := allN_spec h (t - 2048 * c) (by change t - 2048 * c < 2048; omega)
  have e : Nat.add (Nat.mul 2048 c) (t - 2048 * c) = t := by
    change 2048 * c + (t - 2048 * c) = t
    omega
  simp only [e] at this
  have hb : Nat.blt t 26572 = true := Nat.blt_eq.mpr h3
  change Bool.rec (motive := fun _ => Bool) true (ordChk KT O t) (Nat.blt t 26572) = true at this
  rwa [hb] at this

theorem ordChunks_spec {KT O : Nat → Nat} (h : ∀ c < 13, ordChunk KT O c = true) :
    ∀ t < 26572, ordChk KT O t = true := fun t ht =>
  ordChunk_spec (h (t / 2048) (by omega)) (by omega) (by omega) ht

theorem wf84_spec {X : Nat} (h : wf84 X = true) :
    VB 84 (vOf X) ∧ canon X = true ∧ vP X &&& vM X = 0 ∧ 0 < vP X ||| vM X := by
  unfold wf84 at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h0, hp, hm, hz⟩ := h
  have hp' : vP X < 2 ^ 84 := by
    have := Nat.blt_eq.mp hp
    rwa [PackFld.shl_eq, Nat.one_mul] at this
  have hm' : vM X < 2 ^ 84 := by
    have := Nat.blt_eq.mp hm
    rwa [PackFld.shl_eq, Nat.one_mul] at this
  have h0' : vP X &&& vM X = 0 := Nat.eq_of_beq_eq_true h0
  refine ⟨VB.of_lt hp' hm', ?_, h0', Nat.blt_eq.mp hz⟩
  unfold canon
  simp only [PackFld.strictB_eqP, bAnd_iff]
  refine ⟨by rw [show Nat.land (vP X) (vM X) = 0 from h0']; rfl, ?_, ?_⟩
  · rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.blt_eq.mpr (lt_of_lt_of_le hp' (Nat.pow_le_pow_right (by omega) (by omega)))
  · rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.blt_eq.mpr (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by omega) (by omega)))

theorem ord_spec {KT O : Nat → Nat} (h : ∀ t < 26572, ordChk KT O t = true) :
    (∀ p < 26572, wf84 (key KT p) = true) ∧
      ∀ p < 26572, ∀ q < 26572, canonPk (key KT p) = canonPk (key KT q) → p = q := by
  let f : Nat → Nat := fun t => canonPk (key KT (O t))
  have hmono : ∀ s t, s < t → t < 26572 → f s < f t := by
    intro s t hst ht
    induction t with
    | zero => omega
    | succ t ih =>
      have hs := (ordChk_spec (h t (by omega))).2.2 (by omega)
      rcases Nat.lt_or_ge s t with h' | h'
      · exact lt_trans (ih h' (by omega)) hs
      · have e : s = t := by omega
        subst e
        exact hs
  have hinj : ∀ s < 26572, ∀ t < 26572, f s = f t → s = t := by
    intro s hs t ht e
    rcases Nat.lt_trichotomy s t with h' | h' | h'
    · exact absurd e (Nat.ne_of_lt (hmono s t h' ht))
    · exact h'
    · exact absurd e.symm (Nat.ne_of_lt (hmono t s h' hs))
  let g : Fin 26572 → Fin 26572 := fun t => ⟨O t, (ordChk_spec (h t t.2)).1⟩
  have hg : Function.Injective g := by
    intro s t e
    have e' : O s = O t := congrArg Fin.val e
    exact Fin.ext (hinj s s.2 t t.2 (by simp only [f, e']))
  have hsurj := Finite.injective_iff_surjective.mp hg
  have hpre : ∀ p < 26572, ∃ t < 26572, O t = p := fun p hp => by
    obtain ⟨t, ht⟩ := hsurj ⟨p, hp⟩
    exact ⟨t, t.2, congrArg Fin.val ht⟩
  refine ⟨fun p hp => ?_, fun p hp q hq e => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := hpre p hp
    exact (ordChk_spec (h t ht)).2.1
  · obtain ⟨s, hs, rfl⟩ := hpre p hp
    obtain ⟨t, ht, rfl⟩ := hpre q hq
    rw [hinj s hs t ht e]

end CFSG.KC.D43

end

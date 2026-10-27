module

public import Certificates.Data.Kernel.Spor.BTupR
public import CFSG.Certificates.Kernel.Spor.BTupSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

theorem btRtK_spec {k m cnt i : Nat} {S R POS RT : Nat → Nat}
    (h : btRtK k m cnt S R POS RT i = true) {j : Nat} (hj : j < m) :
    btPos RT m i j < cnt ∧ (btDep (btRec R i) = 0 → btPos RT m i j = S j) ∧
      (btDep (btRec R i) ≠ 0 → btPos RT m i j =
        btPos POS k (btPos RT m (btPar (btRec R i)) j) (btLab (btRec R i))) := by
  unfold btRtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true,
    CFSG.KS.Raw.Orb.bIf_eq] at h1
  obtain ⟨h1, h2⟩ := h1
  refine ⟨Nat.blt_eq.mp h1, fun h0 => ?_, fun h0 => ?_⟩
  · rw [if_pos (Nat.beq_eq.mpr h0)] at h2
    exact Nat.beq_eq.mp h2
  · have h0' : Nat.beq (btDep (btRec R i)) (nat_lit 0) = false := by
      cases e : Nat.beq (btDep (btRec R i)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.beq_eq.mp e) h0
    rw [h0', if_neg Bool.false_ne_true] at h2
    exact Nat.beq_eq.mp h2

theorem btRtSl_spec {k m cnt lo len : Nat} {S R POS RT : Nat → Nat}
    (h : btRtSlK k m cnt S R POS RT lo len = true) {i : Nat} (h1 : lo ≤ i) (h2 : i < lo + len)
    (hi : i < cnt) : btRtK k m cnt S R POS RT i = true := by
  unfold btRtSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

theorem btCzK_spec {w d kw km m cnt2 i : Nat} {Y K RT K2 IX : Nat → Nat}
    (h : btCzK w (mask w) d kw km m cnt2 Y K RT K2 IX i = true)
    (hc : ∀ j < m, ∀ t < d, pg w (mask w) (btKey kw km K (btPos RT m i j)) t =
      pg w (mask w) (Y j) (pg w (mask w) (btKey kw km K i) t)) :
    btIx IX i < cnt2 ∧ btKey kw km K i = btKey kw km K2 (btIx IX i) := by
  unfold btCzK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h
  have hall : allN m (fun j => btMov w (mask w) d (Y j) (btKey kw km K i)
      (btKey kw km K (btPos RT m i j))) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun j hj =>
      CFSG.KS.Raw.Orb.allN_iff.2 fun t ht => Nat.beq_eq.mpr (hc j hj t ht)
  rw [if_pos hall, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.beq_eq.mp h.2⟩

theorem btCzSl_spec {w d kw km m cnt cnt2 lo len : Nat} {Y K RT K2 IX : Nat → Nat}
    (h : btCzSlK w (mask w) d kw km m cnt cnt2 Y K RT K2 IX lo len = true) {i : Nat}
    (h1 : lo ≤ i) (h2 : i < lo + len) (hi : i < cnt) :
    btCzK w (mask w) d kw km m cnt2 Y K RT K2 IX i = true := by
  unfold btCzSlK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, if_pos (Nat.blt_eq.mpr hi)] at h'
  exact h'

section Rt

variable {n w d kw km k m cnt base : Nat} {G K R POS S RT : Nat → Nat}
  {gp : Nat → Equiv.Perm (Fin n)} {b : Fin d → Fin n} {y : Nat → Equiv.Perm (Fin n)}
  (hg : ∀ j < k, ∀ x : Fin n, pg w (mask w) (G j) x = gp j x)
  (hp : ∀ i < cnt, btPtK n w (mask w) d kw km k cnt base G K R POS i = true)
  (hfix : ∀ h ∈ genSub n k gp, (∀ t, h (b t) = b t) → h = 1)
  (hb : ∀ t : Fin d, pg w (mask w) base t = b t)
  (hS : ∀ j < m, ∀ t : Fin d, pg w (mask w) (btKey kw km K (S j)) t = y j (b t))
  (hr : ∀ i < cnt, btRtK k m cnt S R POS RT i = true)
include hg hp hfix hb hS hr

theorem btRt_dep : ∀ D i, i < cnt → btDep (btRec R i) = D → ∀ h ∈ genSub n k gp,
    (∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t)) → ∀ j < m,
    btPos RT m i j < cnt ∧
      ∀ t : Fin d, pg w (mask w) (btKey kw km K (btPos RT m i j)) t = (h * y j) (b t) := by
  intro D
  induction D with
  | zero =>
    intro i hi hD h hh he j hj
    obtain ⟨hq, h0, -⟩ := btRtK_spec (hr i hi) hj
    have h1 : h = 1 := hfix h hh fun t => Fin.ext (by
      rw [← he t, (ptFacts (hp i hi)).root hD, hb t])
    refine ⟨hq, fun t => ?_⟩
    rw [h0 hD, hS j hj t, h1, one_mul]
  | succ D ih =>
    intro i hi hD h hh he j hj
    obtain ⟨hpar, hlab, hdep, hmov⟩ := (ptFacts (hp i hi)).tree (by omega)
    obtain ⟨hq, -, h0⟩ := btRtK_spec (hr i hi) hj
    set p := btPar (btRec R i)
    set l := btLab (btRec R i)
    have hh' : (gp l)⁻¹ * h ∈ genSub n k gp :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (gp_mem hlab)) hh
    have he' : ∀ t : Fin d, pg w (mask w) (btKey kw km K p) t = ((gp l)⁻¹ * h) (b t) := by
      intro t
      have hlt : pg w (mask w) (btKey kw km K p) t < n := (ptFacts (hp p hpar)).lt t t.2
      have e1 : gp l ⟨_, hlt⟩ = h (b t) := Fin.ext (by
        rw [← hg l hlab, ← he t, hmov t t.2])
      rw [Equiv.Perm.mul_apply, ← e1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    obtain ⟨hq', he''⟩ := ih p hpar (by omega) _ hh' he' j hj
    refine ⟨hq, fun t => ?_⟩
    rw [h0 (by omega), (ptFacts (hp _ hq')).clos l hlab |>.2 t t.2, he'' t, hg l hlab]
    rw [mul_assoc, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem btRt_spec {i : Nat} (hi : i < cnt) {h : Equiv.Perm (Fin n)} (hh : h ∈ genSub n k gp)
    (he : ∀ t : Fin d, pg w (mask w) (btKey kw km K i) t = h (b t)) {j : Nat} (hj : j < m) :
    btPos RT m i j < cnt ∧
      ∀ t : Fin d, pg w (mask w) (btKey kw km K (btPos RT m i j)) t = (h * y j) (b t) :=
  btRt_dep hg hp hfix hb hS hr _ i hi rfl h hh he j hj

theorem btCz_mem {cnt2 : Nat} {Y K2 IX : Nat → Nat}
    (hY : ∀ j < m, ∀ x : Fin n, pg w (mask w) (Y j) x = y j x)
    (hz : ∀ i < cnt, btCzK w (mask w) d kw km m cnt2 Y K RT K2 IX i = true)
    (hc : btHdK cnt = true) {h : Equiv.Perm (Fin n)} (hh : h ∈ genSub n k gp)
    (hcomm : ∀ j < m, h * y j = y j * h) :
    ∃ q < cnt2, ∀ t : Fin d, pg w (mask w) (btKey kw km K2 q) t = h (b t) := by
  obtain ⟨i, hi, he⟩ := btKey_cover hg hb hp hc hh
  have hcz := btCzK_spec (hz i hi) fun j hj t ht => by
    rw [(btRt_spec hg hp hfix hb hS hr hi hh he hj).2 ⟨t, ht⟩, hcomm j hj, he ⟨t, ht⟩,
      Equiv.Perm.mul_apply]
    exact (hY j hj _).symm
  exact ⟨_, hcz.1, fun t => by rw [← hcz.2, he t]⟩

end Rt

end CFSG.KS.BTup

end

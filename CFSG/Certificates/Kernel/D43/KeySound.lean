module

public import CFSG.Certificates.Kernel.D43.TwinSound
public import CFSG.Certificates.Kernel.D43.RowsSound
public import CFSG.Certificates.Kernel.D43.SignedAct
public import Certificates.Data.Kernel.D43.Cube
public import CFSG.Milestones.ASVolI.F48.D43.Lin
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native CFSG.ASVolI CFSG.Blueprint.Chevalley

theorem canon_of_bits {X : Nat} (h0 : vP X &&& vM X = 0) (hp : vP X < 2 ^ 154)
    (hm : vM X < 2 ^ 154) : canon X = true := by
  unfold canon
  simp only [PackFld.strictB_eqP, bAnd_iff]
  refine ⟨by rw [show Nat.land (vP X) (vM X) = 0 from h0]; rfl, ?_, ?_⟩
  · rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.blt_eq.mpr hp
  · rw [PackFld.shl_eq, Nat.one_mul]
    exact Nat.blt_eq.mpr hm

theorem vneg_bits {X : Nat} (hc : canon X = true) : vP (vneg X) = vM X ∧ vM (vneg X) = vP X := by
  obtain ⟨-, -, hm⟩ := canon_bits hc
  have hm' : vM X < 2 ^ 256 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  exact ⟨vP_vmk hm', vM_vmk hm'⟩

theorem canon_vneg {X : Nat} (hc : canon X = true) : canon (vneg X) = true := by
  obtain ⟨h0, hp, hm⟩ := canon_bits hc
  obtain ⟨e1, e2⟩ := vneg_bits hc
  refine canon_of_bits ?_ (by rw [e1]; exact hm) (by rw [e2]; exact hp)
  rw [e1, e2, Nat.land_comm]
  exact h0

theorem vneg_vneg {X : Nat} (hc : canon X = true) : vneg (vneg X) = X := by
  obtain ⟨e1, e2⟩ := vneg_bits hc
  have e : vneg (vneg X) = vmk (vM (vneg X)) (vP (vneg X)) := rfl
  rw [e, e1, e2, vmk_vP_vM]

theorem canonPk_vneg {X : Nat} (hc : canon X = true) : canonPk (vneg X) = canonPk X := by
  unfold canonPk
  rw [vneg_vneg hc]
  rcases Nat.lt_trichotomy X (vneg X) with h | h | h
  · have h1 : Nat.blt X (vneg X) = true := Nat.blt_eq.mpr h
    have h2 : Nat.blt (vneg X) X = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      omega
    rw [h1, h2]
  · rw [← h]
  · have h1 : Nat.blt (vneg X) X = true := Nat.blt_eq.mpr h
    have h2 : Nat.blt X (vneg X) = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      omega
    rw [h1, h2]

theorem vOf_vneg {X : Nat} (hc : canon X = true) : vOf (vneg X) = (vOf X).neg := by
  obtain ⟨e1, e2⟩ := vneg_bits hc
  unfold vOf V.neg
  rw [e1, e2]

theorem vecOf_vneg {X : Nat} (hc : canon X = true) :
    vecOf (ofV (vOf (vneg X))) = -vecOf (ofV (vOf X)) := by
  rw [vOf_vneg hc, ← neg_ofV, vecOf_neg (wf_of_canon154 (canon154_vOf hc))]

theorem vecOf_high {X : Nat} (hc : canon X = true) (hb : VB 84 (vOf X)) (q : Fin 154)
    (hq : 84 ≤ q.val) : vecOf (ofV (vOf X)) q = 0 := by
  obtain ⟨-, hp, hm⟩ := canon_bits hc
  have hp' : (vOf X).p < 2 ^ 256 := lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (by omega))
  have hm' : (vOf X).m < 2 ^ 256 := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  rw [vecOf_apply, W.toV_ofV hp' hm', V.val_eq_bitVal, (hb q.val hq).1, (hb q.val hq).2]
  rfl

theorem vecOf_vOf_inj {X Y : Nat} (hX : canon X = true) (hY : canon Y = true)
    (h : vecOf (ofV (vOf X)) = vecOf (ofV (vOf Y))) : X = Y :=
  vOf_inj hX hY (vecOf_inj (canon154_vOf hX) (canon154_vOf hY) h)

section Action


theorem exists_ρ_of_checks {KT : Nat → Nat} {RL : List (List Nat)} {T : Nat → Nat → Nat}
    (hrows : ∀ k < 8, rowsOK (RL.getD k []) k = true)
    (hkeys : ∀ k < 8, ∀ p < 26572, T k p < 26572 ∧ (mv (RL.getD k []) (key KT p) = key KT (T k p) ∨
      mv (RL.getD k []) (key KT p) = vneg (key KT (T k p))))
    (hwf : ∀ p < 26572, wf84 (key KT p) = true)
    (hdist : ∀ p < 26572, ∀ q < 26572, canonPk (key KT p) = canonPk (key KT q) → p = q)
    {K : Type} [Field K] (ω : K) (hK : Nat.card K = 27) (hω : ω ^ 3 = ω + 1)
    (h : Fin 8 → ModGL Tag.D4 K)
    (hh : ∀ k, (h k : Module.End K (RootModule Tag.D4 K)) = burnsideF48d_genEnd ω k) :
    ∃ ρ : ↥(Subgroup.closure (Set.range h)) →* Equiv.Perm (Fin 26572),
      ∀ k (p : Fin 26572), ((ρ ⟨h k, Subgroup.subset_closure ⟨k, rfl⟩⟩ p : Fin 26572) : ℕ) =
        T k p := by
  haveI : CharP K 3 := by
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hc : ∀ p < 26572, canon (key KT p) = true := fun p hp => (wf84_spec (hwf p hp)).2.1
  have hb : ∀ p < 26572, VB 84 (vOf (key KT p)) := fun p hp => (wf84_spec (hwf p hp)).1
  let P : ℕ → RootModule Tag.D4 K := fun p => burnsideF48d_Ψ ω (vecOf (ofV (vOf (key KT p))))
  have hsmul : ∀ (g : ModGL Tag.D4 K) (v : RootModule Tag.D4 K),
      g • v = (g : Module.End K (RootModule Tag.D4 K)) v := fun _ _ => rfl
  have hT : ∀ k : Fin 8, ∀ p < 26572, T k p < 26572 ∧
      (h k • P p = P (T k p) ∨ h k • P p = -P (T k p)) := by
    intro k p hp
    obtain ⟨hlt, hmv⟩ := hkeys k k.2 p hp
    refine ⟨hlt, ?_⟩
    have hrk : burnsideF48d_rows (burnsideF48d_colTab ()) k =
        burnsideF48d_genRows (burnsideF48d_colTab ()) k := if_neg (by omega)
    have e : h k • P p =
        burnsideF48d_Ψ ω (vecOf (ofV (vOf (mv (RL.getD k []) (key KT p))))) := by
      rw [hsmul, hh k, ← rows_mulVecT (hrows k k.2) (hb p hp), hrk]
      exact (burnsideF48d_Ψ_combW ω (burnsideF48d_rowsWF _)
        (wf_of_canon154 (canon154_vOf (hc p hp))) _ (burnsideF48d_Ψ_genRows ω hω k)).symm
    rcases hmv with e2 | e2
    · exact Or.inl (by rw [e, e2])
    · refine Or.inr ?_
      rw [e, e2, vecOf_vneg (hc _ hlt), burnsideF48d_Ψ_neg]
  have hinj : ∀ p < 26572, ∀ q < 26572, (P p = P q ∨ P p = -P q) → p = q := by
    intro p hp q hq e
    have hpH := vecOf_high (hc p hp) (hb p hp)
    rcases e with e | e
    · have := burnsideF48d_Ψ_inj ω hω hpH (vecOf_high (hc q hq) (hb q hq)) e
      exact hdist p hp q hq (by rw [vecOf_vOf_inj (hc p hp) (hc q hq) this])
    · have e' : P p = burnsideF48d_Ψ ω (vecOf (ofV (vOf (vneg (key KT q))))) := by
        rw [vecOf_vneg (hc q hq), burnsideF48d_Ψ_neg]
        exact e
      have hnb : VB 84 (vOf (vneg (key KT q))) := by
        rw [vOf_vneg (hc q hq)]
        exact (hb q hq).neg
      have := burnsideF48d_Ψ_inj ω hω hpH (vecOf_high (canon_vneg (hc q hq)) hnb) e'
      have e3 := vecOf_vOf_inj (hc p hp) (canon_vneg (hc q hq)) this
      exact hdist p hp q hq (by rw [e3, canonPk_vneg (hc q hq)])
  exact exists_hom_signed h P (fun k p => T k p) (fun g v => smul_neg g v) hT hinj

end Action

theorem cubeChk_spec {F : Nat → Nat} {k p : Nat} (h : cubeChk F k p = true) :
    tabAt F k p < 26572 ∧ tabAt F k (tabAt F k p) < 26572 ∧
      tabAt F k (tabAt F k (tabAt F k p)) = p := by
  unfold cubeChk at h
  simp only [PackFld.strictB_eqP, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem cubeChunk_spec {F : Nat → Nat} {k c : Nat} (h : cubeChunk F k c = true) {p : Nat}
    (h1 : 2048 * c ≤ p) (h2 : p < 2048 * c + 2048) (h3 : p < 26572) : cubeChk F k p = true := by
  have := allN_spec h (p - 2048 * c) (by change p - 2048 * c < 2048; omega)
  have e : Nat.add (Nat.mul 2048 c) (p - 2048 * c) = p := by
    change 2048 * c + (p - 2048 * c) = p
    omega
  simp only [e] at this
  have hb : Nat.blt p 26572 = true := Nat.blt_eq.mpr h3
  change Bool.rec (motive := fun _ => Bool) true (cubeChk F k p) (Nat.blt p 26572) = true at this
  rwa [hb] at this

theorem exists_perm_of_cube {F : Nat → Nat} {k : Nat} (h : ∀ c < 13, cubeChunk F k c = true) :
    ∃ e : Equiv.Perm (Fin 26572), ∀ p : Fin 26572, ((e p : Fin 26572) : ℕ) = tabAt F k p := by
  have hs : ∀ p < 26572, tabAt F k p < 26572 ∧ tabAt F k (tabAt F k p) < 26572 ∧
      tabAt F k (tabAt F k (tabAt F k p)) = p := fun p hp =>
    cubeChk_spec (cubeChunk_spec (h (p / 2048) (by omega)) (by omega) (by omega) hp)
  refine ⟨{ toFun := fun p => ⟨tabAt F k p, (hs p p.2).1⟩
            invFun := fun p => ⟨tabAt F k (tabAt F k p), (hs p p.2).2.1⟩
            left_inv := fun p => Fin.ext (hs p p.2).2.2
            right_inv := fun p => Fin.ext (hs p p.2).2.2 }, fun p => rfl⟩

end CFSG.KC.D43

end

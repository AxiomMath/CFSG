module

public import CFSG.Certificates.Kernel.ChengHeldSec2Twin
public import CFSG.Certificates.Kernel.ChengHeldS2Bind
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.ChengHeldS2

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum

variable {gens : Array Tab} {E : Enum} {p : ℕ → Equiv.Perm (Fin 256)} {T PL G : ℕ → ℕ}
  {IXP IVP : ℕ}

theorem bind_parts (h : bindK T PL IXP IVP = true) {a : ℕ} (ha : a < 256) :
    pg 9 (mask 9) IXP a < 256 ∧ pg 9 (mask 9) (T (pg 9 (mask 9) IXP a)) 0 = a ∧
      iR IVP a < 256 ∧ mR T IXP a (iR IVP a) = 0 ∧ parOf PL a < 256 := by
  have h1 := allN_spec h a ha
  simp only [bAnd_iff, Nat.blt_eq] at h1
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  exact ⟨a1, Nat.eq_of_beq_eq_true a2, a3, Nat.eq_of_beq_eq_true a4, a5⟩

theorem cl_parts {m : ℕ → ℕ → ℕ} {gs : List ℕ} (h : clK m gs = true) :
    (∀ g ∈ gs, g < 256) ∧ clStepK 256 m gs (clIterK 256 m gs 16) = clIterK 256 m gs 16 := by
  unfold clK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun g hg => by simpa [Nat.blt_eq] using h.1 g hg, Nat.eq_of_beq_eq_true h.2⟩

theorem autRec_parts {m : ℕ → ℕ → ℕ} {inv g : ℕ → ℕ} {α k P : ℕ}
    (h : autRecK m inv g T PL α k P = true) :
    aR P 0 = 0 ∧ ∀ i, 0 < i → i < 256 →
      aR P (oR T i) = m (imgK m inv g α k (lR PL i)) (aR P (pR T PL i)) := by
  unfold autRecK at h
  rw [bAnd_iff] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun i h0 hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact Nat.eq_of_beq_eq_true (allN_spec h.2 j (by omega))

theorem sec2_of (hd : RegData 256 gens E p) (hgs : gens.size = 7)
    (hE : E = penumRec 256 9 256 T PL) (hG : GensOK 256 9 7 G gens) {α : ℕ} (hα : α ≤ 1)
    {P0 P1 P2 : ℕ} (hb : bindK T PL IXP IVP = true)
    (ha : (autRecK (mR T IXP) (iR IVP) (gR G) T PL α 0 P0 &&
      autRecK (mR T IXP) (iR IVP) (gR G) T PL α 1 P1 &&
      autRecK (mR T IXP) (iR IVP) (gR G) T PL α 2 P2) = true)
    (hcl : (clK (mR T IXP) (zGs (gR G)) && clK (mR T IXP) (vGs (mR T IXP) (gR G)) &&
      clK (mR T IXP) (u1Gs (mR T IXP) (gR G)) && clK (mR T IXP) (u2Gs (mR T IXP) (gR G))) = true)
    (htw : (twK 256 (mR T IXP) (iR IVP) (aR P0) (bR (mR T IXP) (zGs (gR G))) &&
      twK 256 (mR T IXP) (iR IVP) (aR P1) (bR (mR T IXP) (zGs (gR G))) &&
      twK 256 (mR T IXP) (iR IVP) (aR P2) (bR (mR T IXP) (zGs (gR G)))) = true)
    (hsq : sqVK 256 (mR T IXP) (bR (mR T IXP) (vGs (mR T IXP) (gR G))) = true)
    (hea : eaCentK 256 (mR T IXP) (bR (mR T IXP) (vGs (mR T IXP) (gR G))) = true)
    (hpf : pairFixK 256 (mR T IXP) (iR IVP) (aR P0) (aR P1) = true)
    (hnc : (notCentK 256 (mR T IXP) (iR IVP) (aR P0) (bR (mR T IXP) (vGs (mR T IXP) (gR G))) &&
      notCentK 256 (mR T IXP) (iR IVP) (aR P2) (bR (mR T IXP) (vGs (mR T IXP) (gR G)))) = true)
    (huf : unitFixK 256 (aR P2) (bR (mR T IXP) (u1Gs (mR T IXP) (gR G)))
      (bR (mR T IXP) (u2Gs (mR T IXP) (gR G))) = true)
    (hgr : α = 1 → graphK 256 (mR T IXP) (iR IVP) (aR P1) (bR (mR T IXP) (vGs (mR T IXP) (gR G)))
      (gR G 0) = true) :
    (twM (mkRegGen 256 gens E) α 0 && twM (mkRegGen 256 gens E) α 1 &&
      twM (mkRegGen 256 gens E) α 2 && sqVM (mkRegGen 256 gens E) &&
      eaCentM (mkRegGen 256 gens E) && pairFixM (mkRegGen 256 gens E) α &&
      graphM (mkRegGen 256 gens E) α && notCentVM (mkRegGen 256 gens E) α 0 &&
      notCentVM (mkRegGen 256 gens E) α 2 && unitFixM (mkRegGen 256 gens E) α) = true := by
  set M := mkRegGen 256 gens E with hM
  set m := mR T IXP
  set inv := iR IVP
  set g := gR G
  have hN : M.N = 256 := rfl
  have hm : ∀ a b, M.m a b = m a b := fun a b =>
    m_eq_mK hd hE (IX := fun a => pg 9 (mask 9) IXP a)
      (fun a ha => ⟨(bind_parts hb ha).1, (bind_parts hb ha).2.1⟩) a b
  have hmf : M.m = m := funext fun a => funext fun b => hm a b
  have hinv : ∀ a, M.inv[a]! = inv a := fun a => by
    rw [inv_eq hd (INV := fun a => pg 9 (mask 9) IVP a) (fun a ha => ?_) a]
    · rfl
    · have h := bind_parts hb ha
      have e : iR IVP a = pg 9 (mask 9) IVP a := by unfold iR; rw [if_pos ha]
      rw [← e]
      exact ⟨h.2.2.1, by rw [hm]; exact h.2.2.2.1⟩
  have hg : ∀ j, M.g j = g j := fun j => by
    change (gens.map fun t => t[0]!)[j]! = gR G j
    unfold gR
    by_cases hj : j < 7
    · rw [if_pos hj, getElem!_pos _ _ (by simpa [hgs] using hj), Array.getElem_map,
        ← getElem!_pos gens j (by rw [hgs]; exact hj), (hG.2 j hj).1, unpack_get' (by omega)]
    · rw [if_neg hj, getElem!_neg _ _ (by simpa [hgs] using hj)]
      rfl
  have hT : TreeSpec M := hd.tree hgs
  have hord : ∀ i, M.order[i]! = oR T i := fun i => by
    unfold oR
    by_cases hi : i < 256
    · change (E.tabs.map fun t => t[0]!)[i]! = _
      rw [if_pos hi, hd.order_get hi, tabs_get hE hi, unpack_get' (by omega)]
    · rw [if_neg hi, getElem!_neg _ _ (by rw [hT.size_order]; exact hi)]
      rfl
  have hpar : ∀ i, M.parent[i]! = pR T PL i := fun i => by
    change (E.par.map fun q => (E.tabs[q]!)[0]!)[i]! = _
    rw [hd.parent_get]
    unfold pR
    by_cases hi : i < 256
    · have hp : E.par[i]! = parOf PL i := by
        subst hE
        rw [penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
      have hpl := (bind_parts hb hi).2.2.2.2
      rw [if_pos hi, hp, tabs_get hE hpl, unpack_get' (by omega)]
    · have hp : E.par[i]! = 0 := by
        subst hE
        rw [penumRec_eq, getElem!_neg _ _ (by simpa using hi)]
        rfl
      rw [if_neg hi, hp, hd.tab_zero_zero]
  have hlab : ∀ i, M.label[i]! = lR PL i := fun i => by
    change E.lab[i]! = _
    unfold lR
    by_cases hi : i < 256
    · subst hE
      rw [if_pos hi, penumRec_eq, getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
    · subst hE
      rw [if_neg hi, penumRec_eq, getElem!_neg _ _ (by simpa using hi)]
      rfl
  have hA : ∀ k P, autRecK m inv g T PL α k P = true → ∀ x, (autArr M α k)[x]! = aR P x := by
    intro k P hk x
    obtain ⟨h0, hr⟩ := autRec_parts hk
    unfold autArr
    rw [autMap_get hT (by rw [hN]; omega) _ h0 (fun i h0 hi => ?_) x]
    · unfold aR
      by_cases hx : x < 256
      · rw [hN, if_pos hx, if_pos hx]
      · rw [hN, if_neg hx, if_neg hx]
    · obtain ⟨-, -, -, hl, -⟩ := hT.step i h0 hi
      rw [hord, hpar, hm, tabImgs_get hm hinv hg (by omega) hl, hlab]
      exact hr i h0 hi
  simp only [Bool.and_eq_true] at ha hcl htw hnc
  obtain ⟨⟨ha0, ha1⟩, ha2⟩ := ha
  obtain ⟨⟨⟨cz, cv⟩, cu1⟩, cu2⟩ := hcl
  obtain ⟨⟨t0, t1⟩, t2⟩ := htw
  have hstep : ∀ gs : List ℕ, (∀ x ∈ gs, x < 256) → ∀ x ∈ gs, ∀ y < M.N, M.m y x < M.N := by
    intro gs hgs' x hx y hy
    exact (hd.rep).m_lt_of_lt hy (hgs' x hx)
  have hcl' : ∀ gs, clK m gs = true →
      (M.closure gs).size = 256 ∧ ∀ z, (M.closure gs)[z]! = bR m gs z := by
    intro gs hc
    obtain ⟨hgs', hfix⟩ := cl_parts hc
    have := closure_get (M := M) (K := 16) hgs' (hstep gs hgs') (by rw [hN]; omega)
      (by rw [hN, hmf]; exact hfix)
    rw [hN, hmf] at this
    exact ⟨this.1, this.2⟩
  have eZ : secZ M = M.closure (zGs g) := by
    unfold secZ zGs
    rw [hg]
  have eV : secV M = M.closure (vGs m g) := by
    unfold secV vGs
    rw [hg, hg, hg, pw_eq hm, hm]
  have eU1 : M.closure [M.pw (M.g 0) 2, M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)] =
      M.closure (u1Gs m g) := by
    unfold u1Gs
    simp only [hg, pw_eq hm, hm]
  have eU2 : M.closure [M.pw (M.g 0) 2,
      M.m (M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)) (M.g 0)] = M.closure (u2Gs m g) := by
    unfold u2Gs
    simp only [hg, pw_eq hm, hm]
  obtain ⟨zs, zg⟩ := hcl' _ cz
  obtain ⟨vs, vg⟩ := hcl' _ cv
  obtain ⟨u1s, u1g⟩ := hcl' _ cu1
  obtain ⟨u2s, u2g⟩ := hcl' _ cu2
  rw [← eZ] at zs zg
  rw [← eV] at vs vg
  rw [← eU1] at u1s u1g
  rw [← eU2] at u2s u2g
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [twM_eq hN hm hinv (hA 0 P0 ha0) zg]; exact t0
  · rw [twM_eq hN hm hinv (hA 1 P1 ha1) zg]; exact t1
  · rw [twM_eq hN hm hinv (hA 2 P2 ha2) zg]; exact t2
  · rw [sqVM_eq hN hm vs vg]; exact hsq
  · rw [eaCentM_eq hN hm vs vg]; exact hea
  · rw [pairFixM_eq hN hm hinv (hA 0 P0 ha0) (hA 1 P1 ha1)]; exact hpf
  · rcases Nat.lt_or_ge α 1 with h0 | h1
    · obtain rfl : α = 0 := by omega
      rfl
    · obtain rfl : α = 1 := by omega
      rw [graphM_eq hN hm hinv (hA 1 P1 ha1) vs vg (hg 0)]
      exact hgr rfl
  · rw [notCentVM_eq hN hm hinv (hA 0 P0 ha0) vs vg]; exact hnc.1
  · rw [notCentVM_eq hN hm hinv (hA 2 P2 ha2) vs vg]; exact hnc.2
  · rw [unitFixM_eq hN hm (hA 2 P2 ha2) u1s u1g u2s u2g]; exact huf

end CFSG.KC.ChengHeldS2

end

module

public import Certificates.Data.Kernel.LyBase.Check
public import CFSG.Certificates.Kernel.LyBenes.Sound
public import CFSG.Certificates.Kernel.LyGlue.WordPtSound
import CFSG.Certificates.Kernel.YModel.SchCard

public section

namespace CFSG.KC.LyBase

open Equiv CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel.Sem
  CFSG.KC.LyGlue CFSG.KC.LyBenes CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def jZ : Nat → List ℤ
  | 0 => [1]
  | 1 => [2]
  | 2 => [-2]
  | 3 => genZ 2
  | 4 => genZ 3
  | 5 => genZ 4
  | _ => []

@[expose] def wZ (w : List Nat) : List ℤ := w.flatMap jZ

theorem jC_eq : ∀ j : Nat, jC j = (jZ j).map lcode
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel
  | 4 => by decide +kernel
  | 5 => by decide +kernel
  | _ + 6 => rfl

theorem jZ_mem : ∀ (j : Nat), ∀ l ∈ jZ j, l ≠ 0 ∧ l.natAbs ≤ 2
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel
  | 4 => by decide +kernel
  | 5 => by decide +kernel
  | _ + 6 => fun _ h => absurd h List.not_mem_nil

theorem cdPtC_map (cF dF : Nat → Nat) (a : Nat) :
    ∀ ws : List ℤ, cdPtC cF dF (ws.map lcode) a = ws.foldr (fun l b => letPt cF dF l b) a
  | [] => rfl
  | l :: ws => by
    change strictN (cdPtC cF dF (ws.map lcode) a) (fun b => letE cF dF (lcode l) b) = _
    rw [strictN_eq, cdPtC_map cF dF a ws]
    rfl

theorem cdPtC_wG {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat)) (hc2 : Ly0.cG * Ly0.cG = 1)
    (hd3 : Ly0.dG ^ 3 = 1) (ws : List ℤ) (hws : ∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 2)
    (a : Fin Ly0.deg) : cdPtC cF dF (ws.map lcode) a = (Ly0.wG Ly0.gens0 ws a : Nat) := by
  rw [cdPtC_map, ← wptE_eq]
  exact wptE_wG hcF hdF hc2 hd3 ws hws a

theorem jwPt_wG {cF dF : Nat → Nat} (hcF : ∀ a : Fin Ly0.deg, cF a = (Ly0.cG a : Nat))
    (hdF : ∀ a : Fin Ly0.deg, dF a = (Ly0.dG a : Nat)) (hc2 : Ly0.cG * Ly0.cG = 1)
    (hd3 : Ly0.dG ^ 3 = 1) (w : List Nat) :
    ∀ a : Fin Ly0.deg, jwPt cF dF w a = (Ly0.wG Ly0.gens0 (wZ w) a : Nat) := by
  induction w with
  | nil =>
    intro a
    have e : wZ [] = [] := rfl
    change (a : Nat) = _
    rw [e, Ly0.wG_nil, Perm.one_apply]
  | cons j w ih =>
    intro a
    have e : wZ (j :: w) = jZ j ++ wZ w := by simp [wZ]
    change strictN (jwPt cF dF w a) (fun b => cdPtC cF dF (jC j) b) = _
    rw [strictN_eq, ih a, jC_eq, cdPtC_wG hcF hdF hc2 hd3 (jZ j) (jZ_mem j), e, Ly0.wG_append,
      Perm.mul_apply]

theorem fixAll_sound {cF dF : Nat → Nat} {w : List Nat} :
    ∀ bs : List Nat, fixAll cF dF bs w = true → ∀ b ∈ bs, jwPt cF dF w b = b
  | [], _, b, hb => absurd hb List.not_mem_nil
  | c :: bs, h, b, hb => by
    have h' : andB (Nat.beq (jwPt cF dF w c) c) (fixAll cF dF bs w) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Nat.eq_of_beq_eq_true h1
    · exact fixAll_sound bs h2 b hb

theorem bFix_sound {cF dF : Nat → Nat} {bs : List Nat} {r : List (Fin 6 × Bool)}
    (h : bFix cF dF bs r = true) :
    isBWord r = true ∧ ∀ b ∈ bs, jwPt cF dF (r.map letIdx) b = b := by
  obtain ⟨h1, h2⟩ := andB_true h
  exact ⟨h1, fixAll_sound bs h2⟩

theorem closeStep_cons (Ns : List Nat) (Ws : List (List Nat)) (X : Nat) :
    closeStep (Ns :: Ws) X = Nat.lor (closeStep Ws X) (netsApply 17 131072 1 Ns X) :=
  strictN_eq (closeStep Ws X) (fun Y => Nat.lor Y (netsApply 17 131072 1 Ns X))

theorem closeR_succ (Ws : List (List Nat)) (r X : Nat) :
    closeR Ws (r + 1) X = closeStep Ws (closeR Ws r X) :=
  strictN_eq (closeR Ws r X) (fun Y => closeStep Ws Y)

theorem testBit_netsApply17 {Ns : List Nat} (hv : ∀ N ∈ Ns, StagesValid 17 N) (X : Nat) {p : Nat}
    (hp : p < 2 ^ 17) : (netsApply 17 131072 1 Ns X).testBit p = X.testBit (compN 17 Ns p) := by
  have e := (acts_netsApply_one (k := 17) hv).2 X 0 (by decide) p hp
  simp only [Nat.mul_zero, Nat.zero_add] at e
  exact e

theorem closeStep_sound {P : Nat → Prop} : ∀ Ws : List (List Nat),
    (∀ Ns ∈ Ws, ∀ N ∈ Ns, StagesValid 17 N) →
    (∀ Ns ∈ Ws, ∀ p < 2 ^ 17, P (compN 17 Ns p) → P p) → ∀ X : Nat,
    (∀ p < 2 ^ 17, X.testBit p = true → P p) →
    ∀ p < 2 ^ 17, (closeStep Ws X).testBit p = true → P p
  | [], _, _, _, hX => hX
  | Ns :: Ws, hv, hP, X, hX => by
    intro p hp h
    rw [closeStep_cons, nlor, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact closeStep_sound Ws (fun M hM => hv M (List.mem_cons_of_mem _ hM))
        (fun M hM => hP M (List.mem_cons_of_mem _ hM)) X hX p hp h
    · have hv' := hv Ns List.mem_cons_self
      rw [testBit_netsApply17 hv' X hp] at h
      exact hP Ns List.mem_cons_self p hp
        (hX _ ((acts_netsApply_one (k := 17) hv').1 p hp) h)

theorem closeR_sound {Ws : List (List Nat)} (hv : ∀ Ns ∈ Ws, ∀ N ∈ Ns, StagesValid 17 N)
    {P : Nat → Prop} (hP : ∀ Ns ∈ Ws, ∀ p < 2 ^ 17, P (compN 17 Ns p) → P p) {X : Nat}
    (hX : ∀ p < 2 ^ 17, X.testBit p = true → P p) :
    ∀ r, ∀ p < 2 ^ 17, (closeR Ws r X).testBit p = true → P p
  | 0 => hX
  | r + 1 => by
    intro p hp h
    rw [closeR_succ] at h
    exact closeStep_sound Ws hv hP _ (closeR_sound hv hP hX r) p hp h

theorem compN_inj {k : Nat} : ∀ {Ns : List Nat}, (∀ N ∈ Ns, StagesValid k N) →
    ∀ {p q : Nat}, compN k Ns p = compN k Ns q → p = q
  | [], _, _, _, h => h
  | N :: Ns, hv, p, q, h => by
    have h' : benesPerm k N (compN k Ns p) = benesPerm k N (compN k Ns q) := h
    have e := congrArg (benesInv k N) h'
    rw [benesInv_benesPerm (hv N List.mem_cons_self),
      benesInv_benesPerm (hv N List.mem_cons_self)] at e
    exact compN_inj (fun M hM => hv M (List.mem_cons_of_mem _ hM)) e

theorem smul_mem_orbit' {n : Nat} {H : Subgroup (Perm (Fin n))} {β q : Fin n}
    (hq : q ∈ MulAction.orbit H β) (g : H) : g • q ∈ MulAction.orbit H β := by
  rw [← MulAction.orbit_eq_iff.mpr hq]
  exact MulAction.mem_orbit q g

theorem closeR_orbit {n : Nat} (H : Subgroup (Perm (Fin n))) {Ws : List (List Nat)}
    (hv : ∀ Ns ∈ Ws, ∀ N ∈ Ns, StagesValid 17 N)
    (hg : ∀ Ns ∈ Ws, ∃ g ∈ H, ∀ a : Fin n, compN 17 Ns a = (g a : Nat)) (r : Nat) (β : Fin n) :
    ∀ p < 2 ^ 17, (closeR Ws r (Nat.shiftLeft 1 β)).testBit p = true →
      ∃ hp : p < n, (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit H β := by
  refine closeR_sound hv (P := fun p => ∃ hp : p < n, (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit H β)
    ?_ ?_ r
  · intro Ns hNs p _ hq
    obtain ⟨hq, hmem⟩ := hq
    obtain ⟨g, hgH, hga⟩ := hg Ns hNs
    have e : compN 17 Ns (g⁻¹ ⟨compN 17 Ns p, hq⟩ : Fin n) = compN 17 Ns p := by
      rw [hga, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    have hpe := compN_inj (hv Ns hNs) e
    refine ⟨hpe ▸ (g⁻¹ ⟨compN 17 Ns p, hq⟩).2, ?_⟩
    have e2 : (⟨p, hpe ▸ (g⁻¹ ⟨compN 17 Ns p, hq⟩).2⟩ : Fin n) =
        (⟨g⁻¹, H.inv_mem hgH⟩ : H) • (⟨compN 17 Ns p, hq⟩ : Fin n) := Fin.ext hpe.symm
    rw [e2]
    exact smul_mem_orbit' hmem _
  · intro p _ h
    rw [nshl, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
    subst h
    exact ⟨β.2, MulAction.mem_orbit_self β⟩

theorem lyb_popMask_testBit {k i : Nat} (hi : i < k) (q : Nat) :
    (popMask (Nat.shiftLeft 1 k) i).testBit q = (decide (q < 2 ^ k) && !q.testBit i) := by
  have hL : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
  have hW : 2 ^ k = 2 ^ (i + 1) * 2 ^ (k - (i + 1)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hc : 2 ^ 2 ^ i - 1 < 2 ^ 2 ^ (i + 1) := by
    have h1 : 2 ^ 2 ^ i ≤ 2 ^ 2 ^ (i + 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 := Nat.two_pow_pos (2 ^ i)
    omega
  simp only [popMask, nmul, ndiv, nshl, ones_eq, Nat.one_shiftLeft, two_shl]
  rw [hW, geom_div hL, Nat.mul_comm, testBit_geom_mul hc, Nat.testBit_two_pow_sub_one]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, Nat.mod_mul]
  have h1 := Nat.mod_lt q (Nat.two_pow_pos i)
  rcases (by omega : q / 2 ^ i % 2 = 0 ∨ q / 2 ^ i % 2 = 1) with h | h
  · have e : q % 2 ^ i + 2 ^ i * (q / 2 ^ i % 2) < 2 ^ i := by
      rw [h]
      omega
    rw [decide_eq_true e, h]
    rfl
  · have e : ¬ q % 2 ^ i + 2 ^ i * (q / 2 ^ i % 2) < 2 ^ i := by
      rw [h]
      omega
    rw [decide_eq_false e, h]
    rfl

theorem lyb_popMask_eq {k i : Nat} (hi : i < k) :
    popMask (Nat.shiftLeft 1 k) i =
      Nat.xor (ones (CFSG.KC.YModel.wid k)) (idPlane (CFSG.KC.YModel.wid k) i) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [lyb_popMask_testBit hi, wid_eq, nxor, Nat.testBit_xor, CFSG.KC.YModel.Sch.testBit_ones',
    idPlane_testBit hi]
  cases decide (q < 2 ^ k) <;> cases q.testBit i <;> rfl

theorem lyb_rec_congr (z : Nat) (f g : Nat → Nat → Nat) (k : Nat)
    (h : ∀ j < k, ∀ a, f j a = g j a) : ∀ j, j ≤ k →
      (Nat.rec (motive := fun _ => Nat) z f j : Nat) = Nat.rec (motive := fun _ => Nat) z g j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    change f j (Nat.rec (motive := fun _ => Nat) z f j) = g j (Nat.rec (motive := fun _ => Nat) z g j)
    rw [ih (by omega), h j (by omega)]

theorem lyb_popc_eq (k X : Nat) :
    popc k X = CFSG.KC.YModel.popc k (Nat.land X (ones (Nat.shiftLeft 1 k))) := by
  unfold CFSG.KC.LyBase.popc CFSG.KC.YModel.popc
  refine lyb_rec_congr _ _ _ k (fun j hj a => ?_) k le_rfl
  beta_reduce
  rw [strictN_eq, strictN_eq, lyb_popMask_eq hj]

theorem popc_card (k X : Nat) :
    popc k X = ((Finset.range (2 ^ k)).filter fun p => X.testBit p = true).card := by
  have hY : Nat.land X (ones (Nat.shiftLeft 1 k)) < 2 ^ 2 ^ k := by
    rw [nland, ones_eq, nshl, Nat.one_shiftLeft]
    exact land_ones_lt X _
  rw [lyb_popc_eq, CFSG.KC.YModel.Sch.popc_eq k _ hY, Finset.card_filter]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [nland, ones_eq, nshl, Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    decide_eq_true hr, Bool.and_true]
  cases X.testBit r <;> rfl

theorem card_le_ncard {n : Nat} (A : Set (Fin n)) (β : Fin n) (S : Finset Nat)
    (hS : ∀ p ∈ S, ∃ hp : p < n, (⟨p, hp⟩ : Fin n) ∈ A) : S.card ≤ A.ncard := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun p => if hp : p < n then (⟨p, hp⟩ : Fin n) else β)
    ?_ ?_
  · intro p hp
    obtain ⟨hpn, hpA⟩ := hS p hp
    simp only [hpn, dite_true]
    exact hpA
  · intro p hp q hq e
    obtain ⟨hpn, _⟩ := hS p hp
    obtain ⟨hqn, _⟩ := hS q hq
    simp only [hpn, hqn, dite_true, Fin.mk.injEq] at e
    exact e

theorem orbitOK_sound {n : Nat} (H : Subgroup (Perm (Fin n))) {Ws : List (List Nat)}
    (hv : ∀ Ns ∈ Ws, ∀ N ∈ Ns, StagesValid 17 N)
    (hg : ∀ Ns ∈ Ws, ∃ g ∈ H, ∀ a : Fin n, compN 17 Ns a = (g a : Nat)) {r m : Nat} (β : Fin n)
    (h : orbitOK Ws r β m = true) : m ≤ (MulAction.orbit H β).ncard := by
  have h1 : m ≤ popc 17 (closeR Ws r (Nat.shiftLeft 1 β)) := Nat.le_of_ble_eq_true h
  rw [popc_card] at h1
  refine h1.trans (card_le_ncard _ β _ fun p hp => ?_)
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact closeR_orbit H hv hg r β p hp.1 hp.2

theorem not_mem_of_distinct {x : Nat} : ∀ xs : List Nat,
    (List.rec (motive := fun _ => Bool) true
      (fun y _ ih' => andB (notB (Nat.beq x y)) ih') xs : Bool) = true → x ∉ xs
  | [], _ => List.not_mem_nil
  | y :: ys, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    intro hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have : Nat.beq x x = true := Nat.beq_refl x
      rw [this] at h1
      exact absurd h1 (by decide)
    · exact not_mem_of_distinct ys h2 hx

theorem distinctN_nodup : ∀ O : List Nat, distinctN O = true → O.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    exact List.nodup_cons.2 ⟨not_mem_of_distinct xs h1, distinctN_nodup xs h2⟩

theorem treeOK_sound {cF dF : Nat → Nat} {Ws : List (List Nat)} {β m : Nat} {O : List Nat}
    {T : List (Nat × Nat)} (h : treeOK cF dF Ws β m O T = true) :
    O.Nodup ∧ m ≤ O.length ∧ ∀ P : Nat → Prop, P β →
      (∀ g a, P a → P (jwPt cF dF (Ws.getD g []) a)) → ∀ x ∈ O, P x := by
  obtain ⟨hA, hB⟩ := andB_true h
  obtain ⟨hA1, hA2⟩ := andB_true hA
  obtain ⟨hB1, hB2⟩ := andB_true hB
  obtain ⟨hB11, hB12⟩ := andB_true hB1
  have h0 : O.getD 0 0 = β := Nat.eq_of_beq_eq_true hB11
  have hlen : O.length = T.length + 1 := Nat.eq_of_beq_eq_true hB12
  have hE := recAll_right (P := edgeOK cF dF Ws O T) T.length hB2
  refine ⟨distinctN_nodup O hA1, Nat.le_of_ble_eq_true hA2, fun P hβ hstep => ?_⟩
  have key : ∀ i, i < O.length → P (O.getD i 0) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      cases i with
      | zero => rw [h0]; exact hβ
      | succ j =>
        obtain ⟨he1, he2⟩ := andB_true (hE j (by omega))
        have hp : (T.getD j (0, 0)).1 ≤ j := Nat.le_of_ble_eq_true he1
        rw [← Nat.eq_of_beq_eq_true he2]
        exact hstep _ _ (ih _ (by omega) (by omega))
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := key i hi
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem treeOK_orbit {cF dF : Nat → Nat} {n : Nat} (H : Subgroup (Perm (Fin n)))
    {Ws : List (List Nat)}
    (hg : ∀ g, ∃ x ∈ H, ∀ a : Fin n, jwPt cF dF (Ws.getD g []) a = (x a : Nat)) {β : Fin n}
    {m : Nat} {O : List Nat} {T : List (Nat × Nat)} (h : treeOK cF dF Ws β m O T = true) :
    m ≤ (MulAction.orbit H β).ncard := by
  obtain ⟨hnd, hm, hP⟩ := treeOK_sound h
  have hO := hP (fun p => ∃ hp : p < n, (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit H β)
    ⟨β.2, MulAction.mem_orbit_self β⟩ (by
      intro g a ⟨ha, hmem⟩
      obtain ⟨x, hxH, hxa⟩ := hg g
      rw [hxa ⟨a, ha⟩]
      refine ⟨(x ⟨a, ha⟩).2, ?_⟩
      exact smul_mem_orbit' hmem (⟨x, hxH⟩ : H))
  refine hm.trans ?_
  rw [← List.toFinset_card_of_nodup hnd]
  exact card_le_ncard _ β _ fun p hp => hO p (List.mem_toFinset.1 hp)

end CFSG.KC.LyBase

end

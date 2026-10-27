
module

public import Certificates.Data.Kernel.U6.Yamada
public import CFSG.Certificates.Kernel.U6Sound3010S
import all CFSG.Certificates.Kernel.U6Sound3010S

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def check3142K (LT : Nat) (aW : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length aW) (nat_lit 9)) (codesK (nat_lit 92) aW)) (check3142 LT aW)

end CFSG.KC.U6

end

namespace CFSG.KC.U6.Tk

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.U6.Snd CFSG.KC.U6.Pk
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.F4.Native (tvC normC)

set_option exponentiation.threshold 70000

theorem ap_toTable (g : Equiv.Perm (Fin 693)) {i : ℕ} (hi : i < 693) :
    ap (toTable g) i = (g ⟨i, hi⟩ : ℕ) := by
  rw [rep_toTable (n := 693) (by norm_num) g i hi, idx_of_lt _ hi]
  rfl

theorem tblEq_toTable {g h : Equiv.Perm (Fin 693)} (e : g = h) :
    tblEq 693 (toTable g) (toTable h) = true := by
  subst e
  exact tblEq_iff.2 fun _ _ => rfl

theorem commT_toTable {g h : Equiv.Perm (Fin 693)} (e : g * h = h * g) :
    commT 693 (toTable g) (toTable h) = true := by
  change tblEq 693 (compT 693 _ _) (compT 693 _ _) = true
  rw [tblEq_iff]
  intro i hi
  rw [Rep.compT (rep_toTable (by norm_num) g) (rep_toTable (by norm_num) h) i hi,
    Rep.compT (rep_toTable (by norm_num) h) (rep_toTable (by norm_num) g) i hi, e]

theorem fixedList_arrOf (g : Equiv.Perm (Fin 693)) :
    (CFSG.Certificates.Native.fixedList 693 (CFSG.EvenSmallLie.UnitarySix.arrOf g)).length =
      {p : Fin 693 | g p = p}.ncard := by
  have hr : CFSG.Monster.B.Co2.Rep 693 (CFSG.EvenSmallLie.UnitarySix.arrOf g) g := fun x => by
    rw [CFSG.EvenSmallLie.UnitarySix.arrOf, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ x.isLt]
  rw [← CFSG.Certificates.finSet_fixedList hr]
  have hP := CFSG.Certificates.pointList_fixedList (n := 693) (CFSG.EvenSmallLie.UnitarySix.arrOf g)
  generalize CFSG.Certificates.Native.fixedList 693 (CFSG.EvenSmallLie.UnitarySix.arrOf g) = l at hP ⊢
  have e : CFSG.Certificates.finSet 693 l = Fin.val ⁻¹' {x | x ∈ l} := rfl
  have hs : {x | x ∈ l} ⊆ Set.range (Fin.val : Fin 693 → ℕ) := fun x hx => ⟨⟨x, hP.lt x hx⟩, rfl⟩
  rw [e, Set.ncard_preimage_of_injective_subset_range Fin.val_injective hs]
  have e2 : {x | x ∈ l} = (l.toFinset : Set ℕ) := by
    ext x
    simp
  rw [e2, Set.ncard_coe_finset, List.toFinset_card_of_nodup hP.sorted.nodup]

theorem anyN_iff {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ m ih =>
    change CFSG.KLie.CT.orB (f m) (anyN m f) = true ↔ _
    rw [orB_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem orN_eq_sumN {w : ℕ} {f : ℕ → ℕ} : ∀ n, (∀ i < n, f i < 2 ^ w) →
    orN n (fun i => Nat.shiftLeft (f i) (Nat.mul w i)) =
      sumN n (fun i => Nat.shiftLeft (f i) (Nat.mul w i))
  | 0, _ => rfl
  | n + 1, hf => by
    have ih := orN_eq_sumN n fun i hi => hf i (by omega)
    have hb := (sumN_fld w f n fun i hi => hf i (by omega)).2
    change Nat.lor (Nat.shiftLeft (f n) (Nat.mul w n)) (orN n _) =
      Nat.add (Nat.shiftLeft (f n) (Nat.mul w n)) (sumN n _)
    rw [ih]
    exact (Nat.shiftLeft_add_eq_or_of_lt hb _).symm

theorem elt_orN {f : ℕ → ℕ} {n i : ℕ} (hf : ∀ i < n, f i >>> 6930 = 0) (hi : i < n) :
    elt (orN n fun i => Nat.shiftLeft (f i) (Nat.mul 6930 i)) i = f i := by
  have hf' : ∀ i < n, f i < 2 ^ 6930 := fun i hi => lt_of_shr (hf i hi)
  rw [elt, orN_eq_sumN n hf']
  exact sumN_get hf' hi

theorem rep_conjP {P Q : ℕ} {g h : Equiv.Perm (Fin 693)} (hP : Rep P g) (hQ : Rep Q h) :
    Rep (conjP P Q) (g * h * g⁻¹) :=
  rep_pc (rep_pc hP hQ) (rep_invP hP)

theorem eq_of_beq_rep {P Q : ℕ} {g h : Equiv.Perm (Fin 693)} (hP : Rep P g) (hQ : Rep Q h)
    (e : Nat.beq P Q = true) : g = h :=
  (rep_ext hP hQ).1 (beq_iff.1 e)

theorem comm_of_commP {P Q : ℕ} {g h : Equiv.Perm (Fin 693)} (hP : Rep P g) (hQ : Rep Q h)
    (e : commP P Q = true) : g * h = h * g :=
  eq_of_beq_rep (rep_pc hP hQ) (rep_pc hQ hP) e

theorem rep_K {LT : ℕ} {L : List (Equiv.Perm (Fin 693))} {kw : List (List ℤ)} {kW : List (List ℕ)}
    (hL : LetsBind L LT) (hkw : kw = kW.map (List.map decZ)) (hc : ∀ w ∈ kW, ∀ c ∈ w, c < 92) :
    (kGensG L kw).length = kW.length ∧
      ∀ j < (kGensG L kw).length, Rep (elt (evList LT kW) j) ((kGensG L kw).getD j 1) := by
  have hlen : (kGensG L kw).length = kW.length := by
    rw [kGensG, hkw, List.length_map, List.length_map]
  refine ⟨hlen, fun j hj => ?_⟩
  have := rep_gens hL kW hc j (hlen ▸ hj)
  rw [← hkw] at this
  exact this

theorem rep_words {S : ℕ} {gs : List (Equiv.Perm (Fin 693))}
    (hS : ∀ j < gs.length, Rep (elt S j) (gs.getD j 1)) {wz : List (List ℤ)} {ws : List (List ℕ)}
    (hwz : wz = ws.map (List.map decZ)) (hc : ∀ w ∈ ws, ∀ c ∈ w, c < 2 * gs.length) :
    ∀ i < ws.length, Rep (elt (evList S ws) i) (evalCodes gs (wz.getD i [])) := by
  intro i hi
  have h := rep_list hS ws hc i hi
  have hi' : i < wz.length := by rw [hwz, List.length_map]; exact hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at h
  rw [List.getD_eq_getElem _ _ hi']
  simp only [hwz, List.getElem_map] at h ⊢
  exact h

theorem tab_ap {UP POS : ℕ} {pts pos : Array ℕ} (hu : decA UP 12 693 = pts)
    (hp : decA POS 10 4096 = pos) {p q : ℕ} (hp' : p < 693) (hq : q < 693) :
    ((tvTabsG pts pos)[p]!).size = 693 ∧ ap (tvTabsG pts pos)[p]! q = tabK UP POS (up UP p) q := by
  subst hu hp
  have hT : (tvTabsG (decA UP 12 693) (decA POS 10 4096))[p]! =
      tvTableG (decA UP 12 693) (decA POS 10 4096) (up UP p) := by
    rw [tvTabsG, getElem!_pos _ p (by simpa using hp'), Array.getElem_ofFn]
    simp only
    rw [decA_get _ _ _ _ hp']
    rfl
  rw [hT]
  refine ⟨by simp [tvTableG], ?_⟩
  obtain ⟨en, bn⟩ := normK_eq (tvC (up UP p) (fget UP q 12))
  unfold ap
  rw [tvTableG, getElem!_pos _ q (by simpa using hq), Array.getElem_ofFn]
  simp only
  rw [decA_get _ _ _ _ hq, decA_get _ _ _ _ bn]
  have e : fget POS (normC (tvC (up UP p) (fget UP q 12))) 10 = tabK UP POS (up UP p) q := by
    change _ = fget POS (normK (tvK (up UP p) (fget UP q 12))) 10
    rw [tvK_eq, en]
  have hlt : tabK UP POS (up UP p) q < 2 ^ 32 := Nat.lt_trans (fget_lt _ _ 10) (by norm_num)
  rw [e, UInt32.toNat_ofNat_of_lt' hlt]

end CFSG.KC.U6.Tk

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native CFSG.EvenSmallLie.UnitarySix

set_option exponentiation.threshold 70000

theorem sound3000 {LT : Nat} {L : List (Equiv.Perm (Fin 693))} {aw kw ow sw : List (List ℤ)}
    {aW kW oW sW : List (List Nat)} (hL : LetsBind L LT)
    (haW : aw = aW.map (List.map decZ)) (hkW : kw = kW.map (List.map decZ))
    (hoW : ow = oW.map (List.map decZ)) (hsW : sw = sW.map (List.map decZ))
    (hlen : aW.length = 9 ∧ kW.length = 3 ∧ oW.length = 21 ∧ sW.length = 21)
    (hcodes : (∀ w ∈ aW ++ kW, ∀ c ∈ w, c < 92) ∧ ∀ w ∈ oW ++ sW, ∀ c ∈ w, c < 6)
    (hk : check3000 LT aW kW oW sW = true) :
    (commCheckG L aw kw = true) ∧ (transCheckG L aw kw ow sw = true) := by
  open Pk Snd Tk in
  obtain ⟨h9, h3, ho21, hs21⟩ := hlen
  obtain ⟨hcAK, hcOS⟩ := hcodes
  have hcA : ∀ w ∈ aW, ∀ c ∈ w, c < 92 := fun w hw => hcAK w (List.mem_append_left _ hw)
  have hcK : ∀ w ∈ kW, ∀ c ∈ w, c < 92 := fun w hw => hcAK w (List.mem_append_right _ hw)
  obtain ⟨hlenA, hA, hj1, hj2, -⟩ := rep_A hL haW h9 hcA
  obtain ⟨hlenK, hK⟩ := rep_K hL hkW hcK
  rw [h3] at hlenK
  have hAS : ∀ j < (aGensG L aw).length, Rep (elt (evList LT aW) j) ((aGensG L aw).getD j 1) :=
    fun j hj => hA j (hlenA ▸ hj)
  have rA : ∀ w : List ℕ, (∀ c ∈ w, c < 18) →
      Rep (evW (evList LT aW) w) (evalCodes (aGensG L aw) (w.map decZ)) := fun w hw =>
    rep_evW hAS w fun c hc => by rw [hlenA]; exact hw c hc
  have rK : ∀ w : List ℕ, (∀ c ∈ w, c < 6) →
      Rep (evW (evList LT kW) w) (evalCodes (kGensG L kw) (w.map decZ)) := fun w hw =>
    rep_evW hK w fun c hc => by rw [hlenK]; exact hw c hc
  have ra1 := rA [2, 4] (by decide)
  have ra2 := rA [4, 10] (by decide)
  have rk1 := rK [4] (by decide)
  have rk2 := rK [0, 4, 0, 4, 1, 4, 1] (by decide)
  have d1 : ([2, 4] : List ℕ).map decZ = [2, 3] := rfl
  have d2 : ([4, 10] : List ℕ).map decZ = [3, 6] := rfl
  have d3 : ([4] : List ℕ).map decZ = [3] := rfl
  have d4 : ([0, 4, 0, 4, 1, 4, 1] : List ℕ).map decZ = [1, 3, 1, 3, -1, 3, -1] := rfl
  rw [d1] at ra1
  rw [d2] at ra2
  rw [d3] at rk1
  rw [d4] at rk2
  have hcO : ∀ w ∈ oW, ∀ c ∈ w, c < 2 * (kGensG L kw).length := fun w hw c hc => by
    rw [hlenK]; exact hcOS w (List.mem_append_left _ hw) c hc
  have hcS : ∀ w ∈ sW, ∀ c ∈ w, c < 2 * (kGensG L kw).length := fun w hw c hc => by
    rw [hlenK]; exact hcOS w (List.mem_append_right _ hw) c hc
  have rG := rep_words hK hoW hcO
  have rS := rep_words hK hsW hcS
  rw [ho21] at rG
  rw [hs21] at rS
  have rO : ∀ i < 21, Rep (conjP (elt (evList (evList LT kW) oW) i) (elt (evList LT aW) 0))
      (orbitEltG L aw kw ow i) := fun i hi => rep_conjP (rG i hi) hj1
  have hO : ∀ i < 21, elt (orN 21 fun i => Nat.shiftLeft (conjP (elt (evList (evList LT kW) oW) i)
      (elt (evList LT aW) 0)) (Nat.mul 6930 i)) i =
        conjP (elt (evList (evList LT kW) oW) i) (elt (evList LT aW) 0) :=
    fun i hi => elt_orN (fun i hi => (rO i hi).1) hi
  unfold check3000 at hk
  simp only [strictB_eq, andB_iff] at hk
  obtain ⟨hc, htr⟩ := hk
  unfold transCore at htr
  rw [andB_iff] at htr
  obtain ⟨hgen, hstab⟩ := htr
  unfold commK at hc
  simp only [strictB_eq, andB_iff] at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have hrc : ∀ {P Q : ℕ} {a k : Equiv.Perm (Fin 693)}, Rep P a → Rep Q k →
      Rep (commutP P Q) (a * k * a⁻¹ * k⁻¹) := fun hP hQ =>
    rep_pc (rep_pc (rep_pc hP hQ) (rep_invP hP)) (rep_invP hQ)
  refine ⟨?_, ?_⟩
  · simp only [commCheckG, Bool.and_eq_true]
    refine ⟨⟨⟨commT_toTable (comm_of_commP rk1 hj1 c1), tblEq_toTable
      (eq_of_beq_rep (hrc ra1 rk1) hj1 c2)⟩, commT_toTable (comm_of_commP rk2 hj2 c3)⟩,
      tblEq_toTable (eq_of_beq_rep (hrc ra2 rk2) hj2 c4)⟩
  · simp only [transCheckG, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
      Bool.or_eq_true, beq_iff_eq]
    refine ⟨fun g hg i hi => ?_, fun m hm => ?_⟩
    ·
      obtain ⟨t, ht, hgt⟩ : ∃ t < 6, Rep (nIf(Nat.blt t 3, elt (evList LT kW) t,
          invP (elt (evList LT kW) (Nat.sub t 3)))) g := by
        rcases List.mem_append.1 hg with hg | hg
        · obtain ⟨j, hj, rfl⟩ := mem_getD hg
          refine ⟨j, by omega, ?_⟩
          rw [blt_iff.2 (by omega)]
          exact hK j hj
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
          obtain ⟨j, hj, rfl⟩ := mem_getD hx
          refine ⟨j + 3, by omega, ?_⟩
          have hb : Nat.blt (j + 3) 3 = false := by
            rw [Bool.eq_false_iff, Ne, blt_iff]
            omega
          rw [hb]
          change Rep (invP (elt (evList LT kW) (j + 3 - 3))) _
          rw [Nat.add_sub_cancel]
          exact rep_invP (hK j hj)
      have h1 := allN_iff.1 hgen t ht
      rw [strictB_eq, allN_iff] at h1
      have h2 := h1 i hi
      rw [strictB_eq, anyN_iff] at h2
      obtain ⟨j, hj, e⟩ := h2
      rw [hO i hi, hO j hj] at e
      exact ⟨j, hj, tblEq_toTable (eq_of_beq_rep (rep_conjP hgt (rO i hi)) (rO j hj) e)⟩
    · rw [strictB_eq, allN_iff] at hstab
      have h := hstab m hm
      rw [orB_iff, beq_iff, strictB_eq, andB_iff] at h
      rcases h with h | ⟨e1, e2⟩
      · exact Or.inl h
      · right
        rw [hO 1 (by norm_num), hO m hm] at e2
        exact ⟨commT_toTable (comm_of_commP (rS m hm) hj1 e1),
          tblEq_toTable (eq_of_beq_rep (rep_conjP (rS m hm) (rO 1 (by norm_num))) (rO m hm) e2)⟩

theorem sound3142 {LT : Nat} {L : List (Equiv.Perm (Fin 693))} {aw : List (List ℤ)}
    {aW : List (List Nat)} (hL : LetsBind L LT) (haw : aw = aW.map (List.map decZ))
    (hk : check3142K LT aW = true) :
    sumCheckG L aw = true := by
  open Pk Snd Tk in
  unfold check3142K check3142 at hk
  simp only [strictB_eq, andB_iff, beq_iff, codesK_iff] at hk
  obtain ⟨⟨h9, hc⟩, hf1, hf2⟩ := hk
  obtain ⟨hlenA, hA, -, -, hj3⟩ := rep_A hL haw h9 hc
  have hAS : ∀ j < (aGensG L aw).length, Rep (elt (evList LT aW) j) ((aGensG L aw).getD j 1) :=
    fun j hj => hA j (hlenA ▸ hj)
  have hc3 : Rep (elt (evList LT aW) 2) (c3G L aw) := by
    have e := rep_unique (rep_evW hAS [4] (by rw [hlenA]; decide))
      (rep_pc (hA 2 (by norm_num)) rep_ID)
    have d : ([4] : List ℕ).map decZ = [3] := rfl
    rw [d] at e
    rw [c3G, e, mul_one]
    exact hA 2 (by norm_num)
  have hjc : Rep (evW (evList LT aW) [0, 2, 8, 4]) (j3G L aw * c3G L aw) := by
    have r := rep_evW hAS [0, 2, 8, 4] (by rw [hlenA]; decide)
    have d : ([0, 2, 8, 4] : List ℕ).map decZ = [1, 2, 5, 3] := rfl
    rw [d] at r
    have e : evalCodes (aGensG L aw) [1, 2, 5, 3] = j3G L aw * c3G L aw := by
      simp [j3G, c3G, evalCodes, mul_assoc]
    rwa [e] at r
  simp only [sumCheckG, Bool.and_eq_true, beq_iff_eq]
  rw [fixedList_arrOf, fixedList_arrOf, ← fixK_eq hc3, ← fixK_eq hjc]
  exact ⟨hf1, hf2⟩

end CFSG.KC.U6

end

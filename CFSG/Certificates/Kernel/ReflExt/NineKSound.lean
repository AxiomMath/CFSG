module

public import Certificates.Data.Kernel.ReflExt.NineK
public import Certificates.Data.CFSGNative.NineAll.Check
public import CFSG.Certificates.Kernel.ReflExt.ReflExtKSound
public import CFSG.Certificates.Kernel.TwoNodeSmall.WitKSound

public section

namespace CFSG.ReflExt.NK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.LaneSound
  CFSG.TwoNodeSmall.PosBK CFSG.TwoNodeSmall.PosBK.OKS CFSG.ReflExt CFSG.ReflExt.RXK CFSG.NineAll

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace NS

open Snd (decR)

theorem takeK_eq {α : Type} : ∀ (l : List α) (k : Nat), takeK l k = l.take k
  | [], k => by cases k <;> rfl
  | _ :: _, 0 => rfl
  | x :: l, k + 1 => by
    change x :: takeK l k = _
    rw [takeK_eq l k]
    rfl

theorem slc_eq {α : Type} (s k : Nat) (l : List α) : slc s k l = (l.drop (k * s)).take s := by
  unfold slc
  rw [dropK_eq, takeK_eq]
  rfl

theorem getElem_slc {α : Type} {s k : Nat} {l : List α} {j : Nat} (hj : j < (slc s k l).length) :
    ∃ h : k * s + j < l.length, (slc s k l)[j] = l[k * s + j] := by
  have hj' := hj
  simp only [slc_eq, List.length_take, List.length_drop] at hj'
  refine ⟨by omega, ?_⟩
  simp only [slc_eq, List.getElem_take, List.getElem_drop]

theorem lt_slc {α : Type} {s : Nat} (hs : 0 < s) {l : List α} {i : Nat} (hi : i < l.length) :
    i % s < (slc s (i / s) l).length := by
  have h1 := Nat.div_add_mod' i s
  have h2 := Nat.mod_lt i hs
  simp only [slc_eq, List.length_take, List.length_drop]
  omega

theorem mem_slc {α : Type} {s : Nat} (hs : 0 < s) {l : List α} {i : Nat} (hi : i < l.length) :
    l[i] ∈ slc s (i / s) l := by
  have h1 := Nat.div_add_mod' i s
  obtain ⟨h, e⟩ := getElem_slc (lt_slc hs hi)
  have e2 : l[i / s * s + i % s] = l[i] := by congr 1
  rw [← e2, ← e]
  exact List.getElem_mem _

theorem all2_slc {α β : Type} {f : α → β → Bool} {l1 : List α} {l2 : List β} {s K : Nat}
    (hs : 0 < s) (hK : l1.length ≤ K * s) (h : ∀ k < K, all2 f (slc s k l1) (slc s k l2) = true) :
    ∀ i (hi : i < l1.length), ∃ h2 : i < l2.length, f l1[i] l2[i] = true := by
  intro i hi
  have h1 := Nat.div_add_mod' i s
  have hk : i / s < K := (Nat.div_lt_iff_lt_mul hs).2 (by omega)
  obtain ⟨hl, hp⟩ := Snd.all2_spec f _ _ (h _ hk)
  have j1 := lt_slc hs hi
  have j2 : i % s < (slc s (i / s) l2).length := by rw [← hl]; exact j1
  obtain ⟨b1, e1⟩ := getElem_slc j1
  obtain ⟨b2, e2⟩ := getElem_slc j2
  have hf := hp _ j1 j2
  rw [e1, e2] at hf
  have hi2 : i < l2.length := by omega
  refine ⟨hi2, ?_⟩
  have q1 : l1[i / s * s + i % s] = l1[i] := by congr 1
  have q2 : l2[i / s * s + i % s] = l2[i] := by congr 1
  rw [q1, q2] at hf
  exact hf

@[expose] def fillL {α : Type} (c : α → Bool) (L : List α) : List α :=
  match L.find? c with
  | none => []
  | some x => L.map fun y => bif c y then y else x

theorem fill_mem {α : Type} {c : α → Bool} {L : List α} {y : α} (h : y ∈ fillL c L) :
    y ∈ L ∧ c y = true := by
  unfold fillL at h
  split at h
  · simp at h
  · rename_i x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    cases hcz : c z
    · simp only [cond_false]
      exact ⟨List.mem_of_find?_eq_some hx, List.find?_some hx⟩
    · simp only [cond_true]
      exact ⟨hz, hcz⟩

theorem fill_get {α : Type} {c : α → Bool} {L : List α} {j : Nat} (hj : j < L.length)
    (hc : c L[j] = true) : (fillL c L)[j]? = some L[j] := by
  unfold fillL
  split
  · rename_i hn
    rw [List.find?_eq_none] at hn
    exact absurd hc (hn _ (List.getElem_mem hj))
  · rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    simp [hc]

theorem allI_spec {α : Type} (f : Nat → α → Bool) : ∀ (l : List α) (i : Nat),
    allI f l i = true → ∀ j (hj : j < l.length), f (i + j) l[j] = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | x :: l, i, h, j, hj => by
    change (f i x && allI f l (Nat.succ i)) = true at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := allI_spec f l (Nat.succ i) h.2 j (by simpa using hj)
      rw [show i + (j + 1) = Nat.succ i + j by omega]
      exact this

theorem natrec_and (b : Nat → Bool) : ∀ D,
    Nat.rec (motive := fun _ => Bool) true (fun j ih => b j && ih) D = true → ∀ j < D, b j = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | D + 1, h, j, hj => by
    change (b D && Nat.rec (motive := fun _ => Bool) true (fun j ih => b j && ih) D) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_or_ge j D with hjD | hjD
    · exact natrec_and b D h.2 j hjD
    · obtain rfl : j = D := by omega
      exact h.1

theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')

theorem bltF {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

variable {P : Pt}

theorem ptX_eq (P : Pt) (ex : List (Nat × Nat)) (b : Nat) :
    ptX P ex b = withBound (withExtra P (ex.map (decR P.D))) b := by
  have e : (fun r : Nat × Nat => (⟨(upk P.D r.2).reverse, upk P.D r.1⟩ : Refl)) = decR P.D := by
    funext r
    rfl
  unfold ptX
  rw [e]

theorem negV_negV (D : Nat) (v : Vec) {i : Nat} (hi : i < D) :
    ln (negV D (negV D v)) i = ln v i := by
  rw [negV_ln D _ hi, negV_ln D _ hi]
  have := ln_le v i
  omega

theorem packR_negneg (hp : P.p = 3) (z : Refl) :
    packR P (Snd.negRf P.D (Snd.negRf P.D z)) = packR P z := by
  rw [Snd.packR3 hp, Snd.packR3 hp]
  simp only [Snd.negRf]
  rw [pk_eq, pk_eq, pkr_eq, pkr_eq]
  unfold fw rv
  congr 1
  · apply enc_map_congr
    intro i hi
    exact negV_negV P.D _ (List.mem_range.mp hi)
  · apply enc_map_congr
    intro i hi
    exact negV_negV P.D _ (List.mem_range.mp (List.mem_reverse.mp hi))

theorem negP_negP (hp : P.p = 3) (z : Refl) :
    negP (fdB 3 P.D) P.D (negP (fdB 3 P.D) P.D (packR P z)) = packR P z := by
  rw [Snd.negP_packR hp, Snd.negP_packR hp, packR_negneg hp]

theorem eqP_refl (a : Nat × Nat) : eqP a a = true := by
  unfold eqP
  simp

theorem eqPM_canon (hp : P.p = 3) {a : Nat × Nat} {z : Refl}
    (h : eqPM (fdB 3 P.D) P.D a (packR P z) = true) :
    canP P.D a = true ∧ eqPM (fdB 3 P.D) P.D (packR P z) (packR P (decR P.D a)) = true := by
  unfold eqPM at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have ha : a = packR P z := by
      unfold eqP at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      exact Prod.ext h.1 h.2
    subst ha
    refine ⟨Snd.canP_packR hp z, ?_⟩
    rw [Snd.packR_decR hp (Snd.canP_packR hp z)]
    unfold eqPM
    rw [eqP_refl]
    rfl
  · have ha : a = packR P (Snd.negRf P.D z) := by
      unfold eqP at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      rw [← Snd.negP_packR hp]
      exact Prod.ext h.1 h.2
    subst ha
    refine ⟨Snd.canP_packR hp _, ?_⟩
    rw [Snd.packR_decR hp (Snd.canP_packR hp _)]
    unfold eqPM
    rw [Snd.negP_packR hp, packR_negneg hp, eqP_refl, Bool.or_true]

theorem canon_facts (hp : P.p = 3) (hD : P.D ≤ 10) {a : Nat × Nat} (hca : canP P.D a = true)
    (hrf : reflOK (fdB 3 P.D) a = true) :
    packR P (decR P.D a) = a ∧ P.dotv (decR P.D a).f (decR P.D a).h = 2 := by
  have hr := Snd.packR_decR hp hca
  refine ⟨hr, ?_⟩
  rw [← hr, Snd.packR3 hp, reflOK_pk hp hD] at hrf
  exact hrf

theorem fix_of_pack (hp : P.p = 3) (hD : P.D ≤ 10) {y : Refl}
    (h : Nat.beq (dotK (fdB 3 P.D) (packR P y).2 (pk P.D P.x)) 0 = true) : P.dotv y.f P.x = 0 := by
  rw [Snd.packR3 hp, Nat.beq_eq] at h
  exact (dotK_pk hp hD y.f P.x).symm.trans h

theorem dotv_zero_of (hp : P.p = 3) [Fact P.p.Prime] {f g : Vec} (ε : ZMod P.p)
    (hv : P.vec f = ε • P.vec g) (h0 : P.dotv g P.x = 0) : P.dotv f P.x = 0 := by
  have e : ((P.dotv f P.x : Nat) : ZMod P.p) = ((0 : Nat) : ZMod P.p) := by
    rw [Pt.dotv_spec, hv, smul_dot, ← Pt.dotv_spec, h0]
    simp
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by rw [hp]; exact dotv_lt hp _ _),
    Nat.zero_mod] at e
  exact e

theorem negR_eq (hp : P.p = 3) (r : Refl) : negR P r = Snd.negRf P.D r := by
  unfold negR Snd.negRf negV
  rw [hp]

theorem negV_canon (D : Nat) (v : Vec) : (negV D v).length = D ∧ ∀ x ∈ negV D v, x < 3 := by
  refine ⟨by simp [negV], ?_⟩
  intro x hx
  simp only [negV, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  omega

theorem decR_negRf (hp : P.p = 3) (r : Refl) :
    decR P.D (packR P (Snd.negRf P.D r)) = Snd.negRf P.D r :=
  Snd.decR_packR_self hp (negV_canon _ _).1 (negV_canon _ _).1 (negV_canon _ _).2
    (negV_canon _ _).2

theorem negRf_congr (hp : P.p = 3) {r s : Refl} (h : packR P r = packR P s) :
    Snd.negRf P.D r = Snd.negRf P.D s := by
  have e1 := Snd.decR_packR_h hp r
  have e2 := Snd.decR_packR_h hp s
  have e3 := Snd.decR_packR_f hp r
  have e4 := Snd.decR_packR_f hp s
  rw [h] at e1 e3
  rw [e1] at e2
  rw [e3] at e4
  unfold Snd.negRf negV
  congr 1
  · apply List.map_congr_left
    intro i hi
    have := congrArg (fun l => l.getD i 0) e4
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (List.mem_range.mp hi), Option.map_some, Option.getD_some, ln] at this
    simp only [List.getD_eq_getElem?_getD]
    rw [this]
  · apply List.map_congr_left
    intro i hi
    have := congrArg (fun l => l.getD i 0) e2
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (List.mem_range.mp hi), Option.map_some, Option.getD_some, ln] at this
    simp only [List.getD_eq_getElem?_getD]
    rw [this]

open Classical in
@[expose] noncomputable def witB (Q : Pt) (k : Nat) : Witness :=
  if h1 : ∃ t, verify Q (.transv t) = true ∧ k = 1 then .transv (Classical.choose h1)
  else if h2 : ∃ o, verify Q (.order o) = true ∧ k = 2 then .order (Classical.choose h2)
  else if h3 : ∃ c, verify Q (.weyl c) = true then .weyl (Classical.choose h3)
  else .kernel []

theorem witB_bad {Q : Pt} {r : WitK.Rec} (h : chkPt Q r = true) (hk : r.1 = 1 ∨ r.1 = 2) :
    isBadW (witB Q r.1) = true ∧ verify Q (witB Q r.1) = true := by
  obtain ⟨-, h1, h2, -⟩ := chkPt_verifyK Q r h
  unfold witB
  rcases hk with hk | hk
  · obtain ⟨t, ht⟩ := h1 hk
    have hx : ∃ t, verify Q (.transv t) = true ∧ r.1 = 1 := ⟨t, ht, hk⟩
    rw [dif_pos hx]
    exact ⟨rfl, (Classical.choose_spec hx).1⟩
  · obtain ⟨o, ho⟩ := h2 hk
    have hn : ¬ ∃ t, verify Q (.transv t) = true ∧ r.1 = 1 := fun ⟨_, _, e⟩ => by omega
    have hx : ∃ o, verify Q (.order o) = true ∧ r.1 = 2 := ⟨o, ho, hk⟩
    rw [dif_neg hn, dif_pos hx]
    exact ⟨rfl, (Classical.choose_spec hx).1⟩

theorem witB_weyl {Q : Pt} {r : WitK.Rec} (h : chkPt Q r = true) (hk : r.1 = 3) :
    ∃ c, witB Q r.1 = .weyl c ∧ verify Q (.weyl c) = true := by
  obtain ⟨-, -, -, h3⟩ := chkPt_verifyK Q r h
  have hx := h3 hk
  have hn1 : ¬ ∃ t, verify Q (.transv t) = true ∧ r.1 = 1 := fun ⟨_, _, e⟩ => by omega
  have hn2 : ¬ ∃ o, verify Q (.order o) = true ∧ r.1 = 2 := fun ⟨_, _, e⟩ => by omega
  unfold witB
  rw [dif_neg hn1, dif_neg hn2, dif_pos hx]
  exact ⟨_, rfl, Classical.choose_spec hx⟩

@[expose] noncomputable def rootsD (P : Pt) (Dl : List CE) : List Root :=
  Dl.flatMap fun x => [Snd.rt P x, Snd.rtN P x]

@[expose] noncomputable def obT (D ty : Nat) (cd : List (Nat × Nat)) (tg : List (List Nat)) :
    List OEnt :=
  (cd.zip tg).flatMap fun ct => match ct.2 with
    | t :: j :: u => bif Nat.beq t ty then [⟨decR D ct.1, u, j⟩] else []
    | _ => []

@[expose] noncomputable def mk0 (P : Pt) (B : Nat) (rp : NK.Rep0) : NineAll.Rep0 :=
  ⟨decR P.D rp.1, witB (ptX P [rp.1] B) rp.2.1⟩

@[expose] noncomputable def mk2 (P : Pt) (a : Nat × Nat) (q : NK.Rep0) : NineAll.Rep2 :=
  ⟨decR P.D q.1, witB (ptX P [a, q.1] P.bound) q.2.1⟩

@[expose] noncomputable def cn {β : Type} (D : Nat) (rp : (Nat × Nat) × β) : Bool := canP D rp.1

@[expose] noncomputable def mk1 (P : Pt) (cd : List (Nat × Nat)) (rp : Rep1) : NRep :=
  { r := decR P.D rp.1
    kind := if rp.2.1 = 0 then .cent else .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1)
    roots := rootsD (withExtra P [decR P.D rp.1])
      (cloD (withExtra P [decR P.D rp.1]) (baseD (withExtra P [decR P.D rp.1])) rp.2.2.2.1)
    reps2 := (fillL (cn P.D) rp.2.2.2.2.1).map (mk2 P rp.1)
    orb2 := Snd.ob2 P.D cd rp.2.2.2.2.2 }

theorem mem_obT {D ty : Nat} {cd : List (Nat × Nat)} {tg : List (List Nat)} {i : Nat}
    (h1 : i < cd.length) (h2 : i < tg.length) {j : Nat} {u : List Nat}
    (ht : tg[i] = ty :: j :: u) : (⟨decR D cd[i], u, j⟩ : OEnt) ∈ obT D ty cd tg := by
  unfold obT
  refine List.mem_flatMap.mpr ⟨(cd[i], tg[i]), List.mem_iff_getElem.mpr
    ⟨i, by simp [h1, h2], by simp⟩, ?_⟩
  simp only [ht, Nat.beq_refl, cond_true]
  simp

theorem of_mem_obT {D ty : Nat} {cd : List (Nat × Nat)} {tg : List (List Nat)} {e : OEnt}
    (he : e ∈ obT D ty cd tg) : ∃ i, ∃ (h1 : i < cd.length) (h2 : i < tg.length), ∃ j u,
      tg[i] = ty :: j :: u ∧ e = ⟨decR D cd[i], u, j⟩ := by
  unfold obT at he
  obtain ⟨ct, hct, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hct
  rw [List.length_zip] at hi
  have h1 : i < cd.length := by omega
  have h2 : i < tg.length := by omega
  refine ⟨i, h1, h2, ?_⟩
  simp only [List.getElem_zip] at he
  rcases ht : tg[i] with _ | ⟨t, _ | ⟨j, u⟩⟩
  · rw [ht] at he
    simp at he
  · rw [ht] at he
    simp at he
  · rw [ht] at he
    cases hb : Nat.beq t ty
    · simp [hb] at he
    · simp only [hb, cond_true, List.mem_singleton] at he
      rw [Nat.eq_of_beq_eq_true hb]
      exact ⟨j, u, rfl, he⟩

theorem tagN_cases {F : Fd} {D n nC X : Nat} {G C : List (Nat × Nat)} {R0 : List NK.Rep0}
    {R1 : List Rep1} {c : Nat × Nat} {t : List Nat} (h : tagN F D n nC X G C R0 R1 c t = true) :
    (∃ j, t = [0, j] ∧ dotK F c.2 X = 0 ∧ j < nC ∧ eqPM F D c (nthK (0, 0) C j) = true) ∨
    (∃ j u, t = 1 :: j :: u ∧ dotK F c.2 X = 0 ∧ j < R0.length ∧ ltAll n u = true ∧
      eqPM F D (nthK r00 R0 j).1 (cw F G u c) = true) ∨
    (∃ j u, t = 2 :: j :: u ∧ dotK F c.2 X ≠ 0 ∧ j < R1.length ∧ ltAll n u = true ∧
      eqPM F D (nthK r10 R1 j).1 (cw F G u c) = true) := by
  match t, h with
  | [], h => exact absurd h Bool.false_ne_true
  | [_], h => exact absurd h Bool.false_ne_true
  | 0 :: j :: u, h =>
    have h' : (Nat.beq (dotK F c.2 X) 0 && u.isEmpty && Nat.blt j nC &&
        eqPM F D c (nthK (0, 0) C j)) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, List.isEmpty_iff] at h'
    obtain ⟨⟨⟨h1, rfl⟩, h3⟩, h4⟩ := h'
    exact Or.inl ⟨j, rfl, h1, h3, h4⟩
  | 1 :: j :: u, h =>
    have h' : (Nat.beq (dotK F c.2 X) 0 && Nat.blt j R0.length && ltAll n u &&
        eqPM F D (nthK r00 R0 j).1 (cw F G u c)) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
    exact Or.inr (Or.inl ⟨j, u, rfl, h1, h2, h3, h4⟩)
  | 2 :: j :: u, h =>
    have h' : (Nat.beq 2 2 && !(Nat.beq (dotK F c.2 X) 0) && Nat.blt j R1.length && ltAll n u &&
        eqPM F D (nthK r10 R1 j).1 (cw F G u c)) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true'] at h'
    obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := h'
    refine Or.inr (Or.inr ⟨j, u, rfl, ?_, h2, h3, h4⟩)
    intro e
    rw [e] at h1
    exact absurd h1 (by decide)
  | (k + 3) :: j :: u, h =>
    have h' : (Nat.beq (k + 3) 2 && !(Nat.beq (dotK F c.2 X) 0) && Nat.blt j R1.length &&
        ltAll n u && eqPM F D (nthK r10 R1 j).1 (cw F G u c)) = true := h
    rw [beqF (by omega)] at h'
    exact absurd h' (by simp)

theorem tag2N_cases {F : Fd} {D n1 nC2 X : Nat} {G1 C2 : List (Nat × Nat)} {Q : List NK.Rep0}
    {c : Nat × Nat} {t0 k : Nat} {w : List Nat}
    (h : tag2N F D n1 nC2 X G1 C2 Q c (t0, k, w) = true) :
    (t0 = 0 ∧ k < nC2 ∧ eqPM F D c (nthK (0, 0) C2 k) = true) ∨
    (t0 = 1 ∧ k < nC2 ∧ bne (Nat.beq (dotK F c.2 (nthK (0, 0) C2 k).1) 0)
      (Nat.beq (dotK F (nthK (0, 0) C2 k).2 c.1) 0) = true) ∨
    (t0 = 2 ∧ k < Q.length ∧ ltAll n1 w = true ∧
      eqPM F D (nthK r00 Q k).1 (cw F G1 w c) = true) ∨
    (t0 = 3 ∧ dotK F c.2 X = 0) := by
  match t0, h with
  | 0, h =>
    have h' : (Nat.blt k nC2 && eqPM F D c (nthK (0, 0) C2 k)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inl ⟨rfl, h'⟩
  | 1, h =>
    have h' : (Nat.blt k nC2 && bne (Nat.beq (dotK F c.2 (nthK (0, 0) C2 k).1) 0)
        (Nat.beq (dotK F (nthK (0, 0) C2 k).2 c.1) 0)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inr (Or.inl ⟨rfl, h'⟩)
  | 2, h =>
    have h' : (Nat.blt k Q.length && ltAll n1 w &&
        eqPM F D (nthK r00 Q k).1 (cw F G1 w c)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    exact Or.inr (Or.inr (Or.inl ⟨rfl, h'.1.1, h'.1.2, h'.2⟩))
  | 3, h =>
    have h' : (Nat.beq 3 3 && Nat.beq (dotK F c.2 X) 0) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h'.2⟩))
  | t0 + 4, h =>
    have h' : (Nat.beq (t0 + 4) 3 && Nat.beq (dotK F c.2 X) 0) = true := h
    rw [beqF (by omega)] at h'
    exact absurd h' (by simp)

theorem bkK_of {F : Fd} {D N : Nat} {R : List (Nat × Nat)} :
    ∀ (bk : List (Nat × List Nat × List Nat)) (prev : Nat) (sf sh : Nat × Nat × Bool),
      bkS N bk prev sf sh = true →
      (∀ b ∈ bk, allK (fun k => Nat.beq (mskF F R (pkrC D k)) b.1) b.2.1 = true ∧
        allK (fun k => Nat.beq (mskH F R (pkC D k)) b.1) b.2.2 = true) →
      bkK F D N R bk prev sf sh = true
  | [], _, _, _, h, _ => h
  | b :: bk, prev, sf, sh, h, hm => by
    change (Nat.ble prev b.1 && bkS N bk (Nat.succ b.1) (addC N b.2.1 sf) (addC N b.2.2 sh)) = true
      at h
    change (Nat.ble prev b.1 && allK (fun k => Nat.beq (mskF F R (pkrC D k)) b.1) b.2.1 &&
      allK (fun k => Nat.beq (mskH F R (pkC D k)) b.1) b.2.2 &&
      bkK F D N R bk (Nat.succ b.1) (addC N b.2.1 sf) (addC N b.2.2 sh)) = true
    rw [Bool.and_eq_true] at h
    obtain ⟨m1, m2⟩ := hm b (by simp)
    rw [h.1, m1, m2, bkK_of bk _ _ _ h.2 (fun b' hb' => hm b' (by simp [hb']))]
    rfl

theorem cand_mem2 (hp : P.p = 3) (hD : P.D ≤ 10) {ys zs : List Refl} (hsub : ∀ ρ ∈ ys, ρ ∈ zs)
    {bk : List (Nat × List Nat × List Nat)} {cd : List (Nat × Nat)}
    (hbk : bkK (fdB 3 P.D) P.D (Nat.pow 3 P.D) (ys.map (packR P)) bk 0 (0, 0, true)
      (0, 0, true) = true)
    (hcd : candOK (fdB 3 P.D) P.D bk cd = true) {c : Refl} (hc : c ∈ candList P zs) :
    decR P.D (packR P c) = c ∧ packR P c ∈ cd := by
  unfold candList at hc
  simp only [List.mem_flatMap, List.mem_map, List.mem_filterMap] at hc
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := hc
  split at hab
  case isFalse => exact absurd hab (by simp)
  case isTrue hcond =>
  obtain rfl := Option.some.inj hab
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨hm, hd2⟩ := hcond
  rw [hp] at hd2
  rw [hp] at ha hb
  obtain ⟨ka, hka, rfl⟩ := Snd.mem_allVecsP _ a ha
  obtain ⟨kb, hkb, rfl⟩ := Snd.mem_allVecsP _ b hb
  obtain ⟨hpw, -, hmF, hmH, hcF, hcH⟩ := Snd.bkK_spec _ _ _ _ bk 0 _ _ [] [] hbk
    (Snd.inv_init _) (Snd.inv_init _)
  obtain ⟨b1, hb1, hk1⟩ := (hcF ka hka).resolve_left (by simp)
  obtain ⟨b2, hb2, hk2⟩ := (hcH kb hkb).resolve_left (by simp)
  have e1 := hmF b1 hb1 ka hk1
  have e2 := hmH b2 hb2 kb hk2
  have e3 : mskF (fdB 3 P.D) (ys.map (packR P)) (pkrC P.D ka) =
      mskH (fdB 3 P.D) (ys.map (packR P)) (pkC P.D kb) := by
    apply Snd.msk_eq
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (hsub ρ hρ)
    have := congrArg (fun l => l.getD i false) hm
    simp only [maskF, maskH, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at this
    rw [Snd.packR3 hp, Snd.pkrC_dig, Snd.pkC_dig]
    simp only [dotK_pk hp hD]
    rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq, ← beq_iff_eq, this, beq_iff_eq]
  have hb12 : b1 = b2 := Snd.pw_unique hpw hb1 hb2 (by rw [← e1, ← e2, e3])
  subst hb12
  refine ⟨Snd.decR_packR_self hp (Snd.dig_length _ _) (Snd.dig_length _ _) (Snd.dig_lt _ _)
    (Snd.dig_lt _ _), ?_⟩
  rw [Snd.candOK_spec hcd]
  have hmem := Snd.mem_prodB_of (F := fdB 3 P.D) (D := P.D) hb1 hk1 hk2 (by
    rw [Snd.pkrC_dig, Snd.pkC_dig, dotK_pk hp hD, hd2]
    rfl)
  rw [Snd.pkC_dig, Snd.pkrC_dig] at hmem
  rw [Snd.packR3 hp]
  exact hmem

theorem roots_ok (hp : P.p = 3) [Fact P.p.Prime] (hWF : P.WF) {x : CE} (hx : Sem P x) :
    ∀ ρ ∈ [Snd.rt P x, Snd.rtN P x], wfR P ρ.r = true ∧ realizes P ρ.w ρ.r = true ∧
      (P.dotv (decR P.D (packR P x.1)).f P.x = 0 → P.dotv ρ.r.f P.x = 0) := by
  have h2 := Snd.sem_wf hWF hx
  intro ρ hρ
  rcases List.mem_cons.mp hρ with rfl | hρ
  · obtain ⟨hf, hh⟩ := Snd.vec_decR hp x.1
    refine ⟨Snd.wfR_of_dot hp ?_, Snd.real_pos hWF hx _ hf hh, fun h => h⟩
    change P.dot (P.vec (decR P.D (packR P x.1)).f) (P.vec (decR P.D (packR P x.1)).h) = 2
    rw [hf, hh]
    exact h2
  · rw [List.mem_singleton] at hρ
    subst hρ
    obtain ⟨hf, hh⟩ := Snd.vec_decR hp (Snd.negRf P.D x.1)
    have hf' : P.vec (decR P.D (packR P (Snd.negRf P.D x.1))).f = -P.vec x.1.f := by
      rw [hf]
      exact Snd.vec_negV hp x.1.f
    have hh' : P.vec (decR P.D (packR P (Snd.negRf P.D x.1))).h = -P.vec x.1.h := by
      rw [hh]
      exact Snd.vec_negV hp x.1.h
    refine ⟨Snd.wfR_of_dot hp ?_, Snd.real_neg hWF hx _ hf' hh', fun h => ?_⟩
    · change P.dot (P.vec (decR P.D (packR P (Snd.negRf P.D x.1))).f)
        (P.vec (decR P.D (packR P (Snd.negRf P.D x.1))).h) = 2
      rw [hf', hh', Snd.dot_neg_neg]
      exact h2
    · change P.dotv (decR P.D (packR P (Snd.negRf P.D x.1))).f P.x = 0
      obtain ⟨hf0, -⟩ := Snd.vec_decR hp x.1
      refine dotv_zero_of hp (-1) ?_ h
      rw [hf', hf0, neg_one_smul]

theorem centOK_of (hp : P.p = 3) (hD : P.D ≤ 10) {t : Refl}
    (h : centK (fdB 3 P.D) P.D (P.gens.map (packR P)) (packR P t) = true) : centOK P t = true := by
  unfold centK at h
  unfold centOK
  rw [Snd.allK_spec] at h
  rw [List.all_eq_true]
  intro g hg
  have hg' := natrec_and _ P.D (h _ (List.mem_map.mpr ⟨g, hg, rfl⟩))
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.mp hj
  have := hg' j hj'
  rw [Nat.beq_eq, shiftLeft_unit P hj', Snd.packR3 hp, Snd.packR3 hp, appK_pk hp hD, appK_pk hp hD,
    appK_pk hp hD, appK_pk hp hD, pk_inj hp] at this
  exact this

theorem lt_of_get {α : Type} {l : List α} {j : Nat} {a : α} (h : l[j]? = some a) : j < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

theorem gens_nth (P : Pt) : ∀ l < (P.gens.map (packR P)).length,
    nthK (0, 0) (P.gens.map (packR P)) l = packR P (P.gens.getD l ⟨[], []⟩) := by
  intro l hl
  rw [List.length_map] at hl
  rw [nthK_eq', List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem dotK_packR (hp : P.p = 3) (hD : P.D ≤ 10) (y : Refl) :
    dotK (fdB 3 P.D) (packR P y).2 (pk P.D P.x) = P.dotv y.f P.x := by
  rw [Snd.packR3 hp]
  exact dotK_pk hp hD y.f P.x

end NS

open NS

open Snd (decR) in
theorem partN_verify (P : Pt) (B : Nat) (d : FDN) (h : ∀ i < 20, partN P B d i = true) :
    ∃ T, verifyAllN P B T = true := by
  obtain ⟨rows, bk, cd, tg, R0, R1⟩ := d
  have h0 := h 0 (by norm_num)
  have h9 := h 9 (by norm_num)
  have h14 := h 14 (by norm_num)
  have h15 := h 15 (by norm_num)
  unfold partN at h0 h9 h14 h15
  simp only [Nat.beq_refl, cond_true, beqF (by norm_num : (9 : Nat) ≠ 0),
    beqF (by norm_num : (14 : Nat) ≠ 0), beqF (by norm_num : (15 : Nat) ≠ 0),
    beqF (by norm_num : (14 : Nat) ≠ 9), beqF (by norm_num : (15 : Nat) ≠ 9),
    beqF (by norm_num : (15 : Nat) ≠ 14), bltF (by norm_num : ¬ (9 : Nat) < 9),
    bltF (by norm_num : ¬ (14 : Nat) < 9), bltF (by norm_num : ¬ (15 : Nat) < 9),
    bltF (by norm_num : ¬ (14 : Nat) < 14), bltF (by norm_num : ¬ (15 : Nat) < 14),
    cond_false] at h0 h9 h14 h15
  have hmsk : ∀ k < 8, mskB (ptF P) P.D (cloE (gensK P) rows)
      (slc (Nat.succ (Nat.div bk.length 8)) k bk) = true := by
    intro k hk
    have := h (k + 1) (by omega)
    unfold partN at this
    simp only [beqF (by omega : k + 1 ≠ 0), cond_false,
      Nat.blt_eq.mpr (by omega : k + 1 < 9), cond_true] at this
    exact this
  have htg : ∀ k < 4, all2 (tagN (ptF P) P.D (gensK P).length (Nat.add (gensK P).length rows.length)
      (pk P.D P.x) (gensK P) (cloE (gensK P) rows) R0 R1)
      (slc (Nat.succ (Nat.div cd.length 4)) k cd) (slc (Nat.succ (Nat.div cd.length 4)) k tg) =
      true := by
    intro k hk
    have := h (k + 10) (by omega)
    unfold partN at this
    simp only [beqF (by omega : k + 10 ≠ 0), beqF (by omega : k + 10 ≠ 9), cond_false,
      bltF (by omega : ¬ k + 10 < 9), Nat.blt_eq.mpr (by omega : k + 10 < 14), cond_true] at this
    exact this
  have hs2 : ∀ r < 4, allI (fun j rp => bne (Nat.beq (Nat.mod j 4) r) true || !(needs2 rp) ||
      s2N P (ptF P) (gensK P) (pk P.D P.x) cd rp) R1 0 = true := by
    intro r hr
    have := h (r + 16) (by omega)
    unfold partN at this
    simp only [beqF (by omega : r + 16 ≠ 0), beqF (by omega : r + 16 ≠ 9),
      beqF (by omega : r + 16 ≠ 14), beqF (by omega : r + 16 ≠ 15), cond_false,
      bltF (by omega : ¬ r + 16 < 9), bltF (by omega : ¬ r + 16 < 14),
      Nat.blt_eq.mpr (by omega : r + 16 < 20), Bool.true_and] at this
    exact this
  change (Nat.beq P.p 3 && Nat.ble 1 P.D && Nat.ble P.D 9 && allK (reflOK (fdB 3 P.D)) (gensK P) &&
      allK (fun g => Nat.beq (dotK (fdB 3 P.D) g.2 (pk P.D P.x)) 0) (gensK P) &&
      cloP (fdB 3 P.D) (gensK P).length (gensK P) rows (gensK P).length 0 (cloE (gensK P) rows) &&
      allK (fun r => Nat.beq (dotK (fdB 3 P.D) r.2 (pk P.D P.x)) 0) (cloE (gensK P) rows) &&
      bkS (Nat.pow 3 P.D) bk 0 (0, 0, true) (0, 0, true)) = true at h0
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, -⟩, hD9⟩, hrefl⟩, hGX⟩, hclo⟩, hX⟩, hbkS⟩ := h0
  have hD : P.D ≤ 10 := by omega
  have hfact : Fact P.p.Prime := ⟨by rw [hp]; norm_num⟩
  have hL := laneOK_three hp hD
  have hgk := Snd.gensK_eq hp
  change candOK (fdB 3 P.D) P.D bk cd = true at h9
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
    Nat.beq (dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x)) 0 && recBad (ptX P [rp.1] B) rp.2) R0 = true at h14
  change allK (fun rp => reflOK (fdB 3 P.D) rp.1 &&
      !(Nat.beq (dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x)) 0) &&
      (bif Nat.beq rp.2.1 0 then centK (fdB 3 P.D) P.D (gensK P) rp.1
       else (Nat.beq rp.2.2.1.1 1 || Nat.beq rp.2.2.1.1 2 || Nat.beq rp.2.2.1.1 3) &&
         chkPt (ptX P [rp.1] P.bound) rp.2.2.1)) R1 = true at h15
  unfold ptF at hmsk htg hs2
  rw [hgk] at hrefl hGX hclo hX hmsk htg h15 hs2
  have hrefl' := (Snd.allK_spec _ _).mp hrefl
  have hWF : P.WF := by
    intro g hg
    have := hrefl' (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [Snd.packR3 hp, reflOK_pk hp hD] at this
    exact Snd.WF_of_dotv this
  have hwfP := Snd.wfCheck_of_WF hp hWF
  rw [List.length_map] at hclo
  obtain ⟨hDl, hsem⟩ := Snd.clo_spec hL rows hclo
  have hC : cloE (P.gens.map (packR P)) rows =
      ((cloD P (baseD P) rows).map fun x => decR P.D (packR P x.1)).map (packR P) := by
    refine hDl.symm.trans ?_
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact (Snd.packR_decR hp (Snd.canP_packR hp x.1)).symm
  have hnC : Nat.add (P.gens.map (packR P)).length rows.length =
      (cloD P (baseD P) rows).length := by
    have := congrArg List.length hDl
    simp only [List.length_map, List.length_append] at this
    rw [List.length_map]
    exact this.symm
  rw [hC] at hX hmsk htg
  rw [hnC] at htg
  set Dl := cloD P (baseD P) rows with hDl_def
  set ys := Dl.map fun x => decR P.D (packR P x.1) with hys
  have hbk : bkK (fdB 3 P.D) P.D (Nat.pow 3 P.D) (ys.map (packR P)) bk 0 (0, 0, true)
      (0, 0, true) = true := by
    apply bkK_of bk 0 _ _ hbkS
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hs : 0 < Nat.succ (Nat.div bk.length 8) := Nat.succ_pos _
    have hk : i / Nat.succ (Nat.div bk.length 8) < 8 := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      change i < 8 * Nat.succ (bk.length / 8)
      omega
    have hm := hmsk _ hk
    unfold mskB at hm
    have := (Snd.allK_spec _ _).mp hm _ (mem_slc hs hi)
    rw [Bool.and_eq_true] at this
    exact this
  have hcdE : ∀ x ∈ cd, packR P (decR P.D x) = x ∧ P.dotv (decR P.D x).f (decR P.D x).h = 2 :=
    fun x hx => Snd.cd_entry hp hD h9 hx
  have htag := all2_slc (Nat.succ_pos _)
    (by change cd.length ≤ 4 * Nat.succ (cd.length / 4); omega) htg
  set T : NTables := ⟨rootsD P Dl, obT P.D 1 cd tg, (fillL (cn P.D) R0).map (mk0 P B),
    obT P.D 2 cd tg, (fillL (cn P.D) R1).map (mk1 P cd)⟩ with hT
  have hsub : ∀ ρ ∈ ys, ρ ∈ T.roots.map (·.r) := by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hρ
    exact List.mem_map.mpr ⟨Snd.rt P x,
      (List.mem_flatMap.mpr ⟨x, hx, by simp⟩ : Snd.rt P x ∈ rootsD P Dl), rfl⟩
  have hcandL : ∀ c ∈ candOfN P T, decR P.D (packR P c) = c ∧ packR P c ∈ cd :=
    fun c hc => cand_mem2 hp hD hsub hbk h9 hc
  have hcanR : ∀ (i : Nat) (hi : i < cd.length) (u : List Nat) (a : Nat × Nat),
      ltAll (P.gens.map (packR P)).length u = true →
      eqPM (fdB 3 P.D) P.D a (cw (fdB 3 P.D) (P.gens.map (packR P)) u cd[i]) = true →
      canP P.D a = true ∧ realizes (withExtra P [decR P.D cd[i]])
        (u ++ [P.gens.length] ++ u.reverse) (decR P.D a) = true := by
    intro i hi u a hu heq
    obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
    have hu' := Snd.ltAll_spec _ u hu
    rw [← hpe, Snd.cw_pack hL _ _ (gens_nth P) u hu'] at heq
    obtain ⟨hca, heq'⟩ := eqPM_canon hp heq
    refine ⟨hca, Snd.conj_real hp hD hWF _ _ hde u (by simpa using hu) ?_⟩
    rw [Snd.cw_pack hL _ _ (gens_nth P) u hu']
    exact heq'
  have hR0 : ∀ rp ∈ R0, reflOK (fdB 3 P.D) rp.1 = true ∧
      dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x) = 0 ∧ (rp.2.1 = 1 ∨ rp.2.1 = 2) ∧
      chkPt (ptX P [rp.1] B) rp.2 = true := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp h14 rp hrp
    simp only [recBad, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have hR1 : ∀ rp ∈ R1, reflOK (fdB 3 P.D) rp.1 = true ∧
      dotK (fdB 3 P.D) rp.1.2 (pk P.D P.x) ≠ 0 ∧
      (rp.2.1 = 0 → centK (fdB 3 P.D) P.D (P.gens.map (packR P)) rp.1 = true) ∧
      (rp.2.1 ≠ 0 → (rp.2.2.1.1 = 1 ∨ rp.2.2.1.1 = 2 ∨ rp.2.2.1.1 = 3) ∧
        chkPt (ptX P [rp.1] P.bound) rp.2.2.1 = true) := by
    intro rp hrp
    have := (Snd.allK_spec _ _).mp h15 rp hrp
    rw [Bool.and_eq_true, Bool.and_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [e] at h2
      exact absurd h2 (by decide)
    · rw [e] at h3
      exact h3
    · rw [beqF e, cond_false, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq,
        Nat.beq_eq, Nat.beq_eq] at h3
      obtain ⟨hk, hc⟩ := h3
      exact ⟨by omega, hc⟩
  have hv0 : vFixN P = true := by
    unfold vFixN
    rw [List.all_eq_true]
    intro g hg
    have := (Snd.allK_spec _ _).mp hGX (packR P g) (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [beq_iff_eq]
    exact fix_of_pack hp hD this
  have hv1 : vRootsN P T = true := by
    unfold vRootsN
    rw [List.all_eq_true]
    intro ρ hρ
    have hρ' : ρ ∈ rootsD P Dl := hρ
    obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
    obtain ⟨hw, hr, hfx⟩ := roots_ok hp hWF (hsem x hx) ρ hρx
    have hfix : P.dotv (decR P.D (packR P x.1)).f P.x = 0 := by
      have := (Snd.allK_spec _ _).mp hX (packR P (decR P.D (packR P x.1)))
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩)
      exact fix_of_pack hp hD this
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hw, hr⟩, hfx hfix⟩
  have hv2 : vCover0 P T (candOfN P T) = true := by
    unfold vCover0
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hfx⟩ := hc'
    rw [beq_iff_eq] at hfx
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨hi', ht⟩ := htag i hi
    have hfxK : dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) = 0 := by
      rw [hci, dotK_packR hp hD, hfx]
    rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true]
    rcases tagN_cases ht with ⟨j, -, -, hj, heq⟩ | ⟨j, u, htj, -, -, -, -⟩ | ⟨j, u, -, hm, -⟩
    · left
      have hjl : j < ys.length := by rw [hys, List.length_map]; exact hj
      rw [Snd.nthK_map _ _ hjl] at heq
      have hyj : packR P ys[j] = packR P Dl[j].1 := by
        simp only [hys, List.getElem_map]
        exact Snd.packR_decR hp (Snd.canP_packR hp _)
      rw [hyj] at heq
      unfold eqPM at heq
      rw [Bool.or_eq_true] at heq
      unfold eqP at heq
      simp only [Bool.and_eq_true, Nat.beq_eq] at heq
      rcases heq with heq | heq
      · refine ⟨Snd.rt P Dl[j], (List.mem_flatMap.mpr ⟨Dl[j], List.getElem_mem _, by simp⟩ :
          Snd.rt P Dl[j] ∈ rootsD P Dl), ?_⟩
        have e : cd[i] = packR P Dl[j].1 := Prod.ext heq.1 heq.2
        change reqb (decR P.D (packR P Dl[j].1)) c = true
        rw [← e, hci, hdc]
        exact Snd.reqb_self c
      · refine ⟨Snd.rtN P Dl[j], (List.mem_flatMap.mpr ⟨Dl[j], List.getElem_mem _, by simp⟩ :
          Snd.rtN P Dl[j] ∈ rootsD P Dl), ?_⟩
        have e : cd[i] = packR P (Snd.negRf P.D Dl[j].1) :=
          (Prod.ext heq.1 heq.2).trans (Snd.negP_packR hp _)
        change reqb (decR P.D (packR P (Snd.negRf P.D Dl[j].1))) c = true
        rw [← e, hci, hdc]
        exact Snd.reqb_self c
    · right
      refine ⟨⟨decR P.D cd[i], u, j⟩, mem_obT hi hi' htj, ?_⟩
      change reqb (decR P.D cd[i]) c = true
      rw [hci, hdc]
      exact Snd.reqb_self c
    · exact absurd hfxK hm
  have hv3 : vCover1 P T (candOfN P T) = true := by
    unfold vCover1 movingOf
    rw [List.all_eq_true]
    intro c hc'
    rw [List.mem_filter] at hc'
    obtain ⟨hc', hmv⟩ := hc'
    obtain ⟨hdc, hcm⟩ := hcandL c hc'
    obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨hi', ht⟩ := htag i hi
    have hmK : dotK (fdB 3 P.D) cd[i].2 (pk P.D P.x) ≠ 0 := by
      rw [hci, dotK_packR hp hD]
      simpa using hmv
    rw [List.any_eq_true]
    rcases tagN_cases ht with ⟨j, -, h0', -⟩ | ⟨j, u, -, h0', -⟩ | ⟨j, u, htj, -, -⟩
    · exact absurd h0' hmK
    · exact absurd h0' hmK
    · refine ⟨⟨decR P.D cd[i], u, j⟩, mem_obT hi hi' htj, ?_⟩
      change reqb (decR P.D cd[i]) c = true
      rw [hci, hdc]
      exact Snd.reqb_self c
  have hv4 : T.orb0.all (entry0OK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ obT P.D 1 cd tg := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    obtain ⟨hi'', ht⟩ := htag i hi
    rw [hju] at ht
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩ | ⟨j', u', e1, -⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, hreal⟩ := hcanR i hi u _ hu heq
      have hget : T.reps0[j]? = some (mk0 P B R0[j]) := by
        change ((fillL (cn P.D) R0).map (mk0 P B))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      obtain ⟨-, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      unfold entry0OK
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      exact hreal
    · exact absurd (List.cons.inj e1).1 (by decide)
  have hv5 : T.reps0.all (rep0OK P B) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ (fillL (cn P.D) R0).map (mk0 P B) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hmem, hca⟩ := fill_mem hrp
    obtain ⟨hrf, hfx, hk, hchk⟩ := hR0 rp hmem
    obtain ⟨hpr, hd2⟩ := canon_facts hp hD hca hrf
    obtain ⟨hbad, hver⟩ := witB_bad hchk hk
    unfold rep0OK verifyBad
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨Snd.wfR_of_dotv hp hd2, ?_⟩, hbad, hver⟩
    change P.dotv (decR P.D rp.1).f P.x = 0
    rw [← dotK_packR hp hD, hpr]
    exact hfx
  have hv6 : T.orb1.all (entry1OK P T) = true := by
    rw [List.all_eq_true]
    intro e he
    have he' : e ∈ obT P.D 2 cd tg := he
    obtain ⟨i, hi, hi', j, u, hju, rfl⟩ := of_mem_obT he'
    obtain ⟨hi'', ht⟩ := htag i hi
    rw [hju] at ht
    rcases tagN_cases ht with ⟨j', e1, -⟩ | ⟨j', u', e1, -⟩ | ⟨j', u', e1, -, hj, hu, heq⟩
    · exact absurd (List.cons.inj e1).1 (by decide)
    · exact absurd (List.cons.inj e1).1 (by decide)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (List.cons.inj e1).2
      rw [nthK_eq', List.getD_eq_getElem _ _ hj] at heq
      obtain ⟨hca, hreal⟩ := hcanR i hi u _ hu heq
      have hget : T.reps[j]? = some (mk1 P cd R1[j]) := by
        change ((fillL (cn P.D) R1).map (mk1 P cd))[j]? = _
        rw [List.getElem?_map, fill_get hj hca]
        rfl
      obtain ⟨-, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
      unfold entry1OK
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
      rw [hget]
      exact hreal
  have hst : ∀ rp ∈ R1, canP P.D rp.1 = true → needs2 rp = true →
      verifyStage2N P (candOfN P T) (mk1 P cd rp) = true ∧
      (rp.2.1 = 0 → centRootsOK P (decR P.D rp.1) (mk1 P cd rp).roots = true) := by
    intro rp hrp hca hn2
    obtain ⟨hrf, -, -, -⟩ := hR1 rp hrp
    obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hrp
    have hs := allI_spec _ R1 0 (hs2 (j % 4) (Nat.mod_lt _ (by norm_num))) j hj
    rw [Nat.zero_add, hjr] at hs
    have e1 : Nat.beq (Nat.mod j 4) (j % 4) = true := Nat.beq_refl _
    rw [e1, hn2] at hs
    have hs' : s2N P (fdB 3 P.D) (P.gens.map (packR P)) (pk P.D P.x) cd rp = true := hs
    obtain ⟨a, kd, rc, ro, Qs, tg2⟩ := rp
    unfold s2N at hs'
    simp only [Bool.and_eq_true] at hs'
    obtain ⟨⟨⟨hclo2, hcen⟩, hQ⟩, hall2⟩ := hs'
    dsimp only at hca hrf hcen hQ hall2 hclo2 ⊢
    obtain ⟨hr, hd2⟩ := canon_facts hp hD hca hrf
    set P1 := withExtra P [decR P.D a] with hP1
    have hWF1 : P1.WF := Snd.wf_extra hWF (Snd.WF_of_dotv hd2)
    have hfact1 : Fact P1.p.Prime := hfact
    have hL1 := laneOK_three (P := P1) hp hD
    have hG1 : P1.gens.map (packR P1) = P.gens.map (packR P) ++ [a] := by
      change (P.gens ++ [decR P.D a]).map (packR P) = _
      rw [List.map_append, List.map_singleton, hr]
    rw [← hG1] at hclo2 hall2 hcen
    rw [List.length_map] at hclo2
    obtain ⟨hDl2, hsem2⟩ := Snd.clo_spec hL1 ro hclo2
    set Dl2 := cloD P1 (baseD P1) ro with hDl2_def
    have hC2 : cloE (P1.gens.map (packR P1)) ro = Dl2.map (fun x => packR P1 x.1) := hDl2.symm
    rw [hC2] at hall2 hcen
    have hlen2 : Nat.add (P1.gens.map (packR P1)).length ro.length = Dl2.length := by
      have := congrArg List.length hDl2
      simp only [List.length_map, List.length_append] at this
      rw [List.length_map]
      exact this.symm
    rw [hlen2] at hall2
    obtain ⟨hl12, hall⟩ := Snd.all2_spec _ cd tg2 hall2
    refine ⟨?_, ?_⟩
    · unfold verifyStage2N
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      ·
        unfold s2RootsN
        rw [List.all_eq_true]
        intro ρ hρ
        have hρ' : ρ ∈ rootsD P1 Dl2 := hρ
        obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
        obtain ⟨hw, hre, -⟩ := roots_ok (P := P1) hp hWF1 (hsem2 x hx) ρ hρx
        rw [Bool.and_eq_true]
        exact ⟨hw, hre⟩
      ·
        unfold s2RepsN
        rw [List.all_eq_true]
        intro q' hq'
        have hq'' : q' ∈ (fillL (cn P.D) Qs).map (mk2 P a) := hq'
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq''
        obtain ⟨hqm, hqc⟩ := fill_mem hq
        have hq1 := (Snd.allK_spec _ _).mp hQ q hqm
        simp only [recBad, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hq1
        obtain ⟨hqr, hqk, hqchk⟩ := hq1
        obtain ⟨-, hqd⟩ := canon_facts hp hD hqc hqr
        obtain ⟨hbad, hver⟩ := witB_bad hqchk hqk
        unfold verifyBad
        simp only [Bool.and_eq_true]
        exact ⟨Snd.wfR_of_dotv hp hqd, hbad, hver⟩
      ·
        unfold s2OrbN
        rw [List.all_eq_true]
        intro x hx
        have hx' : x ∈ Snd.ob2 P.D cd tg2 := hx
        obtain ⟨i, hi, hi2, k, w, htg2, rfl⟩ := Snd.of_mem_ob2 hx'
        have ht2 := hall i hi hi2
        rw [htg2] at ht2
        rcases tag2N_cases ht2 with h' | h' | ⟨-, hk, hw, heq⟩ | h'
        all_goals first | exact absurd h'.1 (by norm_num) | skip
        obtain ⟨hpe, hde⟩ := hcdE cd[i] (List.getElem_mem hi)
        rw [nthK_eq', List.getD_eq_getElem _ _ hk] at heq
        have hw' := Snd.ltAll_spec _ w hw
        have hpe1 : packR P1 (decR P1.D cd[i]) = cd[i] := hpe
        rw [← hpe1, Snd.cw_pack hL1 _ _ (gens_nth P1) w hw'] at heq
        obtain ⟨hqc, heq'⟩ := eqPM_canon (P := P1) hp heq
        have hget : (mk1 P cd (a, kd, rc, ro, Qs, tg2)).reps2[k]? = some (mk2 P a Qs[k]) := by
          change ((fillL (cn P.D) Qs).map (mk2 P a))[k]? = _
          rw [List.getElem?_map, fill_get hk hqc]
          rfl
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨Snd.wfR_of_dotv hp hde, lt_of_get hget⟩, ?_⟩
        rw [hget]
        change realizes (withExtra P [decR P.D a, decR P.D cd[i]])
          (w ++ [P.gens.length + 1] ++ w.reverse) (decR P.D Qs[k].1) = true
        rw [← Snd.withExtra_two]
        have hlen : P.gens.length + 1 = P1.gens.length := by simp [hP1]
        rw [hlen]
        apply Snd.conj_real (P := P1) hp hD hWF1 _ _ hde w (by simpa using hw)
        rw [Snd.cw_pack hL1 _ _ (gens_nth P1) w hw']
        exact heq'
      ·
        rw [List.all_eq_true]
        intro c hc'
        unfold movingOf at hc'
        rw [List.mem_filter] at hc'
        obtain ⟨hc', hmv⟩ := hc'
        obtain ⟨hdc, hcm⟩ := hcandL c hc'
        obtain ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp hcm
        have hi2 : i < tg2.length := by omega
        have ht2 := hall i hi hi2
        rcases htg2 : tg2[i] with ⟨t0, k, w⟩
        rw [htg2, hci] at ht2
        unfold s2CandN asymAny
        simp only [Bool.or_eq_true, List.any_eq_true]
        rcases tag2N_cases ht2 with ⟨-, hk, heq⟩ | ⟨-, hk, has⟩ | ⟨h2, -, -, -⟩ | ⟨-, hfx⟩
        · simp only [Snd.nthK_map _ _ hk] at heq
          unfold eqPM eqP at heq
          simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at heq
          refine Or.inl (Or.inl ?_)
          rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · have he : packR P c = packR P1 Dl2[k].1 := Prod.ext e1 e2
            refine ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
              ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
            change reqb c (decR P.D (packR P1 Dl2[k].1)) = true
            rw [← he, hdc]
            exact Snd.reqb_self c
          · have he : packR P c = packR P1 (Snd.negRf P1.D Dl2[k].1) :=
              (Prod.ext e1 e2).trans (Snd.negP_packR (P := P1) hp _)
            refine ⟨(Snd.rtN P1 Dl2[k]).r, List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
              ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩
            change reqb c (decR P.D (packR P1 (Snd.negRf P1.D Dl2[k].1))) = true
            rw [← he, hdc]
            exact Snd.reqb_self c
        · simp only [Snd.nthK_map _ _ hk] at has
          have hpr : packR P1 Dl2[k].1 = packR P (decR P.D (packR P1 Dl2[k].1)) :=
            (Snd.packR_decR hp (Snd.canP_packR (P := P1) hp _)).symm
          rw [hpr] at has
          simp only [Snd.packR3 hp, dotK_pk hp hD, Snd.nbeq] at has
          refine Or.inl (Or.inr ⟨(Snd.rt P1 Dl2[k]).r, List.mem_map.mpr ⟨_,
            List.mem_flatMap.mpr ⟨Dl2[k], List.getElem_mem hk, by simp [hP1]⟩, rfl⟩, ?_⟩)
          exact has
        · refine Or.inr ⟨⟨decR P.D cd[i], w, k⟩, Snd.mem_ob2 hi hi2 (by rw [htg2, h2]), ?_⟩
          change reqb (decR P.D cd[i]) c = true
          rw [hci, hdc]
          exact Snd.reqb_self c
        · exfalso
          rw [dotK_packR hp hD] at hfx
          rw [hfx] at hmv
          exact absurd hmv (by decide)
    ·
      intro hk0
      rw [hk0] at hcen
      have hcen' : allK (fun e => eqPM (fdB 3 P.D) P.D e a ||
          Nat.beq (dotK (fdB 3 P.D) e.2 (pk P.D P.x)) 0) (Dl2.map fun x => packR P1 x.1) = true :=
        hcen
      unfold centRootsOK
      rw [List.all_eq_true]
      intro ρ hρ
      have hρ' : ρ ∈ rootsD P1 Dl2 := hρ
      obtain ⟨x, hx, hρx⟩ := List.mem_flatMap.mp hρ'
      have hce := (Snd.allK_spec _ _).mp hcen' (packR P1 x.1) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      have hneg : negR P (decR P.D a) = Snd.negRf P.D (decR P.D a) := negR_eq hp _
      simp only [Bool.or_eq_true, beq_iff_eq]
      rw [Bool.or_eq_true] at hce
      rcases hce with hce | hce
      · unfold eqPM at hce
        rw [Bool.or_eq_true] at hce
        unfold eqP at hce
        simp only [Bool.and_eq_true, Nat.beq_eq] at hce
        rcases hce with hce | hce
        · have e : packR P x.1 = a := Prod.ext hce.1 hce.2
          rcases List.mem_cons.mp hρx with rfl | hρ2
          · left
            left
            change reqb (decR P.D (packR P x.1)) (decR P.D a) = true
            rw [e]
            exact Snd.reqb_self _
          · rw [List.mem_singleton] at hρ2
            subst hρ2
            left
            right
            change reqb (decR P.D (packR P (Snd.negRf P.D x.1))) (negR P (decR P.D a)) = true
            rw [hneg, decR_negRf hp, negRf_congr hp (e.trans hr.symm)]
            exact Snd.reqb_self _
        · have e : packR P x.1 = packR P (Snd.negRf P.D (decR P.D a)) :=
            (Prod.ext hce.1 hce.2).trans (by rw [← Snd.negP_packR hp, hr])
          rcases List.mem_cons.mp hρx with rfl | hρ2
          · left
            right
            change reqb (decR P.D (packR P x.1)) (negR P (decR P.D a)) = true
            rw [e, hneg, decR_negRf hp]
            exact Snd.reqb_self _
          · rw [List.mem_singleton] at hρ2
            subst hρ2
            left
            left
            change reqb (decR P.D (packR P (Snd.negRf P.D x.1))) (decR P.D a) = true
            have e2 : packR P (Snd.negRf P.D x.1) = a := by
              rw [← Snd.negP_packR hp, e, Snd.negP_packR hp, packR_negneg hp, hr]
            rw [e2]
            exact Snd.reqb_self _
      · have hfx : P.dotv (decR P.D (packR P x.1)).f P.x = 0 := by
          rw [← dotK_packR hp hD, Snd.packR_decR hp (Snd.canP_packR hp _)]
          exact Nat.eq_of_beq_eq_true hce
        obtain ⟨-, -, hf⟩ := roots_ok (P := P1) hp hWF1 (hsem2 x hx) ρ hρx
        right
        exact hf hfx
  have hv7 : T.reps.all (verifyRepN P (candOfN P T)) = true := by
    rw [List.all_eq_true]
    intro rp' hrp'
    have hrp'' : rp' ∈ (fillL (cn P.D) R1).map (mk1 P cd) := hrp'
    obtain ⟨rp, hrp, rfl⟩ := List.mem_map.mp hrp''
    obtain ⟨hmem, hca⟩ := fill_mem hrp
    obtain ⟨hrf, hmvK, hk0, hk1⟩ := hR1 rp hmem
    obtain ⟨hpr, hd2⟩ := canon_facts hp hD hca hrf
    unfold verifyRepN
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨Snd.wfR_of_dotv hp hd2, ?_⟩, ?_⟩
    · change (P.dotv (decR P.D rp.1).f P.x != 0) = true
      rw [← dotK_packR hp hD, hpr]
      simpa using hmvK
    by_cases hz : rp.2.1 = 0
    · have hk : (mk1 P cd rp).kind = .cent := if_pos hz
      rw [hk]
      obtain ⟨hs, hcr⟩ := hst rp hmem hca (by unfold needs2; rw [hz]; rfl)
      change (centOK P (decR P.D rp.1) && centRootsOK P (decR P.D rp.1) (mk1 P cd rp).roots &&
        verifyStage2N P (candOfN P T) (mk1 P cd rp)) = true
      rw [hs, hcr hz, centOK_of hp hD (by rw [hpr]; exact hk0 hz)]
      rfl
    · obtain ⟨hkk, hchk⟩ := hk1 hz
      have hk : (mk1 P cd rp).kind = .w (witB (ptX P [rp.1] P.bound) rp.2.2.1.1) := if_neg hz
      rw [hk]
      rcases hkk with hkk | hkk | hkk
      · obtain ⟨hbad, hver⟩ := witB_bad hchk (Or.inl hkk)
        generalize witB (ptX P [rp.1] P.bound) rp.2.2.1.1 = w at hbad hver ⊢
        cases w <;> first | exact hver | simp [isBadW] at hbad
      · obtain ⟨hbad, hver⟩ := witB_bad hchk (Or.inr hkk)
        generalize witB (ptX P [rp.1] P.bound) rp.2.2.1.1 = w at hbad hver ⊢
        cases w <;> first | exact hver | simp [isBadW] at hbad
      · obtain ⟨c, hc, hver⟩ := witB_weyl hchk hkk
        rw [hc]
        obtain ⟨hs, -⟩ := hst rp hmem hca (by unfold needs2; rw [hkk]; simp)
        change (verify (withExtra P [decR P.D rp.1]) (.weyl c) &&
          verifyStage2N P (candOfN P T) (mk1 P cd rp)) = true
        rw [hs, Bool.and_true]
        exact hver
  refine ⟨T, ?_⟩
  unfold verifyAllN
  simp only [hwfP, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, Bool.and_self]

end CFSG.ReflExt.NK

end

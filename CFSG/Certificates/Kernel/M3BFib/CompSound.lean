module

public import CFSG.Certificates.Kernel.M3BFib.Lanes
public import CFSG.Certificates.Kernel.M3BFib.SubstClosed
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

@[expose] noncomputable def vz (r : ℕ) : Fin 12 → ZMod 3 := fun k => (((dig3 r).getD k 0 : ℕ) : ZMod 3)

@[expose] noncomputable def dK (D : PD) : ActD 12 :=
  (fun i => (vz (D.1.getD i 0), ((D.2.1.getD i 0 : ℕ) : ZMod 3)), ((D.2.2 : ℕ) : ZMod 3))

@[expose] def GoodPD (D : PD) : Prop :=
  D.1.length = 12 ∧ (∀ r ∈ D.1, GoodRow r) ∧ D.2.1.length = 12

@[expose] def LpOK (B : Fin 12 → Fin 12 → ZMod 3) (Lp : List ℕ) : Prop :=
  Lp.length = 12 ∧ (∀ r ∈ Lp, GoodRow r) ∧
    ∀ a b : Fin 12, vz (Lp.getD a 0) b = if b < a then B a b else 0

theorem cast_mod3 (n : ℕ) : (((n % 3 : ℕ)) : ZMod 3) = (n : ZMod 3) := ZMod.natCast_mod n 3

theorem dig3_getD (x : ℕ) {k : ℕ} (hk : k < 12) : (dig3 x).getD k 0 = (dig x).getD k 0 % 3 := by
  rw [dig3_eq, List.getD_eq_getElem _ _ (by rw [List.length_map, dig_length]; exact hk),
    List.getElem_map, List.getD_eq_getElem _ _ (by rw [dig_length]; exact hk)]

theorem getD_mem_lt {l : List ℕ} {m : ℕ} (h : ∀ a ∈ l, a < m) (hm : 0 < m) (k : ℕ) : l.getD k 0 < m := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hm

theorem getD_mem {α : Type} {l : List α} {d : α} {k : ℕ} (hk : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem lane_vm (u P : List ℕ) (hu : u.length = 12) (hu3 : ∀ a ∈ u, a < 3) (hP : P.length = 12)
    (hg : ∀ p ∈ P, GoodRow p) (k : Fin 12) :
    (((dig (vm u P)).getD k 0 : ℕ) : ZMod 3) = ∑ j : Fin 12, (u.getD j 0 : ZMod 3) * vz (P.getD j 0) k := by
  obtain ⟨h1, h2⟩ := dig_vm u P hu hu3 hP hg
  rw [h1, h2 k k.isLt]
  push_cast
  rfl

theorem vz_vm (u P : List ℕ) (hu : u.length = 12) (hu3 : ∀ a ∈ u, a < 3) (hP : P.length = 12)
    (hg : ∀ p ∈ P, GoodRow p) (k : Fin 12) :
    vz (vm u P) k = ∑ j : Fin 12, (u.getD j 0 : ZMod 3) * vz (P.getD j 0) k := by
  rw [← lane_vm u P hu hu3 hP hg k, vz, dig3_getD _ k.isLt, cast_mod3]

theorem vz_red (x : ℕ) : vz (red x) = vz x := by
  funext k
  rw [vz, vz, dig3_red]

theorem goodRow_enc {ds : List ℕ} (hl : ds.length = 12) (h : ∀ d ∈ ds, d < 3) : GoodRow (enc ds) := by
  unfold GoodRow
  rw [dig3_eq, dig_enc hl fun d hd => lt_trans (h d hd) (by norm_num)]
  congr 1
  conv_rhs => rw [← List.map_id ds]
  exact List.map_congr_left fun d hd => Nat.mod_eq_of_lt (h d hd)

theorem vz_enc {ds : List ℕ} (hl : ds.length = 12) (h : ∀ d ∈ ds, d < 3) (k : Fin 12) :
    vz (enc ds) k = ((ds.getD k 0 : ℕ) : ZMod 3) := by
  rw [vz, dig3_getD _ k.isLt, dig_enc hl fun d hd => lt_trans (h d hd) (by norm_num), cast_mod3]

theorem vz_dig3 (r : ℕ) (j : Fin 12) : (((dig3 r).getD j 0 : ℕ) : ZMod 3) = vz r j := rfl

theorem dot_eq : ∀ (m : ℕ) (u v : List ℕ), u.length = m → v.length = m →
    dot u v = ∑ j : Fin m, u.getD j 0 * v.getD j 0
  | 0, [], [], _, _ => rfl
  | m + 1, a :: u, b :: v, hu, hv => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_succ, List.getD_cons_zero]
    rw [← dot_eq m u v (by simpa using hu) (by simpa using hv)]
    rfl

theorem colsK_length : ∀ (rs : List (List ℕ)), (∀ r ∈ rs, r.length = 12) → (colsK rs).length = 12
  | [], _ => rfl
  | r :: rs, h => by
    change (List.zipWith _ r (colsK rs)).length = 12
    rw [List.length_zipWith, h r List.mem_cons_self,
      colsK_length rs fun q hq => h q (List.mem_cons_of_mem _ hq), min_self]

theorem colsK_getD : ∀ (rs : List (List ℕ)), (∀ r ∈ rs, r.length = 12) → ∀ b < 12,
    (colsK rs).getD b 0 = enc (rs.map fun r => r.getD b 0)
  | [], _, b, hb => by
    change (List.replicate 12 0).getD b 0 = 0
    interval_cases b <;> rfl
  | r :: rs, h, b, hb => by
    have h' : ∀ q ∈ rs, q.length = 12 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    change (List.zipWith _ r (colsK rs)).getD b 0 = _
    rw [getD_zipWith _ _ _ _ (by rw [h r List.mem_cons_self]; exact hb)
      (by rw [colsK_length rs h']; exact hb), colsK_getD rs h' b hb, List.map_cons, enc_cons]
    rfl

theorem zpre_length : ∀ (ds : List ℕ) (m : ℕ), (zpre m ds).length = ds.length
  | [], _ => rfl
  | d :: ds, 0 => by
    change (d :: zpre 0 ds).length = _
    rw [List.length_cons, zpre_length ds 0, List.length_cons]
  | d :: ds, m + 1 => by
    change (0 :: zpre m ds).length = _
    rw [List.length_cons, zpre_length ds m, List.length_cons]

theorem zpre_getD : ∀ (ds : List ℕ) (m l : ℕ),
    (zpre m ds).getD l 0 = if l < m then 0 else ds.getD l 0
  | [], m, l => by simp [zpre]
  | d :: ds, 0, 0 => rfl
  | d :: ds, 0, l + 1 => by
    change (d :: zpre 0 ds).getD (l + 1) 0 = _
    rw [List.getD_cons_succ, zpre_getD ds 0 l, List.getD_cons_succ]
    simp
  | d :: ds, m + 1, 0 => by
    change (0 :: zpre m ds).getD 0 0 = _
    simp
  | d :: ds, m + 1, l + 1 => by
    change (0 :: zpre m ds).getD (l + 1) 0 = _
    rw [List.getD_cons_succ, zpre_getD ds m l, List.getD_cons_succ]
    simp

theorem zpre_lt {ds : List ℕ} (h : ∀ d ∈ ds, d < 3) (m : ℕ) : ∀ d ∈ zpre m ds, d < 3 := by
  intro d hd
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hd
  rw [← List.getD_eq_getElem _ 0 hl, zpre_getD]
  split_ifs
  · norm_num
  · exact getD_mem_lt h (by norm_num) l

theorem upDiag_spec : ∀ (gs : List (List ℕ)) (k : ℕ),
    (upDiag gs k).1.length = gs.length ∧ (upDiag gs k).2.length = gs.length ∧
    ∀ j < gs.length, (upDiag gs k).1.getD j 0 = enc (zpre (k + j + 1) (gs.getD j [])) ∧
      (upDiag gs k).2.getD j 0 = (gs.getD j []).getD (k + j) 0
  | [], k => ⟨rfl, rfl, fun j hj => by simp at hj⟩
  | g :: gs, k => by
    obtain ⟨h1, h2, h3⟩ := upDiag_spec gs (k + 1)
    change (List.cons (enc (zpre (k + 1) g)) (upDiag gs (k + 1)).1).length = _ ∧
      (List.cons (g.getD k 0) (upDiag gs (k + 1)).2).length = _ ∧ ∀ j < _,
      (List.cons (enc (zpre (k + 1) g)) (upDiag gs (k + 1)).1).getD j 0 = _ ∧
      (List.cons (g.getD k 0) (upDiag gs (k + 1)).2).getD j 0 = _
    refine ⟨by simp [h1], by simp [h2], fun j hj => ?_⟩
    rcases j with _ | j
    · simp
    · rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
      obtain ⟨e1, e2⟩ := h3 j (by simpa using hj)
      rw [e1, e2, show k + (j + 1) = k + 1 + j by omega]
      exact ⟨rfl, rfl⟩

theorem getD_map_lt {α β : Type} {f : α → β} {l : List α} {d : α} {d' : β} {i : ℕ}
    (hi : i < l.length) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem ch2_cast {u : ℕ} (hu : u < 3) : ((ch2 u : ℕ) : ZMod 3) = ch2Z (u : ZMod 3) := by
  unfold ch2Z
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu]
  interval_cases u <;> rfl

theorem compK_sound {B : Fin 12 → Fin 12 → ZMod 3} {Lp : List ℕ} (hL : LpOK B Lp) {D D' : PD}
    (hD : GoodPD D) (hD' : GoodPD D') :
    GoodPD (compK Lp D D') ∧ dK (compK Lp D D') = comp B (dK D) (dK D') := by
  obtain ⟨hL1, hL2, hL3⟩ := hL
  obtain ⟨hR, hRg, hc⟩ := hD
  obtain ⟨hR', hRg', hc'⟩ := hD'
  have hd3 : ∀ q ∈ D'.1.map dig3, q.length = 12 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, _, rfl⟩ := hq
    exact dig3_length r
  set MT := colsK (D'.1.map dig3) with hMT
  have hMT1 : MT.length = 12 := colsK_length _ hd3
  have hMTrow : ∀ b < 12, MT.getD b 0 = enc ((D'.1.map dig3).map fun r => r.getD b 0) :=
    colsK_getD _ hd3
  have hcol_len : ∀ b < 12, ((D'.1.map dig3).map fun r => r.getD b 0).length = 12 := by
    intro b _
    rw [List.length_map, List.length_map, hR']
  have hcol_lt : ∀ b < 12, ∀ d ∈ (D'.1.map dig3).map (fun r => r.getD b 0), d < 3 := by
    intro b _ d hd
    rw [List.mem_map] at hd
    obtain ⟨r, hr, rfl⟩ := hd
    rw [List.mem_map] at hr
    obtain ⟨s, _, rfl⟩ := hr
    exact getD_mem_lt (dig3_lt s) (by norm_num) b
  have hMTg : ∀ p ∈ MT, GoodRow p := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hp
    have hb12 : b < 12 := by rwa [hMT1] at hb
    rw [← List.getD_eq_getElem _ 0 hb, hMTrow b hb12]
    exact goodRow_enc (hcol_len b hb12) (hcol_lt b hb12)
  have hMTv : ∀ b l : Fin 12, vz (MT.getD b 0) l = vz (D'.1.getD l 0) b := by
    intro b l
    rw [hMTrow b b.isLt, vz_enc (hcol_len b b.isLt) (hcol_lt b b.isLt),
      getD_map_lt (f := fun r : List ℕ => r.getD b 0) (d := [])
        (by rw [List.length_map, hR']; exact l.isLt),
      getD_map_lt (f := dig3) (d := 0) (by rw [hR']; exact l.isLt)]
    rfl
  set Gd := D'.1.map (fun r => dig3 (vm (dig3 (red (vm (dig3 r) Lp))) MT)) with hGd
  have hGd1 : Gd.length = 12 := by rw [hGd, List.length_map, hR']
  have hGdj : ∀ j : Fin 12, Gd.getD j [] = dig3 (vm (dig3 (red (vm (dig3 (D'.1.getD j 0)) Lp))) MT) := by
    intro j
    rw [hGd, getD_map_lt (f := fun r => dig3 (vm (dig3 (red (vm (dig3 r) Lp))) MT)) (d := 0)
      (by rw [hR']; exact j.isLt)]
  have hGv : ∀ j l : Fin 12, (((Gd.getD j []).getD l 0 : ℕ) : ZMod 3) =
      betaC 12 B (vz (D'.1.getD j 0)) (vz (D'.1.getD l 0)) := by
    intro j l
    rw [hGdj, vz_dig3, vz_vm _ _ (dig3_length _) (dig3_lt _) hMT1 hMTg]
    simp only [vz_dig3, vz_red, vz_vm _ _ (dig3_length _) (dig3_lt _) hL1 hL2, hL3, hMTv, betaC]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hGlt : ∀ g ∈ Gd, g.length = 12 ∧ ∀ d ∈ g, d < 3 := by
    intro g hg
    rw [hGd, List.mem_map] at hg
    obtain ⟨r, _, rfl⟩ := hg
    exact ⟨dig3_length _, dig3_lt _⟩
  obtain ⟨hU1, hU2, hU3⟩ := upDiag_spec Gd 0
  have hUg : ∀ p ∈ (upDiag Gd 0).1, GoodRow p := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [hU1] at hj
    rw [← List.getD_eq_getElem _ 0 (by rw [hU1]; exact hj), (hU3 j hj).1]
    have hg := hGlt (Gd.getD j []) (getD_mem hj)
    exact goodRow_enc (by rw [zpre_length, hg.1]) (zpre_lt hg.2 _)
  have hUv : ∀ j l : Fin 12, vz ((upDiag Gd 0).1.getD j 0) l =
      if j < l then betaC 12 B (vz (D'.1.getD j 0)) (vz (D'.1.getD l 0)) else 0 := by
    intro j l
    have hj : (j : ℕ) < Gd.length := by rw [hGd1]; exact j.isLt
    have hg := hGlt (Gd.getD j []) (getD_mem hj)
    rw [(hU3 j hj).1, vz_enc (by rw [zpre_length, hg.1]) (zpre_lt hg.2 _), zpre_getD, ← hGv j l]
    by_cases h : j < l
    · rw [if_neg (by omega), if_pos h]
    · rw [if_pos (by omega), if_neg h]
      rfl
  have hUd : ∀ j : Fin 12, (((upDiag Gd 0).2.getD j 0 : ℕ) : ZMod 3) =
      betaC 12 B (vz (D'.1.getD j 0)) (vz (D'.1.getD j 0)) := by
    intro j
    rw [(hU3 j (by rw [hGd1]; exact j.isLt)).2, Nat.zero_add, hGv j j]
  have hcK : compK Lp D D' = (D.1.map (fun r => red (vm (dig3 r) D'.1)),
      List.zipWith (fun r ci => (fun u => Nat.mod (Nat.add (Nat.add (Nat.mul D'.2.2 ci)
        (dot u D'.2.1)) (Nat.add (dot (u.map ch2) (upDiag Gd 0).2)
          (dot u (dig (vm u (upDiag Gd 0).1))))) 3) (dig3 r)) D.1 D.2.1,
      Nat.mod (Nat.mul D.2.2 D'.2.2) 3) := rfl
  rw [hcK]
  refine ⟨⟨by rw [List.length_map, hR], fun r hr => ?_, by rw [List.length_zipWith, hR, hc, min_self]⟩, ?_⟩
  · rw [List.mem_map] at hr
    obtain ⟨s, _, rfl⟩ := hr
    exact goodRow_red _
  have hmod : ∀ m : ℕ, ((Nat.mod m 3 : ℕ) : ZMod 3) = (m : ZMod 3) := cast_mod3
  simp only [dK, comp, subst_eq]
  refine Prod.ext (funext fun i => Prod.ext (funext fun k => ?_) ?_) ?_
  · dsimp only
    have hi : (i : ℕ) < D.1.length := by rw [hR]; exact i.isLt
    rw [getD_map_lt (d := 0) hi, vz_red, vz_vm _ _ (dig3_length _) (dig3_lt _) hR' hRg',
      Finset.sum_apply]
    rfl
  · dsimp only
    have hi : (i : ℕ) < D.1.length := by rw [hR]; exact i.isLt
    have hi' : (i : ℕ) < D.2.1.length := by rw [hc]; exact i.isLt
    rw [getD_zipWith _ _ _ _ hi hi']
    set u := dig3 (D.1.getD i 0) with hu
    have hul : u.length = 12 := dig3_length _
    have hu3 : ∀ a ∈ u, a < 3 := dig3_lt _
    have hx : ∀ j : Fin 12, vz (D.1.getD i 0) j = ((u.getD j 0 : ℕ) : ZMod 3) := fun j => rfl
    have s1 : ((dot u D'.2.1 : ℕ) : ZMod 3) =
        ∑ j : Fin 12, ((u.getD j 0 : ℕ) : ZMod 3) * ((D'.2.1.getD j 0 : ℕ) : ZMod 3) := by
      rw [dot_eq 12 _ _ hul hc']
      push_cast
      rfl
    have s2 : ((dot (u.map ch2) (upDiag Gd 0).2 : ℕ) : ZMod 3) =
        ∑ j : Fin 12, ch2Z ((u.getD j 0 : ℕ) : ZMod 3) *
          betaC 12 B (vz (D'.1.getD j 0)) (vz (D'.1.getD j 0)) := by
      rw [dot_eq 12 _ _ (by rw [List.length_map, hul]) (by rw [hU2, hGd1])]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [getD_map_lt (d := 0) (by rw [hul]; exact j.isLt),
        ch2_cast (getD_mem_lt hu3 (by norm_num) _), hUd j]
    have s3 : ((dot u (dig (vm u (upDiag Gd 0).1)) : ℕ) : ZMod 3) =
        ∑ j : Fin 12, ∑ l : Fin 12, if j < l then ((u.getD j 0 : ℕ) : ZMod 3) *
          ((u.getD l 0 : ℕ) : ZMod 3) * betaC 12 B (vz (D'.1.getD j 0)) (vz (D'.1.getD l 0))
          else 0 := by
      rw [dot_eq 12 _ _ hul (dig_length _)]
      push_cast
      simp only [lane_vm u _ hul hu3 (by rw [hU1, hGd1]) hUg, hUv]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    simp only [hx, hmod, Nat.add_eq, Nat.mul_eq]
    push_cast
    rw [s1, s2, s3, Finset.sum_add_distrib]
    ring
  · dsimp only
    rw [hmod, Nat.mul_eq]
    push_cast
    rfl

end CFSG.KC.M3BF

end

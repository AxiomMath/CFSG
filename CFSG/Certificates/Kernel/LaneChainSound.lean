module

public import Certificates.Data.Kernel.LaneChain
public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.Common.ChainBound

public section

namespace CFSG.KS.LaneChain

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.LaneChain CFSG.KC.StabChain CFSG.KS.J4Hub

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_app (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem andT {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem getN_mem : ∀ (l : List Nat) (i : Nat), i < l.length → getN l i ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, i + 1, h => List.mem_cons_of_mem _ (getN_mem l i (by simpa using h))

theorem getN_eq_getElem : ∀ (l : List Nat) (i : Nat) (h : i < l.length), getN l i = l[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => by
    rw [List.getElem_cons_succ]
    exact getN_eq_getElem l i (by simpa using h)

theorem getR_cons (x : Nat) (M : List Nat) {n r : Nat} (hr : r < n + 1) :
    getR (x :: M) (n + 1) r = if r = n then x else getR M n r := by
  unfold getR
  split_ifs with h
  · rw [h]
    change getN (x :: M) (n + 1 - 1 - n) = x
    rw [Nat.add_sub_cancel, Nat.sub_self]
    rfl
  · change getN (x :: M) (n + 1 - 1 - r) = getN M (n - 1 - r)
    have e : n + 1 - 1 - r = (n - 1 - r) + 1 := by omega
    rw [e]
    rfl

theorem getR_mem {M : List Nat} {r : Nat} (hr : r < M.length) : getR M M.length r ∈ M :=
  getN_mem M (M.length - 1 - r) (by omega)

theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

theorem allLt_spec {n : Nat} : ∀ w : List Nat, allLt w n = true → ∀ x ∈ w, x < n
  | [], _, _, hx => absurd hx List.not_mem_nil
  | r :: w, h, x, hx => by
    obtain ⟨h1, h2⟩ := andT h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.blt_eq.mp h1
    · exact allLt_spec w h2 x hx

theorem notIn_spec {x : Nat} : ∀ V : List Nat, notIn x V = true → x ∉ V
  | [], _ => List.not_mem_nil
  | y :: V, h => by
    obtain ⟨h1, h2⟩ := andT h
    intro hx
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [notB] at h1
    · exact notIn_spec V h2 hx

theorem memN_spec {r : Nat} : ∀ G : List Nat, memN r G = true → r ∈ G
  | [], h => absurd h (by simp [memN])
  | y :: G, h => by
    change orB (Nat.beq r y) (memN r G) = true at h
    cases hb : Nat.beq r y
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (memN_spec G h)
    · rw [Nat.beq_eq] at hb
      rw [hb]
      exact List.mem_cons_self

theorem gensK_spec {mul : Nat → Nat → Nat} {M Xs : List Nat} {nreg k : Nat} :
    ∀ Gl : List Nat, gensK mul M Xs Gl nreg k = true → ∀ r ∈ Gl, r < nreg ∧
      ∀ j < k, mul (getR M nreg r) (getN Xs j) = getN Xs j
  | [], _, _, hr => absurd hr List.not_mem_nil
  | r :: Gl, h, r', hr' => by
    obtain ⟨h1, h2⟩ := andT h
    rcases List.mem_cons.1 hr' with rfl | hr'
    · obtain ⟨h3, h4⟩ := andT h1
      refine ⟨Nat.blt_eq.mp h3, ?_⟩
      have key : ∀ m, Nat.rec (motive := fun _ => Bool) true (fun j ih2 => andB ih2
          (Nat.beq (mul (getR M nreg r') (getN Xs j)) (getN Xs j))) m = true →
          ∀ j < m, mul (getR M nreg r') (getN Xs j) = getN Xs j := by
        intro m
        induction m with
        | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero j)
        | succ m ih =>
          intro hm j hj
          obtain ⟨h5, h6⟩ := andT hm
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact ih h5 j hj
          · exact Nat.eq_of_beq_eq_true h6
      exact key k h4
    · exact gensK_spec Gl h2 r' hr'

theorem basesK_spec {vld : Nat → Bool} {S' : Nat} {k : List Nat → Bool} :
    ∀ (Bs : List (List Nat)) (Xs : List Nat), (∀ x ∈ Xs, vld x = true) →
      basesK vld S' k Bs Xs = true → ∃ Xs', (∀ x ∈ Xs', vld x = true) ∧ k Xs' = true
  | [], Xs, hX, h => ⟨Xs, hX, h⟩
  | b :: Bs, Xs, hX, h => by
    have h' : strictB (colDat S' b) (fun x => andB (vld x)
        (basesK vld S' k Bs (List.append Xs (List.cons x List.nil)))) = true := h
    rw [strictB_app] at h'
    replace h := h'
    obtain ⟨h1, h2⟩ := andT h
    refine basesK_spec Bs _ (fun x hx => ?_) h2
    rcases List.mem_append.1 hx with hx | hx
    · exact hX x hx
    · rw [List.mem_singleton.1 hx]
      exact h1

@[expose] def Good {G : Type*} [Group G] {p d : Nat} (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))
    (K : Subgroup G) (w S nb L H : Nat) (x : Nat) : Prop :=
  validM p nb L H x = true ∧ ∃ g ∈ K, ordMat p d w S x = φ g

@[expose] def AllGood {G : Type*} [Group G] {p d : Nat} (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))
    (K : Subgroup G) (w S nb L H : Nat) (M : List Nat) : Prop :=
  ∀ r < M.length, Good φ K w S nb L H (getR M M.length r)

@[expose] def act {G : Type*} [Group G] {p d : Nat} (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))
    (g : G) (X : Matrix (Fin d) (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  φ g * X

structure TreeInv {G : Type*} [Group G] {p d : Nat} (φ : G →* Matrix (Fin d) (Fin d) (ZMod p))
    (K : Subgroup G) (w S nb L H : Nat) (Fx : List (Matrix (Fin d) (Fin d) (ZMod p)))
    (b : Matrix (Fin d) (Fin d) (ZMod p)) (V : List Nat) (ts : List G) : Prop where
  len : V.length = ts.length
  vld : ∀ x ∈ V, validM p nb L H x = true
  nodup : V.Nodup
  mem : ∀ t ∈ ts, t ∈ K
  fix : ∀ t ∈ ts, ∀ X ∈ Fx, act φ t X = X
  img : ∀ i < V.length, ordMat p d w S (getR V V.length i) = act φ (ts.getD i 1) b

variable {p d w S T L H CM RM ONE LV HV nb : Nat}
variable {G : Type*} [Group G] (φ : G →* Matrix (Fin d) (Fin d) (ZMod p)) (K : Subgroup G)

theorem act_mul (g h : G) (X : Matrix (Fin d) (Fin d) (ZMod p)) :
    act φ (g * h) X = act φ g (act φ h X) := by
  simp only [act, map_mul, mul_assoc]

theorem act_one (X : Matrix (Fin d) (Fin d) (ZMod p)) : act φ 1 X = X := by
  simp only [act, map_one, one_mul]

theorem treeInv_cons {Fx : List (Matrix (Fin d) (Fin d) (ZMod p))}
    {b : Matrix (Fin d) (Fin d) (ZMod p)} {V : List Nat} {ts : List G}
    (I : TreeInv φ K w S nb L H Fx b V ts) {v : Nat} {t : G}
    (hv : validM p nb L H v = true) (hn : v ∉ V) (ht : t ∈ K) (hf : ∀ X ∈ Fx, act φ t X = X)
    (hi : ordMat p d w S v = act φ t b) :
    TreeInv φ K w S nb L H Fx b (v :: V) (ts ++ [t]) := by
  refine ⟨by simp [I.len], fun x hx => ?_, List.nodup_cons.2 ⟨hn, I.nodup⟩, fun x hx => ?_,
    fun x hx => ?_, fun i hi' => ?_⟩
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact hv
    · exact I.vld x hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact I.mem x hx
    · rw [List.mem_singleton.1 hx]
      exact ht
  · rcases List.mem_append.1 hx with hx | hx
    · exact I.fix x hx
    · rw [List.mem_singleton.1 hx]
      exact hf
  · rw [List.length_cons] at hi' ⊢
    rw [getR_cons v V hi']
    split_ifs with h
    · subst h
      rw [List.getD_append_right _ _ _ _ (le_of_eq I.len.symm), I.len, Nat.sub_self]
      exact hi
    · have hi2 : i < V.length := by omega
      rw [List.getD_append _ _ _ _ (I.len ▸ hi2)]
      exact I.img i hi2

section

variable (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
include hc hnb

theorem good_mul {x y : Nat} (hx : Good φ K w S nb L H x) (hy : Good φ K w S nb L H y) :
    Good φ K w S nb L H (mulR p w S d T L H CM RM x y) := by
  obtain ⟨hx1, g, hg, hxg⟩ := hx
  obtain ⟨hy1, h, hh, hyh⟩ := hy
  obtain ⟨h1, h2⟩ := mul_sound' hc hnb hx1 hy1
  exact ⟨h1, g * h, K.mul_mem hg hh, by rw [h2, hxg, hyh, map_mul]⟩

theorem good_wfold {M : List Nat} (hM : AllGood φ K w S nb L H M) :
    ∀ (rs : List Nat) (acc : Nat), (∀ x ∈ rs, x < M.length) → Good φ K w S nb L H acc →
      Good φ K w S nb L H (wfold (mulR p w S d T L H CM RM) M M.length rs acc)
  | [], _, _, h => h
  | r :: rs, acc, hr, h => by
    change Good φ K w S nb L H (CFSG.KC.Loop.strictN (mulR p w S d T L H CM RM acc
      (getR M M.length r)) (wfold (mulR p w S d T L H CM RM) M M.length rs))
    rw [strictN_app]
    exact good_wfold hM rs _ (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      (good_mul φ K hc hnb h (hM r (hr r List.mem_cons_self)))

theorem good_wprod {M : List Nat} (hM : AllGood φ K w S nb L H M) {wd : List Nat}
    (hne : wd ≠ []) (hw : ∀ x ∈ wd, x < M.length) :
    Good φ K w S nb L H (wprod (mulR p w S d T L H CM RM) M M.length wd) := by
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact good_wfold φ K hc hnb hM rs _ (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    (hM r (hw r List.mem_cons_self))

omit hc hnb in
theorem allGood_cons {M : List Nat} (hM : AllGood φ K w S nb L H M) {x : Nat}
    (hx : Good φ K w S nb L H x) : AllGood φ K w S nb L H (x :: M) := by
  intro r hr
  rw [List.length_cons] at hr ⊢
  rw [getR_cons x M hr]
  split_ifs with h
  · exact hx
  · exact hM r (by omega)

theorem regsK_spec {k : List Nat → Nat → Bool} : ∀ (W : List (List Nat)) (M : List Nat),
    AllGood φ K w S nb L H M → regsK (mulR p w S d T L H CM RM) k W M M.length = true →
      ∃ M', AllGood φ K w S nb L H M' ∧ k M' M'.length = true
  | [], M, hM, h => ⟨M, hM, h⟩
  | wd :: W, M, hM, h => by
    obtain ⟨h1, h2⟩ := andT h
    obtain ⟨h1a, h1b⟩ := andT h1
    have hne : wd ≠ [] := by
      intro e
      subst e
      simp [notB, lenL] at h1a
    rw [strictB_app] at h2
    have hx := good_wprod φ K hc hnb hM hne (allLt_spec wd h1b)
    have h3 : regsK (mulR p w S d T L H CM RM) k W
        (wprod (mulR p w S d T L H CM RM) M M.length wd :: M)
        (wprod (mulR p w S d T L H CM RM) M M.length wd :: M).length = true := h2
    exact regsK_spec W _ (allGood_cons φ K hM hx) h3

theorem treeK_spec {M Gl : List Nat} {Fx : List (Matrix (Fin d) (Fin d) (ZMod p))}
    {b : Matrix (Fin d) (Fin d) (ZMod p)} (hM : AllGood φ K w S nb L H M)
    (hG : ∀ r ∈ Gl, r < M.length ∧ ∀ g ∈ K, ordMat p d w S (getR M M.length r) = φ g →
      ∀ X ∈ Fx, act φ g X = X)
    {k : Nat → Bool} : ∀ (Tl : List Nat) (pend : Nat) (V : List Nat) (ts : List G),
      TreeInv φ K w S nb L H Fx b V ts → (∀ q, pend = q + 1 → q < V.length) →
      treeK (mulR p w S d T L H CM RM) M M.length Gl k Tl pend V V.length = true →
      ∃ V' ts', TreeInv φ K w S nb L H Fx b V' ts' ∧ k V'.length = true
  | [], pend, V, ts, I, _, h => ⟨V, ts, I, (andT h).2⟩
  | c :: Tl, pend, V, ts, I, hp, h => by
    cases pend with
    | zero =>
      obtain ⟨h1, h2⟩ := andT h
      have h2' : treeK (mulR p w S d T L H CM RM) M M.length Gl k Tl (c + 1) V V.length = true :=
        h2
      exact treeK_spec hM hG Tl _ V ts I (fun q e => by
        rw [Nat.succ.inj e] at h1
        exact Nat.blt_eq.mp h1) h2'
    | succ q =>
      change andB (memN c Gl) (strictB (mulR p w S d T L H CM RM (getR M M.length c)
        (getR V V.length q)) _) = true at h
      obtain ⟨h1, h2⟩ := andT h
      rw [strictB_app] at h2
      obtain ⟨h3, h4⟩ := andT h2
      obtain ⟨hcM, hfix⟩ := hG c (memN_spec Gl h1)
      have hq := hp q rfl
      obtain ⟨hv1, g, hg, hcg⟩ := hM c hcM
      obtain ⟨hv, hmul⟩ := mul_sound' hc hnb hv1 (I.vld _ (getR_mem hq))
      have hqt : q < ts.length := I.len ▸ hq
      have htq : ts.getD q 1 ∈ ts := List.getD_eq_getElem _ _ hqt ▸ List.getElem_mem hqt
      have hI := treeInv_cons φ K I hv (notIn_spec V h3) (K.mul_mem hg (I.mem _ htq))
        (fun X hX => by rw [act_mul, I.fix _ htq X hX, hfix g hg hcg X hX])
        (by rw [hmul, I.img q hq, hcg, act_mul]; rfl)
      have h5 : treeK (mulR p w S d T L H CM RM) M M.length Gl k Tl 0
          (mulR p w S d T L H CM RM (getR M M.length c) (getR V V.length q) :: V)
          (mulR p w S d T L H CM RM (getR M M.length c) (getR V V.length q) :: V).length =
            true := h4
      exact treeK_spec hM hG Tl 0 _ _ hI (fun q' e' => absurd e' (Nat.succ_ne_zero q').symm) h5

@[expose] noncomputable def fixL (p d w S : Nat) (Xs : List Nat) (k : Nat) :
    List (Matrix (Fin d) (Fin d) (ZMod p)) :=
  (List.range k).map fun j => ordMat p d w S (getN Xs j)

theorem levelsK_spec {M Xs : List Nat} (hM : AllGood φ K w S nb L H M)
    (hX : ∀ x ∈ Xs, validM p nb L H x = true) {tot : Nat} {Ts : List (List Nat)} :
    ∀ (Gs : List (List Nat)) (k acc : Nat),
      levelsK (mulR p w S d T L H CM RM) M M.length Xs tot Ts Gs k acc = true →
      ∃ Lc : List (Matrix (Fin d) (Fin d) (ZMod p) × List G), ChainOK (act φ) K Lc ∧
        acc * (Lc.map fun l => l.2.length).prod = tot ∧
        ∀ l ∈ Lc, ∀ t ∈ l.2, ∀ X ∈ fixL p d w S Xs k, act φ t X = X
  | [], k, acc, h => ⟨[], trivial, by simpa using Nat.eq_of_beq_eq_true h,
      fun _ hl => absurd hl List.not_mem_nil⟩
  | Gl :: Gs, k, acc, h => by
    obtain ⟨h1, h2⟩ := andT h
    obtain ⟨hk, hgen⟩ := andT h1
    have hk' : k < Xs.length := by
      rw [← lenL_eq]
      exact Nat.blt_eq.mp hk
    have hXk : validM p nb L H (getN Xs k) = true := hX _ (getN_mem Xs k hk')
    have hG : ∀ r ∈ Gl, r < M.length ∧ ∀ g ∈ K, ordMat p d w S (getR M M.length r) = φ g →
        ∀ X ∈ fixL p d w S Xs k, act φ g X = X := by
      intro r hr
      obtain ⟨hrn, hfx⟩ := gensK_spec Gl hgen r hr
      refine ⟨hrn, fun g _ hg X hXm => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hXm
      have hj' := List.mem_range.1 hj
      obtain ⟨-, e⟩ := mul_sound' hc hnb (hM r hrn).1 (hX _ (getN_mem Xs j (by omega)))
      change φ g * _ = _
      rw [← hg, ← e, hfx j hj']
    let b := ordMat p d w S (getN Xs k)
    have I0 : TreeInv φ K w S nb L H (fixL p d w S Xs k) b [getN Xs k] [1] := by
      refine ⟨rfl, fun x hx => ?_, List.nodup_singleton _, fun t ht => ?_, fun t ht X _ => ?_,
        fun i hi => ?_⟩
      · rw [List.mem_singleton.1 hx]
        exact hXk
      · rw [List.mem_singleton.1 ht]
        exact K.one_mem
      · rw [List.mem_singleton.1 ht]
        exact act_one φ X
      · have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact (act_one φ b).symm
    obtain ⟨V, ts, I, hrest⟩ := treeK_spec φ K hc hnb hM hG _ 0 _ _ I0
      (fun q e => absurd e (Nat.succ_ne_zero q).symm) h2
    obtain ⟨Lc, hC, hprod, hfix⟩ := levelsK_spec hM hX Gs (k + 1) _ hrest
    refine ⟨(b, ts) :: Lc, ⟨I.mem, ?_, fun l hl t ht => hfix l hl t ht b ?_, hC⟩, ?_, ?_⟩
    · have hmap : ts.map (fun t => act φ t b) =
          (List.range V.length).map fun i => ordMat p d w S (getR V V.length i) := by
        apply List.ext_getElem (by simp [I.len])
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [I.img i (by simpa using h2), List.getD_eq_getElem _ _ (by simpa using h1)]
      rw [hmap]
      refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range
      have hi' := List.mem_range.1 hi
      have hj' := List.mem_range.1 hj
      have e2 := ordMat_inj' hc hnb (I.vld _ (getR_mem hi')) (I.vld _ (getR_mem hj')) e
      change getN V (V.length - 1 - i) = getN V (V.length - 1 - j) at e2
      rw [getN_eq_getElem V _ (by omega), getN_eq_getElem V _ (by omega)] at e2
      have e3 := (List.Nodup.getElem_inj_iff I.nodup).1 e2
      omega
    · exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_self k), rfl⟩
    · rw [List.map_cons, List.prod_cons, ← I.len, ← mul_assoc]
      exact hprod
    · intro l hl t ht X hXm
      rcases List.mem_cons.1 hl with rfl | hl
      · exact I.fix t ht X hXm
      · refine hfix l hl t ht X ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hXm
        exact List.mem_map.2 ⟨j, List.mem_range.2 (by have := List.mem_range.1 hj; omega), rfl⟩

theorem card_ge_of_chainOK [Finite K] {M₀ : List Nat} (hM : AllGood φ K w S nb L H M₀)
    {S' tot : Nat} {W Bs Gs Ts : List (List Nat)}
    (h : chainOK (mulR p w S d T L H CM RM) (validM p nb L H) S' W Bs Gs Ts M₀ tot = true) :
    tot ≤ Nat.card K := by
  unfold chainOK at h
  rw [lenL_eq] at h
  obtain ⟨M, hM', h1⟩ := regsK_spec φ K hc hnb W M₀ hM h
  obtain ⟨Xs, hX, h2⟩ := basesK_spec Bs [] (fun x hx => absurd hx List.not_mem_nil) h1
  obtain ⟨Lc, hC, hprod, -⟩ := levelsK_spec φ K hc hnb hM' hX Gs 0 1 h2
  rw [one_mul] at hprod
  rw [← hprod]
  exact prod_le_card_of_chainOK (act φ) (act_mul φ) (act_one φ) K Lc hC

end

end CFSG.KS.LaneChain

end

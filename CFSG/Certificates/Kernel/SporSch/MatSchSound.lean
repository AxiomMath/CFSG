module

public import CFSG.Certificates.Kernel.SporSch.MatSchDefs
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.RankThree.Native.F2Bind

set_option linter.unusedSectionVars false

public section

namespace CFSG.KS.MatSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.RankThree.Native.F2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Certificates
  CFSG.Certificates.ChainArrays

structure Good (d : ℕ) (V : Array ℕ) : Prop where
  hd : 0 < d
  nodup : V.toList.Nodup
  lt : ∀ v ∈ V, v < 2 ^ d

@[expose] def Rep (d : ℕ) (V : Array ℕ) (a : Array ℕ) (M M' : ℕ) : Prop :=
  a = permOfMat d V M ∧ Inv d V M M'

@[expose] noncomputable def vecs (n d md PV : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => pg d md PV i.val

theorem vecs_size (n d md PV : Nat) : (vecs n d md PV).size = n := Array.size_ofFn

theorem vecs_get {n d md PV i : Nat} (hi : i < n) : (vecs n d md PV)[i]! = pg d md PV i :=
  getElem!_ofFn_nat _ hi

theorem pg_row {d md : Nat} (hmd : md = 2 ^ d - 1) (P i : Nat) : pg d md P i = row d P i :=
  land_mask_eq_row hmd P i

theorem good_vecs {n d md PV : Nat} {LK : Nat → Nat} (hd : 0 < d) (hmd : md = 2 ^ d - 1)
    (hv : vecK n d md PV LK = true) : Good d (vecs n d md PV) where
  hd := hd
  nodup := nodup_of_lk (LK := LK) fun i hi => by
    have hi' : i < n := by rwa [vecs_size] at hi
    rw [vecs_get hi']
    exact Nat.eq_of_beq_eq_true (allN_spec hv i hi')
  lt := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hv
    have hi' : i < n := by rwa [vecs_size] at hi
    rw [← getElem!_pos _ i hi, vecs_get hi', pg_row hmd]
    exact row_lt _ _

section Mat

variable {d : Nat} {V : Array Nat} (G : Good d V)
include G

theorem perm_inv {n : Nat} (hVs : V.size = n) {M M' : Nat} (hM : Inv d V M M')
    {g : Equiv.Perm (Fin n)} (hg : ∀ x : Fin n, (permOfMat d V M)[x.val]! = g x) :
    ∀ x : Fin n, (permOfMat d V M')[x.val]! = g⁻¹ x := by
  subst hVs
  intro x
  have hm := hM.2.1 _ (mem_of_lt x.2)
  obtain ⟨hy, hgy⟩ := getElem_vidx hm
  set y := vidx V (vmul d V[x.val]! M')
  have e1 : (permOfMat d V M')[x.val]! = y := permOfMat_get x.2
  have e2 : (g ⟨y, hy⟩ : Nat) = x := by
    rw [← hg ⟨y, hy⟩, permOfMat_get hy, hgy, ← vmul_mmul, hM.2.2.2,
      vmul_idM G.hd (G.lt _ (mem_of_lt x.2)), vidx_get G.nodup x.2]
  have e3 : g ⟨y, hy⟩ = x := Fin.ext e2
  have e4 : g⁻¹ x = ⟨y, hy⟩ := by
    rw [← e3]
    simp
  rw [e1, e4]

theorem perm_mmul_get {A B : Nat} (hA : ∀ v ∈ V, vmul d v A ∈ V) {x : Nat} (hx : x < V.size) :
    (permOfMat d V (mmul d A B))[x]! = (permOfMat d V B)[(permOfMat d V A)[x]!]! := by
  rw [permOfMat_mmul hA, compA_get hx]

theorem perm_lt {A : Nat} (hA : ∀ v ∈ V, vmul d v A ∈ V) {x : Nat} (hx : x < V.size) :
    (permOfMat d V A)[x]! < V.size := by
  rw [permOfMat_get hx]
  exact (getElem_vidx (hA _ (mem_of_lt hx))).1

theorem perm_lt' {n : Nat} (hVs : V.size = n) {A : Nat} (hA : ∀ v ∈ V, vmul d v A ∈ V) {x : Nat}
    (hx : x < n) : (permOfMat d V A)[x]! < n := by
  have := perm_lt G hA (x := x) (by rw [hVs]; exact hx)
  rwa [hVs] at this

end Mat

section Gens

variable {n w kS nb BP d md L I PV : Nat} {PS PSI SM SMI LK : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
  (hv : vecK n d md PV LK = true)
  (hg : ∀ j < kS, bindK n w d md L I PV (PS j) (SM j) (SMI j) = true)

theorem mulK_eq' (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (A B : Nat) :
    mulK d md L A B = mmul d A B := mulK_eq hd hmd hL A B

include hb hd hmd hL hI hv hg in
theorem rep_S {j : Nat} (hj : j < kS) : Rep d (vecs n d md PV) S[j]! (SM j) (SMI j) := by
  have G := good_vecs hd hmd hv
  have hVs := vecs_size n d md PV
  have h := hg j hj
  unfold bindK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hS : S[j]! = unpack n w (PS j) := hb.2.2.2.2.1 j hj
  have hs : S[j]!.size = (vecs n d md PV).size := by rw [hS, hVs]; simp [unpack]
  have himg : ∀ i < (vecs n d md PV).size, (S[j]!)[i]! < (vecs n d md PV).size ∧
      (vecs n d md PV)[(S[j]!)[i]!]! = vmul d (vecs n d md PV)[i]! (SM j) := by
    intro i hi
    rw [hVs] at hi ⊢
    have h4 := allN_spec h1 i hi
    rw [Orb.strictB_eq] at h4
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
    have h5' := Nat.blt_eq.mp h5
    rw [hS, unpack_get hi, vecs_get h5', vecs_get hi, ← vmulK_eq hmd]
    exact ⟨h5', Nat.eq_of_beq_eq_true h6⟩
  obtain ⟨hinv, hpm⟩ := inv_of_images G.hd G.nodup G.lt hs himg
    (by rw [← mulK_eq hd hmd hL, Nat.eq_of_beq_eq_true h2, hI])
    (by rw [← mulK_eq hd hmd hL, Nat.eq_of_beq_eq_true h3, hI])
  exact ⟨hpm, hinv⟩

theorem letM_lt {SM SMI : Nat → Nat} {kS l : Nat} (hl : l < kS) : letM SM SMI kS l = SM l := by
  unfold letM
  rw [nIf_eq, blt_dec]
  simp [hl]

theorem letM_ge {SM SMI : Nat → Nat} {kS l : Nat} (hl : ¬ l < kS) :
    letM SM SMI kS l = SMI (l - kS) := by
  unfold letM
  rw [nIf_eq, blt_dec]
  simp [hl]

theorem letterK_lt {kS l : Nat} (hl : l < kS) : letterK PS PSI kS l = PS l := by
  unfold letterK
  rw [nIf_eq, blt_dec]
  simp [hl]

theorem letterK_ge {kS l : Nat} (hl : ¬ l < kS) : letterK PS PSI kS l = PSI (l - kS) := by
  unfold letterK
  rw [nIf_eq, blt_dec]
  simp [hl]

include hb hp hd hmd hL hI hv hg in
theorem letter_rep {l : Nat} (hl : l < kS + kS) :
    Inv d (vecs n d md PV) (letM SM SMI kS l) (letM SMI SM kS l) ∧
      ∀ x < n, pg w (mask w) (letterK PS PSI kS l) x =
        (permOfMat d (vecs n d md PV) (letM SM SMI kS l))[x]! := by
  have G := good_vecs hd hmd hv
  have hVs := vecs_size n d md PV
  by_cases hlk : l < kS
  · rw [letM_lt hlk, letM_lt hlk, letterK_lt hlk]
    have hr := rep_S hb hd hmd hL hI hv hg hlk
    refine ⟨hr.2, fun x hx => ?_⟩
    rw [← unpack_get hx, ← hb.2.2.2.2.1 l hlk, hr.1]
  · have hj : l - kS < kS := by omega
    rw [letM_ge hlk, letM_ge hlk, letterK_ge hlk]
    have hr := rep_S hb hd hmd hL hI hv hg hj
    refine ⟨hr.2.symm, fun x hx => ?_⟩
    obtain ⟨_, hPSI⟩ := prep_PS hb hp hj
    have hg' : ∀ x : Fin n,
        (permOfMat d (vecs n d md PV) (SM (l - kS)))[x.val]! = permOfArr n S[l - kS]! x :=
      fun x => by
        rw [← hr.1]
        exact rep_S_of hb hp (l - kS) (by rw [hb.2.2.2.1]; exact hj) x
    rw [perm_inv G hVs hr.2 hg' ⟨x, hx⟩, hPSI ⟨x, hx⟩]

end Gens

structure LevM (n w d : Nat) (V : Array Nat) (R o : Nat) (Lv : Level) (TM TIM : Nat → Nat) :
    Prop where
  cnt : rcnt R = Lv.pts.size
  pt : ∀ k < Lv.pts.size, rpt w (mask w) R k = Lv.pts[k]!
  pts_lt : ∀ k < Lv.pts.size, Lv.pts[k]! < n
  pos : ∀ z < n, (rpos w (mask w) (n * w) R z < rcnt R ↔ Lv.pos[z]! < Lv.pts.size)
  posE : ∀ z < n, Lv.pos[z]! < Lv.pts.size → rpos w (mask w) (n * w) R z = Lv.pos[z]!
  inv : ∀ k < Lv.pts.size, Inv d V (TM (o + k)) (TIM (o + k))
  tr : ∀ k < Lv.pts.size, ∀ x < n, (Lv.tr[k]!)[x]! = (permOfMat d V (TM (o + k)))[x]!
  trInv : ∀ k < Lv.pts.size, ∀ x < n, (Lv.trInv[k]!)[x]! = (permOfMat d V (TIM (o + k)))[x]!

theorem bIf_false_true {t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t false = true) :
    e = true := h

section Levels

variable {n w kS nb BP d md L I PV : Nat} {PS PSI SM SMI LK LR ST OF TM TIM : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
  (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
  (hv : vecK n d md PV LK = true)
  (hg : ∀ j < kS, bindK n w d md L I PV (PS j) (SM j) (SMI j) = true)
  (ht : TreeOK n w PS PSI LR kS nb BP) (hst : StepsOK n w PS ST kS nb BP)
  (htr : ∀ l < nb, trK n w (n * w) d md L I SM SMI TM TIM kS (ST l) (LR l) (OF l) = true)

theorem step_mat {i j : Nat} (hi : i ≤ nb) (hj : j < (rawSteps n S base i).size)
    (hl : stAt (stepsAt n w PS kS BP i) j < kS + kS)
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
    (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
    (hv : vecK n d md PV LK = true)
    (hg : ∀ j < kS, bindK n w d md L I PV (PS j) (SM j) (SMI j) = true) :
    Inv d (vecs n d md PV) (letM SM SMI kS (stAt (stepsAt n w PS kS BP i) j))
        (letM SMI SM kS (stAt (stepsAt n w PS kS BP i) j)) ∧
      ∀ x < n, ((rawSteps n S base i)[j]!)[x]! =
        (permOfMat d (vecs n d md PV) (letM SM SMI kS (stAt (stepsAt n w PS kS BP i) j)))[x]! := by
  obtain ⟨hI', hR⟩ := letter_rep (SM := SM) (SMI := SMI) hb hp hd hmd hL hI hv hg hl
  refine ⟨hI', fun x hx => ?_⟩
  rw [← (steps_eq hb hp hk hi hbl).2 j hj x hx, hR x hx]

include hb hp hk hbl hd hmd hL hI hv hg ht hst htr in
theorem levM_of {l : Nat} (hl : l < nb) :
    LevM n w d (vecs n d md PV) (LR l) (OF l) (lev n S base l) TM TIM := by
  have G := good_vecs hd hmd hv
  have hVs := vecs_size n d md PV
  obtain ⟨hpl, A⟩ := agree_treeK hb hp hbl hl (ht l hl).1 (ht l hl).2
  have hT : ST l = stepsAt n w PS kS BP l := hst l hl
  set R := LR l
  set o := OF l
  set TK := fun k => treeF (stp n S base l) (rpar w (mask w) (n * w) R) (rlab n (n * w) R) k k
    with hTK
  have htr' := htr l hl
  unfold trK at htr'
  obtain ⟨h0, htr'⟩ := (bAnd_iff _ _).1 htr'
  obtain ⟨h0', htr'⟩ := (bAnd_iff _ _).1 htr'
  have hstep : ∀ k < rcnt R, 0 < k →
      stAt (ST l) (rlab n (n * w) R k) < kS + kS ∧
      TM (o + k) = mmul d (TM (o + rpar w (mask w) (n * w) R k))
        (letM SM SMI kS (stAt (ST l) (rlab n (n * w) R k))) ∧
      TIM (o + k) = mmul d (letM SMI SM kS (stAt (ST l) (rlab n (n * w) R k)))
        (TIM (o + rpar w (mask w) (n * w) R k)) := by
    intro k hk' hk0
    have e0 := allN_spec htr' k hk'
    rw [beq_zero_false hk0] at e0
    have e := bIf_false_true (t := true) e0
    rw [Orb.strictB_eq, Orb.strictB_eq] at e
    obtain ⟨e1, e⟩ := (bAnd_iff _ _).1 e
    obtain ⟨e2, e3⟩ := (bAnd_iff _ _).1 e
    rw [mulK_eq' hd hmd hL] at e2 e3
    exact ⟨Nat.blt_eq.mp e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩
  have key : ∀ k, k < rcnt R → Inv d (vecs n d md PV) (TM (o + k)) (TIM (o + k)) ∧
      ∀ x : Fin n, (permOfMat d (vecs n d md PV) (TM (o + k)))[x.val]! = TK k x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk'
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.add_zero, Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h0', hI]
        refine ⟨inv_idM hd G.lt, fun x => ?_⟩
        rw [permOfMat_idM hd G.nodup G.lt, hVs, idA_get x.2, hTK]
        simp only [treeF_zero]
        rfl
      · obtain ⟨hpk, hlk⟩ := hpl k hk' hk0
        obtain ⟨hl2, hM, hMI⟩ := hstep k hk' hk0
        rw [hT] at hl2 hM hMI
        obtain ⟨ihI, ihR⟩ := ih _ hpk (by omega)
        obtain ⟨sI, sR⟩ := step_mat hl.le hlk hl2 hb hp hk hbl hd hmd hL hI hv hg
        refine ⟨by rw [hM, hMI]; exact ihI.mul hd sI, fun x => ?_⟩
        rw [hM, perm_mmul_get G ihI.1 (by rw [hVs]; exact x.2), ihR x, ← sR _ (Fin.is_lt _),
          (rep_stp hb hp hlk) (TK _ x), hTK]
        dsimp only
        rw [treeF_step (c := rcnt R) (fun k hk hk0 => (hpl k hk hk0).1) hk' hk0,
          Equiv.Perm.mul_apply]
  refine ⟨A.cnt, A.pt, (native_facts hb hp hl (hbl l hl)).pts_lt, A.pos, A.posE,
    fun k hk' => (key k (by rw [A.cnt]; exact hk')).1,
    fun k hk' x hx => ?_, fun k hk' x hx => ?_⟩
  · rw [(A.tr k hk').1 ⟨x, hx⟩, (key k (by rw [A.cnt]; exact hk')).2 ⟨x, hx⟩]
  · obtain ⟨kI, kR⟩ := key k (by rw [A.cnt]; exact hk')
    rw [(A.tr k hk').2 ⟨x, hx⟩, perm_inv G hVs kI kR ⟨x, hx⟩]

end Levels

theorem siftMK_succ (n w nw d md L I PV : Nat) (LK LR OF TIM : Nat → Nat) (BP f l G : Nat) :
    siftMK n w nw d md L I PV LK LR OF TIM BP (f + 1) l G =
      strictB (LR l) (fun R =>
        strictB (vmulK d md (pg d md PV (pg w (mask w) BP l)) G) (fun u =>
        strictB (LK u) (fun q => bAnd(Nat.blt q n, bAnd(Nat.beq (pg d md PV q) u,
        strictB (rpos w (mask w) nw R q) (fun k => bIf(Nat.blt k (rcnt R),
          strictB (mulK d md L G (TIM (Nat.add (OF l) k)))
            (siftMK n w nw d md L I PV LK LR OF TIM BP f (Nat.succ l)), false))))))) := rfl

section Sift

variable {n w kS nb BP d md L I PV : Nat} {LK LR OF TM TIM : Nat → Nat} {PS : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base) (hbl : ∀ t < nb, base[t]! < n)
  (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
  (hv : vecK n d md PV LK = true)
  (hlev : ∀ l < nb, LevM n w d (vecs n d md PV) (LR l) (OF l) (lev n S base l) TM TIM)

include hb hbl hd hmd hL hI hv hlev in
theorem siftA_of_siftMK : ∀ f l, l + f = nb → ∀ (G : Nat) (g : Array Nat),
    (∀ v ∈ vecs n d md PV, vmul d v G ∈ vecs n d md PV) →
    (∀ x < n, g[x]! = (permOfMat d (vecs n d md PV) G)[x]!) →
    siftMK n w (n * w) d md L I PV LK LR OF TIM BP f l G = true →
    siftA n (rawLevels n S base) base l g = true := by
  have G0 := good_vecs hd hmd hv
  have hVs := vecs_size n d md PV
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  intro f
  induction f with
  | zero =>
    intro l hl G g _ hg h
    have hGI : G = idM d := by
      rw [← hI]
      exact Nat.eq_of_beq_eq_true h
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)]
    unfold eqA
    rw [allLt_iff]
    intro x hx
    rw [hg x hx, hGI, permOfMat_idM hd G0.nodup G0.lt, hVs, idA_get hx]
    exact beq_self_eq_true _
  | succ f ih =>
    intro l hl G g hG hg h
    have hlb : l < nb := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    have Lv := hlev l hlb
    have hbt : base[l]! = pg w (mask w) BP l := hb.2.2.2.2.2.2 l hlb
    have hbn := hbl l hlb
    rw [siftMK_succ] at h
    simp only [Orb.strictB_eq] at h
    obtain ⟨hq, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hu, h⟩ := (bAnd_iff _ _).1 h
    rw [bIf_eq] at h
    split at h
    · rename_i hk
      have hq' := Nat.blt_eq.mp hq
      have hk' := Nat.blt_eq.mp hk
      have hu2 : vmulK d md (pg d md PV (pg w (mask w) BP l)) G =
          vmul d (vecs n d md PV)[base[l]!]! G := by
        rw [vmulK_eq hmd, hbt, vecs_get (hbt ▸ hbn)]
      set u := vmulK d md (pg d md PV (pg w (mask w) BP l)) G
      set q := LK u
      have hu' : (vecs n d md PV)[q]! = u := by
        rw [vecs_get hq']
        exact Nat.eq_of_beq_eq_true hu
      have hgb : g[base[l]!]! = q := by
        rw [hg _ hbn, permOfMat_get (by rw [hVs]; exact hbn), ← hu2, ← hu',
          vidx_get G0.nodup (by rw [hVs]; exact hq')]
      have hK := (Lv.pos q hq').1 hk'
      have hKe := Lv.posE q hq' hK
      rw [siftA, dite_eq_left hls, chainLevels_getElem hls, hgb]
      simp only [hK, decide_true, Bool.true_and]
      have hKi := Lv.inv _ hK
      rw [hKe, mulK_eq' hd hmd hL, Nat.add_eq] at h
      refine ih (l + 1) (by omega) _ _ (maps_mmul hG hKi.2.1) (fun x hx => ?_) h
      have hgx : g[x]! < n := by
        rw [hg x hx]
        exact perm_lt' G0 hVs hG hx
      rw [compA_get hx, Lv.trInv _ hK _ hgx, hg x hx,
        perm_mmul_get G0 hG (by rw [hVs]; exact hx)]
    · exact absurd h Bool.false_ne_true

end Sift

section Sch

variable {n w kS nb BP d md L I PV : Nat} {PS PSI SM SMI LK LR ST OF TM TIM : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hk : kS < 128) (hbl : ∀ t < nb, base[t]! < n)
  (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
  (hv : vecK n d md PV LK = true)
  (hg : ∀ j < kS, bindK n w d md L I PV (PS j) (SM j) (SMI j) = true)
  (hst : StepsOK n w PS ST kS nb BP)
  (hlev : ∀ l < nb, LevM n w d (vecs n d md PV) (LR l) (OF l) (lev n S base l) TM TIM)

include hb hp hk hbl hd hmd hL hI hv hg hst hlev in
theorem schreierOK_of_schMK {i : Nat} (hi : i < nb)
    (hs : ∀ h < rcnt (LR i),
      schMK n w (n * w) d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i (ST i) h 1 = true)
    (chunks : Nat) :
    CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i (rawSteps n S base i)
      (rawLevels n S base)[i]! chunks = true := by
  have G0 := good_vecs hd hmd hv
  have hVs := vecs_size n d md PV
  have Lv := hlev i hi
  have hT : ST i = stepsAt n w PS kS BP i := hst i hi
  obtain ⟨hcnt, hseq⟩ := steps_eq hb hp hk hi.le hbl
  change CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
    (rawSteps n S base i) (lev n S base i) chunks = true
  unfold CFSG.Monster.B.Co2.Native.schreierOK
  apply parLt_of_forall
  intro h hh
  rw [allLt_iff]
  intro j hj
  dsimp only
  have hhc : h < rcnt (LR i) := by rw [Lv.cnt]; exact hh
  have hsh := hs h hhc
  unfold schMK at hsh
  simp only [Orb.strictB_eq] at hsh
  have hsh0 := allN_spec hsh 0 (by decide)
  simp only [Nat.add_eq, Nat.add_zero] at hsh0
  have hsh1 := bIf_of_true (blt_true hhc) hsh0
  rw [hT] at hsh1
  have hjT : j < stCnt (stepsAt n w PS kS BP i) := by rw [hcnt]; exact hj
  have hsj := allN_spec hsh1 j hjT
  obtain ⟨hl2, hsj⟩ := (bAnd_iff _ _).1 hsj
  obtain ⟨hkc, hsj⟩ := (bAnd_iff _ _).1 hsj
  have hl2' := Nat.blt_eq.mp hl2
  obtain ⟨sI, sR⟩ := step_mat (SM := SM) (SMI := SMI) hi.le hj hl2' hb hp hk hbl hd hmd hL hI hv hg
  have hph := Lv.pts_lt h hh
  have hp' : rpt w (mask w) (LR i) h = (lev n S base i).pts[h]! := Lv.pt h hh
  rw [hp', hseq j hj _ hph] at hkc hsj
  set s := (rawSteps n S base i)[j]!
  set z := s[(lev n S base i).pts[h]!]!
  have hz : z < n := by
    change s[(lev n S base i).pts[h]!]! < n
    rw [sR _ hph]
    exact perm_lt' G0 hVs sI.1 hph
  have hK := (Lv.pos z hz).1 (Nat.blt_eq.mp hkc)
  have hKe := Lv.posE z hz hK
  rw [hKe] at hsj
  simp only [hK, decide_true, Bool.true_and]
  have hIh := Lv.inv h hh
  have hIk := Lv.inv _ hK
  rw [mulK_eq' hd hmd hL, mulK_eq' hd hmd hL] at hsj
  refine siftA_of_siftMK hb hbl hd hmd hL hI hv hlev (nb - (i + 1)) (i + 1) (by omega) _ _
    (maps_mmul (maps_mmul hIh.1 sI.1) hIk.2.1) (fun x hx => ?_) hsj
  have hx' : x < (vecs n d md PV).size := by rw [hVs]; exact hx
  have h1 : (permOfMat d (vecs n d md PV) (TM (OF i + h)))[x]! < n :=
    perm_lt' G0 hVs hIh.1 hx
  have h2 : (permOfMat d (vecs n d md PV) (letM SM SMI kS (stAt (stepsAt n w PS kS BP i) j)))[
      (permOfMat d (vecs n d md PV) (TM (OF i + h)))[x]!]! < n :=
    perm_lt' G0 hVs sI.1 h1
  rw [compA_get hx, compA_get hx, Lv.tr h hh x hx, sR _ h1, Lv.trInv _ hK _ h2,
    perm_mmul_get G0 (maps_mmul hIh.1 sI.1) hx', perm_mmul_get G0 hIh.1 hx']

end Sch

theorem rawChainMK_sound {n w kS kO nb BP chunks d md L I PV : Nat}
    {PS PSI LR ST SM SMI LK OF TM TIM : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
    {D : List (List Int)} (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) (hst : StepsOK n w PS ST kS nb BP)
    (hd : 0 < d) (hmd : md = 2 ^ d - 1) (hL : L = lanes d) (hI : I = idM d)
    (hv : vecK n d md PV LK = true)
    (hg : ∀ j < kS, bindK n w d md L I PV (PS j) (SM j) (SMI j) = true)
    (htr : ∀ l < nb, trK n w (n * w) d md L I SM SMI TM TIM kS (ST l) (LR l) (OF l) = true)
    (hs : SchMOK n w (n * w) d md L I PV PS PSI SM SMI LK LR OF TM TIM ST kS BP nb) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  obtain ⟨hk0, hH⟩ := Orb.rawHeadOK_of hb hh
  have hdd := Orb.hd_of_head hk0 hH
  obtain ⟨hp, _, hkS⟩ := Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht' => hdd.base_lt t (by omega)
  have hlev : ∀ l < nb, LevM n w d (vecs n d md PV) (LR l) (OF l) (lev n S base l) TM TIM :=
    fun l hl => levM_of hb hp hkS hbl hd hmd hL hI hv hg ht hst htr hl
  have hperm : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true := by
    have h' := hH
    unfold rawHeadOK at h'
    simp only [Bool.and_eq_true] at h'
    exact fun j hj => allLt_spec h'.1.1.1.1.2 hj
  have hlv : ∀ i < base.size, levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]! = true := by
    intro i hi
    rw [rawLevels_get hi]
    refine levelOK_of (Orb.levelOKT_bfs (hdd.base_lt i hi) (Orb.steps_lt hdd))
      (levelTrOK_bfs fun j hj => ?_)
    refine rep_of_mem_levelSteps (base := base) (i := i) hperm (t := (rawSteps n S base i)[j]!) ?_
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  have hsc : ∀ i < base.size, CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks = true := fun i hi =>
    schreierOK_of_schMK hb hp hkS hbl hd hmd hL hI hv hg hst hlev (hbs ▸ hi)
      (hs i (hbs ▸ hi)) chunks
  change (rawHeadOK n (S.extract 0 kO) S base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D) &&
    allLt base.size (fun i => levelOK n base[i]! (rawSteps n S base i)
      (rawLevels n S base)[i]!) &&
    allLt base.size (fun i => CFSG.Monster.B.Co2.Native.schreierOK n (rawLevels n S base) base i
      (rawSteps n S base i) (rawLevels n S base)[i]! chunks)) = true
  rw [hH, allLt_iff.2 hlv, allLt_iff.2 hsc]
  rfl

theorem levels_cnt {n w kS kO nb BP : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {D : List (List Int)} (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (ht : TreeOK n w PS PSI LR kS nb BP) {i : Nat} (hi : i < nb) :
    (rawLevels n S base)[i]!.pts.size = rcnt (LR i) := by
  obtain ⟨hk0, hH⟩ := Orb.rawHeadOK_of hb hh
  have hdd := Orb.hd_of_head hk0 hH
  obtain ⟨hp, _, _⟩ := Orb.head_facts hh
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hbl : ∀ t < nb, base[t]! < n := fun t ht' => hdd.base_lt t (by omega)
  exact (agree_treeK hb hp hbl hi (ht i hi).1 (ht i hi).2).2.cnt.symm

end CFSG.KS.MatSch

end

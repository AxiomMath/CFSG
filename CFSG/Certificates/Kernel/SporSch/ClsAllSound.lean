module

public import Certificates.Data.Kernel.SporSch.ClsAll
public import CFSG.Certificates.Kernel.SporSch.PtCntSound
public import CFSG.Certificates.Kernel.SporSch.J1CentSound

public section

namespace CFSG.KS.SporSch.CAll

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier Finset

theorem foldUp_add_lt {F : Nat → Nat → Nat} {g : Nat → Nat} :
    ∀ len, (∀ t < len, ∀ s, F t s = s + g t) →
      ∀ s, foldUp len F s = s + ∑ t ∈ range len, g t := by
  intro len
  induction len with
  | zero => intro _ s; rw [CFSG.KC.Pack.foldUp_eq]; simp
  | succ len ih =>
    intro hF s
    have e := ih (fun t ht => hF t (by omega)) s
    rw [CFSG.KC.Pack.foldUp_eq] at e ⊢
    rw [List.range_succ, List.foldl_append, e, List.foldl_cons, List.foldl_nil,
      hF len (by omega), sum_range_succ, Nat.add_assoc]

theorem stepJ_my0 (w m BP nb mx r s : Nat) (R T : List Nat) (c : Nat) :
    stepJ w m BP nb mx 0 r s R T c =
      c + if ordF w m BP nb (apL w m T) mx = true then 1 else 0 := by
  unfold stepJ
  cases ordF w m BP nb (apL w m T) mx
  · rfl
  · rfl

theorem enumJ_succ' (n w m nw BP nb mx my r s : Nat) (LR TR : Nat → Nat) (R : List Nat)
    (d i : Nat) (L : List Nat) (c : Nat) :
    enumJ n w m nw BP nb mx my r s LR TR R (d + 1) i L c =
      foldUp (rcnt (LR i)) (fun k c => enumJ n w m nw BP nb mx my r s LR TR R d (i + 1)
        (TR (roff n nw (LR i) + k) :: L) c) c := by
  change strictN (LR i) (fun Q => foldUp (rcnt Q) (fun k c => strictN (TR (roff n nw Q + k))
    (fun t => enumJ n w m nw BP nb mx my r s LR TR R d (i + 1) (t :: L) c)) c) = _
  rw [CIdx.strictN_eq]
  simp only [CIdx.strictN_eq]

theorem cntJB_eq' (n w m nw BP nb mx my r s : Nat) (LR TR : Nat → Nat) (R : List Nat)
    (lo len : Nat) : cntJB n w m nw BP nb mx my r s LR TR R lo len =
    ∑ l ∈ range len, if lo + l < rcnt (LR 0) then cntJ n w m nw BP nb mx my r s LR TR R (lo + l)
      else 0 := by
  unfold cntJB
  rw [PtCnt.foldUp_add, Nat.zero_add]
  intro l c
  rw [CIdx.strictN_eq]
  change Bool.rec (motive := fun _ => Nat) c (c + _) (Nat.blt (lo + l) (rcnt (LR 0))) = _
  by_cases h : lo + l < rcnt (LR 0)
  · rw [show Nat.blt (lo + l) (rcnt (LR 0)) = true by rw [Nat.blt_eq]; exact h, ite_eq_left h]
    rfl
  · rw [show Nat.blt (lo + l) (rcnt (LR 0)) = false from Bool.eq_false_iff.2 fun e =>
      h (by rw [Nat.blt_eq] at e; exact e), ite_eq_right h, Nat.add_zero]

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem ble_iff {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

section Chain

variable {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS kO nb BP S base D)
include hQ

theorem kO_le : kO ≤ kS := by
  have h := hQ.2.1
  unfold headK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact Nat.le_of_ble_eq_true h.2.2.1

omit hQ in
theorem gen_mem {l : Nat} (hl : l < kO) : permOfArr n S[l]! ∈ Gen n S kO :=
  Subgroup.subset_closure ⟨⟨l, hl⟩, rfl⟩

theorem acts_conjF {l : Nat} (hl : l < kO) {f : Nat → Nat} {g : Equiv.Perm (Fin n)}
    (hf : Acts n f g) :
    Acts n (conjF w (mask w) (PS l) (PSI l) f) (permOfArr n S[l]! * g * (permOfArr n S[l]!)⁻¹) := by
  intro y
  unfold conjF
  obtain ⟨h1, h2⟩ := Orb.prep_PS hQ.1 (perms hQ) (lt_of_lt_of_le hl (kO_le hQ))
  rw [h2 y, hf, h1]
  rfl

theorem enumJ_count {mx r s : Nat} {R : List Nat} : ∀ d i, i + d = nb →
    ∀ (L : List Nat) (pre : Equiv.Perm (Fin n)), pre ∈ Gen n S kO →
      Acts n (apL w (mask w) L.reverse) pre → ∀ c,
      enumJ n w (mask w) (n * w) BP nb mx 0 r s LR TR R d i L c =
        c + (products (trLists n S base i d)).countP fun h => decide (orderOf (pre * h) = mx) := by
  intro d
  induction d with
  | zero =>
    intro i _ L pre hpre hL c
    change stepJ w (mask w) BP nb mx 0 r s R L.reverse c = _
    rw [stepJ_my0]
    simp only [trLists, List.range_zero, List.map_nil, products, List.countP_singleton, mul_one]
    have := ordF_iff hQ (e := mx) hL hpre
    by_cases ho : orderOf pre = mx
    · rw [this.2 ho, decide_eq_true ho]
    · have h' : ordF w (mask w) BP nb (apL w (mask w) L.reverse) mx = false :=
        Bool.eq_false_iff.2 fun h => ho (this.1 h)
      rw [h', decide_eq_false ho]
  | succ d ih =>
    intro i hi L pre hpre hL c
    have hin : i < nb := by omega
    rw [enumJ_succ', foldUp_add_lt (g := fun k => (products (trLists n S base (i + 1) d)).countP
      fun h => decide (orderOf (pre * trP n S base i k * h) = mx))]
    · rw [trLists_succ, PtCnt.countP_products_cons, List.map_map, PtCnt.sum_list_range,
        rcnt_eq hQ hin]
      congr 1
    · intro k hk c'
      rw [rcnt_eq hQ hin] at hk
      refine ih (i + 1) (by omega) _ _ (Subgroup.mul_mem _ hpre (tr_fix hQ hin hk).1) ?_ c'
      intro y
      rw [List.reverse_cons, apL_append, apL_cons, apL_nil, pg_TR hQ hin hk, hL,
        Equiv.Perm.mul_apply]

theorem cntJ_count {mx r s : Nat} {R : List Nat} (hnb : 0 < nb) {k0 : Nat}
    (hk : k0 < sz n S base 0) :
    cntJ n w (mask w) (n * w) BP nb mx 0 r s LR TR R k0 =
      (products (trLists n S base 1 (nb - 1))).countP
        fun h => decide (orderOf (trP n S base 0 k0 * h) = mx) := by
  unfold cntJ
  rw [CIdx.strictN_eq, CIdx.strictN_eq]
  change enumJ n w (mask w) (n * w) BP nb mx 0 r s LR TR R (nb - 1) 1
    [TR (roff n (n * w) (LR 0) + k0)] 0 = _
  rw [enumJ_count hQ (nb - 1) 1 (by omega) _ (trP n S base 0 k0) (tr_fix hQ hnb hk).1
    (fun y => by rw [List.reverse_singleton, apL_cons, apL_nil, pg_TR hQ hnb hk]), Nat.zero_add]

theorem card_ord_eq_sum {mx r s : Nat} {R CS : List Nat} {L : Nat} (hnb : 0 < nb)
    (hCS : rcnt (LR 0) ≤ CS.length * L)
    (hc : ∀ b < CS.length,
      cntJB n w (mask w) (n * w) BP nb mx 0 r s LR TR R (b * L) L = CS.getD b 0) :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ Gen n S kO ∧ orderOf g = mx} = CS.sum := by
  rw [J1C.card_filter hQ]
  have hs : CS.sum = ∑ b ∈ range CS.length, CS.getD b 0 := by
    have := PtCnt.sum_map_getD (fun x => x) CS
    rwa [List.map_id'] at this
  rw [hs, sum_congr rfl fun b hb => (hc b (mem_range.1 hb)).symm]
  simp only [cntJB_eq']
  rw [PtCnt.sum_blocks (fun k => if k < rcnt (LR 0) then
      cntJ n w (mask w) (n * w) BP nb mx 0 r s LR TR R k else 0) L, PtCnt.sum_range_ind hCS,
    rcnt_eq hQ hnb, sum_congr rfl fun k hk => cntJ_count hQ hnb (mem_range.1 hk)]
  obtain ⟨d, rfl⟩ : ∃ d, nb = d + 1 := ⟨nb - 1, by omega⟩
  rw [show (0 : Nat) = 0 + 0 from rfl, trLists_succ, PtCnt.countP_products_cons, List.map_map,
    PtCnt.sum_list_range]
  refine sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.add_sub_cancel]

omit hQ in
theorem clsGK_facts {mx N K ncl : Nat} {E CL O IX PA LB DP : Nat → Nat} {k : Nat}
    (h : clsGK n w (mask w) (n * w) BP nb N kO mx PS PSI LR TR E CL O IX PA LB DP K ncl k = true)
    (hk : k < K) :
    CL k < ncl ∧ O (CL k) ≤ k ∧ k < O (CL k + 1) ∧ E k < N ∧
      (k + 1 < O (CL k + 1) → E k < E (k + 1)) ∧
      ordF w (mask w) BP nb (apL w (mask w) (elemT n (n * w) LR TR nb (E k))) mx = true ∧
      (∀ l < kO, O (CL k) ≤ IX (kO * k + l) ∧ IX (kO * k + l) < O (CL k + 1) ∧
        eqB w (mask w) BP nb (conjF w (mask w) (PS l) (PSI l)
          (apL w (mask w) (elemT n (n * w) LR TR nb (E k))))
          (apL w (mask w) (elemT n (n * w) LR TR nb (E (IX (kO * k + l))))) = true) ∧
      (k ≠ O (CL k) → O (CL k) ≤ PA k ∧ PA k < O (CL k + 1) ∧ DP (PA k) < DP k ∧ LB k < kO ∧
        eqB w (mask w) BP nb (apL w (mask w) (elemT n (n * w) LR TR nb (E k)))
          (conjF w (mask w) (PS (LB k)) (PSI (LB k))
            (apL w (mask w) (elemT n (n * w) LR TR nb (E (PA k))))) = true) := by
  have hkK : Nat.blt k K = true := blt_iff.2 hk
  simp only [clsGK, hkK, CIdx.strictB_eq] at h
  obtain ⟨h1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h6, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h7, h8⟩ := (CIdx.bAnd_iff' _ _).1 h
  refine ⟨blt_iff.1 h1, ble_iff.1 h2, blt_iff.1 h3, blt_iff.1 h4, fun hk1 => ?_, h6,
    fun l hl => ?_, fun hne => ?_⟩
  · have e : Nat.blt (Nat.succ k) (O (Nat.succ (CL k))) = true := blt_iff.2 hk1
    simp only [e] at h5
    exact blt_iff.1 h5
  · have := (allN_iff.1 h7) l hl
    obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 this
    obtain ⟨a2, a3⟩ := (CIdx.bAnd_iff' _ _).1 a
    exact ⟨ble_iff.1 a1, blt_iff.1 a2, a3⟩
  · have e : Nat.beq k (O (CL k)) = false := Bool.eq_false_iff.2 fun e => hne (beq_iff.1 e)
    simp only [e] at h8
    obtain ⟨a1, a⟩ := (CIdx.bAnd_iff' _ _).1 h8
    obtain ⟨a2, a⟩ := (CIdx.bAnd_iff' _ _).1 a
    obtain ⟨a3, a⟩ := (CIdx.bAnd_iff' _ _).1 a
    obtain ⟨a4, a5⟩ := (CIdx.bAnd_iff' _ _).1 a
    exact ⟨ble_iff.1 a1, blt_iff.1 a2, blt_iff.1 a3, blt_iff.1 a4, a5⟩

omit hQ in
theorem clsGHdK_facts {K ncl zp Z : Nat} {E O : Nat → Nat}
    (h : clsGHdK n w (mask w) (n * w) nb LR TR E O K ncl zp Z = true) :
    O 0 = 0 ∧ O ncl = K ∧ (∀ i < ncl, O i < O (i + 1)) ∧
      (∀ i, i + 1 < ncl → E (O i) < E (O (i + 1))) ∧ zp < K ∧
      ∀ x < n, apL w (mask w) (elemT n (n * w) LR TR nb (E zp)) x = pg w (mask w) Z x := by
  unfold clsGHdK at h
  obtain ⟨h1, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h2, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h3, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h4, h⟩ := (CIdx.bAnd_iff' _ _).1 h
  obtain ⟨h5, h6⟩ := (CIdx.bAnd_iff' _ _).1 h
  refine ⟨beq_iff.1 h1, beq_iff.1 h2, fun i hi => blt_iff.1 ((allN_iff.1 h3) i hi),
    fun i hi => ?_, blt_iff.1 h5, fun x hx => ?_⟩
  · have := (allN_iff.1 h4) i (by omega)
    have e : Nat.blt (Nat.succ i) ncl = true := blt_iff.2 hi
    simp only [e] at this
    exact blt_iff.1 this
  · unfold eqAllK at h6
    exact beq_iff.1 ((allN_iff.1 h6) x hx)

structure ClsFacts (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (kO nb N mx : Nat)
    (E CL O : Nat → Nat) (K ncl : Nat) : Prop where
  lt : ∀ k < K, E k < N
  ord : ∀ k < K, orderOf (el n S base nb (E k)) = mx
  inj : ∀ a < K, ∀ b < K, E a = E b → a = b
  blk : ∀ k < K, CL k < ncl ∧ O (CL k) ≤ k ∧ k < O (CL k + 1)
  blk_cl : ∀ i < ncl, ∀ k, O i ≤ k → k < O (i + 1) → k < K ∧ CL k = i
  conj : ∀ a < K, ∀ b < K, CL a = CL b →
    ∃ g ∈ Gen n S kO, g * el n S base nb (E a) * g⁻¹ = el n S base nb (E b)
  closed : ∀ a < K, ∀ g ∈ Gen n S kO, ∃ b < K, CL b = CL a ∧
    el n S base nb (E b) = g * el n S base nb (E a) * g⁻¹

theorem el_mem' {N j : Nat} (hN : ordK LR nb = N) (hj : j < N) : el n S base nb j ∈ Gen n S kO :=
  el_mem hQ (hN ▸ hj)

theorem cls_facts {mx N K ncl zp Z : Nat} {E CL O IX PA LB DP : Nat → Nat}
    (hN : ordK LR nb = N)
    (hhd : clsGHdK n w (mask w) (n * w) nb LR TR E O K ncl zp Z = true)
    (hb : ∀ k < K,
      clsGK n w (mask w) (n * w) BP nb N kO mx PS PSI LR TR E CL O IX PA LB DP K ncl k = true) :
    ClsFacts n S base kO nb N mx E CL O K ncl := by
  obtain ⟨hO0, hOK, hOm, hmin, -, -⟩ := clsGHdK_facts hhd
  have F := fun k (hk : k < K) => clsGK_facts (hb k hk) hk
  have hlt : ∀ k < K, E k < N := fun k hk => (F k hk).2.2.2.1
  have hmem : ∀ k < K, el n S base nb (E k) ∈ Gen n S kO := fun k hk => el_mem' hQ hN (hlt k hk)
  have hacts : ∀ j, Acts n (apL w (mask w) (elemT n (n * w) LR TR nb j)) (el n S base nb j) :=
    fun j y => apL_elemT hQ j y
  have hOmono : ∀ i i', i ≤ i' → i' ≤ ncl → O i ≤ O i' := by
    intro i i' hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact le_rfl
    | succ i' hle ih => exact (ih (by omega)).trans (hOm i' (by omega)).le
  have hOle : ∀ i ≤ ncl, O i ≤ K := fun i hi => hOK ▸ hOmono i ncl hi le_rfl
  have huniq : ∀ i < ncl, ∀ i' < ncl, ∀ k, O i ≤ k → k < O (i + 1) → O i' ≤ k →
      k < O (i' + 1) → i = i' := by
    intro i hi i' hi' k h1 h2 h3 h4
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hOmono (i + 1) i' (by omega) hi'.le
      omega
    · have := hOmono (i' + 1) i (by omega) hi.le
      omega
  have hblk_cl : ∀ i < ncl, ∀ k, O i ≤ k → k < O (i + 1) → k < K ∧ CL k = i := by
    intro i hi k h1 h2
    have hkK : k < K := lt_of_lt_of_le h2 (hOle (i + 1) hi)
    obtain ⟨c1, c2, c3, -⟩ := F k hkK
    exact ⟨hkK, huniq _ c1 _ hi k c2 c3 h1 h2⟩
  have hcl : ∀ k < K, ∀ p, O (CL k) ≤ p → p < O (CL k + 1) → p < K ∧ CL p = CL k :=
    fun k hk p h1 h2 => hblk_cl (CL k) (F k hk).1 p h1 h2
  have hpar : ∀ d, ∀ k < K, DP k = d → ∃ g ∈ Gen n S kO,
      g * el n S base nb (E (O (CL k))) * g⁻¹ = el n S base nb (E k) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk hd
      by_cases hr : k = O (CL k)
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [← hr]
        group
      · obtain ⟨-, -, -, -, -, -, -, hp⟩ := F k hk
        obtain ⟨p1, p2, p3, p4, p5⟩ := hp hr
        obtain ⟨hpK, hpc⟩ := hcl k hk (PA k) p1 p2
        obtain ⟨g, hg, e⟩ := ih _ (hd ▸ p3) (PA k) hpK rfl
        rw [hpc] at e
        have e' := (eqB_iff_eq hQ (hacts _) (acts_conjF hQ p4 (hacts _)) (hmem k hk)
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (gen_mem p4) (hmem _ hpK))
            (Subgroup.inv_mem _ (gen_mem p4)))).1 p5
        refine ⟨permOfArr n S[LB k]! * g, Subgroup.mul_mem _ (gen_mem p4) hg, ?_⟩
        rw [e', ← e]
        group
  have hconj0 : ∀ k < K, ∃ g ∈ Gen n S kO,
      g * el n S base nb (E (O (CL k))) * g⁻¹ = el n S base nb (E k) :=
    fun k hk => hpar _ k hk rfl
  have hconj : ∀ a < K, ∀ b < K, CL a = CL b →
      ∃ g ∈ Gen n S kO, g * el n S base nb (E a) * g⁻¹ = el n S base nb (E b) := by
    intro a ha b hb e
    obtain ⟨g, hg, eg⟩ := hconj0 a ha
    obtain ⟨g', hg', eg'⟩ := hconj0 b hb
    refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
    rw [← eg', ← eg, e]
    group
  have hclosed : ∀ a < K, ∀ g ∈ Gen n S kO, ∃ b < K, CL b = CL a ∧
      el n S base nb (E b) = g * el n S base nb (E a) * g⁻¹ := by
    intro a ha g hg
    let C : Set (Equiv.Perm (Fin n)) := {x | ∃ b < K, CL b = CL a ∧ el n S base nb (E b) = x}
    have hfin : C.Finite := Set.toFinite _
    have hstep : ∀ l < kO, ∀ x ∈ C, permOfArr n S[l]! * x * (permOfArr n S[l]!)⁻¹ ∈ C := by
      rintro l hl _ ⟨b, hb, hcb, rfl⟩
      obtain ⟨-, -, -, -, -, -, hx, -⟩ := F b hb
      obtain ⟨x1, x2, x3⟩ := hx l hl
      obtain ⟨hpK, hpc⟩ := hcl b hb _ x1 x2
      refine ⟨_, hpK, hpc.trans hcb, ?_⟩
      exact ((eqB_iff_eq hQ (acts_conjF hQ hl (hacts _)) (hacts _)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (gen_mem hl) (hmem _ hb))
          (Subgroup.inv_mem _ (gen_mem hl))) (hmem _ hpK)).1 x3).symm
    obtain ⟨b, hb, hcb, e⟩ := J1C.conj_closed hfin hstep g hg _ ⟨a, ha, rfl, rfl⟩
    exact ⟨b, hb, hcb, e⟩
  have hinc : ∀ a b, a < b → b < K → CL a = CL b → a < K → E a < E b := by
    intro a b hab hbK hc haK
    induction b, hab using Nat.le_induction with
    | base =>
      obtain ⟨-, -, -, -, h5, -⟩ := F a haK
      exact h5 (by have := (F (a + 1) hbK).2.2.1; rw [← hc] at this; exact this)
    | succ b hle ih =>
      have hbK' : b < K := by omega
      have hcb : CL b = CL a := by
        obtain ⟨c1, c2, c3, -⟩ := F (b + 1) hbK
        have := (F a haK).2.1
        exact (hcl a haK b (by rw [hc] at this ⊢; omega) (by rw [hc]; omega)).2
      exact (ih hbK' hcb.symm).trans ((F b hbK').2.2.2.2.1 (by
        have := (F (b + 1) hbK).2.2.1
        rw [← hc, ← hcb] at this
        exact this))
  have hfirst : ∀ k < K, E (O (CL k)) ≤ E k ∧ O (CL k) < K ∧ CL (O (CL k)) = CL k := by
    intro k hk
    obtain ⟨c1, c2, c3, -⟩ := F k hk
    obtain ⟨h0K, h0c⟩ := hcl k hk (O (CL k)) le_rfl (lt_of_le_of_lt c2 c3)
    refine ⟨?_, h0K, h0c⟩
    rcases Nat.lt_or_eq_of_le c2 with h | h
    · exact (hinc _ _ h hk h0c h0K).le
    · rw [h]
  have hminc : ∀ i i', i < i' → i' < ncl → E (O i) < E (O i') := by
    intro i i' hii' hi'
    induction i', hii' using Nat.le_induction with
    | base => exact hmin i hi'
    | succ i' hle ih => exact (ih (by omega)).trans (hmin i' hi')
  have hinj : ∀ a < K, ∀ b < K, E a = E b → a = b := by
    intro a ha b hb e
    have key : ∀ a < K, ∀ b < K, E a = E b → E (O (CL a)) ≤ E (O (CL b)) := by
      intro a ha b hb e
      obtain ⟨-, hbK, hbc⟩ := hfirst b hb
      obtain ⟨g, hg, eg⟩ := hconj b hb (O (CL b)) hbK hbc.symm
      obtain ⟨c, hc, hcc, ec⟩ := hclosed a ha g hg
      rw [e, eg] at ec
      have := el_inj hQ (hN ▸ hlt c hc) (hN ▸ hlt _ hbK) ec
      rw [← this]
      have := (hfirst c hc).1
      rwa [hcc] at this
    have e1 := key a ha b hb e
    have e2 := key b hb a ha e.symm
    have hcc : CL a = CL b := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact absurd (hminc _ _ h (F b hb).1) (by omega)
      · exact absurd (hminc _ _ h (F a ha).1) (by omega)
    rcases lt_trichotomy a b with h | h | h
    · exact absurd e (hinc a b h hb hcc ha).ne
    · exact h
    · exact absurd e.symm (hinc b a h ha hcc.symm hb).ne
  refine ⟨hlt, fun k hk => (ordF_iff hQ (hacts _) (hmem k hk)).1 (F k hk).2.2.2.2.2.1, hinj,
    fun k hk => ⟨(F k hk).1, (F k hk).2.1, (F k hk).2.2.1⟩, hblk_cl, hconj, hclosed⟩

theorem cls_cover {mx N K ncl : Nat} {E CL O : Nat → Nat} (hN : ordK LR nb = N)
    (hF : ClsFacts n S base kO nb N mx E CL O K ncl)
    (hK : Nat.card {g : Equiv.Perm (Fin n) // g ∈ Gen n S kO ∧ orderOf g = mx} = K)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Gen n S kO) (ho : orderOf g = mx) :
    ∃ k < K, el n S base nb (E k) = g := by
  by_contra hne
  have hne' : g ∉ {x | ∃ k < K, el n S base nb (E k) = x} := fun ⟨k, hk, e⟩ => hne ⟨k, hk, e⟩
  have hA : {x | ∃ k < K, el n S base nb (E k) = x}.ncard = K := by
    have e : {x | ∃ k < K, el n S base nb (E k) = x} =
        (fun k => el n S base nb (E k)) '' {k | k < K} := by
      ext x
      simp
    have hi : Set.InjOn (fun k => el n S base nb (E k)) {k | k < K} := fun a ha b hb e =>
      hF.inj a ha b hb (el_inj hQ (hN ▸ hF.lt a ha) (hN ▸ hF.lt b hb) e)
    rw [e, hi.ncard_image, show {k | k < K} = ((Finset.range K : Finset Nat) : Set Nat) by
      ext; simp, Set.ncard_coe_finset, Finset.card_range]
  have hsub : insert g {x | ∃ k < K, el n S base nb (E k) = x} ⊆
      {x : Equiv.Perm (Fin n) | x ∈ Gen n S kO ∧ orderOf x = mx} := by
    rintro x (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨hg, ho⟩
    · exact ⟨el_mem' hQ hN (hF.lt k hk), hF.ord k hk⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hne' (Set.toFinite _), hA] at hle
  have hc : {x : Equiv.Perm (Fin n) | x ∈ Gen n S kO ∧ orderOf x = mx}.ncard = K := by
    rw [← Nat.card_coe_set_eq]
    exact hK
  omega

end Chain

end CFSG.KS.SporSch.CAll

end

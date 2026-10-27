module

public import Certificates.Data.Kernel.Spor.ChainSK
public import CFSG.Certificates.Kernel.Spor.PointChainCard
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.ChainSKBase

public section

namespace CFSG.KS.CH.SKT

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.ONSchreier.Native CFSG.ONSchreier

theorem treePt_facts {n r root k : Nat} {STEP : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : treePt n r STEP PTS POS PAR LAB root k = true) :
    PTS k < n ∧ POS (PTS k) = k ∧ (k = 0 → PTS k = root) ∧
      (k ≠ 0 → PAR k < k ∧ LAB k < r ∧ STEP (LAB k) (PTS (PAR k)) = PTS k) := by
  unfold treePt at h
  simp only [strictB_v, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hk => ?_, fun hk => ?_⟩
  · subst hk
    have h3' : Nat.beq (PTS 0) root = true := h3
    exact Nat.eq_of_beq_eq_true h3'
  · have hb : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun e => hk (Nat.eq_of_beq_eq_true e)
    rw [hb] at h3
    dsimp only at h3
    simp only [bAnd_iff] at h3
    exact ⟨Nat.blt_eq.mp h3.1, Nat.blt_eq.mp h3.2.1, Nat.eq_of_beq_eq_true h3.2.2⟩

theorem tree_recorded {n r root t : Nat} {st : Array (Array Nat)} {STEP : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat} (hr : root < n) (hsz : st.size = r)
    (hst : ∀ j < r, ∀ x < n, (st[j]!)[x]! = STEP j x ∧ STEP j x < n)
    (htree : ∀ k < t, treePt n r STEP PTS POS PAR LAB root k = true) :
    ∀ k < t, (cbfs n root st).pos[PTS k]! < (cbfs n root st).pts.size := by
  have F := CFSG.KS.CBF.cbfs_facts hr fun j hj x hx => by
    rw [hsz] at hj
    rw [(hst j hj x hx).1]
    exact (hst j hj x hx).2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨-, -, h0, h1⟩ := treePt_facts (htree k hk)
    by_cases hk0 : k = 0
    · subst hk0
      have e := F.pos_pts 0 F.pos
      rw [F.root] at e
      rw [h0 rfl, e]
      exact F.pos
    · obtain ⟨hpar, hlab, hedge⟩ := h1 hk0
      have hq := ih (PAR k) hpar (by omega)
      have hqn := (treePt_facts (htree (PAR k) (by omega))).1
      obtain ⟨hc, -⟩ := F.closed _ hq (LAB k) (by rw [hsz]; exact hlab)
      rw [F.pts_pos _ hqn hq, (hst _ hlab _ hqn).1, hedge] at hc
      exact hc

theorem le_size_of_tree {n r root t : Nat} {st : Array (Array Nat)} {STEP : Nat → Nat → Nat}
    {PTS POS PAR LAB : Nat → Nat} (hr : root < n) (hsz : st.size = r)
    (hst : ∀ j < r, ∀ x < n, (st[j]!)[x]! = STEP j x ∧ STEP j x < n)
    (htree : ∀ k < t, treePt n r STEP PTS POS PAR LAB root k = true) :
    t ≤ (cbfs n root st).pts.size := by
  have F := CFSG.KS.CBF.cbfs_facts hr fun j hj x hx => by
    rw [hsz] at hj
    rw [(hst j hj x hx).1]
    exact (hst j hj x hx).2
  have hrec := tree_recorded hr hsz hst htree
  calc t = (Finset.range t).card := (Finset.card_range t).symm
    _ ≤ (Finset.range (cbfs n root st).pts.size).card := by
      refine Finset.card_le_card_of_injOn (fun k => (cbfs n root st).pos[PTS k]!)
        (fun k hk => ?_) (fun a ha b hb e => ?_)
      · simp only [Finset.mem_coe, Finset.mem_range] at hk ⊢
        exact hrec k hk
      · simp only [Finset.mem_coe, Finset.mem_range] at ha hb
        have ea := F.pts_pos _ (treePt_facts (htree a ha)).1 (hrec a ha)
        have eb := F.pts_pos _ (treePt_facts (htree b hb)).1 (hrec b hb)
        have e' : PTS a = PTS b := by
          rw [← ea, ← eb]
          exact congrArg (fun z => (cbfs n root st).pts[z]!) e
        calc a = POS (PTS a) := (treePt_facts (htree a ha)).2.1.symm
          _ = POS (PTS b) := by rw [e']
          _ = b := (treePt_facts (htree b hb)).2.1
    _ = (cbfs n root st).pts.size := Finset.card_range _

theorem hyp_of {n m s : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}
    {F FI : Nat → Nat → Nat} (hn : 0 < n) (hS : S.size = s) (hm : m ≤ s)
    (hF : ∀ j < s, ∀ x < n, (S[j]!)[x]! = F j x ∧ F j x < n ∧ FI j x < n ∧ FI j (F j x) = x)
    (hW : ∀ j, m ≤ j → j < s → (∀ l ∈ W[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
      ∀ x < n, F j x = W[j]!.foldr (CFSG.KS.TW.GZ F FI) x)
    (hbn : ∀ k < base.size, base[k]! < n) :
    PCC.Hyp n S base (Subgroup.closure (Set.range fun j : Fin m => permOfArr n S[j.val]!))
      (fun k => ⟨base[k]! % n, Nat.mod_lt _ hn⟩) := by
  have hrep : ∀ j < S.size, PRep n S[j]! (permOfArr n S[j]!) ∧
      PRep n (pinvs n S)[j]! (permOfArr n S[j]!)⁻¹ := fun j hj =>
    prep_permOfArr (CFSG.KS.CH.SKB.pisInv_of hS hF j hj)
  refine ⟨fun j hj => (hrep j hj).1, fun j hj => (hrep j hj).2, ?_, hbn,
    fun k hk => Nat.mod_eq_of_lt (hbn k hk)⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjm : j < m
    · apply Subgroup.subset_closure
      exact ⟨⟨j, hjm⟩, rfl⟩
    · have hjs : j < s := by omega
      obtain ⟨hl, hf⟩ := hW j (by omega) hjs
      obtain ⟨g, hg, hrg⟩ := PCC.pword_mem (S := S) (Si := pinvs n S) (j := j)
        (K := Subgroup.closure (Set.range fun j : Fin m => permOfArr n S[j.val]!))
        (fun h hh => ⟨permOfArr n S[h]!, ih h hh (by omega), (hrep h (by omega)).1,
          (hrep h (by omega)).2⟩) W[j]! (CFSG.KS.CH.SKB.plettersOK_of hl)
      rw [(hrep j hj).1.unique (prep_of_peq (CFSG.KS.CH.SKB.peq_pword_of hS hF hjs hl hf) hrg)]
      exact hg

theorem sizes_eq_of_card {n : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {G : Subgroup (Equiv.Perm (Fin n))} {B : Nat → Fin n} {t : Nat → Nat}
    (H : PCC.Hyp n S base G B) (hle : ∀ l < base.size, t l ≤ (PCC.lv n S base l).pts.size)
    (hc : Nat.card G ≤ ∏ l ∈ Finset.range base.size, t l) :
    ∀ l < base.size, (PCC.lv n S base l).pts.size = t l := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have hpos : ∀ l < base.size, 0 < t l := fun l hl => by
    by_contra h0
    have : ∏ l ∈ Finset.range base.size, t l = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hl) (by omega)
    omega
  have hsub : ∀ l < base.size,
      (PCC.lv n S base l).pts.size ≤ (MulAction.orbit (PCC.Gs G B l) (B l)).ncard := by
    intro l hl
    rw [← PCC.Dset_card H hl, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard fun x hx => PCC.Dset_sub H hl x hx
  have hGs : 0 < Nat.card (PCC.Gs G B base.size) := Nat.card_pos
  have hprod : ∏ l ∈ Finset.range base.size, (PCC.lv n S base l).pts.size ≤
      ∏ l ∈ Finset.range base.size, t l :=
    calc ∏ l ∈ Finset.range base.size, (PCC.lv n S base l).pts.size
        ≤ ∏ l ∈ Finset.range base.size, (MulAction.orbit (PCC.Gs G B l) (B l)).ncard :=
          Finset.prod_le_prod fun l hl => hsub l (Finset.mem_range.1 hl)
      _ ≤ (∏ l ∈ Finset.range base.size, (MulAction.orbit (PCC.Gs G B l) (B l)).ncard) *
          Nat.card (PCC.Gs G B base.size) := Nat.le_mul_of_pos_right _ hGs
      _ = Nat.card G := (PCC.card_chain G B base.size).symm
      _ ≤ _ := hc
  intro l hl
  exact (PCC.eq_of_prod_le base.size (fun l hl => ⟨hpos l hl, hle l hl⟩) hprod l hl).symm

end CFSG.KS.CH.SKT

end

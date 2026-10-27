module

public import Certificates.Data.Kernel.LocalQT.TreeR
public import CFSG.Certificates.Kernel.LocalQTFusionSSound

public section

namespace CFSG.KC.LQT.TR.Pf

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.RW CFSG.KC.LQT.RB CFSG.KC.LQT.TR
open CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.FS.Pf CFSG.KC.LQT.BW.Pf
open CFSG.Quasithin.H13.KGRank CFSG.QuasithinUnique.Lin2.RankCert

theorem spanIdx_congr {N : ℕ} {m1 m2 : ℕ → ℕ → ℕ} (h0 : 0 < N)
    (hag : ∀ a < N, ∀ b < N, m1 a b = m2 a b) (hcl : ∀ a < N, ∀ b < N, m1 a b < N) :
    ∀ F : List ℕ, (∀ f ∈ F, f < N) →
      spanIdx m1 F = spanIdx m2 F ∧ ∀ x ∈ spanIdx m1 F, x < N
  | [], _ => ⟨rfl, by simp [spanIdx, h0]⟩
  | f :: F, hF => by
    obtain ⟨e, hlt⟩ := spanIdx_congr h0 hag hcl F fun x hx => hF x (List.mem_cons_of_mem _ hx)
    have hf : f < N := hF f (List.mem_cons_self ..)
    have em : (spanIdx m1 F).map (m1 f) = (spanIdx m1 F).map (m2 f) :=
      List.map_congr_left fun x hx => hag f hf x (hlt x hx)
    simp only [spanIdx]
    refine ⟨by rw [em, e], fun x hx => ?_⟩
    rw [List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hlt x hx
    · exact hcl f hf y (hlt y hy)

theorem nodeCheck_filter (N : ℕ) (mul : ℕ → ℕ → ℕ) (nodes : Array (List ℕ × List ℕ)) :
    ∀ fuel j F D, nodeCheck N mul nodes fuel j F D =
      nodeCheck N mul nodes fuel j F (D.filter fun x => mul x x == 0) := by
  intro fuel
  induction fuel with
  | zero => intro j F D; rfl
  | succ fuel ih =>
    intro j F D
    have hinv : (D.filter fun x => mul x x == 0).filter (fun x => mul x x == 0) =
        D.filter fun x => mul x x == 0 := by
      rw [List.filter_filter]
      exact List.filter_congr fun x _ => Bool.and_self _
    have key : ∀ rc : ℕ × ℕ, nodeCheck N mul nodes fuel rc.2 (rc.1 :: F)
        (D.filter fun y => mul y rc.1 == mul rc.1 y) = nodeCheck N mul nodes fuel rc.2 (rc.1 :: F)
        ((D.filter fun x => mul x x == 0).filter fun y => mul y rc.1 == mul rc.1 y) := by
      intro rc
      rw [ih _ _ (D.filter _), ih _ _ ((D.filter _).filter _), List.filter_filter,
        List.filter_filter, List.filter_filter]
      exact congrArg _ (List.filter_congr fun x _ => by
        cases (mul x x == 0) <;> cases (mul x rc.1 == mul rc.1 x) <;> rfl)
    simp only [nodeCheck, hinv, key]

theorem nodeCheck_congr {N : ℕ} {m1 m2 : ℕ → ℕ → ℕ} (h0 : 0 < N)
    (hag : ∀ a < N, ∀ b < N, m1 a b = m2 a b) (hcl : ∀ a < N, ∀ b < N, m1 a b < N)
    (nodes : Array (List ℕ × List ℕ)) :
    ∀ fuel j F D, (∀ f ∈ F, f < N) → (∀ x ∈ D, x < N) →
      nodeCheck N m2 nodes fuel j F D = true → nodeCheck N m1 nodes fuel j F D = true := by
  intro fuel
  induction fuel with
  | zero => intro j F D _ _ h; exact h
  | succ fuel ih =>
    intro j F D hF hD h
    have hinv : D.filter (fun x => m1 x x == 0) = D.filter (fun x => m2 x x == 0) :=
      List.filter_congr fun x hx => by rw [hag x (hD x hx) x (hD x hx)]
    obtain ⟨hsp, -⟩ := spanIdx_congr h0 hag hcl F hF
    simp only [nodeCheck] at h ⊢
    rw [hinv, hsp]
    generalize hR : pairsOf (nodes.getD j ([], [])).1 = reps at h ⊢
    generalize hW : triplesOf (nodes.getD j ([], [])).2 = wit at h ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h ⊢
    rcases h with h | ⟨⟨⟨hsl, hc⟩, hw⟩, hr⟩
    · exact Or.inl h
    right
    have hrN : ∀ rc ∈ reps, rc.1 < N := fun rc hrc => (hr rc hrc).1
    refine ⟨⟨⟨hsl, hc⟩, fun w hwm => ?_⟩, fun rc hrc => ?_⟩
    · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw w hwm
      have hw1 : w.1 < N := by
        have : w.1 ∈ wit.map Prod.fst := List.mem_map_of_mem hwm
        rw [← hc, List.mem_filter, List.mem_filter] at this
        exact hD _ this.1.1
      have hk : (reps.getD w.2.2 (0, 0)).1 < N := by
        rw [List.getD_eq_getElem _ _ h2]
        exact hrN _ (List.getElem_mem h2)
      refine ⟨⟨⟨h1, h2⟩, fun f hf => ?_⟩, ?_⟩
      · rw [hag _ h1 _ (hF f hf), hag _ (hF f hf) _ h1]
        exact h3 f hf
      · rw [hag _ h1 _ hw1, hag _ hk _ h1]
        exact h4
    · obtain ⟨h1, h2⟩ := hr rc hrc
      have e : D.filter (fun y => m1 y rc.1 == m1 rc.1 y) =
          D.filter (fun y => m2 y rc.1 == m2 rc.1 y) :=
        List.filter_congr fun y hy => by rw [hag _ (hD y hy) _ h1, hag _ h1 _ (hD y hy)]
      refine ⟨h1, ?_⟩
      rw [e]
      refine ih _ _ _ ?_ ?_ h2
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact h1
        · exact hF f hf
      · intro x hx
        exact hD x (List.mem_filter.1 hx).1

theorem mulIdx_zero (g gi : ℕ) (par cl : Array ℕ) (f k : ℕ) : mulIdx g gi par cl f 0 k = k := by
  cases f <;> simp [mulIdx]

theorem mulT_zero (W g N : ℕ) (PT CT : ℕ → ℕ) (k : ℕ) : mulT W g N PT CT 0 k = k := by
  cases N <;> rfl

theorem cen_of_cenR {W g N zi K L : ℕ} {PT CT : ℕ → ℕ} (hKL : N ≤ K * L)
    (hc : ∀ c < K, cenR W g N zi PT CT (c * L) L = true) :
    ∀ i < N, mulT W g N PT CT zi i = mulT W g N PT CT i zi := by
  intro i hi
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hKL
      omega
    · exact h
  have hcK : i / L < K := by
    rw [Nat.div_lt_iff_lt_mul hL]
    omega
  have hci := hc _ hcK
  rw [cenR] at hci
  have := allR_true hci (i % L) (Nat.mod_lt _ hL)
  rw [Nat.div_add_mod'] at this
  exact P.beq_iff.1 this

theorem cen_of_cayley {Γ : Type} [Group Γ] {N g gi : ℕ} {par cl : Array ℕ} {gens : List Γ}
    {ι : ℕ → Γ} (h : Cayley N g gi par cl gens ι) {zi : ℕ} (hzi : zi < N)
    (hgen : ∀ j < g, mulIdx g gi par cl N cl[j]! zi = mulIdx g gi par cl N zi cl[j]!) :
    ∀ i < N, mulIdx g gi par cl N zi i = mulIdx g gi par cl N i zi := by
  have hms : ∀ a k, a < N → k < N →
      mulIdx g gi par cl N a k < N ∧ ι (mulIdx g gi par cl N a k) = ι a * ι k :=
    fun a k ha hk => h.mulIdx_spec N a k ha.le ha hk
  have hgj : ∀ j < g, cl[j]! < N ∧ ι cl[j]! = gens.getD j 1 := by
    intro j hj
    have := h.step 0 h.pos j hj
    rw [Nat.zero_mul, Nat.zero_add, h.zero, mul_one] at this
    exact this
  have hcz : ∀ j < g, gens.getD j 1 * ι zi = ι zi * gens.getD j 1 := by
    intro j hj
    obtain ⟨hl, he⟩ := hgj j hj
    rw [← he, ← (hms _ _ hl hzi).2, ← (hms _ _ hzi hl).2, hgen j hj]
  have hci : ∀ i, i < N → ι i * ι zi = ι zi * ι i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [h.zero, one_mul, mul_one]
      · obtain ⟨hlt, j, hj, he⟩ := h.parent i hi hpos
        rw [he, mul_assoc, ih _ hlt (hlt.trans hi), ← mul_assoc, hcz j hj, mul_assoc]
  intro i hi
  apply h.inj _ (hms _ _ hzi hi).1 _ (hms _ _ hi hzi).1
  rw [(hms _ _ hzi hi).2, (hms _ _ hi hzi).2, hci i hi]

theorem nodeCheck_of_top {N : ℕ} {mul : ℕ → ℕ → ℕ} {nodes : Array (List ℕ × List ℕ)} {fuel j : ℕ}
    {F D : List ℕ} (h : nodeTop N mul nodes j F D = true)
    (hr : ∀ rc ∈ pairsOf (nodes.getD j ([], [])).1,
      nodeCheck N mul nodes fuel rc.2 (rc.1 :: F) (D.filter fun y => mul y rc.1 == mul rc.1 y) =
        true) :
    nodeCheck N mul nodes (fuel + 1) j F D = true := by
  simp only [nodeTop, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [nodeCheck, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true]
  exact Or.inr ⟨⟨⟨h1, h2⟩, h3⟩, fun rc hrc => ⟨h4 rc hrc, hr rc hrc⟩⟩

theorem treeRT_of_split {W g N zi K : ℕ} {PT CT : ℕ → ℕ} {nodes : Array (List ℕ × List ℕ)}
    {C : List ℕ} (hc : candOK W g N PT CT C = true) (ht : topR W g N zi PT CT nodes C K = true)
    (hch : ∀ k < K, childR W g N zi PT CT nodes C k = true) :
    treeRT W g N zi PT CT nodes = true := by
  have hC : candR W g N PT CT = C := (CFSG.KC.LQT.BW.Pf.eqLW_iff _ _).1 hc
  simp only [topR, andB_eq, Bool.and_eq_true] at ht
  obtain ⟨hzi, hzz, htop, hK⟩ := ht
  rw [treeRT, hC, andB_eq, andB_eq]
  simp only [Bool.and_eq_true]
  refine ⟨hzi, hzz, nodeCheck_of_top htop fun rc hrc => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hrc
  have hkK : k < K := by
    rw [← P.beq_iff.1 hK]
    exact hk
  have := hch k hkK
  simp only [childR, List.getD_eq_getElem _ _ hk] at this
  exact this

theorem cen_mulT {N g W zi : ℕ} {par cl : Array ℕ} {PT CT : ℕ → ℕ}
    (hfP : ∀ i < N, 0 < i → fieldT W PT i = par[i]!)
    (hfC : ∀ i < N, ∀ j < g, fieldT W CT (i * (g + g) + j) = cl[i * (g + g) + j]!)
    (hpar : ∀ i < N, 0 < i → par[i]! < i ∧ 0 < g)
    (hcl : ∀ i < N, ∀ j < g, cl[i * (g + g) + j]! < N) (hzi : zi < N)
    (hcen : ∀ i < N, mulIdx g g par cl N zi i = mulIdx g g par cl N i zi) :
    ∀ i < N, mulT W g N PT CT zi i = mulT W g N PT CT i zi := by
  have hm := mulG_spec' hfP hfC hpar hcl N
  have hmT : ∀ i < N, ∀ k < N, mulT W g N PT CT i k = mulIdx g g par cl N i k :=
    fun i hi k hk => (hm i k hi hk).1
  intro i hi
  rw [hmT _ hzi _ hi, hmT _ hi _ hzi]
  exact hcen i hi

theorem treeR_sound {N g W zi : ℕ} {par cl : Array ℕ} {PT CT : ℕ → ℕ}
    {nodes : Array (List ℕ × List ℕ)}
    (hfP : ∀ i < N, 0 < i → fieldT W PT i = par[i]!)
    (hfC : ∀ i < N, ∀ j < g, fieldT W CT (i * (g + g) + j) = cl[i * (g + g) + j]!)
    (hpar : ∀ i < N, 0 < i → par[i]! < i ∧ 0 < g)
    (hcl : ∀ i < N, ∀ j < g, cl[i * (g + g) + j]! < N)
    (hcen : ∀ i < N, mulT W g N PT CT zi i = mulT W g N PT CT i zi)
    (ht : treeRT W g N zi PT CT nodes = true) :
    treeCheck N g g par cl zi nodes = true := by
  rw [treeRT, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at ht
  obtain ⟨hzi, hzz, ht⟩ := ht
  have hzi' : zi < N := P.blt_iff.1 hzi
  have hN : 0 < N := by omega
  have hm := mulG_spec' hfP hfC hpar hcl N
  have hmT : ∀ i < N, ∀ k < N, mulT W g N PT CT i k = mulIdx g g par cl N i k :=
    fun i hi k hk => (hm i k hi hk).1
  have hcl1 : ∀ i < N, ∀ k < N, mulIdx g g par cl N i k < N := fun i hi k hk => (hm i k hi hk).2
  have hf : (List.range N).filter (fun x => mulIdx g g par cl N x x == 0) =
      candR W g N PT CT := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [candR, invsB, filterN_eq, List.range_succ_eq_map, List.filter_cons, List.filter_cons,
      mulIdx_zero]
    simp only [beq_self_eq_true, ite_true]
    have e0 : CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq 0 0)) (Nat.beq (mulT W g (N' + 1) PT CT 0 0) 0) = false := rfl
    rw [e0]
    simp only [Bool.false_eq_true, ite_false]
    congr 1
    apply List.filter_congr
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyN : y + 1 < N' + 1 := by
      have := List.mem_range.1 hy
      omega
    rw [andB_eq, notB_eq, hmT _ hyN _ hyN]
    have e1 : Nat.beq (y + 1) 0 = false := rfl
    rw [e1, Bool.not_false, Bool.true_and, nbeq_eq]
  unfold treeCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hzi', ?_⟩, fun i hi => ?_⟩, ?_⟩
  · rw [← hmT _ hzi' _ hzi']
    exact P.beq_iff.1 hzz
  · rw [← hmT _ hzi' _ hi, ← hmT _ hi _ hzi']
    exact hcen i hi
  · rw [nodeCheck_filter]
    refine nodeCheck_congr hN (fun a ha b hb => (hmT a ha b hb).symm) hcl1 nodes _ _ _ _ ?_ ?_ ?_
    · intro f hf'
      rw [List.mem_singleton.1 hf']
      exact hzi'
    · intro x hx
      exact List.mem_range.1 (List.mem_filter.1 hx).1
    · rw [hf]
      exact ht

end CFSG.KC.LQT.TR.Pf

end

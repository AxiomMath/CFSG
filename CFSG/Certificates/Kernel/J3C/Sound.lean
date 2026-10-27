module

public import Certificates.Data.Kernel.Spor.CentReg
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.PointChainCard
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.CentReg

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC

theorem foldr_cnt (f : Nat → Bool) :
    ∀ (l : List Nat) (s : Nat),
      List.foldr (fun i s => Nat.add s (Bool.rec (motive := fun _ => Nat) 0 1 (f i))) s l =
        s + (l.filter f).length
  | [], s => rfl
  | x :: l, s => by
    rw [List.foldr_cons, foldr_cnt f l s, List.filter_cons]
    cases f x
    · simp
    · simp only [ite_true, List.length_cons]
      change s + _ + 1 = s + (_ + 1)
      omega

theorem cntN_eq (n : Nat) (f : Nat → Bool) :
    cntN n f = ((Finset.range n).filter fun i => f i = true).card := by
  unfold cntN
  rw [Raw.Orb.foldN_eq]
  refine (foldr_cnt f (List.range n) 0).trans ?_
  rw [Nat.zero_add, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]
  congr 1

section Tree

variable {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}

theorem lab_eq (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {k : Nat} (hk : k < cnt)
    (h0 : 0 < k) : r32 LAB k = LV (r32 TI k) :=
  ((R.pt k hk).tree h0).2.2.1

theorem tw_pt (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x) :
    ∀ k < cnt, actN (tw σ PAR LAB k) root = r32 PTS k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [tw_eq]
    by_cases h0 : k = 0
    · subst h0
      rw [ite_eq_right (by omega), actN_one, R.hd.root]
    · obtain ⟨a1, a2, a3, a4, -⟩ := (R.pt k hk).tree (by omega)
      rw [ite_eq_left ⟨by omega, a1⟩, actN_mul, ih _ a1 (by omega), a3,
        hσ _ a2 _ (R.pt _ (by omega)).lt, a4]

theorem tw_mem (R : Rep n root cnt r L LV PTS POS PAR LAB TI) {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : ∀ t < r, σ (LV t) ∈ H) : ∀ k < cnt, tw σ PAR LAB k ∈ H := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [tw_eq]
    by_cases hc : 0 < k ∧ r32 PAR k < k
    · rw [ite_eq_left hc, lab_eq R hk hc.1]
      exact H.mul_mem (hH _ ((R.pt k hk).tree hc.1).2.1) (ih _ hc.2 (by omega))
    · rw [ite_eq_right hc]
      exact H.one_mem

theorem walkF_tw (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x) :
    ∀ f k, k < cnt → k ≤ f → ∀ q : List Nat, (∀ x ∈ q, x < n) →
      walkF L PAR LAB f k q = q.map (actN (tw σ PAR LAB k)) := by
  intro f
  induction f with
  | zero =>
    intro k _ hkf q _
    have : k = 0 := by omega
    subst this
    rw [tw_eq, ite_eq_right (by omega)]
    have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
    rw [this, List.map_id]
    rfl
  | succ f ih =>
    intro k hk hkf q hq
    rw [walkF_succ, tw_eq]
    by_cases hc : 0 < k ∧ r32 PAR k < k
    · rw [ite_eq_left hc, ite_eq_left hc, mapK_eq, ih _ (by omega) (by omega) q hq, List.map_map]
      apply List.map_congr_left
      intro x hx
      have ht := ((R.pt k hk).tree hc.1).2.1
      simp only [Function.comp_apply, actN_mul]
      rw [lab_eq R hk hc.1, hσ _ ht _ (actN_lt _ (hq x hx))]
    · rw [ite_eq_right hc, ite_eq_right hc]
      have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
      rw [this, List.map_id]

theorem walkK_tw (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x) {k : Nat} (hk : k < cnt)
    {q : List Nat} (hq : ∀ x ∈ q, x < n) : walkK L PAR LAB k q = q.map (actN (tw σ PAR LAB k)) :=
  walkF_tw R hσ k k hk (Nat.le_refl _) q hq

theorem walkInvF_tw (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσi : ∀ t < r, ∀ x < n, actN (σ (LV t))⁻¹ x = L (Nat.xor (LV t) 1) x) :
    ∀ f k, k < cnt → k ≤ f → ∀ q : List Nat, (∀ x ∈ q, x < n) →
      walkInvF L PAR LAB f k q = q.map (actN (tw σ PAR LAB k)⁻¹) := by
  intro f
  induction f with
  | zero =>
    intro k _ hkf q _
    have : k = 0 := by omega
    subst this
    rw [tw_eq, ite_eq_right (by omega), inv_one]
    have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
    rw [this, List.map_id]
    rfl
  | succ f ih =>
    intro k hk hkf q hq
    rw [walkInvF_succ, tw_eq]
    by_cases hc : 0 < k ∧ r32 PAR k < k
    · have ht := ((R.pt k hk).tree hc.1).2.1
      have hb : ∀ x ∈ q.map (L (Nat.xor (r32 LAB k) 1)), x < n := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        rw [lab_eq R hk hc.1, ← hσi _ ht _ (hq y hy)]
        exact actN_lt _ (hq y hy)
      rw [ite_eq_left hc, ite_eq_left hc, mapK_eq, ih _ (by omega) (by omega) _ hb, List.map_map]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, mul_inv_rev, actN_mul]
      rw [lab_eq R hk hc.1, hσi _ ht _ (hq x hx)]
    · rw [ite_eq_right hc, ite_eq_right hc, inv_one]
      have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
      rw [this, List.map_id]

theorem walkInvK_tw (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσi : ∀ t < r, ∀ x < n, actN (σ (LV t))⁻¹ x = L (Nat.xor (LV t) 1) x) {k : Nat}
    (hk : k < cnt) {q : List Nat} (hq : ∀ x ∈ q, x < n) :
    walkInvK L PAR LAB k q = q.map (actN (tw σ PAR LAB k)⁻¹) :=
  walkInvF_tw R hσi k k hk (Nat.le_refl _) q hq

theorem root_lt (R : Rep n root cnt r L LV PTS POS PAR LAB TI) : root < n := by
  rw [← R.hd.root]
  exact (R.pt 0 R.hd.cnt_pos).lt

@[expose] noncomputable def ptSet (n cnt : Nat) (PTS : Nat → Nat) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∃ k < cnt, r32 PTS k = x.val

theorem mem_ptSet {cnt : Nat} {x : Fin n} : x ∈ ptSet n cnt PTS ↔ ∃ k < cnt, r32 PTS k = x.val := by
  unfold ptSet
  simp

theorem card_ptSet (R : Rep n root cnt r L LV PTS POS PAR LAB TI) :
    (ptSet n cnt PTS).card = cnt := by
  refine (Finset.card_bij (t := Finset.range cnt) (fun x _ => r32 POS x.val) (fun x hx => ?_)
    (fun a ha b hb e => ?_) (fun k hk => ?_)).trans (Finset.card_range cnt)
  · obtain ⟨k, hk, e⟩ := mem_ptSet.1 hx
    rw [Finset.mem_range, ← e, (R.pt k hk).pos]
    exact hk
  · obtain ⟨k, hk, ea⟩ := mem_ptSet.1 ha
    obtain ⟨k', hk', eb⟩ := mem_ptSet.1 hb
    apply Fin.ext
    rw [← ea, ← eb, (R.pt k hk).pos, (R.pt k' hk').pos] at e
    rw [← ea, ← eb, e]
  · rw [Finset.mem_range] at hk
    refine ⟨⟨r32 PTS k, (R.pt k hk).lt⟩, mem_ptSet.2 ⟨k, hk, rfl⟩, ?_⟩
    exact (R.pt k hk).pos

theorem inv_maps {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)} (h : ∀ x ∈ S, g x ∈ S) :
    ∀ x ∈ S, g⁻¹ x ∈ S := by
  have hsub : S.image g ⊆ S := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact h x hx
  have heq : S.image g = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ g.injective])
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  simpa using hy

theorem tree_closed (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Subgroup.closure (Set.range fun t : Fin r => σ (LV t.val))) :
    ∀ x ∈ ptSet n cnt PTS, g x ∈ ptSet n cnt PTS := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, rfl⟩ := hg
    intro x hx
    obtain ⟨k, hk, e⟩ := mem_ptSet.1 hx
    obtain ⟨hq, hkq, -⟩ := (R.pt k hk).close t.val t.isLt
    refine mem_ptSet.2 ⟨_, hkq, ?_⟩
    rw [R.pts_pos hq hkq, ← actN_fin, hσ _ t.isLt _ x.isLt, e]
  | one => intro x hx; exact hx
  | mul g h _ _ ihg ihh => intro x hx; exact ihg _ (ihh x hx)
  | inv g _ ih => exact inv_maps ih

theorem root_mem (R : Rep n root cnt r L LV PTS POS PAR LAB TI) :
    (⟨root, root_lt R⟩ : Fin n) ∈ ptSet n cnt PTS :=
  mem_ptSet.2 ⟨0, R.hd.cnt_pos, R.hd.root⟩

end Tree

section Regular

variable {n : Nat}

open MulAction

theorem card_eq_orbit_mul (G : Subgroup (Equiv.Perm (Fin n))) (x : Fin n) :
    Nat.card G = Nat.card (stabilizer G x) * (orbit G x).ncard := by
  rw [← index_stabilizer, Subgroup.card_mul_index]

theorem mem_orbit_iff' {G : Subgroup (Equiv.Perm (Fin n))} {x y : Fin n} :
    y ∈ orbit G x ↔ ∃ g ∈ G, g x = y := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem orbit_ncard_pos (G : Subgroup (Equiv.Perm (Fin n))) (x : Fin n) :
    0 < (orbit G x).ncard :=
  (Set.ncard_pos (Set.toFinite _)).2 ⟨x, mem_orbit_self x⟩

theorem fix_of_card_stab {G : Subgroup (Equiv.Perm (Fin n))} {x : Fin n}
    (h : Nat.card (stabilizer G x) ≤ 1) : ∀ g ∈ G, g x = x → g = 1 := by
  intro g hg hx
  have hb := Subgroup.eq_bot_of_card_le _ h
  have hm : (⟨g, hg⟩ : G) ∈ stabilizer G x := by
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
    exact hx
  rw [hb, Subgroup.mem_bot] at hm
  exact congrArg Subtype.val hm

theorem free_of_card {G C : Subgroup (Equiv.Perm (Fin n))} (hGC : G ≤ C) (x : Fin n)
    (hc : Nat.card C ≤ (orbit G x).ncard) :
    G = C ∧ Nat.card G = (orbit G x).ncard ∧ ∀ g ∈ G, g x = x → g = 1 := by
  have h1 := card_eq_orbit_mul G x
  have h2 := Subgroup.card_le_of_le hGC
  have hpos := orbit_ncard_pos G x
  have hs : Nat.card (stabilizer G x) ≤ 1 := by
    by_contra h
    have : 2 * (orbit G x).ncard ≤ Nat.card (stabilizer G x) * (orbit G x).ncard :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hG : Nat.card G = (orbit G x).ncard := by
    have := Nat.card_pos (α := stabilizer G x)
    have e : Nat.card (stabilizer G x) = 1 := by omega
    rw [h1, e, Nat.one_mul]
  exact ⟨Subgroup.eq_of_le_of_card_ge hGC (by omega), hG, fix_of_card_stab hs⟩

theorem orbit_sub_of_closed {G : Subgroup (Equiv.Perm (Fin n))} {S : Finset (Fin n)}
    (hS : ∀ g ∈ G, ∀ y ∈ S, g y ∈ S) {x : Fin n} (hx : x ∈ S) :
    ∀ y ∈ orbit G x, y ∈ S := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orbit_iff'.1 hy
  exact hS g hg x hx

theorem orbit_eq_ptSet {cnt root r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}
    (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : ∀ t < r, σ (LV t) ∈ G)
    (hS : ∀ g ∈ G, ∀ y ∈ ptSet n cnt PTS, g y ∈ ptSet n cnt PTS) :
    orbit G (⟨root, root_lt R⟩ : Fin n) = (↑(ptSet n cnt PTS) : Set (Fin n)) := by
  ext y
  constructor
  · exact orbit_sub_of_closed hS (root_mem R) y
  · intro hy
    obtain ⟨k, hk, e⟩ := mem_ptSet.1 (Finset.mem_coe.1 hy)
    refine mem_orbit_iff'.2 ⟨_, tw_mem R hG k hk, Fin.ext ?_⟩
    rw [← actN_fin, tw_pt R hσ k hk, e]

theorem tree_free {cnt root r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}
    (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {G C : Subgroup (Equiv.Perm (Fin n))} (hG : ∀ t < r, σ (LV t) ∈ G) (hGC : G ≤ C)
    (hc : Nat.card C ≤ cnt) :
    G = C ∧ cnt ≤ Nat.card G ∧
      ∀ g ∈ G, g (⟨root, root_lt R⟩ : Fin n) = ⟨root, root_lt R⟩ → g = 1 := by
  have hsub : (↑(ptSet n cnt PTS) : Set (Fin n)) ⊆ orbit G (⟨root, root_lt R⟩ : Fin n) := by
    intro y hy
    obtain ⟨k, hk, e⟩ := mem_ptSet.1 (Finset.mem_coe.1 hy)
    refine mem_orbit_iff'.2 ⟨_, tw_mem R hG k hk, Fin.ext ?_⟩
    rw [← actN_fin, tw_pt R hσ k hk, e]
  have hle : cnt ≤ (orbit G (⟨root, root_lt R⟩ : Fin n)).ncard := by
    calc cnt = (ptSet n cnt PTS).card := (card_ptSet R).symm
      _ = (↑(ptSet n cnt PTS) : Set (Fin n)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub
  obtain ⟨e, hG', hfix⟩ := free_of_card hGC (⟨root, root_lt R⟩ : Fin n) (hc.trans hle)
  exact ⟨e, hG' ▸ hle, hfix⟩

theorem card_of_free {cnt root r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}
    (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : ∀ t < r, σ (LV t) ∈ G)
    (hS : ∀ g ∈ G, ∀ y ∈ ptSet n cnt PTS, g y ∈ ptSet n cnt PTS)
    (hfree : ∀ g ∈ G, g (⟨root, root_lt R⟩ : Fin n) = ⟨root, root_lt R⟩ → g = 1) :
    Nat.card G = cnt ∧ ∀ g ∈ G, ∃ k < cnt, r32 PTS k = (g (⟨root, root_lt R⟩ : Fin n) : Nat) ∧
      g = tw σ PAR LAB k := by
  have ho := orbit_eq_ptSet R hσ hG hS
  have hs : Nat.card (stabilizer G (⟨root, root_lt R⟩ : Fin n)) ≤ 1 := by
    refine Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => ?_⟩
    have ha := a.2
    have hb := b.2
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at ha hb
    have e1 := hfree _ a.1.2 ha
    have e2 := hfree _ b.1.2 hb
    exact Subtype.ext (Subtype.ext (e1.trans e2.symm))
  refine ⟨?_, fun g hg => ?_⟩
  · rw [card_eq_orbit_mul, ho, Set.ncard_coe_finset, card_ptSet R]
    have := Nat.card_pos (α := stabilizer G (⟨root, root_lt R⟩ : Fin n))
    have e : Nat.card (stabilizer G (⟨root, root_lt R⟩ : Fin n)) = 1 := by omega
    rw [e, Nat.one_mul]
  · have hm : g (⟨root, root_lt R⟩ : Fin n) ∈ ptSet n cnt PTS := hS g hg _ (root_mem R)
    obtain ⟨k, hk, e⟩ := mem_ptSet.1 hm
    refine ⟨k, hk, e, ?_⟩
    have ht := tw_mem R hG k hk
    have h1 := hfree _ (G.mul_mem (G.inv_mem ht) hg) (by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [← actN_fin (tw σ PAR LAB k), tw_pt R hσ k hk, e])
    rw [inv_mul_eq_one] at h1
    exact h1.symm

end Regular

section Chain

variable {n : Nat}

open MulAction CFSG.KS.PCC

theorem two_level {r0 r1 c0 c1 b0 b1 : Nat} {L0 L1 : Nat → Nat → Nat} {LV0 LV1 : Nat → Nat}
    {PTS0 POS0 PAR0 LAB0 TI0 PTS1 POS1 PAR1 LAB1 TI1 : Nat → Nat}
    {σ0 σ1 : Nat → Equiv.Perm (Fin n)}
    (R0 : Rep n b0 c0 r0 L0 LV0 PTS0 POS0 PAR0 LAB0 TI0)
    (R1 : Rep n b1 c1 r1 L1 LV1 PTS1 POS1 PAR1 LAB1 TI1)
    (hσ0 : ∀ t < r0, ∀ x < n, actN (σ0 (LV0 t)) x = L0 (LV0 t) x)
    (hσ1 : ∀ t < r1, ∀ x < n, actN (σ1 (LV1 t)) x = L1 (LV1 t) x)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG0 : ∀ t < r0, σ0 (LV0 t) ∈ G)
    (hG1 : ∀ t < r1, σ1 (LV1 t) ∈ G ∧
      σ1 (LV1 t) (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩)
    (hc : Nat.card G ≤ c0 * c1) :
    (∀ g ∈ G, ∃ k < c0, r32 PTS0 k = (g (⟨b0, root_lt R0⟩ : Fin n) : Nat)) ∧
      ∀ g ∈ G, g (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩ →
        ∃ j < c1, r32 PTS1 j = (g (⟨b1, root_lt R1⟩ : Fin n) : Nat) ∧ g = tw σ1 PAR1 LAB1 j := by
  classical
  set B : Nat → Fin n := fun i => if i = 0 then ⟨b0, root_lt R0⟩ else ⟨b1, root_lt R1⟩ with hB
  set D : Nat → Finset (Fin n) := fun i => if i = 0 then ptSet n c0 PTS0 else ptSet n c1 PTS1
    with hDd
  have hB0 : B 0 = ⟨b0, root_lt R0⟩ := rfl
  have hB1 : B 1 = ⟨b1, root_lt R1⟩ := rfl
  have hG1' : ∀ t < r1, σ1 (LV1 t) ∈ Gs G B 1 := fun t ht => by
    rw [mem_Gs]
    refine ⟨(hG1 t ht).1, fun k hk => ?_⟩
    have : k = 0 := by omega
    subst this
    exact (hG1 t ht).2
  have hD : ∀ l < 2, ∀ x ∈ D l, x ∈ orbit (Gs G B l) (B l) := by
    intro l hl x hx
    rw [mem_orbit_Gs]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · obtain ⟨k, hk, e⟩ := mem_ptSet.1 hx
      refine ⟨_, tw_mem R0 hG0 k hk, Fin.ext ?_⟩
      rw [hB0, ← actN_fin, tw_pt R0 hσ0 k hk, e]
    · obtain ⟨k, hk, e⟩ := mem_ptSet.1 hx
      refine ⟨_, tw_mem R1 hG1' k hk, Fin.ext ?_⟩
      rw [hB1, ← actN_fin, tw_pt R1 hσ1 k hk, e]
  have hprod : ∏ l ∈ Finset.range 2, (D l).card = c0 * c1 := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero, Nat.one_mul]
    change (ptSet n c0 PTS0).card * (ptSet n c1 PTS1).card = c0 * c1
    rw [card_ptSet R0, card_ptSet R1]
  have hsub := orbit_sub D (L := 2) hD (by rw [hprod]; exact hc)
  have htriv : ∀ g ∈ Gs G B 2, g = 1 := by
    have hchain := card_chain G B 2
    have hle : ∏ l ∈ Finset.range 2, (D l).card ≤
        ∏ l ∈ Finset.range 2, (orbit (Gs G B l) (B l)).ncard := by
      apply Finset.prod_le_prod
      intro l hl
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard (fun x hx => hD l (Finset.mem_range.1 hl) x hx)
    have hG : 0 < Nat.card G := Nat.card_pos
    have h1 : Nat.card (Gs G B 2) ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ Nat.card (Gs G B 2) := by omega
      have h3 := Nat.mul_le_mul_left (∏ l ∈ Finset.range 2,
        (orbit (Gs G B l) (B l)).ncard) h2
      rw [hprod] at hle
      omega
    intro g hg
    have := Subgroup.eq_bot_of_card_le _ h1
    rw [this] at hg
    exact (Subgroup.mem_bot).1 hg
  refine ⟨fun g hg => ?_, fun g hg hfix => ?_⟩
  · have hm := hsub 0 (by omega) (g (B 0)) (mem_orbit_Gs.2 ⟨g, hg, rfl⟩)
    obtain ⟨k, hk, e⟩ := mem_ptSet.1 hm
    exact ⟨k, hk, e⟩
  · have hg1 : g ∈ Gs G B 1 := by
      rw [mem_Gs]
      refine ⟨hg, fun k hk => ?_⟩
      have : k = 0 := by omega
      subst this
      exact hfix
    have hm := hsub 1 (by omega) (g (B 1)) (mem_orbit_Gs.2 ⟨g, hg1, rfl⟩)
    obtain ⟨j, hj, e⟩ := mem_ptSet.1 hm
    refine ⟨j, hj, e, ?_⟩
    have ht := (mem_Gs _ _).1 (tw_mem R1 hG1' j hj)
    have hm2 : (tw σ1 PAR1 LAB1 j)⁻¹ * g ∈ Gs G B 2 := by
      rw [mem_Gs]
      refine ⟨G.mul_mem (G.inv_mem ht.1) hg, fun k hk => ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [ht.2 0 (by omega)]
        exact hfix
      · apply Fin.ext
        rw [← e]
        exact (tw_pt R1 hσ1 j hj).symm.trans (actN_fin _ (B 1))
    have := htriv _ hm2
    rw [inv_mul_eq_one] at this
    exact this.symm

end Chain

section Cent

variable {n : Nat}

open MulAction

@[expose] def centIn (G : Subgroup (Equiv.Perm (Fin n))) (a : Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  G ⊓ Subgroup.centralizer {a}

theorem mem_centIn {G : Subgroup (Equiv.Perm (Fin n))} {a g : Equiv.Perm (Fin n)} :
    g ∈ centIn G a ↔ g ∈ G ∧ g * a = a * g := by
  unfold centIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem card_cent_le (G : Subgroup (Equiv.Perm (Fin n))) (a : Equiv.Perm (Fin n)) {x : Fin n}
    (hx : a x = x) :
    Nat.card (centIn G a) ≤ {y | a y = y}.ncard * Nat.card (stabilizer (centIn G a) x) := by
  rw [card_eq_orbit_mul, Nat.mul_comm]
  refine Nat.mul_le_mul_right _ (Set.ncard_le_ncard (fun y hy => ?_) (Set.toFinite _))
  obtain ⟨g, hg, rfl⟩ := mem_orbit_iff'.1 hy
  have e := (mem_centIn.1 hg).2
  change a (g x) = g x
  rw [← Equiv.Perm.mul_apply, ← e, Equiv.Perm.mul_apply, hx]

theorem card_stab_le {G : Subgroup (Equiv.Perm (Fin n))} {a t : Equiv.Perm (Fin n)}
    {x b0 b1 : Fin n} {c1 : Nat} {s : Nat → Equiv.Perm (Fin n)} (ht : t ∈ G) (htx : t b0 = x)
    (hrep : ∀ g ∈ G, g b0 = b0 → ∃ j < c1, (s j b1 : Nat) = g b1 ∧ g = s j) :
    Nat.card (stabilizer (centIn G a) x) ≤ ((Finset.range c1).filter fun j =>
      s j ((t⁻¹ * a * t) b1) = (t⁻¹ * a * t) (s j b1)).card := by
  classical
  have hmem : ∀ h : stabilizer (centIn G a) x, t⁻¹ * (h : Equiv.Perm (Fin n)) * t ∈ G ∧
      (t⁻¹ * (h : Equiv.Perm (Fin n)) * t) b0 = b0 := by
    intro h
    have hh := h.2
    rw [mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at hh
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem ht) (mem_centIn.1 h.1.2).1) ht, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htx, hh, Equiv.Perm.inv_eq_iff_eq, htx]
  let f : stabilizer (centIn G a) x → Nat := fun h => Classical.choose (hrep _ (hmem h).1 (hmem h).2)
  have hf : ∀ h, f h < c1 ∧ (s (f h) b1 : Nat) = (t⁻¹ * (h : Equiv.Perm (Fin n)) * t) b1 ∧
      t⁻¹ * (h : Equiv.Perm (Fin n)) * t = s (f h) := fun h =>
    Classical.choose_spec (hrep _ (hmem h).1 (hmem h).2)
  let F : stabilizer (centIn G a) x → {j // j ∈ (Finset.range c1).filter fun j =>
      s j ((t⁻¹ * a * t) b1) = (t⁻¹ * a * t) (s j b1)} := fun h => ⟨f h, by
    obtain ⟨h1, -, h3⟩ := hf h
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨h1, ?_⟩
    rw [← h3, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    refine congrArg (fun g : Equiv.Perm (Fin n) => g b1) ?_
    have e := (mem_centIn.1 h.1.2).2
    calc t⁻¹ * (h : Equiv.Perm (Fin n)) * t * (t⁻¹ * a * t)
        = t⁻¹ * ((h : Equiv.Perm (Fin n)) * a) * t := by
          simp only [mul_assoc, mul_inv_cancel_left]
      _ = t⁻¹ * (a * (h : Equiv.Perm (Fin n))) * t := by rw [e]
      _ = t⁻¹ * a * t * (t⁻¹ * (h : Equiv.Perm (Fin n)) * t) := by
          simp only [mul_assoc, mul_inv_cancel_left]⟩
  have hF : Function.Injective F := by
    intro h h' e
    have e' : f h = f h' := congrArg Subtype.val e
    have k1 := (hf h).2.2
    have k2 := (hf h').2.2
    rw [e'] at k1
    have : (h : Equiv.Perm (Fin n)) = h' := by
      have := k1.trans k2.symm
      simpa using this
    exact Subtype.ext (Subtype.ext this)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_eq_finsetCard] at this

theorem fixCnt_eq {A : Nat → Nat} {a : Equiv.Perm (Fin n)} (hA : ∀ x < n, A x = actN a x) :
    fixCnt n A = {y | a y = y}.ncard := by
  classical
  unfold fixCnt
  rw [cntN_eq, Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun y _ => y.val) (fun y hy => ?_) (fun y _ z _ e => Fin.ext e)
    (fun x hx => ?_)
  · simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [hA _ y.isLt, actN_fin, hy]
    exact ⟨y.isLt, Nat.beq_refl _⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    rw [← actN_fin]
    change actN a x = x
    rw [← hA x hx.1]
    exact Nat.eq_of_beq_eq_true hx.2

end Cent

section CentOK

variable {n : Nat}

theorem conjAt_eq {cnt root r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}
    (R : Rep n root cnt r L LV PTS POS PAR LAB TI)
    (hσ : ∀ t < r, ∀ x < n, actN (σ (LV t)) x = L (LV t) x)
    (hσi : ∀ t < r, ∀ x < n, actN (σ (LV t))⁻¹ x = L (Nat.xor (LV t) 1) x)
    {A : Nat → Nat} {a : Equiv.Perm (Fin n)} (hA : ∀ x < n, A x = actN a x) {k : Nat}
    (hk : k < cnt) (z : Fin n) :
    conjAt L PAR LAB A k z =
      ((tw σ PAR LAB k)⁻¹ * a * tw σ PAR LAB k) z := by
  unfold conjAt hd
  rw [walkK_tw R hσ hk (q := [z.val]) (by simp)]
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
  have hb : ∀ y ∈ [A (actN (tw σ PAR LAB k) z)], y < n := by
    intro y hy
    rw [List.mem_singleton] at hy
    rw [hy, hA _ (actN_lt _ z.isLt)]
    exact actN_lt _ (actN_lt _ z.isLt)
  rw [walkInvK_tw R hσi hk hb]
  simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
  rw [hA _ (actN_lt _ z.isLt), ← actN_mul, ← actN_mul, actN_fin]

theorem centOK_sound {r0 r1 c0 c1 b0 b1 m k : Nat} {L : Nat → Nat → Nat} {LV0 LV1 : Nat → Nat}
    {PTS0 POS0 PAR0 LAB0 TI0 PTS1 POS1 PAR1 LAB1 TI1 : Nat → Nat}
    {σ : Nat → Equiv.Perm (Fin n)}
    (R0 : Rep n b0 c0 r0 L LV0 PTS0 POS0 PAR0 LAB0 TI0)
    (R1 : Rep n b1 c1 r1 L LV1 PTS1 POS1 PAR1 LAB1 TI1)
    (hσ0 : ∀ t < r0, ∀ x < n, actN (σ (LV0 t)) x = L (LV0 t) x)
    (hσi0 : ∀ t < r0, ∀ x < n, actN (σ (LV0 t))⁻¹ x = L (Nat.xor (LV0 t) 1) x)
    (hσ1 : ∀ t < r1, ∀ x < n, actN (σ (LV1 t)) x = L (LV1 t) x)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG0 : ∀ t < r0, σ (LV0 t) ∈ G)
    (hG1 : ∀ t < r1, σ (LV1 t) ∈ G ∧
      σ (LV1 t) (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩)
    (hc : Nat.card G ≤ c0 * c1) {A : Nat → Nat} {a : Equiv.Perm (Fin n)}
    (hA : ∀ x < n, A x = actN a x)
    (h : centOK L PTS0 PAR0 LAB0 c0 PTS1 PAR1 LAB1 c1 A k b1 m = true) :
    Nat.card (centIn G a) ≤ fixCnt n A * m := by
  classical
  unfold centOK at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hk, hfix, hm⟩ := h
  set t := tw σ PAR0 LAB0 k with htdef
  have htpt := tw_pt R0 hσ0 k hk
  have hxlt : r32 PTS0 k < n := (R0.pt k hk).lt
  set x : Fin n := ⟨r32 PTS0 k, hxlt⟩ with hxdef
  have htx : t (⟨b0, root_lt R0⟩ : Fin n) = x := by
    apply Fin.ext
    rw [← actN_fin, htpt]
  have hax : a x = x := by
    apply Fin.ext
    rw [← actN_fin, ← hA _ hxlt]
    exact hfix
  obtain ⟨-, hrep⟩ := two_level R0 R1 hσ0 hσ1 hG0 hG1 hc
  have hrep' : ∀ g ∈ G, g (⟨b0, root_lt R0⟩ : Fin n) = ⟨b0, root_lt R0⟩ →
      ∃ j < c1, (tw σ PAR1 LAB1 j (⟨b1, root_lt R1⟩ : Fin n) : Nat) =
        g (⟨b1, root_lt R1⟩ : Fin n) ∧ g = tw σ PAR1 LAB1 j := by
    intro g hg hgf
    obtain ⟨j, hj, -, e⟩ := hrep g hg hgf
    exact ⟨j, hj, by rw [e], e⟩
  have hst := card_stab_le (a := a) (tw_mem R0 hG0 k hk) htx hrep'
  have hcent := card_cent_le G a hax
  have hcnt : centCnt L PAR0 LAB0 PTS1 PAR1 LAB1 c1 A k b1 =
      ((Finset.range c1).filter fun j => tw σ PAR1 LAB1 j ((t⁻¹ * a * t) ⟨b1, root_lt R1⟩) =
        (t⁻¹ * a * t) (tw σ PAR1 LAB1 j ⟨b1, root_lt R1⟩)).card := by
    unfold centCnt
    rw [Raw.Orb.strictN_eq, cntN_eq]
    congr 1
    apply Finset.filter_congr
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have e1 := conjAt_eq R0 hσ0 hσi0 hA hk (⟨b1, root_lt R1⟩ : Fin n)
    have e2 := conjAt_eq R0 hσ0 hσi0 hA hk (tw σ PAR1 LAB1 j ⟨b1, root_lt R1⟩)
    have hpt : r32 PTS1 j = (tw σ PAR1 LAB1 j ⟨b1, root_lt R1⟩ : Nat) := by
      rw [← actN_fin, tw_pt R1 hσ1 j hj']
    have e1' : conjAt L PAR0 LAB0 A k b1 = ((t⁻¹ * a * t) ⟨b1, root_lt R1⟩ : Nat) := e1
    beta_reduce
    rw [e1', hpt, e2]
    unfold hd
    rw [walkK_tw R1 hσ1 hj' (q := [((t⁻¹ * a * t) ⟨b1, root_lt R1⟩ : Nat)]) (by simp)]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, actN_fin, Nat.beq_eq,
      Fin.val_inj]
    exact Iff.rfl
  rw [fixCnt_eq hA, ← hm, hcnt]
  exact hcent.trans (Nat.mul_le_mul_left _ hst)

end CentOK

end CFSG.KS.CentReg

end

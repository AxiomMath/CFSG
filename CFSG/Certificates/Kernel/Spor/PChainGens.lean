module

public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.PC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] def trProds (n : Nat) (letters : Array Table) (CNT : Nat → Nat)
    (PAR LAB : Nat → Nat → Nat) : Nat → Nat → Set (Equiv.Perm (Fin n))
  | 0, _ => {1}
  | d + 1, i => {g | ∃ k < CNT i, ∃ u ∈ trProds n letters CNT PAR LAB d (i + 1),
      g = twL n letters PAR LAB i k * u}

noncomputable abbrev lvGrp (n NL : Nat) (letters : Array Table) (L : Nat → Nat → Nat)
    (B : Nat → Nat) (i : Nat) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {g | ∃ l ∈ lvK L B NL i, sig n letters l = g}

theorem closure_mul_stable {G : Type*} [Group G] [Finite G] {X U : Set G}
    (h : ∀ s ∈ X, ∀ u ∈ U, s * u ∈ U) : ∀ g ∈ Subgroup.closure X, ∀ u ∈ U, g * u ∈ U := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => intro u hu; rwa [one_mul]
  | mul x y _ _ hx hy => intro u hu; rw [mul_assoc]; exact hx _ (hy u hu)
  | inv x _ hx =>
    have hp : ∀ e : Nat, ∀ u ∈ U, x ^ e * u ∈ U := by
      intro e
      induction e with
      | zero => intro u hu; rwa [pow_zero, one_mul]
      | succ e ih => intro u hu; rw [pow_succ, mul_assoc]; exact ih _ (hx u hu)
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      apply inv_eq_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [e]
    exact hp _

section

variable {n NL m : Nat} {letters : Array Table} {base Q qb : Array Nat}
  {L : Nat → Nat → Nat} {B : Nat → Nat} {QL : List Nat} {QB CNT : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat → Nat}

theorem lvGrp_le_grp (i : Nat) : lvGrp n NL letters L B i ≤ grp n NL letters := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact sig_mem ⟨l, (mem_lvK.1 hl).1⟩

theorem lvGrp_anti {i j : Nat} (hij : i ≤ j) :
    lvGrp n NL letters L B j ≤ lvGrp n NL letters L B i := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨hl', hf⟩ := mem_lvK.1 hl
  exact Subgroup.subset_closure ⟨l, mem_lvK.2 ⟨hl', fun t ht => hf t (by omega)⟩, rfl⟩

theorem twL_mem (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ k < CNT i, twL n letters PAR LAB i k ∈ lvGrp n NL letters L B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · rw [ite_eq_left hc]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, lab_mem H hi hk hc.1, rfl⟩)
        (ih _ hc.2 (by omega))
    · rw [ite_eq_right hc]
      exact Subgroup.one_mem _

theorem trProds_sub (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ d i, i + d = m → ∀ u ∈ trProds n letters CNT PAR LAB d i, u ∈ lvGrp n NL letters L B i
  | 0, _, _, u, hu => by
    rw [trProds, Set.mem_singleton_iff] at hu
    rw [hu]
    exact Subgroup.one_mem _
  | d + 1, i, hid, u, hu => by
    obtain ⟨k, hk, v, hv, rfl⟩ := hu
    exact Subgroup.mul_mem _ (twL_mem H (by omega) k hk)
      (lvGrp_anti (Nat.le_succ i) (trProds_sub H d (i + 1) (by omega) v hv))

theorem one_mem_trProds (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ d i, i + d = m → (1 : Equiv.Perm (Fin n)) ∈ trProds n letters CNT PAR LAB d i
  | 0, _, _ => rfl
  | d + 1, i, hid => by
    refine ⟨0, ((rep_of H (by omega : i < m)).hd.cnt_pos), 1,
      one_mem_trProds H d (i + 1) (by omega), ?_⟩
    rw [twL, tw_eq, ite_eq_right (by omega), one_mul]

theorem ncard_trProds :
    ∀ d i, (trProds n letters CNT PAR LAB d i).ncard ≤
      ((List.range d).map fun l => CNT (i + l)).prod
  | 0, _ => by simp [trProds]
  | d + 1, i => by
    have hsub : trProds n letters CNT PAR LAB (d + 1) i ⊆
        (fun p : Nat × Equiv.Perm (Fin n) => twL n letters PAR LAB i p.1 * p.2) ''
          ((↑(Finset.range (CNT i)) : Set Nat) ×ˢ trProds n letters CNT PAR LAB d (i + 1)) := by
      rintro _ ⟨k, hk, u, hu, rfl⟩
      exact ⟨(k, u), ⟨by simpa using hk, hu⟩, rfl⟩
    have hfin : ((↑(Finset.range (CNT i)) : Set Nat) ×ˢ
        trProds n letters CNT PAR LAB d (i + 1)).Finite :=
      (Finset.finite_toSet _).prod (Set.toFinite _)
    calc (trProds n letters CNT PAR LAB (d + 1) i).ncard
        ≤ ((fun p : Nat × Equiv.Perm (Fin n) => twL n letters PAR LAB i p.1 * p.2) ''
          ((↑(Finset.range (CNT i)) : Set Nat) ×ˢ trProds n letters CNT PAR LAB d (i + 1))).ncard :=
          Set.ncard_le_ncard hsub (hfin.image _)
      _ ≤ ((↑(Finset.range (CNT i)) : Set Nat) ×ˢ trProds n letters CNT PAR LAB d (i + 1)).ncard :=
          Set.ncard_image_le hfin
      _ = CNT i * (trProds n letters CNT PAR LAB d (i + 1)).ncard := by
          rw [Set.ncard_prod, Set.ncard_coe_finset, Finset.card_range]
      _ ≤ CNT i * ((List.range d).map fun l => CNT (i + 1 + l)).prod :=
          Nat.mul_le_mul_left _ (ncard_trProds d (i + 1))
      _ = ((List.range (d + 1)).map fun l => CNT (i + l)).prod := by
          rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
          congr 2
          apply List.map_congr_left
          intro l _
          simp only [Function.comp_apply]
          congr 1
          omega

theorem sift_rep (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ d j, j + d = m → ∀ g : Equiv.Perm (Fin n),
      siftF L POS PAR LAB CNT QB QL d j (QL.map (actN g)) = true →
      ∃ u ∈ trProds n letters CNT PAR LAB d j, ∀ x ∈ QL, actN g x = actN u x
  | 0, j, _, g, h => by
    refine ⟨1, rfl, ?_⟩
    have h' : listEqK (QL.map (actN g)) QL = true := h
    rw [listEqK_iff] at h'
    intro x hx
    rw [map_self h' x hx, actN_one]
  | d + 1, j, hj, g, h => by
    have hjm : j < m := by omega
    rw [siftF_succ, Bool.and_eq_true, decide_eq_true_iff] at h
    obtain ⟨hk, h⟩ := h
    unfold walkInvK at h
    rw [walkInvF_eq H hjm _ _ hk (Nat.le_refl _) _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact actN_lt _ (QL_lt H y hy)), List.map_map] at h
    have e : actN (twL n letters PAR LAB j (r32 (POS j) ((QL.map (actN g)).getD (QB j) 0)))⁻¹ ∘
        actN g = actN ((twL n letters PAR LAB j
          (r32 (POS j) ((QL.map (actN g)).getD (QB j) 0)))⁻¹ * g) :=
      funext fun x => (actN_mul _ _ x).symm
    rw [e] at h
    obtain ⟨u, hu, hgu⟩ := sift_rep H d (j + 1) (by omega) _ h
    refine ⟨_, ⟨_, hk, u, hu, rfl⟩, fun x hx => ?_⟩
    rw [actN_mul, ← hgu x hx, ← actN_mul, mul_inv_cancel_left]

theorem mem_trProds_of_sift (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hsep : ∀ g ∈ grp n NL letters, (∀ x ∈ QL, actN g x = x) → g = 1)
    {d j : Nat} (hj : j + d = m) {g : Equiv.Perm (Fin n)} (hg : g ∈ grp n NL letters)
    (h : siftF L POS PAR LAB CNT QB QL d j (QL.map (actN g)) = true) :
    g ∈ trProds n letters CNT PAR LAB d j := by
  obtain ⟨u, hu, hgu⟩ := sift_rep H d j hj g h
  have hu' := lvGrp_le_grp j (trProds_sub H d j hj u hu)
  have e := hsep (u⁻¹ * g) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hg) fun x hx => by
    rw [actN_mul, hgu x hx, ← actN_mul, inv_mul_cancel, actN_one]
  rwa [← mul_inv_cancel_left u g, e, mul_one]

theorem sch_rep (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hsep : ∀ g ∈ grp n NL letters, (∀ x ∈ QL, actN g x = x) → g = 1)
    {i l k : Nat} (hi : i < m) (hl : l ∈ lvK L B NL i) (hk : k < CNT i)
    (h : schK L PTS POS PAR LAB CNT QB QL m i l k = true) :
    ∃ k' < CNT i, ∃ u ∈ trProds n letters CNT PAR LAB (m - (i + 1)) (i + 1),
      sig n letters l * twL n letters PAR LAB i k = twL n letters PAR LAB i k' * u := by
  have hl' := (mem_lvK.1 hl).1
  have hQL := QL_lt H
  unfold schK at h
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hky, h⟩ := h
  unfold siftK walkK walkInvK at h
  rw [walkF_eq H hi k k hk (Nat.le_refl _) QL hQL, mapK_eq, List.map_map,
    walkInvF_eq H hi _ _ hky (Nat.le_refl _) _ (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact lab_lt H hl' _ (actN_lt _ (hQL z hz))), List.map_map] at h
  have e : List.map (actN (twL n letters PAR LAB i (r32 (POS i) (L l (r32 (PTS i) k))))⁻¹ ∘
      L l ∘ actN (twL n letters PAR LAB i k)) QL =
      QL.map (actN ((twL n letters PAR LAB i (r32 (POS i) (L l (r32 (PTS i) k))))⁻¹ *
        sig n letters l * twL n letters PAR LAB i k)) := by
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply, actN_mul]
    rw [actN_sig H hl' (actN_lt _ (hQL x hx))]
  rw [e] at h
  have hG : ∀ k < CNT i, twL n letters PAR LAB i k ∈ grp n NL letters := fun k hk =>
    lvGrp_le_grp i (twL_mem H hi k hk)
  have hsl : sig n letters l ∈ grp n NL letters := sig_mem ⟨l, hl'⟩
  have hm := mem_trProds_of_sift H hsep (d := m - (i + 1)) (j := i + 1) (by omega)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hG _ hky)) hsl) (hG k hk)) h
  exact ⟨_, hky, _, hm, by simp only [mul_assoc, mul_inv_cancel_left]⟩

theorem lvStep_mul_mem (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hsep : ∀ g ∈ grp n NL letters, (∀ x ∈ QL, actN g x = x) → g = 1)
    {i d : Nat} (hid : i + d + 1 = m) {X : List Nat} (hX : ∀ l ∈ X, l ∈ lvK L B NL i)
    (hsch : ∀ l ∈ X, ∀ k < CNT i, schK L PTS POS PAR LAB CNT QB QL m i l k = true)
    (ih : ∀ g ∈ lvGrp n NL letters L B (i + 1), ∀ u ∈ trProds n letters CNT PAR LAB d (i + 1),
      g * u ∈ trProds n letters CNT PAR LAB d (i + 1)) :
    ∀ g ∈ Subgroup.closure {g | ∃ l ∈ X, sig n letters l = g},
      ∀ u ∈ trProds n letters CNT PAR LAB (d + 1) i, g * u ∈ trProds n letters CNT PAR LAB (d + 1) i := by
  refine closure_mul_stable ?_
  rintro _ ⟨l, hl, rfl⟩ _ ⟨k, hk, v, hv, rfl⟩
  have hd : m - (i + 1) = d := by omega
  obtain ⟨k', hk', u, hu, e⟩ := sch_rep H hsep (by omega) (hX l hl) hk (hsch l hl k hk)
  rw [hd] at hu
  refine ⟨k', hk', u * v, ih u (trProds_sub H d (i + 1) (by omega) u hu) v hv, ?_⟩
  rw [← mul_assoc, e, mul_assoc]

theorem lvGrp_mul_mem (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hsep : ∀ g ∈ grp n NL letters, (∀ x ∈ QL, actN g x = x) → g = 1)
    (hsch : ∀ i < m, 0 < i → ∀ k < CNT i, ∀ t < (lvK L B NL i).length,
      schK L PTS POS PAR LAB CNT QB QL m i (lvAt L B NL i t) k = true)
    (hterm : termK L B NL m QL = true) :
    ∀ d i, i + d = m → 0 < i → ∀ g ∈ lvGrp n NL letters L B i,
      ∀ u ∈ trProds n letters CNT PAR LAB d i, g * u ∈ trProds n letters CNT PAR LAB d i
  | 0, i, hid, _ => by
    refine closure_mul_stable ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    rw [trProds, Set.mem_singleton_iff] at hu ⊢
    rw [hu, mul_one]
    unfold termK at hterm
    rw [List.all_eq_true] at hterm
    have h := hterm l (by rw [← hid, Nat.add_zero]; exact hl)
    rw [listEqK_iff, mapK_eq] at h
    have hl' := (mem_lvK.1 hl).1
    exact hsep _ (sig_mem ⟨l, hl'⟩) fun x hx => by
      rw [actN_sig H hl' (QL_lt H x hx)]
      exact map_self h x hx
  | d + 1, i, hid, hi => by
    have e : lvGrp n NL letters L B i = Subgroup.closure {g | ∃ l ∈ lvK L B NL i, sig n letters l = g} :=
      rfl
    rw [e]
    refine lvStep_mul_mem H hsep (by omega) (fun l hl => hl) (fun l hl k hk => ?_)
      (lvGrp_mul_mem H hsep hsch hterm d (i + 1) (by omega) (by omega))
    obtain ⟨t, ht, rfl⟩ := exists_lvAt hl
    exact hsch i (by omega) hi k hk t ht

theorem pchainK_gens_sound (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hm : 0 < m) (S : List Nat) (hS : ∀ s ∈ S, s < NL)
    (hgen : grp n NL letters ≤ Subgroup.closure {g | ∃ s ∈ S, sig n letters s = g})
    (hsep : ∀ g ∈ grp n NL letters, (∀ x ∈ QL, actN g x = x) → g = 1)
    (hsch0 : ∀ s ∈ S, ∀ k < CNT 0, schK L PTS POS PAR LAB CNT QB QL m 0 s k = true)
    (hsch : ∀ i < m, 0 < i → ∀ k < CNT i, ∀ t < (lvK L B NL i).length,
      schK L PTS POS PAR LAB CNT QB QL m i (lvAt L B NL i t) k = true)
    (hterm : termK L B NL m QL = true) :
    chainTrees n letters base =
        Array.ofFn (n := m) (fun i => tbfsRec n (CNT i.val) (PTS i.val) (POS i.val) (PAR i.val)
          (LAB i.val)) ∧
      ∀ chunks, chainOK n letters base Q qb (chainTrees n letters base) chunks = true := by
  refine pchain_of_card H ?_
  have h0 := lvStep_mul_mem H hsep (i := 0) (d := m - 1) (by omega)
    (fun s hs => mem_lvK.2 ⟨hS s hs, fun t ht => absurd ht (Nat.not_lt_zero _)⟩) hsch0
    (lvGrp_mul_mem H hsep hsch hterm (m - 1) 1 (by omega) Nat.one_pos)
  have hsub : (grp n NL letters : Set (Equiv.Perm (Fin n))) ⊆
      trProds n letters CNT PAR LAB m 0 := by
    intro g hg
    have e : m - 1 + 1 = m := by omega
    have h1 := h0 g (hgen hg) 1 (by rw [e]; exact one_mem_trProds H m 0 (by omega))
    rwa [mul_one, e] at h1
  calc Nat.card (grp n NL letters)
      = (grp n NL letters : Set (Equiv.Perm (Fin n))).ncard := Nat.card_coe_set_eq _
    _ ≤ (trProds n letters CNT PAR LAB m 0).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((List.range m).map fun l => CNT (0 + l)).prod := ncard_trProds m 0
    _ = ((List.range m).map CNT).prod := by simp only [Nat.zero_add]

end

end CFSG.KS.PC

end

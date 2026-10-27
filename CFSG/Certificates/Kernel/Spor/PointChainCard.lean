module

public import CFSG.Certificates.Kernel.Spor.CbfsFacts
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.CFSGNative.ONSchreier.Vectors

public section

namespace CFSG.KS.PCC

open CFSG.ONSchreier.Native CFSG.ONSchreier

variable {n : Nat}

theorem pword_prefix {S T Si Ti : Array (Array Nat)} {j : Nat}
    (hS : ∀ h < j, S[h]! = T[h]!) (hSi : ∀ h < j, Si[h]! = Ti[h]!) :
    ∀ w : List Int, plettersOK j w = true → pword n S Si w = pword n T Ti w
  | [], _ => rfl
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have ih := pword_prefix hS hSi w (by simpa [plettersOK, List.all_eq_true] using hw)
    rw [pword, pword, ih]
    congr 1
    unfold pletter
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos, ite_eq_left hpos]
      exact hS _ (by omega)
    · rw [ite_eq_right hpos, ite_eq_right hpos]
      exact hSi _ (by omega)

private theorem forIn_inv {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_inv R E f hf k (a + 1) b' (by omega) hR

private theorem push_lt {α : Type} [Inhabited α] {a : Array α} {v : α} {k : Nat}
    (hk : k < a.size) : (a.push v)[k]! = a[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, getElem!_pos a k hk]

private theorem push_eq {α : Type} [Inhabited α] {a : Array α} {v : α} :
    (a.push v)[a.size]! = v := by
  rw [getElem!_pos _ a.size (by simp), Array.getElem_push_eq]

theorem extendStrong_eq (orig : Array (Array Nat)) (W : Array (List Int)) :
    extendStrong n orig W = (forIn (m := Id) (List.range' orig.size (W.size - orig.size))
      (orig, orig.map (pinvCand n)) fun j s =>
        pure (ForInStep.yield (s.1.push (pword n s.1 s.2 W[j]!),
          s.2.push (pinvCand n (pword n s.1 s.2 W[j]!))))).1 := by
  unfold extendStrong
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]
  rfl

private def ExtInv (n : Nat) (a0 a1 : Array Nat) (W : Array (List Int)) (j : Nat)
    (s : Array (Array Nat) × Array (Array Nat)) : Prop :=
  2 ≤ j ∧ s.1.size = j ∧ s.2.size = j ∧ (∀ i < j, s.2[i]! = pinvCand n s.1[i]!) ∧
    s.1[0]! = a0 ∧ s.1[1]! = a1 ∧ ∀ i, 2 ≤ i → i < j → s.1[i]! = pword n s.1 s.2 W[i]!

theorem strongArrs_facts {a0 a1 : Array Nat} {W : Array (List Int)} (h2 : 2 ≤ W.size)
    (hW : ∀ j < W.size, 2 ≤ j → plettersOK j W[j]! = true) :
    (strongArrs n a0 a1 W).size = W.size ∧ (strongArrs n a0 a1 W)[0]! = a0 ∧
      (strongArrs n a0 a1 W)[1]! = a1 ∧
      ∀ j < W.size, 2 ≤ j → (strongArrs n a0 a1 W)[j]! =
        pword n (strongArrs n a0 a1 W) (pinvs n (strongArrs n a0 a1 W)) W[j]! := by
  have hI := forIn_inv (ExtInv n a0 a1 W) W.size (fun j s =>
      pure (ForInStep.yield (s.1.push (pword n s.1 s.2 W[j]!),
        s.2.push (pinvCand n (pword n s.1 s.2 W[j]!)))))
    (fun j s hj ⟨hj2, h1, h2', hinv, h0, h1', hw⟩ => by
      refine ⟨_, rfl, by omega, by simp [h1], by simp [h2'], fun i hi => ?_, ?_, ?_,
        fun i hi2 hi => ?_⟩
      · by_cases hij : i < j
        · rw [push_lt (by omega), push_lt (by omega), hinv i hij]
        · have e : i = j := by omega
          subst e
          rw [← h2', push_eq, h2', ← h1, push_eq]
      · rw [push_lt (by omega), h0]
      · rw [push_lt (by omega), h1']
      · have hagS : ∀ h < i, s.1[h]! = (s.1.push (pword n s.1 s.2 W[j]!))[h]! :=
          fun h hh => (push_lt (by omega)).symm
        have hagSi : ∀ h < i, s.2[h]! = (s.2.push (pinvCand n (pword n s.1 s.2 W[j]!)))[h]! :=
          fun h hh => (push_lt (by omega)).symm
        by_cases hij : i < j
        · rw [push_lt (by omega), hw i hi2 hij]
          exact pword_prefix hagS hagSi _ (hW i (by omega) hi2)
        · have e : i = j := by omega
          subst e
          rw [← h1, push_eq, h1]
          exact pword_prefix hagS hagSi _ (hW i (by omega) hi2))
    (W.size - 2) 2 (#[a0, a1], #[a0, a1].map (pinvCand n)) (by omega)
    ⟨le_rfl, rfl, by simp, fun i hi => by
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> simp, rfl, rfl, fun i hi2 hi => by omega⟩
  obtain ⟨-, hs, -, hinv, h0, h1, hw⟩ := hI
  have e : 2 + (W.size - 2) = W.size := by omega
  rw [e] at hs hinv hw
  have hS : strongArrs n a0 a1 W = (forIn (m := Id) (List.range' 2 (W.size - 2))
      (#[a0, a1], #[a0, a1].map (pinvCand n)) fun j s =>
        pure (ForInStep.yield (s.1.push (pword n s.1 s.2 W[j]!),
          s.2.push (pinvCand n (pword n s.1 s.2 W[j]!))))).1 := extendStrong_eq #[a0, a1] W
  rw [hS]
  refine ⟨hs, h0, h1, fun j hj hj2 => ?_⟩
  rw [hw j hj2 hj]
  refine pword_prefix (fun h _ => rfl) (fun h hh => ?_) _ (hW j hj hj2)
  rw [hinv h (by omega), pinvs, getElem!_map' _ _ (by omega)]

theorem permOfArr_eq (t : Array Nat) :
    CFSG.Monster.B.Co2.permOfArr n t = CFSG.ONSchreier.permOfArr n t := by
  rw [CFSG.Monster.B.Co2.permOfArr, CFSG.ONSchreier.permOfArr]

theorem pword_mem {K : Subgroup (Equiv.Perm (Fin n))} {S Si : Array (Array Nat)} {j : Nat}
    (hS : ∀ h < j, ∃ g ∈ K, PRep n S[h]! g ∧ PRep n Si[h]! g⁻¹) :
    ∀ w : List Int, plettersOK j w = true → ∃ g ∈ K, PRep n (pword n S Si w) g
  | [], _ => ⟨1, K.one_mem, prep_pid⟩
  | l :: w, hw => by
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    obtain ⟨g, hg, hrep⟩ := pword_mem hS w (by simpa [plettersOK, List.all_eq_true] using hw)
    obtain ⟨σ, hσ, h1, h2⟩ := hS (l.natAbs - 1) (by omega)
    rw [pword]
    unfold pletter
    by_cases hpos : 0 < l
    · rw [ite_eq_left hpos]
      have e : l.toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact ⟨σ * g, K.mul_mem hσ hg, prep_pcomp h1 hrep⟩
    · rw [ite_eq_right hpos]
      have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact ⟨σ⁻¹ * g, K.mul_mem (K.inv_mem hσ) hg, prep_pcomp h2 hrep⟩

theorem strong_mem {K : Subgroup (Equiv.Perm (Fin n))} {S : Array (Array Nat)}
    {W : Array (List Int)}
    (hinv : ∀ j < S.size, pisInv n S[j]! (pinvCand n S[j]!) = true)
    (h01 : ∀ j < S.size, j < 2 → permOfArr n S[j]! ∈ K)
    (hw : ∀ j < S.size, 2 ≤ j →
      plettersOK j W[j]! = true ∧ S[j]! = pword n S (pinvs n S) W[j]!) :
    ∀ j < S.size, permOfArr n S[j]! ∈ K := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hj2 : j < 2
    · exact h01 j hj hj2
    · obtain ⟨hl, he⟩ := hw j hj (by omega)
      obtain ⟨g, hg, hrep⟩ := pword_mem (K := K) (S := S) (Si := pinvs n S) (j := j)
        (fun h hh => ⟨permOfArr n S[h]!, ih h hh (by omega),
          (prep_permOfArr (hinv h (by omega))).1, by
            rw [pinvs, getElem!_map' _ _ (by omega)]
            exact (prep_permOfArr (hinv h (by omega))).2⟩) _ hl
      rw [← he] at hrep
      rw [(prep_permOfArr (hinv j hj)).1.unique hrep]
      exact hg

@[expose] noncomputable def Gs (G : Subgroup (Equiv.Perm (Fin n))) (B : Nat → Fin n) :
    Nat → Subgroup (Equiv.Perm (Fin n))
  | 0 => G
  | l + 1 => (MulAction.stabilizer (Gs G B l) (B l)).map (Gs G B l).subtype

theorem mem_Gs {G : Subgroup (Equiv.Perm (Fin n))} {B : Nat → Fin n} :
    ∀ l g, g ∈ Gs G B l ↔ g ∈ G ∧ ∀ k < l, g (B k) = B k
  | 0, g => by simp [Gs]
  | l + 1, g => by
    have e : Gs G B (l + 1) = (MulAction.stabilizer (Gs G B l) (B l)).map (Gs G B l).subtype :=
      rfl
    rw [e, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := (mem_Gs l x.1).1 x.2
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def] at hx
      refine ⟨h1.1, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1.2 k hk
      · exact hx
    · rintro ⟨hG, hfix⟩
      refine ⟨⟨g, (mem_Gs l g).2 ⟨hG, fun k hk => hfix k (by omega)⟩⟩, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
      exact hfix l (by omega)

theorem mem_orbit_Gs {G : Subgroup (Equiv.Perm (Fin n))} {B : Nat → Fin n} {l : Nat}
    {x : Fin n} : x ∈ MulAction.orbit (Gs G B l) (B l) ↔ ∃ g ∈ Gs G B l, g (B l) = x := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem card_Gs_succ (G : Subgroup (Equiv.Perm (Fin n))) (B : Nat → Fin n) (l : Nat) :
    Nat.card (Gs G B (l + 1)) * (MulAction.orbit (Gs G B l) (B l)).ncard =
      Nat.card (Gs G B l) := by
  have e : Gs G B (l + 1) = (MulAction.stabilizer (Gs G B l) (B l)).map (Gs G B l).subtype :=
    rfl
  rw [e, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    ← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem card_chain (G : Subgroup (Equiv.Perm (Fin n))) (B : Nat → Fin n) :
    ∀ L, Nat.card G = (∏ l ∈ Finset.range L, (MulAction.orbit (Gs G B l) (B l)).ncard) *
      Nat.card (Gs G B L)
  | 0 => by simp [Gs]
  | L + 1 => by
    rw [card_chain G B L, Finset.prod_range_succ, ← card_Gs_succ G B L]
    ring

theorem eq_of_prod_le {f g : Nat → Nat} : ∀ L, (∀ l < L, 0 < f l ∧ f l ≤ g l) →
    (∏ l ∈ Finset.range L, g l) ≤ ∏ l ∈ Finset.range L, f l → ∀ l < L, f l = g l
  | 0, _, _ => fun l hl => absurd hl (Nat.not_lt_zero l)
  | L + 1, hfg, hle => by
    rw [Finset.prod_range_succ, Finset.prod_range_succ] at hle
    have hf : 0 < ∏ l ∈ Finset.range L, f l :=
      Finset.prod_pos fun l hl => (hfg l (by simp at hl; omega)).1
    have hFG : ∏ l ∈ Finset.range L, f l ≤ ∏ l ∈ Finset.range L, g l :=
      Finset.prod_le_prod fun l hl => (hfg l (by simp at hl; omega)).2
    obtain ⟨h1, h2⟩ := hfg L (by omega)
    have eL : f L = g L := by
      by_contra hne
      have hlt : f L < g L := lt_of_le_of_ne h2 hne
      have c1 : (∏ l ∈ Finset.range L, f l) * f L < (∏ l ∈ Finset.range L, f l) * g L :=
        mul_lt_mul_of_pos_left hlt hf
      have c2 : (∏ l ∈ Finset.range L, f l) * g L ≤ (∏ l ∈ Finset.range L, g l) * g L :=
        Nat.mul_le_mul_right _ hFG
      omega
    have hle' : ∏ l ∈ Finset.range L, g l ≤ ∏ l ∈ Finset.range L, f l := by
      rw [eL] at hle
      exact Nat.le_of_mul_le_mul_right hle (by omega)
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact eq_of_prod_le L (fun l hl => hfg l (by omega)) hle' l hl
    · exact eL

theorem orbit_sub {G : Subgroup (Equiv.Perm (Fin n))} {B : Nat → Fin n} {L : Nat}
    (D : Nat → Finset (Fin n)) (hD : ∀ l < L, ∀ x ∈ D l, x ∈ MulAction.orbit (Gs G B l) (B l))
    (hc : Nat.card G ≤ ∏ l ∈ Finset.range L, (D l).card) :
    ∀ l < L, ∀ x ∈ MulAction.orbit (Gs G B l) (B l), x ∈ D l := by
  have hsub : ∀ l < L, (↑(D l) : Set (Fin n)) ⊆ MulAction.orbit (Gs G B l) (B l) :=
    fun l hl x hx => hD l hl x hx
  have hle : ∀ l < L, (D l).card ≤ (MulAction.orbit (Gs G B l) (B l)).ncard := fun l hl => by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (hsub l hl)
  have hG : 0 < Nat.card G := Nat.card_pos
  have hpos : ∀ l < L, 0 < (D l).card := fun l hl => by
    by_contra h0
    have : ∏ l ∈ Finset.range L, (D l).card = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hl) (by omega)
    omega
  have hL : 0 < Nat.card (Gs G B L) := Nat.card_pos
  have hchain := card_chain G B L
  have hprod : (∏ l ∈ Finset.range L, (MulAction.orbit (Gs G B l) (B l)).ncard) ≤
      ∏ l ∈ Finset.range L, (D l).card := by
    have : (∏ l ∈ Finset.range L, (MulAction.orbit (Gs G B l) (B l)).ncard) ≤
        (∏ l ∈ Finset.range L, (MulAction.orbit (Gs G B l) (B l)).ncard) *
          Nat.card (Gs G B L) := Nat.le_mul_of_pos_right _ hL
    omega
  have heq := eq_of_prod_le L (fun l hl => ⟨hpos l hl, hle l hl⟩) hprod
  intro l hl x hx
  have e := Set.eq_of_subset_of_ncard_le (hsub l hl)
    (by rw [Set.ncard_coe_finset, heq l hl])
  rw [← e] at hx
  exact hx

structure Hyp (n : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (G : Subgroup (Equiv.Perm (Fin n))) (B : Nat → Fin n) : Prop where
  rep : ∀ j < S.size, PRep n S[j]! (permOfArr n S[j]!)
  repInv : ∀ j < S.size, PRep n (pinvs n S)[j]! (permOfArr n S[j]!)⁻¹
  mem : ∀ j < S.size, permOfArr n S[j]! ∈ G
  base_lt : ∀ k < base.size, base[k]! < n
  base_val : ∀ k < base.size, ((B k : Fin n) : Nat) = base[k]!

@[expose] noncomputable def levPerms (n : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (i : Nat) : List (Equiv.Perm (Fin n)) :=
  (levIdx S base i).map (fun j => permOfArr n S[j]!) ++
    (levIdx S base i).map (fun j => (permOfArr n S[j]!)⁻¹)

@[expose] def lv (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i : Nat) : CLevel :=
  cbfs n base[i]! (levSteps S (pinvs n S) base i)

@[expose] noncomputable def tv (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i k : Nat) :
    Equiv.Perm (Fin n) :=
  pathT (levPerms n S base i) (fun k => (lv n S base i).par[k]!)
    (fun k => (lv n S base i).lab[k]!) k

@[expose] noncomputable def Dset (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Finset (Fin n) :=
  Finset.univ.filter fun x => (lv n S base i).pos[(x : Nat)]! < (lv n S base i).pts.size

theorem arr_append_get {α : Type} [Inhabited α] (idx : List Nat) (f g : Nat → α) {j : Nat}
    (hj : j < 2 * idx.length) :
    ((idx.map f).toArray ++ (idx.map g).toArray)[j]! =
      if j < idx.length then f idx[j]! else g idx[j - idx.length]! := by
  rw [getElem!_pos _ j (by simp; omega)]
  by_cases h : j < idx.length
  · rw [Array.getElem_append_left (by simpa using h), getElem!_pos idx j h]
    simp [h]
  · rw [Array.getElem_append_right (by simp; omega), getElem!_pos idx (j - idx.length) (by omega)]
    simp [h]

theorem getD_lt {α : Type} {l : List α} {j : Nat} {d : α} (h : j < l.length) :
    l.getD j d = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_ge {α : Type} {l : List α} {j : Nat} {d : α} (h : l.length ≤ j) :
    l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem list_append_getD (idx : List Nat) (f g : Nat → Equiv.Perm (Fin n)) {j : Nat}
    (hj : j < 2 * idx.length) :
    (idx.map f ++ idx.map g).getD j 1 =
      if j < idx.length then f idx[j]! else g idx[j - idx.length]! := by
  rw [getD_lt (by simp; omega)]
  by_cases h : j < idx.length
  · rw [List.getElem_append_left (by simpa using h), getElem!_pos idx j h]
    simp [h]
  · rw [List.getElem_append_right (by simp; omega), getElem!_pos idx (j - idx.length) (by omega)]
    simp [h]

theorem getD_mem {K : Subgroup (Equiv.Perm (Fin n))} {l : List (Equiv.Perm (Fin n))}
    (h : ∀ σ ∈ l, σ ∈ K) (j : Nat) : l.getD j 1 ∈ K := by
  by_cases hj : j < l.length
  · rw [getD_lt hj]
    exact h _ (List.getElem_mem hj)
  · rw [getD_ge (by omega)]
    exact K.one_mem

theorem parBelow_of {m chunks : Nat} {p : Nat → Bool} (h : ∀ i < m, p i = true) :
    parBelow m chunks p = true := by
  unfold parBelow
  rw [List.all_eq_true]
  intro t ht
  simp only [List.mem_map, List.mem_range] at ht
  obtain ⟨c, -, rfl⟩ := ht
  change allBelowN (m / chunks + 1)
    (fun k => !(decide (c * (m / chunks + 1) + k < m)) || p (c * (m / chunks + 1) + k)) = true
  rw [allBelowN_iff]
  intro k _
  by_cases hk : c * (m / chunks + 1) + k < m
  · simp [hk, h _ hk]
  · simp [hk]

section Levels

variable {S : Array (Array Nat)} {base : Array Nat} {G : Subgroup (Equiv.Perm (Fin n))}
  {B : Nat → Fin n}

theorem steps_get {i : Nat} (hi : i < base.size) :
    (allSteps S (pinvs n S) base)[i]! = levSteps S (pinvs n S) base i := by
  rw [allSteps, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem invs_get {i : Nat} (hi : i < base.size) :
    (allInvSteps S (pinvs n S) base)[i]! = levInvSteps S (pinvs n S) base i := by
  rw [allInvSteps, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem lev_get {i : Nat} (hi : i < base.size) :
    (cLevels n base (allSteps S (pinvs n S) base))[i]! = lv n S base i := by
  rw [cLevels, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  change cbfs n base[i]! (allSteps S (pinvs n S) base)[i]! = _
  rw [steps_get hi]
  rfl

theorem idx_get_lt {i j : Nat} (hj : j < (levIdx S base i).length) :
    (levIdx S base i)[j]! < S.size := by
  rw [getElem!_pos _ j hj]
  exact CArrays.levIdx_lt (List.getElem_mem hj)

theorem levSteps_size (i : Nat) :
    (levSteps S (pinvs n S) base i).size = 2 * (levIdx S base i).length := by
  simp [levSteps]
  omega

theorem steps_rep (H : Hyp n S base G B) {i j : Nat}
    (hj : j < (levSteps S (pinvs n S) base i).size) :
    PRep n (levSteps S (pinvs n S) base i)[j]! ((levPerms n S base i).getD j 1) ∧
      PRep n (levInvSteps S (pinvs n S) base i)[j]! ((levPerms n S base i).getD j 1)⁻¹ := by
  rw [levSteps_size] at hj
  rw [levPerms, list_append_getD _ _ _ hj, levSteps, levInvSteps, arr_append_get _ _ _ hj,
    arr_append_get _ _ _ hj]
  by_cases h : j < (levIdx S base i).length
  · simp only [h, ↓reduceIte]
    exact ⟨H.rep _ (idx_get_lt h), H.repInv _ (idx_get_lt h)⟩
  · simp only [h, ↓reduceIte, inv_inv]
    have h' : j - (levIdx S base i).length < (levIdx S base i).length := by omega
    exact ⟨H.repInv _ (idx_get_lt h'), H.rep _ (idx_get_lt h')⟩

theorem levPerms_mem (H : Hyp n S base G B) {i : Nat} (hi : i ≤ base.size) :
    ∀ σ ∈ levPerms n S base i, σ ∈ Gs G B i := by
  have key : ∀ j ∈ levIdx S base i, permOfArr n S[j]! ∈ Gs G B i := fun j hj => by
    have hjS := CArrays.levIdx_lt hj
    have hj' := hj
    unfold levIdx at hj'
    have hfix : pfixes base S[j]! i = true := (List.mem_filter.1 hj').2
    rw [mem_Gs]
    refine ⟨H.mem j hjS, fun k hk => ?_⟩
    have h1 := allBelowN_spec hfix hk
    rw [beq_iff_eq] at h1
    apply Fin.ext
    rw [← H.rep j hjS (B k), H.base_val k (by omega)]
    exact h1
  intro σ hσ
  rw [levPerms, List.mem_append, List.mem_map, List.mem_map] at hσ
  rcases hσ with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact key j hj
  · exact (Gs G B i).inv_mem (key j hj)

theorem lv_facts (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) :
    CLevelFacts n base[i]! (levSteps S (pinvs n S) base i) (lv n S base i) :=
  CBF.cbfs_facts (H.base_lt i hi) fun _ hj _ hx => (steps_rep H hj).1.lt hx

theorem tv_zero (i : Nat) : tv n S base i 0 = 1 := pathT_zero _ _ _

theorem tv_step (H : Hyp n S base G B) {i k : Nat} (hi : i < base.size)
    (hk : k < (lv n S base i).pts.size) (hk0 : 0 < k) :
    tv n S base i k = (levPerms n S base i).getD ((lv n S base i).lab[k]!) 1 *
      tv n S base i ((lv n S base i).par[k]!) := by
  rw [tv, pathT_step _ _ _ hk0 ((lv_facts H hi).par_lt k hk hk0)]
  rfl

theorem tv_mem (H : Hyp n S base G B) {i : Nat} (hi : i ≤ base.size) :
    ∀ k, tv n S base i k ∈ Gs G B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [tv, pathT]
    split
    · rename_i h
      exact (Gs G B i).mul_mem (getD_mem (levPerms_mem H hi) _) (ih _ h.2)
    · exact (Gs G B i).one_mem

theorem tv_pt (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) :
    ∀ k < (lv n S base i).pts.size, ((tv n S base i k (B i) : Fin n) : Nat) =
      (lv n S base i).pts[k]! := by
  have F := lv_facts H hi
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [tv_zero, F.root, Equiv.Perm.one_apply, H.base_val i hi]
    · have hpos := Nat.pos_of_ne_zero hk0
      have hpar := F.par_lt k hk hpos
      have hlab := F.lab_lt k hk hpos
      rw [tv_step H hi hk hpos, Equiv.Perm.mul_apply]
      have e : tv n S base i ((lv n S base i).par[k]!) (B i) =
          ⟨(lv n S base i).pts[(lv n S base i).par[k]!]!, F.pts_lt _ (by omega)⟩ :=
        Fin.ext (ih _ hpar (by omega))
      rw [e, ← (steps_rep H hlab).1 ⟨_, F.pts_lt _ (by omega)⟩]
      exact F.edge k hk hpos

theorem trApp_eq' (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) : ∀ fuel k, k < fuel →
    k < (lv n S base i).pts.size → ∀ p (hp : p < n),
      trApp (levSteps S (pinvs n S) base i) (lv n S base i) fuel k p =
        (tv n S base i k ⟨p, hp⟩ : Nat) := by
  have F := lv_facts H hi
  intro fuel
  induction fuel with
  | zero => intro k hk; omega
  | succ fuel ih =>
    intro k hk hkm p hp
    rw [trApp]
    by_cases hk0 : k = 0
    · subst hk0
      simp [tv_zero]
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hpar := F.par_lt k hkm hpos
      have hlab := F.lab_lt k hkm hpos
      simp only [beq_iff_eq, hk0, ↓reduceIte]
      rw [ih _ (by omega) (by omega) p hp, (steps_rep H hlab).1.apply (Fin.isLt _),
        tv_step H hi hkm hpos, Equiv.Perm.mul_apply]

theorem trInvApp_eq' (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) : ∀ fuel k, k < fuel →
    k < (lv n S base i).pts.size → ∀ p (hp : p < n),
      trInvApp (levInvSteps S (pinvs n S) base i) (lv n S base i) fuel k p =
        ((tv n S base i k)⁻¹ ⟨p, hp⟩ : Nat) := by
  have F := lv_facts H hi
  intro fuel
  induction fuel with
  | zero => intro k hk; omega
  | succ fuel ih =>
    intro k hk hkm p hp
    rw [trInvApp]
    by_cases hk0 : k = 0
    · subst hk0
      simp [tv_zero]
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hpar := F.par_lt k hkm hpos
      have hlab := F.lab_lt k hkm hpos
      simp only [beq_iff_eq, hk0, ↓reduceIte]
      rw [(steps_rep H hlab).2.apply hp, ih _ (by omega) (by omega) _ (Fin.isLt _),
        tv_step H hi hkm hpos, _root_.mul_inv_rev, Equiv.Perm.mul_apply]

theorem Dset_card (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) :
    (Dset n S base i).card = (lv n S base i).pts.size := by
  have F := lv_facts H hi
  rw [← Finset.card_range (lv n S base i).pts.size]
  refine Finset.card_bij (fun x _ => (lv n S base i).pos[(x : Nat)]!) (fun x hx => ?_)
    (fun a ha b hb e => ?_) (fun k hk => ?_)
  · simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_range.2 hx
  · simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    apply Fin.ext
    calc (a : Nat) = (lv n S base i).pts[(lv n S base i).pos[(a : Nat)]!]! :=
          (F.pts_pos _ a.2 ha).symm
      _ = (lv n S base i).pts[(lv n S base i).pos[(b : Nat)]!]! := by rw [e]
      _ = b := F.pts_pos _ b.2 hb
  · have hk' := Finset.mem_range.1 hk
    refine ⟨⟨(lv n S base i).pts[k]!, F.pts_lt k hk'⟩, ?_, F.pos_pts k hk'⟩
    simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [F.pos_pts k hk']
    exact hk'

theorem Dset_sub (H : Hyp n S base G B) {i : Nat} (hi : i < base.size) :
    ∀ x ∈ Dset n S base i, x ∈ MulAction.orbit (Gs G B i) (B i) := by
  intro x hx
  simp only [Dset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have F := lv_facts H hi
  rw [mem_orbit_Gs]
  refine ⟨tv n S base i ((lv n S base i).pos[(x : Nat)]!), tv_mem H hi.le _, Fin.ext ?_⟩
  rw [tv_pt H hi _ hx, F.pts_pos _ x.2 hx]

theorem cOrbitSizes_prod :
    (cOrbitSizes n S base).prod = ∏ i ∈ Finset.range base.size, (lv n S base i).pts.size := by
  rw [cOrbitSizes, cLevels, Array.toList_ofFn, List.map_ofFn, List.prod_ofFn,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  rw [steps_get i.isLt]
  rfl

theorem complete (H : Hyp n S base G B) (hc : Nat.card G ≤ (cOrbitSizes n S base).prod)
    {i : Nat} (hi : i < base.size) {g : Equiv.Perm (Fin n)} (hg : g ∈ Gs G B i) :
    (lv n S base i).pos[(g (B i) : Nat)]! < (lv n S base i).pts.size := by
  have hc' : Nat.card G ≤ ∏ l ∈ Finset.range base.size, (Dset n S base l).card := by
    refine hc.trans (le_of_eq ?_)
    rw [cOrbitSizes_prod]
    exact Finset.prod_congr rfl fun l hl => (Dset_card H (Finset.mem_range.1 hl)).symm
  have h := orbit_sub (Dset n S base) (L := base.size) (fun l hl => Dset_sub H hl) hc' i hi
    (g (B i)) (mem_orbit_Gs.2 ⟨g, hg, rfl⟩)
  simpa [Dset] using h

theorem psift_ok (H : Hyp n S base G B) (hc : Nat.card G ≤ (cOrbitSizes n S base).prod) :
    ∀ d l, l + d = base.size → ∀ (img : Array Nat) (g : Equiv.Perm (Fin n)), g ∈ Gs G B l →
      img.size = base.size → (∀ t < base.size, img[t]! = (g (B t) : Nat)) →
      psift (cLevels n base (allSteps S (pinvs n S) base)) (allInvSteps S (pinvs n S) base) base
        (Array.ofFn (n := base.size) fun i => i.val) false l img = true := by
  intro d
  induction d with
  | zero =>
    intro l hl img g _ _ _
    rw [psift, dite_eq_right_of_eq_false (eq_false (by simp [cLevels]; omega))]
    rfl
  | succ d ih =>
    intro l hl img g hg hsz himg
    have hlb : l < base.size := by omega
    have hls : l < (cLevels n base (allSteps S (pinvs n S) base)).size := by
      simp [cLevels]
      exact hlb
    have F := lv_facts H hlb
    rw [psift, dite_eq_left_of_eq_true (eq_true hls)]
    have hlev : (cLevels n base (allSteps S (pinvs n S) base))[l] = lv n S base l := by
      rw [← getElem!_pos _ l hls, lev_get hlb]
    have hb : (Array.ofFn (n := base.size) fun i => i.val)[l]! = l := getElem!_ofFn_nat _ hlb
    simp only [hlev, hb, himg l hlb, Bool.and_eq_true, decide_eq_true_eq]
    have hk := complete H hc hlb hg
    refine ⟨hk, ?_⟩
    have hT := (mem_Gs _ _).1 (tv_mem H hlb.le ((lv n S base l).pos[(g (B l) : Nat)]!))
    refine ih (l + 1) (by omega) _ ((tv n S base l ((lv n S base l).pos[(g (B l) : Nat)]!))⁻¹ * g)
      ?_ (by rw [Array.size_map, hsz]) (fun t ht => ?_)
    · rw [mem_Gs] at hg ⊢
      refine ⟨G.mul_mem (G.inv_mem hT.1) hg.1, fun k' hk' => ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
      · rw [hg.2 k' hk', hT.2 k' hk']
      · apply Fin.ext
        rw [tv_pt H hlb _ hk, F.pts_pos _ (g (B _)).2 hk]
    · rw [getElem!_map' _ _ (by rw [hsz]; exact ht), himg t ht, invs_get hlb,
        trInvApp_eq' H hlb _ _ hk hk _ (Fin.isLt _), Equiv.Perm.mul_apply]

theorem schreier_ok (H : Hyp n S base G B) (hc : Nat.card G ≤ (cOrbitSizes n S base).prod)
    {i : Nat} (hi : i < base.size) (chunks : Nat) :
    cschreierOK (cLevels n base (allSteps S (pinvs n S) base)) (allSteps S (pinvs n S) base)
      (allInvSteps S (pinvs n S) base) base (Array.ofFn (n := base.size) fun i => i.val) false i
      chunks = true := by
  unfold cschreierOK
  rw [lev_get hi, steps_get hi, invs_get hi]
  have F := lv_facts H hi
  refine parBelow_of fun h hh => allBelowN_iff.2 fun j hj => ?_
  obtain ⟨hk, -⟩ := F.closed h hh j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hk, ?_⟩
  have hσ := steps_rep H hj
  have hσG := getD_mem (levPerms_mem H hi.le) j
  set σ := (levPerms n S base i).getD j 1 with hσdef
  set k := (lv n S base i).pos[((levSteps S (pinvs n S) base i)[j]!)[(lv n S base i).pts[h]!]!]!
    with hkdef
  have hTh := (mem_Gs _ _).1 (tv_mem H hi.le h)
  have hTk := (mem_Gs _ _).1 (tv_mem H hi.le k)
  have hσ' := (mem_Gs _ _).1 hσG
  have hxh : tv n S base i h (B i) = ⟨(lv n S base i).pts[h]!, F.pts_lt h hh⟩ :=
    Fin.ext (tv_pt H hi h hh)
  have hy : ((levSteps S (pinvs n S) base i)[j]!)[(lv n S base i).pts[h]!]! < n :=
    hσ.1.lt (F.pts_lt h hh)
  have hkey : tv n S base i k (B i) = σ (tv n S base i h (B i)) := by
    apply Fin.ext
    rw [tv_pt H hi k hk, hxh, ← hσ.1 ⟨_, F.pts_lt h hh⟩, F.pts_pos _ hy hk]
  refine psift_ok H hc (base.size - (i + 1)) (i + 1) (by omega) _
    ((tv n S base i k)⁻¹ * σ * tv n S base i h) ?_
    (by simp [schreierImgs]) (fun t ht => ?_)
  · rw [mem_Gs]
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hTk.1) hσ'.1) hTh.1, fun k' hk' => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · rw [hTh.2 k' hk', hσ'.2 k' hk', hTk.2 k' hk']
    · exact hkey.symm
  · rw [schreierImgs, getElem!_map' _ _ ht, ← H.base_val t ht,
      trApp_eq' H hi _ _ hh hh _ (Fin.isLt _), hσ.1.apply (Fin.isLt _),
      trInvApp_eq' H hi _ _ hk hk _ (Fin.isLt _), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

end Levels

theorem peq_self (t : Array Nat) : peq n t t = true :=
  allBelowN_iff.2 fun _ _ => beq_self_eq_true _

theorem pointChainOK_of_card' {a0 a1 : Array Nat} {W : Array (List Int)}
    {base : Array Nat} {chunks : Nat}
    (hW : 2 ≤ W.size ∧ W[0]! = [] ∧ W[1]! = [] ∧ ∀ j < W.size, 2 ≤ j → plettersOK j W[j]! = true)
    (hperm : ∀ j < (strongArrs n a0 a1 W).size,
      pisInv n (strongArrs n a0 a1 W)[j]! (pinvCand n (strongArrs n a0 a1 W)[j]!) = true)
    (hb : ∀ i < base.size, base[i]! < n)
    (hcard : Nat.card (Subgroup.closure ({CFSG.Monster.B.Co2.permOfArr n a0,
      CFSG.Monster.B.Co2.permOfArr n a1} : Set (Equiv.Perm (Fin n)))) ≤
      (cOrbitSizes n (strongArrs n a0 a1 W) base).prod) :
    pointChainOK n 2 (strongArrs n a0 a1 W) base W chunks = true := by
  obtain ⟨h2, -, -, hWl⟩ := hW
  obtain ⟨hsz, hS0, hS1, hSw⟩ := strongArrs_facts (n := n) (a0 := a0) (a1 := a1) h2 hWl
  generalize strongArrs n a0 a1 W = S at hsz hS0 hS1 hSw hperm hcard ⊢
  have hcard' : Nat.card (Subgroup.closure ({permOfArr n S[0]!, permOfArr n S[1]!} :
      Set (Equiv.Perm (Fin n)))) ≤ (cOrbitSizes n S base).prod := by
    rw [hS0, hS1, ← permOfArr_eq, ← permOfArr_eq]
    exact hcard
  have hinvS : ∀ j < S.size, (pinvs n S)[j]! = pinvCand n S[j]! := fun j hj =>
    getElem!_map' _ _ hj
  have hmem := strong_mem (K := Subgroup.closure ({permOfArr n S[0]!, permOfArr n S[1]!} :
      Set (Equiv.Perm (Fin n)))) (W := W) hperm
    (fun j _ hj2 => by
      apply Subgroup.subset_closure
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp)
    (fun j hj hj2 => ⟨hWl j (by omega) hj2, hSw j (by omega) hj2⟩)
  have hlevs : (allBelowN base.size fun i => clevelOK n base[i]! (allSteps S (pinvs n S) base)[i]!
        (cLevels n base (allSteps S (pinvs n S) base))[i]!) = true ∧
      (allBelowN base.size fun i => cschreierOK (cLevels n base (allSteps S (pinvs n S) base))
        (allSteps S (pinvs n S) base) (allInvSteps S (pinvs n S) base) base
        (Array.ofFn (n := base.size) fun i => i.val) false i chunks) = true := by
    by_cases hn : 0 < n
    · have H : Hyp n S base (Subgroup.closure ({permOfArr n S[0]!, permOfArr n S[1]!} :
          Set (Equiv.Perm (Fin n)))) (fun k => ⟨base[k]! % n, Nat.mod_lt _ hn⟩) :=
        ⟨fun j hj => (prep_permOfArr (hperm j hj)).1,
          fun j hj => by rw [hinvS j hj]; exact (prep_permOfArr (hperm j hj)).2, hmem, hb,
          fun k hk => Nat.mod_eq_of_lt (hb k hk)⟩
      refine ⟨allBelowN_iff.2 fun i hi => ?_,
        allBelowN_iff.2 fun i hi => schreier_ok H hcard' hi chunks⟩
      rw [lev_get hi, steps_get hi]
      exact CBF.clevelOK_of_facts (lv_facts H hi)
    · have h0 : base.size = 0 := by
        by_contra h
        have := hb 0 (by omega)
        omega
      rw [h0]
      exact ⟨allBelowN_iff.2 fun i hi => absurd hi (Nat.not_lt_zero _),
        allBelowN_iff.2 fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  unfold pointChainOK chainOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨by omega, hsz.symm⟩, allBelowN_iff.2 fun j hj => ?_⟩,
    allBelowN_iff.2 fun j hj => ?_⟩, allBelowN_iff.2 fun i hi => decide_eq_true (hb i hi)⟩,
    Array.size_ofFn⟩, allBelowN_iff.2 fun i hi => ?_⟩,
    allBelowN_iff.2 fun i hi => decide_eq_true (hb i hi)⟩, rfl⟩, hlevs.1⟩, hlevs.2⟩
  · rw [hinvS j hj]
    exact hperm j hj
  · by_cases hj2 : j < 2
    · simp [hj2]
    · rw [← hSw j (by omega) (by omega), hWl j (by omega) (by omega), peq_self]
      simp
  · rw [getElem!_ofFn_nat _ hi]
    simp [hi]

end CFSG.KS.PCC

end

module

public import Certificates.Data.Kernel.ChengHeldEAK
public import CFSG.Certificates.Kernel.ChengHeldPropsAutSound
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelEA
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ChengHeldS2

section Group

variable {H : Type} [Group H]

@[expose] def IsEA (K : Subgroup H) (k : ℕ) : Prop :=
  (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) ∧ (∀ a ∈ K, a * a = 1) ∧ Nat.card K = 2 ^ k

theorem isEA_bot : IsEA (⊥ : Subgroup H) 0 := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, by rw [Subgroup.card_bot]; rfl⟩
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rw [Subgroup.mem_bot.1 ha, one_mul]

@[expose] def extSub (K : Subgroup H) (a : H) (ha : a * a = 1) (hc : ∀ x ∈ K, a * x = x * a) :
    Subgroup H where
  carrier := {h | h ∈ K ∨ a * h ∈ K}
  mul_mem' := by
    intro x y hx hy
    have back : ∀ u, a * (a * u) = u := fun u => by rw [← mul_assoc, ha, one_mul]
    have comm_of : ∀ x, a * x ∈ K → a * x = x * a := fun x hx => by
      have h1 := hc _ hx
      rw [back] at h1
      calc a * x = a * x * a * a := by rw [mul_assoc (a * x) a a, ha, mul_one]
        _ = x * a := by rw [← h1]
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (K.mul_mem hx hy)
    · refine Or.inr ?_
      have e : a * (x * y) = x * (a * y) := by rw [← mul_assoc, hc x hx, mul_assoc]
      rw [e]
      exact K.mul_mem hx hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact K.mul_mem hx hy
    · refine Or.inl ?_
      have e : x * y = (a * x) * (a * y) := by
        rw [comm_of x hx, mul_assoc, ← mul_assoc a a y, ha, one_mul]
      rw [e]
      exact K.mul_mem hx hy
  one_mem' := Or.inl K.one_mem
  inv_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (K.inv_mem hx)
    · refine Or.inr ?_
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
      have hcx : a * x = x * a := by
        have h1 := hc _ hx
        rw [← mul_assoc, ha, one_mul] at h1
        calc a * x = a * x * a * a := by rw [mul_assoc (a * x) a a, ha, mul_one]
          _ = x * a := by rw [← h1]
      have e : a * x⁻¹ = (a * x)⁻¹ := by
        rw [mul_inv_rev, hai]
        exact ((Commute.inv_right (show Commute a x from hcx))).eq
      rw [e]
      exact K.inv_mem hx

theorem mem_extSub {K : Subgroup H} {a : H} {ha : a * a = 1} {hc : ∀ x ∈ K, a * x = x * a}
    {h : H} : h ∈ extSub K a ha hc ↔ h ∈ K ∨ a * h ∈ K := Iff.rfl

theorem isEA_ext {K : Subgroup H} {k : ℕ} (hK : IsEA K k) {a : H} (ha : a * a = 1)
    (hc : ∀ x ∈ K, a * x = x * a) (haK : a ∉ K) : IsEA (extSub K a ha hc) (k + 1) := by
  obtain ⟨hab, h2, hcard⟩ := hK
  have back : ∀ u, a * (a * u) = u := fun u => by rw [← mul_assoc, ha, one_mul]
  have form : ∀ x ∈ extSub K a ha hc, ∃ u ∈ K, x = u ∨ x = a * u := by
    rintro x (hx | hx)
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨a * x, hx, Or.inr (back x).symm⟩
  have cK : ∀ u ∈ K, Commute a u := fun u hu => hc u hu
  have cKK : ∀ u ∈ K, ∀ v ∈ K, Commute u v := fun u hu v hv => hab u hu v hv
  have cx : ∀ x ∈ extSub K a ha hc, ∀ u ∈ K, Commute x u := by
    intro x hx u hu
    obtain ⟨v, hv, hxv | hxv⟩ := form x hx <;> rw [hxv]
    · exact cKK v hv u hu
    · exact (cK u hu).mul_left (cKK v hv u hu)
  have cxa : ∀ x ∈ extSub K a ha hc, Commute x a := by
    intro x hx
    obtain ⟨v, hv, hxv | hxv⟩ := form x hx <;> rw [hxv]
    · exact (cK v hv).symm
    · exact (Commute.refl a).mul_left (cK v hv).symm
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨v, hv, hyv | hyv⟩ := form y hy <;> rw [hyv]
    · exact (cx x hx v hv).eq
    · exact ((cxa x hx).mul_right (cx x hx v hv)).eq
  · obtain ⟨v, hv, hxv | hxv⟩ := form x hx <;> rw [hxv]
    · exact h2 v hv
    · rw [mul_assoc, ← mul_assoc v a v, ← (cK v hv).eq, mul_assoc a v v, h2 v hv, mul_one, ha]
  · have hle : K ≤ extSub K a ha hc := fun x hx => Or.inl hx
    have hidx : (K.subgroupOf (extSub K a ha hc)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a, Or.inr (by rw [ha]; exact K.one_mem)⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      by_cases hb : (b : H) ∈ K
      · refine Or.inr ⟨hb, fun hba => haK ?_⟩
        have : a = (b : H)⁻¹ * ((b : H) * a) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact K.mul_mem (K.inv_mem hb) hba
      · refine Or.inl ⟨?_, hb⟩
        rcases b.2 with hb' | hb'
        · exact absurd hb' hb
        · rw [(cxa b b.2).eq]
          exact hb'
    have h1 := (K.subgroupOf (extSub K a ha hc)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hidx, hcard] at h1
    rw [← h1, pow_succ]

end Group

variable {M : RegModel} {H : Type} [Group H] (R : Rep M H)

@[expose] def Rp (r : ℕ) (K : Subgroup H) : Prop :=
  r < 2 ^ M.N ∧ ∀ h, r.testBit (R.pt h) = true ↔ h ∈ K

@[expose] def SK (k r : ℕ) : Prop := ∃ K : Subgroup H, IsEA K k ∧ Rp R r K

theorem rp_unique {r r' : ℕ} {K : Subgroup H} (h : Rp R r K) (h' : Rp R r' K) : r = r' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < M.N
  · obtain ⟨g, rfl⟩ := R.pt_surj i hi
    rw [Bool.eq_iff_iff, h.2, h'.2]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h'.1 (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem eaMask_lt {X : Array ℕ} (hX : ∀ i ∈ X.toList, i < M.N) : eaMask X < 2 ^ M.N := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [eaMask_testBit, decide_eq_false_iff_not]
  exact fun h => absurd (hX i h) (by omega)

theorem rp_eaMask {X : Array ℕ} {K : Subgroup H} (hX : ∀ i, i ∈ X.toList ↔ ∃ h ∈ K, R.pt h = i) :
    Rp R (eaMask X) K := by
  refine ⟨eaMask_lt fun i hi => ?_, fun h => ?_⟩
  · obtain ⟨g, -, rfl⟩ := (hX i).1 hi
    exact R.pt_lt g
  · rw [eaMask_testBit, decide_eq_true_iff, hX]
    exact ⟨fun ⟨g, hg, e⟩ => R.pt_inj e ▸ hg, fun hh => ⟨h, hh, rfl⟩⟩

@[expose] def Pext (M : RegModel) (L : Array (Array ℕ)) (invs : Array ℕ) (X : Array ℕ) : Prop :=
  ∃ E ∈ L.toList, ∃ a ∈ invs.toList, (eaMask E).testBit a = false ∧
    (∀ e ∈ E.toList, M.m a e = M.m e a) ∧ X = E ++ E.map fun e => M.m a e

@[expose] def EaInv (M : RegModel) (L : Array (Array ℕ)) (invs : Array ℕ)
    (s : Std.HashSet ℕ × Array (Array ℕ)) : Prop :=
  (∀ x, s.1.contains x = true ↔ x ∈ s.2.toList.map eaMask) ∧ (s.2.toList.map eaMask).Nodup ∧
    ∀ X ∈ s.2.toList, Pext M L invs X

theorem eaInv_step {L : Array (Array ℕ)} {invs : Array ℕ} {E : Array ℕ} (hE : E ∈ L.toList)
    {a : ℕ} (ha : a ∈ invs.toList) {s : Std.HashSet ℕ × Array (Array ℕ)} (hs : EaInv M L invs s) :
    EaInv M L invs (eaNextStep M E s a) := by
  obtain ⟨h1, h2, h3⟩ := hs
  unfold eaNextStep
  split_ifs with c1 c2
  · have hn : eaMask (E ++ E.map fun e => M.m a e) ∉ s.2.toList.map eaMask := by
      rw [← h1]
      simpa using c2
    refine ⟨fun x => ?_, ?_, fun X hX => ?_⟩
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, h1, Array.toList_push,
        List.map_append, List.mem_append]
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      exact ⟨fun h => h.elim (fun e => Or.inr e.symm) Or.inl,
        fun h => h.elim Or.inr (fun e => Or.inl e.symm)⟩
    · rw [Array.toList_push, List.map_append]
      refine List.Nodup.append h2 (by simp) ?_
      simp only [List.map_cons, List.map_nil, List.disjoint_singleton]
      exact hn
    · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hX
      rcases hX with hX | rfl
      · exact h3 X hX
      · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Array.all_eq_true',
          beq_iff_eq] at c1
        exact ⟨E, hE, a, ha, c1.1, fun e he => c1.2 e (Array.mem_def.2 he), rfl⟩
  · exact ⟨h1, h2, h3⟩
  · exact ⟨h1, h2, h3⟩

theorem foldl_mem_inv {σ α : Type} (f : σ → α → σ) (I : σ → Prop) :
    ∀ (l : List α), (∀ s x, x ∈ l → I s → I (f s x)) → ∀ s, I s → I (l.foldl f s)
  | [], _, s, hs => hs
  | x :: l, h, s, hs => foldl_mem_inv f I l (fun s y hy => h s y (List.mem_cons_of_mem _ hy))
      (f s x) (h s x List.mem_cons_self hs)

theorem eaNext_inv (L : Array (Array ℕ)) (invs : Array ℕ) :
    EaInv M L invs (L.foldl (fun s E => invs.foldl (eaNextStep M E) s) (∅, #[])) := by
  rw [← Array.foldl_toList]
  refine foldl_mem_inv _ _ _ (fun s E hE hs => ?_) _ ⟨fun x => by simp, by simp, by simp⟩
  rw [← Array.foldl_toList]
  exact foldl_mem_inv _ _ _ (fun s a ha hs => eaInv_step hE ha hs) _ hs

theorem pt_sq {h : H} (hh : M.m (R.pt h) (R.pt h) = 0) : h * h = 1 :=
  R.pt_inj (by rw [R.pt_mul, hh, R.pt_one])

theorem eaInvs_spec {a : ℕ} (ha : a ∈ (eaInvs M).toList) :
    a < M.N ∧ a ≠ 0 ∧ M.m a a = 0 := by
  unfold eaInvs at ha
  simp only [List.toList_toArray, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2⟩

theorem eaL_sound (k : ℕ) : ∀ X ∈ (eaL M (k + 1)).toList, ∃ K : Subgroup H, IsEA K (k + 1) ∧
    ∀ i, i ∈ X.toList ↔ ∃ h ∈ K, R.pt h = i := by
  induction k with
  | zero =>
    intro X hX
    have e1 : eaL M 1 = (eaInvs M).map fun a => #[0, a] := rfl
    rw [e1, Array.toList_map, List.mem_map] at hX
    obtain ⟨a, ha, rfl⟩ := hX
    obtain ⟨ha1, ha2, ha3⟩ := eaInvs_spec ha
    obtain ⟨g, rfl⟩ := R.pt_surj a ha1
    have hg : g * g = 1 := pt_sq R ha3
    have hgK : g ∉ (⊥ : Subgroup H) := fun h => ha2 (by rw [Subgroup.mem_bot.1 h, R.pt_one])
    have hc : ∀ x ∈ (⊥ : Subgroup H), g * x = x * g := fun x hx => by
      rw [Subgroup.mem_bot.1 hx, mul_one, one_mul]
    refine ⟨extSub ⊥ g hg hc, isEA_ext isEA_bot hg hc hgK, fun i => ?_⟩
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_extSub, Subgroup.mem_bot]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, R.pt_one⟩
      · exact ⟨g, Or.inr hg, rfl⟩
    · rintro ⟨h, hh | hh, rfl⟩
      · exact Or.inl (by rw [hh, R.pt_one])
      · right
        rw [eq_inv_of_mul_eq_one_right hh, hgi]
  | succ k ih =>
    intro X hX
    have e2 : eaL M (k + 2) = M.eaNext (eaInvs M) (eaL M (k + 1)) := rfl
    rw [e2, eaNext_eq_foldl] at hX
    obtain ⟨E, hE, a, ha, hbit, hcom, rfl⟩ := (eaNext_inv (M := M) _ _).2.2 X hX
    obtain ⟨K, hK, hEK⟩ := ih E hE
    obtain ⟨ha1, -, ha3⟩ := eaInvs_spec ha
    obtain ⟨g, rfl⟩ := R.pt_surj a ha1
    have hg : g * g = 1 := pt_sq R ha3
    have hgK : g ∉ K := fun h => by
      have : R.pt g ∈ E.toList := (hEK _).2 ⟨g, h, rfl⟩
      rw [eaMask_testBit, decide_eq_false_iff_not] at hbit
      exact hbit this
    have hc : ∀ x ∈ K, g * x = x * g := fun x hx => R.pt_inj (by
      rw [R.pt_mul, R.pt_mul]
      exact hcom _ ((hEK _).2 ⟨x, hx, rfl⟩))
    refine ⟨extSub K g hg hc, isEA_ext hK hg hc hgK, fun i => ?_⟩
    have back : ∀ u, g * (g * u) = u := fun u => by rw [← mul_assoc, hg, one_mul]
    rw [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map]
    constructor
    · rintro (hi | ⟨e, he, rfl⟩)
      · obtain ⟨h, hh, rfl⟩ := (hEK _).1 hi
        exact ⟨h, Or.inl hh, rfl⟩
      · obtain ⟨h, hh, rfl⟩ := (hEK _).1 he
        refine ⟨g * h, Or.inr (by rw [back]; exact hh), R.pt_mul g h⟩
    · rintro ⟨h, hh | hh, rfl⟩
      · exact Or.inl ((hEK _).2 ⟨h, hh, rfl⟩)
      · exact Or.inr ⟨R.pt (g * h), (hEK _).2 ⟨_, hh, rfl⟩, by rw [← R.pt_mul, back]⟩

theorem eaL_nodup (k : ℕ) : ((eaL M (k + 1)).toList.map eaMask).Nodup := by
  cases k with
  | zero =>
    have e1 : eaL M 1 = (eaInvs M).map fun a => #[0, a] := rfl
    rw [e1, Array.toList_map, List.map_map]
    have hnd : (eaInvs M).toList.Nodup := by
      unfold eaInvs
      simpa using (List.nodup_range).filter _
    refine hnd.map_on fun a ha b hb e => ?_
    have hb0 := (eaInvs_spec hb).2.1
    rw [Function.comp_apply, Function.comp_apply] at e
    have h1 : (eaMask #[0, b]).testBit b = true := by
      rw [eaMask_testBit]
      simp
    rw [← e, eaMask_testBit] at h1
    simp at h1
    rcases h1 with h | h
    · exact absurd h hb0
    · exact h.symm
  | succ k =>
    have e2 : eaL M (k + 2) = M.eaNext (eaInvs M) (eaL M (k + 1)) := rfl
    rw [e2, eaNext_eq_foldl]
    exact (eaNext_inv _ _).2.1

theorem size_eaL (k : ℕ) {LC : List ℕ} (hnd : LC.Nodup) (hmem : ∀ r, r ∈ LC ↔ SK R (k + 1) r) :
    (eaL M (k + 1)).size = LC.length := by
  have hLM : ∀ r, r ∈ (eaL M (k + 1)).toList.map eaMask ↔ r ∈ LC := by
    intro r
    rw [hmem, List.mem_map]
    constructor
    · rintro ⟨X, hX, rfl⟩
      obtain ⟨K, hK, hXK⟩ := eaL_sound R k X hX
      exact ⟨K, hK, rp_eaMask R hXK⟩
    · rintro ⟨K, ⟨hab, h2, hcard⟩, hr⟩
      obtain ⟨l, hl, hlK⟩ := Rep.eaL_complete R (k + 1) (by omega) K hab h2 hcard
      refine ⟨l, Array.mem_def.1 hl, rp_unique R (rp_eaMask R fun i => ?_) hr⟩
      constructor
      · intro hi
        obtain ⟨K', -, hK'⟩ := eaL_sound R k l (Array.mem_def.1 hl)
        obtain ⟨g, -, rfl⟩ := (hK' i).1 hi
        exact ⟨g, (hlK g).2 hi, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact (hlK g).1 hg
  have e := List.toFinset_card_of_nodup (eaL_nodup (M := M) k)
  rw [show ((eaL M (k + 1)).toList.map eaMask).toFinset = LC.toFinset from
    Finset.ext fun r => by simp only [List.mem_toFinset, hLM], List.toFinset_card_of_nodup hnd,
    List.length_map, Array.length_toList] at e
  exact e.symm

variable {n w : ℕ} {T PL G : ℕ → ℕ} {IXP IVP : ℕ}

@[expose] def LevelOK (k n L c : ℕ) : Prop :=
  ((List.range c).map fun j => pg n (mask n) L j).Nodup ∧
    ∀ r, r ∈ (List.range c).map (fun j => pg n (mask n) L j) ↔ SK R k r

theorem bitM_eq (B x : ℕ) : bitM B x = B.testBit x := by
  unfold bitM
  rw [Bool.eq_iff_iff, Nat.blt_eq]
  change 0 < B &&& 1 <<< x ↔ _
  rw [Nat.one_shiftLeft, Nat.and_two_pow]
  cases B.testBit x <;> simp

theorem subM_iff (A B : ℕ) : subM A B = true ↔ ∀ i, A.testBit i = true → B.testBit i = true := by
  unfold subM
  rw [Nat.beq_eq]
  change A &&& B = A ↔ _
  constructor
  · intro h i hi
    have e := congrArg (fun z => z.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at e
    exact e
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hA : A.testBit i
    · rfl
    · rw [h i hA]
      rfl

theorem bEqv_iff (p q : Bool) : bEqv p q = true ↔ p = q := by
  cases p <;> cases q <;> decide

theorem pg_lt (w P i : ℕ) : pg w (mask w) P i < 2 ^ w := by
  unfold pg mask
  change P >>> (w * i) &&& (1 <<< w - 1) < 2 ^ w
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem eaMask_pair (a : ℕ) : eaMask #[0, a] = Nat.lor 1 (Nat.shiftLeft 1 a) := by
  unfold eaMask
  rw [← Array.foldl_toList]
  rfl

theorem bIf_pos {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem ne_of_notBeq {a b : ℕ} (h : (!Nat.beq a b) = true) : a ≠ b := by
  intro e
  subst e
  simp [Nat.beq_refl] at h

theorem notBeq_of_ne {a b : ℕ} (h : a ≠ b) : (!Nat.beq a b) = true := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem testBit_lt {r i N : ℕ} (hr : r < 2 ^ N) (hi : r.testBit i = true) : i < N := by
  have := Nat.ge_two_pow_of_testBit hi
  by_contra hc
  have : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem nodup_of_incr {f : ℕ → ℕ} {c : ℕ} (h : ∀ t < c - 1, f t < f (t + 1)) :
    ((List.range c).map f).Nodup := by
  have mono : ∀ i j, i < j → j < c → f i < f j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
      · exact lt_trans (ih hij (by omega)) (h j (by omega))
      · exact h i (by omega)
  refine (List.nodup_range).map_on fun i hi j hj e => ?_
  rw [List.mem_range] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (ne_of_lt (mono i j hlt hj))
  · exact absurd e (ne_of_gt (mono j i hlt hi))

theorem exists_rp (K : Subgroup H) : ∃ r, Rp R r K := by
  classical
  refine ⟨eaMask ((List.range M.N).filter fun i => ∃ h ∈ K, R.pt h = i).toArray,
    rp_eaMask R fun i => ?_⟩
  simp only [List.toList_toArray, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ⟨g, hg, e⟩ => ⟨e ▸ R.pt_lt g, g, hg, e⟩⟩

structure Rows (M : RegModel) (n w : ℕ) (T : ℕ → ℕ) (IXP IVP : ℕ) : Prop where
  N_eq : M.N = n
  row : ∀ x y, x < n → y < n → pg w (mask w) (T (pg w (mask w) IXP x)) y = M.m x y
  inv : ∀ x, iW n w IVP x = M.inv[x]!

theorem rows_of {PL G : ℕ → ℕ} (hB : Bound M n w T PL G IXP IVP) : Rows M n w T IXP IVP :=
  ⟨hB.N_eq, fun x y hx hy => by rw [hB.m_eq, mW_row hx hy], fun x => (hB.inv_eq x).symm⟩

variable {AP RK CMP cI : ℕ}

theorem eaInvW_parts (hW : Rows M n w T IXP IVP) (h : eaInvW n w T IXP AP RK cI = true) :
    (∀ t < cI, ∃ g : H, R.pt g = pg w (mask w) AP t ∧ g ≠ 1 ∧ g * g = 1) ∧
    (∀ g : H, g ≠ 1 → g * g = 1 → pg w (mask w) RK (R.pt g) < cI ∧
      pg w (mask w) AP (pg w (mask w) RK (R.pt g)) = R.pt g) := by
  unfold eaInvW at h
  rw [bAnd_iff] at h
  have hN := hW.N_eq
  refine ⟨fun t ht => ?_, fun g hg1 hg2 => ?_⟩
  · have h1 := allN_spec h.1 t ht
    simp only [strictB_eq] at h1
    rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h1
    obtain ⟨a1, a2, a3⟩ := h1
    obtain ⟨g, hg⟩ := R.pt_surj _ (by rw [hN]; exact a1)
    refine ⟨g, hg, fun e => ne_of_notBeq a2 (by rw [← hg, e, R.pt_one]), pt_sq R ?_⟩
    rw [hg, ← hW.row _ _ a1 a1]
    exact Nat.eq_of_beq_eq_true a3
  · have hx : R.pt g < n := hN ▸ R.pt_lt g
    have h1 := allN_spec h.2 (R.pt g) hx
    simp only [strictB_eq] at h1
    have hc : bAnd(Bool.not (Nat.beq (R.pt g) 0),
        Nat.beq (pg w (mask w) (T (pg w (mask w) IXP (R.pt g))) (R.pt g)) 0) = true := by
      rw [bAnd_iff]
      refine ⟨notBeq_of_ne fun e => hg1 (R.pt_inj (by rw [e, R.pt_one])), ?_⟩
      rw [hW.row _ _ hx hx, ← R.pt_mul, hg2, R.pt_one]
      exact Nat.beq_refl 0
    have h2 := bIf_pos h1 hc
    rw [bAnd_iff, Nat.blt_eq] at h2
    exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem eaCMW_parts (hW : Rows M n w T IXP IVP) (h : eaCMW n w T IXP IVP AP CMP cI = true)
    {t : ℕ} (ht : t < cI) {g : H} (hg : R.pt g = pg w (mask w) AP t) (hg2 : g * g = 1) (x : H) :
    (pg n (mask n) CMP t).testBit (R.pt x) = true ↔ g * x = x * g := by
  have hN := hW.N_eq
  have hx : R.pt x < n := hN ▸ R.pt_lt x
  have hgn : R.pt g < n := hN ▸ R.pt_lt g
  have h1 := allN_spec h t ht
  simp only [strictB_eq] at h1
  rw [← hg] at h1
  have h2 := allN_spec h1 (R.pt x) hx
  rw [bEqv_iff, bitM_eq] at h2
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have e1 : iW n w IVP (R.pt x) = R.pt x⁻¹ := by rw [hW.inv, R.pt_inv]
  have e2 : pg w (mask w) (T (pg w (mask w) IXP (R.pt g))) (R.pt x⁻¹) = R.pt (g * x⁻¹) := by
    rw [hW.row _ _ hgn (hN ▸ R.pt_lt _), R.pt_mul]
  have e3 : iW n w IVP (R.pt (g * x⁻¹)) = R.pt (g * x⁻¹)⁻¹ := by rw [hW.inv, R.pt_inv]
  have e4 : pg w (mask w) (T (pg w (mask w) IXP (R.pt g))) (R.pt x) = R.pt (g * x) := by
    rw [hW.row _ _ hgn hx, R.pt_mul]
  rw [h2, e1, e2, e3, e4, Nat.beq_eq, R.pt_inj.eq_iff, mul_inv_rev, inv_inv, hgi]

theorem levelOK_one (hW : Rows M n w T IXP IVP) {L1 : ℕ} (hI : eaInvW n w T IXP AP RK cI = true)
    (hL : eaL1W n w AP L1 cI = true) : LevelOK R 1 n L1 cI := by
  obtain ⟨hI1, hI2⟩ := eaInvW_parts R hW hI
  unfold eaL1W at hL
  rw [bAnd_iff] at hL
  have hval : ∀ t < cI, pg n (mask n) L1 t = eaMask #[0, pg w (mask w) AP t] := by
    intro t ht
    rw [Nat.eq_of_beq_eq_true (allN_spec hL.1 t ht), eaMask_pair]
  have pair : ∀ g : H, g ≠ 1 → g * g = 1 → ∃ K, IsEA K 1 ∧ Rp R (eaMask #[0, R.pt g]) K ∧ g ∈ K := by
    intro g hg1 hg
    have hgK : g ∉ (⊥ : Subgroup H) := fun h => hg1 (Subgroup.mem_bot.1 h)
    have hc : ∀ x ∈ (⊥ : Subgroup H), g * x = x * g := fun x hx => by
      rw [Subgroup.mem_bot.1 hx, mul_one, one_mul]
    refine ⟨extSub ⊥ g hg hc, isEA_ext isEA_bot hg hc hgK, rp_eaMask R fun i => ?_,
      Or.inr (by rw [hg]; exact Subgroup.one_mem _)⟩
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_extSub, Subgroup.mem_bot]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨1, Or.inl rfl, R.pt_one⟩
      · exact ⟨g, Or.inr hg, rfl⟩
    · rintro ⟨h, hh | hh, rfl⟩
      · exact Or.inl (by rw [hh, R.pt_one])
      · right
        rw [eq_inv_of_mul_eq_one_right hh, hgi]
  refine ⟨nodup_of_incr fun t ht => Nat.blt_eq.mp (allN_spec hL.2 t ht), fun r => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range] at ht
    obtain ⟨g, hg, hg1, hg2⟩ := hI1 t ht
    obtain ⟨K, hK, hr, -⟩ := pair g hg1 hg2
    rw [hval t ht, ← hg]
    exact ⟨K, hK, hr⟩
  · rintro ⟨K, ⟨hab, h2, hcard⟩, hr⟩
    have := R.finite
    obtain ⟨g, hgK, hg1, hKg⟩ := eaL_exists_coset (F := ⊥) bot_le
      (by rw [hcard, Subgroup.card_bot]; rfl)
    have hg1' : g ≠ 1 := fun e => hg1 (e ▸ Subgroup.one_mem _)
    obtain ⟨hlt, hap⟩ := hI2 g hg1' (h2 g hgK)
    refine ⟨_, List.mem_range.2 hlt, ?_⟩
    obtain ⟨K', hK', hr', hgK'⟩ := pair g hg1' (h2 g hgK)
    rw [hval _ hlt, hap]
    have hle : K ≤ K' := fun h hh => by
      rcases hKg h hh with e | e
      · rw [Subgroup.mem_bot.1 e]
        exact K'.one_mem
      · rw [← inv_mul_eq_one.1 (Subgroup.mem_bot.1 e)]
        exact hgK'
    have heq : K = K' := Subgroup.eq_of_le_of_card_ge hle (by rw [hK'.2.2, hcard])
    rw [heq] at hr
    exact rp_unique R hr' hr

theorem levelOK_succ (hW : Rows M n w T IXP IVP) {k L0 c0 L1 c1 PJ PT b : ℕ} {Wt : ℕ → ℕ}
    (hI : eaInvW n w T IXP AP RK cI = true) (hC : eaCMW n w T IXP IVP AP CMP cI = true)
    (h0 : LevelOK R k n L0 c0) (hU : eaUpW n w T IXP AP CMP cI L0 c0 L1 c1 PJ PT = true)
    (hV : eaWitW n w AP CMP cI L0 c0 L1 c1 Wt b = true) : LevelOK R (k + 1) n L1 c1 := by
  have hN := hW.N_eq
  obtain ⟨hI1, hI2⟩ := eaInvW_parts R hW hI
  unfold eaUpW at hU
  rw [bAnd_iff] at hU
  have sound : ∀ i < c1, SK R (k + 1) (pg n (mask n) L1 i) := by
    intro i hi
    have h1 := allN_spec hU.1 i hi
    simp only [strictB_eq] at h1
    rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.blt_eq] at h1
    obtain ⟨hj, ht, hbit, hsub, hF⟩ := h1
    obtain ⟨g, hg, hg1, hg2⟩ := hI1 _ ht
    obtain ⟨K, hK, hEK⟩ := (h0.2 _).1 (List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩)
    have hgK : g ∉ K := fun hgk => by
      rw [← hg, bitM_eq, (hEK.2 g).2 hgk] at hbit
      exact absurd hbit (by decide)
    have hc : ∀ x ∈ K, g * x = x * g := fun x hx =>
      (eaCMW_parts R hW hC ht hg hg2 x).1 ((subM_iff _ _).1 hsub _ ((hEK.2 x).2 hx))
    refine ⟨extSub K g hg2 hc, isEA_ext hK hg2 hc hgK,
      lt_of_lt_of_le (pg_lt n L1 i) (Nat.pow_le_pow_right (by norm_num) (by omega)), fun h => ?_⟩
    have hy := allN_spec hF (R.pt h) (hN ▸ R.pt_lt h)
    rw [bEqv_iff, bitM_eq, bitM_eq, bitM_eq, ← hg, hW.row _ _ (hN ▸ R.pt_lt g) (hN ▸ R.pt_lt h),
      ← R.pt_mul] at hy
    rw [hy, Bool.or_eq_true, hEK.2, hEK.2, mem_extSub]
  refine ⟨nodup_of_incr fun t ht => Nat.blt_eq.mp (allN_spec hU.2 t ht), fun r => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact sound i (List.mem_range.1 hi)
  · rintro ⟨X, ⟨hab, h2, hcard⟩, hr⟩
    have := R.finite
    obtain ⟨Y0, hY0⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := k)
      (by rw [hcard]; exact pow_dvd_pow 2 (by omega))
    set Y := Y0.map X.subtype with hYdef
    have hYX : Y ≤ X := Subgroup.map_subtype_le Y0
    have hYc : Nat.card Y = 2 ^ k := by
      rw [Subgroup.card_map_of_injective X.subtype_injective, hY0]
    obtain ⟨rY, hrY⟩ := exists_rp R Y
    obtain ⟨j, hj, hjY⟩ := List.mem_map.1 ((h0.2 rY).2
      ⟨Y, ⟨fun a ha b hb => hab a (hYX ha) b (hYX hb), fun a ha => h2 a (hYX ha), hYc⟩, hrY⟩)
    rw [List.mem_range] at hj
    obtain ⟨g, hgX, hgY, hXg⟩ := eaL_exists_coset hYX (by rw [hcard, hYc, pow_succ, mul_comm])
    have hg1 : g ≠ 1 := fun e => hgY (e ▸ Y.one_mem)
    obtain ⟨ht, hap⟩ := hI2 g hg1 (h2 g hgX)
    have hrYE : Rp R (pg n (mask n) L0 j) Y := by rw [hjY]; exact hrY
    have h1 := allN_spec hV j hj
    simp only [strictB_eq] at h1
    have h3 := allN_spec h1 _ ht
    rw [hap] at h3
    have hc : bAnd(Bool.not (bitM (pg n (mask n) L0 j) (R.pt g)),
        subM (pg n (mask n) L0 j) (pg n (mask n) CMP (pg w (mask w) RK (R.pt g)))) = true := by
      rw [bAnd_iff, bitM_eq]
      refine ⟨?_, ?_⟩
      · cases hb : (pg n (mask n) L0 j).testBit (R.pt g)
        · rfl
        · exact absurd ((hrYE.2 g).1 hb) hgY
      rw [subM_iff]
      intro i hi
      obtain ⟨y, rfl⟩ := R.pt_surj i (testBit_lt hrYE.1 hi)
      rw [eaCMW_parts R hW hC ht hap.symm (h2 g hgX) y]
      exact hab g hgX y (hYX ((hrYE.2 y).1 hi))
    have h4 := bIf_pos h3 hc
    rw [bAnd_iff, Nat.blt_eq, bAnd_iff, bitM_eq] at h4
    obtain ⟨hi1, hsub, hgF⟩ := h4
    refine ⟨_, List.mem_range.2 hi1, ?_⟩
    obtain ⟨K, hK, hFK⟩ := sound _ hi1
    have hYK : ∀ y ∈ Y, y ∈ K := fun y hy =>
      (hFK.2 y).1 ((subM_iff _ _).1 hsub _ ((hrYE.2 y).2 hy))
    have hgK : g ∈ K := (hFK.2 g).1 hgF
    have hle : X ≤ K := fun h hh => by
      rcases hXg h hh with e | e
      · exact hYK h e
      · have : h = g * (g⁻¹ * h) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
        rw [this]
        exact K.mul_mem hgK (hYK _ e)
    have heq : X = K := Subgroup.eq_of_le_of_card_ge hle (by rw [hK.2.2, hcard])
    rw [heq] at hr
    exact rp_unique R hFK hr

theorem eaCounts_of {L : ℕ → ℕ} {c : ℕ → ℕ} (h : ∀ k < 6, LevelOK R (k + 1) n (L k) (c k)) :
    M.eaCounts = [c 0, c 1, c 2, c 3, c 4, c 5] := by
  have e : ∀ k < 6, (eaL M (k + 1)).size = c k := fun k hk => by
    rw [size_eaL R k (h k hk).1 (h k hk).2, List.length_map, List.length_range]
  rw [eaCounts_eq, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num)]

end CFSG.KC.ChengHeldP

end

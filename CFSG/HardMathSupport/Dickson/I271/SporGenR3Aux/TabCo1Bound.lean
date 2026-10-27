module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveLeaf
public import CFSG.Sporadic.Schreier.Co1Chain
public import Certificates.Data.TabCo1Kit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Matrix

attribute [local instance] CFSG.Sporadic.Co1Schreier.vecAct

section Chain

@[expose] noncomputable def vCh (G : Subgroup GL24) (base : List ℕ) : ℕ → Subgroup GL24
  | 0 => G
  | i + 1 => (MulAction.stabilizer (vCh G base i) (toVecD 24 (base.getD i 0))).map
      (vCh G base i).subtype

variable {H : Subgroup GL24} {base : List ℕ}

theorem mem_vCh_succ {i : ℕ} {g : GL24} :
    g ∈ vCh H base (i + 1) ↔
      g ∈ vCh H base i ∧ g • toVecD 24 (base.getD i 0) = toVecD 24 (base.getD i 0) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hs⟩
    exact ⟨⟨g, hg⟩, hs, rfl⟩

theorem card_vCh (i : ℕ) : Nat.card (vCh H base i) =
    Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0))) *
      Nat.card (vCh H base (i + 1)) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (vCh H base i)
      (toVecD 24 (base.getD i 0))),
    Nat.card_prod, vCh, Subgroup.card_map_of_injective (vCh H base i).subtype_injective]

theorem vCh_le (i : ℕ) : vCh H base i ≤ H := by
  induction i with
  | zero => exact fun x hx => hx
  | succ i ih =>
    intro g hg
    exact ih (mem_vCh_succ.1 hg).1

theorem fix_of_mem_vCh {i : ℕ} {g : GL24} (hg : g ∈ vCh H base i) {j : ℕ} (hj : j < i) :
    ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 (base.getD j 0) =
      toVecD 24 (base.getD j 0) := by
  induction i with
  | zero => omega
  | succ i ih =>
    obtain ⟨h1, h2⟩ := mem_vCh_succ.1 hg
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact ih h1 h
    · exact h2

theorem card_le_prod_of_orbit_bound (cnt : ℕ → ℕ)
    (horb : ∀ i < base.length,
      Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0))) ≤ cnt i)
    (hbot : ∀ g ∈ vCh H base base.length, g = 1) :
    Nat.card H ≤ ∏ i ∈ Finset.range base.length, cnt i := by
  have key : ∀ k ≤ base.length, Nat.card H ≤
      (∏ i ∈ Finset.range k, cnt i) * Nat.card (vCh H base k) := by
    intro k
    induction k with
    | zero => intro _; rw [Finset.prod_range_zero, one_mul]; exact le_of_eq rfl
    | succ k ih =>
      intro hk
      refine le_trans (ih (by omega)) ?_
      rw [Finset.prod_range_succ, mul_assoc, card_vCh (H := H) (base := base) k]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (horb k (by omega)))
  have h1 : Nat.card (vCh H base base.length) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
    rw [hbot a.1 a.2, hbot b.1 b.2]
  have := key base.length le_rfl
  rwa [h1, mul_one] at this

end Chain


section Vectors

variable {cs : Array (Array ℕ)} {B : ℕ → Matrix (Fin 24) (Fin 24) (ZMod 2)}

theorem toVecD_slotN (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    (base : List ℕ) (s : ℕ × ℕ) :
    toVecD 24 (slotN cs base s) = B s.2 *ᵥ toVecD 24 (base.getD s.1 0) := by
  unfold slotN
  rw [hB]

theorem slotN_lt (hlt : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24) (base : List ℕ)
    (s : ℕ × ℕ) : slotN cs base s < 2 ^ 24 :=
  CFSG.Sporadic.Co1.Module.vecMulN_lt _ (hlt s.2) _

theorem fN_lt (hlt : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24) (base : List ℕ)
    (F : List (ℕ × ℕ)) : fN cs base F < 2 ^ 24 := by
  unfold fN
  have : ∀ acc, acc < 2 ^ 24 → F.foldl (fun acc s => acc ^^^ slotN cs base s) acc < 2 ^ 24 := by
    induction F with
    | nil => exact fun acc h => h
    | cons s F ih =>
      intro acc h
      rw [List.foldl_cons]
      exact ih _ (Nat.xor_lt_two_pow h (slotN_lt hlt base s))
  exact this 0 (by norm_num)

theorem combN_lt (hlt : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24) (S : List ℕ) {F : ℕ}
    (hF : F < 2 ^ 24) (x : ℕ) : combN cs S F x < 2 ^ 24 := by
  unfold combN
  have : ∀ acc, acc < 2 ^ 24 → S.foldl (fun acc a => acc ^^^ vecMulN 24 (cs.getD a #[]) x) acc <
      2 ^ 24 := by
    induction S with
    | nil => exact fun acc h => h
    | cons a S ih =>
      intro acc h
      rw [List.foldl_cons]
      exact ih _ (Nat.xor_lt_two_pow h (CFSG.Sporadic.Co1.Module.vecMulN_lt _ (hlt a) _))
  exact this F hF

theorem fN_fixed (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hM : ∀ a, M * B a = B a * M) (base : List ℕ)
    (F : List (ℕ × ℕ))
    (hfix : ∀ s ∈ F, M *ᵥ toVecD 24 (base.getD s.1 0) = toVecD 24 (base.getD s.1 0)) :
    M *ᵥ toVecD 24 (fN cs base F) = toVecD 24 (fN cs base F) := by
  unfold fN
  have : ∀ acc, M *ᵥ toVecD 24 acc = toVecD 24 acc → (∀ s ∈ F, M *ᵥ toVecD 24 (base.getD s.1 0) =
      toVecD 24 (base.getD s.1 0)) →
      M *ᵥ toVecD 24 (F.foldl (fun acc s => acc ^^^ slotN cs base s) acc) =
        toVecD 24 (F.foldl (fun acc s => acc ^^^ slotN cs base s) acc) := by
    clear hfix
    induction F with
    | nil => exact fun acc h _ => h
    | cons s F ih =>
      intro acc h hf
      rw [List.foldl_cons]
      refine ih _ ?_ (fun t ht => hf t (List.mem_cons_of_mem _ ht))
      rw [toVecD_xor, Matrix.mulVec_add, h, toVecD_slotN hB, Matrix.mulVec_mulVec, hM,
        ← Matrix.mulVec_mulVec, hf s List.mem_cons_self]
  exact this 0 (by rw [toVecD_zero, Matrix.mulVec_zero]) hfix

theorem combN_equiv (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hM : ∀ a, M * B a = B a * M) (S : List ℕ) {F : ℕ}
    (hF : M *ᵥ toVecD 24 F = toVecD 24 F) {x u : ℕ} (hxu : toVecD 24 x = M *ᵥ toVecD 24 u) :
    toVecD 24 (combN cs S F x) = M *ᵥ toVecD 24 (combN cs S F u) := by
  unfold combN
  have : ∀ (a b : ℕ), toVecD 24 b = M *ᵥ toVecD 24 a →
      toVecD 24 (S.foldl (fun acc a => acc ^^^ vecMulN 24 (cs.getD a #[]) x) b) =
        M *ᵥ toVecD 24 (S.foldl (fun acc a => acc ^^^ vecMulN 24 (cs.getD a #[]) u) a) := by
    induction S with
    | nil => exact fun a b h => h
    | cons c S ih =>
      intro a b h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih _ _ ?_
      rw [toVecD_xor, toVecD_xor, h, ← hB, ← hB, hxu, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hM]
  exact this F F hF.symm

end Vectors


section Types

open Classical in
@[expose] noncomputable def typV (w : Vec24) : ℕ :=
  if w = 0 then 0 else if w ∈ CFSG.Sporadic.Co1Block.certX then 2 else 3


theorem lt_of_mem_certVecs {v : ℕ} (hv : v ∈ certVecs.toList) : v < 2 ^ 24 := by
  obtain ⟨i, hi, rfl⟩ := mem_certVecs_iff.1 hv
  exact certVecs_lt hi

theorem mem_certX_iff {v : ℕ} (hv : v < 2 ^ 24) :
    toVecD 24 v ∈ CFSG.Sporadic.Co1Block.certX ↔ v ∈ certVecs.toList := by
  constructor
  · intro h
    obtain ⟨y, hy, hyv⟩ := exists_mem_of_certX h
    have := toVecD_injective (lt_of_mem_certVecs hy) hv hyv
    rwa [this] at hy
  · exact toVecD_mem_certX

theorem typN_eq {v : ℕ} (hv : v < 2 ^ 24) : typN (xsSet ()) v = typV (toVecD 24 v) := by
  unfold typN typV xsSet
  by_cases h0 : v = 0
  · subst h0
    simp [toVecD_zero]
  · have h1 : toVecD 24 v ≠ 0 := fun h =>
      h0 (toVecD_injective hv (by norm_num) (by rw [h, toVecD_zero]))
    have h2 : (v == 0) = false := by simpa using h0
    rw [h2, if_neg h1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hm : v ∈ certVecs.toList
    · have h3 : (Std.HashSet.ofList certVecs.toList).contains v = true := contains_xs.2 hm
      rw [if_pos h3, if_pos ((mem_certX_iff hv).2 hm)]
    · have h3 : ¬ (Std.HashSet.ofList certVecs.toList).contains v = true :=
        fun h => hm (contains_xs.1 h)
      rw [if_neg h3, if_neg (fun h => hm ((mem_certX_iff hv).1 h))]

theorem inv_mulVec_mulVec (g : GL24) (w : Vec24) :
    ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem typV_mulVec {g : GL24} (hg : g ∈ GA) (w : Vec24) :
    typV (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w) = typV w := by
  have h0 : ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = 0 ↔ w = 0 := by
    constructor
    · intro h
      rw [← inv_mulVec_mulVec g w, h, Matrix.mulVec_zero]
    · intro h
      rw [h, Matrix.mulVec_zero]
  have h1 : ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈
      CFSG.Sporadic.Co1Block.certX ↔ w ∈ CFSG.Sporadic.Co1Block.certX := by
    constructor
    · intro h
      have := mulVec_mem_certX (Subgroup.inv_mem _ hg) h
      rwa [inv_mulVec_mulVec] at this
    · exact mulVec_mem_certX hg
  unfold typV
  by_cases hw : w = 0
  · rw [if_pos hw, if_pos (h0.2 hw)]
  · rw [if_neg hw, if_neg (fun h => hw (h0.1 h))]
    by_cases hx : w ∈ CFSG.Sporadic.Co1Block.certX
    · rw [if_pos hx, if_pos (h1.2 hx)]
    · rw [if_neg hx, if_neg (fun h => hx (h1.1 h))]

end Types


section Orbit

variable
  {cs : Array (Array ℕ)} {B : ℕ → Matrix (Fin 24) (Fin 24) (ZMod 2)}
  {H : Subgroup GL24} {base : List ℕ}

theorem mem_foldl_filter {α β : Type} (P : β → α → Bool) (l : List β) (L : List α) (x : α) :
    x ∈ l.foldl (fun cand c => cand.filter (P c)) L ↔ x ∈ L ∧ ∀ c ∈ l, P c x = true := by
  induction l generalizing L with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih, List.mem_filter]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_candList (xs : Std.HashSet ℕ) (cs : Array (Array ℕ)) (base : List ℕ) (u : ℕ)
    (conds : List Cond) (x : ℕ) :
    x ∈ candList xs cs base u conds ↔ x ∈ certVecs.toList ∧ ∀ c ∈ conds,
      typN xs (combN cs c.1 (fN cs base c.2) x) = typN xs (combN cs c.1 (fN cs base c.2) u) := by
  unfold candList
  rw [mem_foldl_filter (fun c x => typN xs (combN cs c.1 (fN cs base c.2) x) ==
      typN xs (combN cs c.1 (fN cs base c.2) u)) conds certVecs.toList x]
  simp only [beq_iff_eq]

theorem getD_take_zero (base : List ℕ) (i j : ℕ) :
    (base.take i).getD j 0 = if j < i then base.getD j 0 else 0 := by
  by_cases h : j < i
  · rw [if_pos h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]
  · rw [if_neg h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem mem_candList_of_mem_vCh (hHA : H ≤ GA)
    (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    (hlt : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24)
    (hcomm : ∀ g ∈ H, ∀ a, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * B a =
      B a * ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    {i : ℕ} {g : GL24} (hg : g ∈ vCh H base i) (u y : ℕ) (hy : y ∈ certVecs.toList)
    (hyu : toVecD 24 y = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 u)
    (conds : List Cond) : y ∈ candList (xsSet ()) cs (base.take i) u conds := by
  rw [mem_candList]
  refine ⟨hy, fun c _ => ?_⟩
  have hgH : g ∈ H := vCh_le i hg
  have hM := hcomm g hgH
  have hF : ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (fN cs (base.take i) c.2) = toVecD 24 (fN cs (base.take i) c.2) := by
    refine fN_fixed hB hM _ _ (fun s _ => ?_)
    rw [getD_take_zero]
    by_cases h : s.1 < i
    · rw [if_pos h]
      exact fix_of_mem_vCh hg h
    · rw [if_neg h, toVecD_zero, Matrix.mulVec_zero]
  have hF' := fN_lt hlt (base.take i) c.2
  have h1 := combN_equiv hB hM c.1 hF hyu
  rw [typN_eq (combN_lt hlt c.1 hF' y), typN_eq (combN_lt hlt c.1 hF' u), h1]
  exact typV_mulVec (hHA hgH) _

theorem card_orbit_le_candList (hHA : H ≤ GA)
    (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    (hlt : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24)
    (hcomm : ∀ g ∈ H, ∀ a, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * B a =
      B a * ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (i : ℕ) (hu : base.getD i 0 ∈ certVecs.toList) (conds : List Cond) :
    Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0))) ≤
      (candList (xsSet ()) cs (base.take i) (base.getD i 0) conds).length := by
  set Lc := candList (xsSet ()) cs (base.take i) (base.getD i 0) conds with hLc
  have hsub : (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)) : Set Vec24) ⊆
      toVecD 24 '' ((Lc.toFinset : Finset ℕ) : Set ℕ) := by
    intro w hw
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hw
    have hgw : g • toVecD 24 (base.getD i 0) =
        ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ toVecD 24 (base.getD i 0) := by
      rw [Subgroup.smul_def, vecAct_smul]
    obtain ⟨y, hy, hyw⟩ := exists_mem_of_certX
      (mulVec_mem_certX (hHA (vCh_le i g.2)) (toVecD_mem_certX hu))
    refine ⟨y, ?_, by rw [hyw, hgw]⟩
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact mem_candList_of_mem_vCh hHA hB hlt hcomm g.2 _ y hy hyw conds
  calc Nat.card (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)))
      = Set.ncard (MulAction.orbit (vCh H base i) (toVecD 24 (base.getD i 0)) : Set Vec24) :=
        Nat.card_coe_set_eq _
    _ ≤ Set.ncard (toVecD 24 '' ((Lc.toFinset : Finset ℕ) : Set ℕ)) :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ Set.ncard (((Lc.toFinset : Finset ℕ)) : Set ℕ) :=
        Set.ncard_image_le (Finset.finite_toSet _)
    _ = Lc.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Lc.length := List.toFinset_card_le _

end Orbit


section Final

variable
  {cs : Array (Array ℕ)} {B : ℕ → Matrix (Fin 24) (Fin 24) (ZMod 2)}
  {H : Subgroup GL24} {base : List ℕ}

theorem fixed_vecMulN {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (R : Array ℕ)
    (hR : ∀ k < 24, M *ᵥ toVecD 24 (R[k]?.getD 0) = toVecD 24 (R[k]?.getD 0)) (c : ℕ) :
    M *ᵥ toVecD 24 (vecMulN 24 R c) = toVecD 24 (vecMulN 24 R c) := by
  unfold vecMulN
  have key : ∀ (l : List ℕ), (∀ j ∈ l, j < 24) → ∀ acc : ℕ,
      M *ᵥ toVecD 24 acc = toVecD 24 acc →
      M *ᵥ toVecD 24 (l.foldl (fun acc j => if c.testBit j then acc ^^^ (R[j]?.getD 0) else acc)
        acc) = toVecD 24 (l.foldl
          (fun acc j => if c.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc) := by
    intro l
    induction l with
    | nil => exact fun _ acc h => h
    | cons j l ih =>
      intro hl acc h
      rw [List.foldl_cons]
      refine ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) _ ?_
      split_ifs
      · rw [toVecD_xor, Matrix.mulVec_add, h, hR j (hl j List.mem_cons_self)]
      · exact h
  exact key _ (fun j hj => List.mem_range.1 hj) 0 (by rw [toVecD_zero, Matrix.mulVec_zero])

theorem toVecD_shiftLeft24 (i : Fin 24) : toVecD 24 (1 <<< (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem getD_slot_array (span : List (ℕ × ℕ)) (f : ℕ × ℕ → ℕ) {k : ℕ} (hk : k < span.length) :
    (span.map f).toArray[k]?.getD 0 = f span[k] := by
  simp [hk]

theorem eq_one_of_fix_span
    (hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v))
    {g : GL24}
    (hM : ∀ a, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * B a =
      B a * ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (hfix : ∀ j < base.length, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (base.getD j 0) = toVecD 24 (base.getD j 0))
    {span : List (ℕ × ℕ)} {comb : List ℕ} (hs : span.length = 24)
    (hsj : ∀ s ∈ span, s.1 < base.length)
    (hspan : ∀ l < 24,
      vecMulN 24 (span.map (slotN cs base)).toArray (comb.getD l 0) = 1 <<< l) : g = 1 := by
  have hR : ∀ k < 24, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 ((span.map (slotN cs base)).toArray[k]?.getD 0) =
        toVecD 24 ((span.map (slotN cs base)).toArray[k]?.getD 0) := by
    intro k hk
    have hk' : k < span.length := by omega
    rw [getD_slot_array span _ hk']
    have hmem := List.getElem_mem hk'
    rw [toVecD_slotN hB, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hfix _ (hsj _ hmem)]
  apply Units.ext
  rw [Units.val_one]
  apply Matrix.ext_of_mulVec_single
  intro l
  rw [Matrix.one_mulVec, ← toVecD_shiftLeft24 l, ← hspan l l.2]
  exact fixed_vecMulN _ hR _

theorem spanOK_spec {nb : ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : spanOK cs nb base span comb = true) :
    span.length = 24 ∧ comb.length = 24 ∧ (∀ s ∈ span, s.1 < base.length ∧ s.2 < nb) ∧
      ∀ l < 24, vecMulN 24 (span.map (slotN cs base)).toArray (comb.getD l 0) = 1 <<< l := by
  unfold spanOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem boundOK_spec {nb : ℕ} {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)}
    {comb : List ℕ} (h : boundOK cs nb base conds cnts span comb = true) :
    cs.size = nb ∧ conds.length = base.length ∧ cnts.length = base.length ∧
      (∀ i < base.length, base.getD i 0 ∈ certVecs.toList ∧
        (candList (xsSet ()) cs (base.take i) (base.getD i 0) (conds.getD i [])).length ≤
          cnts.getD i 0) ∧ spanOK cs nb base span comb = true := by
  unfold boundOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, h5⟩
  have := h4 i hi
  unfold lvlOK at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨contains_xs.1 this.1, this.2⟩

theorem prod_range_getD (l : List ℕ) : ∏ i ∈ Finset.range l.length, l.getD i 0 = l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.prod_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    exact mul_comm _ _

theorem cs_getD_of_le {nb : ℕ} (hcs : cs.size = nb) {a : ℕ} (ha : nb ≤ a) :
    cs.getD a #[] = #[] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
  rfl

theorem toVecD_vecMulN_empty (v : ℕ) : toVecD 24 (vecMulN 24 #[] v) = 0 := by
  unfold vecMulN
  have key : ∀ l : List ℕ, ∀ acc : ℕ, acc = 0 →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (#[] : Array ℕ)[j]?.getD 0 else acc)
        acc = 0 := by
    intro l
    induction l with
    | nil => exact fun acc h => h
    | cons j l ih =>
      intro acc h
      rw [List.foldl_cons]
      refine ih _ ?_
      split_ifs <;> simp [h]
  rw [key _ 0 rfl, toVecD_zero]

theorem card_le_of_boundOK (hHA : H ≤ GA) {nb : ℕ} {β : ℕ → GL24}
    (hcs : ∀ a < nb, ActsBy (β a) (cs.getD a #[]))
    (hcl : ∀ (a j : ℕ), (cs.getD a #[])[j]?.getD 0 < 2 ^ 24)
    (hcomm : ∀ g ∈ H, ∀ a < nb, g * β a = β a * g)
    {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOK cs nb base conds cnts span comb = true) : Nat.card H ≤ cnts.prod := by
  obtain ⟨hsz, -, hcnt, hlev, hspanOK⟩ := boundOK_spec h
  obtain ⟨hs24, -, hspj, hspan⟩ := spanOK_spec hspanOK
  let B : ℕ → Matrix (Fin 24) (Fin 24) (ZMod 2) :=
    fun a => if a < nb then ((β a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) else 0
  have hB : ∀ a v, B a *ᵥ toVecD 24 v = toVecD 24 (vecMulN 24 (cs.getD a #[]) v) := by
    intro a v
    by_cases ha : a < nb
    · simp only [B, if_pos ha]
      exact hcs a ha v
    · simp only [B, if_neg ha]
      rw [cs_getD_of_le hsz (by omega), toVecD_vecMulN_empty, Matrix.zero_mulVec]
  have hcB : ∀ g ∈ H, ∀ a, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) * B a =
      B a * ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    intro g hg a
    by_cases ha : a < nb
    · simp only [B, if_pos ha]
      rw [← Units.val_mul, ← Units.val_mul, hcomm g hg a ha]
    · simp only [B, if_neg ha, Matrix.mul_zero, Matrix.zero_mul]
  have key := card_le_prod_of_orbit_bound (H := H) (base := base) (fun i => cnts.getD i 0)
    (fun i hi => le_trans (card_orbit_le_candList hHA hB hcl hcB i (hlev i hi).1 (conds.getD i []))
      (hlev i hi).2)
    (fun g hg => eq_one_of_fix_span hB (hcB g (vCh_le _ hg))
      (fun j hj => fix_of_mem_vCh hg hj) hs24 (fun s hs => (hspj s hs).1) hspan)
  rwa [← hcnt, prod_range_getD] at key

theorem colsOf_getD {rs : List Native.Rows} {a : ℕ} (ha : a < rs.length) :
    (colsOf rs).getD a #[] = transposeRows 24 (rs.getD a (Native.one ())) := by
  simp [colsOf, Array.getD, ha, List.getD_eq_getElem]

theorem colsOf_getD_of_le {rs : List Native.Rows} {a : ℕ} (ha : rs.length ≤ a) :
    (colsOf rs).getD a #[] = #[] := by
  simp [colsOf, Array.getD, not_lt.2 ha]

theorem card_le_of_listBound {rs : List Native.Rows} {βs : List GL24} (hr : List.Forall₂ MRep rs βs)
    {H : Subgroup GL24} (hHA : H ≤ GA) (hcomm : ∀ g ∈ H, ∀ β ∈ βs, g * β = β * g) {nb : ℕ}
    (hnb : rs.length = nb) {base : List ℕ} {conds : List (List Cond)} {cnts : List ℕ}
    {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOK (colsOf rs) nb base conds cnts span comb = true) : Nat.card H ≤ cnts.prod := by
  subst hnb
  have hlen : rs.length = βs.length := hr.length_eq
  refine card_le_of_boundOK (β := fun a => βs.getD a 1) hHA ?_ ?_ ?_ h
  · intro a ha
    rw [colsOf_getD ha]
    exact (getD_rep hr MRep.one a).actsBy
  · intro a j
    by_cases ha : a < rs.length
    · rw [colsOf_getD ha]
      exact CFSG.Sporadic.Co1.Module.transposeRows_lt _ j
    · rw [colsOf_getD_of_le (not_lt.1 ha)]
      simp
  · intro g hg a ha
    refine hcomm g hg _ ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

theorem comm_pow_aux {G : Type} [Group G] {g k : G} (h : g * k = k * g) (a : ℕ) :
    g * k ^ a = k ^ a * g := by
  induction a with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem card_centralizer_le_of_powBound {k : GL24} {kR : Native.Rows} (rk : MRep kR k)
    {base : List ℕ} {conds : List (List Cond)} {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : boundOK (colsOf (powList kR 5)) 5 base conds cnts span comb = true) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set GL24) ⊓ GA) ≤ cnts.prod := by
  have hr : List.Forall₂ MRep (powList kR 5) ((List.range 5).map fun a => k ^ a) := by
    unfold powList
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun a _ => ?_
    exact rk.pow a
  have hlen : (powList kR 5).length = 5 := by simp [powList]
  have hcomm : ∀ g ∈ Subgroup.centralizer ({k} : Set GL24) ⊓ GA,
      ∀ β ∈ (List.range 5).map (fun a => k ^ a), g * β = β * g := by
    intro g hg β hβ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hβ
    have h0 := (Subgroup.mem_inf.1 hg).1
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 h0
    exact comm_pow_aux h1 a
  exact card_le_of_listBound hr inf_le_right hcomm hlen h

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1

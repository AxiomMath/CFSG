module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

namespace Clauses

theorem fst_apply_of_mem_centralizer {g : Perm Pt}
    (hg : g ∈ Subgroup.centralizer (sylowT : Set (Perm Pt))) (i : ZMod 3) (z : ZMod 5) :
    (g (i, z)).1 = i := by
  rw [Subgroup.mem_centralizer_iff] at hg
  by_contra hne
  have h := congrArg (fun σ : Perm Pt => (σ (i, z)).2)
    (hg (shiftPerm (Pi.single (g (i, z)).1 1)) (shiftPerm_mem_sylowT _))
  simp [Ne.symm hne] at h
  exact absurd h (by decide)

end Clauses

theorem mem_sylowT_of_mem_centralizer {g : Perm Pt}
    (hg : g ∈ Subgroup.centralizer (sylowT : Set (Perm Pt))) : g ∈ sylowT := by
  have h1 := Clauses.fst_apply_of_mem_centralizer hg
  rw [Subgroup.mem_centralizer_iff] at hg
  have h2 : ∀ i z, (g (i, z + 1)).2 = (g (i, z)).2 + 1 := by
    intro i z
    have h := congrArg (fun σ : Perm Pt => (σ (i, z)).2)
      (hg (shiftPerm (Pi.single i 1)) (shiftPerm_mem_sylowT _))
    simpa [h1] using h.symm
  have h3 : ∀ i z, (g (i, z)).2 = (g (i, 0)).2 + z := by
    intro i z
    have key : ∀ n : ℕ, (g (i, (n : ZMod 5))).2 = (g (i, 0)).2 + n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ, h2, ih]; ring
    simpa using key z.val
  refine mem_sylowT_iff.2 ⟨fun i => (g (i, 0)).2, ?_⟩
  ext ⟨i, z⟩
  · simp [h1]
  · rw [h3 i z]
    simp [add_comm]

namespace Clauses

theorem eq_or_eq_or_eq_of_cyc3_apply_ne {i : ZMod 3} {a b c : ZMod 5} {q : Pt}
    (h : cyc3 i a b c q ≠ q) : q = (i, a) ∨ q = (i, b) ∨ q = (i, c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply h
  simp [cyc3, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]

theorem cyc3_apply_left {i : ZMod 3} {a b c : ZMod 5} (hac : a ≠ c) (hbc : b ≠ c) :
    cyc3 i a b c (i, a) = (i, c) := by
  have h1 : ((i, c) : Pt) ≠ (i, a) := fun h => hac (congrArg Prod.snd h).symm
  have h2 : ((i, c) : Pt) ≠ (i, b) := fun h => hbc (congrArg Prod.snd h).symm
  simp [cyc3, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]

theorem apply_ne_of_commute {g x : Perm Pt} (h : g * x = x * g) {p : Pt} (hp : x p ≠ p) :
    x (g p) ≠ g p := by
  intro hx
  apply hp
  apply g.injective
  have h1 : g (x p) = x (g p) := by
    simpa [Perm.mul_apply] using congrArg (fun σ : Perm Pt => σ p) h
  rw [h1, hx]

theorem zmod_five_aux : ∀ z w : ZMod 5, (w = z ∨ w = z + 1 ∨ w = z + 2) →
    (w = z ∨ w = z + 3 ∨ w = z + 4) → w = z := by
  decide

theorem zmod_five_ne : ∀ z : ZMod 5, z ≠ z + 1 ∧ z ≠ z + 2 ∧ z + 1 ≠ z + 2 ∧ z ≠ z + 3 ∧
    z ≠ z + 4 ∧ z + 3 ≠ z + 4 := by
  decide

end Clauses

theorem eq_one_of_forall_commute_blockAlt {g : Perm Pt}
    (h : ∀ i, ∀ x ∈ blockAlt i, g * x = x * g) : g = 1 := by
  refine Equiv.ext fun p => ?_
  obtain ⟨i, z⟩ := p
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := Clauses.zmod_five_ne z
  have hx1 := cyc3_mem_blockAlt i n1 n2 n3
  have hx2 := cyc3_mem_blockAlt i n4 n5 n6
  have hp1 : cyc3 i z (z + 1) (z + 2) (i, z) ≠ (i, z) := by
    rw [Clauses.cyc3_apply_left n2 n3]
    exact fun h' => n2 (by simpa using congrArg Prod.snd h')
  have hp2 : cyc3 i z (z + 3) (z + 4) (i, z) ≠ (i, z) := by
    rw [Clauses.cyc3_apply_left n5 n6]
    exact fun h' => n5 (by simpa using congrArg Prod.snd h')
  have hq1 := Clauses.eq_or_eq_or_eq_of_cyc3_apply_ne
    (Clauses.apply_ne_of_commute (h i _ hx1) hp1)
  have hq2 := Clauses.eq_or_eq_or_eq_of_cyc3_apply_ne
    (Clauses.apply_ne_of_commute (h i _ hx2) hp2)
  have hfst : (g (i, z)).1 = i := by
    rcases hq1 with h' | h' | h' <;> simp [h']
  have hsnd : (g (i, z)).2 = z := by
    refine Clauses.zmod_five_aux z _ ?_ ?_
    · rcases hq1 with h' | h' | h' <;> simp [h']
    · rcases hq2 with h' | h' | h' <;> simp [h']
  exact Prod.ext hfst hsnd

namespace Clauses

theorem conj_mem_blockAlt_of_mem {j k : ZMod 3} {a h : Perm Pt} (ha : a ∈ blockAlt k)
    (hh : h ∈ blockAlt j) : a * h * a⁻¹ ∈ blockAlt j := by
  by_cases hkj : k = j
  · subst hkj
    exact mul_mem (mul_mem ha hh) (inv_mem ha)
  · rw [blockAlt_commute hkj ha hh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh

theorem conj_mul_mem_blockAlt {j k l : ZMod 3} {a b h : Perm Pt} (ha : a ∈ blockAlt k)
    (hb : b ∈ blockAlt l) (hh : h ∈ blockAlt j) : a * b * h * (a * b)⁻¹ ∈ blockAlt j := by
  simpa [mul_assoc] using conj_mem_blockAlt_of_mem ha (conj_mem_blockAlt_of_mem hb hh)

theorem commutator_mem {M W : Subgroup (Perm Pt)}
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) {x y : Perm Pt} (hx : x ∈ W) (hy : y ∈ M) :
    x * y * x⁻¹ * y⁻¹ ∈ W := by
  have h1 : y * x⁻¹ * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hN hy) x⁻¹).1 (W.inv_mem hx)
  simpa [mul_assoc] using W.mul_mem hx h1

theorem commutator_ne_one {x y : Perm Pt} (h : x * y ≠ y * x) : x * y * x⁻¹ * y⁻¹ ≠ 1 :=
  fun h0 => h (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h0))

theorem exists_mem_inf_blockAlt_ne_one {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hMW : M ≤ wr) (hWM : W ≤ M) (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt)))
    (hW : W ≠ ⊥) : ∃ j, ∃ d ∈ blockAlt j, d ∈ W ∧ d ≠ 1 := by
  rw [Ne, Subgroup.eq_bot_iff_forall] at hW
  push Not at hW
  obtain ⟨w, hw, hw1⟩ := hW
  have h1 : ¬ ∀ i, ∀ x ∈ blockAlt i, w * x = x * w :=
    fun h => hw1 (eq_one_of_forall_commute_blockAlt h)
  push Not at h1
  obtain ⟨i, h, hh, hwh⟩ := h1
  have hcW : w * h * w⁻¹ * h⁻¹ ∈ W := commutator_mem hN hw (hA i hh)
  have hc1 : w * h * w⁻¹ * h⁻¹ ≠ 1 := commutator_ne_one hwh
  have hcA : w * h * w⁻¹ ∈ blockAlt (blk w i) := conj_mem_blockAlt (hMW (hWM hw)) hh
  have h2 : ¬ ∀ j, ∀ x ∈ blockAlt j, (w * h * w⁻¹ * h⁻¹) * x = x * (w * h * w⁻¹ * h⁻¹) :=
    fun h' => hc1 (eq_one_of_forall_commute_blockAlt h')
  push Not at h2
  obtain ⟨j, h', hh', hch⟩ := h2
  refine ⟨j, (w * h * w⁻¹ * h⁻¹) * h' * (w * h * w⁻¹ * h⁻¹)⁻¹ * h'⁻¹, ?_, ?_, ?_⟩
  · exact mul_mem (conj_mul_mem_blockAlt hcA (inv_mem hh) hh') (inv_mem hh')
  · exact commutator_mem hN hcW (hA j hh')
  · exact commutator_ne_one hch

theorem blockAlt_le_of_mem_inf {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) {j : ZMod 3} {d : Perm Pt}
    (hd : d ∈ blockAlt j) (hdW : d ∈ W) (hd1 : d ≠ 1) : blockAlt j ≤ W := by
  have hle : W ⊓ blockAlt j ≤ blockAlt j := inf_le_right
  have : ((W ⊓ blockAlt j).subgroupOf (blockAlt j)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro n k hn hk
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hN (hA j hk)) n).1 hn.1,
      (blockAlt j).mul_mem ((blockAlt j).mul_mem hk hn.2) ((blockAlt j).inv_mem hk)⟩
  have := isSimpleGroup_blockAlt j
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((W ⊓ blockAlt j).subgroupOf (blockAlt j)) with h | h
  · have hmem : (⟨d, hd⟩ : blockAlt j) ∈ (W ⊓ blockAlt j).subgroupOf (blockAlt j) :=
      Subgroup.mem_subgroupOf.2 ⟨hdW, hd⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact absurd (congrArg Subtype.val hmem) hd1
  · exact (Subgroup.subgroupOf_eq_top.1 h).trans inf_le_left

theorem blockAlt_succ_le {M W : Subgroup (Perm Pt)} (hτ : blockShift ∈ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) {j : ZMod 3} (h : blockAlt j ≤ W) :
    blockAlt (j + 1) ≤ W := by
  intro x hx
  have h1 : blockShift⁻¹ * x * blockShift⁻¹⁻¹ ∈ blockAlt (blk blockShift⁻¹ (j + 1)) :=
    conj_mem_blockAlt (wr.inv_mem blockShift_mem_wr) hx
  have h2 : blk blockShift⁻¹ (j + 1) = j := by simp [blk, Perm.inv_def]
  rw [h2, inv_inv] at h1
  have h3 := (Subgroup.mem_normalizer_iff.1 (hN hτ) _).1 (h h1)
  simpa [mul_assoc] using h3

end Clauses

theorem blockAlt_le_of_ne_bot {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (hW : W ≠ ⊥) (i : ZMod 3) :
    blockAlt i ≤ W := by
  obtain ⟨j, d, hd, hdW, hd1⟩ := Clauses.exists_mem_inf_blockAlt_ne_one hA hMW hWM hN hW
  have h0 := Clauses.blockAlt_le_of_mem_inf hA hN hd hdW hd1
  have h1 := Clauses.blockAlt_succ_le hτ hN h0
  have h2 := Clauses.blockAlt_succ_le hτ hN h1
  rcases (by decide : ∀ j i : ZMod 3, i = j ∨ i = j + 1 ∨ i = j + 1 + 1) j i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem eq_bot_of_coprime {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (hW : Nat.Coprime 5 (Nat.card W)) :
    W = ⊥ := by
  by_contra hbot
  have h1 := Subgroup.card_dvd_of_le (blockAlt_le_of_ne_bot hA hτ hMW hWM hN hbot 0)
  rw [card_blockAlt] at h1
  have h2 : 5 ∣ Nat.card W := (by norm_num : 5 ∣ 60).trans h1
  exact absurd (hW.eq_one_of_dvd h2) (by norm_num)

theorem eq_bot_or_sylowT_le {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) : W = ⊥ ∨ sylowT ≤ W := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · exact Or.inr (sylowT_le_iSup_blockAlt.trans
      (iSup_le fun i => blockAlt_le_of_ne_bot hA hτ hMW hWM hN hbot i))

theorem inf_centralizer_sylowT_le {M : Subgroup (Perm Pt)} :
    M ⊓ Subgroup.centralizer (sylowT : Set (Perm Pt)) ≤ sylowT :=
  fun _ hg => mem_sylowT_of_mem_centralizer hg.2

theorem eq_bot_of_isPGroup {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (hW : IsPGroup 5 W) : W = ⊥ := by
  by_contra hbot
  have hp : IsPGroup 5 (blockAlt 0) := hW.to_le (blockAlt_le_of_ne_bot hA hτ hMW hWM hN hbot 0)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [card_blockAlt] at hn
  have h3 : 3 ∣ 5 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem exists_normal_closure {M W : Subgroup (Perm Pt)} (hA : ∀ i, blockAlt i ≤ M)
    (hτ : blockShift ∈ M) (hMW : M ≤ wr) (hWM : W ≤ M)
    (hN : M ≤ Subgroup.normalizer (W : Set (Perm Pt))) (hT : sylowT ≤ W) :
    ∃ J : Fin 3 → Subgroup (Perm Pt),
      (∀ i, J i ≤ W ∧ Nonempty (J i ≃* alternatingGroup (Fin 5))) ∧
      (∀ i j, i ≠ j → ⁅J i, J j⁆ = ⊥) ∧ sylowT ≤ ⨆ i, J i := by
  have hW : W ≠ ⊥ := by
    rintro rfl
    have h1 : sylowT = ⊥ := le_bot_iff.1 hT
    have h2 := card_sylowT
    rw [h1, Subgroup.card_bot] at h2
    norm_num at h2
  refine ⟨fun i => blockAlt i, fun i => ⟨blockAlt_le_of_ne_bot hA hτ hMW hWM hN hW i,
    ⟨blockAltEquiv i⟩⟩, fun i j hij => ?_, sylowT_le_iSup_blockAlt⟩
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact blockAlt_commute hij ha hb

end CFSG.AGLEmbedding.A15Local

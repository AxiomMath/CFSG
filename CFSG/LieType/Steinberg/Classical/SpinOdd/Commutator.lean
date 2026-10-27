module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Basic
public import CFSG.LieType.Steinberg.Classical.OrthogonalRoots

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

open _root_.Classical in
@[expose] def commCe (e f : Fin n → ℤ) (p : ℕ × ℕ) : ℤ :=
  if p = (1, 1) then
    (if IsLong e ∧ IsLong f then chainSign e f
    else if IsShort e ∧ IsShort f then shortSign e f
    else if IsLong e then mixedSign₁ e f
    else -mixedSign₁ f e)
  else if p = (1, 2) then mixedSign₂ e f
  else if p = (2, 1) then -mixedSign₂ f e
  else 1

@[expose] def commC (α β : Fin n → ℤ) (p : ℕ × ℕ) : ℤ := commCe (toStdB n α) (toStdB n β) p

theorem natAbs_neg_eq_one_or_eq_two {z : ℤ} (h : z.natAbs = 1 ∨ z.natAbs = 2) :
    (-z).natAbs = 1 ∨ (-z).natAbs = 2 := by
  rwa [Int.natAbs_neg]

theorem natAbs_eq_one_or_eq_two_of_sign {z : ℤ} (h : z = 1 ∨ z = -1) :
    z.natAbs = 1 ∨ z.natAbs = 2 := by
  rcases h with rfl | rfl <;> exact Or.inl rfl

theorem commCe_natAbs (e f : Fin n → ℤ) (p : ℕ × ℕ) :
    (commCe e f p).natAbs = 1 ∨ (commCe e f p).natAbs = 2 := by
  unfold commCe
  split_ifs
  · exact natAbs_eq_one_or_eq_two_of_sign (chainSign_eq_one_or_eq_neg_one e f)
  · exact (natAbs_shortSign e f).symm
  · exact natAbs_eq_one_or_eq_two_of_sign (mixedSign₁_eq_one_or_eq_neg_one e f)
  · exact natAbs_neg_eq_one_or_eq_two
      (natAbs_eq_one_or_eq_two_of_sign (mixedSign₁_eq_one_or_eq_neg_one f e))
  · exact natAbs_eq_one_or_eq_two_of_sign (mixedSign₂_eq_one_or_eq_neg_one e f)
  · exact natAbs_neg_eq_one_or_eq_two
      (natAbs_eq_one_or_eq_two_of_sign (mixedSign₂_eq_one_or_eq_neg_one f e))
  · exact Or.inl rfl

theorem commC_natAbs (α β : Fin n → ℤ) (p : ℕ × ℕ) :
    (commC α β p).natAbs = 1 ∨ (commC α β p).natAbs = 2 :=
  commCe_natAbs _ _ p

theorem commC_natAbs_mem (α : Fin n → ℤ) (_ : α ∈ (Φ n K).roots) (β : Fin n → ℤ)
    (_ : β ∈ (Φ n K).roots) (p : ℕ × ℕ) (_ : p ∈ expPairs (Φ n K) α β) :
    (commC α β p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  rcases commC_natAbs α β p with h | h <;> simp [h]

theorem commCe_chain {e f : Fin n → ℤ} (he : IsLong e) (hf : IsLong f) :
    commCe e f (1, 1) = chainSign e f := by
  rw [commCe, ite_eq_left rfl, ite_eq_left ⟨he, hf⟩]

theorem commCe_short {e f : Fin n → ℤ} (he : IsShort e) (hf : IsShort f) :
    commCe e f (1, 1) = shortSign e f := by
  rw [commCe, ite_eq_left rfl, ite_eq_right fun h => he.not_isLong h.1, ite_eq_left ⟨he, hf⟩]

theorem commCe_mixed {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep e f) :
    commCe e f (1, 1) = mixedSign₁ e f ∧ commCe e f (1, 2) = mixedSign₂ e f := by
  have he := hp.isLong
  have hf := hp.isShort
  refine ⟨?_, ?_⟩
  · rw [commCe, ite_eq_left rfl, ite_eq_right fun h => hf.not_isLong h.2,
      ite_eq_right fun h => h.1.not_isLong he, ite_eq_left he]
  · rw [commCe, ite_eq_right (by decide), ite_eq_left rfl]

theorem commCe_mixed_swap {p : PairRep n} {e f : Fin n → ℤ} (hp : p.IsMixedRep f e) :
    commCe e f (1, 1) = -mixedSign₁ f e ∧ commCe e f (2, 1) = -mixedSign₂ f e := by
  have hf := hp.isLong
  have he := hp.isShort
  refine ⟨?_, ?_⟩
  · rw [commCe, ite_eq_left rfl, ite_eq_right fun h => he.not_isLong h.1,
      ite_eq_right fun h => h.2.not_isLong hf, ite_eq_right he.not_isLong]
  · rw [commCe, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

section Products

variable {ι M : Type*} [Monoid M]

theorem prod_map_of_forall_notMem {L : List ι} (h : ∀ p, p ∉ L) (g : ι → M) :
    (L.map g).prod = 1 := by
  rw [List.eq_nil_iff_forall_not_mem.mpr h, List.map_nil, List.prod_nil]

theorem prod_map_of_mem_iff_eq {L : List ι} (hL : L.Nodup) {a : ι} (h : ∀ p, p ∈ L ↔ p = a)
    (g : ι → M) : (L.map g).prod = g a := by
  have hperm : L.Perm [a] :=
    (List.perm_ext_iff_of_nodup hL (List.nodup_singleton a)).mpr fun p => by
      rw [h, List.mem_singleton]
  rw [List.perm_singleton.mp hperm, List.map_singleton, List.prod_singleton]

theorem prod_map_of_mem_iff_eq_or_eq {L : List ι} (hL : L.Nodup) {a b : ι} (hab : a ≠ b)
    (h : ∀ p, p ∈ L ↔ p = a ∨ p = b) (g : ι → M) (hc : Commute (g a) (g b)) :
    (L.map g).prod = g a * g b := by
  have hperm : L.Perm [a, b] :=
    (List.perm_ext_iff_of_nodup hL (by simp [hab])).mpr fun p => by simp [h]
  rcases List.perm_pair.mp hperm with rfl | rfl
  · simp
  · simpa using hc.eq.symm

end Products

theorem toStdB_nsmul' (p : ℕ) (v : Fin n → ℤ) : toStdB n (p • v) = p • toStdB n v := by
  rw [← natCast_zsmul, toStdB_smul, natCast_zsmul]

theorem toStdB_comb (p q : ℕ) (α β : Fin n → ℤ) :
    toStdB n (p • α + q • β) = p • toStdB n α + q • toStdB n β := by
  rw [toStdB_add, toStdB_nsmul', toStdB_nsmul']

theorem mem_list_iff (O : CommOrder (Φ n K)) {α β : Fin n → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanB n) ∅) (hβ : β ∈ roots (isFiniteType_cartanB n) ∅)
    (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ O.list α β ↔
      (p = (1, 1) ∧ IsRootVec (toStdB n α + toStdB n β)) ∨
      (p = (1, 2) ∧ IsRootVec (toStdB n α + 2 • toStdB n β)) ∨
      (p = (2, 1) ∧ IsRootVec (2 • toStdB n α + toStdB n β)) := by
  rw [O.mem_iff α hα β hβ hαβ p, Orthogonal.mem_expPairs_B (Φ_roots (K := K)) hα hβ hαβ p,
    Φ_roots, mem_roots_iff, toStdB_comb]
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · exact Or.inl ⟨rfl, by simpa using h⟩
    · exact Or.inr (Or.inl ⟨rfl, by simpa using h⟩)
    · exact Or.inr (Or.inr ⟨rfl, by simpa using h⟩)
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨Or.inl rfl, by simpa using h⟩
    · exact ⟨Or.inr (Or.inl rfl), by simpa using h⟩
    · exact ⟨Or.inr (Or.inr rfl), by simpa using h⟩

theorem iff_of_one_one {A B C : Prop} (hA : A) (hB : ¬B) (hC : ¬C) (q : ℕ × ℕ) :
    (q = (1, 1) ∧ A ∨ q = (1, 2) ∧ B ∨ q = (2, 1) ∧ C) ↔ q = (1, 1) := by
  constructor
  · rintro (⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩)
    · rfl
    · exact absurd h hB
    · exact absurd h hC
  · rintro rfl
    exact Or.inl ⟨rfl, hA⟩

theorem iff_of_one_two {A B C : Prop} (hA : A) (hB : B) (hC : ¬C) (q : ℕ × ℕ) :
    (q = (1, 1) ∧ A ∨ q = (1, 2) ∧ B ∨ q = (2, 1) ∧ C) ↔ q = (1, 1) ∨ q = (1, 2) := by
  constructor
  · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, h⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd h hC
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hA⟩
    · exact Or.inr (Or.inl ⟨rfl, hB⟩)

theorem iff_of_two_one {A B C : Prop} (hA : A) (hB : ¬B) (hC : C) (q : ℕ × ℕ) :
    (q = (1, 1) ∧ A ∨ q = (1, 2) ∧ B ∨ q = (2, 1) ∧ C) ↔ q = (1, 1) ∨ q = (2, 1) := by
  constructor
  · rintro (⟨rfl, -⟩ | ⟨-, h⟩ | ⟨rfl, -⟩)
    · exact Or.inl rfl
    · exact absurd h hB
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hA⟩
    · exact Or.inr (Or.inr ⟨rfl, hC⟩)

theorem commutatorFormula (O : CommOrder (Φ n K)) : CommutatorFormula (x n K) O commC := by
  intro α hα β hβ hαβ c d
  have he : IsRootVec (toStdB n α) := mem_roots_iff.mp hα
  have hf : IsRootVec (toStdB n β) := mem_roots_iff.mp hβ
  have hef : toStdB n α + toStdB n β ≠ 0 := fun h =>
    hαβ (toStdB_injective n (by rw [toStdB_add, h, toStdB_zero]))
  have hmem := mem_list_iff O hα hβ hαβ
  have hx : ∀ (p : ℕ × ℕ) (a : K), x n K (p.1 • α + p.2 • β) a =
      elt (oddFrame n K) (p.1 • toStdB n α + p.2 • toStdB n β) a := fun p a => by
    rw [x, toStdB_comb]
  simp only [hx]
  rw [x, x]
  rcases classify (oddFrame n K) he hf hef with ⟨hle, hlf, hl, h12, h21⟩ |
    ⟨⟨p, hp⟩, h12, h21⟩ | ⟨⟨p, hp⟩, h21⟩ | ⟨⟨p, hp⟩, h12⟩ | ⟨h11, h12, h21, hcomm⟩
  ·
    rw [prod_map_of_mem_iff_eq (O.nodup α β) (a := (1, 1)) (fun q => by
      rw [hmem]; exact iff_of_one_one (Or.inl hl) h12 h21 q)]
    simp only [one_smul, pow_one]
    rw [elt_of_isLong _ hle, elt_of_isLong _ hlf, elt_of_isLong _ hl,
      commutator_rootElt _ hle hlf hef hl, commC, commCe_chain hle hlf]
  ·
    have hes : IsShort (toStdB n α) := by
      rw [hp.2.1]
      exact isShort_single _ _
    have hfs : IsShort (toStdB n β) := by
      rw [hp.2.2]
      exact isShort_single _ _
    rw [prod_map_of_mem_iff_eq (O.nodup α β) (a := (1, 1)) (fun q => by
      rw [hmem]; exact iff_of_one_one (Or.inl hp.isLong_add) h12 h21 q)]
    simp only [one_smul, pow_one]
    rw [elt_of_isShort _ hes, elt_of_isShort _ hfs, elt_of_isLong _ hp.isLong_add,
      commutator_shortElt_shortElt _ hp, commC, commCe_short hes hfs]
  ·
    have h11 : IsRootVec (toStdB n α + toStdB n β) := Or.inr hp.isShort_add
    have h12 : IsRootVec (toStdB n α + 2 • toStdB n β) := Or.inl hp.isLong_add_two_nsmul
    rw [prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (1, 2)) (by decide)
      (fun q => by rw [hmem]; exact iff_of_one_two h11 h12 h21 q)]
    · simp only [one_smul, pow_one]
      obtain ⟨hc1, hc2⟩ := commCe_mixed hp
      rw [elt_of_isLong _ hp.isLong, elt_of_isShort _ hp.isShort,
        elt_of_isShort _ hp.isShort_add, elt_of_isLong _ hp.isLong_add_two_nsmul,
        commutator_rootElt_shortElt _ hp, commC, commC, hc1, hc2]
    · simp only [one_smul, pow_one]
      rw [elt_of_isShort _ hp.isShort_add, elt_of_isLong _ hp.isLong_add_two_nsmul]
      exact commute_shortElt_rootElt_of_isMixedRep _ hp _ _
  ·
    have h11 : IsRootVec (toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact Or.inr hp.isShort_add
    have h21 : IsRootVec (2 • toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact Or.inl hp.isLong_add_two_nsmul
    have hs1 : IsShort (toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact hp.isShort_add
    have hl2 : IsLong (2 • toStdB n α + toStdB n β) := by
      rw [add_comm]
      exact hp.isLong_add_two_nsmul
    rw [prod_map_of_mem_iff_eq_or_eq (O.nodup α β) (a := (1, 1)) (b := (2, 1)) (by decide)
      (fun q => by rw [hmem]; exact iff_of_two_one h11 h12 h21 q)]
    · simp only [one_smul, pow_one]
      obtain ⟨hc1, hc2⟩ := commCe_mixed_swap hp
      have hcomm := commute_shortElt_rootElt_of_isMixedRep (oddFrame n K) hp
        (((-mixedSign₁ (toStdB n β) (toStdB n α) : ℤ) : K) * c * d)
        (((-mixedSign₂ (toStdB n β) (toStdB n α) : ℤ) : K) * c ^ 2 * d)
      rw [add_comm (toStdB n β), add_comm (toStdB n β)] at hcomm
      rw [elt_of_isShort _ hp.isShort, elt_of_isLong _ hp.isLong, elt_of_isShort _ hs1,
        elt_of_isLong _ hl2, commC, commC, hc1, hc2, ← commutatorElement_inv,
        commutator_rootElt_shortElt _ hp, _root_.mul_inv_rev, ← shortElt_neg, ← rootElt_neg,
        add_comm (toStdB n β), add_comm (toStdB n β),
        show -((mixedSign₂ (toStdB n β) (toStdB n α) : K) * d * c ^ 2) =
          ((-mixedSign₂ (toStdB n β) (toStdB n α) : ℤ) : K) * c ^ 2 * d by push_cast; ring,
        show -((mixedSign₁ (toStdB n β) (toStdB n α) : K) * d * c) =
          ((-mixedSign₁ (toStdB n β) (toStdB n α) : ℤ) : K) * c * d by push_cast; ring]
      exact hcomm.eq.symm
    · simp only [one_smul, pow_one]
      rw [elt_of_isShort _ hs1, elt_of_isLong _ hl2, add_comm (toStdB n α),
        add_comm (2 • toStdB n α)]
      exact commute_shortElt_rootElt_of_isMixedRep _ hp _ _
  ·
    rw [prod_map_of_forall_notMem (fun q h => by
      rcases (hmem q).mp h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩
      · exact h11 h'
      · exact h12 h'
      · exact h21 h')]
    exact commutatorElement_eq_one_iff_commute.mpr (hcomm c d)

end CFSG.LieType.Steinberg.SpinOdd

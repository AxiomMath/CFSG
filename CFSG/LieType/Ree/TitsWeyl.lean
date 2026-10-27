module

public import CFSG.LieType.Ree.RelWeylRee

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem length_mul_simple_add_one {w : WeylGroup τ} {i : Fin τ.rank}
    (h : height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0) :
    (coxeterSystem τ).length (w * simple τ i) + 1 = (coxeterSystem τ).length w := by
  have hle : w • (Pi.single i 1 : Fin τ.rank → ℤ) ≤ 0 := fun k =>
    (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single τ i) w)).1 h k
  exact (coxeterSystem τ).isRightDescent_iff.1
    ((CFSG.LieType.RootSystem.isRightDescent_iff (isFiniteType_cartan τ) w i).2 hle)

@[expose] def DescentWord : WeylGroup τ → List (Fin τ.rank) → Prop
  | _, [] => True
  | w, j :: ω => height (w • (Pi.single j 1 : Fin τ.rank → ℤ)) < 0 ∧
      DescentWord (w * simple τ j) ω

theorem length_mul_wordProd_add : ∀ (ω : List (Fin τ.rank)) (w : WeylGroup τ),
    DescentWord w ω →
      (coxeterSystem τ).length (w * (coxeterSystem τ).wordProd ω) + ω.length =
        (coxeterSystem τ).length w
  | [], w, _ => by simp
  | j :: ω, w, ⟨hj, hω⟩ => by
    have h1 : (coxeterSystem τ).length (w * (coxeterSystem τ).simple j) + 1 =
        (coxeterSystem τ).length w := length_mul_simple_add_one hj
    have h2 : (coxeterSystem τ).length (w * (coxeterSystem τ).simple j *
        (coxeterSystem τ).wordProd ω) + ω.length =
        (coxeterSystem τ).length (w * (coxeterSystem τ).simple j) :=
      length_mul_wordProd_add ω (w * simple τ j) hω
    rw [CoxeterSystem.wordProd_cons, ← mul_assoc, List.length_cons]
    omega

variable (τ) in
@[expose] def prefixRoots : List (Fin τ.rank) → List (Fin τ.rank → ℤ)
  | [] => []
  | j :: ω => Pi.single j 1 :: (prefixRoots ω).map (reflect τ j)

theorem descentWord_of_prefixRoots : ∀ (ω : List (Fin τ.rank)) (w : WeylGroup τ),
    (∀ β ∈ prefixRoots τ ω, height (w • β) < 0) → DescentWord w ω
  | [], _, _ => trivial
  | j :: ω, w, h => ⟨h _ (List.mem_cons_self ..), descentWord_of_prefixRoots ω (w * simple τ j)
      fun β hβ => by
        rw [mul_smul, simple_smul]
        exact h _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hβ))⟩

theorem height_smul_eq_sum (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    height (w • v) = ∑ k, v k * height (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [← CFSG.LieType.RootSystem.sum_smul_single v]
  rw [Finset.smul_sum]
  simp only [smul_def, map_zsmul, height, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem height_smul_neg_of_support {w : WeylGroup τ} {J : Finset (Fin τ.rank)}
    (hw : ∀ j ∈ J, height (w • (Pi.single j 1 : Fin τ.rank → ℤ)) < 0)
    {β : Fin τ.rank → ℤ} (hsupp : ∀ k, k ∉ J → β k = 0) (hnn : ∀ k, 0 ≤ β k) (hne : β ≠ 0) :
    height (w • β) < 0 := by
  rw [height_smul_eq_sum]
  obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hkJ : k ∈ J := by
    by_contra h
    exact hk (hsupp k h)
  have hterm : ∀ l, β l * height (w • (Pi.single l 1 : Fin τ.rank → ℤ)) ≤ 0 := by
    intro l
    by_cases hl : l ∈ J
    · exact mul_nonpos_of_nonneg_of_nonpos (hnn l) (hw l hl).le
    · rw [hsupp l hl, zero_mul]
  exact Finset.sum_neg' (fun l _ => hterm l) ⟨k, Finset.mem_univ _,
    mul_neg_of_pos_of_neg (lt_of_le_of_ne (hnn k) (Ne.symm hk)) (hw k hkJ)⟩

end CFSG.LieType.Chevalley

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag)

noncomputable abbrev blockElt (i : Fin t.tag.rank) : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd (t.reeOrbitWord i)

theorem blockElt_mul_self (i : Fin t.tag.rank) : t.blockElt i * t.blockElt i = 1 := by
  rw [blockElt, ← CoxeterSystem.wordProd_append]
  refine ext_single fun k => ?_
  rw [wordProd_smul, one_smul]
  revert i k
  cases t <;> decide +kernel

theorem blockCheck : ∀ i : Fin t.tag.rank, ∀ β ∈ prefixRoots t.tag (t.reeOrbitWord i),
    (∀ k, k ≠ i → k ≠ t.perm i → β k = 0) ∧ (∀ k, 0 ≤ β k) ∧ β ≠ 0 := by
  cases t <;> decide +kernel

theorem reeOrbitWord_ne_nil (i : Fin t.tag.rank) : 0 < (t.reeOrbitWord i).length := by
  revert i
  cases t <;> decide

variable {t}

theorem height_smul_perm_neg {w : WeylGroup t.tag} (hw : t.weylPerm w = w)
    {i : Fin t.tag.rank} (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    height (w • (Pi.single (t.perm i) 1 : Fin t.tag.rank → ℤ)) < 0 := by
  have h := dualRoot_smul w (isRoot_single t.tag i)
  rw [dualRoot_single, hw] at h
  rw [← h]
  exact (height_dualRoot_neg_iff (IsRoot.smul (isRoot_single t.tag i) w)).2 hi

theorem length_mul_blockElt_lt {w : WeylGroup t.tag} (hw : t.weylPerm w = w)
    {i : Fin t.tag.rank} (hi : height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    (coxeterSystem t.tag).length (w * t.blockElt i) < (coxeterSystem t.tag).length w := by
  have hρ := height_smul_perm_neg hw hi
  have hd : DescentWord w (t.reeOrbitWord i) := by
    refine descentWord_of_prefixRoots _ w fun β hβ => ?_
    obtain ⟨hsupp, hnn, hne⟩ := t.blockCheck i β hβ
    refine height_smul_neg_of_support (J := {i, t.perm i}) (fun j hj => ?_)
      (fun k hk => hsupp k (fun h => hk (by simp [h])) (fun h => hk (by simp [h]))) hnn hne
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hi
    · rw [Finset.mem_singleton.1 hj]
      exact hρ
  have h1 := length_mul_wordProd_add _ w hd
  have h2 := t.reeOrbitWord_ne_nil i
  change (coxeterSystem t.tag).length (w * (coxeterSystem t.tag).wordProd (t.reeOrbitWord i)) <
    (coxeterSystem t.tag).length w
  omega

theorem mem_closure_blockElt : ∀ (n : ℕ) (w : WeylGroup t.tag),
    (coxeterSystem t.tag).length w = n → t.weylPerm w = w →
      w ∈ Subgroup.closure (Set.range t.blockElt) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw
    by_cases h1 : w = 1
    · rw [h1]
      exact one_mem _
    obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
    have hlt := length_mul_blockElt_lt hw hi
    have hδ : t.weylPerm (w * t.blockElt i) = w * t.blockElt i := by
      rw [map_mul, hw, (mem_relWeylRee t).1 (reeOrbitWord_mem t i)]
    have hmem := ih _ (hn ▸ hlt) (w * t.blockElt i) rfl hδ
    have : w = w * t.blockElt i * t.blockElt i := by
      rw [mul_assoc, blockElt_mul_self, mul_one]
    rw [this]
    exact mul_mem hmem (Subgroup.subset_closure ⟨i, rfl⟩)

end ReeTag

end CFSG.LieType.Ree

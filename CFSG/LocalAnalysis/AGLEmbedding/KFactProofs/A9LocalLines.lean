module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm
public import TauCeti.Algebra.Group.Subgroup.Map

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A9Local

open Equiv CFSG.Open

private theorem shiftPerm_pow_three (f : ZMod 3 → ZMod 3) : shiftPerm f ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one, ← shiftPerm_add, ← shiftPerm_add, ← shiftPerm_zero]
  congr 1
  funext i
  exact zmod_three_add_self (f i)

private theorem shiftPerm_ne_one {f : ZMod 3 → ZMod 3} (hf : f ≠ 0) : shiftPerm f ≠ 1 := by
  intro h
  exact hf (shiftPerm_injective (h.trans shiftPerm_zero.symm))

private theorem orderOf_shiftPerm {f : ZMod 3 → ZMod 3} (hf : f ≠ 0) :
    orderOf (shiftPerm f) = 3 := by
  exact @orderOf_eq_prime (Perm Pt) _ (shiftPerm f) 3 ⟨Nat.prime_three⟩
    (shiftPerm_pow_three f) (shiftPerm_ne_one hf)

private theorem mem_zpowers_shiftPerm {f : ZMod 3 → ZMod 3} (hf : f ≠ 0) {x : Perm Pt} :
    x ∈ Subgroup.zpowers (shiftPerm f) ↔
      x = 1 ∨ x = shiftPerm f ∨ x = (shiftPerm f)⁻¹ := by
  have h3 := orderOf_shiftPerm hf
  have hsq : (shiftPerm f) ^ 2 = (shiftPerm f)⁻¹ := by
    have hmul : shiftPerm f * (shiftPerm f) ^ 2 = 1 := by
      rw [← pow_succ', shiftPerm_pow_three]
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    have hk : (shiftPerm f) ^ k = (shiftPerm f) ^ (k % (3 : ℤ)) := by
      simpa [h3] using (zpow_mod_orderOf (shiftPerm f) k).symm
    have hmod : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
      have h1 := Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
      omega
    rw [hk]
    rcases hmod with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp [hsq]
  · rintro (h | h | h)
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.mem_zpowers_iff.2 ⟨-1, by simp⟩

private theorem shiftPerm_neg (f : ZMod 3 → ZMod 3) :
    shiftPerm (-f) = (shiftPerm f)⁻¹ := by
  have h : shiftPerm f * shiftPerm (-f) = 1 := by
    rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero]
  exact eq_inv_of_mul_eq_one_right h

theorem zpowers_shiftPerm_eq_iff {f g : ZMod 3 → ZMod 3} (hf : f ≠ 0) :
    Subgroup.zpowers (shiftPerm f) = Subgroup.zpowers (shiftPerm g) ↔ g = f ∨ g = -f := by
  constructor
  · intro heq
    have hmem : shiftPerm g ∈ Subgroup.zpowers (shiftPerm f) := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    rw [mem_zpowers_shiftPerm hf] at hmem
    rcases hmem with h1 | h2 | h3
    · exfalso
      have hgbot : Subgroup.zpowers (shiftPerm g) = ⊥ := Subgroup.zpowers_eq_bot.2 h1
      have hfb : Subgroup.zpowers (shiftPerm f) = ⊥ := by rw [heq, hgbot]
      exact shiftPerm_ne_one hf (Subgroup.zpowers_eq_bot.1 hfb)
    · exact Or.inl (shiftPerm_injective h2)
    · refine Or.inr (shiftPerm_injective ?_)
      rw [shiftPerm_neg]
      exact h3
  · rintro (rfl | hg)
    · rfl
    · rw [hg, shiftPerm_neg, Subgroup.zpowers_inv]

private abbrev signVec (k : ZMod 3) (f : ZMod 3 → ZMod 3) : ZMod 3 → ZMod 3 :=
  fun i => if i = k then f i else -f i

private abbrev blockVec (f : ZMod 3 → ZMod 3) : ZMod 3 → ZMod 3 :=
  fun i => f (i - 1)

private abbrev SameLine (f g : ZMod 3 → ZMod 3) : Prop := f = g ∨ f = -g

private theorem zmod_three_eq (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

private theorem exists_zpowers_of_card_three {V : Subgroup (Perm Pt)}
    (hV : V ≤ baseGroup) (hV3 : Nat.card V = 3) :
    ∃ f : ZMod 3 → ZMod 3, f ≠ 0 ∧ V = Subgroup.zpowers (shiftPerm f) := by
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h] at hV3
    simp at hV3
  obtain ⟨⟨g, hgV⟩, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVne
  obtain ⟨f, rfl⟩ := mem_baseGroup_iff.1 (hV hgV)
  have hf : f ≠ 0 := by
    intro hf0
    apply hgne
    exact Subtype.ext (by simpa [hf0] using shiftPerm_zero)
  have hle : Subgroup.zpowers (shiftPerm f) ≤ V := by
    rw [Subgroup.zpowers_le]
    exact hgV
  have hEq : Subgroup.zpowers (shiftPerm f) = V :=
    @Subgroup.eq_of_le_of_card_ge (Perm Pt) _ (Subgroup.zpowers (shiftPerm f)) V
      (Nat.finite_of_card_ne_zero (by rw [hV3]; norm_num)) hle
      (by rw [hV3, Nat.card_zpowers, orderOf_shiftPerm hf])
  exact ⟨f, hf, hEq.symm⟩

private theorem eq_single_of_zero_of_ne {f : ZMod 3 → ZMod 3} {k : ZMod 3}
    (hzero : ∀ i : ZMod 3, i ≠ k → f i = 0) :
    f = Pi.single k (f k) := by
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · rw [Pi.single_eq_of_ne hi]
    exact hzero i hi

private theorem zpowers_shiftPerm_congr {f g : ZMod 3 → ZMod 3}
    (h : f = g ∨ f = -g) :
    Subgroup.zpowers (shiftPerm f) = Subgroup.zpowers (shiftPerm g) := by
  rcases h with rfl | rfl
  · rfl
  · rw [show shiftPerm (-g) = (shiftPerm g)⁻¹ from shiftPerm_neg g, Subgroup.zpowers_inv]

private theorem exists_single_of_eq_single {f : ZMod 3 → ZMod 3} {k : ZMod 3}
    (hk : f k ≠ 0) (hf_eq : f = Pi.single k (f k)) :
    ∃ k : ZMod 3, Subgroup.zpowers (shiftPerm f) =
      Subgroup.zpowers (shiftPerm (Pi.single k 1)) := by
  have hval : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
  rcases hval (f k) hk with h | h
  · refine ⟨k, ?_⟩
    rw [hf_eq, h]
  · refine ⟨k, ?_⟩
    have hneg : (Pi.single k (-1 : ZMod 3) : ZMod 3 → ZMod 3) = -(Pi.single k 1) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · rw [Pi.single_eq_of_ne hi, Pi.neg_apply, Pi.single_eq_of_ne hi]
        exact neg_zero.symm
    rw [hf_eq, h, hneg]
    exact zpowers_shiftPerm_congr (Or.inr rfl)

private theorem exists_single_of_zero_away {V₁ : Subgroup (Perm Pt)}
    {f : ZMod 3 → ZMod 3} {k : ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (hk : f k ≠ 0) (hzero : ∀ i : ZMod 3, i ≠ k → f i = 0) :
    ∃ k : ZMod 3, V₁ = Subgroup.zpowers (shiftPerm (Pi.single k 1)) := by
  obtain ⟨k', hk'⟩ := exists_single_of_eq_single hk (eq_single_of_zero_of_ne hzero)
  exact ⟨k', hVf.trans hk'⟩

private theorem distinct_full :
    ∀ f : ZMod 3 → ZMod 3, f 0 ≠ 0 → f 1 ≠ 0 → f 2 ≠ 0 →
    f ≠ 0 ∧ signVec 0 f ≠ 0 ∧ signVec 1 f ≠ 0 ∧ signVec 0 (signVec 1 f) ≠ 0 ∧
    ¬ SameLine f (signVec 0 f) ∧ ¬ SameLine f (signVec 1 f) ∧
    ¬ SameLine f (signVec 0 (signVec 1 f)) ∧
    ¬ SameLine (signVec 0 f) (signVec 1 f) ∧
    ¬ SameLine (signVec 0 f) (signVec 0 (signVec 1 f)) ∧
    ¬ SameLine (signVec 1 f) (signVec 0 (signVec 1 f)) := by
  decide +kernel

private theorem distinct_pair01 :
    ∀ f : ZMod 3 → ZMod 3, f 0 ≠ 0 → f 1 ≠ 0 → f 2 = 0 →
    f ≠ 0 ∧ signVec 0 f ≠ 0 ∧ blockVec f ≠ 0 ∧ blockVec (signVec 0 f) ≠ 0 ∧
    ¬ SameLine f (signVec 0 f) ∧ ¬ SameLine f (blockVec f) ∧
    ¬ SameLine f (blockVec (signVec 0 f)) ∧
    ¬ SameLine (signVec 0 f) (blockVec f) ∧
    ¬ SameLine (signVec 0 f) (blockVec (signVec 0 f)) ∧
    ¬ SameLine (blockVec f) (blockVec (signVec 0 f)) := by
  decide +kernel

private theorem distinct_pair02 :
    ∀ f : ZMod 3 → ZMod 3, f 0 ≠ 0 → f 2 ≠ 0 → f 1 = 0 →
    f ≠ 0 ∧ signVec 0 f ≠ 0 ∧ blockVec f ≠ 0 ∧ blockVec (signVec 0 f) ≠ 0 ∧
    ¬ SameLine f (signVec 0 f) ∧ ¬ SameLine f (blockVec f) ∧
    ¬ SameLine f (blockVec (signVec 0 f)) ∧
    ¬ SameLine (signVec 0 f) (blockVec f) ∧
    ¬ SameLine (signVec 0 f) (blockVec (signVec 0 f)) ∧
    ¬ SameLine (blockVec f) (blockVec (signVec 0 f)) := by
  decide +kernel

private theorem distinct_pair12 :
    ∀ f : ZMod 3 → ZMod 3, f 1 ≠ 0 → f 2 ≠ 0 → f 0 = 0 →
    f ≠ 0 ∧ signVec 1 f ≠ 0 ∧ blockVec f ≠ 0 ∧
    blockVec (signVec 0 (signVec 1 f)) ≠ 0 ∧
    ¬ SameLine f (signVec 1 f) ∧ ¬ SameLine f (blockVec f) ∧
    ¬ SameLine f (blockVec (signVec 0 (signVec 1 f))) ∧
    ¬ SameLine (signVec 1 f) (blockVec f) ∧
    ¬ SameLine (signVec 1 f) (blockVec (signVec 0 (signVec 1 f))) ∧
    ¬ SameLine (blockVec f) (blockVec (signVec 0 (signVec 1 f))) := by
  decide +kernel

private theorem conj_s0 (f : ZMod 3 → ZMod 3) :
    signAt 0 * shiftPerm f * (signAt 0)⁻¹ = shiftPerm (signVec 0 f) :=
  signAt_conj_shiftPerm 0 f

private theorem conj_s1 (f : ZMod 3 → ZMod 3) :
    signAt 1 * shiftPerm f * (signAt 1)⁻¹ = shiftPerm (signVec 1 f) :=
  signAt_conj_shiftPerm 1 f

private theorem conj_b (f : ZMod 3 → ZMod 3) :
    blockShift * shiftPerm f * blockShift⁻¹ = shiftPerm (blockVec f) :=
  blockShift_conj_shiftPerm f

private theorem conj_s0s1 (f : ZMod 3 → ZMod 3) :
    (signAt 0 * signAt 1) * shiftPerm f * (signAt 0 * signAt 1)⁻¹ =
      shiftPerm (signVec 0 (signVec 1 f)) := by
  calc (signAt 0 * signAt 1) * shiftPerm f * (signAt 0 * signAt 1)⁻¹
      = signAt 0 * (signAt 1 * shiftPerm f * (signAt 1)⁻¹) * (signAt 0)⁻¹ := by
        group
    _ = signAt 0 * shiftPerm (signVec 1 f) * (signAt 0)⁻¹ := by rw [conj_s1]
    _ = shiftPerm (signVec 0 (signVec 1 f)) := conj_s0 _

private theorem conj_bs0 (f : ZMod 3 → ZMod 3) :
    (blockShift * signAt 0) * shiftPerm f * (blockShift * signAt 0)⁻¹ =
      shiftPerm (blockVec (signVec 0 f)) := by
  calc (blockShift * signAt 0) * shiftPerm f * (blockShift * signAt 0)⁻¹
      = blockShift * (signAt 0 * shiftPerm f * (signAt 0)⁻¹) * blockShift⁻¹ := by
        group
    _ = blockShift * shiftPerm (signVec 0 f) * blockShift⁻¹ := by rw [conj_s0]
    _ = shiftPerm (blockVec (signVec 0 f)) := conj_b _

private theorem conj_bs0s1 (f : ZMod 3 → ZMod 3) :
    (blockShift * signAt 0 * signAt 1) * shiftPerm f *
        (blockShift * signAt 0 * signAt 1)⁻¹ =
      shiftPerm (blockVec (signVec 0 (signVec 1 f))) := by
  calc (blockShift * signAt 0 * signAt 1) * shiftPerm f *
        (blockShift * signAt 0 * signAt 1)⁻¹
      = blockShift * ((signAt 0 * signAt 1) * shiftPerm f * (signAt 0 * signAt 1)⁻¹) *
          blockShift⁻¹ := by group
    _ = blockShift * shiftPerm (signVec 0 (signVec 1 f)) * blockShift⁻¹ := by rw [conj_s0s1]
    _ = shiftPerm (blockVec (signVec 0 (signVec 1 f))) := conj_b _

private theorem map_conj_zpowers {h : Perm Pt} {f g : ZMod 3 → ZMod 3}
    (hg : h * shiftPerm f * h⁻¹ = shiftPerm g) :
    (Subgroup.zpowers (shiftPerm f)).map (MulAut.conj h).toMonoidHom =
      Subgroup.zpowers (shiftPerm g) := by
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers ((MulAut.conj h) (shiftPerm f)) = _
  rw [MulAut.conj_apply, hg]

private theorem false_of_three_mem_pair {α : Type*} {A B a b c : α}
    (ha : a = A ∨ a = B) (hb : b = A ∨ b = B) (hc : c = A ∨ c = B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> simp_all

private theorem zpowers_shiftPerm_ne_of_not_same {f v : ZMod 3 → ZMod 3} (hv : v ≠ 0)
    (h : ¬ SameLine f v) :
    Subgroup.zpowers (shiftPerm v) ≠ Subgroup.zpowers (shiftPerm f) := by
  intro hEq
  exact h ((zpowers_shiftPerm_eq_iff hv).1 hEq)

private theorem mem_pair_of_mem_three {α : Type*} {a V₁ V₂ V₃ : α}
    (ha : a ∈ ({V₁, V₂, V₃} : Set α)) (hne : a ≠ V₁) : a = V₂ ∨ a = V₃ := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

private theorem false_of_invariant_four {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    {f v1 v2 v3 : ZMod 3 → ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (hv1 : v1 ≠ 0) (hv2 : v2 ≠ 0) (hv3 : v3 ≠ 0)
    (hW1 : Subgroup.zpowers (shiftPerm v1) ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))))
    (hW2 : Subgroup.zpowers (shiftPerm v2) ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))))
    (hW3 : Subgroup.zpowers (shiftPerm v3) ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))))
    (hfv1 : ¬ SameLine f v1) (hfv2 : ¬ SameLine f v2) (hfv3 : ¬ SameLine f v3)
    (h12 : ¬ SameLine v1 v2) (h13 : ¬ SameLine v1 v3) (h23 : ¬ SameLine v2 v3) :
    False := by
  have hW1ne : Subgroup.zpowers (shiftPerm v1) ≠ V₁ := by
    rw [hVf]
    exact zpowers_shiftPerm_ne_of_not_same hv1 hfv1
  have hW2ne : Subgroup.zpowers (shiftPerm v2) ≠ V₁ := by
    rw [hVf]
    exact zpowers_shiftPerm_ne_of_not_same hv2 hfv2
  have hW3ne : Subgroup.zpowers (shiftPerm v3) ≠ V₁ := by
    rw [hVf]
    exact zpowers_shiftPerm_ne_of_not_same hv3 hfv3
  have hW12 : Subgroup.zpowers (shiftPerm v1) ≠ Subgroup.zpowers (shiftPerm v2) :=
    Ne.symm (zpowers_shiftPerm_ne_of_not_same hv2 h12)
  have hW13 : Subgroup.zpowers (shiftPerm v1) ≠ Subgroup.zpowers (shiftPerm v3) :=
    Ne.symm (zpowers_shiftPerm_ne_of_not_same hv3 h13)
  have hW23 : Subgroup.zpowers (shiftPerm v2) ≠ Subgroup.zpowers (shiftPerm v3) :=
    Ne.symm (zpowers_shiftPerm_ne_of_not_same hv3 h23)
  exact false_of_three_mem_pair
    (mem_pair_of_mem_three hW1 hW1ne) (mem_pair_of_mem_three hW2 hW2ne)
    (mem_pair_of_mem_three hW3 hW3ne) hW12 hW13 hW23

private theorem invariant_contra_full {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    {f : ZMod 3 → ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0) (h2 : f 2 ≠ 0)
    (hinv : ∀ g ∈ ({signAt 0, signAt 1, blockShift} : Set (Perm Pt)),
      ∀ V ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))),
        V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt)))) :
    False := by
  obtain ⟨-, hv1, hv2, hv3, hfv1, hfv2, hfv3, h12, h13, h23⟩ :=
    distinct_full f h0 h1 h2
  have hS0 : V₁.map (MulAut.conj (signAt 0)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv (signAt 0) (by simp) V₁ (by simp)
  have hS1 : V₁.map (MulAut.conj (signAt 1)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv (signAt 1) (by simp) V₁ (by simp)
  have hS01 : V₁.map (MulAut.conj (signAt 0 * signAt 1)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← Subgroup.map_conj_map_conj V₁ (signAt 1) (signAt 0)]
    exact hinv (signAt 0) (by simp) _ (hinv (signAt 1) (by simp) V₁ (by simp))
  have hW1 : Subgroup.zpowers (shiftPerm (signVec 0 f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s0 f), ← hVf]
    exact hS0
  have hW2 : Subgroup.zpowers (shiftPerm (signVec 1 f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s1 f), ← hVf]
    exact hS1
  have hW3 : Subgroup.zpowers (shiftPerm (signVec 0 (signVec 1 f))) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s0s1 f), ← hVf]
    exact hS01
  exact false_of_invariant_four hVf hv1 hv2 hv3 hW1 hW2 hW3 hfv1 hfv2 hfv3 h12 h13 h23

private theorem invariant_contra_pair01 {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    {f : ZMod 3 → ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0) (h2 : f 2 = 0)
    (hinv : ∀ g ∈ ({signAt 0, signAt 1, blockShift} : Set (Perm Pt)),
      ∀ V ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))),
        V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt)))) :
    False := by
  obtain ⟨-, hv1, hv2, hv3, hfv1, hfv2, hfv3, h12, h13, h23⟩ :=
    distinct_pair01 f h0 h1 h2
  have hS0 : V₁.map (MulAut.conj (signAt 0)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv (signAt 0) (by simp) V₁ (by simp)
  have hSb : V₁.map (MulAut.conj blockShift).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv blockShift (by simp) V₁ (by simp)
  have hSb0 : V₁.map (MulAut.conj (blockShift * signAt 0)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← Subgroup.map_conj_map_conj V₁ (signAt 0) blockShift]
    exact hinv blockShift (by simp) _ hS0
  have hW1 : Subgroup.zpowers (shiftPerm (signVec 0 f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s0 f), ← hVf]
    exact hS0
  have hW2 : Subgroup.zpowers (shiftPerm (blockVec f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_b f), ← hVf]
    exact hSb
  have hW3 : Subgroup.zpowers (shiftPerm (blockVec (signVec 0 f))) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_bs0 f), ← hVf]
    exact hSb0
  exact false_of_invariant_four hVf hv1 hv2 hv3 hW1 hW2 hW3 hfv1 hfv2 hfv3 h12 h13 h23

private theorem invariant_contra_pair02 {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    {f : ZMod 3 → ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (h0 : f 0 ≠ 0) (h2 : f 2 ≠ 0) (h1 : f 1 = 0)
    (hinv : ∀ g ∈ ({signAt 0, signAt 1, blockShift} : Set (Perm Pt)),
      ∀ V ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))),
        V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt)))) :
    False := by
  obtain ⟨-, hv1, hv2, hv3, hfv1, hfv2, hfv3, h12, h13, h23⟩ :=
    distinct_pair02 f h0 h2 h1
  have hS0 : V₁.map (MulAut.conj (signAt 0)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv (signAt 0) (by simp) V₁ (by simp)
  have hSb : V₁.map (MulAut.conj blockShift).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv blockShift (by simp) V₁ (by simp)
  have hSb0 : V₁.map (MulAut.conj (blockShift * signAt 0)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← Subgroup.map_conj_map_conj V₁ (signAt 0) blockShift]
    exact hinv blockShift (by simp) _ hS0
  have hW1 : Subgroup.zpowers (shiftPerm (signVec 0 f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s0 f), ← hVf]
    exact hS0
  have hW2 : Subgroup.zpowers (shiftPerm (blockVec f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_b f), ← hVf]
    exact hSb
  have hW3 : Subgroup.zpowers (shiftPerm (blockVec (signVec 0 f))) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_bs0 f), ← hVf]
    exact hSb0
  exact false_of_invariant_four hVf hv1 hv2 hv3 hW1 hW2 hW3 hfv1 hfv2 hfv3 h12 h13 h23

private theorem invariant_contra_pair12 {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    {f : ZMod 3 → ZMod 3}
    (hVf : V₁ = Subgroup.zpowers (shiftPerm f))
    (h1 : f 1 ≠ 0) (h2 : f 2 ≠ 0) (h0 : f 0 = 0)
    (hinv : ∀ g ∈ ({signAt 0, signAt 1, blockShift} : Set (Perm Pt)),
      ∀ V ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))),
        V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt)))) :
    False := by
  obtain ⟨-, hv1, hv2, hv3, hfv1, hfv2, hfv3, h12, h13, h23⟩ :=
    distinct_pair12 f h1 h2 h0
  have hS1 : V₁.map (MulAut.conj (signAt 1)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv (signAt 1) (by simp) V₁ (by simp)
  have hSb : V₁.map (MulAut.conj blockShift).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) :=
    hinv blockShift (by simp) V₁ (by simp)
  have hS01 : V₁.map (MulAut.conj (signAt 0 * signAt 1)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← Subgroup.map_conj_map_conj V₁ (signAt 1) (signAt 0)]
    exact hinv (signAt 0) (by simp) _ (hinv (signAt 1) (by simp) V₁ (by simp))
  have hSb01 : V₁.map (MulAut.conj (blockShift * signAt 0 * signAt 1)).toMonoidHom ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [mul_assoc, ← Subgroup.map_conj_map_conj V₁ (signAt 0 * signAt 1) blockShift]
    exact hinv blockShift (by simp) _ hS01
  have hW1 : Subgroup.zpowers (shiftPerm (signVec 1 f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_s1 f), ← hVf]
    exact hS1
  have hW2 : Subgroup.zpowers (shiftPerm (blockVec f)) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_b f), ← hVf]
    exact hSb
  have hW3 : Subgroup.zpowers (shiftPerm (blockVec (signVec 0 (signVec 1 f)))) ∈
      ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))) := by
    rw [← map_conj_zpowers (conj_bs0s1 f), ← hVf]
    exact hSb01
  exact false_of_invariant_four hVf hv1 hv2 hv3 hW1 hW2 hW3 hfv1 hfv2 hfv3 h12 h13 h23

theorem eq_zpowers_single_of_invariant {V₁ V₂ V₃ : Subgroup (Perm Pt)}
    (hV : V₁ ≤ baseGroup) (hV3 : Nat.card V₁ = 3)
    (hinv : ∀ g ∈ ({signAt 0, signAt 1, blockShift} : Set (Perm Pt)),
      ∀ V ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt))),
        V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂, V₃} : Set (Subgroup (Perm Pt)))) :
    ∃ k : ZMod 3, V₁ = Subgroup.zpowers (shiftPerm (Pi.single k 1)) := by
  obtain ⟨f, hf, hVf⟩ := exists_zpowers_of_card_three hV hV3
  by_cases h0 : f 0 = 0
  · by_cases h1 : f 1 = 0
    · have h2 : f 2 ≠ 0 := by
        intro h2
        apply hf
        funext i
        rcases zmod_three_eq i with rfl | rfl | rfl <;> simp [h0, h1, h2]
      have hzero : ∀ i : ZMod 3, i ≠ 2 → f i = 0 := by
        intro i hi
        rcases zmod_three_eq i with rfl | rfl | rfl
        exacts [h0, h1, absurd rfl hi]
      exact exists_single_of_zero_away hVf h2 hzero
    · by_cases h2 : f 2 = 0
      · have hzero : ∀ i : ZMod 3, i ≠ 1 → f i = 0 := by
          intro i hi
          rcases zmod_three_eq i with rfl | rfl | rfl
          exacts [h0, absurd rfl hi, h2]
        exact exists_single_of_zero_away hVf h1 hzero
      · exact (invariant_contra_pair12 hVf h1 h2 h0 hinv).elim
  · by_cases h1 : f 1 = 0
    · by_cases h2 : f 2 = 0
      · have hzero : ∀ i : ZMod 3, i ≠ 0 → f i = 0 := by
          intro i hi
          rcases zmod_three_eq i with rfl | rfl | rfl
          exacts [absurd rfl hi, h1, h2]
        exact exists_single_of_zero_away hVf h0 hzero
      · exact (invariant_contra_pair02 hVf h0 h2 h1 hinv).elim
    · by_cases h2 : f 2 = 0
      · exact (invariant_contra_pair01 hVf h0 h1 h2 hinv).elim
      · exact (invariant_contra_full hVf h0 h1 h2 hinv).elim

private abbrev triple (k : ZMod 3) : Perm Pt :=
  Equiv.swap (k + 1, (0 : ZMod 3)) (k + 1, 1) *
    Equiv.swap (k + 1, (0 : ZMod 3)) (k + 2, 0)

private theorem triple_mem_alternating (k : ZMod 3) :
    triple k ∈ alternatingGroup Pt := by
  rw [Perm.mem_alternatingGroup]
  fin_cases k <;> decide +kernel

private theorem triple_commute (k : ZMod 3) :
    Commute (triple k) (shiftPerm (Pi.single k 1)) := by
  change triple k * shiftPerm (Pi.single k 1) = shiftPerm (Pi.single k 1) * triple k
  fin_cases k <;> decide +kernel

private theorem triple_conj_apply (k : ZMod 3) :
    (triple k * shiftPerm (Pi.single (k + 1) 1) * (triple k)⁻¹) (k + 2, 0) =
      (k + 1, 0) := by
  fin_cases k <;> decide +kernel

theorem exists_commute_not_mem_nrm (k : ZMod 3) :
    ∃ g ∈ alternatingGroup Pt, Commute g (shiftPerm (Pi.single k 1)) ∧ g ∉ nrm := by
  refine ⟨triple k, triple_mem_alternating k, triple_commute k, ?_⟩
  intro hg
  have hconj : triple k * shiftPerm (Pi.single (k + 1) 1) * (triple k)⁻¹ ∈ baseGroup := by
    rw [Subgroup.mem_set_normalizer_iff] at hg
    exact (hg _).1 (shiftPerm_mem_baseGroup _)
  obtain ⟨f, hf⟩ := mem_baseGroup_iff.1 hconj
  have hca : shiftPerm f (k + 2, 0) = (k + 1, 0) := by
    rw [← hf]
    exact triple_conj_apply k
  have hfst := congrArg Prod.fst hca
  simp [shiftPerm_apply] at hfst
  have h21 : (2 : ZMod 3) = 1 := by
    have := congrArg (fun x : ZMod 3 => x - k) hfst
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
  exact absurd h21 (by decide)

end CFSG.AGLEmbedding.A9Local

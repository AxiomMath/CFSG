module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.RootSystem.Form

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

variable {τ : Tag}

theorem simple_inv
    (i : Fin τ.rank) : (simple τ i)⁻¹ = simple τ i :=
  (coxeterSystem τ).inv_simple i

theorem simple_mul_simple_self
    (i : Fin τ.rank) : simple τ i * simple τ i = 1 :=
  (coxeterSystem τ).simple_mul_simple_self i

theorem length_simple_mul_cases
    (w : WeylGroup τ) (i : Fin τ.rank) :
    (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1 ∨
      (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w :=
  (coxeterSystem τ).length_simple_mul w i

theorem length_mul_simple_cases
    (w : WeylGroup τ) (i : Fin τ.rank) :
    (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1 ∨
      (coxeterSystem τ).length (w * simple τ i) + 1 = (coxeterSystem τ).length w :=
  (coxeterSystem τ).length_mul_simple w i

theorem isLeftDescent_iff_length
    (w : WeylGroup τ) (i : Fin τ.rank) :
    (coxeterSystem τ).IsLeftDescent w i ↔
      (coxeterSystem τ).length (simple τ i * w) + 1 = (coxeterSystem τ).length w :=
  (coxeterSystem τ).isLeftDescent_iff

theorem not_isLeftDescent_iff_length
    (w : WeylGroup τ) (i : Fin τ.rank) :
    ¬ (coxeterSystem τ).IsLeftDescent w i ↔
      (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1 :=
  (coxeterSystem τ).not_isLeftDescent_iff

theorem isRightDescent_iff_length
    (w : WeylGroup τ) (i : Fin τ.rank) :
    (coxeterSystem τ).IsRightDescent w i ↔
      (coxeterSystem τ).length (w * simple τ i) + 1 = (coxeterSystem τ).length w :=
  (coxeterSystem τ).isRightDescent_iff

theorem not_isRightDescent_iff_length
    (w : WeylGroup τ) (i : Fin τ.rank) :
    ¬ (coxeterSystem τ).IsRightDescent w i ↔
      (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1 :=
  (coxeterSystem τ).not_isRightDescent_iff

theorem smul_single_mem_negRoots_iff
    (w : WeylGroup τ) (i : Fin τ.rank) :
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ {α | IsRoot τ α ∧ height α < 0} ↔
      (coxeterSystem τ).IsRightDescent w i := by
  have hroot := IsRoot.smul (isRoot_single τ i) w
  rw [CFSG.LieType.RootSystem.isRightDescent_iff, ← smul_def]
  refine ⟨fun h j => ((IsRoot.height_neg_iff hroot).1 h.2) j, fun h => ⟨hroot, ?_⟩⟩
  exact (IsRoot.height_neg_iff hroot).2 fun j => h j

theorem mem_posRoots_iff_not_mem_negRoots
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    α ∈ {α | IsRoot τ α ∧ 0 < height α} ↔ α ∉ {α | IsRoot τ α ∧ height α < 0} := by
  simp only [Set.mem_ofPred_eq, hα, true_and, not_lt]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hα.height_ne_zero.symm⟩

theorem coroot_inv_smul_of_smul_single
    {u : WeylGroup τ} {i j : Fin τ.rank}
    (h : u • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single i 1) (v : Fin τ.rank → ℤ) :
    coroot τ.cartan j (u⁻¹ • v) = coroot τ.cartan i v := by
  have key : ∀ (k : Fin τ.rank) (x : Fin τ.rank → ℤ),
      form (isFiniteType_cartan τ) (toRat x) (Pi.single k 1) =
        symmetrizer (isFiniteType_cartan τ) k * (coroot τ.cartan k x : ℚ) := fun k x => by
    rw [form_single_right, coroot_apply]
    push_cast
    simp [toRat_apply]
  have hform1 : form (isFiniteType_cartan τ) (toRat (u⁻¹ • v)) (Pi.single j 1) =
      form (isFiniteType_cartan τ) (toRat v) (Pi.single i 1) := by
    rw [← toRat_single, ← toRat_single, ← form_weylAction (isFiniteType_cartan τ) u, ← smul_def,
      ← smul_def, smul_inv_smul, h]
  have hform2 : form (isFiniteType_cartan τ) (Pi.single j 1) (Pi.single j 1) =
      form (isFiniteType_cartan τ) (Pi.single i 1) (Pi.single i 1) := by
    rw [← toRat_single, ← toRat_single, ← form_weylAction (isFiniteType_cartan τ) u, ← smul_def,
      h]
  rw [form_single_single, form_single_single] at hform2
  have hd : symmetrizer (isFiniteType_cartan τ) j = symmetrizer (isFiniteType_cartan τ) i := by
    linarith
  rw [key, key, hd] at hform1
  exact_mod_cast mul_left_cancel₀ (symmetrizer_pos (isFiniteType_cartan τ) i).ne' hform1

theorem mul_simple_mul_inv_of_smul_single
    {u : WeylGroup τ} {i j : Fin τ.rank}
    (h : u • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single i 1) :
    u * simple τ j * u⁻¹ = simple τ i := by
  have hz : ∀ (c : ℤ) (x : Fin τ.rank → ℤ), u • (c • x) = c • (u • x) := fun c x => by
    rw [smul_def, smul_def, map_zsmul]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin τ.rank → ℤ) fun v => ?_
  rw [mul_smul, mul_smul, simple_smul, simple_smul, ← reflection_cartan, ← reflection_cartan,
    reflection_apply_coroot, reflection_apply_coroot, smul_sub, smul_inv_smul, hz, h,
    coroot_inv_smul_of_smul_single h v]

theorem exists_exchange
    {ω : List (Fin τ.rank)} {i : Fin τ.rank}
    (hle : (coxeterSystem τ).length (simple τ i * (coxeterSystem τ).wordProd ω) ≤
      (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω)) :
    ∃ (j : ℕ) (hj : j < ω.length),
      simple τ i * (coxeterSystem τ).wordProd (ω.take j) =
          (coxeterSystem τ).wordProd (ω.take j) * simple τ ω[j] ∧
        simple τ i * (coxeterSystem τ).wordProd ω =
          (coxeterSystem τ).wordProd (ω.eraseIdx j) := by
  classical
  set w := (coxeterSystem τ).wordProd ω with hw
  have hdesc : (coxeterSystem τ).IsLeftDescent w i := by
    rw [isLeftDescent_iff_length]
    rcases length_simple_mul_cases w i with h | h
    · omega
    · exact h
  have hneg : height (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 :=
    ((smul_single_mem_negRoots_iff w⁻¹ i).2 ((coxeterSystem τ).isRightDescent_inv_iff.2 hdesc)).2
  have hex : ∃ k, ¬ 0 < height (((coxeterSystem τ).wordProd (ω.take k))⁻¹ •
      (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    ⟨ω.length, by rw [List.take_length, ← hw]; exact not_lt.2 hneg.le⟩
  have hk₀ := Nat.find_spec hex
  have hk₀len : Nat.find hex ≤ ω.length := Nat.find_min' hex (by
    rw [List.take_length, ← hw]
    exact not_lt.2 hneg.le)
  have hk₀ne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, List.take_zero, CoxeterSystem.wordProd_nil, inv_one, one_smul, height_single] at hk₀
    exact hk₀ one_pos
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjlen : j < ω.length := by omega
  have hPj : 0 < height (((coxeterSystem τ).wordProd (ω.take j))⁻¹ •
      (Pi.single i 1 : Fin τ.rank → ℤ)) := not_not.1 (Nat.find_min hex (by omega))
  rw [hj] at hk₀
  set u := (coxeterSystem τ).wordProd (ω.take j) with hu
  have htake : (coxeterSystem τ).wordProd (ω.take (j + 1)) = u * simple τ ω[j] := by
    rw [← List.take_concat_get' ω j hjlen, (coxeterSystem τ).wordProd_append,
      (coxeterSystem τ).wordProd_singleton]
  have hroot : IsRoot τ (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ i) u⁻¹
  have hst : u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single ω[j] 1 := by
    by_contra hne
    apply hk₀
    rw [htake, mul_inv_rev, simple_inv, mul_smul, simple_smul]
    exact height_reflect_pos hroot hPj hne
  have hut : u • (Pi.single ω[j] 1 : Fin τ.rank → ℤ) = Pi.single i 1 := by
    rw [← hst, smul_inv_smul]
  have hcomm : simple τ i * u = u * simple τ ω[j] := by
    rw [← mul_simple_mul_inv_of_smul_single hut, inv_mul_cancel_right]
  refine ⟨j, hjlen, hcomm, ?_⟩
  have hsplit : ω = ω.take (j + 1) ++ ω.drop (j + 1) := (List.take_append_drop _ _).symm
  rw [hw]
  conv_lhs => rw [hsplit]
  rw [(coxeterSystem τ).wordProd_append, htake, List.eraseIdx_eq_take_drop_succ,
    (coxeterSystem τ).wordProd_append, ← mul_assoc, ← mul_assoc, hcomm, mul_assoc u,
    simple_mul_simple_self, mul_one]

theorem weyl_exchange_condition
    (τ : Tag) :
    (∀ (w : WeylGroup τ) (i : Fin τ.rank),
      (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ {α | IsRoot τ α ∧ height α < 0} →
        (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w - 1) ∧
      (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ {α | IsRoot τ α ∧ 0 < height α} →
        (coxeterSystem τ).length (simple τ i * w) = (coxeterSystem τ).length w + 1)) ∧
    (∀ (w : WeylGroup τ) (i : Fin τ.rank),
      ((coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w - 1 ↔
        w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ {α | IsRoot τ α ∧ height α < 0}) ∧
      (w • (Pi.single i 1 : Fin τ.rank → ℤ) ∉ {α | IsRoot τ α ∧ height α < 0} →
        (coxeterSystem τ).length (w * simple τ i) = (coxeterSystem τ).length w + 1)) ∧
    (∀ (ω : List (Fin τ.rank)) (i : Fin τ.rank),
      (coxeterSystem τ).length (simple τ i * (coxeterSystem τ).wordProd ω) ≤
          (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) →
        ∃ (j : ℕ) (hj : j < ω.length),
          simple τ i * (coxeterSystem τ).wordProd (ω.take j) =
              (coxeterSystem τ).wordProd (ω.take j) * simple τ ω[j] ∧
            simple τ i * (coxeterSystem τ).wordProd ω =
              (coxeterSystem τ).wordProd (ω.eraseIdx j)) ∧
    (∀ w : WeylGroup τ, w ≠ 1 →
      ∃ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ {α | IsRoot τ α ∧ height α < 0}) := by
  refine ⟨fun w i => ⟨fun h => ?_, fun h => ?_⟩, fun w i => ⟨⟨fun h => ?_, fun h => ?_⟩,
    fun h => ?_⟩, fun ω i hle => exists_exchange hle, fun w hw => ?_⟩
  · have hd : (coxeterSystem τ).IsLeftDescent w i :=
      (coxeterSystem τ).isRightDescent_inv_iff.1 ((smul_single_mem_negRoots_iff w⁻¹ i).1 h)
    rw [isLeftDescent_iff_length] at hd
    omega
  · have hd : ¬ (coxeterSystem τ).IsLeftDescent w i := fun hd =>
      ((mem_posRoots_iff_not_mem_negRoots (IsRoot.smul (isRoot_single τ i) w⁻¹)).1 h)
        ((smul_single_mem_negRoots_iff w⁻¹ i).2 ((coxeterSystem τ).isRightDescent_inv_iff.2 hd))
    exact (not_isLeftDescent_iff_length w i).1 hd
  · refine (smul_single_mem_negRoots_iff w i).2 ((isRightDescent_iff_length w i).2 ?_)
    rcases length_mul_simple_cases w i with h' | h'
    · omega
    · exact h'
  · have hd := (smul_single_mem_negRoots_iff w i).1 h
    rw [isRightDescent_iff_length] at hd
    omega
  · exact (not_isRightDescent_iff_length w i).1 fun hd =>
      h ((smul_single_mem_negRoots_iff w i).2 hd)
  · obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one hw
    exact ⟨i, IsRoot.smul (isRoot_single τ i) w, hi⟩

end CFSG.LieType.Chevalley

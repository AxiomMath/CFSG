module

public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.WeylExchange

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem smul_eq_sum_smul_single
    (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ j, v j • (w • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_comm w (v j) _

theorem mem_parabolicWeylGroup_of_coord
    {A : Set (Fin τ.rank)} :
    ∀ (n : ℕ) (w : WeylGroup τ), (coxeterSystem τ).length w = n →
      (∀ v : Fin τ.rank → ℤ, ∀ i ∉ A, (w • v) i = v i) →
      w ∈ parabolicWeylGroup τ A ∧ ∃ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω ∧
        (coxeterSystem τ).wordProd ω = w ∧ ∀ i ∈ ω, i ∈ A := by
  intro n
  induction n with
  | zero =>
    intro w hw _
    rw [CoxeterSystem.length_eq_zero_iff] at hw
    subst hw
    exact ⟨one_mem _, [], by simp [CoxeterSystem.IsReduced], by simp, by simp⟩
  | succ n ih =>
    intro w hw hfix
    have hw1 : w ≠ 1 := fun h => by
      rw [h, CoxeterSystem.length_one] at hw
      omega
    obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w hw1
    have hiA : i ∈ A := by
      by_contra hi
      have h1 := hfix (Pi.single i 1) i hi
      have h2 := (IsRoot.height_neg_iff hroot).1 hneg i
      rw [h1, Pi.single_eq_same] at h2
      omega
    have hlen : (coxeterSystem τ).length (w * simple τ i) = n := by
      have := ((weyl_exchange_condition τ).2.1 w i).1.2 ⟨hroot, hneg⟩
      omega
    have hsi : simple τ i ∈ parabolicWeylGroup τ A := Subgroup.subset_closure ⟨i, hiA, rfl⟩
    have hfix' : ∀ v : Fin τ.rank → ℤ, ∀ j ∉ A, ((w * simple τ i) • v) j = v j := by
      intro v j hj
      rw [mul_smul, hfix _ j hj, smul_apply_of_mem_parabolicWeylGroup hsi v hj]
    obtain ⟨hmem, ω, hred, hprod, hletters⟩ := ih _ hlen hfix'
    have hw' : w = w * simple τ i * simple τ i := by
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
    refine ⟨hw' ▸ mul_mem hmem hsi, ω ++ [i], ?_, ?_, fun j hj => ?_⟩
    · rw [CoxeterSystem.IsReduced, CoxeterSystem.wordProd_append, hprod,
        CoxeterSystem.wordProd_singleton, ← hw', hw, List.length_append, List.length_singleton]
      have := hred
      rw [CoxeterSystem.IsReduced, hprod, hlen] at this
      omega
    · rw [CoxeterSystem.wordProd_append, hprod, CoxeterSystem.wordProd_singleton, ← hw']
    · rcases List.mem_append.1 hj with hj | hj
      · exact hletters j hj
      · rw [List.mem_singleton] at hj
        exact hj ▸ hiA

theorem neg_mem_parabolicPosRoots_of_simple_neg
    {A : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A)
    (hneg : ∀ i ∈ A, height (w • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0)
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicPosRoots τ A) :
    -(w • α) ∈ parabolicPosRoots τ A := by
  obtain ⟨⟨hroot, hzero⟩, -, hpos⟩ := hα
  have hwα : IsRoot τ (w • α) := IsRoot.smul hroot w
  have hcoord : ∀ k, (w • α) k ≤ 0 := by
    intro k
    rw [smul_eq_sum_smul_single, Finset.sum_apply]
    refine Finset.sum_nonpos fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j ∈ A
    · exact mul_nonpos_of_nonneg_of_nonpos ((IsRoot.height_pos_iff hroot).1 hpos j)
        ((IsRoot.height_neg_iff (IsRoot.smul (isRoot_single τ j) w)).1 (hneg j hj) k)
    · rw [hzero j hj, zero_mul]
  have hht : height (w • α) < 0 := by
    rcases IsRoot.height_pos_or_neg hwα with h | h
    · have := (IsRoot.height_pos_iff hwα).1 h
      have hall : w • α = 0 := funext fun k => le_antisymm (hcoord k) (this k)
      exact absurd hall (IsRoot.ne_zero hwα)
    · exact h
  refine ⟨⟨IsRoot.neg hwα, fun i hi => ?_⟩, IsRoot.neg hwα, by rw [height_neg]; omega⟩
  rw [Pi.neg_apply, smul_apply_of_mem_parabolicWeylGroup hw α hi, hzero i hi, neg_zero]

theorem parabolic_Weyl_coordinate_stabilizer
    (τ : Tag) (A : Set (Fin τ.rank)) :
    (parabolicWeylGroup τ A : Set (WeylGroup τ)) =
      {w | ∀ v : Fin τ.rank → ℤ, ∀ i ∉ A, (w • v) i = v i} ∧
    (∀ w ∈ parabolicWeylGroup τ A, ∃ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω ∧
      (coxeterSystem τ).wordProd ω = w ∧ ∀ i ∈ ω, i ∈ A) ∧
    Finite (parabolicWeylGroup τ A) ∧
    ∃! wA : WeylGroup τ, wA ∈ parabolicWeylGroup τ A ∧
      (fun α => wA • α) '' parabolicPosRoots τ A = (fun α => -α) '' parabolicPosRoots τ A := by
  have hset : (parabolicWeylGroup τ A : Set (WeylGroup τ)) =
      {w | ∀ v : Fin τ.rank → ℤ, ∀ i ∉ A, (w • v) i = v i} := by
    ext w
    exact ⟨fun hw v i hi => smul_apply_of_mem_parabolicWeylGroup hw v hi,
      fun hw => (mem_parabolicWeylGroup_of_coord _ w rfl hw).1⟩
  refine ⟨hset, fun w hw => (mem_parabolicWeylGroup_of_coord _ w rfl
    fun v i hi => smul_apply_of_mem_parabolicWeylGroup hw v hi).2, inferInstance, ?_⟩
  obtain ⟨⟨w, hw⟩, hmax⟩ := Finite.exists_max fun u : parabolicWeylGroup τ A =>
    (coxeterSystem τ).length (u : WeylGroup τ)
  have hneg : ∀ (u : WeylGroup τ), u ∈ parabolicWeylGroup τ A →
      (coxeterSystem τ).length u = (coxeterSystem τ).length w →
      ∀ i ∈ A, height (u • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
    intro u hu hlu i hi
    rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single τ i) u) with h | h
    · exfalso
      have hnn : u • (Pi.single i 1 : Fin τ.rank → ℤ) ∉ {α | IsRoot τ α ∧ height α < 0} :=
        fun h' => absurd h'.2 (by omega)
      have hl := ((weyl_exchange_condition τ).2.1 u i).2 hnn
      have hmem : u * simple τ i ∈ parabolicWeylGroup τ A :=
        mul_mem hu (Subgroup.subset_closure ⟨i, hi, rfl⟩)
      have := hmax ⟨_, hmem⟩
      simp only at this
      omega
    · exact h
  have hmaps : ∀ (u : WeylGroup τ), u ∈ parabolicWeylGroup τ A →
      (coxeterSystem τ).length u = (coxeterSystem τ).length w →
      (fun α => u • α) '' parabolicPosRoots τ A ⊆ (fun α => -α) '' parabolicPosRoots τ A := by
    rintro u hu hlu _ ⟨α, hα, rfl⟩
    exact ⟨_, neg_mem_parabolicPosRoots_of_simple_neg hu (hneg u hu hlu) hα, neg_neg _⟩
  have hwA : (fun α => w • α) '' parabolicPosRoots τ A =
      (fun α => -α) '' parabolicPosRoots τ A := by
    refine Set.Subset.antisymm (hmaps w hw rfl) ?_
    rintro _ ⟨β, hβ, rfl⟩
    have hwi : w⁻¹ ∈ parabolicWeylGroup τ A := inv_mem hw
    obtain ⟨α, hα, hαβ⟩ := hmaps w⁻¹ hwi (CoxeterSystem.length_inv _ _) ⟨β, hβ, rfl⟩
    refine ⟨α, hα, ?_⟩
    simp only at hαβ ⊢
    rw [← neg_eq_iff_eq_neg.2 hαβ.symm, smul_neg, smul_inv_smul]
  refine ⟨w, ⟨hw, hwA⟩, fun w' ⟨hw', hw'A⟩ => ?_⟩
  set u := w⁻¹ * w'
  have hu : u ∈ parabolicWeylGroup τ A := mul_mem (inv_mem hw) hw'
  have hpos : ∀ i, 0 < height (u • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    intro i
    by_cases hi : i ∈ A
    · have hei : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ A :=
        ⟨⟨isRoot_single τ i, fun j hj => Pi.single_eq_of_ne (fun h => hj (by rw [h]; exact hi)) _⟩,
          isRoot_single τ i, by rw [height_single]; exact one_pos⟩
      obtain ⟨β, hβ, hβe⟩ : w' • (Pi.single i 1 : Fin τ.rank → ℤ) ∈
          (fun α => -α) '' parabolicPosRoots τ A := hw'A ▸ ⟨_, hei, rfl⟩
      obtain ⟨γ, hγ, hγβ⟩ : -β ∈ (fun α => w • α) '' parabolicPosRoots τ A := by
        rw [hwA]
        exact ⟨β, hβ, rfl⟩
      have : u • (Pi.single i 1 : Fin τ.rank → ℤ) = γ := by
        simp only at hβe hγβ
        rw [show u = w⁻¹ * w' from rfl, mul_smul, ← hβe, ← hγβ]
        simp only [inv_smul_smul]
      rw [this]
      exact hγ.2.2
    · have h1 := smul_apply_of_mem_parabolicWeylGroup hu (Pi.single i 1) hi
      rw [Pi.single_eq_same] at h1
      rcases IsRoot.height_pos_or_neg (IsRoot.smul (isRoot_single τ i) u) with h | h
      · exact h
      · have := (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single τ i) u)).1 h i
        omega
  have hu1 : u = 1 := by
    by_contra hu1
    obtain ⟨i, -, hi⟩ := (weyl_exchange_condition τ).2.2.2 u hu1
    have := hpos i
    omega
  have : w' = w * u := by rw [mul_inv_cancel_left]
  rw [this, hu1, mul_one]

end CFSG.LieType.Chevalley

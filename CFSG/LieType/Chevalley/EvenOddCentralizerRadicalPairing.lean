module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLayerAction
public import CFSG.LieType.Chevalley.SylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def rootPairing
    : LinearMap.BilinForm K (RootModule τ K) :=
  LinearMap.mk₂ K
    (fun x y => ∑ β : {v // IsRoot τ v}, x (Sum.inr β) * y (Sum.inr ⟨-β.1, IsRoot.neg β.2⟩))
    (fun x x' y => by simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp only [Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp only [Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm])

theorem rootPairing_apply
    (x y : RootModule τ K) :
    rootPairing τ K x y =
      ∑ β : {v // IsRoot τ v}, x (Sum.inr β) * y (Sum.inr ⟨-β.1, IsRoot.neg β.2⟩) :=
  rfl

theorem rootVec_apply_inr (δ : Fin τ.rank → ℤ) (β : {v // IsRoot τ v}) :
    rootVec τ K δ (Sum.inr β) = if β.1 = δ then 1 else 0 := by
  classical
  by_cases hδ : IsRoot τ δ
  · rw [rootVec_of_isRoot hδ, Finsupp.single_apply]
    by_cases h : β.1 = δ
    · rw [ite_eq_left (congrArg Sum.inr (Subtype.ext h.symm)), ite_eq_left h]
    · rw [ite_eq_right fun h' => h (congrArg Subtype.val (Sum.inr_injective h')).symm,
        ite_eq_right h]
  · rw [rootVec_of_not hδ, ite_eq_right fun h : β.1 = δ => hδ (h ▸ β.2)]
    rfl

theorem rootPairing_rootVec_neg
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (x : RootModule τ K) :
    rootPairing τ K x (rootVec τ K (-α)) = x (Sum.inr ⟨α, hα⟩) := by
  rw [rootPairing_apply, Fintype.sum_eq_single (⟨α, hα⟩ : {v // IsRoot τ v})]
  · rw [rootVec_apply_inr, ite_eq_left rfl, mul_one]
  · intro β hβ
    rw [rootVec_apply_inr, ite_eq_right, mul_zero]
    intro h
    exact hβ (Subtype.ext (neg_inj.1 h))

open _root_.Classical in
theorem rootPairing_rootVec
    (γ δ : Fin τ.rank → ℤ) :
    rootPairing τ K (rootVec τ K γ) (rootVec τ K δ) =
      if IsRoot τ γ ∧ γ + δ = 0 then 1 else 0 := by
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_of_isRoot hγ, rootPairing_apply,
      Fintype.sum_eq_single (⟨γ, hγ⟩ : {v // IsRoot τ v})]
    · rw [Finsupp.single_eq_same, one_mul, rootVec_apply_inr]
      by_cases h : -γ = δ
      · rw [ite_eq_left h, ite_eq_left ⟨hγ, by rw [← h, add_neg_cancel]⟩]
      · rw [ite_eq_right h, ite_eq_right fun h' => h (neg_eq_of_add_eq_zero_right h'.2)]
    · intro β hβ
      rw [Finsupp.single_eq_of_ne fun h => hβ (Sum.inr_injective h), zero_mul]
  · rw [ite_eq_right fun h => hγ h.1, rootVec_of_not hγ, map_zero, LinearMap.zero_apply]

theorem not_isRoot_two_smul
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (j : Fin τ.rank) {m : ℤ} (hm : m ≠ 0)
    (h₁ : IsRoot τ (α + m • Pi.single j 1)) (h₂ : IsRoot τ (α + (2 * m) • Pi.single j 1)) :
    False := by
  have e₁ := mul_add_eq_zero_of_isRoot hτ hα j h₁
  have e₂ := mul_add_eq_zero_of_isRoot hτ hα j h₂
  rcases mul_eq_zero.1 e₁ with h | h
  · exact hm h
  · rcases mul_eq_zero.1 e₂ with h' | h'
    · exact hm (by omega)
    · exact hm (by omega)

theorem rootPairing_torusElt
    (i : Fin τ.rank) (t : Kˣ) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) :
    rootPairing τ K ((torusElt τ K i t : Module.End K (RootModule τ K)) (rootVec τ K α))
        ((torusElt τ K i t : Module.End K (RootModule τ K)) (rootVec τ K (-β))) =
      rootPairing τ K (rootVec τ K α) (rootVec τ K (-β)) := by
  rw [torusElt_rootVec i t hα, torusElt_rootVec i t (IsRoot.neg hβ)]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, rootPairing_rootVec]
  split_ifs with h
  · have hαβ : α = β := add_neg_eq_zero.1 h.2
    have e : (∑ j, τ.cartan i j * (-α) j) = -∑ j, τ.cartan i j * α j := by
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [← hαβ, e]
    simp only [zpow_neg, Units.val_inv_eq_inv_val, mul_one]
    exact inv_mul_cancel₀ (Units.ne_zero _)
  · simp

theorem rootPairing_rootOp
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    {J : Set (Fin τ.rank)} {n : ℕ} {j : Fin τ.rank} (hj : j ∈ J) {m : ℤ} (hm : m = 1 ∨ m = -1)
    (f : Module.End K (RootModule τ K)) (c : K)
    (hf : ∀ γ, IsRoot τ γ → γ ≠ Pi.single j 1 → γ ≠ -Pi.single j 1 →
      f (rootVec τ K γ) = rootVec τ K γ + c • rootVec τ K (γ + m • Pi.single j 1))
    {α β : Fin τ.rank → ℤ} (hα : α ∈ layerRoots τ J (n + 1)) (hβ : β ∈ layerRoots τ J (n + 1)) :
    rootPairing τ K (f (rootVec τ K α)) (f (rootVec τ K (-β))) =
      rootPairing τ K (rootVec τ K α) (rootVec τ K (-β)) := by
  obtain ⟨h₁, h₂, -, -, -, -⟩ := ne_single_of_mem_layerRoots hj hα
  obtain ⟨h₃, h₄, -, -, -, -⟩ := ne_single_of_mem_layerRoots hj hβ
  have h₃' : -β ≠ Pi.single j 1 := fun h => h₄ (by rw [← h, neg_neg])
  have h₄' : -β ≠ -Pi.single j 1 := fun h => h₃ (neg_inj.1 h)
  have hm0 : m ≠ 0 := by omega
  rw [hf α hα.1 h₁ h₂, hf (-β) (IsRoot.neg hβ.1) h₃' h₄']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    rootPairing_rootVec]
  set e : Fin τ.rank → ℤ := m • Pi.single j 1 with he
  have hD : ¬(IsRoot τ (α + e) ∧ α + e + (-β + e) = 0) := by
    rintro ⟨hr, hsum⟩
    have hβ' : β = α + (2 * m) • Pi.single j 1 := by
      rw [mul_smul, two_smul, ← he]
      linear_combination (exp := 1) -hsum
    exact not_isRoot_two_smul hτ hα.1 j hm0 hr (hβ' ▸ hβ.1)
  have hBC : (IsRoot τ α ∧ α + (-β + e) = 0) ↔ (IsRoot τ (α + e) ∧ α + e + -β = 0) := by
    constructor
    · rintro ⟨-, h⟩
      have hb : α + e = β := by linear_combination (exp := 1) h
      exact ⟨hb ▸ hβ.1, by rw [hb, add_neg_cancel]⟩
    · rintro ⟨-, h⟩
      exact ⟨hα.1, by linear_combination (exp := 1) h⟩
  rw [ite_eq_right hD]
  by_cases hB : IsRoot τ α ∧ α + (-β + e) = 0
  · rw [ite_eq_left hB, ite_eq_left (hBC.1 hB)]
    linear_combination c * h2
  · rw [ite_eq_right hB, ite_eq_right (mt hBC.2 hB)]
    ring

theorem rootPairing_map_of_basis
    {J : Set (Fin τ.rank)} {n : ℕ}
    (f : Module.End K (RootModule τ K))
    (hf : ∀ α ∈ layerRoots τ J (n + 1), ∀ β ∈ layerRoots τ J (n + 1),
      rootPairing τ K (f (rootVec τ K α)) (f (rootVec τ K (-β))) =
        rootPairing τ K (rootVec τ K α) (rootVec τ K (-β)))
    {x y : RootModule τ K} (hx : x ∈ parabolicGraded τ K J (n + 1))
    (hy : y ∈ parabolicGraded τ K J (-(n + 1))) :
    rootPairing τ K (f x) (f y) = rootPairing τ K x y := by
  unfold parabolicGraded at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    rcases hx' with ⟨α, hα, hd, rfl⟩ | ⟨hd, -, -⟩
    · have hαL : α ∈ layerRoots τ J (n + 1) :=
        ⟨hα, height_pos_of_degree (J := J) hα (by omega), hd⟩
      induction hy using Submodule.span_induction with
      | mem y hy' =>
        rcases hy' with ⟨γ, hγ, hdγ, rfl⟩ | ⟨hdγ, -, -⟩
        · have hd' : parabolicDegree τ J (-γ) = n + 1 := by rw [parabolicDegree_neg, hdγ]; ring
          have hβ : -γ ∈ layerRoots τ J (n + 1) :=
            ⟨IsRoot.neg hγ, height_pos_of_degree (J := J) (IsRoot.neg hγ) (by omega), hd'⟩
          have h := hf α hαL (-γ) hβ
          rwa [neg_neg] at h
        · omega
      | zero => simp only [map_zero]
      | add y y' _ _ h h' => simp only [map_add, h, h']
      | smul c y _ h => simp only [map_smul, h]
    · omega
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' _ _ h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | smul c x _ h => simp only [map_smul, LinearMap.smul_apply, h]

theorem rootPairing_parabolicLevi
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) {x y : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hy : y ∈ parabolicGraded τ K J (-(n + 1))) :
    rootPairing τ K ((g : Module.End K (RootModule τ K)) x)
        ((g : Module.End K (RootModule τ K)) y) = rootPairing τ K x y := by
  have hM : parabolicLevi τ K J = Subgroup.closure
      (Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  have hgen : ∀ g ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c},
      ∀ x ∈ parabolicGraded τ K J (n + 1), ∀ y ∈ parabolicGraded τ K J (-(n + 1)),
        rootPairing τ K ((g : Module.End K (RootModule τ K)) x)
          ((g : Module.End K (RootModule τ K)) y) = rootPairing τ K x y := by
    rintro g (⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩) x hx y hy
    · exact rootPairing_map_of_basis _ (fun α hα β hβ => rootPairing_torusElt i t hα.1 hβ.1) hx hy
    · refine rootPairing_map_of_basis _ (fun α hα β hβ => ?_) hx hy
      refine rootPairing_rootOp hτ h2 hj (Or.inl rfl) _ c (fun γ hγ h₁ h₂ => ?_) hα hβ
      rw [coe_xUnit, xOp_rootVec hτ j c hγ h₁ h₂, one_smul]
    · refine rootPairing_map_of_basis _ (fun α hα β hβ => ?_) hx hy
      refine rootPairing_rootOp hτ h2 hj (Or.inr rfl) _ c (fun γ hγ h₁ h₂ => ?_) hα hβ
      rw [coe_yUnit, yOp_rootVec hτ j c hγ h₁ h₂, neg_smul, one_smul, sub_eq_add_neg]
  have hinv : ∀ g ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c},
      g⁻¹ ∈ Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} := by
    rintro g (⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c', rfl | rfl⟩)
    · refine Or.inl ⟨⟨i, t⁻¹⟩, ?_⟩
      simp only
      rw [eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
    · exact Or.inr ⟨j, hj, -c', Or.inl (xUnit_neg j c').symm⟩
    · exact Or.inr ⟨j, hj, -c', Or.inr (yUnit_neg j c').symm⟩
  rw [hM] at hg
  induction hg using Subgroup.closure_induction'' generalizing x y with
  | mem g hgs => exact hgen g hgs x hx y hy
  | inv_mem g hgs => exact hgen g⁻¹ (hinv g hgs) x hx y hy
  | one => simp only [Units.val_one, Module.End.one_apply]
  | mul g h hg₁ hh₁ ihg ihh =>
    have hhM : h ∈ parabolicLevi τ K J := by rw [hM]; exact hh₁
    rw [Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      ihg (parabolicLevi_preserves hhM _ hx) (parabolicLevi_preserves hhM _ hy), ihh hx hy]

theorem natCast_eq_one_of_odd (h2 : (2 : K) = 0) {m : ℕ} (hm : Odd m) : (m : K) = 1 := by
  obtain ⟨k, rfl⟩ := hm
  push_cast
  rw [h2, zero_mul, zero_add]

theorem exists_fixed_neg_of_fixed
    [Finite K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h2 : (2 : K) = 0) (J : Set (Fin τ.rank)) (n : ℕ) {S : Subgroup (ModGL τ K)}
    (hS : S ≤ parabolicLevi τ K J) (hodd : Odd (Nat.card S)) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (n + 1)) (hx0 : x ≠ 0)
    (hfix : ∀ s ∈ S, (s : Module.End K (RootModule τ K)) x = x) :
    ∃ y ∈ parabolicGraded τ K J (-(n + 1)), y ≠ 0 ∧
      ∀ s ∈ S, (s : Module.End K (RootModule τ K)) y = y := by
  classical
  have := finite_modGL (τ := τ) (K := K)
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Finsupp.ext h)
  have hbL : b ∈ gradedLabels τ J (n + 1) := by
    have hx' := hx
    rw [parabolicGraded_eq_supported] at hx'
    exact (Finsupp.mem_supported K x).1 hx' (Finsupp.mem_support_iff.2 hb)
  obtain ⟨α, hα, rfl⟩ := mem_layerRoots_of_mem_gradedLabels hbL
  have hy₀ : rootVec τ K (-α) ∈ parabolicGraded τ K J (-(n + 1)) :=
    rootVec_mem_parabolicGraded (IsRoot.neg hα.1) (by rw [parabolicDegree_neg, hα.2.2])
  set y : RootModule τ K := ∑ s : S, ((s : ModGL τ K) : Module.End K (RootModule τ K))
    (rootVec τ K (-α)) with hy
  refine ⟨y, Submodule.sum_mem _ fun s _ => parabolicLevi_preserves (hS s.2) _ hy₀, ?_, ?_⟩
  · intro h0
    have hpair : rootPairing τ K x y = x (Sum.inr ⟨α, hα.1⟩) := by
      rw [hy, map_sum]
      have hterm : ∀ s : S, rootPairing τ K x (((s : ModGL τ K) : Module.End K (RootModule τ K))
          (rootVec τ K (-α))) = x (Sum.inr ⟨α, hα.1⟩) := fun s => by
        conv_lhs => rw [← hfix s s.2]
        rw [rootPairing_parabolicLevi hτ h2 J n (hS s.2) hx hy₀, rootPairing_rootVec_neg hα.1]
      rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_eq_nat_card, natCast_eq_one_of_odd h2 hodd, one_mul]
    rw [h0, map_zero] at hpair
    exact hb hpair.symm
  · intro s hs
    rw [hy, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨s, hs⟩ : S)) _ _ fun t => ?_
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply]

end CFSG.LieType.Chevalley.EvenOddRadical

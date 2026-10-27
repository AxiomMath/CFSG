module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


private theorem exc_root_eq_or_neg_aux1 {τ : Tag} {α β : Fin τ.rank → ℤ} {m : ℤ}
    (hα : IsRoot τ α) (h : α = m • β) : m = 1 ∨ m = -1 := by
  classical
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hα
  have hthis : w⁻¹ • α = w⁻¹ • (m • β) := by rw [h]
  rw [← hw, inv_smul_smul] at hthis
  have hz : w⁻¹ • (m • β) = m • (w⁻¹ • β) := by
    rw [smul_def, smul_def]
    exact map_zsmul (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w⁻¹).toAddMonoidHom m β
  rw [hz] at hthis
  have hj := congrFun hthis j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at hj
  exact Int.eq_one_or_neg_one_of_mul_eq_one hj.symm

theorem exc_root_eq_or_neg {τ : Tag} {x γ : Fin τ.rank → ℤ} (hx : IsRoot τ x) (hγ : IsRoot τ γ)
    {c : ℤ} (h : (2 : ℤ) • x = c • γ) : x = γ ∨ x = -γ := by
  rcases Int.even_or_odd c with hc | hc
  · obtain ⟨c', rfl⟩ := hc
    have h2 : x = c' • γ := by
      funext k
      have hk := congrFun h k
      simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
      have hmul : 2 * x k = 2 * (c' * γ k) := by rw [hk]; ring
      omega
    rcases exc_root_eq_or_neg_aux1 (β := γ) (m := c') hx h2 with h1 | h1
    · left; rw [h2, h1, one_smul]
    · right; rw [h2, h1, neg_one_smul]
  · obtain ⟨c', rfl⟩ := hc
    have hy : γ = (2 : ℤ) • (x - c' • γ) := by
      funext k
      have hk := congrFun h k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hk ⊢
      have hmul : 2 * x k = 2 * (c' * γ k) + γ k := by rw [hk]; ring
      omega
    have hcontra := exc_root_eq_or_neg_aux1 (β := x - c' • γ) (m := 2) hγ hy
    omega

private theorem exc_card_pos_odd_aux1 {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    corootPair β β = 2 := by
  have hpos := iform_self_pos_of_isRoot hβ
  have h := corootPair_mul hβ β
  exact mul_right_cancel₀ hpos.ne' (by rw [h])

private theorem exc_card_pos_odd_aux2 {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) : corootPair β (-v) = - corootPair β v := by
  have hpos := iform_self_pos_of_isRoot hβ
  have hneg : iform β (-v) = - iform β v := by
    rw [show -v = (-1 : ℤ) • v by rw [neg_one_smul], iform_smul_right]
    ring
  have h1 := corootPair_mul hβ (-v)
  have h2 := corootPair_mul hβ v
  rw [hneg] at h1
  apply mul_right_cancel₀ hpos.ne'
  rw [h1]
  have e : (2 : ℤ) * -iform β v = - (corootPair β v * iform β β) := by
    have h3 : (2 : ℤ) * -iform β v = -(2 * iform β v) := by ring
    rw [h3, ← h2]
  rw [e]
  ring

private theorem exc_card_pos_odd_aux3 {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    corootPair β (rootReflection β • v) = - corootPair β v := by
  have hpos := iform_self_pos_of_isRoot hβ
  have h1 := corootPair_mul hβ (rootReflection β • v)
  have h2 := corootPair_mul hβ v
  rw [rootReflection_smul hβ, iform_sub_right, iform_smul_right] at h1
  apply mul_right_cancel₀ hpos.ne'
  rw [rootReflection_smul hβ, h1, mul_sub, ← h2]
  ring

private noncomputable abbrev excKindTheta {τ : Tag} (γ : Fin τ.rank → ℤ) (P : Set (Fin τ.rank → ℤ))
    (h : ∀ x : ↥P, -(rootReflection γ • (x : Fin τ.rank → ℤ)) ∈ P) : Function.End ↥P :=
  fun x => ⟨-(rootReflection γ • (x : Fin τ.rank → ℤ)), h x⟩

private theorem exc_card_pos_odd_aux4 {τ : Tag} {P : Set (Fin τ.rank → ℤ)}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h : ∀ x : ↥P, -(rootReflection γ • (x : Fin τ.rank → ℤ)) ∈ P) :
    excKindTheta γ P h ^ 2 = 1 := by
  funext x
  apply Subtype.ext
  change - (rootReflection γ • (-(rootReflection γ • (x : Fin τ.rank → ℤ))))
    = (x : Fin τ.rank → ℤ)
  simp only [smul_neg, neg_neg, smul_smul, rootReflection_mul_self hγ, one_smul]

private theorem exc_card_pos_odd_aux5 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {P : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) (hP : ∀ x : Fin τ.rank → ℤ, x ∈ P ↔ x ∈ Ψ ∧ 0 < corootPair γ x)
    (h : ∀ x : ↥P, -(rootReflection γ • (x : Fin τ.rank → ℤ)) ∈ P) :
    Function.fixedPoints (excKindTheta γ P h) = {x : ↥P | (x : Fin τ.rank → ℤ) = γ} := by
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  ext x
  constructor
  · intro hx
    have hx' : -(rootReflection γ • (x : Fin τ.rank → ℤ)) = (x : Fin τ.rank → ℤ) :=
      congrArg Subtype.val hx
    have hr : rootReflection γ • (x : Fin τ.rank → ℤ) = -(x : Fin τ.rank → ℤ) := by
      simpa using congrArg Neg.neg hx'
    have h2 : (2 : ℤ) • (x : Fin τ.rank → ℤ) =
        corootPair γ (x : Fin τ.rank → ℤ) • γ := by
      funext k
      have hk := congrFun hr k
      rw [rootReflection_smul hγr] at hk
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hk ⊢
      omega
    have hxP := (hP x.1).1 x.2
    rcases exc_root_eq_or_neg (hΨ.isRoot x.1 hxP.1) hγr h2 with hv | hv
    · exact hv
    · exfalso
      have hpos := hxP.2
      rw [hv, exc_card_pos_odd_aux2 hγr, exc_card_pos_odd_aux1 hγr] at hpos
      norm_num at hpos
  · intro hx
    apply Subtype.ext
    show -(rootReflection γ • (x : Fin τ.rank → ℤ)) = (x : Fin τ.rank → ℤ)
    rw [hx, rootReflection_smul_self hγr, neg_neg]

theorem exc_card_pos_odd {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) :
    Odd {x : Fin τ.rank → ℤ | x ∈ Ψ ∧ 0 < corootPair γ x}.ncard := by
  classical
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  set P : Set (Fin τ.rank → ℤ) := {x | x ∈ Ψ ∧ 0 < corootPair γ x} with hPdef
  have hPfin : P.Finite :=
    (finite_setOf_isRoot τ).subset fun x hx => hΨ.isRoot x hx.1
  haveI : Fintype ↥P := hPfin.fintype
  have hγP : γ ∈ P := ⟨hγ, by rw [exc_card_pos_odd_aux1 hγr]; norm_num⟩
  have hθmem : ∀ x : ↥P, -(rootReflection γ • (x : Fin τ.rank → ℤ)) ∈ P := by
    intro x
    refine ⟨hΨ.neg_mem _ (hΨ.reflection_mem x.1 x.2.1 γ hγ), ?_⟩
    rw [exc_card_pos_odd_aux2 hγr, exc_card_pos_odd_aux3 hγr]
    simpa using x.2.2
  have hθ2 : excKindTheta γ P hθmem ^ 2 = 1 := exc_card_pos_odd_aux4 hγr hθmem
  have hfix : Function.fixedPoints (excKindTheta γ P hθmem)
      = {x : ↥P | (x : Fin τ.rank → ℤ) = γ} :=
    exc_card_pos_odd_aux5 hΨ hγ (fun x => by simp [hPdef]) hθmem
  have hfixP : Function.fixedPoints (excKindTheta γ P hθmem) = {⟨γ, hγP⟩} := by
    rw [hfix]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  have hcardFix : Fintype.card (Function.fixedPoints (excKindTheta γ P hθmem)) = 1 := by
    rw [Set.fintypeCard_eq_ncard, hfixP]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := excKindTheta γ P hθmem) (p := 2) (n := 1)
    (by simpa using hθ2)
  have hcardP_odd : Odd (Fintype.card ↥P) := by
    rw [Nat.ModEq, hcardFix] at hmod
    rw [Nat.odd_iff]
    simpa using hmod
  rw [← Set.fintypeCard_eq_ncard]
  exact hcardP_odd

private theorem exc_reflection_perm_sign_aux1 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    [Fintype ↥Ψ] [DecidableEq ↥Ψ] (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ Ψ) (π : Equiv.Perm ↥Ψ)
    (hπ : ∀ x : ↥Ψ, (π x : Fin τ.rank → ℤ) = rootReflection γ • (x : Fin τ.rank → ℤ)) :
    Function.fixedPoints π = {x : ↥Ψ | corootPair γ (x : Fin τ.rank → ℤ) = 0} := by
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  ext x
  constructor
  · intro hx
    have hx' : (π x : Fin τ.rank → ℤ) = (x : Fin τ.rank → ℤ) := congrArg Subtype.val hx
    have h3 : (x : Fin τ.rank → ℤ) - corootPair γ (x : Fin τ.rank → ℤ) • γ
        = (x : Fin τ.rank → ℤ) := by
      have := hx'
      rwa [hπ x, rootReflection_smul hγr] at this
    have h2 : corootPair γ (x : Fin τ.rank → ℤ) • γ = 0 := sub_eq_self.mp h3
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hγr.ne_zero
  · intro hx
    apply Subtype.ext
    rw [hπ x, rootReflection_smul hγr, hx, zero_smul, sub_zero]

private theorem exc_reflection_perm_sign_aux2 {α : Type*} [Fintype α] (f : α → ℤ) :
    (Finset.univ.filter fun x => f x ≠ 0).card =
      (Finset.univ.filter fun x => 0 < f x).card
        + (Finset.univ.filter fun x => f x < 0).card := by
  have e1 : (Finset.univ.filter fun x => f x ≠ 0).filter (fun x => 0 < f x)
      = Finset.univ.filter fun x => 0 < f x := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
  have e2 : (Finset.univ.filter fun x => f x ≠ 0).filter (fun x => ¬ 0 < f x)
      = Finset.univ.filter fun x => f x < 0 := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hne, hnot⟩; omega
    · intro h; exact ⟨by omega, by omega⟩
  rw [← e1, ← e2]
  exact (Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x => f x ≠ 0) (p := fun x => 0 < f x)).symm

private theorem exc_reflection_perm_sign_aux3 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    [Fintype ↥Ψ] (hΨ : IsRootComponent Ψ) (γ : Fin τ.rank → ℤ) :
    (Finset.univ.filter fun x : ↥Ψ => 0 < corootPair γ x).card
      = {x : Fin τ.rank → ℤ | x ∈ Ψ ∧ 0 < corootPair γ x}.ncard := by
  have hPfin : {x : Fin τ.rank → ℤ | x ∈ Ψ ∧ 0 < corootPair γ x}.Finite :=
    (finite_setOf_isRoot τ).subset fun x hx => hΨ.isRoot x hx.1
  haveI : Fintype ↥{x : Fin τ.rank → ℤ | x ∈ Ψ ∧ 0 < corootPair γ x} := hPfin.fintype
  rw [← Fintype.card_subtype (p := fun x : ↥Ψ => 0 < corootPair γ x)]
  rw [← Set.fintypeCard_eq_ncard]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

private theorem exc_reflection_perm_sign_aux4 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    [Fintype ↥Ψ] (γ : Fin τ.rank → ℤ) (π : Equiv.Perm ↥Ψ)
    (hππ : ∀ x : ↥Ψ, π (π x) = x)
    (hcπ : ∀ x : ↥Ψ, corootPair γ ((π x : ↥Ψ) : Fin τ.rank → ℤ)
      = - corootPair γ (x : Fin τ.rank → ℤ)) :
    (Finset.univ.filter fun x : ↥Ψ => 0 < corootPair γ x).card
      = (Finset.univ.filter fun x : ↥Ψ => corootPair γ x < 0).card := by
  refine Finset.card_bij' (fun x _ => π x) (fun x _ => π x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := hcπ x
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := hcπ x
    omega
  · intro x hx; exact hππ x
  · intro x hx; exact hππ x

private theorem exc_reflection_perm_sign_aux5 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    [Fintype ↥Ψ] [DecidableEq ↥Ψ] (γ : Fin τ.rank → ℤ) (π : Equiv.Perm ↥Ψ)
    (hfix : Function.fixedPoints π = {x : ↥Ψ | corootPair γ (x : Fin τ.rank → ℤ) = 0}) :
    (Finset.univ.filter fun x : ↥Ψ => corootPair γ x = 0).card
      = Fintype.card (Function.fixedPoints π) := by
  rw [Set.fintypeCard_eq_ncard, hfix, ← Set.fintypeCard_eq_ncard]
  change (Finset.univ.filter fun x : ↥Ψ => corootPair γ x = 0).card
    = Fintype.card {x : ↥Ψ // corootPair γ x = 0}
  rw [Fintype.card_subtype (p := fun x : ↥Ψ => corootPair γ x = 0)]

theorem exc_reflection_perm_sign {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} [Fintype ↥Ψ] [DecidableEq ↥Ψ]
    (hΨ : IsRootComponent Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (π : Equiv.Perm ↥Ψ)
    (hπ : ∀ x : ↥Ψ, (π x : Fin τ.rank → ℤ) = rootReflection γ • (x : Fin τ.rank → ℤ)) :
    Equiv.Perm.sign π = -1 := by
  classical
  have hγr : IsRoot τ γ := hΨ.isRoot γ hγ
  have hcπ : ∀ x : ↥Ψ, corootPair γ ((π x : ↥Ψ) : Fin τ.rank → ℤ)
      = - corootPair γ (x : Fin τ.rank → ℤ) := by
    intro x; rw [hπ x, exc_card_pos_odd_aux3 hγr]
  have hππ : ∀ x : ↥Ψ, π (π x) = x := by
    intro x; apply Subtype.ext
    rw [hπ (π x), hπ x, smul_smul, rootReflection_mul_self hγr, one_smul]
  have hπ2 : π ^ 2 = 1 := by
    refine Equiv.ext fun x => ?_
    rw [pow_two]; simpa using hππ x
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hπ2
  have hfix := exc_reflection_perm_sign_aux1 hΨ hγ π hπ
  have hA := (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ↥Ψ)) (p := fun x : ↥Ψ => corootPair γ x = 0)).symm
  have hB := exc_reflection_perm_sign_aux2 (fun x : ↥Ψ => corootPair γ x)
  have hC := exc_reflection_perm_sign_aux5 γ π hfix
  have hD := exc_reflection_perm_sign_aux4 γ π hππ hcπ
  have hPpos := exc_reflection_perm_sign_aux3 hΨ γ
  have hexp : (Fintype.card ↥Ψ - Fintype.card (Function.fixedPoints π)) / 2
      = {x : Fin τ.rank → ℤ | x ∈ Ψ ∧ 0 < corootPair γ x}.ncard := by
    have hcardα : Fintype.card ↥Ψ
        = (Finset.univ.filter fun x : ↥Ψ => corootPair γ x = 0).card
          + (Finset.univ.filter fun x : ↥Ψ => corootPair γ x ≠ 0).card := by
      rw [← Finset.card_univ]; exact hA
    rw [hcardα, hB, ← hD, ← hC, hPpos]
    rw [Nat.add_sub_cancel_left, ← two_mul,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hsign, hexp]
  exact Odd.neg_one_pow (exc_card_pos_odd hΨ hγ)

end CFSG.LocalAnalysis.GLTheoremA.I167

end

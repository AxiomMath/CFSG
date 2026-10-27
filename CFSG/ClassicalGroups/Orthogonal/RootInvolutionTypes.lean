module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def eichlerPairProd (P : ℕ → HypPair Q) (j : ℕ) : ℕ → V ≃ₗ[K] V
  | 0 => 1
  | k + 1 => eichlerPairProd P j k * eichler Q (P (j + 2 * k)).e (P (j + 2 * k + 1)).e

theorem eichlerPairProd_zero (P : ℕ → HypPair Q) (j : ℕ) : eichlerPairProd P j 0 = 1 :=
  rfl

theorem eichlerPairProd_succ (P : ℕ → HypPair Q) (j k : ℕ) :
    eichlerPairProd P j (k + 1) =
      eichlerPairProd P j k * eichler Q (P (j + 2 * k)).e (P (j + 2 * k + 1)).e :=
  rfl

theorem eichlerPairProd_mem_elementaryGroup (P : ℕ → HypPair Q) (j k : ℕ) :
    eichlerPairProd P j k ∈ elementaryGroup Q := by
  induction k with
  | zero => exact one_mem _
  | succ k ih => exact mul_mem ih (eichler_mem_elementaryGroup Q _ _)

theorem eichlerPairProd_mem_orthogonalGroup (P : ℕ → HypPair Q) (j k : ℕ) :
    eichlerPairProd P j k ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q (eichlerPairProd_mem_elementaryGroup P j k)

theorem eichlerPairProd_add (P : ℕ → HypPair Q) (j k₁ k₂ : ℕ) :
    eichlerPairProd P j (k₁ + k₂) = eichlerPairProd P j k₁ * eichlerPairProd P (j + 2 * k₁) k₂ := by
  induction k₂ with
  | zero => rw [Nat.add_zero, eichlerPairProd_zero, mul_one]
  | succ k ih =>
    rw [← Nat.add_assoc, eichlerPairProd_succ, ih, eichlerPairProd_succ, mul_assoc,
      show j + 2 * (k₁ + k) = j + 2 * k₁ + 2 * k by ring]

theorem eichlerPairProd_apply_of_polar {P : ℕ → HypPair Q} {j k : ℕ} {x : V}
    (hx : ∀ i, j ≤ i → i < j + 2 * k → polar Q x (P i).e = 0) : eichlerPairProd P j k x = x := by
  induction k with
  | zero =>
    rw [eichlerPairProd_zero]
    rfl
  | succ k ih =>
    rw [eichlerPairProd_succ, LinearEquiv.mul_apply,
      eichler_apply_of_polar_eq_zero (hx (j + 2 * k) (by omega) (by omega))
        (hx (j + 2 * k + 1) (by omega) (by omega)),
      ih fun i hi hi' => hx i hi (by omega)]

private theorem commute_eichler_of_fix {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} (hu : g u = u) (hw : g w = w) :
    g * eichler Q u w = eichler Q u w * g := by
  have hc := eichler_conj hg u w
  rw [hu, hw] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

private theorem eichlerPairProd_commute_next {P : ℕ → HypPair Q} {r j k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : j + 2 * (k + 1) ≤ r) :
    eichlerPairProd P j k * eichler Q (P (j + 2 * k)).e (P (j + 2 * k + 1)).e =
      eichler Q (P (j + 2 * k)).e (P (j + 2 * k + 1)).e * eichlerPairProd P j k := by
  have hfix : ∀ i', (i' = j + 2 * k ∨ i' = j + 2 * k + 1) →
      eichlerPairProd P j k (P i').e = (P i').e := by
    intro i' hi'
    exact eichlerPairProd_apply_of_polar fun i hi1 hi2 =>
      (hP i' i (by omega) (by omega) (by omega)).ee
  exact commute_eichler_of_fix (eichlerPairProd_mem_orthogonalGroup P j k) (hfix _ (Or.inl rfl))
    (hfix _ (Or.inr rfl))

private theorem eichlerPairProd_fix_next {P : ℕ → HypPair Q} {r j k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : j + 2 * (k + 1) ≤ r) :
    eichlerPairProd P j k (P (j + 2 * k)).e = (P (j + 2 * k)).e ∧
      eichlerPairProd P j k (P (j + 2 * k)).f = (P (j + 2 * k)).f ∧
      eichlerPairProd P j k (P (j + 2 * k + 1)).e = (P (j + 2 * k + 1)).e ∧
      eichlerPairProd P j k (P (j + 2 * k + 1)).f = (P (j + 2 * k + 1)).f := by
  have hfix : ∀ i', (i' = j + 2 * k ∨ i' = j + 2 * k + 1) →
      eichlerPairProd P j k (P i').e = (P i').e ∧ eichlerPairProd P j k (P i').f = (P i').f :=
    fun i' hi' => ⟨eichlerPairProd_apply_of_polar fun i hi1 hi2 =>
        (hP i' i (by omega) (by omega) (by omega)).ee,
      eichlerPairProd_apply_of_polar fun i hi1 hi2 =>
        (hP i' i (by omega) (by omega) (by omega)).fe⟩
  exact ⟨(hfix _ (Or.inl rfl)).1, (hfix _ (Or.inl rfl)).2, (hfix _ (Or.inr rfl)).1,
    (hfix _ (Or.inr rfl)).2⟩

private theorem commSpace_eichler_eq_span [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0)
    (hli : LinearIndependent K ![u, w]) :
    commSpace (eichler Q u w) = Submodule.span K {u, w} ∧
      finrank K (commSpace (eichler Q u w)) = 2 := by
  have heq : commSpace (eichler Q u w) = Submodule.span K {u, w} :=
    le_antisymm (commSpace_eichler_le_span u w) (span_le_commSpace_eichler hQ hu hw hli)
  refine ⟨heq, ?_⟩
  have h2 := finrank_span_eq_card hli
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at h2
  rw [heq, h2]

variable [CharP K 2]

private theorem eichler_mul_self_of_charTwo (u w : V) : eichler Q u w * eichler Q u w = 1 := by
  by_cases hw : polar Q u w = 0
  · rw [eichler_mul hw hw, ← two_smul K w, CharTwo.two_eq_zero, zero_smul, eichler_zero_right]
  · rw [eichler_of_polar_ne_zero hw, one_mul]

theorem eichlerPairProd_mul_self {P : ℕ → HypPair Q} {r j k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : j + 2 * k ≤ r) :
    eichlerPairProd P j k * eichlerPairProd P j k = 1 := by
  induction k with
  | zero => rw [eichlerPairProd_zero, mul_one]
  | succ k ih =>
    have hc := eichlerPairProd_commute_next hP hk
    rw [eichlerPairProd_succ]
    set s := eichlerPairProd P j k
    set E := eichler Q (P (j + 2 * k)).e (P (j + 2 * k + 1)).e
    calc s * E * (s * E) = s * (E * s) * E := by group
      _ = s * (s * E) * E := by rw [hc]
      _ = s * s * (E * E) := by group
      _ = 1 := by rw [ih (by omega), eichler_mul_self_of_charTwo, mul_one]

theorem eichler_mul_eichlerPairProd_mul_self {P : ℕ → HypPair Q} {r k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : 2 * k + 1 ≤ r) {a₁ : V}
    (hperp : ∀ i < r, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0) :
    eichler Q (P 0).e a₁ * eichlerPairProd P 1 k * (eichler Q (P 0).e a₁ * eichlerPairProd P 1 k) =
      1 := by
  have h0 : eichlerPairProd P 1 k (P 0).e = (P 0).e :=
    eichlerPairProd_apply_of_polar fun i hi1 hi2 => (hP 0 i (by omega) (by omega) (by omega)).ee
  have h1 : eichlerPairProd P 1 k a₁ = a₁ :=
    eichlerPairProd_apply_of_polar fun i hi1 hi2 => by
      rw [polar_comm]
      exact (hperp i (by omega)).1
  have hc := commute_eichler_of_fix (eichlerPairProd_mem_orthogonalGroup P 1 k) h0 h1
  set A := eichler Q (P 0).e a₁
  set B := eichlerPairProd P 1 k
  calc A * B * (A * B) = A * (B * A) * B := by group
    _ = A * (A * B) * B := by rw [hc]
    _ = A * A * (B * B) := by group
    _ = 1 := by
      rw [eichler_mul_self_of_charTwo, eichlerPairProd_mul_self hP (by omega), mul_one]

omit [CharP K 2] in
private theorem polar_commSpace_fixed {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hx : x ∈ commSpace s)
    (hy : s y = y) : polar Q x y = 0 := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  rw [polar_sub_left, ← hy, polar_map_of_mem hs, hy, sub_self]

omit [CharP K 2] in
private theorem eichler_sub_mem_span (e e' v : V) :
    eichler Q e e' v - v ∈ Submodule.span K {e, e'} := by
  obtain ⟨a, b, h⟩ := eichler_apply_eq_add (Q := Q) e e' v
  rw [h, add_assoc, add_sub_cancel_left]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

omit [CharP K 2] in
private theorem apply_eq_of_mem_span_pair {s : V ≃ₗ[K] V} {e e' z : V} (he : s e = e)
    (he' : s e' = e') (hz : z ∈ Submodule.span K {e, e'}) : s z = z := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [map_add, map_smul, map_smul, he, he']

omit [CharP K 2] in
private theorem commSpace_mul_eichler_eq_sup {s : V ≃ₗ[K] V} {P P' : HypPair Q}
    (hPP' : P.Orth P') (hfix : s P.e = P.e ∧ s P.f = P.f ∧ s P'.e = P'.e ∧ s P'.f = P'.f) :
    commSpace (s * eichler Q P.e P'.e) = commSpace s ⊔ Submodule.span K {P.e, P'.e} := by
  obtain ⟨he, hf, he', hf'⟩ := hfix
  have hdecomp : ∀ v, (s * eichler Q P.e P'.e) v - v =
      (s v - v) + (eichler Q P.e P'.e v - v) := fun v => by
    have h := apply_eq_of_mem_span_pair he he' (eichler_sub_mem_span (Q := Q) P.e P'.e v)
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [LinearEquiv.mul_apply, h]
    abel
  have hEf : eichler Q P.e P'.e P.f - P.f = P'.e := by
    rw [eichler_apply P.Q_e hPP'.ee, P.polar_fe, hPP'.fe, P'.Q_e]
    module
  have hEf' : eichler Q P.e P'.e P'.f - P'.f = -P.e := by
    rw [eichler_apply P.Q_e hPP'.ee, polar_comm Q P'.f P.e, hPP'.ef, P'.polar_fe, P'.Q_e]
    module
  have he'mem : P'.e ∈ commSpace (s * eichler Q P.e P'.e) := by
    have h := sub_mem_commSpace (s * eichler Q P.e P'.e) P.f
    rwa [hdecomp, hf, sub_self, zero_add, hEf] at h
  have hemem : P.e ∈ commSpace (s * eichler Q P.e P'.e) := by
    have h := sub_mem_commSpace (s * eichler Q P.e P'.e) P'.f
    rw [hdecomp, hf', sub_self, zero_add, hEf'] at h
    simpa using Submodule.neg_mem _ h
  have hspan_le : Submodule.span K {P.e, P'.e} ≤ commSpace (s * eichler Q P.e P'.e) := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hemem
    · exact he'mem
  apply le_antisymm
  · intro y hy
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    rw [hdecomp]
    exact Submodule.add_mem_sup (sub_mem_commSpace s v) (eichler_sub_mem_span P.e P'.e v)
  · refine sup_le ?_ hspan_le
    intro y hy
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    have h := sub_mem_commSpace (s * eichler Q P.e P'.e) v
    rw [hdecomp] at h
    simpa using Submodule.sub_mem _ h (hspan_le (eichler_sub_mem_span (Q := Q) P.e P'.e v))

omit [CharP K 2] in
private theorem disjoint_commSpace_span {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {P P' : HypPair Q} (hPP' : P.Orth P')
    (hf : s P.f = P.f) (hf' : s P'.f = P'.f) :
    Disjoint (commSpace s) (Submodule.span K {P.e, P'.e}) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 := polar_commSpace_fixed hs hx hf
  have h2 := polar_commSpace_fixed hs hx hf'
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx'
  simp only [polar_add_left, polar_smul_left, P.polar_ef, hPP'.ef, polar_comm Q P'.e P.f,
    hPP'.fe, P'.polar_ef, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  rw [h1, h2, zero_smul, zero_smul, add_zero]

omit [CharP K 2] in
private theorem finrank_span_orth_e_eq_two [FiniteDimensional K V] {P P' : HypPair Q}
    (hPP' : P.Orth P') : finrank K (Submodule.span K {P.e, P'.e}) = 2 := by
  have hli : LinearIndependent K ![P.e, P'.e] := by
    rw [LinearIndependent.pair_iff]
    intro α β h
    have h1 := congrArg (fun v => polar Q v P.f) h
    have h2 := congrArg (fun v => polar Q v P'.f) h
    simp only [polar_add_left, polar_smul_left, P.polar_ef, hPP'.ef, polar_comm Q P'.e P.f,
      hPP'.fe, P'.polar_ef, polar_zero_left, smul_eq_mul, mul_one, mul_zero, add_zero,
      zero_add] at h1 h2
    exact ⟨h1, h2⟩
  have h2 := finrank_span_eq_card hli
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at h2
  exact h2

omit [CharP K 2] in
theorem finrank_commSpace_mul_eichler_of_fix [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {P P' : HypPair Q} (hPP' : P.Orth P')
    (hfix : s P.e = P.e ∧ s P.f = P.f ∧ s P'.e = P'.e ∧ s P'.f = P'.f) :
    finrank K (commSpace (s * eichler Q P.e P'.e)) = finrank K (commSpace s) + 2 ∧
      ((∀ x ∈ commSpace (s * eichler Q P.e P'.e), Q x = 0) ↔ ∀ x ∈ commSpace s, Q x = 0) := by
  have hsup := commSpace_mul_eichler_eq_sup hPP' hfix
  have hdis := disjoint_commSpace_span hs hPP' hfix.2.1 hfix.2.2.2
  have hQspan : ∀ z ∈ Submodule.span K {P.e, P'.e}, Q z = 0 := by
    intro z hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P.Q_e, P'.Q_e,
      polar_smul_left, polar_smul_right, hPP'.ee]
    simp
  refine ⟨?_, ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq (commSpace s)
      (Submodule.span K {P.e, P'.e})
    rw [hdis.eq_bot, finrank_bot, add_zero, ← hsup, finrank_span_orth_e_eq_two hPP'] at h
    exact h
  · rw [hsup]
    constructor
    · intro h x hx
      exact h x (Submodule.mem_sup_left hx)
    · intro h x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      have h1 := polar_commSpace_fixed hs hy hfix.1
      have h2 := polar_commSpace_fixed hs hy hfix.2.2.1
      have hyz : polar Q y z = 0 := by
        obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
        rw [polar_add_right, polar_smul_right, polar_smul_right, h1, h2]
        simp
      rw [QuadraticMap.map_add Q, h y hy, hQspan z hz, hyz, add_zero, add_zero]

omit [CharP K 2] in
theorem commSpace_eichlerPairProd [FiniteDimensional K V] {P : ℕ → HypPair Q} {r j k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : j + 2 * k ≤ r) :
    finrank K (commSpace (eichlerPairProd P j k)) = 2 * k ∧
      ∀ x ∈ commSpace (eichlerPairProd P j k), Q x = 0 := by
  induction k with
  | zero =>
    have h1 : commSpace (eichlerPairProd P j 0) = ⊥ := by
      rw [eichlerPairProd_zero, eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
      rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]
    refine ⟨by rw [h1, finrank_bot], fun x hx => ?_⟩
    rw [h1, Submodule.mem_bot] at hx
    rw [hx, map_zero]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨h1, h2⟩ := finrank_commSpace_mul_eichler_of_fix
      (eichlerPairProd_mem_orthogonalGroup P j k)
      (hP (j + 2 * k) (j + 2 * k + 1) (by omega) (by omega) (by omega))
      (eichlerPairProd_fix_next hP hk)
    rw [eichlerPairProd_succ]
    exact ⟨by rw [h1, ih1]; ring, h2.2 ih2⟩

omit [CharP K 2] in
theorem commSpace_eichler_mul_eichlerPairProd [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P : ℕ → HypPair Q} {r k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : 2 * k + 1 ≤ r) {a₁ : V}
    (ha₁ : Q a₁ ≠ 0) (hperp : ∀ i < r, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0) :
    finrank K (commSpace (eichler Q (P 0).e a₁ * eichlerPairProd P 1 k)) = 2 * k + 2 ∧
      ∃ x ∈ commSpace (eichler Q (P 0).e a₁ * eichlerPairProd P 1 k), Q x ≠ 0 := by
  induction k with
  | zero =>
    rw [eichlerPairProd_zero, mul_one]
    have ha0 : a₁ ≠ 0 := fun h => ha₁ (by rw [h, map_zero])
    have hli : LinearIndependent K ![(P 0).e, a₁] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hs : s = 0 := by
        have h := congrArg (fun v => polar Q v (P 0).f) hst
        simp only [polar_add_left, polar_smul_left, (P 0).polar_ef, polar_zero_left,
          polar_comm Q a₁ (P 0).f, (hperp 0 (by omega)).2, smul_eq_mul, mul_one, mul_zero,
          add_zero] at h
        exact h
      rw [hs, zero_smul, zero_add] at hst
      exact ⟨hs, (smul_eq_zero.mp hst).resolve_right ha0⟩
    obtain ⟨heq, hfin⟩ :=
      commSpace_eichler_eq_span hQ (P 0).Q_e (hperp 0 (by omega)).1 hli
    exact ⟨hfin, a₁, by rw [heq]; exact Submodule.subset_span (by simp), ha₁⟩
  | succ k ih =>
    obtain ⟨ih1, x, hx, hQx⟩ := ih (by omega)
    have hfix : ∀ i', 1 ≤ i' → i' < r →
        eichler Q (P 0).e a₁ (P i').e = (P i').e ∧ eichler Q (P 0).e a₁ (P i').f = (P i').f := by
      intro i' h1 h2
      have hO := hP i' 0 h2 (by omega) (by omega)
      exact ⟨eichler_apply_of_polar_eq_zero hO.ee (hperp i' h2).1,
        eichler_apply_of_polar_eq_zero hO.fe (hperp i' h2).2⟩
    have hnext := eichlerPairProd_fix_next (j := 1) (k := k) hP (by omega)
    have hs : eichler Q (P 0).e a₁ * eichlerPairProd P 1 k ∈
        TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem (eichler_mem_orthogonalGroup Q _ _) (eichlerPairProd_mem_orthogonalGroup P 1 k)
    obtain ⟨h1, h2⟩ := finrank_commSpace_mul_eichler_of_fix hs
      (hP (1 + 2 * k) (1 + 2 * k + 1) (by omega) (by omega) (by omega))
      ⟨by rw [LinearEquiv.mul_apply, hnext.1, (hfix _ (by omega) (by omega)).1],
        by rw [LinearEquiv.mul_apply, hnext.2.1, (hfix _ (by omega) (by omega)).2],
        by rw [LinearEquiv.mul_apply, hnext.2.2.1, (hfix _ (by omega) (by omega)).1],
        by rw [LinearEquiv.mul_apply, hnext.2.2.2, (hfix _ (by omega) (by omega)).2]⟩
    rw [eichlerPairProd_succ, ← mul_assoc]
    refine ⟨by rw [h1, ih1]; ring, ?_⟩
    by_contra hall
    push Not at hall
    exact hQx (h2.1 hall x hx)

omit [CharP K 2] in
private theorem exists_nat_family {r : ℕ} (hr : 0 < r) (P : Fin r → HypPair Q) :
    ∃ P' : ℕ → HypPair Q, ∀ i (h : i < r), P' i = P ⟨i, h⟩ :=
  ⟨fun i => if h : i < r then P ⟨i, h⟩ else P ⟨0, hr⟩, fun _ h => dif_pos h⟩

omit [CharP K 2] in
private theorem exists_rootCFrame_of_pairs {m : ℕ} (hm2 : 2 ≤ m) {P : Fin m → HypPair Q}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ (P : ℕ → HypPair Q) (a₁ a₂ : V),
      (∀ i i', i < m - 1 → i' < m - 1 → i ≠ i' → (P i).Orth (P i')) ∧ Q a₁ = 1 ∧
        polar Q a₁ a₂ = 1 ∧
        ∀ i < m - 1, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
          polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0 := by
  obtain ⟨P', hP'⟩ := exists_nat_family (by omega) P
  set L := P ⟨m - 1, by omega⟩
  refine ⟨P', L.e + L.f, L.f, fun i i' hi hi' hne => ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [hP' i (by omega), hP' i' (by omega)]
    exact hP _ _ fun h => hne (congrArg Fin.val h)
  · rw [QuadraticMap.map_add Q, L.Q_e, L.Q_f, L.polar_ef, zero_add, zero_add]
  · rw [polar_add_left, L.polar_ef, L.polar_ff, add_zero]
  · have O := hP ⟨i, by omega⟩ ⟨m - 1, by omega⟩ fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [hP' i (by omega), polar_add_right, polar_add_right, O.ee, O.ef, O.fe, O.ff, add_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩

omit [CharP K 2] in
private theorem exists_rootCFrame_of_aniso {r : ℕ} (hr : 0 < r) {P : Fin r → HypPair Q}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : V}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hu : Q u = 1) (hne : polar Q u v ≠ 0) :
    ∃ (P : ℕ → HypPair Q) (a₁ a₂ : V),
      (∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) ∧ Q a₁ = 1 ∧
        polar Q a₁ a₂ = 1 ∧
        ∀ i < r, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
          polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0 := by
  obtain ⟨P', hP'⟩ := exists_nat_family hr P
  refine ⟨P', u, (polar Q u v)⁻¹ • v, fun i i' hi hi' hne' => ?_, hu, ?_, fun i hi => ?_⟩
  · rw [hP' i hi, hP' i' hi']
    exact hP _ _ fun h => hne' (congrArg Fin.val h)
  · rw [polar_smul_right_eq, inv_mul_cancel₀ hne]
  · obtain ⟨hu1, hu2⟩ := HypPair.mem_perp.mp (huv ⟨i, hi⟩).1
    obtain ⟨hv1, hv2⟩ := HypPair.mem_perp.mp (huv ⟨i, hi⟩).2
    rw [hP' i hi, polar_smul_right_eq, polar_smul_right_eq, hv1, hv2, mul_zero]
    exact ⟨hu1, hu2, rfl, rfl⟩

theorem exists_rootCFrame [Finite K] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : finrank K V = 2 * m) (hm2 : 2 ≤ m) :
    ∃ (P : ℕ → HypPair Q) (a₁ a₂ : V),
      (∀ i i', i < m - 1 → i' < m - 1 → i ≠ i' → (P i).Orth (P i')) ∧ Q a₁ = 1 ∧
        polar Q a₁ a₂ = 1 ∧
        ∀ i < m - 1, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
          polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0 := by
  rcases CFSG.ComponentClassification.UnbalancedCatalog.exists_hypPairs_normal m ⊤
      (polarNondegOn_top hQ) (by rw [finrank_top, hm]) with
    ⟨P, -, hP⟩ | ⟨r, hr, P, u, v, -, hP, -, -, huv, hu, hne, -⟩
  · exact exists_rootCFrame_of_pairs hm2 hP
  · obtain rfl : r = m - 1 := by omega
    exact exists_rootCFrame_of_aniso (by omega) hP huv hu hne

end CFSG.ClassicalGroups.Orthogonal

module

public import CFSG.LieType.Steinberg.CentralExt.HalfSpaceLift
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
public import CFSG.LieType.Steinberg.Adjoint.Datum

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ExceptionalCover
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.AdjointClosed

attribute [local instance] TorusLift.centerCommGroup

variable {τ : Tag} {K : Type} [Field K]

theorem zpow_sum_eq_prod {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

@[expose] def tvec (w : Kˣ) (m : Fin τ.rank → ℤ) : Fin τ.rank → Kˣ := fun k => w ^ m k

theorem rootChar_tvec (w : Kˣ) (m β : Fin τ.rank → ℤ) :
    rootChar K β (tvec w m) = w ^ ∑ k, m k * cartanCoord β k := by
  rw [rootChar_apply, zpow_sum_eq_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  change (w ^ m k) ^ cartanCoord β k = _
  rw [← zpow_mul]

theorem cartanCoord_reflect (i k : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    cartanCoord (reflect τ i β) k = cartanCoord β k - cartanCoord β i * τ.cartan k i := by
  simp only [cartanCoord, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

theorem reflect_mem_span (i : Fin τ.rank) (x : Fin τ.rank → ℤ) (k : Fin τ.rank) :
    reflect τ i x k ∈ Ideal.span (Set.range x) := by
  rw [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact Ideal.sub_mem _ (Ideal.subset_span ⟨k, rfl⟩) (Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))

section Lift

variable {G : Type*} [Group G] {k : Type} [Field k] {x : (Fin τ.rank → ℤ) → k → G}
  (hx : ∀ γ, IsRoot τ γ → ∀ c d, x γ (c + d) = x γ c * x γ d)
  (T : (Fin τ.rank → kˣ) →* G)
  (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
    T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
  {E : Type*} [Group E] {π : E →* G}

variable (x π) in
@[expose] def IsRootLift (γ : Fin τ.rank → ℤ) (Y : k → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = x γ s) ∧
    ∀ (t : Fin τ.rank → kˣ) (e : E), π e = T t →
      ∀ s, e * Y s * e⁻¹ = Y ((rootChar k γ t : k) * s)

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen hT in
theorem commPairing_eq_zero [Finite k] (hk4 : Nat.card k ≠ 4) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {m : Fin τ.rank → ℤ} (hm : ∑ j, m j * cartanCoord γ j = 1) :
    TorusLift.commPairing hcen hπ (hx γ hγ) = 0 := by
  obtain ⟨p, _, _⟩ := TorusLift.exists_prime_charP (k := k)
  refine Pairing.pairing_eq_zero_of_units p hk4 (TorusLift.commPairing_self hcen hπ _)
    fun u hu s t => TorusLift.commPairing_smul hcen hπ (hx γ hγ)
      (g := T (tvec (Units.mk0 u hu) m)) (fun c => ?_) s t
  rw [hT _ γ hγ, rootChar_tvec, hm, zpow_one, Units.val_mk0]

include hx hcen hπ hT in
theorem exists_isRootLift [Finite k] (hk4 : Nat.card k ≠ 4) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {m : Fin τ.rank → ℤ} (hm : ∑ j, m j * cartanCoord γ j = 1) {w : kˣ}
    (hw : w ≠ 1) : ∃ Y : k → E, IsRootLift x T π γ Y := by
  have hg : ∀ s, T (tvec w m) * x γ s * (T (tvec w m))⁻¹ = x γ ((w : k) * s) := fun s => by
    rw [hT _ γ hγ, rootChar_tvec, hm, zpow_one]
  have hw' : (w : k) ≠ 1 := fun h => hw (Units.val_eq_one.1 h)
  exact ⟨TorusLift.canonLift hπ (x := x γ) (T (tvec w m)) (w : k),
    TorusLift.canonLift_add hcen hπ (hx γ hγ) (commPairing_eq_zero hx T hT hcen hπ hk4 hγ hm) hg
      hw',
    TorusLift.map_canonLift hπ (hx γ hγ) hg hw',
    fun t _e he s => TorusLift.conj_canonLift hcen hπ
      (by rw [← map_mul T, mul_comm t, map_mul, mul_inv_cancel_right])
      (fun s' => hT t γ hγ s') he s⟩

variable (x π) in
open _root_.Classical in
@[expose] noncomputable def X (γ : Fin τ.rank → ℤ) : k → E :=
  if h : ∃ Y : k → E, IsRootLift x T π γ Y then h.choose else fun _ => 1

theorem X_isRootLift {γ : Fin τ.rank → ℤ} (h : ∃ Y : k → E, IsRootLift x T π γ Y) :
    IsRootLift x T π γ (X x T π γ) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

end Lift

theorem cartanCoord_reflect_mem_span (i : Fin τ.rank) (x : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    cartanCoord (reflect τ i x) j ∈ Ideal.span (Set.range (cartanCoord x)) := by
  rw [cartanCoord_reflect]
  exact Ideal.sub_mem _ (Ideal.subset_span ⟨j, rfl⟩)
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem span_range_eq_top {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    Ideal.span (Set.range γ) = ⊤ := by
  induction hγ with
  | basis j => exact (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨j, by simp⟩)
  | @reflect i v _ ih =>
    rw [eq_top_iff, ← ih, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have h := reflect_mem_span i (reflect τ i v) k
    rwa [reflect_reflect] at h

open Matrix in
theorem exists_unitVec {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : τ.cartan * B = 1)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ m : Fin τ.rank → ℤ, ∑ k, m k * cartanCoord γ k = 1 := by
  obtain ⟨n, hn⟩ := Ideal.mem_span_range_iff_exists_fun.1
    ((Ideal.eq_top_iff_one _).1 (span_range_eq_top hγ))
  have hBA : B * τ.cartan = 1 := mul_eq_one_comm.1 hB
  refine ⟨n ᵥ* B, ?_⟩
  change n ᵥ* B ⬝ᵥ (τ.cartan *ᵥ γ) = 1
  rw [dotProduct_mulVec, vecMul_vecMul, hBA, vecMul_one]
  exact hn

theorem span_range_cartanCoord_eq_top (hnb : ∀ j, ∃ i, τ.cartan i j = -1)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : Ideal.span (Set.range (cartanCoord γ)) = ⊤ := by
  induction hγ with
  | basis j =>
    obtain ⟨i, hi⟩ := hnb j
    have h : cartanCoord (Pi.single j 1 : Fin τ.rank → ℤ) i = -1 := by
      simp [cartanCoord, Pi.single_apply, hi]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, h⟩) isUnit_one.neg
  | @reflect i v _ ih =>
    rw [eq_top_iff, ← ih, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h := cartanCoord_reflect_mem_span i (reflect τ i v) j
    rwa [reflect_reflect] at h

theorem exists_unitVec_of_neighbour (hnb : ∀ j, ∃ i, τ.cartan i j = -1)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1 :=
  Ideal.mem_span_range_iff_exists_fun.1
    ((Ideal.eq_top_iff_one _).1 (span_range_cartanCoord_eq_top hnb hγ))


variable (K) in
@[expose] noncomputable def torusAdj (t : Fin τ.rank → Kˣ) : adjointGroup τ K :=
  ⟨torusVec τ K t, torusVec_mem_adjointGroup t⟩

theorem torusAdj_one : torusAdj K (1 : Fin τ.rank → Kˣ) = 1 :=
  Subtype.ext (map_one _)

theorem torusAdj_mul (t t' : Fin τ.rank → Kˣ) :
    torusAdj K (t * t') = torusAdj K t * torusAdj K t' :=
  Subtype.ext (map_mul _ _ _)

theorem torusAdj_commute (t t' : Fin τ.rank → Kˣ) : Commute (torusAdj K t) (torusAdj K t') := by
  change torusAdj K t * torusAdj K t' = torusAdj K t' * torusAdj K t
  rw [← torusAdj_mul, ← torusAdj_mul, mul_comm]

theorem torusAdj_mulSingle (k : Fin τ.rank) (s : Kˣ) :
    torusAdj K (Pi.mulSingle k s) = torusElement τ K k s :=
  Subtype.ext (torusVec_mulSingle k s)

@[expose] def IsCorootVec (γ m : Fin τ.rank → ℤ) : Prop :=
  ∀ β, iform γ γ * ∑ k, m k * cartanCoord β k = 2 * iform γ β

theorem exists_isCorootVec {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : ∃ m, IsCorootVec γ m := by
  induction hγ with
  | basis j =>
    refine ⟨Pi.single j 1, fun β => ?_⟩
    rw [iform_single_single, iform_single_left]
    have e : ∑ k, (Pi.single j 1 : Fin τ.rank → ℤ) k * cartanCoord β k = cartanCoord β j := by
      simp [Pi.single_apply]
    rw [e, cartanCoord]
    ring
  | @reflect i v _ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨fun k => m k - (∑ l, m l * τ.cartan l i) * (Pi.single i 1 : Fin τ.rank → ℤ) k,
      fun β => ?_⟩
    have e1 : iform (reflect τ i v) β = iform v (reflect τ i β) := by
      conv_lhs => rw [← reflect_reflect τ i β]
      exact iform_reflect i v (reflect τ i β)
    have e2 : ∑ k, (m k - (∑ l, m l * τ.cartan l i) * (Pi.single i 1 : Fin τ.rank → ℤ) k) *
          cartanCoord β k = ∑ k, m k * cartanCoord (reflect τ i β) k := by
      simp only [cartanCoord_reflect, sub_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [iform_reflect, e1, e2, hm]

theorem IsCorootVec.self {γ m : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hm : IsCorootVec γ m) :
    ∑ k, m k * cartanCoord γ k = 2 := by
  have hpos : 0 < iform γ γ := iform_self_pos hγ.ne_zero
  have h : iform γ γ * ∑ k, m k * cartanCoord γ k = iform γ γ * 2 := by
    rw [hm γ]
    ring
  exact mul_left_cancel₀ hpos.ne' h

theorem exists_sep {w : Kˣ} (hw : 4 ≤ orderOf w) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hli : LinIndepPair γ δ) :
    ∃ t : Fin τ.rank → Kˣ, rootChar K γ t = 1 ∧ rootChar K δ t ≠ 1 := by
  obtain ⟨mγ, hmγ⟩ := exists_isCorootVec hγ
  obtain ⟨mδ, hmδ⟩ := exists_isCorootVec hδ
  obtain ⟨a, ha⟩ : ∃ a, ∑ k, mδ k * cartanCoord γ k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, ∑ k, mγ k * cartanCoord δ k = b := ⟨_, rfl⟩
  have hNγ : 0 < iform γ γ := iform_self_pos hγ.ne_zero
  have hNδ : 0 < iform δ δ := iform_self_pos hδ.ne_zero
  have h2γ := hmγ.self hγ
  have h2δ := hmδ.self hδ
  have hA : iform δ δ * a = 2 * iform γ δ := by rw [← ha, hmδ γ, iform_comm]
  have hB : iform γ γ * b = 2 * iform γ δ := by rw [← hb, hmγ δ]
  have hpow : ∀ e : ℤ, 0 < e → e < 4 → w ^ e ≠ 1 := fun e he1 he4 h => by
    have := Int.le_of_dvd he1 (orderOf_dvd_iff_zpow_eq_one.2 h)
    omega
  by_cases hs : iform γ δ = 0
  · have ha0 : a = 0 := by
      have h0 : iform δ δ * a = 0 := by rw [hA, hs, mul_zero]
      exact (mul_eq_zero.1 h0).resolve_left hNδ.ne'
    refine ⟨tvec w mδ, ?_, ?_⟩
    · rw [rootChar_tvec, ha, ha0, zpow_zero]
    · rw [rootChar_tvec, h2δ]
      exact hpow 2 (by norm_num) (by norm_num)
  · have hne : γ ≠ δ := fun h => by
      have := hli 1 (-1) (by rw [h]; simp)
      omega
    have hne' : γ ≠ -δ := fun h => by
      have := hli 1 1 (by rw [h]; simp)
      omega
    have hcs := iform_sq_lt hγ hδ hne hne'
    have hab : iform γ γ * iform δ δ * (a * b) = 4 * iform γ δ ^ 2 := by
      have h' : (iform δ δ * a) * (iform γ γ * b) = (2 * iform γ δ) * (2 * iform γ δ) := by
        rw [hA, hB]
      linear_combination h'
    have hsq : 0 < iform γ δ ^ 2 := by positivity
    have hN : 0 < iform γ γ * iform δ δ := mul_pos hNγ hNδ
    have hab0 : 0 < a * b := by
      by_contra hle
      have hle' : a * b ≤ 0 := not_lt.1 hle
      nlinarith
    have hab4 : a * b < 4 := by nlinarith
    refine ⟨tvec w fun k => 2 * mδ k - a * mγ k, ?_, ?_⟩
    · rw [rootChar_tvec]
      have e : ∑ k, (2 * mδ k - a * mγ k) * cartanCoord γ k = 2 * a - a * 2 := by
        simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [ha, h2γ]
      rw [e, show 2 * a - a * 2 = 0 by ring, zpow_zero]
    · rw [rootChar_tvec]
      have e : ∑ k, (2 * mδ k - a * mγ k) * cartanCoord δ k = 4 - a * b := by
        simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [h2δ, hb]
        ring
      rw [e]
      exact hpow _ (by omega) (by omega)

variable {F : RootOperatorFamily τ}

theorem torusAdj_conj_xPar (t : Fin τ.rank → Kˣ) (γ : Fin τ.rank → ℤ) (c : K) :
    torusAdj K t * xPar F γ c * (torusAdj K t)⁻¹ = xPar F γ ((rootChar K γ t : K) * c) := by
  by_cases hγ : IsRoot τ γ
  · induction t using torusVec_induction generalizing c with
    | h1 => rw [torusAdj_one, map_one, Units.val_one, one_mul, one_mul, inv_one, mul_one]
    | hmul t t' ht ht' =>
      have e : torusAdj K (t * t') * xPar F γ c * (torusAdj K (t * t'))⁻¹ =
          torusAdj K t * (torusAdj K t' * xPar F γ c * (torusAdj K t')⁻¹) * (torusAdj K t)⁻¹ := by
        rw [torusAdj_mul]
        group
      rw [e, ht', ht, map_mul, Units.val_mul, mul_assoc]
    | hsingle k s =>
      rw [torusAdj_mulSingle, xPar_of_isRoot hγ, xPar_of_isRoot hγ,
        F.torusElement_mul_eltElement_mul_inv, rootChar_mulSingle]
      rfl
  · rw [xPar_of_not_isRoot hγ, xPar_of_not_isRoot hγ, mul_one, mul_inv_cancel]

@[expose] noncomputable def torusAdjHom : (Fin τ.rank → Kˣ) →* adjointGroup τ K where
  toFun := torusAdj K
  map_one' := torusAdj_one
  map_mul' := torusAdj_mul


abbrev tagDatum (τ : Tag) {G : Type*} [Group G] (hA : TauCeti.IsFiniteType τ.cartan)
    (RG : (Fin τ.rank → ℤ) → Subgroup G) : UniversalRootDatum G where
  rank := τ.rank
  cartan := τ.cartan
  isFiniteType := hA
  divisible := ∅
  rootGroup := RG

theorem exists_section_of_torus_of_sep {G : Type*} [Group G]
    (hA : TauCeti.IsFiniteType τ.cartan) {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k]
    [Finite k] (hk4 : Nat.card k ≠ 4) {w : kˣ} (hw1 : w ≠ 1)
    {x : (Fin τ.rank → ℤ) → k → G} {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hprim : ∀ γ, IsRoot τ γ → ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1)
    (hsep : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → LinIndepPair γ δ →
      ∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1)
    {E : Type*} [Group E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  have hmem : ∀ {γ}, γ ∈ (tagDatum τ hA RG).roots → IsRoot τ γ := fun {γ} hγ => by
    rw [hroots] at hγ
    exact hγ
  have hx : ∀ γ, IsRoot τ γ → ∀ c d, x γ (c + d) = x γ c * x γ d := fun γ hγ => by
    have hγ' : γ ∈ (tagDatum τ hA RG).roots := by
      rw [hroots]
      exact hγ
    exact (hE.param γ hγ').2.1
  have hspec : ∀ γ ∈ (tagDatum τ hA RG).roots, IsRootLift x T π γ (X x T π γ) := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ (hmem hγ)
    exact X_isRootLift T (exists_isRootLift hx T hT hcen hπ hk4 (hmem hγ) hm hw1)
  refine HalfSpaceLift.exists_section_of_lift hcen rfl hE hP (X := X x T π)
    (tor := fun t : Fin τ.rank → kˣ => TorusLift.lift hπ (T t))
    (χ := fun t γ => (rootChar k γ t : k)) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun t γ hγ c => (hspec γ hγ).2.2 t _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  obtain ⟨t, h1, h2⟩ := hsep γ δ (hmem hγ) (hmem hδ) hli
  exact ⟨t, by rw [h1, Units.val_one], fun h => h2 (Units.val_eq_one.1 h)⟩

theorem exists_section_of_torus {G : Type*} [Group G] (hA : TauCeti.IsFiniteType τ.cartan)
    {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k] [Finite k] (hk : 5 ≤ Nat.card k)
    {x : (Fin τ.rank → ℤ) → k → G} {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hprim : ∀ γ, IsRoot τ γ → ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1)
    {E : Type*} [Group E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : G →* E, ∀ g, π (σ g) = g := by
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := kˣ)
  have hw4 : 4 ≤ orderOf w := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_units]
    omega
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw4
    omega
  exact exists_section_of_torus_of_sep hA (by omega) hw1 hroots hE hP T hT hprim
    (fun γ δ hγ hδ hli => exists_sep hw4 hγ hδ hli) hπ hcen

theorem exists_section_of_central (F : RootOperatorFamily τ) [Finite K] (hK : 5 ≤ Nat.card K)
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : τ.cartan * B = 1)
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (adjDatum F K).isFiniteType (adjDatum F K).divisible)}
    (hE : ChevalleyExtras (adjDatum F K) K (xPar F) C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan (adjDatum F K).isFiniteType
      (adjDatum F K).divisible) (xPar (K := K) F))
    {E : Type*} [Group E] {π : E →* adjointGroup τ K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : adjointGroup τ K →* E, ∀ g, π (σ g) = g :=
  exists_section_of_torus (isFiniteType_cartan τ) (RG := rootGroup F K) hK (adjDatum_roots F K) hE
    hP torusAdjHom (fun t γ _ c => torusAdj_conj_xPar t γ c) (fun _ hγ => exists_unitVec hB hγ)
    hπ hcen

end CFSG.LieType.Steinberg.CentralExt.AdjointClosed

module

public import CFSG.CharacterTheory.Semidihedral.Principal.KleinFourSylowBrauerFiber
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace FreeSix

variable {G : Type*} [Group G]

@[reducible, expose] def cT (t : G) : Subgroup G :=
  Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)

@[reducible, expose] def dV (V : Subgroup G) : Subgroup G := Subgroup.centralizer (V : Set G)

@[reducible, expose] def mV (V : Subgroup G) : Subgroup G := Subgroup.normalizer (V : Set G)

@[reducible, expose] def vInM (V : Subgroup G) : Subgroup (mV V) := V.subgroupOf (mV V)

@[reducible, expose] def dInM (V : Subgroup G) : Subgroup (mV V) :=
  Subgroup.centralizer ((vInM V : Subgroup (mV V)) : Set (mV V))

@[reducible, expose] def eInM (V E : Subgroup G) : Subgroup (mV V) := E.subgroupOf (mV V)

@[reducible, expose] def vInC (V : Subgroup G) (t : G) : Subgroup (cT t) := V.subgroupOf (cT t)

@[reducible, expose] def dInC (V : Subgroup G) (t : G) : Subgroup (cT t) :=
  Subgroup.centralizer ((vInC V t : Subgroup (cT t)) : Set (cT t))

@[reducible, expose] def kInC (V : Subgroup G) (t : G) : Subgroup (cT t) :=
  Subgroup.normalizer ((vInC V t : Subgroup (cT t)) : Set (cT t))

@[reducible, expose] def vInK (V : Subgroup G) (t : G) : Subgroup (kInC V t) :=
  (vInC V t).subgroupOf (kInC V t)

@[reducible, expose] def dInK (V : Subgroup G) (t : G) : Subgroup (kInC V t) :=
  Subgroup.centralizer ((vInK V t : Subgroup (kInC V t)) : Set (kInC V t))

@[reducible, expose] def eInK (V E : Subgroup G) (t : G) : Subgroup (kInC V t) :=
  (E.subgroupOf (cT t)).subgroupOf (kInC V t)

section Groups

variable {V : Subgroup G} (hV : IsKleinFour V)
include hV

theorem isPGroup_two : IsPGroup 2 V :=
  IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)

theorem le_dV : V ≤ dV V :=
  OrbitIdempotents.le_centralizer_self_of_comm V (KleinFourFiber.kleinFour_comm hV)

omit hV in
theorem le_mV : V ≤ mV V := Subgroup.le_normalizer

omit hV in
theorem dV_le_mV : dV V ≤ mV V := Subgroup.centralizer_le_normalizer _

theorem le_cT {t : G} (htV : t ∈ V) : V ≤ cT t :=
  KleinFourFiber.le_centralizer_zpowers hV htV

omit hV in
theorem dV_le_cT {t : G} (htV : t ∈ V) : dV V ≤ cT t :=
  Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htV)

theorem comm (a : G) (ha : a ∈ V) (b : G) (hb : b ∈ V) : a * b = b * a :=
  KleinFourFiber.kleinFour_comm hV a ha b hb

theorem mul_self {t : G} (htV : t ∈ V) : t * t = 1 := by
  have : IsKleinFour V := hV
  exact congrArg Subtype.val (IsKleinFour.mul_self (⟨t, htV⟩ : V))

end Groups

theorem mem_kInC_iff {V : Subgroup G} {t : G} (hVC : V ≤ cT t) (x : cT t) :
    x ∈ kInC V t ↔ (x : G) ∈ mV V := by
  constructor
  · exact KleinFourFiber.mem_normalizer_of_subgroupOf hVC x
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hx) y

theorem factorization_two_pow_mul {a k : ℕ} (hk : Odd k) : (2 ^ a * k).factorization 2 = a := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hk)
  rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) hk0, Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hk)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem exists_sylow_card_eight {H : Type*} [Group H] [Finite H] {k : ℕ} (hk : Odd k)
    (hcard : Nat.card H = 8 * k) : ∃ Q : Sylow 2 H, Nat.card (Q : Subgroup H) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 H))
  refine ⟨Q, ?_⟩
  rw [Q.card_eq_multiplicity, hcard, show 8 * k = 2 ^ 3 * k by norm_num,
    factorization_two_pow_mul hk]
  norm_num

section Index

variable {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)

include hED in
theorem le_mV_of_le_dV : E ≤ mV V := hED.trans dV_le_mV

include hV hED hDVE in
theorem conj_mem_of_mem [Finite G] (hEodd : Odd (Nat.card E)) {m : G} (hm : m ∈ mV V) {e : G}
    (he : e ∈ E) : m * e * m⁻¹ ∈ E := by
  have hx : m * e * m⁻¹ ∈ dV V := (centralizer_conjugation_mem_iff V m e hm).mpr (hED he)
  obtain ⟨v, hv, e', he', hve⟩ := hDVE _ hx
  set k := Nat.card E
  have hek : e ^ k = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := E) (x := ⟨e, he⟩))
    exact h
  have he'k : e' ^ k = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := E) (x := ⟨e', he'⟩))
    exact h
  have hcomm : Commute v e' := (Subgroup.mem_centralizer_iff.mp (hED he')) v hv
  have hv2 : v * v = 1 := mul_self hV hv
  have hvk : v ^ k = v := by
    obtain ⟨j, hj⟩ := hEodd
    rw [hj, pow_succ, pow_mul, sq, hv2, one_pow, one_mul]
  have hpow : (m * e * m⁻¹) ^ k = 1 := by
    rw [conj_pow, hek, mul_one, mul_inv_cancel]
  rw [hve, hcomm.mul_pow, hvk, he'k, mul_one] at hpow
  rw [hve, hpow, one_mul]
  exact he'

include hV hED hVE hDVE in
theorem card_dV : Nat.card (dV V) = 4 * Nat.card E := by
  rw [FourGroupParity.card_centralizer_eq V E (comm hV) hED hVE hDVE, hV.card_four]

include hV in
theorem index_dV (hAut : Function.Surjective V.normalizerMonoidHom) :
    ((dV V).subgroupOf (mV V)).index = 6 := by
  have : IsKleinFour V := hV
  rw [← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hAut, Subgroup.card_top]
  exact CFSG.GorensteinWalter.kleinFourAut_card V

@[expose, instance_reducible] noncomputable def conjAction (V : Subgroup G) :
    MulAction (mV V) V :=
  MulAction.compHom V V.normalizerMonoidHom

include hV in
theorem index_cT_subgroupOf (hAut : Function.Surjective V.normalizerMonoidHom) {t : G}
    (htV : t ∈ V) (ht1 : t ≠ 1) [Finite G] :
    ((cT t).subgroupOf (mV V)).index = 3 := by
  have : IsKleinFour V := hV
  let := conjAction V
  set t' : V := ⟨t, htV⟩
  have hstab : MulAction.stabilizer (mV V) t' = (cT t).subgroupOf (mV V) := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (m : G) * t * (m : G)⁻¹ = t := congrArg Subtype.val h
      apply DihedralAssociates.mem_centralizer_zpowers_of_commute
      calc (m : G) * t = (m : G) * t * (m : G)⁻¹ * m := by group
        _ = t * m := by rw [h']
    · intro h
      apply Subtype.ext
      change (m : G) * t * (m : G)⁻¹ = t
      rw [(Subgroup.mem_centralizer_iff.mp h t (Subgroup.mem_zpowers t)).symm, mul_inv_cancel_right]
  have horbit : MulAction.orbit (mV V) t' = {v : V | v ≠ 1} := by
    ext u
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, rfl⟩ h1
      apply ht1
      have h' : (m : G) * t * (m : G)⁻¹ = 1 := congrArg Subtype.val h1
      exact conj_eq_one_iff.mp h'
    · intro hu
      have ht1' : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
      let σ : V ≃* V := IsKleinFour.mulEquiv (Equiv.swap t' u)
        (Equiv.swap_apply_of_ne_of_ne ht1'.symm hu.symm)
      obtain ⟨m, hm⟩ := hAut σ
      refine ⟨m, ?_⟩
      change V.normalizerMonoidHom m t' = u
      rw [hm]
      exact Equiv.swap_apply_left t' u
  have h3 : (MulAction.orbit (mV V) t').ncard = 3 := by
    rw [horbit, ← Nat.card_coe_set_eq]
    exact FourGroupParity.card_nonidentity (H := G) V hV
  rw [← hstab, MulAction.index_stabilizer, h3]

include hV in
theorem relIndex_dV_cT (hAut : Function.Surjective V.normalizerMonoidHom) {t : G}
    (htV : t ∈ V) (ht1 : t ≠ 1) [Finite G] :
    ((dV V).subgroupOf (mV V)).relIndex ((cT t).subgroupOf (mV V)) = 2 := by
  have hle : (dV V).subgroupOf (mV V) ≤ (cT t).subgroupOf (mV V) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (dV_le_cT htV (Subgroup.mem_subgroupOf.mp hx))
  have h := Subgroup.relIndex_mul_index hle
  rw [index_dV hV hAut, index_cT_subgroupOf hV hAut htV ht1] at h
  omega

@[expose] def kInCEquiv {V : Subgroup G} {t : G} (hVC : V ≤ cT t) :
    kInC V t ≃* (cT t).subgroupOf (mV V) where
  toFun x := ⟨⟨((x : cT t) : G), (mem_kInC_iff hVC x).mp x.2⟩, (x : cT t).2⟩
  invFun y := ⟨⟨((y : mV V) : G), y.2⟩, (mem_kInC_iff hVC _).mpr (y : mV V).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

include hV hED hVE hDVE in
theorem card_mV (hAut : Function.Surjective V.normalizerMonoidHom) [Finite G] :
    Nat.card (mV V) = 8 * (3 * Nat.card E) := by
  have h := Subgroup.card_mul_index ((dV V).subgroupOf (mV V))
  rw [index_dV hV hAut, Nat.card_congr (Subgroup.subgroupOfEquivOfLe dV_le_mV).toEquiv,
    card_dV hV hED hVE hDVE] at h
  rw [← h]
  ring

include hV hED hVE hDVE in
theorem card_kInC (hAut : Function.Surjective V.normalizerMonoidHom) {t : G} (htV : t ∈ V)
    (ht1 : t ≠ 1) [Finite G] : Nat.card (kInC V t) = 8 * Nat.card E := by
  rw [Nat.card_congr (kInCEquiv (le_cT hV htV)).toEquiv]
  have h := Subgroup.card_mul_index ((cT t).subgroupOf (mV V))
  rw [index_cT_subgroupOf hV hAut htV ht1, card_mV hV hED hVE hDVE hAut] at h
  omega

end Index

theorem exists_three_orbits {K X : Type*} [Group K] [MulAction K X] (Ω : Set X)
    (hΩ : Ω.ncard = 6) (hfin : Ω.Finite) (hinv : ∀ (k : K) (x : X), x ∈ Ω → k • x ∈ Ω)
    (h2 : ∀ x ∈ Ω, (MulAction.orbit K x).ncard = 2) :
    ∃ x : Fin 3 → X, (∀ j, x j ∈ Ω) ∧
      (∀ j k, j ≠ k → Disjoint (MulAction.orbit K (x j)) (MulAction.orbit K (x k))) ∧
      Ω = ⋃ j, MulAction.orbit K (x j) := by
  have hsub : ∀ x ∈ Ω, MulAction.orbit K x ⊆ Ω := by
    rintro x hx _ ⟨k, rfl⟩
    exact hinv k x hx
  have hfinO : ∀ x ∈ Ω, (MulAction.orbit K x).Finite := fun x hx => hfin.subset (hsub x hx)
  have hdisj : ∀ x y : X, y ∉ MulAction.orbit K x →
      Disjoint (MulAction.orbit K x) (MulAction.orbit K y) := by
    intro x y hy
    rw [Set.disjoint_left]
    intro z hzx hzy
    apply hy
    rw [← MulAction.orbit_eq_iff.mpr hzx, MulAction.orbit_eq_iff.mpr hzy]
    exact MulAction.mem_orbit_self y
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero (s := Ω) (by rw [hΩ]; norm_num)
  have h₁ : (Ω \ MulAction.orbit K x₀).ncard = 4 := by
    rw [Set.ncard_sdiff (hsub x₀ hx₀) (hfinO x₀ hx₀), hΩ, h2 x₀ hx₀]
  obtain ⟨x₁, hx₁Ω, hx₁O⟩ := Set.nonempty_of_ncard_ne_zero
    (s := Ω \ MulAction.orbit K x₀) (by rw [h₁]; norm_num)
  have hd₀₁ := hdisj x₀ x₁ hx₁O
  have hU₁ : (MulAction.orbit K x₀ ∪ MulAction.orbit K x₁).ncard = 4 := by
    rw [Set.ncard_union_eq hd₀₁ (hfinO x₀ hx₀) (hfinO x₁ hx₁Ω), h2 x₀ hx₀, h2 x₁ hx₁Ω]
  have hU₁sub : MulAction.orbit K x₀ ∪ MulAction.orbit K x₁ ⊆ Ω :=
    Set.union_subset (hsub x₀ hx₀) (hsub x₁ hx₁Ω)
  have h₂ : (Ω \ (MulAction.orbit K x₀ ∪ MulAction.orbit K x₁)).ncard = 2 := by
    rw [Set.ncard_sdiff hU₁sub ((hfinO x₀ hx₀).union (hfinO x₁ hx₁Ω)), hΩ, hU₁]
  obtain ⟨x₂, hx₂Ω, hx₂O⟩ := Set.nonempty_of_ncard_ne_zero
    (s := Ω \ (MulAction.orbit K x₀ ∪ MulAction.orbit K x₁)) (by rw [h₂]; norm_num)
  have hd₀₂ := hdisj x₀ x₂ (fun h => hx₂O (Or.inl h))
  have hd₁₂ := hdisj x₁ x₂ (fun h => hx₂O (Or.inr h))
  have hU : MulAction.orbit K x₀ ∪ MulAction.orbit K x₁ ∪ MulAction.orbit K x₂ = Ω := by
    apply Set.eq_of_subset_of_ncard_le (Set.union_subset hU₁sub (hsub x₂ hx₂Ω)) _ hfin
    rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩)
      ((hfinO x₀ hx₀).union (hfinO x₁ hx₁Ω)) (hfinO x₂ hx₂Ω), hU₁, h2 x₂ hx₂Ω, hΩ]
  refine ⟨![x₀, x₁, x₂], fun j => ?_, fun j k hjk => ?_, ?_⟩
  · fin_cases j
    · exact hx₀
    · exact hx₁Ω
    · exact hx₂Ω
  · fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd rfl hjk
      | exact hd₀₁ | exact hd₀₂ | exact hd₁₂
      | exact hd₀₁.symm | exact hd₀₂.symm | exact hd₁₂.symm
  · rw [← hU]
    ext y
    simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, IsEmpty.exists_iff, or_false]
    tauto

@[expose] def linearOrbit (E : Subgroup G) (ν : E →* ℂˣ) (X : Set G) : Set (E →* ℂˣ) :=
  {ν' | ∃ x ∈ X, ∀ e e' : E, (e' : G) = x⁻¹ * e * x → ν' e = ν e'}

section Orbits

variable [Finite G] {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (hEodd : Odd (Nat.card E))

@[expose] def oddConj (m : mV V) : E →* E where
  toFun e := ⟨(m : G)⁻¹ * e * m, by
    have h := conj_mem_of_mem hV hED hDVE hEodd ((mV V).inv_mem m.2) e.2
    rwa [inv_inv] at h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem oddConj_apply (m : mV V) (e : E) :
    (oddConj hV hED hDVE hEodd m e : G) = (m : G)⁻¹ * e * m := rfl

@[expose, instance_reducible] def linearAction : MulAction (mV V) (E →* ℂˣ) where
  smul m ν := ν.comp (oddConj hV hED hDVE hEodd m)
  one_smul ν := MonoidHom.ext fun e => by
    change ν (oddConj hV hED hDVE hEodd 1 e) = ν e
    congr 1
    apply Subtype.ext
    rw [oddConj_apply]
    simp
  mul_smul m₁ m₂ ν := MonoidHom.ext fun e => by
    change ν (oddConj hV hED hDVE hEodd (m₁ * m₂) e) =
      ν (oddConj hV hED hDVE hEodd m₂ (oddConj hV hED hDVE hEodd m₁ e))
    congr 1
    apply Subtype.ext
    rw [oddConj_apply, oddConj_apply, oddConj_apply, Subgroup.coe_mul]
    group

theorem linearAction_apply (m : mV V) (ν : E →* ℂˣ) (e : E) :
    (@HSMul.hSMul _ _ _ (@instHSMul _ _ (linearAction hV hED hDVE hEodd).toSMul) m ν) e =
      ν (oddConj hV hED hDVE hEodd m e) := rfl

theorem mem_linearOrbit_iff (L : Subgroup (mV V)) (μ ν : E →* ℂˣ) :
    ν ∈ linearOrbit E μ ((L.map (mV V).subtype : Subgroup G) : Set G) ↔
      ∃ l : L, (@HSMul.hSMul _ _ _ (@instHSMul _ _ (linearAction hV hED hDVE hEodd).toSMul)
        (l : mV V) μ) = ν := by
  constructor
  · rintro ⟨x, ⟨m, hmL, rfl⟩, hx⟩
    refine ⟨⟨m, hmL⟩, ?_⟩
    refine MonoidHom.ext fun e => ?_
    rw [linearAction_apply, hx e (oddConj hV hED hDVE hEodd m e) (oddConj_apply _ _ _ _ m e)]
  · rintro ⟨⟨m, hmL⟩, rfl⟩
    refine ⟨m, ⟨m, hmL, rfl⟩, fun e e' he' => ?_⟩
    rw [linearAction_apply]
    congr 1
    apply Subtype.ext
    rw [oddConj_apply, he']

variable (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)

include hωV in
theorem stabilizer_restrict
    (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V) :
    @MulAction.stabilizer (mV V) (E →* ℂˣ) _ (linearAction hV hED hDVE hEodd)
      (ω.comp (Subgroup.inclusion hED)) = (dV V).subgroupOf (mV V) := by
  let := linearAction hV hED hDVE hEodd
  ext m
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    apply hωstab m m.2
    intro x y hy
    obtain ⟨v, hv, e, he, hx⟩ := hDVE x x.2
    have hv' : (m : G)⁻¹ * v * m ∈ V := by
      have h' := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem m.2) v).mp hv
      rwa [inv_inv] at h'
    set e' := oddConj hV hED hDVE hEodd m ⟨e, he⟩
    have hy' : y = (⟨(m : G)⁻¹ * v * m, le_dV hV hv'⟩ : dV V) * ⟨e', hED e'.2⟩ := by
      apply Subtype.ext
      change (y : G) = (m : G)⁻¹ * v * m * ((m : G)⁻¹ * e * m)
      rw [hy, hx]
      group
    have hx' : x = (⟨v, le_dV hV hv⟩ : dV V) * ⟨e, hED he⟩ := Subtype.ext hx
    have hμ := congrArg (fun f : E →* ℂˣ => f ⟨e, he⟩) h
    change ω.comp (Subgroup.inclusion hED) e' = ω.comp (Subgroup.inclusion hED) ⟨e, he⟩ at hμ
    rw [hy', hx', map_mul, map_mul, hωV ⟨(m : G)⁻¹ * v * m, le_dV hV hv'⟩ hv',
      hωV ⟨v, le_dV hV hv⟩ hv, one_mul, one_mul]
    exact hμ
  · intro hm
    refine MonoidHom.ext fun e => ?_
    obtain ⟨v₀, hv₀, e₀, he₀, hm'⟩ := hDVE _ hm
    have hcomm : (e : G) * v₀ = v₀ * e :=
      (Subgroup.mem_centralizer_iff.mp (hED e.2) v₀ hv₀).symm
    have hconj : oddConj hV hED hDVE hEodd m e = (⟨e₀, he₀⟩ : E)⁻¹ * e * ⟨e₀, he₀⟩ := by
      apply Subtype.ext
      rw [oddConj_apply, hm']
      change (v₀ * e₀)⁻¹ * e * (v₀ * e₀) = e₀⁻¹ * e * e₀
      calc (v₀ * e₀)⁻¹ * e * (v₀ * e₀) = e₀⁻¹ * v₀⁻¹ * ((e : G) * v₀) * e₀ := by group
        _ = e₀⁻¹ * e * e₀ := by rw [hcomm]; group
    change ω.comp (Subgroup.inclusion hED) (oddConj hV hED hDVE hEodd m e) = _
    rw [hconj, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

include hV hED hDVE hEodd hωV in
theorem orbit_structure
    (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {t : G} (htV : t ∈ V) (ht1 : t ≠ 1) :
    (linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)).ncard = 6 ∧
    ∃ μs : Fin 3 → (E →* ℂˣ),
      (∀ j, μs j ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)) ∧
      (∀ j, (linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G)).ncard = 2) ∧
      (∀ j k, j ≠ k → Disjoint (linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G))
        (linearOrbit E (μs k) ((cT t ⊓ mV V : Subgroup G) : Set G))) ∧
      linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G) =
        ⋃ j, linearOrbit E (μs j) ((cT t ⊓ mV V : Subgroup G) : Set G) := by
  let := linearAction hV hED hDVE hEodd
  set μ := ω.comp (Subgroup.inclusion hED)
  set L : Subgroup (mV V) := (cT t).subgroupOf (mV V)
  have htop : ((⊤ : Subgroup (mV V)).map (mV V).subtype : Subgroup G) = mV V := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hLmap : (L.map (mV V).subtype : Subgroup G) = cT t ⊓ mV V :=
    Subgroup.subgroupOf_map_subtype _ _
  have hΩ : linearOrbit E μ (mV V : Set G) = MulAction.orbit (mV V) μ := by
    ext ν
    have h := mem_linearOrbit_iff hV hED hDVE hEodd ⊤ μ ν
    rw [htop] at h
    rw [h, MulAction.mem_orbit_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, hl⟩, fun ⟨m, hm⟩ => ⟨⟨m, Subgroup.mem_top m⟩, hm⟩⟩
  have hLorbit : ∀ ν, linearOrbit E ν ((cT t ⊓ mV V : Subgroup G) : Set G) =
      MulAction.orbit L ν := by
    intro ν
    ext ν'
    have h := mem_linearOrbit_iff hV hED hDVE hEodd L ν ν'
    rw [hLmap] at h
    rw [h, MulAction.mem_orbit_iff]
    rfl
  have hstab := stabilizer_restrict hV hED hDVE hEodd ω hωV hωstab
  have hcard : (MulAction.orbit (mV V) μ).ncard = 6 := by
    rw [← MulAction.index_stabilizer, hstab, index_dV hV hAut]
  have hDnormal : ((dV V).subgroupOf (mV V)).Normal :=
    KleinFourFiber.centralizer_subgroupOf_normalizer_normal V
  have hstabν : ∀ ν ∈ MulAction.orbit (mV V) μ,
      MulAction.stabilizer (mV V) ν = (dV V).subgroupOf (mV V) := by
    rintro ν ⟨m, rfl⟩
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, hstab]
    exact Subgroup.Normal.map_conj_eq ((dV V).subgroupOf (mV V)) m
  have hL2 : ∀ ν ∈ MulAction.orbit (mV V) μ, (MulAction.orbit L ν).ncard = 2 := by
    intro ν hν
    rw [← MulAction.index_stabilizer]
    have hLstab : MulAction.stabilizer L ν = (MulAction.stabilizer (mV V) ν).subgroupOf L := by
      ext l
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
      rfl
    rw [hLstab, hstabν ν hν]
    exact relIndex_dV_cT hV hAut htV ht1
  have hfin : (MulAction.orbit (mV V) μ).Finite := Set.finite_range _
  obtain ⟨x, hxΩ, hdisj, hunion⟩ := exists_three_orbits (K := L) (MulAction.orbit (mV V) μ)
    hcard hfin (fun l ν hν => by
      obtain ⟨m, rfl⟩ := hν
      exact ⟨(l : mV V) * m, mul_smul (l : mV V) m μ⟩) hL2
  refine ⟨hΩ ▸ hcard, x, fun j => hΩ ▸ hxΩ j, fun j => (hLorbit (x j)).symm ▸ hL2 (x j) (hxΩ j),
    fun j k hjk => ?_, ?_⟩
  · rw [hLorbit, hLorbit]
    exact hdisj j k hjk
  · rw [hΩ, hunion]
    exact Set.iUnion_congr fun j => (hLorbit (x j)).symm

end Orbits

section Levels

variable {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V) (hVE : V ⊓ E = ⊥)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e)

omit [Group G] in
theorem mem_dInM_iff {G : Type*} [Group G] {V : Subgroup G} (x : mV V) :
    x ∈ dInM V ↔ (x : G) ∈ dV V :=
  KleinFourFiber.mem_centralizer_subgroupOf_iff le_mV x

include hED in
theorem eInM_le_dInM : eInM V E ≤ dInM V := fun x hx => (mem_dInM_iff x).mpr (hED hx)

include hVE in
theorem vInM_inf_eInM : vInM V ⊓ eInM V E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxE⟩
  have h : (x : G) ∈ V ⊓ E := ⟨hxV, hxE⟩
  rw [hVE, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

include hED hDVE in
theorem decomp_dInM : ∀ w ∈ dInM V, ∃ a ∈ vInM V, ∃ x ∈ eInM V E, w = a * x := by
  intro w hw
  obtain ⟨v, hv, e, he, hwve⟩ := hDVE _ ((mem_dInM_iff w).mp hw)
  exact ⟨⟨v, le_mV hv⟩, hv, ⟨e, le_mV_of_le_dV hED he⟩, he, Subtype.ext hwve⟩

include hV in
theorem comm_vInM : ∀ a ∈ vInM V, ∀ b ∈ vInM V, a * b = b * a := fun a ha b hb =>
  Subtype.ext (comm hV a ha b hb)

include hV in
theorem isKleinFour_vInM : IsKleinFour (vInM V) :=
  KleinFourFiber.isKleinFour_subgroupOf hV le_mV

include hV in
theorem isPGroup_vInM : IsPGroup 2 (vInM V) := (isPGroup_two hV).comap_subtype

omit [Group G] in
instance vInM_normal {G : Type*} [Group G] {V : Subgroup G} : (vInM V).Normal :=
  Subgroup.normal_in_normalizer

include hED in
theorem card_eInM : Nat.card (eInM V E) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_mV_of_le_dV hED)).toEquiv

variable {t : G} (htV : t ∈ V)

omit [Group G] in
theorem vInC_le_kInC {G : Type*} [Group G] {V : Subgroup G} {t : G} : vInC V t ≤ kInC V t :=
  Subgroup.le_normalizer

include hV htV in
theorem mem_dInK_iff (x : kInC V t) : x ∈ dInK V t ↔ ((x : cT t) : G) ∈ dV V :=
  (KleinFourFiber.mem_centralizer_subgroupOf_iff vInC_le_kInC x).trans
    (KleinFourFiber.mem_centralizer_subgroupOf_iff (le_cT hV htV) _)

include hV htV in
theorem mem_dInC_iff (x : cT t) : x ∈ dInC V t ↔ (x : G) ∈ dV V :=
  KleinFourFiber.mem_centralizer_subgroupOf_iff (le_cT hV htV) x

include hED htV in
theorem le_cT_of_le_dV : E ≤ cT t := hED.trans (dV_le_cT htV)

include hV hED htV in
theorem eInC_le_kInC : E.subgroupOf (cT t) ≤ kInC V t := fun x hx =>
  (mem_kInC_iff (le_cT hV htV) x).mpr (le_mV_of_le_dV hED hx)

include hV hED htV in
theorem eInK_le_dInK : eInK V E t ≤ dInK V t := fun x hx => (mem_dInK_iff hV htV x).mpr (hED hx)

include hVE in
theorem vInK_inf_eInK : vInK V t ⊓ eInK V E t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxE⟩
  have h : ((x : cT t) : G) ∈ V ⊓ E := ⟨hxV, hxE⟩
  rw [hVE, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h))

include hV hED hDVE htV in
theorem decomp_dInK : ∀ w ∈ dInK V t, ∃ a ∈ vInK V t, ∃ x ∈ eInK V E t, w = a * x := by
  intro w hw
  obtain ⟨v, hv, e, he, hwve⟩ := hDVE _ ((mem_dInK_iff hV htV w).mp hw)
  refine ⟨⟨⟨v, le_cT hV htV hv⟩, (mem_kInC_iff (le_cT hV htV) _).mpr (le_mV hv)⟩, hv,
    ⟨⟨e, le_cT_of_le_dV hED htV he⟩, eInC_le_kInC hV hED htV he⟩, he, ?_⟩
  exact Subtype.ext (Subtype.ext hwve)

include hV htV in
theorem isKleinFour_vInK : IsKleinFour (vInK V t) :=
  KleinFourFiber.isKleinFour_subgroupOf (KleinFourFiber.isKleinFour_subgroupOf hV (le_cT hV htV))
    vInC_le_kInC

include hV in
theorem isPGroup_vInK : IsPGroup 2 (vInK V t) := (isPGroup_two hV).comap_subtype.comap_subtype

include hV in
theorem isPGroup_vInC : IsPGroup 2 (vInC V t) := (isPGroup_two hV).comap_subtype

include hV htV in
theorem isKleinFour_vInC : IsKleinFour (vInC V t) :=
  KleinFourFiber.isKleinFour_subgroupOf hV (le_cT hV htV)

include hV hED htV in
theorem eInC_le_dInC : E.subgroupOf (cT t) ≤ dInC V t := fun x hx =>
  (mem_dInC_iff hV htV x).mpr (hED hx)

include hVE in
theorem vInC_inf_eInC : vInC V t ⊓ E.subgroupOf (cT t) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxV, hxE⟩
  have h : (x : G) ∈ V ⊓ E := ⟨hxV, hxE⟩
  rw [hVE, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

include hV hED hDVE htV in
theorem decomp_dInC : ∀ w ∈ dInC V t, ∃ a ∈ vInC V t, ∃ x ∈ E.subgroupOf (cT t), w = a * x := by
  intro w hw
  obtain ⟨v, hv, e, he, hwve⟩ := hDVE _ ((mem_dInC_iff hV htV w).mp hw)
  exact ⟨⟨v, le_cT hV htV hv⟩, hv, ⟨e, le_cT_of_le_dV hED htV he⟩, he, Subtype.ext hwve⟩

include hV in
theorem comm_vInC : ∀ a ∈ vInC V t, ∀ b ∈ vInC V t, a * b = b * a := fun a ha b hb =>
  Subtype.ext (comm hV a ha b hb)

include hED htV in
theorem card_eInC : Nat.card (E.subgroupOf (cT t)) = Nat.card E :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_cT_of_le_dV hED htV)).toEquiv

omit [Group G] in
instance vInK_normal {G : Type*} [Group G] {V : Subgroup G} {t : G} : (vInK V t).Normal :=
  Subgroup.normal_in_normalizer

include hV hED htV in
theorem card_eInK : Nat.card (eInK V E t) = Nat.card E := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (eInC_le_kInC hV hED htV)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_cT_of_le_dV hED htV)).toEquiv]

include hV hED hVE hDVE in
theorem exists_sylow_mV [Finite G] (hEodd : Odd (Nat.card E))
    (hAut : Function.Surjective V.normalizerMonoidHom) :
    ∃ Q : Sylow 2 (mV V), Nat.card (Q : Subgroup (mV V)) = 8 :=
  exists_sylow_card_eight (Nat.odd_mul.mpr ⟨by decide, hEodd⟩) (card_mV hV hED hVE hDVE hAut)

include hV hED hVE hDVE htV in
theorem exists_sylow_kInC [Finite G] (hEodd : Odd (Nat.card E))
    (hAut : Function.Surjective V.normalizerMonoidHom) (ht1 : t ≠ 1) :
    ∃ Q : Sylow 2 (kInC V t), Nat.card (Q : Subgroup (kInC V t)) = 8 :=
  exists_sylow_card_eight hEodd (card_kInC hV hED hVE hDVE hAut htV ht1)

end Levels

section Labels

@[expose] def AffordsInflation {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (ι : X → G) (V : Subgroup G) {E : Subgroup G}
    (ν : E →* ℂˣ) (n : basis.index) : Prop :=
  ∀ (x : X) (v : G) (e : E), v ∈ V → ι x = v * e → (basis.representation n).character x = ν e

theorem affordsInflation_iff_of_labelTransport {X Y : Type*} [Group X] [Fintype X] [Group Y]
    [Fintype Y] (bX : FiniteIrreducibleCharacterBasis X) (bY : FiniteIrreducibleCharacterBasis Y)
    (f : X ≃* Y) (ιX : X → G) (ιY : Y → G) (hι : ∀ x, ιY (f x) = ιX x) (V : Subgroup G)
    {E : Subgroup G} (ν : E →* ℂˣ) {n : bX.index} {n' : bY.index}
    (h : CFSG.Wreathed.BlockOrbits.LabelTransport bX bY f n n') :
    AffordsInflation bX ιX V ν n ↔ AffordsInflation bY ιY V ν n' := by
  constructor
  · intro hn y v e hv hy
    obtain ⟨x, rfl⟩ := f.surjective y
    rw [h x]
    exact hn x v e hv ((hι x).symm.trans hy)
  · intro hn' x v e hv hx
    rw [← h x]
    exact hn' (f x) v e hv ((hι x).trans hx)

theorem character_one_of_labelTransport {X Y : Type*} [Group X] [Fintype X] [Group Y]
    [Fintype Y] {bX : FiniteIrreducibleCharacterBasis X} {bY : FiniteIrreducibleCharacterBasis Y}
    {f : X ≃* Y} {n : bX.index} {n' : bY.index}
    (h : CFSG.Wreathed.BlockOrbits.LabelTransport bX bY f n n') :
    (bY.representation n').character 1 = (bX.representation n).character 1 := by
  rw [← map_one f]
  exact h 1

theorem exists_label_of_hom {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (χ : X →* ℂˣ) :
    ∃ n : basis.index, ∀ x, (basis.representation n).character x = χ x := by
  let linear : X →* ℂ := (Units.coeHom ℂ).comp χ
  let data : FiniteComplexRepresentation X :=
    { vector := ℂ, representation := scalarHomRepresentation linear }
  obtain ⟨n, hn⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data
    (representation_complex_line_isIrreducible _)
  refine ⟨n, fun x => ?_⟩
  rw [hn]
  exact congrFun (scalarHomRepresentation_character linear) x

variable [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (hEodd : Odd (Nat.card E))
  (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)

omit [Fintype G] in
@[expose] def dConj {m : G} (hm : m ∈ mV V) : dV V →* dV V where
  toFun x := ⟨m⁻¹ * x * m, by
    have h := (centralizer_conjugation_mem_iff V m⁻¹ x ((mV V).inv_mem hm)).mpr x.2
    rwa [inv_inv] at h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

include hV hDVE hEodd hωV in
theorem exists_affording_label_dV (basisD : FiniteIrreducibleCharacterBasis (dV V))
    {ν : E →* ℂˣ} (hν : ν ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)) :
    ∃ n : basisD.index, AffordsInflation basisD (fun x => (x : G)) V ν n ∧
      (basisD.representation n).character 1 = 1 := by
  obtain ⟨m, hm, hνm⟩ := hν
  obtain ⟨n, hn⟩ := exists_label_of_hom basisD (ω.comp (dConj hm))
  refine ⟨n, fun x v e hv hx => ?_, ?_⟩
  · rw [hn x]
    have hv' : m⁻¹ * v * m ∈ V := by
      have h' := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem hm) v).mp hv
      rwa [inv_inv] at h'
    have he' : m⁻¹ * (e : G) * m ∈ E := by
      have h' := conj_mem_of_mem hV hED hDVE hEodd ((mV V).inv_mem hm) e.2
      rwa [inv_inv] at h'
    have hsplit : dConj hm x = (⟨m⁻¹ * v * m, le_dV hV hv'⟩ : dV V) * ⟨m⁻¹ * e * m, hED he'⟩ := by
      apply Subtype.ext
      change m⁻¹ * (x : G) * m = m⁻¹ * v * m * (m⁻¹ * e * m)
      have hx' : (x : G) = v * e := hx
      rw [hx']
      group
    have hμ := hνm e ⟨m⁻¹ * e * m, he'⟩ rfl
    change ((ω (dConj hm x) : ℂˣ) : ℂ) = (ν e : ℂ)
    rw [hsplit, map_mul, hωV ⟨m⁻¹ * v * m, le_dV hV hv'⟩ hv', one_mul, hμ]
    rfl
  · rw [hn 1, map_one, Units.val_one]

include hV hDVE hEodd hωV in
theorem stabilizer_of_mem_linearOrbit
    (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V)
    {ν : E →* ℂˣ} (hν : ν ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)) :
    @MulAction.stabilizer (mV V) (E →* ℂˣ) _ (linearAction hV hED hDVE hEodd) ν =
      (dV V).subgroupOf (mV V) := by
  let := linearAction hV hED hDVE hEodd
  have htop : ((⊤ : Subgroup (mV V)).map (mV V).subtype : Subgroup G) = mV V := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := mem_linearOrbit_iff hV hED hDVE hEodd ⊤ (ω.comp (Subgroup.inclusion hED)) ν
  rw [htop] at h
  obtain ⟨⟨m, -⟩, rfl⟩ := h.mp hν
  have : ((dV V).subgroupOf (mV V)).Normal :=
    KleinFourFiber.centralizer_subgroupOf_normalizer_normal V
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    stabilizer_restrict hV hED hDVE hEodd ω hωV hωstab]
  exact Subgroup.Normal.map_conj_eq ((dV V).subgroupOf (mV V)) m

end Labels

section LocalLabels

variable [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (hEodd : Odd (Nat.card E))
  {H : Type*} [Group H] [Fintype H] (ρ : H →* G) (hρ : Function.Injective ρ)
  (E' : Subgroup H) (eE : E' ≃* E) (heE : ∀ y, (eE y : G) = ρ y)
  (eb : FiniteIrreducibleCharacterBasis E')

omit [Fintype G] in
include hρ heE in
theorem exists_conjugateLabel_iff (X : Set G) (hX : ∀ g, g ∈ X ↔ ∃ h, ρ h = g)
    (μ ν : E →* ℂˣ) (μ' ν' : eb.index) (hμ' : ∀ y, (eb.representation μ').character y = μ (eE y))
    (hν' : ∀ y, (eb.representation ν').character y = ν (eE y)) :
    (∃ h : H, ConjugateLabel E' eb h μ' ν') ↔ ν ∈ linearOrbit E μ X := by
  constructor
  · rintro ⟨h, hconj⟩
    refine ⟨ρ h, (hX _).mpr ⟨h, rfl⟩, fun e e' he' => ?_⟩
    have hy : ((eE.symm e : E') : H) = h * (eE.symm e' : E') * h⁻¹ := by
      apply hρ
      rw [← heE, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, ← heE,
        MulEquiv.apply_symm_apply, he']
      group
    have hval := hconj (eE.symm e') (eE.symm e) hy
    rw [hν', hμ', MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hval
    exact Units.ext hval
  · rintro ⟨g, hg, hνg⟩
    obtain ⟨h, rfl⟩ := (hX g).mp hg
    refine ⟨h, fun x y hxy => ?_⟩
    rw [hν', hμ']
    have he : ((eE x : E) : G) = (ρ h)⁻¹ * (eE y : G) * ρ h := by
      rw [heE, heE, hxy, map_mul, map_mul, map_inv]
      group
    rw [hνg (eE y) (eE x) he]

include hV hDVE hEodd hρ heE in
theorem conjugateLabel_self_iff (hρM : ∀ h, ρ h ∈ mV V) (μ : E →* ℂˣ) (μ' : eb.index)
    (hμ' : ∀ y, (eb.representation μ').character y = μ (eE y))
    (hstab : @MulAction.stabilizer (mV V) (E →* ℂˣ) _ (linearAction hV hED hDVE hEodd) μ =
      (dV V).subgroupOf (mV V)) (h : H) :
    ConjugateLabel E' eb h μ' μ' ↔ ρ h ∈ dV V := by
  let := linearAction hV hED hDVE hEodd
  set m : mV V := ⟨ρ h, hρM h⟩
  have hmstab : m ∈ MulAction.stabilizer (mV V) μ ↔ ρ h ∈ dV V := by
    rw [hstab, Subgroup.mem_subgroupOf]
  have hinvstab : m⁻¹ ∈ MulAction.stabilizer (mV V) μ ↔ m ∈ MulAction.stabilizer (mV V) μ :=
    ⟨fun hm => by simpa using (MulAction.stabilizer (mV V) μ).inv_mem hm,
      fun hm => (MulAction.stabilizer (mV V) μ).inv_mem hm⟩
  rw [← hmstab, ← hinvstab, MulAction.mem_stabilizer_iff]
  have hconjE : ∀ e : E, (ρ h) * (e : G) * (ρ h)⁻¹ ∈ E := fun e =>
    conj_mem_of_mem hV hED hDVE hEodd (hρM h) e.2
  constructor
  · intro hconj
    refine MonoidHom.ext fun e => ?_
    set y : E' := eE.symm ⟨(ρ h) * e * (ρ h)⁻¹, hconjE e⟩
    have hy : (y : H) = h * (eE.symm e : E') * h⁻¹ := by
      apply hρ
      rw [← heE, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, ← heE,
        MulEquiv.apply_symm_apply]
    have hval := hconj (eE.symm e) y hy
    rw [hμ', hμ', MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hval
    change μ (oddConj hV hED hDVE hEodd m⁻¹ e) = μ e
    have hoc : oddConj hV hED hDVE hEodd m⁻¹ e = ⟨(ρ h) * e * (ρ h)⁻¹, hconjE e⟩ := by
      apply Subtype.ext
      rw [oddConj_apply]
      change (m⁻¹ : G)⁻¹ * e * (m⁻¹ : G) = _
      rw [inv_inv]
    rw [hoc]
    exact Units.ext hval
  · intro hm x y hxy
    rw [hμ', hμ']
    have hval := congrArg (fun f : E →* ℂˣ => (f (eE x) : ℂ)) hm
    change (μ (oddConj hV hED hDVE hEodd m⁻¹ (eE x)) : ℂ) = μ (eE x) at hval
    have hoc : oddConj hV hED hDVE hEodd m⁻¹ (eE x) = eE y := by
      apply Subtype.ext
      rw [oddConj_apply, heE, heE, hxy, map_mul, map_mul, map_inv]
      change ((ρ h)⁻¹)⁻¹ * ρ x * (ρ h)⁻¹ = _
      rw [inv_inv]
    rw [hoc] at hval
    exact hval

end LocalLabels

section Blocks

omit [Group G] in
theorem centralCharacterScalar_embedded_linear {W F : Type*} [Group W] [Fintype W] [Group F]
    [Fintype F] (wb : FiniteIrreducibleCharacterBasis W) (ι : F →* W) (hι : Function.Injective ι)
    (lam : F →* ℂˣ) (n : wb.index) (hn1 : (wb.representation n).character 1 = 1)
    (hn : ∀ y, (wb.representation n).character (ι y) = lam y) :
    centralCharacterScalar wb (MonoidAlgebra.mapDomainRingHom ℂ ι
      (complexCharacterIdempotent fun y => (lam y : ℂ))) n = 1 := by
  set z := MonoidAlgebra.mapDomainRingHom ℂ ι (complexCharacterIdempotent fun y => (lam y : ℂ))
  have hF : (Nat.card F : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hW : (Nat.card W : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hzero : ∀ x : W, x ∉ Set.range ι → z.coeff x * (wb.representation n).character x = 0 :=
    fun x hx => by rw [CFSG.Wreathed.BlockOrbits.embedded_coeff_zero _ _ _ hx, zero_mul]
  have himage : ∀ y : F, z.coeff (ι y) * (wb.representation n).character (ι y) =
      (Nat.card F : ℂ)⁻¹ := by
    intro y
    rw [CFSG.Wreathed.BlockOrbits.embedded_coeff _ hι, complexCharacterIdempotent_coeff, hn,
      map_one, Units.val_one, map_inv, Units.val_inv_eq_inv_val]
    have hy : (lam y : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hsum : ∑ x : W, z.coeff x * (wb.representation n).character x = 1 := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun x _ hx =>
      hzero x fun ⟨y, hy⟩ => hx (Finset.mem_image.mpr ⟨y, Finset.mem_univ y, hy⟩),
      Finset.sum_image fun a _ b _ h => hι h]
    simp only [himage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card]
    field_simp
  have hinv : ∑ x : W, z.coeff x⁻¹ * (wb.representation n).character x⁻¹ =
      ∑ x : W, z.coeff x * (wb.representation n).character x :=
    Fintype.sum_equiv (Equiv.inv W) _ _ fun x => rfl
  unfold centralCharacterScalar characterPairing
  rw [hn1, div_one, hinv, hsum]
  field_simp

variable {H : Type*} [Group H] [Fintype H]

theorem blockIdempotent_eq_of_linear (P E' : Subgroup H)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hEW : E' ≤ Subgroup.centralizer (P : Set H))
    (hPE : P ⊓ E' = ⊥) (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E', w = a * x)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (eb : FiniteIrreducibleCharacterBasis E') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {p : ℕ} [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hPp : IsPGroup p P) (hEp : ¬ p ∣ Nat.card E') (lam : E' →* ℂˣ) (ν : eb.index)
    (hν : ∀ y, (eb.representation ν).character y = lam y) (n : wb.index)
    (hn1 : (wb.representation n).character 1 = 1)
    (hn : ∀ y, (wb.representation n).character (Subgroup.inclusion hEW y) = lam y) :
    characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) n) =
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
        (complexCharacterIdempotent (eb.representation ν).character) := by
  have hiff := OrbitIdempotents.blockIdempotent_eq_iff_mem P E' hPab hEW hPE hW wb eb ideal hPp
    hEp ν n
  unfold OrbitIdempotents.embeddedIdempotent at hiff
  rw [hiff, OrbitIdempotents.mem_idempotentSupport]
  unfold OrbitIdempotents.embeddedIdempotent
  have hfun : (eb.representation ν).character = fun y => (lam y : ℂ) := funext hν
  rw [hfun]
  exact centralCharacterScalar_embedded_linear wb (Subgroup.inclusion hEW)
    (Subgroup.inclusion_injective hEW) lam n hn1 hn

theorem brauer_orbit_block (hb : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (P : Subgroup H) [P.Normal]
    (hP : IsKleinFour P) (hPp : IsPGroup 2 P) (Q : Sylow 2 H)
    (hQ : Nat.card (Q : Subgroup H) = 8) (E' : Subgroup H)
    (hEW : E' ≤ Subgroup.centralizer (P : Set H)) (hEodd : Odd (Nat.card E'))
    (hPE : P ⊓ E' = ⊥) (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E', w = a * x)
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
    (eb : FiniteIrreducibleCharacterBasis E') (μ : eb.index)
    (horbit : Even (Finset.univ.filter fun ν => ∃ h : H, ConjugateLabel E' eb h μ ν).card) :
    ∃ A : hb.index, coefficientBlockDefect hb ideal 2 A P ∧
      ∀ β : wb.index,
        (brauerNormalizerCharacterResidueHom ideal 2 P hPp (Subgroup.centralizer (P : Set H))
            le_rfl (Subgroup.centralizer_le_normalizer _) wb β =
          centralCharacterResidueHom hb ideal A ↔
        ∃ ν : eb.index, (∃ h : H, ConjugateLabel E' eb h μ ν) ∧
          characterSubsetIdempotent wb
              (coefficientBlock wb (localizedComplexIntegerRing ideal) β) =
            MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
              (complexCharacterIdempotent (eb.representation ν).character)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := KleinFourFiber.kleinFour_comm hP
  have hEp : ¬ 2 ∣ Nat.card E' := fun h =>
    (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr h)
  obtain ⟨-, -, -, -, hexists, hevery, -, himage, hBr, -, -⟩ :=
    normal_abelian_p_centralizer_orbit_idempotents hb ideal 2 P hPp hPab E' hEW hEp hPE hW wb eb
  obtain ⟨β₀, hβ₀, -⟩ := hexists μ
  obtain ⟨A, hA⟩ := himage β₀
  obtain ⟨-, hpar⟩ := order_eight_normal_four_group_orbit_defect_parity hb ideal P hP hPp Q hQ E'
    hEW hEodd hPE hW wb eb
  obtain ⟨-, -, heven, -⟩ := hpar A μ β₀ hβ₀ hA
  refine ⟨A, heven horbit, fun β => ?_⟩
  obtain ⟨ν, hν⟩ := hevery β
  constructor
  · intro hβ
    exact ⟨ν, (hBr μ ν β₀ β hβ₀ hν).mp (hA.trans hβ.symm), hν⟩
  · rintro ⟨ν', hconj, hν'⟩
    rw [← (hBr μ ν' β₀ β hβ₀ hν').mpr hconj]
    exact hA

end Blocks

section Level

variable [Fintype G] {V E : Subgroup G} (hV : IsKleinFour V) (hED : E ≤ dV V)
  (hDVE : ∀ x ∈ dV V, ∃ v ∈ V, ∃ e ∈ E, x = v * e) (hEodd : Odd (Nat.card E))
  (ω : dV V →* ℂˣ) (hωV : ∀ x : dV V, (x : G) ∈ V → ω x = 1)
  (hωstab : ∀ m ∈ mV V, (∀ x y : dV V, (y : G) = m⁻¹ * x * m → ω y = ω x) → m ∈ dV V)
  {H : Type*} [Group H] [Fintype H] (ρ : H →* G) (hρ : Function.Injective ρ)
  (hρM : ∀ h, ρ h ∈ mV V) (P : Subgroup H) (hPV : ∀ a, a ∈ P ↔ ρ a ∈ V)
  (E' : Subgroup H) (eE : E' ≃* E) (heE : ∀ y, (eE y : G) = ρ y)
  (hEW : E' ≤ Subgroup.centralizer (P : Set H))
  (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (P : Set H)))
  (φ : Subgroup.centralizer (P : Set H) ≃* dV V) (hφ : ∀ w, (φ w : G) = ρ w)

omit [Fintype G] in
include heE in
theorem affordsInflation_inclusion {ν : E →* ℂˣ} {n : wb.index}
    (hn : AffordsInflation wb (fun w => ρ w) V ν n) (y : E') :
    (wb.representation n).character (Subgroup.inclusion hEW y) = ν (eE y) :=
  hn _ 1 (eE y) V.one_mem (by rw [one_mul, heE]; rfl)

omit [Fintype G] in
theorem affordsInflation_one {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (ι : X → G) (hι : ι 1 = 1) {ν : E →* ℂˣ}
    {n : basis.index} (hn : AffordsInflation basis ι V ν n) :
    (basis.representation n).character 1 = 1 := by
  have h := hn 1 1 1 V.one_mem (by rw [hι, one_mul]; rfl)
  rw [h, map_one, Units.val_one]

include hV hED hDVE hEodd hωV hφ in
theorem exists_affording_label {ν : E →* ℂˣ}
    (hν : ν ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G)) :
    ∃ n : wb.index, AffordsInflation wb (fun w => ρ w) V ν n := by
  obtain ⟨basisD⟩ := finiteIrreducibleCharacterBasis_exists (G := dV V)
  obtain ⟨n₀, hn₀, -⟩ := exists_affording_label_dV hV hED hDVE hEodd ω hωV basisD hν
  obtain ⟨n, hn⟩ := CFSG.Wreathed.BlockOrbits.labelTransport_exists basisD wb φ.symm n₀
  refine ⟨n, (affordsInflation_iff_of_labelTransport basisD wb φ.symm (fun x => (x : G))
    (fun w => ρ w) (fun x => ?_) V ν hn).mp hn₀⟩
  rw [← hφ, MulEquiv.apply_symm_apply]

variable (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hPE : P ⊓ E' = ⊥)
  (hW : ∀ w ∈ Subgroup.centralizer (P : Set H), ∃ a ∈ P, ∃ x ∈ E', w = a * x)
  (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (hPp : IsPGroup 2 P)
  (hEp : ¬ 2 ∣ Nat.card E')

omit [Fintype G] in
include hPab hPE hW hPp hEp heE in
theorem blockIdempotent_of_affordsInflation {ν : E →* ℂˣ} {n : wb.index}
    (hn : AffordsInflation wb (fun w => ρ w) V ν n) :
    characterSubsetIdempotent wb (coefficientBlock wb (localizedComplexIntegerRing ideal) n) =
      MonoidAlgebra.mapDomainRingHom ℂ (Subgroup.inclusion hEW)
        (complexCharacterIdempotent fun y => (ν (eE y) : ℂ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists (G := E')
  obtain ⟨ν', hν'⟩ := exists_label_of_hom eb (ν.comp eE.toMonoidHom)
  have h := blockIdempotent_eq_of_linear P E' hPab hEW hPE hW wb eb ideal hPp hEp
    (ν.comp eE.toMonoidHom) ν' hν' n
    (affordsInflation_one wb (fun w => ρ w) (by simp) hn)
    (fun y => affordsInflation_inclusion ρ P E' eE heE hEW wb hn y)
  rw [h]
  congr 2
  funext y
  exact hν' y

omit [Fintype G] in
include hPab hPE hW hPp hEp heE hEW in
theorem eq_of_sameCoefficientBlock_of_affordsInflation {ν ν' : E →* ℂˣ} {n n' : wb.index}
    (hn : AffordsInflation wb (fun w => ρ w) V ν n)
    (hn' : AffordsInflation wb (fun w => ρ w) V ν' n')
    (hsame : sameCoefficientBlock wb (localizedComplexIntegerRing ideal) n n') : ν = ν' := by
  have h1 := blockIdempotent_of_affordsInflation ρ P E' eE heE hEW wb hPab hPE hW ideal hPp
    hEp hn
  have h2 := blockIdempotent_of_affordsInflation ρ P E' eE heE hEW wb hPab hPE hW ideal hPp
    hEp hn'
  rw [(KleinFourFiber.coefficientBlock_eq_iff wb _ n n').mpr hsame, h2] at h1
  have h3 := MonoidAlgebra.mapDomain_injective (R := ℂ) (Subgroup.inclusion_injective hEW) h1
  refine MonoidHom.ext fun e => Units.ext ?_
  have hc := congrArg (fun z : MonoidAlgebra ℂ E' => z.coeff (eE.symm e)⁻¹) h3
  simp only [complexCharacterIdempotent_coeff, inv_inv, MulEquiv.apply_symm_apply, map_one,
    Units.val_one] at hc
  have hE : (1 : ℂ) / (Nat.card E' : ℂ) ≠ 0 :=
    div_ne_zero one_ne_zero (by exact_mod_cast Nat.card_pos.ne')
  exact (mul_left_cancel₀ hE hc).symm

include hV hED hDVE hEodd hωV hωstab hρ hρM heE hEW hφ hPab hPE hW hPp in
theorem level_block (hb : FiniteIrreducibleCharacterBasis H) [P.Normal] [E'.Normal]
    (hP : IsKleinFour P) (Q : Sylow 2 H) (hQ : Nat.card (Q : Subgroup H) = 8)
    (hEodd' : Odd (Nat.card E')) (X : Set G) (hX : ∀ g, g ∈ X ↔ ∃ h, ρ h = g)
    {μ₀ : E →* ℂˣ} (hμ₀ : μ₀ ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G))
    (hidx : Even ((dV V).comap ρ).index) :
    ∃ A : hb.index, coefficientBlockDefect hb ideal 2 A P ∧
      ∀ n : wb.index,
        (brauerNormalizerCharacterResidueHom ideal 2 P hPp (Subgroup.centralizer (P : Set H))
            le_rfl (Subgroup.centralizer_le_normalizer _) wb n =
          centralCharacterResidueHom hb ideal A ↔
        ∃ ν ∈ linearOrbit E μ₀ X, ∃ n' : wb.index,
          AffordsInflation wb (fun w => ρ w) V ν n' ∧
            sameCoefficientBlock wb (localizedComplexIntegerRing ideal) n' n) := by
  let := linearAction hV hED hDVE hEodd
  have hEp : ¬ 2 ∣ Nat.card E' := fun h =>
    (Nat.not_even_iff_odd.mpr hEodd') (even_iff_two_dvd.mpr h)
  obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists (G := E')
  obtain ⟨μ', hμ'⟩ := exists_label_of_hom eb (μ₀.comp eE.toMonoidHom)
  have hstab := stabilizer_of_mem_linearOrbit hV hED hDVE hEodd ω hωV hωstab hμ₀
  have horbit : Even (Finset.univ.filter fun ν => ∃ h : H, ConjugateLabel E' eb h μ' ν).card := by
    rw [FourGroupParity.card_orbit_eq_index E' eb μ']
    have hls : FourGroupParity.labelStabilizer E' eb μ' = (dV V).comap ρ := by
      ext h
      rw [FourGroupParity.mem_labelStabilizer, Subgroup.mem_comap]
      exact conjugateLabel_self_iff hV hED hDVE hEodd ρ hρ E' eE heE eb hρM μ₀ μ' hμ' hstab h
    rw [hls]
    exact hidx
  obtain ⟨A, hAdef, hAiff⟩ := brauer_orbit_block hb ideal P hP hPp Q hQ E' hEW hEodd' hPE hW wb
    eb μ' horbit
  refine ⟨A, hAdef, fun n => ?_⟩
  rw [hAiff n]
  have hMorbit : ∀ ν, ν ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G) ↔
      ν ∈ MulAction.orbit (mV V) (ω.comp (Subgroup.inclusion hED)) := by
    intro ν
    have htop : ((⊤ : Subgroup (mV V)).map (mV V).subtype : Subgroup G) = mV V := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h := mem_linearOrbit_iff hV hED hDVE hEodd ⊤ (ω.comp (Subgroup.inclusion hED)) ν
    rw [htop] at h
    rw [h, MulAction.mem_orbit_iff]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, hl⟩, fun ⟨m, hm⟩ => ⟨⟨m, Subgroup.mem_top m⟩, hm⟩⟩
  constructor
  · rintro ⟨ν'', ⟨h, hconj⟩, hidem⟩
    set m : mV V := ⟨ρ h, hρM h⟩
    set ν : E →* ℂˣ := m • μ₀
    have hν'' : ∀ y, (eb.representation ν'').character y = ν (eE y) := by
      intro y
      have hx : (h⁻¹ * (y : H) * h) ∈ E' := by
        have hmem := (inferInstance : E'.Normal).conj_mem y y.2 h⁻¹
        rwa [inv_inv] at hmem
      have hval := hconj ⟨h⁻¹ * y * h, hx⟩ y (by group)
      rw [hval, hμ']
      change (μ₀ (eE ⟨h⁻¹ * y * h, hx⟩) : ℂ) = μ₀ (oddConj hV hED hDVE hEodd m (eE y))
      congr 2
      apply Subtype.ext
      rw [oddConj_apply, heE, heE, map_mul, map_mul, map_inv]
    have hνX : ν ∈ linearOrbit E μ₀ X :=
      (exists_conjugateLabel_iff ρ hρ E' eE heE eb X hX μ₀ ν μ' ν'' hμ' hν'').mp ⟨h, hconj⟩
    have hνΩ : ν ∈ linearOrbit E (ω.comp (Subgroup.inclusion hED)) (mV V : Set G) := by
      rw [hMorbit] at hμ₀ ⊢
      obtain ⟨m₀, hm₀⟩ := hμ₀
      refine ⟨m * m₀, ?_⟩
      change (m * m₀) • ω.comp (Subgroup.inclusion hED) = ν
      rw [mul_smul]
      have hm₀' : m₀ • ω.comp (Subgroup.inclusion hED) = μ₀ := hm₀
      rw [hm₀']
    obtain ⟨n', hn'⟩ := exists_affording_label hV hED hDVE hEodd ω hωV ρ P wb φ hφ hνΩ
    refine ⟨ν, hνX, n', hn', ?_⟩
    rw [← KleinFourFiber.coefficientBlock_eq_iff]
    apply characterSubsetIdempotent_injective wb
    rw [blockIdempotent_of_affordsInflation ρ P E' eE heE hEW wb hPab hPE hW ideal hPp hEp hn',
      hidem]
    congr 2
    funext y
    exact (hν'' y).symm
  · rintro ⟨ν, hνX, n', hn', hsame⟩
    obtain ⟨ν'', hν''⟩ := exists_label_of_hom eb (ν.comp eE.toMonoidHom)
    refine ⟨ν'', (exists_conjugateLabel_iff ρ hρ E' eE heE eb X hX μ₀ ν μ' ν'' hμ' hν'').mpr hνX,
      ?_⟩
    rw [← (KleinFourFiber.coefficientBlock_eq_iff wb _ n' n).mpr hsame,
      blockIdempotent_of_affordsInflation ρ P E' eE heE hEW wb hPab hPE hW ideal hPp hEp hn']
    congr 2
    funext y
    exact (hν'' y).symm

end Level

section Assembly

omit [Group G] in
theorem labelTransport_symm {X Y : Type*} [Group X] [Fintype X] [Group Y] [Fintype Y]
    {bX : FiniteIrreducibleCharacterBasis X} {bY : FiniteIrreducibleCharacterBasis Y}
    {f : X ≃* Y} {n : bX.index} {n' : bY.index}
    (h : CFSG.Wreathed.BlockOrbits.LabelTransport bX bY f n n') :
    CFSG.Wreathed.BlockOrbits.LabelTransport bY bX f.symm n' n := by
  intro y
  rw [← h (f.symm y), MulEquiv.apply_symm_apply]

omit [Group G] in
theorem image_coefficientBlock_eq_of_iff {X : Type*} [Group X] [Fintype X]
    (basis : FiniteIrreducibleCharacterBasis X) (ring : Subring ℂ) (P Q : basis.index → Prop)
    (h : ∀ β, P β ↔ ∃ n, Q n ∧ sameCoefficientBlock basis ring n β) :
    (Finset.univ.filter P).image (coefficientBlock basis ring) =
      (Finset.univ.filter Q).image (coefficientBlock basis ring) := by
  ext Y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨n, hn, hsame⟩ := (h β).mp hβ
    exact ⟨n, hn, (KleinFourFiber.coefficientBlock_eq_iff basis ring n β).mpr hsame⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (h n).mpr ⟨n, hn, sameCoefficientBlock_refl basis ring n⟩, rfl⟩

variable {V E : Subgroup G} (hV : IsKleinFour V) {t : G} (htV : t ∈ V)

include hV htV in
theorem isPGroup_zpowers : IsPGroup 2 (Subgroup.zpowers t) :=
  (isPGroup_two hV).to_le (Subgroup.zpowers_le.mpr htV)

include hV htV in
theorem zpowers_le_cT : Subgroup.zpowers t ≤ cT t :=
  (Subgroup.zpowers_le.mpr htV).trans (le_cT hV htV)

theorem zpowers_subgroupOf_normal : ((Subgroup.zpowers t).subgroupOf (cT t)).Normal := by
  constructor
  intro z hz g
  rw [Subgroup.mem_subgroupOf] at hz ⊢
  have hcomm := Subgroup.mem_centralizer_iff.mp g.2 z hz
  change (g : G) * z * (g : G)⁻¹ ∈ Subgroup.zpowers t
  rw [← hcomm, mul_inv_cancel_right]
  exact hz

include hV htV in
theorem mem_four_cases {s : G} (hsV : s ∈ V) (hst : s ∉ Subgroup.zpowers t) (ht1 : t ≠ 1)
    {v : G} (hv : v ∈ V) : v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  have : IsKleinFour V := hV
  by_cases h1 : v = 1
  · exact Or.inl h1
  by_cases h2 : v = t
  · exact Or.inr (Or.inl h2)
  by_cases h3 : v = s
  · exact Or.inr (Or.inr (Or.inl h3))
  right; right; right
  have hs1 : s ≠ 1 := fun h => hst (h ▸ Subgroup.one_mem _)
  have hts : t ≠ s := fun h => hst (h ▸ Subgroup.mem_zpowers t)
  have hmul := IsKleinFour.eq_mul_of_ne_all (x := (⟨t, htV⟩ : V)) (y := ⟨s, hsV⟩)
    (z := ⟨v, hv⟩) (fun h => ht1 (congrArg Subtype.val h)) (fun h => hs1 (congrArg Subtype.val h))
    (fun h => hts (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val hmul

include hV htV in
theorem centralizer_zpowers_eq_dInC (ht1 : t ≠ 1) (s : cT t) (hsV : (s : G) ∈ V)
    (hst : (s : G) ∉ Subgroup.zpowers t) :
    Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (cT t)) : Set (cT t)) = dInC V t := by
  ext x
  rw [mem_dInC_iff hV htV]
  constructor
  · intro hx
    have hxs : (s : cT t) * x = x * s :=
      Subgroup.mem_centralizer_iff.mp hx s (Subgroup.mem_zpowers s)
    have hxs' : (s : G) * x = x * s := congrArg Subtype.val hxs
    have hxt : t * (x : G) = x * t :=
      Subgroup.mem_centralizer_iff.mp x.2 t (Subgroup.mem_zpowers t)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases mem_four_cases hV htV hsV hst ht1 hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hxt
    · exact hxs'
    · rw [mul_assoc, hxs', ← mul_assoc, hxt, mul_assoc]
  · intro hx
    apply DihedralAssociates.mem_centralizer_zpowers_of_commute
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp hx (s : G) hsV)).symm

@[expose, reducible] def rhoK (V : Subgroup G) (t : G) : kInC V t →* G :=
  (cT t).subtype.comp (kInC V t).subtype

include hV htV in
theorem index_comap_rhoK [Finite G] (hAut : Function.Surjective V.normalizerMonoidHom)
    (ht1 : t ≠ 1) : ((dV V).comap (rhoK V t)).index = 2 := by
  have hcomap : (dV V).comap (rhoK V t) =
      (((dV V).subgroupOf (mV V)).subgroupOf ((cT t).subgroupOf (mV V))).comap
        (kInCEquiv (le_cT hV htV)).toMonoidHom := by
    ext x
    rfl
  rw [hcomap, Subgroup.index_comap_of_surjective _ (kInCEquiv (le_cT hV htV)).surjective]
  exact relIndex_dV_cT hV hAut htV ht1

end Assembly

end FreeSix

end CFSG.Semidihedral.Principal

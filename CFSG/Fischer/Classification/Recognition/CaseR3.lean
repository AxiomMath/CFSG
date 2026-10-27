module

public import CFSG.Fischer.Classification.Recognition.R3Model
public import CFSG.Fischer.Classification.Orthogonal3.Mu
public import CFSG.Fischer.Classification.Basic.Local
public import CFSG.Fischer.Classification.Skeleton

public section

namespace CFSG.Fischer.Classification.Recognition

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

namespace R3

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem isQuasisimple_of_mulEquiv (e : A ≃* B) (hA : CFSG.Open.IsQuasisimple A) :
    CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem card_quotient_center_congr (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem isSimpleGroup_commutator_of_mulEquiv (e : A ≃* B) [IsSimpleGroup (commutator A)] :
    IsSimpleGroup (commutator B) := by
  have hmap : (commutator A).map (e : A →* B) = commutator B := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : A →* B) e.surjective]
  let e₁ : commutator A ≃* (commutator A).map (e : A →* B) :=
    (commutator A).equivMapOfInjective (e : A →* B) e.injective
  let e₂ : (commutator A).map (e : A →* B) ≃* commutator B := MulEquiv.subgroupCongr hmap
  exact (e₁.trans e₂).symm.isSimpleGroup

end Transport

section Components

variable {X : Type} [Group X]

theorem isSubnormal_subgroupOf {A B : Subgroup X} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem isComponent_subgroupOf {K C : Subgroup X} (hK : IsComponentOf K C) :
    CFSG.IsComponent (K.subgroupOf C) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1).symm
    (localCores_isQuasisimple hK.2.2), isSubnormal_subgroupOf hK.2.1⟩

theorem commute_of_commutator_eq_bot {C A B : Subgroup X} (hA : A ≤ C) (hB : B ≤ C)
    (h : ⁅A.subgroupOf C, B.subgroupOf C⁆ = ⊥) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have hc : ⁅(⟨a, hA ha⟩ : C), (⟨b, hB hb⟩ : C)⁆ ∈ ⁅A.subgroupOf C, B.subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact congrArg Subtype.val hc

theorem false_of_commute_conj {E : Set X} (hP : Pair X E) {K K' : Subgroup X} {e : X}
    (he : e ∈ E) (hK' : ∀ k ∈ K, e * k * e⁻¹ ∈ K') (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    {k₀ : K} (hk5 : k₀ ^ 5 ∈ Subgroup.center K) (hk : k₀ ∉ Subgroup.center K) : False := by
  set k : X := (k₀ : X)
  have hkK : k ∈ K := k₀.2
  have hek : k⁻¹ * e * k ∈ E := by simpa using Pair.conj_mem hP he k⁻¹
  have h6 : (e * (k⁻¹ * e * k)) ^ 6 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    rcases Pair.orderOf_mul_mem hP he hek with h | h | h <;> rw [h] <;> norm_num
  set a := e * k⁻¹ * e⁻¹
  have ha : a ∈ K' := hK' _ (inv_mem hkK)
  have hak : e * (k⁻¹ * e * k) = a * k := by
    simp only [a, Pair.inv_eq hP he]
    group
  have hc : Commute a k := (hcomm k hkK a ha).symm
  rw [hak, hc.mul_pow] at h6
  have hk6 : k ^ 6 ∈ K' := by
    rw [eq_inv_of_mul_eq_one_right h6]
    exact inv_mem (pow_mem ha 6)
  have hcen6 : k₀ ^ 6 ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hcomm y y.2 _ hk6
  apply hk
  have : k₀ = k₀ ^ 6 * (k₀ ^ 5)⁻¹ := by group
  rw [this]
  exact mul_mem hcen6 (inv_mem hk5)

theorem exists_pow_mem_center [Finite X] {K : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card (K ⧸ Subgroup.center K)) :
    ∃ k₀ : K, k₀ ^ p ∈ Subgroup.center K ∧ k₀ ∉ Subgroup.center K := by
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ Subgroup.center K) p hp
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨k₀, ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
  · intro h
    rw [← QuotientGroup.eq_one_iff] at h
    rw [h, orderOf_one] at hq
    exact (Fact.out : p.Prime).one_lt.ne hq

end Components

section Pair

variable {X : Type} [Group X] {E : Set X}

theorem conj_mem_localGroup (hP : Pair X E) {d k h : X}
    (hk : k * d = d * k) (hh : h ∈ LocalGroup E d) : k * h * k⁻¹ ∈ LocalGroup E d := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    have := (Pair.conj_mem_localClass_iff hP k).2 hx
    rw [hk, mul_inv_cancel_right] at this
    exact Subgroup.subset_closure this
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    have : k * (x * y) * k⁻¹ = k * x * k⁻¹ * (k * y * k⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem localGroup_le_centralizer (d : X) :
    LocalGroup E d ≤ Subgroup.centralizer ({d} : Set X) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_localGroup' hx)

theorem normal_localGroup_subgroupOf (hP : Pair X E) (d : X) :
    ((LocalGroup E d).subgroupOf (Subgroup.centralizer ({d} : Set X))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (localGroup_le_centralizer d)]
  exact fun h k hh hk =>
    conj_mem_localGroup hP (Subgroup.mem_centralizer_singleton_iff.1 hk) hh

theorem conj_mem_of_mem_localClass [Finite X] (hP : Pair X E) {d : X} {K : Subgroup X}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set X)))
    (h5 : 5 ∣ Nat.card (K ⧸ Subgroup.center K)) {e : X} (he : e ∈ LocalClass E d) :
    ∀ k ∈ K, e * k * e⁻¹ ∈ K := by
  set C := Subgroup.centralizer ({d} : Set X)
  have heC : e ∈ C := localGroup_le_centralizer d (Subgroup.subset_closure he)
  set φ := MulAut.conj e
  set K' := K.map φ.toMonoidHom
  have hCφ : C.map φ.toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem heC hy) (inv_mem heC)
    · intro hx
      refine ⟨e⁻¹ * x * e, mul_mem (mul_mem (inv_mem heC) hx) heC, ?_⟩
      change e * (e⁻¹ * x * e) * e⁻¹ = x
      group
  have hK'c : IsComponentOf K' C := by
    have := IsComponentOf.map_mulEquiv φ hK
    rwa [hCφ] at this
  have hmemK' : ∀ k ∈ K, e * k * e⁻¹ ∈ K' := fun k hk => ⟨k, hk, rfl⟩
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf hK)
      (isComponent_subgroupOf hK'c) with h | h
  · have hKK' : K = K' := by
      have := (Subgroup.subgroupOf_inj).1 h
      rwa [inf_eq_left.2 hK.1, inf_eq_left.2 hK'c.1] at this
    intro k hk
    rw [hKK']
    exact hmemK' k hk
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨k₀, hk5, hk⟩ := exists_pow_mem_center (K := K) (p := 5) h5
    exact false_of_commute_conj hP he.1 hmemK' (commute_of_commutator_eq_bot hK.1 hK'c.1 h)
      hk5 hk

theorem normal_subgroupOf_localGroup (hP : Pair X E) {d : X} {K : Subgroup X}
    (hKL : K ≤ LocalGroup E d) (hnorm : ∀ e ∈ LocalClass E d, ∀ k ∈ K, e * k * e⁻¹ ∈ K) :
    (K.subgroupOf (LocalGroup E d)).Normal := by
  have hLN : LocalGroup E d ≤ Subgroup.normalizer (K : Set X) := by
    rw [LocalGroup, Subgroup.closure_le]
    intro e he
    rw [SetLike.mem_coe, Subgroup.mem_set_normalizer_iff]
    intro k
    refine ⟨hnorm e he k, fun hk => ?_⟩
    have h1 := hnorm e he _ hk
    have hee : e * e = 1 := Pair.mul_self hP he.1
    have : e * (e * k * e⁻¹) * e⁻¹ = k := by
      rw [inv_eq_of_mul_eq_one_right hee]
      calc e * (e * k * e) * e = (e * e) * k * (e * e) := by group
        _ = k := by rw [hee, one_mul, mul_one]
    rwa [this] at h1
  rw [Subgroup.normal_subgroupOf_iff hKL]
  exact fun k l hk hl => (Subgroup.mem_set_normalizer_iff.1 (hLN hl) k).1 hk

end Pair

section Model

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem nonabelian_commutator_R3 (hf : IsF3Form f) (hm : 5 ≤ m)
    (hS : IsSimpleGroup (commutator (R3 f))) : ∃ a b : commutator (R3 f), a * b ≠ b * a := by
  by_contra! hab
  obtain ⟨φ, hφ⟩ := Pair.exists_mulEquiv_perm_three (pair_R3 hf (by omega))
    (center_R3_eq_bot hf (by omega)) hS hab
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  obtain ⟨w, hw, hwv⟩ := F3.exists_norm_eq_perp hf (by omega) hv (one_ne_zero (α := ZMod 3))
  have hvw : f v w = 0 := by rw [hf.symm]; exact hwv
  have hne : reflBar f v ≠ reflBar f w := by
    intro h
    rcases (reflBar_eq_reflBar_iff hf (by omega) hv hw).1 h with h' | h'
    · rw [h', hv] at hwv
      exact one_ne_zero hwv
    · rw [h', LinearMap.BilinForm.neg_left, hv] at hwv
      exact one_ne_zero (neg_eq_zero.1 hwv)
  have hc : reflBar f v * reflBar f w = reflBar f w * reflBar f v :=
    (reflBar_commute_iff hf (by omega) hv hw).2 (Or.inl hvw)
  have key : ∀ σ τ : Equiv.Perm (Fin 3), σ.support.card = 2 → τ.support.card = 2 →
      σ * τ = τ * σ → σ = τ := by
    decide
  have hsw : ∀ {u}, f u u = 1 → (φ (reflBar f u)).support.card = 2 := fun hu =>
    Equiv.Perm.card_support_eq_two.2 ((hφ _).1 (reflBar_mem_D3 hu))
  exact hne (φ.injective (key _ _ (hsw hv) (hsw hw) (by rw [← map_mul, ← map_mul, hc])))

theorem le_localGroup (hf : IsF3Form f) (hm : 5 ≤ m) (hS : IsSimpleGroup (commutator (R3 f)))
    {v : Fin m → ZMod 3} (hv : f v v = 1) {K : Subgroup (R3 f)}
    (hK : IsComponentOf K (Subgroup.centralizer ({reflBar f v} : Set (R3 f)))) :
    K ≤ LocalGroup (D3 f) (reflBar f v) := by
  have hP := pair_R3 hf (by omega)
  have : Finite (R3 f) := Pair.finite hP
  set d := reflBar f v
  rcases CFSG.LocalCores.component_normal_subgroup (isComponent_subgroupOf hK)
      (normal_localGroup_subgroupOf hP d) with h | h
  · exact fun x hx => (h (show (⟨x, hK.1 hx⟩ : Subgroup.centralizer ({d} : Set (R3 f))) ∈
      K.subgroupOf _ from hx) :)
  · exfalso
    have hcomm := commute_of_commutator_eq_bot hK.1 (localGroup_le_centralizer d) h
    have hKd : K ≤ Subgroup.zpowers d := by
      intro k hk
      have hkd : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
      have hkD : ∀ g ∈ LocalClass (D3 f) d, k * g = g * k := fun g hg =>
        hcomm k hk g (Subgroup.subset_closure hg)
      rcases Pair.eq_one_or_eq_of_centralizes hP (center_R3_eq_bot hf (by omega)) hS
          (nonabelian_commutator_R3 hf hm hS) (tripleProperty_D3 hf hm) (reflBar_mem_D3 hv)
          hkd hkD with h' | h'
      · rw [h']
        exact one_mem _
      · rw [h']
        exact Subgroup.mem_zpowers d
    refine IsQuasisimple.not_le_of_comm hK.2.2 (A := Subgroup.zpowers d) ?_ hKd
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Commute.zpow_zpow_self d i j

theorem componentOrder_R3 (hf : IsF3Form f) (hm : 5 ≤ m)
    (hS : IsSimpleGroup (commutator (R3 f))) {v : Fin m → ZMod 3} (hv : f v v = 1)
    {K : Subgroup (R3 f)}
    (hK : IsComponentOf K (Subgroup.centralizer ({reflBar f v} : Set (R3 f)))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  intro hN
  set N := Nat.card (K ⧸ Subgroup.center K) with hNdef
  have h5 : 5 ∣ N := by
    rcases hN with h | h | h <;> rw [h] <;> norm_num
  have h11 : 11 ∣ N := by
    rcases hN with h | h | h <;> rw [h] <;> norm_num
  have h3 : ¬ 3 ^ 14 ∣ N := by
    rcases hN with h | h | h <;> rw [h] <;> norm_num
  have hP := pair_R3 hf (by omega)
  have : Finite (R3 f) := Pair.finite hP
  have hKL := le_localGroup hf hm hS hv hK
  have hKn := normal_subgroupOf_localGroup hP hKL fun e he =>
    conj_mem_of_mem_localClass hP hK h5 he
  let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun])
  have hf' := isF3Form_restrictForm hf hv e
  let Ψ := localGroupEquivR3 hf (by omega) hv e (restrictForm_apply e)
  set K₂ := (K.subgroupOf (LocalGroup (D3 f) (reflBar f v))).map Ψ.toMonoidHom
  have hK₂n : K₂.Normal := hKn.map Ψ.toMonoidHom Ψ.surjective
  let eK : K ≃* K₂ := (Subgroup.subgroupOfEquivOfLe hKL).symm.trans
    ((K.subgroupOf _).equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
  have hK₂q : CFSG.Open.IsQuasisimple K₂ := isQuasisimple_of_mulEquiv eK hK.2.2
  obtain ⟨i, z, hi, hz, hcard⟩ := card_reflGroup_eq hf' (by omega) hK₂n hK₂q
  rw [← card_quotient_center_congr eK, ← hNdef] at hcard
  have h11R : 11 ∣ Nat.card (F3.reflGroup (restrictForm f e)) := by
    rw [hcard]
    exact dvd_mul_of_dvd_right h11 _
  have h3R := pow_dvd_card_of_eleven_dvd hf' (by omega) h11R
  rw [hcard] at h3R
  have hcop : Nat.Coprime (3 ^ 14) (i * z) := by
    rcases hi with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num
  exact h3 (hcop.dvd_of_dvd_mul_left h3R)

end Model

end R3

theorem componentOrder_case5 {G : Type} [Group G] [Finite G] {D : Set G} (hH : Hyp G D)
    (h5 : ∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  obtain ⟨m, hm, f, hsymm, hnd, hmodel⟩ := h5
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff D).1 hmodel
  obtain ⟨v, hv, hvd⟩ := mem_D3_iff.1 ((hψ d).1 hd)
  have := hH.simple
  have hS : IsSimpleGroup (commutator (R3 f)) := R3.isSimpleGroup_commutator_of_mulEquiv ψ
  have hK' := IsComponentOf.map_mulEquiv ψ hK
  rw [map_centralizer_singleton, ← hvd] at hK'
  rw [← card_quotient_center_map_mulEquiv ψ K]
  exact R3.componentOrder_R3 hf hm hS hv hK'

end CFSG.Fischer.Classification.Recognition

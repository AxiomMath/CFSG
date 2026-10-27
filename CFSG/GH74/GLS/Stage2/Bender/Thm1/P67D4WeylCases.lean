module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoNF
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem hom_mul_conj {Y G : Type*} [Group Y] [Group G] (φ : G →* MulAut Y) (δ : G) (h : Y) :
    φ δ * MulAut.conj h = MulAut.conj (φ δ h) * φ δ :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_mul_hom_mul {Y G : Type*} [Group Y] [Group G] (φ : G →* MulAut Y) (g h : Y)
    (δ δ' : G) :
    (MulAut.conj g * φ δ) * (MulAut.conj h * φ δ') =
      MulAut.conj (g * φ δ h) * φ (δ * δ') := by
  calc (MulAut.conj g * φ δ) * (MulAut.conj h * φ δ')
      = MulAut.conj g * (φ δ * MulAut.conj h) * φ δ' := by simp only [mul_assoc]
    _ = MulAut.conj g * (MulAut.conj (φ δ h) * φ δ) * φ δ' := by rw [hom_mul_conj]
    _ = MulAut.conj (g * φ δ h) * φ (δ * δ') := by rw [map_mul, map_mul]; simp only [mul_assoc]

theorem conj_mul_hom_mul_conj {Y G : Type*} [Group Y] [Group G] (φ : G →* MulAut Y) (g h : Y)
    (δ : G) : (MulAut.conj g * φ δ) * MulAut.conj h = MulAut.conj (g * φ δ h) * φ δ := by
  have := conj_mul_hom_mul φ g h δ 1
  rwa [map_one, mul_one, mul_one] at this

theorem inv_conj_mul_hom_inv {Y G : Type*} [Group Y] [Group G] (φ : G →* MulAut Y) (g : Y)
    (δ : G) :
    (MulAut.conj g * φ δ⁻¹)⁻¹ = MulAut.conj (φ δ g⁻¹) * φ δ := by
  calc (MulAut.conj g * φ δ⁻¹)⁻¹ = φ δ * (MulAut.conj g)⁻¹ := by
        rw [mul_inv_rev, map_inv, inv_inv]
    _ = φ δ * MulAut.conj g⁻¹ := by rw [map_inv]
    _ = MulAut.conj (φ δ g⁻¹) * φ δ := hom_mul_conj φ δ g⁻¹

theorem eq_or_eq_inv_of_pow_three_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {σ δ : G}
    (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) (hδ1 : δ ≠ 1) (hδ3 : δ ^ 3 = 1) :
    δ = σ ∨ δ = σ⁻¹ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra h
  push Not at h
  obtain ⟨hδσ, hδσ'⟩ := h
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by norm_num)
  have hσ2 : σ ≠ σ⁻¹ := by
    intro h2
    apply hσ1
    have h3 : σ * σ = 1 := mul_eq_one_iff_eq_inv.2 h2
    calc σ = σ ^ 3 * (σ * σ)⁻¹ := by group
      _ = 1 := by rw [hσ3, h3]; simp
  have hsub : ({1, σ, σ⁻¹, δ} : Finset G) ⊆ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [inv_pow, hσ3, inv_one]
    · exact hδ3
  have h4 : ({1, σ, σ⁻¹, δ} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact fun h => hδσ' h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hσ2, fun h => hδσ h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hσ1 h.symm, fun h => ?_, fun h => hδ1 h.symm⟩
      apply hσ1
      have : σ⁻¹ = 1 := h.symm
      simpa using this
  have := Finset.card_le_card hsub
  omega

theorem cyclic_mem_zpowers_of_pow_three {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) : b ∈ Subgroup.zpowers a := by
  by_cases hb1 : b = 1
  · rw [hb1]
    exact one_mem _
  · rcases eq_or_eq_inv_of_pow_three_eq_one ha1 ha3 hb1 hb3 with h | h
    · rw [h]
      exact Subgroup.mem_zpowers a
    · rw [h]
      exact inv_mem (Subgroup.mem_zpowers a)

theorem mem_zpowers_of_commute_pow_three {G : Type*} [Group G] (R : Subgroup G)
    (hR : Nat.card R = 12) {a b : G} (ha : a ∈ R) (hb : b ∈ R) (hab : a * b = b * a)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) : b ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEa : IsElementaryAbelian 3 (Subgroup.zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one ha3
  have hEb : IsElementaryAbelian 3 (Subgroup.zpowers b) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hb3
  have hcent : Subgroup.zpowers b ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute a b from hab) k).eq
  have hS := IsElementaryAbelian.sup_of_le_centralizer (p := 3) (E := Subgroup.zpowers a)
    (C := Subgroup.zpowers b) hcent
  have hP : IsPGroup 3 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    IsElementaryAbelian.isPGroup 3 _
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ R :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  have hfin' : Finite ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∣ 12 := by
    rw [← hR]
    exact Subgroup.card_dvd_of_le hle
  have hcardE : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hdvdE : Nat.card (Subgroup.zpowers a) ∣
      Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) :=
    Subgroup.card_dvd_of_le le_sup_left
  rw [hk] at hdvd
  rw [hk, hcardE] at hdvdE
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · norm_num at hdvdE
      · rfl
    · exfalso
      have h9 : 9 ∣ 3 ^ k := by
        have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 h
        simpa using this
      have := h9.trans hdvd
      omega
  have heq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hk1, hcardE]; norm_num)
  have : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  rwa [← heq] at this

theorem exists_zpow_eq_one_of_commute {N W : Type*} [Group N] [Group W] (w : N →* W)
    (R : Subgroup W) (hR : Nat.card R = 12) (hwR : ∀ x, w x ∈ R) (n v : N)
    (hn3 : w n ^ 3 = 1) (hv3 : w v ^ 3 = 1) (hcomm : w n * w v = w v * w n)
    (hv1 : w v ≠ 1) : ∃ j : ℤ, w n * w v ^ j = 1 := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_commute_pow_three R hR (hwR v) (hwR n) hcomm.symm hv3 hn3 hv1)
  refine ⟨-j, ?_⟩
  rw [← hj, ← zpow_add, add_neg_cancel, zpow_zero]

theorem ringEquiv_ne_one_of_pow {K : Type*} [Field K] [Finite K] {q : ℕ} (hq : 1 < q)
    (hK : Nat.card K = q ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) : σ ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro h1
  have hfix : ∀ c : K, c ^ q = c := fun c => by rw [← hσ c, h1]; rfl
  have hP0 : (Polynomial.X ^ q - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial K).natDegree = q :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hfix, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK, hdeg] at hle
  have : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  rw [pow_one] at this
  omega

theorem mul_comm_of_mem_isElementaryAbelian {p : ℕ} {G : Type*} [Group G] {A : Subgroup G}
    [IsElementaryAbelian p A] {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_not_mem_zpowers_of_card_nine {H : Type*} [Group H] (V : Subgroup H)
    (hVc : Nat.card V = 9) {e : H} (he3 : e ^ 3 = 1) : ∃ y ∈ V, y ∉ Subgroup.zpowers e := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_dvd_of_le (show V ≤ Subgroup.zpowers e from hcon)
  rw [hVc, Nat.card_zpowers] at h1
  have h2 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one he3
  have h3 := Nat.le_of_dvd (by norm_num) h2
  have h4 := Nat.pos_of_dvd_of_pos h2 (by norm_num)
  have h5 := Nat.le_of_dvd h4 h1
  omega

theorem exists_ker_of_card_nine {H G : Type*} [Group H] [Group G] [Finite G] [IsCyclic G]
    (Θ : H →* G) (V : Subgroup H) (hVc : Nat.card V = 9) (hV3 : ∀ x ∈ V, x ^ 3 = 1)
    {e : H} (heV : e ∈ V) (hΘe : Θ e ≠ 1) : ∃ ι ∈ V, ι ≠ 1 ∧ Θ ι = 1 := by
  obtain ⟨y, hyV, hy⟩ := exists_not_mem_zpowers_of_card_nine V hVc (hV3 e heV)
  have hΘ3 : ∀ x ∈ V, Θ x ^ 3 = 1 := fun x hx => by rw [← map_pow, hV3 x hx, map_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (cyclic_mem_zpowers_of_pow_three hΘe (hΘ3 e heV) (hΘ3 y hyV))
  refine ⟨y * e ^ (-k), mul_mem hyV (zpow_mem heV _), fun h => hy ?_, ?_⟩
  · have : y = e ^ k := by
      calc y = y * e ^ (-k) * e ^ k := by
            rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
        _ = e ^ k := by rw [h, one_mul]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers e) k
  · rw [map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]

theorem entrywise_mem_monomialSubgroup
    {t : CFSG.Blueprint.Chevalley.TwistTag} {K : Type} [Field K]
    (δ : K ≃+* K) {g : CFSG.Blueprint.Chevalley.ModGL t.tag K}
    (hg : g ∈ CFSG.LieType.Chevalley.monomialSubgroup t.tag K) :
    Units.map (CFSG.Blueprint.Chevalley.entrywiseHom δ.toRingHom) g ∈
      CFSG.LieType.Chevalley.monomialSubgroup t.tag K :=
  CFSG.LieType.Chevalley.baseChangeGL_mem_monomialSubgroup δ.toRingHom hg

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem graphFixedWeylHom_entrywise (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    (δ : K ≃+* K) (m m' : graphFixedMonomial t K σ)
    (hm : (m' : ModGL t.tag K) = Units.map (entrywiseHom δ.toRingHom) (m : ModGL t.tag K)) :
    graphFixedWeylHom t K σ m' = graphFixedWeylHom t K σ m := by
  obtain ⟨w, k, hk, hmk⟩ := monomialSubgroup_le_torusWeylCosets
    (graphFixedMonomial_le_monomialSubgroup t K σ m.2)
  have h1 : graphFixedWeylHom t K σ m = w :=
    graphFixedWeylHom_eq (hmk ▸ mapsRootLines_mul_canonicalRep hk w)
  have h2 : graphFixedWeylHom t K σ m' = w := by
    refine graphFixedWeylHom_eq ?_
    rw [hm, hmk, map_mul, entrywise_canonicalRep]
    exact mapsRootLines_mul_canonicalRep (entrywise_mem_torusGroup hk) w
  rw [h1, h2]

section MonoY

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

@[expose] noncomputable def monoY : Subgroup 𝒞[K, σ] :=
  (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf 𝒞[K, σ]

@[expose] noncomputable def weylY : monoY σ →* WeylGroup TwistTag.D4.tag :=
  (graphFixedWeylHom TwistTag.D4 K σ.toRingHom).comp
    ((graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.subgroupComap
      (graphFixedMonomial TwistTag.D4 K σ.toRingHom))

theorem fieldActor_mem_monoY (δ : K ≃+* K) {x : 𝒞[K, σ]} (hx : x ∈ monoY σ) :
    fieldActor (t := TwistTag.D4) σ δ x ∈ monoY σ := by
  have hx' := Subgroup.mem_inf.1 hx
  have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := ringEquiv_comm_of_finite σ δ
  change ((fieldActor (t := TwistTag.D4) σ δ x : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
    graphFixedMonomial TwistTag.D4 K σ.toRingHom
  rw [coe_fieldActor]
  exact Subgroup.mem_inf.2 ⟨entrywise_mem_monomialSubgroup δ hx'.1,
    units_map_entrywiseHom_mem_twistedFixedGroup hδ hx'.2⟩

@[expose] noncomputable def actY (δ : K ≃+* K) : monoY σ →* monoY σ where
  toFun x := ⟨fieldActor σ δ x, fieldActor_mem_monoY σ δ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem coe_actY (δ : K ≃+* K) (x : monoY σ) :
    ((actY σ δ x : monoY σ) : 𝒞[K, σ]) = fieldActor σ δ (x : 𝒞[K, σ]) := rfl

theorem weylY_actY (δ : K ≃+* K) (x : monoY σ) : weylY σ (actY σ δ x) = weylY σ x :=
  graphFixedWeylHom_entrywise TwistTag.D4 σ.toRingHom δ _ _ rfl

theorem fieldActor_mem_graphFixedTorus (δ : K ≃+* K) {x : 𝒞[K, σ]}
    (hx : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ((fieldActor (t := TwistTag.D4) σ δ x : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  have hx' := Subgroup.mem_inf.1 hx
  have hδ : ∀ c, δ (σ.toRingHom c) = σ.toRingHom (δ c) := ringEquiv_comm_of_finite σ δ
  rw [coe_fieldActor]
  exact Subgroup.mem_inf.2 ⟨entrywise_mem_torusGroup hx'.1,
    units_map_entrywiseHom_mem_twistedFixedGroup hδ hx'.2⟩

theorem graphFixedRootWeylHom_fieldActor (δ : K ≃+* K) (g : 𝒞[K, σ])
    (hg : (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom) :
    graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨((fieldActor (t := TwistTag.D4) σ δ g : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K),
        Subgroup.mem_inf.2 ⟨fieldActor_mem_monoY σ δ hg, (fieldActor σ δ g).2⟩⟩ =
      graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
        ⟨(g : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hg, g.2⟩⟩ :=
  weylY_actY σ δ ⟨g, hg⟩

end MonoY

theorem d4_weyl_cases {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hVe : IsElementaryAbelian 3 V) (hVc : Nat.card V = 9)
    (hV0 : ∀ x ∈ V, ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hout : ∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    (∃ φ ∈ V, φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        (φ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ ∨
          φ⁻¹ = MulAut.conj h * fieldActor (t := TwistTag.D4) σ σ)) ∨
    (∃ (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧ v ≠ 1 ∧
      v ^ 3 = 1 ∧ MulAut.conj v ∈ V ∧
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
      (δ = σ ∨ δ = σ⁻¹) ∧
      MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ ∈ V ∧
      (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) := by
  classical
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcard, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hp.one_lt) hK σ hσ
  have := hVe
  have hV3 : ∀ x ∈ V, x ^ 3 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_isElementaryAbelian (p := 3) hx hy
  have hinn : ∀ x : MulAut 𝒞[K, σ],
      x ∈ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ↔ Θ x = 1 := fun x => by
    rw [← hΘker, MonoidHom.mem_ker]
  have hΘform : ∀ (g : 𝒞[K, σ]) (δ : K ≃+* K),
      Θ (MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) = δ := fun g δ => hΘ _ g δ rfl
  by_cases hc1 : ∃ x ∈ V, x ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range ∧
      ∃ g : 𝒞[K, σ], (g : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        ∃ δ : K ≃+* K, x = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ
  · left
    obtain ⟨x, hxV, hxout, g, hgT, δ, hx⟩ := hc1
    have hΘx : Θ x = δ := by rw [hx]; exact hΘform g δ
    have hδ1 : δ ≠ 1 := fun h => hxout ((hinn x).2 (by rw [hΘx, h]))
    have hδ3 : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV3 x hxV, map_one]
    rcases eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3 with h | h
    · rw [h] at hx
      exact ⟨x, hxV, hxout, g, hgT, Or.inl hx⟩
    · rw [h] at hx
      refine ⟨x, hxV, hxout, fieldActor (t := TwistTag.D4) σ σ g⁻¹, ?_, Or.inr ?_⟩
      · exact fieldActor_mem_graphFixedTorus σ σ (x := g⁻¹) (inv_mem hgT)
      · rw [hx]
        exact inv_conj_mul_hom_inv (fieldActorHom (t := TwistTag.D4) σ) g σ
  · right
    push Not at hc1
    obtain ⟨e, heV, heout⟩ := hout
    obtain ⟨n, δ, hnM, hen⟩ := hV0 e heV
    have hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom :=
      fun h => hc1 e heV heout n h δ hen
    have hΘe : Θ e = δ := by rw [hen]; exact hΘform n δ
    have hδ1 : δ ≠ 1 := fun h => heout ((hinn e).2 (by rw [hΘe, h]))
    have hδ3 : δ ^ 3 = 1 := by rw [← hΘe, ← map_pow, hV3 e heV, map_one]
    obtain ⟨ι, hιV, hι1, hΘι⟩ :=
      exists_ker_of_card_nine Θ V hVc hV3 heV (by rw [hΘe]; exact hδ1)
    obtain ⟨v, hv⟩ := (hinn ι).2 hΘι
    have hv1 : v ≠ 1 := fun h => hι1 (by rw [← hv, h, map_one])
    have hv3 : v ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hv, hV3 ι hιV, map_one]
    have hvM : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom := by
      obtain ⟨g', δ', hg'M, hιg'⟩ := hV0 ι hιV
      have hδ' : δ' = 1 := (hΘ ι g' δ' hιg').symm.trans hΘι
      rw [hδ', fieldActor_one, mul_one] at hιg'
      have : v = g' := hinj (hv.trans hιg')
      rw [this]
      exact hg'M
    have hweyl1 : ∀ x : monoY σ, weylY σ x = 1 ↔
        ((x : 𝒞[K, σ]) : ModGL TwistTag.D4.tag K) ∈
          graphFixedTorus TwistTag.D4 K σ.toRingHom := fun x => by
      change graphFixedWeylHom TwistTag.D4 K σ.toRingHom ⟨(x : 𝒞[K, σ]).1, x.2⟩ = 1 ↔ _
      rw [← MonoidHom.mem_ker, graphFixedWeylHom_ker, Subgroup.mem_subgroupOf]
    have hweylmem : ∀ x : monoY σ, weylY σ x ∈ relWeylTwist TwistTag.D4 := fun x =>
      graphFixedWeylHom_mem TwistTag.D4 K σ.toRingHom ⟨(x : 𝒞[K, σ]).1, x.2⟩
    let nm : monoY σ := ⟨n, hnM⟩
    let vm : monoY σ := ⟨v, hvM⟩
    have hfA3 : fieldActor (t := TwistTag.D4) σ δ ^ 3 = 1 := by
      have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) δ 3
      rw [hδ3, map_one] at h
      exact h.symm
    have hNs : normSeq (fieldActor (t := TwistTag.D4) σ δ) n 3 = 1 :=
      normSeq_eq_one_of_pow_eq_one hZ hfA3 (by rw [← hen]; exact hV3 e heV)
    have hN3 : nm * actY σ δ nm * actY σ δ (actY σ δ nm) = 1 := by
      refine Subtype.ext ?_
      have h : normSeq (fieldActor (t := TwistTag.D4) σ δ) n 3 = n * fieldActor σ δ n *
          fieldActor σ δ (fieldActor σ δ n) := by
        simp only [normSeq, pow_two, MulAut.mul_apply, MulAut.one_apply, pow_zero, pow_one,
          one_mul]
      show n * fieldActor σ δ n * fieldActor σ δ (fieldActor σ δ n) = 1
      rw [← h]
      exact hNs
    have hwn3 : weylY σ nm ^ 3 = 1 := by
      have h := congrArg (weylY σ) hN3
      simp only [map_mul, weylY_actY, map_one] at h
      rw [pow_three']
      exact h
    have hwv3 : weylY σ vm ^ 3 = 1 := by
      rw [← map_pow, show vm ^ 3 = 1 from Subtype.ext hv3, map_one]
    have hcomm : nm * actY σ δ vm = vm * nm := by
      have h := hVcomm e heV ι hιV
      rw [hen, ← hv] at h
      have h1 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) * MulAut.conj v =
          MulAut.conj (n * fieldActor σ δ v) * fieldActor σ δ :=
        conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n v δ
      have h2 : MulAut.conj v * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) =
          MulAut.conj (v * n) * fieldActor σ δ := by rw [← mul_assoc, ← map_mul]
      rw [h1, h2] at h
      exact Subtype.ext (hinj (mul_right_cancel h))
    have hwcomm : weylY σ nm * weylY σ vm = weylY σ vm * weylY σ nm := by
      have h := congrArg (weylY σ) hcomm
      rw [map_mul, map_mul, weylY_actY] at h
      exact h
    by_cases hwv1 : weylY σ vm = 1
    · refine ⟨v, n, δ, (hweyl1 vm).1 hwv1, hv1, hv3, by rw [hv]; exact hιV, hnM, hnT,
        eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3, by rw [← hen]; exact heV, ?_⟩
      rw [← hen]
      have h := hVcomm e heV ι hιV
      rw [← hv] at h
      have h1 : e * MulAut.conj v = MulAut.conj (e v) * e := mulAut_mul_conj e v
      rw [h] at h1
      exact (hinj (mul_right_cancel h1)).symm
    · exfalso
      obtain ⟨j, hj⟩ := exists_zpow_eq_one_of_commute (weylY σ) (relWeylTwist TwistTag.D4)
        card_relWeylTwist_D4 hweylmem nm vm hwn3 hwv3 hwcomm hwv1
      let g'' : monoY σ := nm * actY σ δ vm ^ j
      have hg''W : weylY σ g'' = 1 := by
        change weylY σ (nm * actY σ δ vm ^ j) = 1
        rw [map_mul, map_zpow, weylY_actY]
        exact hj
      have hg''T := (hweyl1 g'').1 hg''W
      have hcoe : (g'' : 𝒞[K, σ]) = n * fieldActor σ δ (v ^ j) := by
        rw [map_zpow]
        rfl
      have hee : e * ι ^ j = MulAut.conj (g'' : 𝒞[K, σ]) * fieldActor σ δ := by
        rw [hcoe, hen, ← hv, ← map_zpow]
        exact conj_mul_hom_mul_conj (fieldActorHom (t := TwistTag.D4) σ) n (v ^ j) δ
      have hΘ' : Θ (e * ι ^ j) = δ := by rw [hee]; exact hΘform _ δ
      exact hc1 (e * ι ^ j) (mul_mem heV (zpow_mem hιV j))
        (fun h => hδ1 (hΘ'.symm.trans ((hinn _).1 h))) (g'' : 𝒞[K, σ]) hg''T δ hee

end CFSG.GH74.GLS.Stage2.Bender.Thm1

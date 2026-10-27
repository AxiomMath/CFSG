module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.LieType.Chevalley.ChevalleyFrobeniusFixedNormalizer
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.GroupTheory.LangNormOneDescent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
open CFSG.GroupTheory

theorem conj_mul_pow {C : Type*} [Group C] (x : C) (T : MulAut C) (n : ℕ) :
    (MulAut.conj x * T) ^ n =
      MulAut.conj (((List.range n).map fun i => (T ^ i) x).prod) * T ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ^ n * MulAut.conj x = MulAut.conj ((T ^ n) x) * T ^ n := by
      ext u
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [pow_succ, ih, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, map_mul, mul_assoc, ← mul_assoc (T ^ n), hT, pow_succ]
    simp only [mul_assoc]

section Entrywise

variable {τ : Tag} {K : Type} [Field K]

theorem entrywiseAdjointAut_mul
    (σ σ' : K ≃+* K) :
    entrywiseAdjointAut τ (σ * σ') = entrywiseAdjointAut τ σ * entrywiseAdjointAut τ σ' := by
  have hσ : (σ * σ').toRingHom = σ.toRingHom.comp σ'.toRingHom := RingHom.ext fun _ => rfl
  refine MulEquiv.ext fun g => Subtype.ext (Units.ext ?_)
  rw [MulAut.mul_apply, coe_entrywiseAdjointAut, coe_entrywiseAdjointAut,
    coe_entrywiseAdjointAut, Units.coe_map, Units.coe_map, Units.coe_map, hσ]
  exact (entrywise_entrywise (R := K) _ _ _).symm

theorem entrywiseAdjointAut_one
    : entrywiseAdjointAut τ (1 : K ≃+* K) = 1 := by
  have h1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
  refine MulEquiv.ext fun g => Subtype.ext (Units.ext ?_)
  rw [coe_entrywiseAdjointAut, MulAut.one_apply, Units.coe_map, h1]
  exact entrywise_id (R := K) _

@[expose] def entrywiseAdjointAutHom
    : (K ≃+* K) →* MulAut (adjointGroup τ K) where
  toFun := entrywiseAdjointAut τ
  map_one' := entrywiseAdjointAut_one
  map_mul' := entrywiseAdjointAut_mul

theorem entrywiseAdjointAut_pow
    (σ : K ≃+* K) (n : ℕ) :
    entrywiseAdjointAut τ (σ ^ n) = entrywiseAdjointAut τ σ ^ n :=
  map_pow (entrywiseAdjointAutHom (τ := τ)) σ n

theorem units_map_entrywiseHom_eq_baseChangeGL
    (σ : K →+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ) g = baseChangeGL σ g :=
  Units.ext ((baseChange_entrywise σ _).unique (baseChange_baseChangeEnd σ _))

end Entrywise

theorem ringEquiv_pow_apply {K : Type} [Field K] (T : K ≃+* K) (n : ℕ) (c : K) :
    (T ^ n) c = (⇑T)^[n] c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Function.iterate_succ_apply', ← ih]
    rfl

theorem exists_conj_eq_entrywiseAdjointAut
    (τ : Tag) {ℓ f e p : ℕ} [Fact ℓ.Prime] (K : Type)
    [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (he : 1 ≤ e) (hp : 1 ≤ p)
    (hep : e * p = f) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosure K L] (x : adjointGroup τ K)
    (hβp : (MulAut.conj x * entrywiseAdjointAut τ T) ^ p = 1) :
    ∃ δ : MulAut (adjointGroup τ K),
      δ * (MulAut.conj x * entrywiseAdjointAut τ T) * δ⁻¹ = entrywiseAdjointAut τ T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hTp : T ^ p = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_apply, RingAut.one_apply]
    have hit : ∀ n : ℕ, (⇑T)^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hβp' := hβp
  rw [conj_mul_pow, ← entrywiseAdjointAut_pow, hTp, entrywiseAdjointAut_one, mul_one] at hβp'
  generalize hNdef : ((List.range p).map fun i => (entrywiseAdjointAut τ T ^ i) x).prod = N
    at hβp'
  have hN1 : N = 1 := by
    have hc : N ∈ Subgroup.center (adjointGroup τ K) := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h1 : N * g * N⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ g) hβp'
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * N = N * g * N⁻¹ * N := by rw [h1]
        _ = N * g := by group
    rw [center_adjointGroup_eq_bot] at hc
    exact Subgroup.mem_bot.1 hc
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L e he).1 τ
  have hS1 : ∀ g, ((S.toMonoidHom g : adjointGroup τ L) : ModGL τ L) =
      Units.map (entrywiseHom (iterateFrobenius L ℓ e)) g := hS
  let ι : adjointGroup τ K →* adjointGroup τ L :=
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).codRestrict
      (adjointGroup τ L) fun u => baseChangeGL_mem_adjointGroup (algebraMap K L) u.2
  have hι : ∀ u, (ι u : ModGL τ L) = baseChangeGL (algebraMap K L) u := fun _ => rfl
  have hFrc : (iterateFrobenius L ℓ e).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have hSι : ∀ u, S (ι u) = ι (entrywiseAdjointAut τ T u) := by
    intro u
    apply Subtype.ext
    rw [hS, hι, hι, coe_entrywiseAdjointAut, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      baseChangeGL_baseChangeGL, hFrc]
  have hSιi : ∀ (i : ℕ) (u : adjointGroup τ K),
      (⇑S.toMonoidHom)^[i] (ι u) = ι ((entrywiseAdjointAut τ T ^ i) u) := by
    intro i
    induction i with
    | zero => intro u; rfl
    | succ i ih =>
      intro u
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      exact hSι _
  have hnorm : ((List.range p).map fun i => (⇑S.toMonoidHom)^[i] (ι x)).prod = 1 := by
    have h1 : ((List.range p).map fun i => (⇑S.toMonoidHom)^[i] (ι x)) =
        ((List.range p).map fun i => (entrywiseAdjointAut τ T ^ i) x).map ι := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hSιi i x
    rw [h1, ← map_list_prod, hNdef, hN1, map_one]
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom hp hLang (ι x) hnorm
  have hFrK : ∀ c : L, ((iterateFrobenius L ℓ e) ^ p) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L ℓ e))^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, hK]
  have hiterS : ∀ (n : ℕ) (g : adjointGroup τ L), (((⇑S.toMonoidHom)^[n] g : adjointGroup τ L) :
      ModGL τ L) = Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ n)) g := by
    intro n
    induction n with
    | zero =>
      intro g
      refine Units.ext ?_
      rw [Function.iterate_zero, id_eq, Units.coe_map, pow_zero, RingHom.one_def]
      exact (entrywise_id (R := L) _).symm
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply', hS1, ih]
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.coe_map, pow_succ', RingHom.mul_def]
      exact entrywise_entrywise (R := L) _ _ _
  have hhfix : (h : ModGL τ L) ∈ adjointGroup τ L ⊓
      (Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ p))).eqLocus (MonoidHom.id _) := by
    refine ⟨h.2, ?_⟩
    change Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ p)) (h : ModGL τ L) = h
    rw [← hiterS p h, mem_iterateFixedSubgroup.1 hR]
  obtain ⟨-, -, hnorml⟩ := Chevalley_Frobenius_fixed_ambient_normalizer τ K L _ hFrK
  have hmap : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL τ L)).toMonoidHom =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml hhfix)
  let eH : adjointGroup τ K ≃* (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (adjointGroup τ K) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) :
      ModGL τ L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let δ : MulAut (adjointGroup τ K) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap).trans eH.symm)
  have hδ : ∀ u, baseChangeGL (algebraMap K L) (δ u : ModGL τ K) =
      (h : ModGL τ L) * baseChangeGL (algebraMap K L) u * (h : ModGL τ L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap (eH u))) :
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) : ModGL τ L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hδinv : ∀ u, baseChangeGL (algebraMap K L) (δ⁻¹ u : ModGL τ K) =
      (h : ModGL τ L)⁻¹ * baseChangeGL (algebraMap K L) u * (h : ModGL τ L) := by
    intro u
    have h1 := hδ (δ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨δ, MulEquiv.ext fun u => Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_)⟩
  have hxh' : baseChangeGL (algebraMap K L) (x : ModGL τ K) =
      (h : ModGL τ L)⁻¹ * ((S h : adjointGroup τ L) : ModGL τ L) := by
    rw [← hι, hxh]
    rfl
  have hT' : ∀ w, baseChangeGL (algebraMap K L) ((entrywiseAdjointAut τ T w :
      adjointGroup τ K) : ModGL τ K) = ((S (ι w) : adjointGroup τ L) : ModGL τ L) := by
    intro w
    rw [hSι, hι]
  have hSh : ∀ w : adjointGroup τ L, ((S w : adjointGroup τ L) : ModGL τ L) =
      Units.map (entrywiseHom (iterateFrobenius L ℓ e)) w := hS
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hδ, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, hxh', hT',
    hT', hSh (ι (δ⁻¹ u)), hι, hδinv, hSh h, hSh (ι u), hι, map_mul, map_mul, map_inv]
  group


theorem odd_F4_prime_field_coset_descent
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (α : MulAut (adjointGroup .F4 K)) (hαp : orderOf α = p)
    (hαinn : α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range) :
    ∃ (x : adjointGroup .F4 K) (σ : K ≃+* K) (δ : MulAut (adjointGroup .F4 K)),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut .F4 σ ∧
      δ * α * δ⁻¹ = entrywiseAdjointAut .F4 σ ∧ p ∣ f ∧
      Nat.card (fixSubfield σ) = ℓ ^ (f / p) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨hNF, Θ, hΘ, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4 (Or.inl rfl)
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  have hασ : α = MulAut.conj x * entrywiseAdjointAut .F4 σ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
    exact hxσ u
  have hΘα : Θ α = σ := hΘ α x σ hxσ
  have hαpow : α ^ p = 1 := by rw [← hαp]; exact pow_orderOf_eq_one α
  have hσp : orderOf σ = p := by
    have h1 : σ ^ p = 1 := by rw [← hΘα, ← map_pow, hαpow, map_one]
    have h2 : σ ≠ 1 := fun h1 => hαinn (by rw [← hΘker, MonoidHom.mem_ker, hΘα, h1])
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime h1 h2
  obtain ⟨φ, hφ, hφord, hφgen, hcard, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hpf : p ∣ f := by
    rw [← hcard, ← hσp]
    exact orderOf_dvd_natCard σ
  have hfixcard : Nat.card (fixSubfield σ) = ℓ ^ (f / p) := by
    obtain ⟨-, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
    rw [Nat.card_zpowers, hσp] at hScard
    rw [← hScard]
    have hset : (fixSubfield σ : Set K) = (S : Set K) := by
      rw [hS]
      ext c
      change σ c = c ↔ ∀ τ' ∈ Subgroup.zpowers σ, τ' c = c
      constructor
      · intro hc τ' hτ'
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hτ')
        rw [ringEquiv_pow_apply]
        exact Function.iterate_fixed hc n
      · intro hc
        exact hc σ (Subgroup.mem_zpowers σ)
    rw [show fixSubfield σ = S from SetLike.coe_injective hset]
  set e := f / p with he
  have hep : e * p = f := Nat.div_mul_cancel hpf
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hT : ∀ c, (φ ^ e) c = c ^ (ℓ ^ e) := by
    intro c
    rw [ringEquiv_pow_apply]
    have hit : ∀ n : ℕ, (⇑φ)^[n] c = c ^ (ℓ ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hφ, pow_succ, pow_mul]
    exact hit e
  have hσmem : σ ∈ Subgroup.zpowers φ := by rw [hφgen]; exact Subgroup.mem_top σ
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hk : φ ^ k = σ := hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [← hk, orderOf_one] at hσp
    exact hp.one_lt.ne hσp
  have hgcd : Nat.gcd f k = e := by
    have h1 := orderOf_pow' φ hk0
    rw [hk, hσp, hφord] at h1
    rw [he, h1, Nat.div_div_self (Nat.gcd_dvd_left f k) (by omega)]
  have hzp : Subgroup.zpowers σ = Subgroup.zpowers (φ ^ e) := by
    rw [← hk, ← zpow_natCast, ← zpow_natCast φ e, Subgroup.zpowers_eq_zpowers_iff', hφord,
      Int.gcd_natCast_natCast, Int.gcd_natCast_natCast, Nat.gcd_comm, hgcd,
      Nat.gcd_eq_left ⟨p, hep.symm⟩]
  have hTσ : φ ^ e ∈ Subgroup.zpowers σ := by rw [hzp]; exact Subgroup.mem_zpowers _
  have hσT : σ ∈ Subgroup.zpowers (φ ^ e) := by rw [← hzp]; exact Subgroup.mem_zpowers _
  obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hTσ)
  replace hj' : σ ^ j' = φ ^ e := hj'
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσT)
  replace hj : (φ ^ e) ^ j = σ := hj
  have hjj : α ^ (j' * j) = α := by
    have h1 : σ ^ (j' * j) = σ ^ 1 := by rw [pow_mul, hj', hj, pow_one]
    rw [pow_eq_pow_iff_modEq, hσp] at h1
    have h2 : α ^ (j' * j) = α ^ 1 := by rw [pow_eq_pow_iff_modEq, hαp]; exact h1
    rwa [pow_one] at h2
  have hβ : α ^ j' = MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut .F4 σ ^ i) x).prod) * entrywiseAdjointAut .F4 (φ ^ e) := by
    rw [hασ, conj_mul_pow, ← entrywiseAdjointAut_pow, hj']
  have hβp : (MulAut.conj (((List.range j').map fun i =>
      (entrywiseAdjointAut .F4 σ ^ i) x).prod) * entrywiseAdjointAut .F4 (φ ^ e)) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hαpow, one_pow]
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut .F4 K hK he1 hp.one_lt.le hep (φ ^ e) hT
    (AlgebraicClosure K) _ hβp
  refine ⟨x, σ, δ, hσp, hασ, ?_, hpf, hfixcard⟩
  have hαβ : α = (α ^ j') ^ j := by rw [← pow_mul, hjj]
  rw [hαβ, ← conj_pow, hβ, hδ, ← entrywiseAdjointAut_pow, hj]

end CFSG.LieType.Chevalley

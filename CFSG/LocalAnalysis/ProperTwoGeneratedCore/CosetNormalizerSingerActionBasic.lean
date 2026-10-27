module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

open scoped Pointwise

variable {G : Type*} [Group G]

abbrev involutionSubgroup (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ R ∧ orderOf x = 2}

theorem involutionSubgroup_le (R : Subgroup G) : involutionSubgroup R ≤ R :=
  (Subgroup.closure_le R).2 fun _ hx => hx.1

theorem closure_ne_one_eq (A : Subgroup G) : Subgroup.closure {x | x ∈ A ∧ x ≠ 1} = A := by
  refine le_antisymm ((Subgroup.closure_le A).2 fun _ hx => hx.1) fun x hx => ?_
  by_cases h : x = 1
  · rw [h]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hx, h⟩

theorem involutionSubgroup_eq {R A : Subgroup G}
    (h : ∀ x, x ∈ R ∧ orderOf x = 2 ↔ x ∈ A ∧ x ≠ 1) : involutionSubgroup R = A := by
  rw [← closure_ne_one_eq A]
  exact congrArg Subgroup.closure (Set.ext h)

theorem orderOf_map_of_injOn {G' : Type*} [Group G'] {φ : G →* G'} {R : Subgroup G}
    (hinj : Set.InjOn φ R) {x : G} (hx : x ∈ R) : orderOf (φ x) = orderOf x :=
  (orderOf_injective (φ.comp R.subtype) (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
    ⟨x, hx⟩).trans (Subgroup.orderOf_mk x hx)

theorem involutionSubgroup_map {G' : Type*} [Group G'] (φ : G →* G') {R : Subgroup G}
    (hinj : Set.InjOn φ R) : (involutionSubgroup R).map φ = involutionSubgroup (R.map φ) := by
  change (Subgroup.closure _).map φ = Subgroup.closure _
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxR, hx⟩, rfl⟩
    exact ⟨⟨x, hxR, rfl⟩, (orderOf_map_of_injOn hinj hxR).trans hx⟩
  · rintro ⟨⟨x, hxR, rfl⟩, hy⟩
    exact ⟨x, ⟨hxR, (orderOf_map_of_injOn hinj hxR).symm.trans hy⟩, rfl⟩

@[expose] def IsSingerAction (A : Subgroup G) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F), Nat.card F = q ∧ ∃ e : Additive A ≃+ F,
    ∀ σ : MulAut A, σ ∈ A.normalizerMonoidHom.range ↔
      ∃ c : Fˣ, ∀ x : A, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x)

theorem IsSingerAction.of_map {G' : Type*} [Group G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {A : Subgroup G} (hinj : Set.InjOn φ A)
    (hN : ∀ g : G, φ g ∈ Subgroup.normalizer ((A.map φ : Subgroup G') : Set G') →
      g ∈ Subgroup.normalizer (A : Set G))
    {q : ℕ} (h : IsSingerAction (A.map φ) q) : IsSingerAction A q := by
  obtain ⟨F, _, hF, e, he⟩ := h
  have hψinj : Function.Injective (φ.subgroupMap A) := fun x y hxy =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  let ψ : A ≃* A.map φ :=
    MulEquiv.ofBijective (φ.subgroupMap A) ⟨hψinj, φ.subgroupMap_surjective A⟩
  have hψ (x : A) : ((ψ x : A.map φ) : G') = φ x := rfl
  refine ⟨F, inferInstance, hF, (MulEquiv.toAdditive ψ).trans e, fun σ => ?_⟩
  let σ' : MulAut (A.map φ) := ψ.symm.trans (σ.trans ψ)
  have hσ' (x : A) : σ' (ψ x) = ψ (σ x) := by
    simp only [σ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have key : σ ∈ A.normalizerMonoidHom.range ↔
      σ' ∈ (A.map φ).normalizerMonoidHom.range := by
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨⟨φ g, Subgroup.le_normalizer_map φ ⟨g, g.2, rfl⟩⟩, MulEquiv.ext fun y => ?_⟩
      obtain ⟨x, rfl⟩ := ψ.surjective y
      rw [hσ']
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hψ, hψ,
        Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_mul, map_inv]
    · rintro ⟨g', hg'⟩
      obtain ⟨g, hg⟩ := hφ g'
      have hgN : g ∈ Subgroup.normalizer (A : Set G) := hN g (hg ▸ g'.2)
      refine ⟨⟨g, hgN⟩, MulEquiv.ext fun x => hψinj (Subtype.ext ?_)⟩
      have h1 := congrArg (fun τ : MulAut (A.map φ) => ((τ (ψ x) : A.map φ) : G')) hg'
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, hσ', hψ] at h1
      change φ ((A.normalizerMonoidHom ⟨g, hgN⟩ x : A) : G) = φ (σ x : G)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, map_mul, map_mul, map_inv, hg]
      exact h1
  rw [key, he]
  refine exists_congr fun c => ⟨fun hc x => ?_, fun hc y => ?_⟩
  · have h1 := hc (ψ x)
    rw [hσ'] at h1
    exact h1
  · obtain ⟨x, rfl⟩ := ψ.surjective y
    rw [hσ']
    exact hc x

theorem IsSingerAction.map_mulEquiv {G' : Type*} [Group G'] (E : G ≃* G') {A : Subgroup G}
    {q : ℕ} (h : IsSingerAction A q) : IsSingerAction (A.map E.toMonoidHom) q := by
  have hA : (A.map E.toMonoidHom).map E.symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp
  refine IsSingerAction.of_map E.symm.surjective E.symm.injective.injOn (fun g hg => ?_)
    (by rw [hA]; exact h)
  rw [hA] at hg
  have h1 := Subgroup.le_normalizer_map E.toMonoidHom ⟨_, hg, rfl⟩
  simpa using h1

theorem IsSingerAction.sylow [Finite G] {p : ℕ} [Fact p.Prime] {Q₀ : Sylow p G} {q : ℕ}
    (h : IsSingerAction (involutionSubgroup (Q₀ : Subgroup G)) q) (Q : Sylow p G) :
    IsSingerAction (involutionSubgroup (Q : Subgroup G)) q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G Q₀ Q
  have hQ : ((g • Q₀ : Sylow p G) : Subgroup G) =
      (Q₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hQ, ← involutionSubgroup_map _ (MulAut.conj g).injective.injOn]
  exact h.map_mulEquiv (MulAut.conj g)

theorem eq_one_of_pow_two_pow_of_odd {H : Subgroup G} (hodd : Odd (Nat.card H)) {c : G}
    (hc : c ∈ H) {n : ℕ} (hn : c ^ 2 ^ n = 1) : c = 1 := by
  have h1 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : (orderOf c).Coprime (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd))
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard H hc))

theorem mem_of_map_mem_of_central_odd {G' : Type*} [Group G'] {φ : G →* G'}
    (hker : φ.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card φ.ker)) {U : Subgroup G}
    (hU : IsPGroup 2 U) {y : G} {n : ℕ} (hy : y ^ 2 ^ n = 1) (hφy : φ y ∈ U.map φ) :
    y ∈ U := by
  obtain ⟨u, hu, hφu⟩ := hφy
  obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hc : u⁻¹ * y ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφu, inv_mul_cancel]
  have hcomm : Commute u (u⁻¹ * y) := Subgroup.mem_center_iff.1 (hker hc) u
  have hyN : y ^ 2 ^ (n + k) = 1 := by rw [pow_add, pow_mul, hy, one_pow]
  have huN : u ^ 2 ^ (n + k) = 1 := by rw [add_comm, pow_add, pow_mul, hk', one_pow]
  have hpow : (u⁻¹ * y) ^ 2 ^ (n + k) = 1 := by
    have h := hcomm.mul_pow (2 ^ (n + k))
    rwa [mul_inv_cancel_left, hyN, huN, one_mul, eq_comm] at h
  have h1 := eq_one_of_pow_two_pow_of_odd hodd hc hpow
  rw [inv_mul_eq_one] at h1
  rw [← h1]
  exact hu

theorem IsSingerAction.of_central_odd_kernel [Finite G] {G' : Type*} [Group G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card φ.ker)) (R : Sylow 2 G) {q : ℕ}
    (h : IsSingerAction (involutionSubgroup ((R : Subgroup G).map φ)) q) :
    IsSingerAction (involutionSubgroup (R : Subgroup G)) q := by
  have hpow : ∀ x ∈ (R : Subgroup G), ∃ n : ℕ, x ^ 2 ^ n = 1 := fun x hx => by
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨x, hx⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hinj : Set.InjOn φ (R : Subgroup G) := fun x hx y hy hxy => by
    obtain ⟨n, hn⟩ := hpow _ ((R : Subgroup G).mul_mem ((R : Subgroup G).inv_mem hx) hy)
    have hk : x⁻¹ * y ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    exact inv_mul_eq_one.1 (eq_one_of_pow_two_pow_of_odd hodd hk hn)
  have hUR : involutionSubgroup (R : Subgroup G) ≤ R := involutionSubgroup_le _
  have hUmap := involutionSubgroup_map φ hinj
  have hUp : IsPGroup 2 (involutionSubgroup (R : Subgroup G)) := R.isPGroup'.to_le hUR
  have hconj : ∀ g : G, φ g ∈ Subgroup.normalizer
      (((involutionSubgroup (R : Subgroup G)).map φ : Subgroup G') : Set G') →
      ∀ x ∈ involutionSubgroup (R : Subgroup G),
        g * x * g⁻¹ ∈ involutionSubgroup (R : Subgroup G) := fun g hg x hx => by
    obtain ⟨n, hn⟩ := hpow x (hUR hx)
    refine mem_of_map_mem_of_central_odd hker hodd hUp (n := n)
      (by rw [conj_pow, hn, mul_one, mul_inv_cancel]) ?_
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hg (φ x)).1 ⟨x, hx, rfl⟩
  refine IsSingerAction.of_map hφ (hinj.mono fun x hx => hUR hx) (fun g hg => ?_)
    (by rw [hUmap]; exact h)
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj g hg x, fun hx => ?_⟩
  have h1 := hconj g⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using h1

theorem isSingerAction_of_central_odd_quotient [Finite G] {J : Type*} [Group J]
    (C : Subgroup G) [C.Normal] (hC : C ≤ Subgroup.center G) (hCodd : Odd (Nat.card C))
    (E : G ⧸ C ≃* J) {q : ℕ}
    (hJ : ∀ Q : Sylow 2 J, IsSingerAction (involutionSubgroup (Q : Subgroup J)) q)
    (R : Sylow 2 G) : IsSingerAction (involutionSubgroup (R : Subgroup G)) q := by
  let φ : G →* J := E.toMonoidHom.comp (QuotientGroup.mk' C)
  have hφ : Function.Surjective φ := E.surjective.comp (QuotientGroup.mk'_surjective C)
  have hker : φ.ker = C := by
    ext x
    simp [φ]
  refine IsSingerAction.of_central_odd_kernel hφ (hker ▸ hC) (hker ▸ hCodd) R ?_
  rw [← Sylow.coe_mapSurjective hφ R]
  exact hJ _

@[expose] def singerScalarAut {A F : Type*} [Group A] [Field F] (e : Additive A ≃+ F)
    (c : Fˣ) : MulAut A where
  toFun x := Additive.toMul (e.symm (c * e (Additive.ofMul x)))
  invFun x := Additive.toMul (e.symm ((c⁻¹ : Fˣ) * e (Additive.ofMul x)))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [mul_add]

theorem apply_singerScalarAut {A F : Type*} [Group A] [Field F] (e : Additive A ≃+ F)
    (c : Fˣ) (x : A) : e (Additive.ofMul (singerScalarAut e c x)) = c * e (Additive.ofMul x) := by
  simp [singerScalarAut]

@[expose] def singerScalarHom {A F : Type*} [Group A] [Field F] (e : Additive A ≃+ F) :
    Fˣ →* MulAut A where
  toFun := singerScalarAut e
  map_one' := MulEquiv.ext fun x => by simp [singerScalarAut]
  map_mul' c d := MulEquiv.ext fun x => by simp [singerScalarAut, mul_assoc]

theorem singerScalarHom_injective {A F : Type*} [Group A] [Field F] (e : Additive A ≃+ F) :
    Function.Injective (singerScalarHom e) := fun c d h => by
  have h1 := congrArg (fun σ : MulAut A =>
    e (Additive.ofMul (σ (Additive.toMul (e.symm 1))))) h
  simp only [singerScalarHom, MonoidHom.coe_mk, OneHom.coe_mk, apply_singerScalarAut,
    ofMul_toMul, AddEquiv.apply_symm_apply, mul_one] at h1
  exact Units.ext h1

theorem range_normalizerMonoidHom_eq {A : Subgroup G} {F : Type*} [Field F]
    {e : Additive A ≃+ F}
    (he : ∀ σ : MulAut A, σ ∈ A.normalizerMonoidHom.range ↔
      ∃ c : Fˣ, ∀ x : A, e (Additive.ofMul (σ x)) = c * e (Additive.ofMul x)) :
    A.normalizerMonoidHom.range = (singerScalarHom e).range := by
  ext σ
  rw [he, MonoidHom.mem_range]
  refine exists_congr fun c => ⟨fun hc => MulEquiv.ext fun x => ?_, ?_⟩
  · apply Additive.ofMul.injective
    apply e.injective
    rw [hc]
    exact apply_singerScalarAut e c x
  · rintro rfl x
    exact apply_singerScalarAut e c x

theorem IsSingerAction.conclusion {A : Subgroup G} {f : ℕ} (hf : f ≠ 0)
    (h : IsSingerAction A (2 ^ f)) :
    IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ f ∧ IsCyclic A.normalizerMonoidHom.range ∧
      Nat.card A.normalizerMonoidHom.range = 2 ^ f - 1 ∧
      (∀ x y : A, x ≠ 1 → y ≠ 1 →
        ∃! σ : A.normalizerMonoidHom.range, (σ : MulAut A) x = y) ∧
      IsSingerAction A (2 ^ f) := by
  obtain ⟨F, _, hF, e, he⟩ := id h
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hrange := range_normalizerMonoidHom_eq he
  have hinj := singerScalarHom_injective e
  have hinj' : Function.Injective fun x : A => e (Additive.ofMul x) :=
    e.injective.comp Additive.ofMul.injective
  refine ⟨?_, (Nat.card_congr (Additive.ofMul.trans e.toEquiv)).trans hF, ?_, ?_, ?_, h⟩
  · have h2 : (2 : F) = 0 := by
      have := Fintype.ofFinite F
      have h := FiniteField.cast_card_eq_zero F
      rw [Fintype.card_eq_nat_card, hF, Nat.cast_pow, Nat.cast_ofNat] at h
      exact (pow_eq_zero_iff hf).1 h
    refine
      { is_comm := ⟨fun x y => hinj' ?_⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hinj' ?_ }
    · simp only [ofMul_mul, map_add, add_comm]
    · simp only [ofMul_pow, map_nsmul, ofMul_one, map_zero, nsmul_eq_mul, Nat.cast_ofNat, h2,
        zero_mul]
  · rw [hrange]
    exact isCyclic_of_surjective (singerScalarHom e).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  · rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hF]
  · intro x y hx hy
    have hex : e (Additive.ofMul x) ≠ 0 := by
      rw [Ne, ← map_zero e, e.injective.eq_iff, ofMul_eq_zero]
      exact hx
    have hey : e (Additive.ofMul y) ≠ 0 := by
      rw [Ne, ← map_zero e, e.injective.eq_iff, ofMul_eq_zero]
      exact hy
    let c : Fˣ := Units.mk0 (e (Additive.ofMul y) / e (Additive.ofMul x)) (div_ne_zero hey hex)
    have hmem : singerScalarHom e c ∈ A.normalizerMonoidHom.range := by
      rw [hrange]
      exact ⟨c, rfl⟩
    refine ⟨⟨_, hmem⟩, hinj' ?_, ?_⟩
    · change e (Additive.ofMul (singerScalarAut e c x)) = _
      rw [apply_singerScalarAut, Units.val_mk0, div_mul_cancel₀ _ hex]
    · rintro ⟨σ, hσ⟩ hσx
      rw [hrange] at hσ
      obtain ⟨d, rfl⟩ := hσ
      have h1 := congrArg (fun z : A => e (Additive.ofMul z)) hσx
      change e (Additive.ofMul (singerScalarAut e d x)) = _ at h1
      rw [apply_singerScalarAut] at h1
      have hdc : d = c := Units.ext (by rw [Units.val_mk0, eq_div_iff hex, h1])
      subst hdc
      rfl

@[expose] def rootScalarSubgroup {F : Type*} [Field F] (ι : Multiplicative F →* G) :
    Subgroup G where
  carrier := {g | ∃ c : Fˣ, ∀ b : F,
    g * ι (Multiplicative.ofAdd b) * g⁻¹ = ι (Multiplicative.ofAdd (c * b))}
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun b => ?_⟩
    rw [show g * h * ι (Multiplicative.ofAdd b) * (g * h)⁻¹ =
        g * (h * ι (Multiplicative.ofAdd b) * h⁻¹) * g⁻¹ by group, hd, hc, Units.val_mul,
      mul_assoc]
  one_mem' := ⟨1, fun b => by simp⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun b => ?_⟩
    have h := hc ((c⁻¹ : Fˣ) * b)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    rw [← h]
    group

theorem mem_rootScalarSubgroup {F : Type*} [Field F] {ι : Multiplicative F →* G} {g : G} :
    g ∈ rootScalarSubgroup ι ↔ ∃ c : Fˣ, ∀ b : F,
      g * ι (Multiplicative.ofAdd b) * g⁻¹ = ι (Multiplicative.ofAdd (c * b)) :=
  Iff.rfl

theorem rootScalarSubgroup_le_normalizer {F : Type*} [Field F] (ι : Multiplicative F →* G) :
    rootScalarSubgroup ι ≤ Subgroup.normalizer (ι.range : Set G) := by
  have hconj : ∀ g ∈ rootScalarSubgroup ι, ∀ x ∈ ι.range, g * x * g⁻¹ ∈ ι.range := by
    rintro g ⟨c, hc⟩ _ ⟨b, rfl⟩
    exact ⟨_, (hc (Multiplicative.toAdd b)).symm⟩
  intro g hg
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj g hg x, fun hx => ?_⟩
  have h1 := hconj g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using h1

theorem isSingerAction_range {F : Type} [Field F] (ι : Multiplicative F →* G)
    (hι : Function.Injective ι)
    (hN : Subgroup.normalizer (ι.range : Set G) ≤ rootScalarSubgroup ι)
    (hT : ∀ c : Fˣ, ∃ g : G, ∀ b : F,
      g * ι (Multiplicative.ofAdd b) * g⁻¹ = ι (Multiplicative.ofAdd (c * b))) :
    IsSingerAction ι.range (Nat.card F) := by
  let ψ : Multiplicative F ≃* ι.range := MonoidHom.ofInjective hι
  let e : Additive ι.range ≃+ F := MulEquiv.toAdditiveLeft ψ.symm
  have he (b : F) : e (Additive.ofMul (ψ (Multiplicative.ofAdd b))) = b := by
    simp [e]
  have hψ (b : F) : ((ψ (Multiplicative.ofAdd b) : ι.range) : G) =
      ι (Multiplicative.ofAdd b) := rfl
  have hconj : ∀ (g : Subgroup.normalizer (ι.range : Set G)) (c : Fˣ),
      (∀ b : F, (g : G) * ι (Multiplicative.ofAdd b) * (g : G)⁻¹ =
        ι (Multiplicative.ofAdd (c * b))) →
      ∀ b : F, ι.range.normalizerMonoidHom g (ψ (Multiplicative.ofAdd b)) =
        ψ (Multiplicative.ofAdd (c * b)) := fun g c hc b => by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hψ, hψ, hc]
  refine ⟨F, inferInstance, rfl, e, fun σ => ⟨?_, ?_⟩⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := hN g.2
    refine ⟨c, fun x => ?_⟩
    obtain ⟨b, rfl⟩ := ψ.surjective x
    rw [← ofAdd_toAdd b, hconj g c hc, he, he]
  · rintro ⟨c, hc⟩
    obtain ⟨g, hg⟩ := hT c
    have hgN : g ∈ Subgroup.normalizer (ι.range : Set G) :=
      rootScalarSubgroup_le_normalizer ι ⟨c, hg⟩
    refine ⟨⟨g, hgN⟩, MulEquiv.ext fun x => ?_⟩
    obtain ⟨b, rfl⟩ := ψ.surjective x
    rw [← ofAdd_toAdd b, hconj ⟨g, hgN⟩ c hg]
    apply Additive.ofMul.injective
    apply e.injective
    rw [hc, he, he]

theorem isSingerAction_sylow_of_range [Finite G] {F : Type} [Field F]
    (ι : Multiplicative F →* G) (hι : Function.Injective ι) (Q₀ : Sylow 2 G)
    (hQ₀ : involutionSubgroup (Q₀ : Subgroup G) = ι.range)
    (hN : Subgroup.normalizer (ι.range : Set G) ≤ rootScalarSubgroup ι)
    (hT : ∀ c : Fˣ, ∃ g : G, ∀ b : F,
      g * ι (Multiplicative.ofAdd b) * g⁻¹ = ι (Multiplicative.ofAdd (c * b)))
    (Q : Sylow 2 G) : IsSingerAction (involutionSubgroup (Q : Subgroup G)) (Nat.card F) :=
  IsSingerAction.sylow (Q₀ := Q₀) (by rw [hQ₀]; exact isSingerAction_range ι hι hN hT) Q

theorem fixes_of_mem_normalizer {X : Type*} (ρ : G →* Equiv.Perm X) {α : X} {A : Subgroup G}
    (hfix : ∀ a ∈ A, ρ a α = α) (hfree : ∀ a ∈ A, ∀ x : X, ρ a x = x → x ≠ α → a = 1)
    (hA : A ≠ ⊥) {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) : ρ g α = α := by
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  by_contra hgα
  have hb : g⁻¹ * a * g ∈ A := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) a).1 haA
    rwa [inv_inv] at h1
  have h1 := hfix _ hb
  rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_eq_iff_eq] at h1
  exact ha1 (Subtype.ext (hfree a haA _ h1 hgα))

theorem eq_one_of_regular {X : Type*} (ρ : G →* Equiv.Perm X) {α : X} {Q : Subgroup G}
    (hreg : ∀ x y : X, x ≠ α → y ≠ α → ∃! u : Q, ρ u x = y) {a : G} (ha : a ∈ Q) {x : X}
    (hx : ρ a x = x) (hxα : x ≠ α) : a = 1 := by
  obtain ⟨u, -, huniq⟩ := hreg x x hxα hxα
  have h1 := huniq ⟨a, ha⟩ hx
  have h2 := huniq 1 (by simp)
  exact congrArg Subtype.val (h1.trans h2.symm)

end CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger

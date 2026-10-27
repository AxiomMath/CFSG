module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAction

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Module Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule
open scoped IsMulCommutative Matrix

section Nine

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) K W) (σ : W →ₗ[ZMod 2] W)
  (hσσ : ∀ w, σ (σ w) = w) (hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w))
  (A : Submodule (ZMod 2) W) (hA : ∀ w, w ∈ A ↔ σ w = w)
  (β : Sym3 ≃ₗ[ZMod 2] A) (hβ : ∀ (g : S) (B : Sym3), ρ (g, g) (β B : W) = β (symThreeCongr g B))

include hσσ hσρ hA hβ in
theorem exists_tensor_model_of_sym (hW : finrank (ZMod 2) W = 9) :
    ∃ (Φ : W ≃ₗ[ZMod 2] Mat3) (α : S ≃* S),
      (∀ k w, Φ (ρ k w) = repM (α k.1, α k.2) (Φ w)) ∧ ∀ w, Φ (σ w) = (Φ w)ᵀ := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have hdA : finrank (ZMod 2) A = 6 := by rw [← β.finrank_eq, finrank_sym3]
  have hkerA : LinearMap.ker (σ - LinearMap.id) = A := by
    ext w
    rw [LinearMap.mem_ker, hA, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  set I := LinearMap.range (σ - LinearMap.id) with hI
  have hIA : I ≤ A := by
    rintro _ ⟨w, rfl⟩
    rw [hA, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hσσ]
    rw [sub_eq_add_neg, sub_eq_add_neg, ZModModule.neg_eq_self, ZModModule.neg_eq_self, add_comm]
  have hIdim : finrank (ZMod 2) I = 3 := by
    have h := LinearMap.finrank_range_add_finrank_ker (σ - LinearMap.id)
    rw [hkerA, hdA, hW, ← hI] at h
    omega
  have hσdiag : ∀ (g : S) (w : W), (σ - LinearMap.id : W →ₗ[ZMod 2] W) (ρ (g, g) w) =
      ρ (g, g) ((σ - LinearMap.id : W →ₗ[ZMod 2] W) w) := fun g w => by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, sigma_diag ρ σ hσρ]
  have hdims : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, ρ (g, g) u ∈ U) →
      finrank (ZMod 2) U = 0 ∨ finrank (ZMod 2) U = 3 ∨ finrank (ZMod 2) U = 6 ∨
        finrank (ZMod 2) U = 9 := by
    intro U hU
    set f : U →ₗ[ZMod 2] W := (σ - LinearMap.id).domRestrict U with hf
    have hker : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) ↥(U ⊓ A) := by
      have e : LinearMap.ker f ≃ₗ[ZMod 2] ↥(U ⊓ A) :=
        { toFun := fun x => ⟨(x : U), Submodule.mem_inf.2 ⟨(x : U).2, (hA _).2 (by
            have h := LinearMap.mem_ker.1 x.2
            change σ ((x : U) : W) - ((x : U) : W) = 0 at h
            exact sub_eq_zero.1 h)⟩⟩
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl
          invFun := fun y => ⟨⟨y, (Submodule.mem_inf.1 y.2).1⟩, LinearMap.mem_ker.2 (by
            change σ (y : W) - (y : W) = 0
            rw [(hA _).1 (Submodule.mem_inf.1 y.2).2, sub_self])⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      exact e.finrank_eq
    have hrange : ∀ g : S, ∀ u ∈ LinearMap.range f, ρ (g, g) u ∈ LinearMap.range f := by
      rintro g _ ⟨x, rfl⟩
      exact ⟨⟨ρ (g, g) x, hU g _ x.2⟩, hσdiag g x⟩
    have hrI : LinearMap.range f ≤ I := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    have hr := finrank_inf_A ρ A β hβ (LinearMap.range f) hrange
    rw [inf_of_le_left (hrI.trans hIA)] at hr
    have hrle := Submodule.finrank_mono hrI
    have hk := finrank_inf_A ρ A β hβ U hU
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    rw [hker] at hsum
    omega
  have hfix : ∀ w, (∀ g, ρ (g, g) w = w) → w = 0 := fun w hw => by
    have hinv : ∀ (g : S), ∀ u ∈ Submodule.span (ZMod 2) {w},
        ρ (g, g) u ∈ Submodule.span (ZMod 2) {w} := fun g u hu => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [map_smul, hw g]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)
    by_contra hw0
    have h := hdims _ hinv
    rw [finrank_span_singleton hw0] at h
    omega
  have hnt : ∃ g w, σ w = w ∧ ρ (g, g) w - w ∉ LinearMap.range (σ - LinearMap.id) := by
    refine ⟨tLow₁, β E11, (hA _).1 (β E11).2, fun hmem => ?_⟩
    set U' : AddSubgroup Sym3 :=
      { carrier := {B | (β B : W) ∈ I}
        add_mem' := fun {B B'} hB hB' => by
          change ((β (B + B') : A) : W) ∈ I
          rw [map_add, Submodule.coe_add]
          exact I.add_mem hB hB'
        zero_mem' := by
          change ((β 0 : A) : W) ∈ I
          rw [map_zero, Submodule.coe_zero]
          exact I.zero_mem
        neg_mem' := fun {B} hB => by
          change ((β (-B) : A) : W) ∈ I
          rw [map_neg, Submodule.coe_neg]
          exact I.neg_mem hB } with hU'
    have hinv : ∀ (g : S), ∀ B ∈ U', symThreeCongr g B ∈ U' := fun g B hB => by
      change ((β (symThreeCongr g B) : A) : W) ∈ I
      rw [← hβ]
      obtain ⟨w, hw⟩ := hB
      exact ⟨ρ (g, g) w, by rw [hσdiag, hw]⟩
    have hcard : Nat.card U' = 8 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have e : U' ≃ I := Equiv.ofBijective (fun B => ⟨β B.1, B.2⟩) ⟨fun B B' h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (β.injective (Subtype.ext h')), fun x => by
          refine ⟨⟨β.symm ⟨x, hIA x.2⟩, ?_⟩, Subtype.ext ?_⟩
          · change ((β (β.symm ⟨x, hIA x.2⟩) : A) : W) ∈ I
            rw [LinearEquiv.apply_symm_apply]
            exact x.2
          · change ((β (β.symm ⟨x, hIA x.2⟩) : A) : W) = x
            rw [LinearEquiv.apply_symm_apply]⟩
      rw [Nat.card_congr e, ← FiniteField.pow_finrank_eq_natCard 2, hIdim]
      norm_num
    have hdiag0 : ∀ B : Sym3, B ∈ U' → symThreeDiag (B : Mat3) = 0 := by
      rcases invariant_addSubgroup U' hinv with h | h | h
      · rw [h, AddSubgroup.card_bot] at hcard
        norm_num at hcard
      · exact fun B hB => (h B).1 hB
      · rw [h, AddSubgroup.card_top, card_symThree] at hcard
        norm_num at hcard
    apply symThreeDiag_congr_sub_ne_zero
    apply hdiag0
    change ((β (symThreeCongr tLow₁ E11 - E11) : A) : W) ∈ I
    rw [map_sub, Submodule.coe_sub, ← hβ]
    exact hmem
  exact exists_tensor_model ρ σ hσσ hσρ hfix hdims hW (by rw [hkerA, hdA]) hnt

end Nine

@[expose] def alphaHat (α : S ≃* S) : Ehat ≃* Ehat :=
  SemidirectProduct.congr (MulEquiv.prodCongr α α) (MulEquiv.refl _) fun ε => by
    rcases mult_two_cases ε with rfl | rfl
    · exact MulEquiv.ext fun k => rfl
    · exact MulEquiv.ext fun k => rfl

theorem alphaHat_right (α : S ≃* S) (e : Ehat) : (alphaHat α e).right = e.right := rfl

section Model9

variable {F : Type*} [Group F] {C : Type*} [Group C] [Finite C]
  [Fact (Nat.Prime 2)] [CFSG.IsElementaryAbelian 2 C]

theorem exists_model_of_two_factor9 (hC : Nat.card C = 2 ^ 9) (κ : F →* MulAut C)
    {Y : Type*} [Group Y] (θ : F →* Y) {R : Subgroup F} (hθker : θ.ker = R)
    {D : Subgroup Y} [D.Normal] (Ψ : D ≃* K) {a : F} (ha : a * a = 1)
    (hΨa : ∀ (d : Y) (hd : d ∈ D) (hda : (θ a)⁻¹ * d * θ a ∈ D), Ψ ⟨_, hda⟩ = (Ψ ⟨d, hd⟩).swap)
    (χ : Y →* Multiplicative (ZMod 2)) (hχa : χ (θ a) = Multiplicative.ofAdd 1) (hχ : χ.ker = D)
    {Q : Subgroup F} [Q.Normal] (hQD : Q.map θ = D) (hcomap : D.comap θ = R ⊔ Q)
    (hRQ : ∀ x ∈ D.comap θ, ∀ r ∈ R, x * r = r * x)
    (η : Q ≃* K) (hη : ∀ (q : Q) (hq : θ q ∈ D), η q = Ψ ⟨θ q, hq⟩)
    {A : Subgroup C} (hA : ∀ c : C, κ a c = c ↔ c ∈ A) (τ : Multiplicative Sym3 ≃* A)
    (hτ : ∀ (g : S) (B : Sym3), κ ((η.symm (g, g) : Q) : F) ((τ (Multiplicative.ofAdd B) : A) : C) =
      ((τ (Multiplicative.ofAdd (symThreeCongr g B)) : A) : C)) :
    ∃ (Ω : Y ≃* Ehat) (Φ : Mat3 ≃ₗ[ZMod 2] Additive C),
      (∀ y : Y, (Ω y).right = χ y) ∧ Ω (θ a) = sE ∧ (∀ r ∈ R, ∀ c : C, κ r c = c) ∧
      ∀ (f : F) (x : Mat3), conjRep κ f (Φ x) = Φ (repE (Ω (θ f)) x) := by
  classical
  have hā2 : θ a * θ a = 1 := by rw [← map_mul, ha, map_one]
  have hāinv : (θ a)⁻¹ = θ a := inv_eq_of_mul_eq_one_right hā2
  obtain ⟨Ω₀, hΩD, hΩa⟩ := exists_mulEquiv_Ehat D Ψ hā2 (fun d => by
    have hda : (θ a)⁻¹ * (d : Y) * θ a ∈ D := by
      have := (inferInstance : D.Normal).conj_mem _ d.2 (θ a)⁻¹
      rwa [inv_inv] at this
    have h2 : MulAut.conjNormal (θ a) d = ⟨_, hda⟩ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change θ a * (d : Y) * (θ a)⁻¹ = (θ a)⁻¹ * d * θ a
      rw [hāinv])
    rw [h2, hΨa]) χ hχa hχ
  set ρF := conjRep κ with hρF
  set ρ : Representation (ZMod 2) K (Additive C) :=
    ρF.comp (Q.subtype.comp η.symm.toMonoidHom) with hρ
  set σ : Additive C →ₗ[ZMod 2] Additive C := ρF a with hσ
  have hρapply : ∀ k w, ρ k w = ρF ((η.symm k : Q) : F) w := fun k w => rfl
  have hθQ : ∀ q : Q, θ q ∈ D := fun q => hQD ▸ mem_map_of_mem θ q.2
  have hσσ : ∀ w, σ (σ w) = w := fun w => by
    change ρF a (ρF a w) = w
    rw [← Module.End.mul_apply, ← map_mul, ha, map_one, Module.End.one_apply]
  have hconj : ∀ k : K, a * ((η.symm k : Q) : F) * a⁻¹ = ((η.symm k.swap : Q) : F) := by
    intro k
    set q := η.symm k with hq
    have hmem : a * (q : F) * a⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem _ q.2 a
    have h1 : η ⟨_, hmem⟩ = k.swap := by
      have hθ' : θ (a * (q : F) * a⁻¹) = (θ a)⁻¹ * θ q * θ a := by
        rw [map_mul, map_mul, map_inv, hāinv]
      rw [hη ⟨_, hmem⟩ (hθQ _)]
      have e : (⟨θ (a * (q : F) * a⁻¹), hθQ ⟨_, hmem⟩⟩ : D) =
          ⟨(θ a)⁻¹ * θ q * θ a, hθ' ▸ hθQ ⟨_, hmem⟩⟩ := Subtype.ext hθ'
      rw [e, hΨa _ (hθQ q), ← hη q (hθQ q), hq, MulEquiv.apply_symm_apply]
    have h2 : (⟨_, hmem⟩ : Q) = η.symm k.swap := by rw [← h1, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h2
  have hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w) := fun k w => by
    change ρF a (ρF ((η.symm k : Q) : F) w) = ρF ((η.symm k.swap : Q) : F) (ρF a w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← hconj k]
    congr 2
    group
  set Asub := subOf A with hAsub
  have hAiff : ∀ w, w ∈ Asub ↔ σ w = w := fun w => by
    rw [mem_subOf, ← hA]
    constructor
    · intro h
      exact congrArg Additive.ofMul h
    · intro h
      exact congrArg Additive.toMul h
  let β₀ : Sym3 →+ Additive C :=
    { toFun := fun B => Additive.ofMul ((τ (Multiplicative.ofAdd B) : A) : C)
      map_zero' := by simp
      map_add' := fun B B' => by
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        rfl }
  have hβ₀mem : ∀ B, β₀ B ∈ Asub := fun B => (τ (Multiplicative.ofAdd B)).2
  let β₁ : Sym3 →ₗ[ZMod 2] Asub :=
    (AddMonoidHom.toZModLinearMap 2 β₀).codRestrict Asub hβ₀mem
  have hβ₁bij : Function.Bijective β₁ := by
    constructor
    · intro B B' h
      have h1 : ((τ (Multiplicative.ofAdd B) : A) : C) = ((τ (Multiplicative.ofAdd B') : A) : C) :=
        congrArg (fun x : Asub => Additive.toMul (x : Additive C)) h
      exact Multiplicative.ofAdd.injective (τ.injective (Subtype.ext h1))
    · rintro ⟨w, hw⟩
      refine ⟨Multiplicative.toAdd (τ.symm ⟨Additive.toMul w, hw⟩), Subtype.ext ?_⟩
      change Additive.ofMul ((τ (Multiplicative.ofAdd (Multiplicative.toAdd
        (τ.symm ⟨Additive.toMul w, hw⟩))) : A) : C) = w
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rfl
  let β : Sym3 ≃ₗ[ZMod 2] Asub := LinearEquiv.ofBijective β₁ hβ₁bij
  have hβapply : ∀ B, (β B : Additive C) = Additive.ofMul ((τ (Multiplicative.ofAdd B) : A) : C) :=
    fun B => rfl
  have hβ : ∀ (g : S) (B : Sym3), ρ (g, g) (β B : Additive C) = β (symThreeCongr g B) :=
    fun g B => by
      rw [hρapply, hβapply, hβapply, hρF, conjRep_ofMul, hτ]
  have hW : finrank (ZMod 2) (Additive C) = 9 := finrank_additive hC
  obtain ⟨Φ₀, α, hΦρ, hΦσ⟩ := exists_tensor_model_of_sym ρ σ hσσ hσρ Asub hAiff β hβ hW
  have hQcomap : ∀ q : Q, (q : F) ∈ D.comap θ := fun q => hθQ q
  have hRtriv : ∀ r ∈ R, ∀ w, ρF r w = w := by
    intro r hr
    set Fr : Module.End (ZMod 2) Mat3 :=
      Φ₀.toLinearMap ∘ₗ ρF r ∘ₗ Φ₀.symm.toLinearMap with hFr
    have hFapply : ∀ x, Fr x = Φ₀ (ρF r (Φ₀.symm x)) := fun x => rfl
    have hcomm : ∀ k, Fr * repM k = repM k * Fr := by
      intro k
      set k' : K := (α.symm k.1, α.symm k.2) with hk'
      have hk : ((α k'.1, α k'.2) : K) = k := by
        rw [hk', MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      ext1 x
      rw [Module.End.mul_apply, Module.End.mul_apply, hFapply, hFapply, ← hk]
      have e1 : Φ₀.symm (repM (α k'.1, α k'.2) x) = ρ k' (Φ₀.symm x) := by
        apply Φ₀.injective
        rw [LinearEquiv.apply_symm_apply, hΦρ, LinearEquiv.apply_symm_apply]
      rw [e1, ← hΦρ, hρapply, hρapply, ← Module.End.mul_apply, ← map_mul,
        ← Module.End.mul_apply, ← map_mul, hRQ _ (hQcomap (η.symm k')) r hr]
    have hFne : Fr ≠ 0 := by
      intro h0
      have h1 : Fr 1 = 0 := by rw [h0, LinearMap.zero_apply]
      rw [hFapply, LinearEquiv.map_eq_zero_iff] at h1
      have h2 : Φ₀.symm (1 : Mat3) = 0 := by
        have h3 : linAut (κ r) (Φ₀.symm 1) = 0 := h1
        rwa [LinearEquiv.map_eq_zero_iff] at h3
      rw [LinearEquiv.map_eq_zero_iff] at h2
      exact one_ne_zero h2
    have hF1 : Fr = 1 := (repM_end_cases Fr hcomm).resolve_left hFne
    intro w
    have h1 : Fr (Φ₀ w) = Φ₀ w := by rw [hF1, Module.End.one_apply]
    rw [hFapply, LinearEquiv.symm_apply_apply] at h1
    exact Φ₀.injective h1
  set Ω : Y ≃* Ehat := Ω₀.trans (alphaHat α) with hΩ
  have hΩright : ∀ y : Y, (Ω y).right = χ y := by
    intro y
    change (alphaHat α (Ω₀ y)).right = χ y
    rw [alphaHat_right]
    rcases mult_two_cases (χ y) with h | h
    · have hy : y ∈ D := by rw [← hχ]; exact h
      rw [h, show y = ((⟨y, hy⟩ : D) : Y) from rfl, hΩD]
      rfl
    · have hy : y * (θ a)⁻¹ ∈ D := by
        rw [← hχ, MonoidHom.mem_ker, map_mul, map_inv, h, hχa, mul_inv_cancel]
      have e1 : y = ((⟨y * (θ a)⁻¹, hy⟩ : D) : Y) * θ a := by
        change y = y * (θ a)⁻¹ * θ a
        group
      rw [h, e1, map_mul, hΩD, hΩa]
      rfl
  have hΩa' : Ω (θ a) = sE := by
    change alphaHat α (Ω₀ (θ a)) = sE
    rw [hΩa]
    exact SemidirectProduct.ext (Prod.ext (map_one α) (map_one α)) rfl
  have hΩQ : ∀ q : Q, Ω (θ q) = SemidirectProduct.inl (α (η q).1, α (η q).2) := fun q => by
    have h1 : Ω₀ (θ q) = SemidirectProduct.inl (η q) := by
      rw [hη q (hθQ q)]
      exact hΩD ⟨θ q, hθQ q⟩
    change alphaHat α (Ω₀ (θ q)) = _
    rw [h1]
    rfl
  have hΩR : ∀ r ∈ R, Ω (θ r) = 1 := fun r hr => by
    rw [show θ r = 1 from (hθker ▸ hr : r ∈ θ.ker), map_one]
  set Φ : Mat3 ≃ₗ[ZMod 2] Additive C := Φ₀.symm with hΦ
  have hΦQ : ∀ (q : Q) (x : Mat3), ρF q (Φ x) = Φ (repE (Ω (θ q)) x) := by
    intro q x
    rw [hΩQ, repE_inl, show (q : F) = ((η.symm (η q) : Q) : F) by rw [MulEquiv.symm_apply_apply],
      ← hρapply]
    apply Φ₀.injective
    rw [hΦ, hΦρ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hΦa : ∀ x : Mat3, σ (Φ x) = Φ (repE (Ω (θ a)) x) := by
    intro x
    rw [hΩa', repE_sE_apply]
    apply Φ₀.injective
    rw [hΦ, hΦσ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine ⟨Ω, Φ, hΩright, hΩa', fun r hr c => ?_, ?_⟩
  · have h1 := hRtriv r hr (Additive.ofMul c)
    exact congrArg Additive.toMul h1
  have hRQmul : ∀ x ∈ D.comap θ, ∃ r ∈ R, ∃ q : Q, x = r * q := by
    intro x hx
    have hRn : R.Normal := hθker ▸ MonoidHom.normal_ker θ
    rw [hcomap, ← SetLike.mem_coe, Subgroup.normal_mul] at hx
    obtain ⟨r, hr, q, hq, rfl⟩ := hx
    exact ⟨r, hr, ⟨q, hq⟩, rfl⟩
  have hinner : ∀ (r : F) (hr : r ∈ R) (q : Q) (x : Mat3),
      ρF (r * q) (Φ x) = Φ (repE (Ω (θ (r * q))) x) := by
    intro r hr q x
    rw [map_mul, map_mul, Module.End.mul_apply, map_mul, hΩR r hr, one_mul, hRtriv r hr, hΦQ]
  intro f x
  rcases mult_two_cases (χ (θ f)) with h | h
  · have hf : f ∈ D.comap θ := by
      rw [mem_comap, ← hχ]
      exact h
    obtain ⟨r, hr, q, rfl⟩ := hRQmul f hf
    exact hinner r hr q x
  · have hf : f * a ∈ D.comap θ := by
      rw [mem_comap, ← hχ, MonoidHom.mem_ker, map_mul, map_mul, h, hχa]
      exact ofAdd_one_mul_ofAdd_one
    obtain ⟨r, hr, q, hrq⟩ := hRQmul (f * a) hf
    have hfeq : f = r * q * a := by
      rw [← hrq, mul_assoc, ha, mul_one]
    rw [hfeq, map_mul, Module.End.mul_apply, show θ (r * q * a) = θ (r * q) * θ a from
      map_mul θ _ _, map_mul Ω]
    change ρF (r * q) (σ (Φ x)) = Φ (repE (Ω (θ (r * q)) * Ω (θ a)) x)
    rw [hΦa, hinner r hr q, repE_mul_apply]

end Model9

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

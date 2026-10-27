module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellLinear
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank

public section

namespace CFSG.LieType.SteinbergBR.TransvStab

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

abbrev Ann (k : Type*) [Field k] {V : Type*} [AddCommGroup V] [Module k V] (c : V) :
    Submodule k (Dual k V) :=
  LinearMap.ker (Dual.eval k V c)

theorem ann_apply {c : V} (f : Ann k c) : (f : Dual k V) c = 0 :=
  LinearMap.mem_ker.1 f.2

@[expose] noncomputable def transvSL (c : V) (f : Ann k c) : SpecialLinearGroup k V :=
  ⟨LinearEquiv.transvection (ann_apply f), LinearEquiv.transvection.det_eq_one _⟩

@[expose] noncomputable def transvHom (c : V) : Multiplicative (Ann k c) →* SpecialLinearGroup k V
    where
  toFun f := transvSL c (Multiplicative.toAdd f)
  map_one' := SpecialLinearGroup.ext _ _ fun x => by
    change x + (0 : Dual k V) x • c = x
    rw [LinearMap.zero_apply, zero_smul, add_zero]
  map_mul' f g := SpecialLinearGroup.ext _ _ fun x => by
    change LinearMap.transvection (((Multiplicative.toAdd f : Ann k c) : Dual k V) +
      ((Multiplicative.toAdd g : Ann k c) : Dual k V)) c x = LinearMap.transvection
        ((Multiplicative.toAdd f : Ann k c) : Dual k V) c (LinearMap.transvection
          ((Multiplicative.toAdd g : Ann k c) : Dual k V) c x)
    rw [LinearMap.transvection.comp_of_right_eq_apply (ann_apply _)]

theorem transvHom_apply (c : V) (f : Multiplicative (Ann k c)) (x : V) :
    transvHom c f x = x + ((Multiplicative.toAdd f : Ann k c) : Dual k V) x • c :=
  rfl

theorem transvHom_injective {c : V} (hc : c ≠ 0) :
    Function.Injective (transvHom (k := k) c) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  have h : ∀ x, ((Multiplicative.toAdd f : Ann k c) : Dual k V) x = 0 := fun x => by
    have := congrArg (fun u : SpecialLinearGroup k V => u x) hf
    simp only [transvHom_apply] at this
    have h1 : ((Multiplicative.toAdd f : Ann k c) : Dual k V) x • c = 0 := by
      have h2 : x + ((Multiplicative.toAdd f : Ann k c) : Dual k V) x • c = x := this
      simpa using h2
    exact (smul_eq_zero.1 h1).resolve_right hc
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (LinearMap.ext h)

theorem card_ann [Finite k] {c : V} (hc : c ≠ 0) [FiniteDimensional k V] :
    Nat.card (Ann k c) = Nat.card k ^ (finrank k V - 1) := by
  have hsurj : Function.Surjective (Dual.eval k V c) := by
    intro r
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hc
    exact ⟨r • f, by rw [map_smul, Dual.eval_apply, hf, smul_eq_mul, mul_one]⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker (Dual.eval k V c)
  have h1 : finrank k (LinearMap.range (Dual.eval k V c)) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self]
  have h2 : finrank k (Dual k V) = finrank k V := Subspace.dual_finrank_eq
  rw [Module.natCard_eq_pow_finrank (K := k)]
  congr 1
  change finrank k (LinearMap.ker (Dual.eval k V c)) = _
  omega

end CFSG.LieType.SteinbergBR.TransvStab

namespace CFSG.LieType

open Module CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.TransvStab

theorem nq_natural_central_extension_transvection_stabilizers {k : Type*} [Field k] [Finite k]
    [CharP k 2] {n : ℕ} (hn : 2 ≤ n) {V : Type*} [AddCommGroup V] [Module k V]
    (hV : finrank k V = n) {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (ρ : SpecialLinearGroup k V →* (E ≃ₗ[ZMod 2] E))
    (φ : E →+ V) (hφ : Function.Surjective φ)
    (hequiv : ∀ (s : SpecialLinearGroup k V) (x : E), φ (ρ s x) = s (φ x))
    (hker : ∀ (s : SpecialLinearGroup k V) (x : E), φ x = 0 → ρ s x = x) (e : E) :
    (∃ A : Subgroup (SpecialLinearGroup k V), (∀ a ∈ A, ρ a e = e) ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = Nat.card k ^ (n - 1)) ∧
    (4 ≤ Nat.card k ^ (n - 1) → ∃ A : Subgroup (SpecialLinearGroup k V), (∀ a ∈ A, ρ a e = e) ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 4) := by
  have hfin : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  have h2V : ∀ v : V, 2 • v = 0 := fun v => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  obtain ⟨c, hc, hcv⟩ : ∃ c : V, c ≠ 0 ∧ (φ e ≠ 0 → c = φ e) := by
    by_cases hv : φ e = 0
    · have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
      obtain ⟨c, hc⟩ := exists_ne (0 : V)
      exact ⟨c, hc, fun h => absurd hv h⟩
    · exact ⟨φ e, hv, fun _ => rfl⟩
  have hsq : ∀ x : Multiplicative (Ann k c), x * x = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    apply Subtype.ext
    change ((Multiplicative.toAdd x : Ann k c) : Dual k V) +
      ((Multiplicative.toAdd x : Ann k c) : Dual k V) = 0
    rw [← two_smul k, show (2 : k) = 0 from CharTwo.two_eq_zero, zero_smul]
  set A := MonoidHom.range (G := Multiplicative (Ann k c)) (transvHom (k := k) c) with hA
  have hEA : IsElementaryAbelian 2 A :=
    EvenSp.isElementaryAbelian_range (G := Multiplicative (Ann k c)) _
      (fun x y => mul_comm x y) fun x => by
      rw [sq, hsq]
  have hcard : Nat.card A = Nat.card k ^ (n - 1) := by
    rw [hA, ← Nat.card_congr (MonoidHom.ofInjective (G := Multiplicative (Ann k c))
      (transvHom_injective (k := k) hc)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, card_ann hc, hV]
  have hfix : ∀ a ∈ A, ρ a e = e := by
    rintro _ ⟨f, rfl⟩
    by_cases hv : φ e = 0
    · exact hker _ e hv
    by_cases hf0 : f = 1
    · rw [hf0, map_one, map_one]
      rfl
    have hcv' := hcv hv
    set t := transvHom (k := k) c f with ht
    have ht2 : t * t = 1 := by rw [ht, ← map_mul, hsq, map_one]
    let : Module (ZMod 2) V := AddCommGroup.zmodModule h2V
    let bE : Module.End (ZMod 2) E := (ρ t).toLinearMap
    let bV : Module.End (ZMod 2) V :=
      AddMonoidHom.toZModLinearMap 2 (t : V ≃ₗ[k] V).toLinearMap.toAddMonoidHom
    let φ' : E →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 φ
    have hE : bE * bE = 1 := LinearMap.ext fun x => by
      have h : (ρ t * ρ t) x = x := by rw [← map_mul, ht2, map_one]; rfl
      exact h
    have hVsq : bV * bV = 1 := LinearMap.ext fun x => by
      have h : (t * t) x = x := by rw [ht2]; rfl
      exact h
    have hcomm : φ' ∘ₗ bE = bV ∘ₗ φ' := LinearMap.ext fun x => hequiv t x
    have hker' : ∀ x ∈ LinearMap.ker φ', bE x = x := fun x hx => hker t x hx
    have hfne : ((Multiplicative.toAdd f : Ann k c) : Dual k V) ≠ 0 := by
      intro h0
      apply hf0
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h0
    obtain ⟨y, hy⟩ : ∃ y : V, ((Multiplicative.toAdd f : Ann k c) : Dual k V) y ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hfne (LinearMap.ext hall)
    refine CFSG.QuasithinUnique.Setup.Campbell.involution_image_fixed_lift bE bV hE hVsq φ' hφ
      hcomm hker' e ⟨(((Multiplicative.toAdd f : Ann k c) : Dual k V) y)⁻¹ • y, ?_⟩
    change t ((((Multiplicative.toAdd f : Ann k c) : Dual k V) y)⁻¹ • y) -
      (((Multiplicative.toAdd f : Ann k c) : Dual k V) y)⁻¹ • y = φ e
    rw [ht, transvHom_apply, map_smul, smul_eq_mul, inv_mul_cancel₀ hy, one_smul,
      add_sub_cancel_left, hcv']
  refine ⟨⟨A, hfix, hEA, hcard⟩, fun h4 => ?_⟩
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨m, -, hm⟩ := FiniteField.card k 2
  have hqm : Nat.card k ^ (n - 1) = 2 ^ ((m : ℕ) * (n - 1)) := by
    rw [Nat.card_eq_fintype_card, hm, ← pow_mul]
  have h4dvd : 2 ^ 2 ∣ Nat.card A := by
    rw [hcard, hqm]
    apply pow_dvd_pow
    by_contra hlt
    have : 2 ^ ((m : ℕ) * (n - 1)) ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos (by omega)
    rw [← hqm] at this
    omega
  have : Finite (SpecialLinearGroup k V) := by
    have : Finite V := Module.finite_of_finite k
    have : Finite (V ≃ₗ[k] V) := Finite.of_injective (fun u : V ≃ₗ[k] V => (u : V → V))
      fun u w h => LinearEquiv.ext (congrFun h)
    exact Subtype.finite
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4dvd
  refine ⟨H.map A.subtype, fun a ha => ?_, ?_, ?_⟩
  · obtain ⟨b, -, rfl⟩ := ha
    exact hfix _ b.2
  · refine { is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨⟨a, ha⟩, -, hax⟩ := x.2
      obtain ⟨⟨b, hb⟩, -, hby⟩ := y.2
      apply Subtype.ext
      change (x : SpecialLinearGroup k V) * y = y * x
      rw [← hax, ← hby]
      exact congrArg Subtype.val (hEA.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨⟨a, ha⟩, -, hax⟩ := x.2
      apply Subtype.ext
      change (x : SpecialLinearGroup k V) ^ 2 = 1
      rw [← hax]
      exact elemPow_eq_one_of_isElementaryAbelian (A := A) a ha
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hH]
    norm_num

end CFSG.LieType

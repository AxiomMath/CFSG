module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResC

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open Matrix

section Lift

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_sylow_two_lift (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {T : Subgroup (primeFormP h (idGram K n))} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    {Â : Subgroup (primeFormUnitary h (idGram K n))}
    (hÂT : ∀ X ∈ Â, T.map (primeFormConjHom h (idGram K n) X).toMonoidHom = T) :
    ∃ T₂ : Subgroup (GL (Fin n) K), IsPGroup 2 T₂ ∧ T₂ ≠ ⊥ ∧
      T₂ ≤ primeFormUnitary h (idGram K n) ∧
      ∀ X ∈ Â, ∀ t ∈ T₂, (X : GL (Fin n) K) * t * (X : GL (Fin n) K)⁻¹ ∈ T₂ := by
  classical
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := normOneScalars h (gramSU h (idGram K n)) n
  let Tc : Subgroup (gramSU h (idGram K n)) := T.comap (QuotientGroup.mk' N)
  let Tl : Subgroup (GL (Fin n) K) := Tc.map (gramSU h (idGram K n)).subtype
  have hconj : ∀ X ∈ Â, ∀ t ∈ Tl, (X : GL (Fin n) K) * t * (X : GL (Fin n) K)⁻¹ ∈ Tl := by
    rintro X hX _ ⟨g, hg, rfl⟩
    refine ⟨⟨(X : GL (Fin n) K) * g * (X : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (idGram K n) X.2 g.2⟩, ?_, rfl⟩
    have hm := Subgroup.mem_map_of_mem (primeFormConjHom h (idGram K n) X).toMonoidHom
      (show (g : primeFormP h (idGram K n)) ∈ T from hg)
    rw [hÂT X hX] at hm
    show ((⟨(X : GL (Fin n) K) * g * (X : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (idGram K n) X.2 g.2⟩ : gramSU h (idGram K n)) :
        primeFormP h (idGram K n)) ∈ T
    rw [← primeFormConjHom_mk h (idGram K n) X g]
    exact hm
  haveI : Group.IsNilpotent T := hT2.isNilpotent
  let ψ : Tc →* T :=
    MonoidHom.codRestrict ((QuotientGroup.mk' N).comp Tc.subtype) T (fun x => x.2)
  have hψ : ψ.ker ≤ Subgroup.center Tc := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (QuotientGroup.mk' N) (x : gramSU h (idGram K n)) = 1 := congrArg Subtype.val hx
    have hxN : (x : gramSU h (idGram K n)) ∈ N := (QuotientGroup.eq_one_iff _).mp hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (normOneScalars_le_center h (gramSU h (idGram K n)) n hxN) y
  have hψs : Function.Surjective ψ := by
    rintro ⟨t, ht⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N t
    exact ⟨⟨g, ht⟩, rfl⟩
  haveI : Group.IsNilpotent Tc := Subgroup.isNilpotent_of_ker_le_center ψ hψ
  let e : Tc ≃* Tl := Tc.equivMapOfInjective (gramSU h (idGram K n)).subtype Subtype.val_injective
  haveI : Group.IsNilpotent Tl := Group.nilpotent_of_mulEquiv e
  have h2T : 2 ∣ Nat.card T := by
    rcases hT2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq T h1) hT
    · exact h2
  have h2Tl : 2 ∣ Nat.card Tl := by
    rw [← Nat.card_congr e.toEquiv]
    exact h2T.trans (Subgroup.card_dvd_of_surjective hψs)
  obtain ⟨P⟩ : Nonempty (Sylow 2 Tl) := inferInstance
  have hPc : (P : Subgroup Tl).Characteristic := Sylow.characteristic_of_normal P inferInstance
  let φ : ∀ X ∈ Â, Tl ≃* Tl := fun X hX => MulEquiv.ofBijective
    (((MulAut.conj (X : GL (Fin n) K)).toMonoidHom.comp Tl.subtype).codRestrict Tl
      (fun t => hconj X hX t t.2))
    (Finite.injective_iff_bijective.mp (fun a b hab =>
      Subtype.ext ((MulAut.conj (X : GL (Fin n) K)).injective (congrArg Subtype.val hab))))
  refine ⟨(P : Subgroup Tl).map Tl.subtype, P.isPGroup'.map _, ?_, ?_, ?_⟩
  · intro hbot
    exact P.ne_bot_of_dvd_card h2Tl
      ((Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hbot)
  · rintro _ ⟨x, -, rfl⟩
    exact ((mem_gramSU_iff_unitary h).mp (Subgroup.map_subtype_le Tc x.2)).1
  · rintro X hX _ ⟨x, hx, rfl⟩
    have hmem : φ X hX x ∈ (P : Subgroup Tl) := by
      rw [← Subgroup.characteristic_iff_map_eq.mp hPc (φ X hX)]
      exact Subgroup.mem_map_of_mem _ hx
    exact ⟨φ X hX x, hmem, rfl⟩

theorem exists_isotropic_stable [CharP K 2] (h : UnitaryFieldData ℓ f K) {n : ℕ}
    {T : Subgroup (GL (Fin n) K)} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hTU : T ≤ primeFormUnitary h (idGram K n))
    {Â : Subgroup (GL (Fin n) K)} (hÂU : Â ≤ primeFormUnitary h (idGram K n))
    (hN : ∀ X ∈ Â, ∀ t ∈ T, X * t * X⁻¹ ∈ T) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ W ≤ W.orthogonalBilin (idForm h n) ∧
      ∀ X ∈ Â, ∀ w ∈ W, (X : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  classical
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set Fx : Set (Fin n → K) :=
    {w | ∀ t ∈ T, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w} with hFx
  set Wp : Submodule K (Fin n → K) := ⨅ (w : Fin n → K) (_ : w ∈ Fx), LinearMap.ker (idForm h n w)
    with hWp
  have hmemWp : ∀ v, v ∈ Wp ↔ ∀ w ∈ Fx, idForm h n w v = 0 := by
    intro v
    simp only [hWp, Submodule.mem_iInf, LinearMap.mem_ker]
  have hTWp : ∀ t ∈ T, ∀ v ∈ Wp, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Wp := by
    intro t ht v hv
    rw [hmemWp] at hv ⊢
    intro w hw
    have e := idForm_mulVec_of_mem_primeFormUnitary (hTU ht) w v
    rw [show ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w from hw t ht] at e
    rw [e]
    exact hv w hw
  obtain ⟨v₀, hv₀0, hv₀F, hv₀W⟩ : ∃ v : Fin n → K, v ≠ 0 ∧ v ∈ Fx ∧ v ∈ Wp := by
    by_contra hcon
    push Not at hcon
    letI act : MulAction T Wp :=
      { smul := fun t v => ⟨((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (v : Fin n → K),
          hTWp t t.2 v v.2⟩
        one_smul := fun v => Subtype.ext (show (((1 : T) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ (v : Fin n → K) = v by
          rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec])
        mul_smul := fun s t v => Subtype.ext (show (((s * t : T) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ (v : Fin n → K) = ((s : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ (((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (v : Fin n → K)) by
          rw [Matrix.mulVec_mulVec, Subgroup.coe_mul, Units.val_mul]) }
    have hWp0 : ∀ v ∈ Wp, v = 0 := by
      intro v hv
      by_contra hv0
      have hmod := hT2.card_modEq_card_fixedPoints Wp
      have h2W : 2 ∣ Nat.card Wp := by
        have hx : (⟨v, hv⟩ : Wp) ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
        have h2x : 2 • (⟨v, hv⟩ : Wp) = 0 := by
          rw [two_nsmul, ← two_smul K, h2, zero_smul]
        rw [← addOrderOf_eq_prime h2x hx]
        exact addOrderOf_dvd_natCard _
      have hfix1 : Nat.card (MulAction.fixedPoints T Wp) = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, fun t => Subtype.ext (show (((t : T) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K) = 0 from Matrix.mulVec_zero _)⟩,
          fun y => ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        by_contra hy0
        have hyF : ((y : Wp) : Fin n → K) ∈ Fx := fun t ht =>
          congrArg Subtype.val (y.2 ⟨t, ht⟩)
        exact hcon _ hy0 hyF (y : Wp).2
      rw [hfix1] at hmod
      unfold Nat.ModEq at hmod
      omega
    apply hT
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    apply Units.ext
    rw [Units.val_one]
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [Matrix.one_mulVec]
    have hmem : ((t : Matrix (Fin n) (Fin n) K) *ᵥ v - v) ∈ Wp := by
      rw [hmemWp]
      intro w hw
      rw [map_sub]
      have e := idForm_mulVec_of_mem_primeFormUnitary (hTU ht) w v
      rw [show (t : Matrix (Fin n) (Fin n) K) *ᵥ w = w from hw t ht] at e
      rw [e, sub_self]
    exact sub_eq_zero.1 (hWp0 _ hmem)
  have hFxadd : ∀ v w, v ∈ Fx → w ∈ Fx → v + w ∈ Fx := fun v w hv hw t ht => by
    rw [Matrix.mulVec_add, hv t ht, hw t ht]
  have hFxsmul : ∀ (c : K) v, v ∈ Fx → c • v ∈ Fx := fun c v hv t ht => by
    rw [Matrix.mulVec_smul, hv t ht]
  have hFxD : ∀ {D : GL (Fin n) K}, (∀ t ∈ T, D⁻¹ * t * D ∈ T) →
      ∀ v ∈ Fx, (D : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Fx := by
    intro D hN' v hv t ht
    have e : (t : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) =
        (D : Matrix (Fin n) (Fin n) K) * ((D⁻¹ * t * D : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec,
      show ((D⁻¹ * t * D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v from
        hv _ (hN' t ht)]
  have hWpD : ∀ {D : GL (Fin n) K}, D ∈ primeFormUnitary h (idGram K n) →
      (∀ t ∈ T, D * t * D⁻¹ ∈ T) → ∀ v ∈ Wp, (D : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Wp := by
    intro D hDU hN v hv
    rw [hmemWp] at hv ⊢
    intro w hw
    have hw' : ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ Fx :=
      hFxD (D := D⁻¹) (fun t ht => by rw [inv_inv]; exact hN t ht) w hw
    have e1 : (D : Matrix (Fin n) (Fin n) K) *ᵥ (((D⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have e := idForm_mulVec_of_mem_primeFormUnitary hDU
      (((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) v
    rw [e1] at e
    rw [e]
    exact hv _ hw'
  let FxS : Submodule K (Fin n → K) :=
    { carrier := Fx
      add_mem' := fun {v w} hv hw => hFxadd v w hv hw
      zero_mem' := fun t _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv => hFxsmul c v hv }
  refine ⟨FxS ⊓ Wp, ?_, ?_, ?_⟩
  · intro hbot
    exact hv₀0 ((Submodule.eq_bot_iff _).mp hbot v₀ ⟨hv₀F, hv₀W⟩)
  · intro m hm
    rw [Submodule.mem_orthogonalBilin_iff]
    intro x hx
    exact (hmemWp m).1 hm.2 x hx.1
  · intro X hX w hw
    refine ⟨hFxD (D := X) (fun t ht => ?_) w hw.1, hWpD (hÂU hX) (hN X hX) w hw.2⟩
    simpa using hN X⁻¹ (inv_mem hX) t ht

end Lift

section EigenSixAux

variable {K : Type} [Field K]

private noncomputable def u6eRes (A : Subgroup (GL (Fin 6) K)) (W : Submodule K (Fin 6 → K))
    (hW : ∀ X ∈ A, ∀ w ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) :
    A →* Module.End K W where
  toFun X := LinearMap.restrict (Matrix.mulVecLin (X.1 : Matrix (Fin 6) (Fin 6) K))
    (fun w hw => hW X.1 X.2 w hw)
  map_one' := by
    ext w
    simp
  map_mul' X Y := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact (Matrix.mulVec_mulVec (w : Fin 6 → K) (X.1 : Matrix (Fin 6) (Fin 6) K)
      (Y.1 : Matrix (Fin 6) (Fin 6) K)).symm

private theorem u6e_exists_eigen {V : Type*} [AddCommGroup V] [Module K V] {G : Type*} [Group G]
    (hG : IsPGroup 3 G) (ρ : G →* LinearMap.GeneralLinearGroup K V)
    (hnd : ¬ 3 ∣ Nat.card (Projectivization K V)) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ∃ a : K, (ρ g : V →ₗ[K] V) v = a • v := by
  letI : MulAction G (Projectivization K V) := MulAction.compHom _ ρ
  obtain ⟨x, hx⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card (Projectivization K V) hnd
  refine ⟨x.rep, x.rep_nonzero, fun g => ?_⟩
  have hgx : ρ g • x = x := MulAction.mem_fixedPoints.mp hx g
  rw [← Projectivization.mk_rep x] at hgx
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hgx
  obtain ⟨a, ha⟩ := hgx
  exact ⟨a, ha.symm⟩

private theorem u6e_eigen_of_card (A : Subgroup (GL (Fin 6) K)) (hA3 : IsPGroup 3 A)
    (W : Submodule K (Fin 6 → K))
    (hWA : ∀ X ∈ A, ∀ w ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (hnd : ¬ 3 ∣ Nat.card (Projectivization K W)) :
    ∃ w : Fin 6 → K, w ≠ 0 ∧ w ∈ W ∧
      ∀ X ∈ A, ∃ μ : K, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w := by
  obtain ⟨v, hv0, hv⟩ := u6e_exists_eigen hA3 (u6eRes A W hWA).toHomUnits hnd
  refine ⟨(v : Fin 6 → K), fun h0 => hv0 (Subtype.ext h0), v.2, fun X hX => ?_⟩
  obtain ⟨a, ha⟩ := hv ⟨X, hX⟩
  exact ⟨a, congrArg Subtype.val ha⟩

private theorem u6e_finrank_le_three (h : UnitaryFieldData 2 1 K) {W : Submodule K (Fin 6 → K)}
    (hiso : W ≤ W.orthogonalBilin (idForm h 6)) : Module.finrank K W ≤ 3 := by
  have hσ : Function.Surjective h.bar := fun c => ⟨h.bar c, UnitaryFieldData.bar_bar h c⟩
  have h1 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hσ
    (idForm_separatingLeft h 6) W
  have h2 := Submodule.finrank_mono hiso
  rw [Module.finrank_fin_fun] at h1
  omega

private theorem u6e_orth_le (h : UnitaryFieldData 2 1 K) {W : Submodule K (Fin 6 → K)}
    (hiso : W ≤ W.orthogonalBilin (idForm h 6)) (hd : Module.finrank K W = 3) :
    W.orthogonalBilin (idForm h 6) ≤ W := by
  have hσ : Function.Surjective h.bar := fun c => ⟨h.bar c, UnitaryFieldData.bar_bar h c⟩
  have h1 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hσ
    (idForm_separatingLeft h 6) W
  rw [Module.finrank_fin_fun] at h1
  have heq : W = W.orthogonalBilin (idForm h 6) :=
    Submodule.eq_of_le_of_finrank_eq hiso (by omega)
  exact heq.symm.le

private theorem u6e_fix_sq [CharP K 2] (h : UnitaryFieldData 2 1 K) {X : GL (Fin 6) K}
    (hX : X ∈ primeFormUnitary h (idGram K 6)) {W : Submodule K (Fin 6 → K)}
    (hWW : W.orthogonalBilin (idForm h 6) ≤ W)
    (hfix : ∀ u ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ u = u) :
    (X : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have hy : ((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v - v) ∈ W.orthogonalBilin (idForm h 6) := by
    intro u hu
    have e := idForm_mulVec_of_mem_primeFormUnitary hX u v
    rw [hfix u hu] at e
    rw [map_sub, e, sub_self]
  have h3 := hfix _ (hWW hy)
  rw [Matrix.mulVec_sub] at h3
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.sub_apply] at h4
  linear_combination h4 + (((X : Matrix (Fin 6) (Fin 6) K) *ᵥ v) i - v i) * h2

private theorem u6e_res_inj [CharP K 2] (h : UnitaryFieldData 2 1 K) {A : Subgroup (GL (Fin 6) K)}
    (hA3 : IsPGroup 3 A) (hAU : A ≤ primeFormUnitary h (idGram K 6))
    {W : Submodule K (Fin 6 → K)} (hWW : W.orthogonalBilin (idForm h 6) ≤ W)
    (hWA : ∀ X ∈ A, ∀ w ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) :
    Function.Injective (u6eRes A W hWA) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hfix : ∀ u ∈ W, (X.1 : Matrix (Fin 6) (Fin 6) K) *ᵥ u = u := by
    intro u hu
    exact congrArg Subtype.val (LinearMap.congr_fun hX ⟨u, hu⟩)
  have hsq := u6e_fix_sq h (hAU X.2) hWW hfix
  have hX2 : X ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two, Subgroup.coe_one, Units.val_one]
    exact hsq
  obtain ⟨k, hk⟩ := hA3 X
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  rw [hm, pow_succ, pow_mul, hX2, one_pow, one_mul] at hk
  exact hk

private theorem u6e_card_dvd [CharP K 2] [Finite K] (h : UnitaryFieldData 2 1 K)
    {A : Subgroup (GL (Fin 6) K)}
    (hA3 : IsPGroup 3 A) (hAU : A ≤ primeFormUnitary h (idGram K 6))
    {W : Submodule K (Fin 6 → K)} (hWW : W.orthogonalBilin (idForm h 6) ≤ W)
    (hWA : ∀ X ∈ A, ∀ w ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (hd : Module.finrank K W = 3) : Nat.card A ∣ 181440 := by
  have hinj := u6e_res_inj h hA3 hAU hWW hWA
  have hinj' : Function.Injective (u6eRes A W hWA).toHomUnits := by
    intro X Y hXY
    exact hinj (congrArg Units.val hXY)
  have h1 := Subgroup.card_dvd_of_injective _ hinj'
  let b := Module.finBasisOfFinrankEq K W hd
  let e : (Module.End K W)ˣ ≃* GL (Fin 3) K :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have h2 : Nat.card (Module.End K W)ˣ = Nat.card (GL (Fin 3) K) := Nat.card_congr e.toEquiv
  letI : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card]
    norm_num
  have h3 : Nat.card (GL (Fin 3) K) = 181440 := by
    rw [Matrix.card_GL_field, hq, Fin.prod_univ_three]
    norm_num
  rw [h2, h3] at h1
  exact h1

end EigenSixAux

section EigenSix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_common_eigenvector_six (h : UnitaryFieldData 2 1 K)
    {Â : Subgroup (GL (Fin 6) K)} (hÂ3 : IsPGroup 3 Â)
    (hÂU : Â ≤ primeFormUnitary h (idGram K 6)) (hcard : 81 < Nat.card Â)
    {W : Submodule K (Fin 6 → K)} (hW : W ≠ ⊥) (hiso : W ≤ W.orthogonalBilin (idForm h 6))
    (hWÂ : ∀ X ∈ Â, ∀ w ∈ W, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W) :
    ∃ w : Fin 6 → K, w ≠ 0 ∧ w ∈ W ∧
      ∀ X ∈ Â, ∃ μ : K, (X : Matrix (Fin 6) (Fin 6) K) *ᵥ w = μ • w := by
  have hd3 := u6e_finrank_le_three h hiso
  have hd1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW
  have hK : Nat.card K = 4 := by
    rw [h.card]
    norm_num
  by_cases h3 : Module.finrank K W = 3
  · exfalso
    have hdvd := u6e_card_dvd h hÂ3 hÂU (u6e_orth_le h hiso h3) hWÂ h3
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hÂ3
    rw [hn] at hdvd hcard
    have hn5 : 5 ≤ n := by
      by_contra hlt
      have : 3 ^ n ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    have : 3 ^ 5 ∣ 181440 := (pow_dvd_pow 3 hn5).trans hdvd
    norm_num at this
  · refine u6e_eigen_of_card Â hÂ3 W hWÂ ?_
    have hd : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
    rcases hd with hd | hd <;>
      · rw [Projectivization.card_of_finrank K W hd, hK]
        norm_num [Finset.sum_range_succ]

end EigenSix

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

end

module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.FixDim
public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.BinRep

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section FixCard

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Lg : Subgroup (Module.End (ZMod 2) V)ˣ} [Fact (repOfSubgroup Lg).IsIrreducible] {m : ℕ}
  {k : Type} [Field k] {S : Type} [Group S] [Finite S]

theorem card_fix_D (b : Module.Basis (Fin m) (EndRing (repOfSubgroup Lg)) V)
    (ιD : EndRing (repOfSubgroup Lg) →+* k) (hιD : Function.Injective ιD) (φS : S ≃* ↥Lg)
    (A' : Subgroup S) :
    Nat.card {v : V // ∀ s ∈ A', ((φS s : ↥Lg) : (Module.End (ZMod 2) V)ˣ).val v = v} =
      Nat.card (EndRing (repOfSubgroup Lg)) ^ Module.finrank k
        (CFSG.Quasithin.SmithCurtis.fixSub ((matRepE b ιD).comp φS.toMonoidHom) A') := by
  classical
  set D := EndRing (repOfSubgroup Lg) with hD
  let FD : Submodule D V :=
    { carrier := {v | ∀ s ∈ A', repD (repOfSubgroup Lg) (φS s) v = v}
      add_mem' := fun {a c} ha hc s hs => by rw [map_add, ha s hs, hc s hs]
      zero_mem' := fun s _ => map_zero _
      smul_mem' := fun d v hv s hs => by rw [map_smul, hv s hs] }
  have h1 : Nat.card {v : V // ∀ s ∈ A', ((φS s : ↥Lg) : (Module.End (ZMod 2) V)ˣ).val v = v} =
      Nat.card FD := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    simp only [FD, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
      repD_apply, repOfSubgroup_apply]
  have : Module.Finite D V := Module.Finite.of_finite
  rw [h1, Module.natCard_eq_pow_finrank (K := D)]
  congr 1
  let T : A' → Matrix (Fin m) (Fin m) D := fun s => matRep b (φS s.1)
  letI : Algebra D k := ιD.toAlgebra
  have : FaithfulSMul D k := ⟨fun {r₁ r₂} h => by
    have h1 := h 1
    simp only [Algebra.smul_def, mul_one] at h1
    exact hιD h1⟩
  have h2 : FD.map b.equivFun.toLinearMap = fixF T := by
    ext c
    rw [mem_fixF]
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩ s
      have := LinearMap.toMatrix_mulVec_repr b b (repD (repOfSubgroup Lg) (φS s.1)) v
      rw [hv s.1 s.2] at this
      simpa [T, matRep] using this
    · intro h
      refine ⟨b.equivFun.symm c, fun s hs => ?_, LinearEquiv.apply_symm_apply _ _⟩
      have hv : (⇑(b.repr (b.equivFun.symm c)) : Fin m → D) = c := by
        have := LinearEquiv.apply_symm_apply b.equivFun c
        rw [Module.Basis.equivFun_apply] at this
        exact this
      have h4 := LinearMap.toMatrix_mulVec_repr b b (repD (repOfSubgroup Lg) (φS s)) (b.equivFun.symm c)
      have h3 := h ⟨s, hs⟩
      simp only [T, matRep, MonoidHom.coe_mk, OneHom.coe_mk] at h3
      rw [hv, h3] at h4
      exact b.repr.injective (Finsupp.ext fun i => (congrFun h4 i).symm.trans (congrFun hv i).symm)
  have h3 : CFSG.Quasithin.SmithCurtis.fixSub ((matRepE b ιD).comp φS.toMonoidHom) A' =
      fixK (k := k) T := by
    ext w
    rw [CFSG.Quasithin.SmithCurtis.mem_fixSub, mem_fixK]
    constructor
    · intro h s
      have := h s.1 s.2
      rw [MonoidHom.comp_apply, matRepE_apply] at this
      exact this
    · intro h s hs
      rw [MonoidHom.comp_apply, matRepE_apply]
      exact h ⟨s, hs⟩
  rw [← LinearEquiv.finrank_map_eq b.equivFun FD, h2, h3, finrank_fixK]

end FixCard

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem offender_periodic_data_fix
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥)
    (hel : IsElemAbelian2 E) (hquad : IsQuadratic E)
    (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E))
    {S : Type} [Group S] [Nontrivial S] (ι : S ≃* ↥L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (ιK : K →+* k)
      (ρ : Representation k S (Fin m → k)),
      1 ≤ δ ∧ 1 ≤ m ∧ ρ.IsIrreducible ∧ Function.Injective ρ ∧ Function.Injective ιK ∧
      Nat.card W = 2 ^ (δ * m) ∧
      (∀ s i j, (ρ s (Pi.single j 1)) i ^ (2 ^ δ) = ρ s (Pi.single j 1) i) ∧
      (∀ (a : MulAut W) (ha : a ∈ E), ∃ B : Module.End k (Fin m → k), IsUnit B ∧ ∀ s : S,
        B * ρ s = ρ (ι.symm (X1.conjAut L (hEN ha) (ι s))) * B) ∧
      (∀ A' : Subgroup S, Nat.card ↥(fixV ((A'.map ι.toMonoidHom).map L.subtype)) =
        2 ^ (δ * Module.finrank k (CFSG.Quasithin.SmithCurtis.fixSub ρ A'))) := by
  classical
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWnt : Nontrivial W := hirr.1
  have hVnt : Nontrivial V := by
    obtain ⟨x, hx⟩ := exists_ne (1 : W)
    exact ⟨⟨Multiplicative.toAdd (θ x), 0, fun h => hx (θ.injective (by simpa using h))⟩⟩
  have hVfin : Finite V := Finite.of_equiv W (θ.toEquiv.trans Multiplicative.toAdd)
  set Ψ : MulAut W ≃* (Module.End (ZMod 2) V)ˣ := binUnits θ with hΨ
  set L' : Subgroup (Module.End (ZMod 2) V)ˣ := L.map Ψ.toMonoidHom with hL'
  set A : Subgroup (Module.End (ZMod 2) V)ˣ := E.map Ψ.toMonoidHom with hA
  let eL : ↥L ≃* ↥L' := Subgroup.equivMapOfInjective L Ψ.toMonoidHom Ψ.injective
  let φS : S ≃* ↥L' := ι.trans eL
  have hφS : ∀ s, ((φS s : ↥L') : (Module.End (ZMod 2) V)ˣ) = Ψ ((ι s : ↥L) : MulAut W) := fun s => rfl
  have hLperf : Group.IsPerfect ↥L' := CurtisExc.isPerfect_of_mulEquiv eL hperf
  have hLnt : L' ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    have h1 : ((φS s : ↥L') : (Module.End (ZMod 2) V)ˣ) = 1 := by
      have h2 : ((φS s : ↥L') : (Module.End (ZMod 2) V)ˣ) ∈ (⊥ : Subgroup (Module.End (ZMod 2) V)ˣ) := by
        rw [← h]; exact (φS s).2
      exact h2
    exact hs (φS.injective (Subtype.ext (by simpa using h1)))
  have hirrL : (repOfSubgroup L').IsIrreducible := by
    rw [isIrreducible_iff]
    refine ⟨hVnt, fun U hU => ?_⟩
    set c : V → W := fun v => θ.symm (Multiplicative.ofAdd v) with hc
    set U₀ : Subgroup W :=
      { carrier := {x | Multiplicative.toAdd (θ x) ∈ U}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have : Multiplicative.toAdd (θ (x * y)) =
              Multiplicative.toAdd (θ x) + Multiplicative.toAdd (θ y) := by simp
          show Multiplicative.toAdd (θ (x * y)) ∈ U
          rw [this]; exact U.add_mem hx hy
        inv_mem' := fun {x} hx => by
          have : Multiplicative.toAdd (θ x⁻¹) = - Multiplicative.toAdd (θ x) := by simp
          show Multiplicative.toAdd (θ x⁻¹) ∈ U
          rw [this]; exact U.neg_mem hx } with hU₀
    have hU₀inv : ∀ g ∈ L, ∀ u ∈ U₀, g u ∈ U₀ := by
      intro g hg u hu
      have h1 := hU ⟨Ψ g, g, hg, rfl⟩ (Multiplicative.toAdd (θ u)) hu
      show Multiplicative.toAdd (θ (g u)) ∈ U
      have e : (Ψ g).val (Multiplicative.toAdd (θ u)) = Multiplicative.toAdd (θ (g u)) := by
        rw [binUnits_val]; simp
      rw [repOfSubgroup_apply] at h1
      rwa [show ((⟨Ψ g, g, hg, rfl⟩ : ↥L') : (Module.End (ZMod 2) V)ˣ).val
          (Multiplicative.toAdd (θ u)) = _ from e] at h1
    rcases hirr.2 U₀ hU₀inv with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
        show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U
        simpa using hw
      rw [h0, Subgroup.mem_bot] at hx
      rw [Submodule.mem_bot]
      have := congrArg (fun x => Multiplicative.toAdd (θ x)) hx
      simpa using this
    · right
      rw [eq_top_iff]
      intro w _
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact Subgroup.mem_top _
      have hx' : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U := hx
      simpa using hx'
  have : Fact (repOfSubgroup L').IsIrreducible := ⟨hirrL⟩
  have hAnorm : ∀ a ∈ A, ∀ g ∈ L', a * g * a⁻¹ ∈ L' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨e * l * e⁻¹, ((Subgroup.mem_normalizer_iff.mp (hEN he)) l).mp hl, ?_⟩
    simp
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have : e * e = 1 := by rw [← pow_two]; exact hel.2 e he
    show Ψ e * Ψ e = 1
    rw [← map_mul, this, map_one]
  have hAnt : A ≠ ⊥ := by
    intro h
    apply hE
    rw [eq_bot_iff]
    intro e he
    have : Ψ e ∈ A := ⟨e, he, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Ψ.injective (this.trans (map_one Ψ).symm)
  have hquadA : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ w
    exact B42L2.quad_map θ hquad (Layer.binPsi θ e) ⟨e, he, rfl⟩ (Layer.binPsi θ f) ⟨f, hf, rfl⟩ w
  have hoffA : Nat.card V ≤ Nat.card A * Nat.card {w : V // ∀ a ∈ A, a.val w = w} := by
    have h1 : Nat.card ↥A = Nat.card ↥E :=
      Subgroup.card_map_of_injective Ψ.injective
    have h2 : Nat.card {w : V // ∀ a ∈ A, a.val w = w} = Nat.card ↥(fixV E) := by
      rw [← B42SL3.card_fix_map θ E]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · rintro h _ ⟨e, he, rfl⟩
        exact h _ ⟨e, he, rfl⟩
      · rintro h _ ⟨e, he, rfl⟩
        exact h _ ⟨e, he, rfl⟩
    rw [h1, h2, ← Layer.Actor.natCard_eq θ]
    exact hoff
  obtain ⟨hlin, -, -, -, hinjL, -, -, -, -⟩ :=
    quadratic_offender_endomorphism_field_linearization (k := ZMod 2) L' A hLperf hLnt hAnorm hA2
      hAnt hquadA hoffA
  have hDfin : Finite (EndRing (repOfSubgroup L')) := finite_endRing _
  have hDchar : CharP (EndRing (repOfSubgroup L')) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing (repOfSubgroup L'))).injective 2
  have : Fintype (EndRing (repOfSubgroup L')) := Fintype.ofFinite _
  obtain ⟨δp, -, hδp⟩ := FiniteField.card (EndRing (repOfSubgroup L')) 2
  set δ : ℕ := (δp : ℕ) with hδdef
  have hDcard : Nat.card (EndRing (repOfSubgroup L')) = 2 ^ δ := by
    rw [Nat.card_eq_fintype_card, hδp]
  have hδ : 1 ≤ δ := δp.pos
  have : Module.Finite (EndRing (repOfSubgroup L')) V := Module.Finite.of_finite
  set m : ℕ := Module.finrank (EndRing (repOfSubgroup L')) V with hm
  let b : Module.Basis (Fin m) (EndRing (repOfSubgroup L')) V := Module.finBasis _ V
  have hm1 : 1 ≤ m := Module.finrank_pos
  have hVcard : Nat.card V = 2 ^ (δ * m) := by
    rw [natCard_eq_pow_finrank (ρ := repOfSubgroup L'), hDcard, pow_mul]
  obtain ⟨-, k, _, _, _, ιK, ιD, -, -, -, -, hKinj, hDinj, -, hDfrob, -⟩ :=
    SL2Modules.finite_fields_common_extension 2 hn hδ hK hDcard
  let ρ : Representation k S (Fin m → k) := (matRepE b ιD).comp φS.toMonoidHom
  have hρirr : ρ.IsIrreducible := by
    have h0 := matRepE_isIrreducible b ιD
    rw [isIrreducible_iff] at h0 ⊢
    refine ⟨h0.1, fun U hU => h0.2 U fun g u hu => ?_⟩
    obtain ⟨s, rfl⟩ := φS.surjective g
    exact hU s u hu
  have hρinj : Function.Injective ρ := by
    intro s s' h
    have h1 : (matRep b (φS s)).map ιD = (matRep b (φS s')).map ιD :=
      Matrix.toLin'.injective h
    have h2 : matRep b (φS s) = matRep b (φS s') :=
      Matrix.ext fun i j => hDinj (congrFun (congrFun h1 i) j)
    have h3 : repD (repOfSubgroup L') (φS s) = repD (repOfSubgroup L') (φS s') :=
      (LinearMap.toMatrix b b).injective h2
    exact φS.injective (hinjL h3)
  have hentry : ∀ (s : S) (i j : Fin m), ρ s (Pi.single j 1) i = ιD (matRep b (φS s) i j) := by
    intro s i j
    show matRepE b ιD (φS s) (Pi.single j 1) i = _
    rw [matRepE_apply]
    simp
  refine ⟨δ, m, k, inferInstance, inferInstance, inferInstance, ιK, ρ, hδ, hm1, hρirr, hρinj,
    hKinj, ?_, ?_, ?_, ?_⟩
  · rw [Layer.Actor.natCard_eq θ, hVcard]
  · intro s i j
    rw [hentry]
    exact hDfrob _
  · intro a ha
    have haA : Ψ a ∈ A := ⟨a, ha, rfl⟩
    have hlinear : ∀ x ∈ A, ∃ f : V →ₗ[EndRing (repOfSubgroup L')] V, ∀ v, f v = x.val v := by
      intro x hx
      refine ⟨{ toFun := x.val, map_add' := map_add _, map_smul' := fun d v => ?_ }, fun v => rfl⟩
      have := congrArg (fun φ : Module.End (ZMod 2) V => φ v) (hlin x hx d)
      exact this
    obtain ⟨f, hf⟩ := hlinear _ haA
    obtain ⟨f', hf'⟩ := hlinear _ (A.inv_mem haA)
    set Mf := LinearMap.toMatrix b b f with hMf
    set Mf' := LinearMap.toMatrix b b f' with hMf'
    have hff' : f * f' = 1 := by
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, hf', hf, ← Module.End.mul_apply, ← Units.val_mul]
      simp
    have hf'f : f' * f = 1 := by
      apply LinearMap.ext
      intro v
      rw [Module.End.mul_apply, hf, hf', ← Module.End.mul_apply, ← Units.val_mul]
      simp
    have hMM' : Mf * Mf' = 1 := by
      rw [hMf, hMf', ← LinearMap.toMatrix_mul, hff', LinearMap.toMatrix_one]
    have hM'M : Mf' * Mf = 1 := by
      rw [hMf, hMf', ← LinearMap.toMatrix_mul, hf'f, LinearMap.toMatrix_one]
    refine ⟨Matrix.toLin' (Mf.map ιD), ?_, fun s => ?_⟩
    · refine ⟨⟨Matrix.toLin' (Mf.map ιD), Matrix.toLin' (Mf'.map ιD), ?_, ?_⟩, rfl⟩
      · rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hMM',
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
        rfl
      · rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hM'M,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
        rfl
    · set s' : S := ι.symm (X1.conjAut L (hEN ha) (ι s)) with hs'
      have hΨ' : Ψ ((ι s' : ↥L) : MulAut W) = Ψ a * Ψ ((ι s : ↥L) : MulAut W) * (Ψ a)⁻¹ := by
        rw [hs', MulEquiv.apply_symm_apply, X1.coe_conjAut]
        simp
      have hrel : f * repD (repOfSubgroup L') (φS s) = repD (repOfSubgroup L') (φS s') * f := by
        apply LinearMap.ext
        intro v
        rw [Module.End.mul_apply, Module.End.mul_apply]
        show f ((φS s : (Module.End (ZMod 2) V)ˣ).val v) = (φS s' : (Module.End (ZMod 2) V)ˣ).val (f v)
        rw [hf, hf, hφS, hφS]
        have key : Ψ a * Ψ ((ι s : ↥L) : MulAut W) = Ψ ((ι s' : ↥L) : MulAut W) * Ψ a := by
          rw [hΨ']; group
        have := congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val v) key
        simpa [Units.val_mul, Module.End.mul_apply] using this
      have hMrel : Mf * matRep b (φS s) = matRep b (φS s') * Mf := by
        have h1 := congrArg (LinearMap.toMatrix b b) hrel
        rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul] at h1
        exact h1
      show Matrix.toLin' (Mf.map ιD) * Matrix.toLin' ((matRep b (φS s)).map ιD) =
        Matrix.toLin' ((matRep b (φS s')).map ιD) * Matrix.toLin' (Mf.map ιD)
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Matrix.map_mul, ← Matrix.map_mul, hMrel]
  · intro A'
    haveI : Finite S := Finite.of_equiv ↥L ι.symm.toEquiv
    have h1 : Nat.card ↥(fixV ((A'.map ι.toMonoidHom).map L.subtype)) =
        Nat.card {v : V // ∀ s ∈ A', ((φS s : ↥L') : (Module.End (ZMod 2) V)ˣ).val v = v} := by
      rw [← B42SL3.card_fix_map θ ((A'.map ι.toMonoidHom).map L.subtype)]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
      constructor
      · intro h s hs
        have := h (Layer.binPsi θ ((ι s : ↥L) : MulAut W))
          ⟨_, ⟨ι s, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
        rw [hφS s, binUnits_val_eq]
        exact this
      · rintro h _ ⟨e, ⟨x, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
        have := h s hs
        rw [hφS s, binUnits_val_eq] at this
        exact this
    rw [h1, card_fix_D b ιD hDinj φS A', hDcard, ← pow_mul]


end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

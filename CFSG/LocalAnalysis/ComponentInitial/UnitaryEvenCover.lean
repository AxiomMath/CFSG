module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverPairing
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverSylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement Pointwise

variable {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 1 K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

variable (h r) in
@[expose] def detKerHom :
    (GeneralLinearGroup.det : GL (Fin r) K →* Kˣ).ker →* detFixed h r :=
  Subgroup.inclusion fun A hA => by
    rw [mem_detFixed]
    have h1 : (A : Matrix (Fin r) (Fin r) K).det = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hA)
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    rw [h1, map_one]

omit [CharP K 2] in
theorem coe_detKerHom (A : (GeneralLinearGroup.det : GL (Fin r) K →* Kˣ).ker) :
    ((detKerHom h r A : detFixed h r) : GL (Fin r) K) = A :=
  rfl

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem exists_radical_complement [Finite E] (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) (hr : 4 ≤ r) :
    ∃ M₀ : Subgroup E, M₀ ≤ preN θ ∧ (∀ y ∈ M₀, θ y = 1 → y = 1) ∧
      (∀ {B : Matrix (Fin r) (Fin r) K}, IsHerm h B → ∃ y ∈ M₀, IsN θ B y) ∧
      ∀ (A : SpecialLinearGroup (Fin r) K) (u : E), θ u = leviHom h r A →
        ∀ y ∈ M₀, u * y * u⁻¹ ∈ M₀ := by
  have hK := card_eq_four h
  have hr1 : 1 ≤ r := by omega
  have hpg : IsPGroup 2 θ.ker := fun c => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, OneMemClass.coe_one]
    exact h2 c c.2)⟩
  set T := preN θ with hT
  let : CommGroup T :=
    { (inferInstance : Group T) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_preN hθ hC hr hpg a.2 b.2) }
  set Γ := (GeneralLinearGroup.det : GL (Fin r) K →* Kˣ).ker with hΓ
  set α : Γ →* MulAut E := (BinarySymplecticSix.liftConj hθ hC).comp
    ((hypProj h r 0).comp ((lHom h r).comp (detKerHom h r))) with hα
  have hliftα : ∀ (A : Γ) (x : E), ∃ g, θ g = hypProj h r 0 (lHom h r (detKerHom h r A)) ∧
      α A x = g * x * g⁻¹ := fun A x => by
    obtain ⟨g, hg⟩ := hθ (hypProj h r 0 (lHom h r (detKerHom h r A)))
    refine ⟨g, hg, ?_⟩
    change BinarySymplecticSix.liftConj hθ hC (hypProj h r 0 (lHom h r (detKerHom h r A))) x = _
    rw [← hg, BinarySymplecticSix.liftConj_apply, MulAut.conj_apply]
  have hαT : ∀ A, ∀ x ∈ T, α A x ∈ T := fun A x hx => by
    obtain ⟨g, hg, he⟩ := hliftα A x
    obtain ⟨B, hB⟩ := mem_preN.mp hx
    rw [he]
    exact (hB.conj _ hg).mem
  set ρ := BinarySymplecticSix.restrictAct α T hαT with hρ
  let : DistribMulAction Γ (Additive T) :=
    { smul := fun A t => Additive.ofMul (ρ A (Additive.toMul t))
      one_smul := fun t => by
        change Additive.ofMul (ρ 1 (Additive.toMul t)) = t
        rw [map_one, MulAut.one_apply]
        rfl
      mul_smul := fun A B t => by
        change Additive.ofMul (ρ (A * B) (Additive.toMul t)) =
          Additive.ofMul (ρ A (ρ B (Additive.toMul t)))
        rw [map_mul, MulAut.mul_apply]
      smul_zero := fun A => by
        change Additive.ofMul (ρ A 1) = 0
        rw [map_one]
        rfl
      smul_add := fun A t t' => by
        change Additive.ofMul (ρ A (Additive.toMul t * Additive.toMul t')) = _
        rw [map_mul]
        rfl }
  have hsmul : ∀ (A : Γ) (t : Additive T),
      ((Additive.toMul (A • t) : T) : E) = α A (Additive.toMul t : T) := fun _ _ => rfl
  set coord : T → Matrix (Fin r) (Fin r) K := fun t => Classical.choose (mem_preN.mp t.2)
    with hcoordDef
  have hcoord : ∀ t : T, IsN θ (coord t) (t : E) := fun t =>
    Classical.choose_spec (mem_preN.mp t.2)
  have huniq : ∀ (t : T) {B : Matrix (Fin r) (Fin r) K}, IsN θ B (t : E) → coord t = B :=
    fun t B hB => (hcoord t).eq_of_isN hr1 hB
  let πT : Additive T →+ Matrix (Fin r) (Fin r) K :=
    { toFun := fun t => coord (Additive.toMul t)
      map_zero' := huniq 1 (isN_zero_iff.mpr (map_one θ))
      map_add' := fun t t' => huniq _ ((hcoord _).mul (hcoord _)) }
  have hπT : ∀ t : Additive T, πT t = coord (Additive.toMul t) := fun _ => rfl
  have hker : ∀ t : Additive T, πT t = 0 ↔ θ ((Additive.toMul t : T) : E) = 1 := fun t => by
    rw [hπT]
    constructor
    · intro h0
      have := hcoord (Additive.toMul t)
      rw [h0] at this
      exact isN_zero_iff.mp this
    · intro h1
      exact huniq _ (isN_zero_iff.mpr h1)
  obtain ⟨-, M₀, hinv, -, -, hinj, hsurj⟩ :=
    four_element_hermitian_trivial_module_extension_splitting hK (Or.inr ⟨hr, rfl⟩)
      (M := Additive T) inferInstance
      (fun t => ⟨2, by
        change Additive.ofMul ((Additive.toMul t) ^ 2 ^ 2) = 0
        have hsq : θ (((Additive.toMul t : T) : E) ^ 2) = 1 := by
          have := (hcoord (Additive.toMul t)).mul (hcoord (Additive.toMul t))
          rw [show coord (Additive.toMul t) + coord (Additive.toMul t) = 0 by
            ext i j
            exact CharTwo.add_self_eq_zero _] at this
          rw [pow_two]
          exact isN_zero_iff.mp this
        have h4 : ((Additive.toMul t : T) : E) ^ 2 ^ 2 = 1 := by
          rw [show (2 ^ 2 : ℕ) = 2 * 2 from rfl, pow_mul, h2 _ hsq]
        exact congrArg Additive.ofMul (Subtype.ext h4)⟩)
      πT (fun t => isHerm_iff.mp (hcoord _).1)
      (fun B hB => by
        obtain ⟨t, ht⟩ := exists_isN hθ (isHerm_iff.mpr hB)
        exact ⟨Additive.ofMul ⟨t, ht.mem⟩, huniq _ ht⟩)
      (fun A t => by
        rw [hπT, hπT]
        obtain ⟨g, hg, he⟩ := hliftα A (Additive.toMul t : T)
        refine huniq _ ?_
        rw [hsmul, he, ← map_bar_transpose (h := h)]
        have hc := (hcoord (Additive.toMul t)).conj (detKerHom h r A) hg
        rw [coe_detKerHom] at hc
        exact hc)
      (fun c hc => by
        rw [AddMonoidHom.mem_ker, hker] at hc
        have h1 := h2 _ hc
        rw [two_nsmul]
        change Additive.ofMul (Additive.toMul c * Additive.toMul c) = 0
        rw [← pow_two]
        exact congrArg Additive.ofMul (Subtype.ext h1))
      (fun A c hc => by
        rw [AddMonoidHom.mem_ker, hker] at hc
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hsmul]
        exact BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ hc)
  let Mt : Subgroup E :=
    { carrier := {e | ∃ he : e ∈ T, Additive.ofMul (⟨e, he⟩ : T) ∈ M₀}
      one_mem' := ⟨one_mem T, zero_mem M₀⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, add_mem ha' hb'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, neg_mem ha'⟩ }
  refine ⟨Mt, fun e he => he.1, fun v hv hv1 => ?_, fun {B} hB => ?_, fun A u hu y hy => ?_⟩
  · obtain ⟨hvT, hvM⟩ := hv
    have h0 := hinj _ hvM ((hker _).mpr hv1)
    exact congrArg Subtype.val (Additive.ofMul.injective h0 : (⟨v, hvT⟩ : T) = 1)
  · obtain ⟨t, ht, htB⟩ := hsurj B (isHerm_iff.mp hB)
    refine ⟨((Additive.toMul t : T) : E), ⟨(Additive.toMul t : T).2, ht⟩, ?_⟩
    rw [← htB, hπT]
    exact hcoord _
  · obtain ⟨hyT, hyM⟩ := hy
    set A' : Γ := ⟨SpecialLinearGroup.toGL A, by
      rw [MonoidHom.mem_ker]
      exact Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, Units.val_one]
        exact A.2)⟩ with hA'
    have hαu : α A' y = u * y * u⁻¹ := by
      change BinarySymplecticSix.liftConj hθ hC
        (hypProj h r 0 (lHom h r (detKerHom h r A'))) y = _
      rw [show hypProj h r 0 (lHom h r (detKerHom h r A')) = θ u from hu.symm,
        BinarySymplecticSix.liftConj_apply, MulAut.conj_apply]
    have hgT : u * y * u⁻¹ ∈ T := hαu ▸ hαT A' y hyT
    refine ⟨hgT, ?_⟩
    have e : Additive.ofMul (⟨u * y * u⁻¹, hgT⟩ : T) = A' • Additive.ofMul ⟨y, hyT⟩ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change u * y * u⁻¹ = ((Additive.toMul (A' • Additive.ofMul (⟨y, hyT⟩ : T)) : T) : E)
      rw [hsmul]
      exact hαu.symm
    rw [e]
    exact hinv A' _ hyM

include hθ hC in
theorem ker_eq_bot_of_sq [Finite E] [Group.IsPerfect E] (hsq : ∀ c, θ c = 1 → c ^ 2 = 1)
    (hr : 4 ≤ r) : θ.ker = ⊥ := by
  have hK := card_eq_four h
  have := h.finite
  have hr1 : 1 ≤ r := by omega
  have h2 : IsPGroup 2 θ.ker := fun c => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, OneMemClass.coe_one]
    exact hsq c c.2)⟩
  obtain ⟨M₀, hM₀N, hM₀inj, hM₀surj, hM₀norm⟩ := exists_radical_complement hθ hC hsq hr
  obtain ⟨hperf, hYinj⟩ := exists_levi_split (by omega) hr hθ hC h2
  set R := (leviHom h r).range with hR
  set Y := ⁅R.comap θ, R.comap θ⁆ with hY
  have hYsurj : ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y, θ y = leviHom h r A := fun A => by
    have hA : leviHom h r A ∈ Y.map θ := by
      rw [hY, SymplecticSixCover.map_derivedComap hθ R]
      exact ⟨A, rfl⟩
    obtain ⟨y, hy, hyA⟩ := hA
    exact ⟨y, hy, hyA⟩
  set Ut := Y ⊓ ((LinearFlag.unitriangular r K).map (leviHom h r)).comap θ with hUt
  have hUtN : Ut ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    obtain ⟨A, -, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hM₀norm A u hAu.symm y, fun hy => ?_⟩
    have := hM₀norm A⁻¹ u⁻¹ (by rw [map_inv, ← hAu, map_inv]) _ hy
    rwa [show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group] at this
  set P₀ := M₀ ⊔ Ut with hP₀
  have hP₀mul : (P₀ : Set E) = (M₀ : Set E) * (Ut : Set E) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ Ut hUtN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hz
    obtain ⟨m, hm, u, hu, rfl⟩ := hz
    obtain ⟨B, hB, hmB⟩ := mem_preN.mp (hM₀N hm)
    obtain ⟨A, hA, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    have h1 : hypProj h r 0 (nElt hB) * hypProj h r 0 (lHom h r (slHom h r A)) = 1 := by
      rw [← hmB]
      change θ m * leviHom h r A = 1
      rw [hAu, ← map_mul, hθz]
    have hA1 := eq_one_of_hypProj_nElt_mul_lHom hr1 hB hA h1
    have hθu : θ u = 1 := by rw [← hAu, hA1, map_one]
    have hθm : θ m = 1 := by rwa [map_mul, hθu, mul_one] at hθz
    rw [hM₀inj m hm hθm, hYinj u (Subgroup.mem_inf.mp hu).1 hθu, one_mul]
  obtain ⟨-, -, -, -, ⟨S, hS⟩, -, -⟩ := unitary_order_and_Sylow h hr1 (Nat.zero_le 1)
  have hSle : (S : Subgroup (hypPSU h r 0)) ≤ P₀.map θ := by
    intro s hs
    rw [hS] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨A, hA, B, hB, rfl⟩ := exists_lHom_mul_nElt_of_mem hg
    obtain ⟨y, hy, hyA⟩ := hYsurj A
    obtain ⟨m, hm, hmB⟩ := hM₀surj hB
    have hyU : y ∈ Ut := ⟨hy, ⟨A, hA, hyA.symm⟩⟩
    refine ⟨y * m, mul_mem (Subgroup.mem_sup_right hyU) (Subgroup.mem_sup_left hm), ?_⟩
    obtain ⟨hB', hmB'⟩ := hmB
    rw [map_mul, hyA, hmB', map_mul]
    rfl
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC h2 S P₀ hSle hinj

include hθ hC in
theorem ker_eq_bot_of_hypPSU [Finite E] [Group.IsPerfect E] (h2 : IsPGroup 2 θ.ker)
    (hr : 4 ≤ r) : θ.ker = ⊥ :=
  UnitaryOddCover.ker_eq_bot_of_sq_reduction
    (fun _ hθ' hC' hsq => ker_eq_bot_of_sq hθ' hC' hsq hr) θ hθ hC h2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem even_even_dimensional_unitary_prime_field_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {r : ℕ} (hr : 4 ≤ r) (hJ : CFSG.Blueprint.LieModel J .PSU (2 * r) 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hcard]; norm_num⟩
    have := h.charP
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 0) h
    let φ : hypPSU h r 0 ≃* J := (hypPSUEquivStatedProj h hR (by omega)).trans e.symm
    set η' : E →* hypPSU h r 0 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryEvenCover.ker_eq_bot_of_hypPSU (φ.symm.surjective.comp hη)
      (hker ▸ hC) (hker ▸ h2) hr
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial

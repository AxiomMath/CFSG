module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4FusionTwo
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem units_zmod_two_eq_one : ∀ u : (ZMod 2)ˣ, u = 1 := by decide

theorem toGL_bijective_zmod_two :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) → GL (Fin 4) (ZMod 2)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL_injective, fun U => ?_⟩
  have hU : U ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* GL (Fin 4) (ZMod 2)).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact units_zmod_two_eq_one _
  obtain ⟨A, hA⟩ := hU
  exact ⟨A, hA⟩

theorem center_SL_zmod_two : center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have key : ∀ r : ZMod 2, r ^ 4 = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r hr
  rw [hr1] at hrA
  refine mem_bot.2 (Subtype.ext ?_)
  rw [← hrA]
  simp

theorem isSimpleGroup_mulAut_of_elemAb_sixteen {E : Type*} [Group E] [Finite E]
    (hc : ∀ a b : E, a * b = b * a) (hs : ∀ a : E, a * a = 1) (hcard : Nat.card E = 16) :
    IsSimpleGroup (MulAut E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup E := { ‹Group E› with mul_comm := hc }
  have h2 : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [sq, hs]
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule h2
  have hfin : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  have h4 : Module.finrank (ZMod 2) (Additive E) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    have h1 : Nat.card (Additive E) = 2 ^ 4 := by
      change Nat.card E = 2 ^ 4
      rw [hcard]
      norm_num
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun α => { (MulEquiv.toAdditive α : Additive E ≃+ Additive E) with
        map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive α) c x }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := fun α => by ext; rfl
      right_inv := fun f => by ext; rfl
      map_mul' := fun α β => by ext; rfl }
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive E) h4
  let eGL : MulAut E ≃* GL (Fin 4) (ZMod 2) :=
    (e.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive E)).symm).trans
      (Matrix.GeneralLinearGroup.toLin' b).symm
  let eSL : GL (Fin 4) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    (MulEquiv.ofBijective _ toGL_bijective_zmod_two).symm
  let ePSL : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq center_SL_zmod_two.symm)
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 4 (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  exact ((eGL.trans eSL).trans ePSL).isSimpleGroup

theorem eq_top_of_index_le_seven {A : Type*} [Group A] [IsSimpleGroup A]
    (hA : Nat.card A = 20160) {K : Subgroup A} (hK : K.index ≤ 7) : K = ⊤ := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
  · exfalso
    have hd := K.index_normalCore_dvd_factorial_index
    rw [h, index_bot, hA] at hd
    have h7 : K.index.factorial ∣ Nat.factorial 7 := Nat.factorial_dvd_factorial hK
    have := Nat.le_of_dvd (Nat.factorial_pos 7) (hd.trans h7)
    norm_num [Nat.factorial] at this
  · exact eq_top_iff.2 (h ▸ K.normalCore_le)

theorem exists_fixed_of_isPGroup {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    {Z Q : Subgroup G} (hZ : ∀ z, z ∈ Z ↔ z ∈ P ∧ ∀ q ∈ P, z * q = q * z)
    (hcard : Nat.card P = 16 * Nat.card Z) (hQ : IsPGroup 2 Q)
    (hQP : Q ≤ normalizer (P : Set G)) :
    ∃ p ∈ P, p ∉ Z ∧ ∀ q ∈ Q, q * p * q⁻¹ * p⁻¹ ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q' : Subgroup (normalizer (P : Set G)) := Q.subgroupOf (normalizer (P : Set G)) with hQ'
  have hQ'p : IsPGroup 2 Q' := hQ.of_equiv (subgroupOfEquivOfLe hQP).symm
  let _ : MulAction Q' (innSub P) := MulAction.compHom _ ((secHom P).comp Q'.subtype)
  have hsmul : ∀ (q : Q') (c : innSub P), q • c = secHom P (q : normalizer (P : Set G)) c :=
    fun _ _ => rfl
  have hmod := hQ'p.card_modEq_card_fixedPoints (innSub P)
  rw [card_innSub P hZ hcard] at hmod
  obtain ⟨c, hc, hc1⟩ : ∃ c ∈ MulAction.fixedPoints Q' (innSub P), c ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 : MulAction.fixedPoints Q' (innSub P) = {1} := by
      ext c
      refine ⟨fun hc => hno c hc, ?_⟩
      rintro rfl q
      rw [hsmul, map_one]
    rw [h1, Nat.card_unique] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨_, ⟨p, rfl⟩⟩, hp⟩ : ∃ c' : innSub P, c' = c := ⟨c, rfl⟩
  refine ⟨p, p.2, fun hpZ => hc1 ?_, fun q hq => ?_⟩
  · rw [← hp]
    exact Subtype.ext ((conj_eq_one_iff_mem P hZ p).2 hpZ)
  · have hqN : q ∈ normalizer (P : Set G) := hQP hq
    have hfix := hc ⟨⟨q, hqN⟩, hq⟩
    rw [hsmul, ← hp] at hfix
    have e := congrArg Subtype.val hfix
    rw [secHom_apply_conj] at e
    have hpq := (conj_eq_conj_iff P).1 e
    have hmem : q * p * q⁻¹ * (p : G)⁻¹ ∈ P :=
      mul_mem ((mem_normalizer_iff.1 hqN p).1 p.2) (inv_mem p.2)
    exact (hZ _).2 ⟨hmem, fun r hr => congrArg Subtype.val (hpq ⟨r, hr⟩)⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

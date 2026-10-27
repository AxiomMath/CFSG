module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeTailCoord
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeD
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LieType.Universal.Spin CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank TauCeti

theorem finite_orthElementaryGroup_tail {F A : Type} [Field F] [Finite F] [AddCommGroup A]
    [Module F A] [Finite A] (r : ℕ) (qA : QuadraticForm F A) :
    Finite (orthElementaryGroup (quadTail r qA)) := by
  have : Finite (((Fin r ⊕ Fin r → F) × A) → ((Fin r ⊕ Fin r → F) × A)) := inferInstance
  have : Finite (((Fin r ⊕ Fin r → F) × A) ≃ₗ[F] ((Fin r ⊕ Fin r → F) × A)) :=
    Finite.of_injective (β := ((Fin r ⊕ Fin r → F) × A) → ((Fin r ⊕ Fin r → F) × A))
      (fun e => ⇑e) fun a b h => LinearEquiv.ext (congrFun h)
  infer_instance

theorem false_of_tail_model {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] [CharP F 3] {A : Type} [AddCommGroup A] [Module F A]
    [FiniteDimensional F A] {r : ℕ} (hr : 3 ≤ r) {qA : QuadraticForm F A}
    (hani : qA.Anisotropic) (hreg : (QuadraticMap.polarBilin qA).Nondegenerate)
    (hm : Module.finrank F A = 1 ∨ Module.finrank F A = 2) {Q₀ : (ι → F) → F}
    (θ : ↥K ≃* StatedProj (StatedOmega Q₀))
    (e₁ : StatedOmega Q₀ ≃* orthElementaryGroup (quadTail r qA))
    (hker : ¬ 3 ∣ Nat.card ((StatedScalars ι F).subgroupOf (StatedOmega Q₀)))
    (h81 : 81 ≤ Nat.card F ^ (r - 1) * Nat.card A) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite A := Module.finite_of_finite F
  have := finite_orthElementaryGroup_tail r qA
  have : Finite (StatedOmega Q₀) := Finite.of_equiv _ e₁.symm.toEquiv
  obtain ⟨⟨S, hS⟩, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 3) hr hani hreg hm
  set PE := (tailUnipotent r qA).subgroupOf (orthElementaryGroup (quadTail r qA))
  let PΩ : Subgroup (StatedOmega Q₀) := PE.map e₁.symm.toMonoidHom
  have hPΩ : Nat.card PΩ = 3 ^ (Nat.card (StatedOmega Q₀)).factorization 3 := by
    rw [Subgroup.card_map_of_injective e₁.symm.injective, ← hS, S.card_eq_multiplicity,
      Nat.card_congr e₁.toEquiv]
  let eP : PE ≃* PΩ := e₁.symm.subgroupMap PE
  obtain ⟨Q, φ', hQ, hφ'⟩ := Proving.exists_sylow_hom_comm_of_surjective
    (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf (StatedOmega Q₀)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hker)
    PΩ hPΩ ((tailUnipCoord hani (by omega)).comp eP.symm.toMonoidHom)
    ((tailUnipCoord_surjective hani (by omega)).comp eP.symm.surjective)
  refine E27Config.false_of_sylow_hom_comm h hz θ Q hQ φ' hφ' ?_
  rw [show Nat.card (Multiplicative ((Fin (r - 1) → F) × A)) =
      Nat.card ((Fin (r - 1) → F) × A) from rfl, Nat.card_prod, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin (r - 1)), Fintype.card_fin]
  exact h81

theorem false_of_pomegaOdd_model_char_three {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {r f : ℕ}
    (hcl : StatedClassicalModel K .POmegaOdd r 3 f) (hfr : 4 ≤ f * r) : False := by
  obtain ⟨⟨-, hf, hr, -⟩, F, _, _, hF, ⟨θ⟩⟩ := hcl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨hB, hT3⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd h2 hr
  have hE := orthogonal_odd_derived_elementary hK2 hB hT3
  refine false_of_tail_model h hz hr anisotropic_oddTailForm (nondegenerate_oddTailForm h2)
    (Or.inl finrank_unit_fun) θ (tailOmegaEquiv (oddTailIsometry r F) (coe_quadOdd r F) hE) ?_ ?_
  · refine not_three_dvd_card_scalars_statedOmega (v₀ := Pi.single (.inr (.inr ())) 1)
      (fun c v => ?_) ?_
    · rw [← coe_quadOdd r F, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← coe_quadOdd r F, quadOdd_apply]
      simp
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Unit), Fintype.card_unit, pow_one,
      ← pow_succ, Nat.sub_add_cancel (by omega), hF, ← pow_mul]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (f * r) := Nat.pow_le_pow_right (by norm_num) hfr

theorem false_of_pomegaMinus_model_char_three {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {n f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus n 3 f) : False := by
  obtain ⟨⟨-, hf, hn⟩, F, _, _, hF, b, c, hirr, ⟨θ⟩⟩ := hcl
  have hn : 4 ≤ n := hn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  obtain ⟨hB, hT3⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus hn hirr
  have hE := orthogonal_odd_derived_elementary hK2 hB hT3
  refine false_of_tail_model h hz (r := n - 1) (by omega) (anisotropic_minusTailForm hirr)
    (nondegenerate_minusTailForm hirr) (Or.inr finrank_fin_two_fun) θ
    (tailOmegaEquiv (minusTailIsometry n F b c) (coe_quadMinus n F b c) hE) ?_ ?_
  · refine not_three_dvd_card_scalars_statedOmega (v₀ := Pi.single (.inr (.inr 0)) 1)
      (fun c' v => ?_) ?_
    · rw [← coe_quadMinus n F b c, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← coe_quadMinus n F b c, quadMinus_apply]
      simp
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, hF, ← pow_mul,
      ← pow_mul, ← pow_add]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (f * (n - 1 - 1) + f * 2) := Nat.pow_le_pow_right (by norm_num) (by
        have hsum : f * (n - 1 - 1) + f * 2 = f * n := by
          rw [← Nat.mul_add]
          congr 1
          omega
        rw [hsum]
        have : 1 ≤ f := hf
        nlinarith)

theorem false_of_typeB_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hp : q.p = 3) (hr : 3 ≤ r) (hfr : 4 ≤ q.exponent * r)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.B r q, hv⟩).Group) : False := by
  have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv
    (by rw [hp]; norm_num) hr e
  rw [hp] at hcl
  exact false_of_pomegaOdd_model_char_three h hz hcl hfr

theorem false_of_typeTwistedD_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (n : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD n q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group) : False := by
  have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD n q hv e
  rw [hp] at hcl
  exact false_of_pomegaMinus_model_char_three h hz hcl

end CFSG.HardMathSupport.Malle.E27Lie

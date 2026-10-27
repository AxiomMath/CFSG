module

public import CFSG.CharacterTheory.Burnside.NontrivialIrrep
public import CFSG.CharacterTheory.Burnside.ClassSumIntegral
public import CFSG.CharacterTheory.Burnside.IntegralTraceScalar
public import CFSG.CharacterTheory.Burnside.ScalarKernel
public import CFSG.CharacterTheory.Burnside.CharacterSelection

public section

namespace CFSG

namespace Burnside.CharacterObstruction

open CategoryTheory
open scoped BigOperators

theorem no_prime_pow_conjClass
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnoncomm : ¬ ∀ y z : G, y * z = z * y)
    (x : G) (hx : x ≠ 1) (r k : ℕ) (hr : Nat.Prime r) :
    Nat.card (ConjClasses.mk x).carrier ≠ r ^ k := by
  classical
  intro hclasspow
  let B : _root_.CFSG.ClassFun.IrrepCharBasis ℂ G :=
    _root_.CFSG.ClassFun.irrepCharBasis (k := ℂ) (G := G)
  obtain ⟨i₀, i, hi₀char, -, hii₀, hχx, hrdim⟩ :=
    Burnside.ClassFun.IrrepCharBasis.exists_char_ne_zero_not_dvd_finrank
      B hx hr
  let V : FDRep ℂ G := B.V i
  let : Simple V := B.simple i
  let : Nontrivial V := FDRep.nontrivial_of_simple V
  let d : ℕ := Module.finrank ℂ V
  let c : ℕ := (Finset.univ.filter fun y : G => IsConj y x).card
  let f : _root_.CFSG.ClassFun ℂ G :=
    _root_.CFSG.ClassFun.conjClassIndicator ℂ x⁻¹
  obtain ⟨lambda, hlambdaHom⟩ :=
    _root_.CFSG.ClassFun.actionHom_is_scalar f V
  have hlambda : _root_.CFSG.ClassFun.action f V =
      lambda • (LinearMap.id : Module.End ℂ V) := by
    have h := congrArg
      (fun m : V ⟶ V => FDRep.homToLinearMap m) hlambdaHom
    exact h
  have hlambdaInt : IsIntegral ℤ lambda :=
    Burnside.ClassFun.isIntegral_scalar_of_action_conjClassIndicator_eq
      x V lambda hlambda
  have htraceClass :
      LinearMap.trace ℂ V (_root_.CFSG.ClassFun.action f V) =
        (c : ℂ) * V.character x := by
    rw [_root_.CFSG.ClassFun.trace_action]
    calc
      (∑ g : G, f g * V.character g⁻¹) =
          ∑ g : G, f g⁻¹ * V.character g := by
        simpa using
          (Equiv.sum_comp (Equiv.inv G)
            (fun g : G => f g * V.character g⁻¹)).symm
      _ = _root_.CFSG.ClassFun.characterPairingLeft ℂ G
          (_root_.CFSG.ClassFun.character V) f := by
        rw [_root_.CFSG.ClassFun.characterPairingLeft_apply]
        apply Finset.sum_congr rfl
        intro g _
        exact mul_comm _ _
      _ = (c : ℂ) * V.character x := by
        simpa [f, c] using
          (_root_.CFSG.ClassFun.characterPairingLeft_conjClassIndicator
            (_root_.CFSG.ClassFun.character V) x)
  have htraceScalar :
      LinearMap.trace ℂ V (_root_.CFSG.ClassFun.action f V) =
        lambda * (d : ℂ) := by
    simpa [d] using
      (_root_.CFSG.ClassFun.trace_action_eq_scalar_mul_finrank
        f V lambda hlambdaHom)
  have hclassEq : (c : ℂ) * V.character x = (d : ℂ) * lambda := by
    rw [← htraceClass, htraceScalar]
    exact mul_comm _ _
  have hset : (ConjClasses.mk x).carrier = {y : G | IsConj y x} := by
    ext y
    simp only [Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj]
  have hcClass : c = Nat.card (ConjClasses.mk x).carrier := by
    dsimp [c]
    rw [hset]
    change (Finset.univ.filter fun y : G => IsConj y x).card =
      Nat.card {y : G // IsConj y x}
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  have hcpow : c = r ^ k := hcClass.trans hclasspow
  have hcop : c.Coprime d := by
    rw [hcpow]
    exact (hr.coprime_pow_of_not_dvd hrdim).symm
  have hd0 : d ≠ 0 := by
    exact (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hcharInt : IsIntegral ℤ (V.character x) :=
    Representation.isIntegral_character_of_isOfFinOrder
      V.ρ x (isOfFinOrder_of_finite x)
  have hnormalizedInt :
      IsIntegral ℤ (V.character x / (d : ℂ)) :=
    isIntegral_div_of_coprime_mul_eq_mul hd0 hcop hcharInt hlambdaInt hclassEq
  change IsIntegral ℤ
    (LinearMap.trace ℂ V (V.ρ x) / (d : ℂ)) at hnormalizedInt
  obtain ⟨n, hn, hxn⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite x)
  have hrhoPow : V.ρ x ^ n = 1 := by
    rw [← map_pow, hxn, map_one]
  have htraceNe :
      LinearMap.trace ℂ V (V.ρ x) / (Module.finrank ℂ V : ℂ) ≠ 0 := by
    change V.character x / (d : ℂ) ≠ 0
    exact div_ne_zero hχx (by exact_mod_cast hd0)
  have hscalarRho : V.ρ x =
      (V.character x / (d : ℂ)) •
        (1 : Module.End ℂ V) := by
    apply Module.End.eq_smul_one_of_pow_eq_one_of_isIntegral_trace_div_finrank
      (V.ρ x) hn hrhoPow htraceNe
    simpa [d] using hnormalizedInt
  have hrhoNe : V.ρ ≠ 1 :=
    Burnside.ClassFun.IrrepCharBasis.rho_ne_one_of_ne_of_character_eq_one
      B hii₀ hi₀char
  have hscalarRhoId : V.ρ x =
      (V.character x / (d : ℂ)) •
        (LinearMap.id : Module.End ℂ V) := by
    rw [hscalarRho]
    congr 1
  exact
    (Burnside.ScalarKernel.no_nonidentity_scalar_of_isSimpleGroup
      V.ρ hrhoNe hnoncomm hx)
      ⟨V.character x / (d : ℂ), hscalarRhoId⟩

end Burnside.CharacterObstruction

end CFSG

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Cov
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Sl2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Real
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3InvType
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Z7

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Sp
open scoped MatrixGroups commutatorElement

section Outer

theorem kaU3II3_thm : KAU3II3 := by
  intro p f F _ _ hp hp2 hf hq3 hF Y _ _ ⟨e⟩ α hout hα2
  classical
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hud e
  have hq : Odd (p ^ f) := by rw [hq3]; decide
  have h3 : 3 ≤ p ^ f := by rw [hq3]
  have hinj := conj_injective_q3 hud hp2 hq3 hθ
  have hθi : Function.Injective θ := cover_injective_q3 hud hq3 hθ
  have hY : Nat.card Y = 6048 := card_eq_6048_of_equiv hud hq3 e
  have hp3 : p = 3 := by
    have : p ∣ 3 := hq3 ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
  rcases involution_type_of_three_le hud hp2 h3 hθ hα2 with
    ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI hud hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  · obtain ⟨D⟩ := outerData_of_typeII hud hp2 h3 hθ hφ hAu hAA hrel
    have h3k : (3 : ↥hud.fixedField) = 0 := by
      have : Fintype ↥hud.fixedField := Fintype.ofFinite _
      have h' := Nat.cast_card_eq_zero ↥hud.fixedField
      rw [← Nat.card_eq_fintype_card, D.card, hq3] at h'
      exact_mod_cast h'
    have h2k : (2 : ↥hud.fixedField) ≠ 0 := by
      intro h2'
      apply one_ne_zero (α := ↥hud.fixedField)
      linear_combination h3k - h2'
    set Ω : Subgroup Y := (θ.comp D.Ψ).range with hΩdef
    have hΩC : Ω ≤ fixSub α := by
      rintro _ ⟨S, rfl⟩
      exact D.fixed S
    have hΩgen : Subgroup.closure {x : Y | x ∈ Ω ∧ Odd (orderOf x)} = Ω :=
      range_closure_odd (θ.comp D.Ψ) (sl2_closure_odd_of_three h3k)
    have hΩp : ∀ p' : ℕ, p'.Prime → p' ≠ 2 → ∀ X : Subgroup Y, IsPGroup p' ↥X → X ≤ fixSub α →
        (∀ ω ∈ Ω, ω ∈ normalizer (X : Set Y)) → X = ⊥ := by
      intro p' hp' hp'2 X hX hXC hXn
      by_cases h3' : p' = 3
      ·
        subst h3'
        by_contra hX1
        have : Fact (Nat.Prime p) := ⟨hp⟩
        have hchar : CharP F p := hud.charP
        have hXp : IsPGroup p ↥X := by rw [hp3]; exact hX
        have hXtp := u3q3_isPGroup_map_comap (unitarySU p f F 3) θ hθi hXp
        have hXt1 := u3q3_map_comap_ne_bot (unitarySU p f F 3) θ hθ.surj hX1
        have hinv : ∀ S : SL(2, ↥hud.fixedField),
            ∀ v ∈ fixedSpace ((X.comap θ).map (unitarySU p f F 3).subtype),
            (((D.Ψ S : ↥(unitarySU p f F 3)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
              fixedSpace ((X.comap θ).map (unitarySU p f F 3).subtype) := fun S v hv =>
          fixedSpace_invariant (mem_normalizer_map_comap _ θ X (hXn _ ⟨S, rfl⟩)) hv
        rcases D.irr _ hinv with hW | hW
        · obtain ⟨v, hv0, hv⟩ := exists_fixed_vector _ hXtp
          have hv' : v ∈ fixedSpace ((X.comap θ).map (unitarySU p f F 3).subtype) := hv
          rw [hW] at hv'
          exact hv0 (by simpa using hv')
        · apply hXt1
          rw [eq_bot_iff]
          intro x hx
          have hall : ∀ v : Fin 3 → F, (x : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := fun v => by
            have hv : v ∈ fixedSpace ((X.comap θ).map (unitarySU p f F 3).subtype) := by
              rw [hW]
              exact Submodule.mem_top
            exact hv x hx
          have hx1 : (x : Matrix (Fin 3) (Fin 3) F) = 1 := by
            apply Matrix.ext_of_mulVec_single
            intro i
            rw [hall (Pi.single i 1), Matrix.one_mulVec]
          exact Subgroup.mem_bot.2 (Units.ext hx1)
      · by_cases h7 : p' = 7
        ·
          subst h7
          by_contra hX1
          have hcard := card_eq_seven_of_pGroup hY hX hX1
          have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
          have hcyc : IsCyclic ↥X := isCyclic_of_prime_card hcard
          have hu : θ (D.Ψ (sl2Upper (1 : ↥hud.fixedField))) ∈ normalizer (X : Set Y) :=
            hXn _ ⟨_, rfl⟩
          have hv : θ (D.Ψ (sl2Lower (1 : ↥hud.fixedField))) ∈ normalizer (X : Set Y) :=
            hXn _ ⟨_, rfl⟩
          have hcc := commutator_mem_centralizer_of_cyclic_cl hcyc hu hv
          set c : SL(2, ↥hud.fixedField) :=
            ⁅sl2Upper (1 : ↥hud.fixedField), sl2Lower (1 : ↥hud.fixedField)⁆ with hc
          have hmapc : θ (D.Ψ c) = ⁅θ (D.Ψ (sl2Upper (1 : ↥hud.fixedField))),
              θ (D.Ψ (sl2Lower (1 : ↥hud.fixedField)))⁆ := by
            rw [hc, map_commutatorElement, map_commutatorElement]
          have hcsq : c * c = -1 := sl2_comm_sq h3k
          have ht2 : θ (D.Ψ c) * θ (D.Ψ c) = 1 := by
            rw [← map_mul, ← map_mul, hcsq, D.negone, map_one]
          have ht1 : θ (D.Ψ c) ≠ 1 := by
            intro h1
            have hne := u3q3_sl2_neg_one_ne_one h2k
            rcases D.ker c h1 with h2 | h2
            · rw [h2, one_mul] at hcsq
              exact hne hcsq.symm
            · rw [h2, neg_mul_neg, one_mul] at hcsq
              exact hne hcsq.symm
          obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX1
          have hy7 : (y : Y) ^ 7 = 1 := pow_seven_eq_one_of_pGroup hY hX y y.2
          have hcc' : θ (D.Ψ c) ∈ centralizer (X : Set Y) := by
            rw [hmapc]
            exact hcc
          have hycomm : (y : Y) * θ (D.Ψ c) = θ (D.Ψ c) * y :=
            Subgroup.mem_centralizer_iff.mp hcc' y y.2
          exact hy1 (Subtype.ext (no_seven_centralizes_involution hud hp2 hq3 e hy7 ht2 ht1 hycomm))
        · exact pGroup_eq_bot_of_not_dvd hp' hX (by rw [hY]; exact not_dvd_6048 hp' hp'2 h3' h7)
    have hsq : ∀ σ : MulAut Y, σ * σ ∈ innSub Y := fun σ => by
      obtain ⟨y, hy⟩ := aut_sq_inner_q3 hud hp2 hq3 hF hθ σ
      exact ⟨y, hy⟩
    exact ka_all_of_omega hinj Ω hΩC hΩgen hΩp (ka_out_triv_of_sq_inner hsq)

end Outer

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

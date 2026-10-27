module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Cov
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Q3Sl2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Z7
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.S3
open scoped MatrixGroups

section Gen2

variable {p f : ℕ} {F : Type} [Field F]

theorem unitarySU_two_closure_odd_q3 [Finite F] (h : UnitaryFieldData p f F) (hq3 : p ^ f = 3) :
    Subgroup.closure {B : ↥(unitarySU p f F 2) | Odd (orderOf B)} = ⊤ := by
  obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ := CFSG.RankThree.PartTwo.Census.nonempty_sl2_mulEquiv_unitarySU_two h
  have h3k : (3 : k) = 0 := by
    have : Fintype k := Fintype.ofFinite k
    have h' := Nat.cast_card_eq_zero k
    rw [← Nat.card_eq_fintype_card, hk, hq3] at h'
    exact_mod_cast h'
  have hcl := sl2_closure_odd_of_three h3k
  rw [eq_top_iff]
  intro B _
  obtain ⟨A, rfl⟩ := ψ.surjective B
  have hA : A ∈ Subgroup.closure {A : SL(2, k) | Odd (orderOf A)} := by
    rw [hcl]
    exact Subgroup.mem_top A
  have hle : Subgroup.closure {A : SL(2, k) | Odd (orderOf A)} ≤
      (Subgroup.closure {B : ↥(unitarySU p f F 2) | Odd (orderOf B)}).comap ψ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro A' hA'
    exact Subgroup.subset_closure (Odd.of_dvd_nat hA' (orderOf_map_dvd ψ.toMonoidHom A'))
  exact hle hA

end Gen2

section Inner

theorem kaU3I3_thm : KAU3I3 := by
  intro p f F _ _ hp hp2 hf hq3 hF Y _ _ ⟨e⟩ α hin hα2 hα1
  classical
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv hud e
  have hq : Odd (p ^ f) := by rw [hq3]; decide
  have hinj := conj_injective_q3 hud hp2 hq3 hθ₀
  obtain ⟨s, hs⟩ := hin
  have hs2 : s * s = 1 := by
    apply hinj
    rw [map_mul, map_one]
    simpa [hs] using hα2
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hα1
    rw [← hs, map_one]
  have hS : SingleInv Y := SingleInv.of_mulEquiv e.symm (singleInv_psu hud hp2)
  obtain ⟨g, hg⟩ := hS (θ₀ (dU hq)) s (theta_dU_sq hq θ₀) (theta_dU_ne_one hud hq hθ₀) hs2 hs1
  set θ : ↥(unitarySU p f F 3) →* Y := (MulAut.conj g).toMonoidHom.comp θ₀ with hθdef
  have hθ : IsCover hud θ := hθ₀.comp_equiv (MulAut.conj g)
  have hθdU : θ (dU hq) = s := by simpa [hθdef, MulAut.conj_apply] using hg
  have hθi : Function.Injective θ := cover_injective_q3 hud hq3 hθ
  have hY : Nat.card Y = 6048 := card_eq_6048_of_equiv hud hq3 e
  have hp3 : p = 3 := by
    have : p ∣ 3 := hq3 ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
  have hfix : ∀ c : Y, c ∈ fixSub α ↔ c * s = s * c := by
    intro c
    rw [mem_fixSub, ← hs, MulAut.conj_apply]
    constructor
    · intro h1
      calc c * s = (s * c * s⁻¹) * s := by rw [h1]
        _ = s * c := by group
    · intro h1
      rw [← h1]
      group
  set Ω : Subgroup Y := (θ.comp (levU hq.pos)).range with hΩdef
  have hΩC : Ω ≤ fixSub α := by
    rintro _ ⟨B, rfl⟩
    rw [hfix, ← hθdU]
    have := levU_mem_centralizer hq B
    rw [mem_centralizer_singleton_iff] at this
    show θ (levU hq.pos B) * θ (dU hq) = θ (dU hq) * θ (levU hq.pos B)
    rw [← map_mul, ← map_mul, this]
  have hΩgen : Subgroup.closure {x : Y | x ∈ Ω ∧ Odd (orderOf x)} = Ω :=
    range_closure_odd (θ.comp (levU hq.pos)) (unitarySU_two_closure_odd_q3 hud hq3)
  have hΩp : ∀ p' : ℕ, p'.Prime → p' ≠ 2 → ∀ X : Subgroup Y, IsPGroup p' ↥X → X ≤ fixSub α →
      (∀ ω ∈ Ω, ω ∈ normalizer (X : Set Y)) → X = ⊥ := by
    intro p' hp' hp'2 X hX hXC hXn
    by_cases h3 : p' = 3
    ·
      subst h3
      by_contra hX1
      have : Fact (Nat.Prime p) := ⟨hp⟩
      have hchar : CharP F p := hud.charP
      have hXp : IsPGroup p ↥X := by rw [hp3]; exact hX
      refine block_no_lgroup hud hq.pos (by omega)
        ((X.comap θ).map (unitarySU p f F 3).subtype) (Subgroup.map_subtype_le _)
        (u3q3_isPGroup_map_comap _ θ hθi hXp) (u3q3_map_comap_ne_bot _ θ hθ.surj hX1) fun B => ?_
      exact mem_normalizer_map_comap _ θ X (hXn _ ⟨B, rfl⟩)
    · by_cases h7 : p' = 7
      · subst h7
        have h7' := pow_seven_eq_one_of_pGroup hY hX
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hxs : x * s = s * x := (hfix x).1 (hXC hx)
        exact no_seven_centralizes_involution hud hp2 hq3 e (h7' x hx) hs2 hs1 hxs
      · exact pGroup_eq_bot_of_not_dvd hp' hX (by rw [hY]; exact not_dvd_6048 hp' hp'2 h3 h7)
  have hsq : ∀ σ : MulAut Y, σ * σ ∈ innSub Y := fun σ => by
    obtain ⟨y, hy⟩ := aut_sq_inner_q3 hud hp2 hq3 hF hθ σ
    exact ⟨y, hy⟩
  exact ka_all_of_omega hinj Ω hΩC hΩgen hΩp (ka_out_triv_of_sq_inner hsq)

end Inner

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

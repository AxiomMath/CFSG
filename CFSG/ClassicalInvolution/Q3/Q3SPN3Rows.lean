module

public import CFSG.ClassicalInvolution.Q3.Q3SPN3Frame
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4On
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3SPN3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TWY CFSG.ClassicalInvolution.Q3.Q3TLK
  CFSG.ClassicalInvolution.Asc77.SPN
open CFSG.ClassicalInvolution.Asc77 (TwinPairOn)
open CFSG.ClassicalInvolution.G2D4Models.Twin

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


section Odd

theorem spinGenOn_odd3 :
    SpinGenOn .POmegaOdd (Generic.modelUniv .POmegaOdd 3 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ 3 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hdim : Module.finrank 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 hn3
  have cq := centralQuot3_odd (m := 3) le_rfl
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup (quadOdd 3 𝔽₃)), ¬ 3 ∣ orderOf c :=
    (powCop3_model (t := .POmegaOdd) (n := 3) trivial hadm (by decide) (by decide)).cop
  show SpinGenOn .POmegaOdd ⟨spinGroup (quadOdd 3 𝔽₃), oddDatum 3 𝔽₃⟩
  exact spinGenOn_of_spin3 odd_gf3 card_gf3 (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) hZ3 (by omega)
    (fun F₁ F₂ h => by
      have := Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega)
    (fun H _ _ ψ hψ => LiftSim.liftSimFr (Asc77.liftSim_quadOdd hp2 hn3 he ψ hψ)) _ cq

end Odd

section Minus

theorem spinGenOn_minus3 :
    SpinGenOn .POmegaMinus (Generic.modelUniv .POmegaMinus 4 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have hdim : Module.finrank 𝔽₃ (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr 3 1)
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have cq := Q3TY.centralQuot3_minus hadm
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf c :=
    (powCop3_model (t := .POmegaMinus) (n := 4) trivial hadm (by decide) (by decide)).cop
  show SpinGenOn .POmegaMinus ⟨spinGroup (quadMinus 4 𝔽₃ (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2), Twisted.minusDatum 4 (minusCoeffs_irr 3 1)⟩
  exact spinGenOn_of_spin3 odd_gf3 card_gf3
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr 3 1))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr 3 1))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr 3 1)) hZ3 (by omega)
    (fun F₁ F₂ h => TG3.hproj_minus (minusCoeffs_irr 3 1) hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ => LiftSim.liftSimFr (Asc77.liftSim_quadMinus hp2 hn4 he ψ hψ)) _ cq

end Minus

section D4

theorem spinGenOn_d4_ord3 {H : Type} [Group H] [Finite H] {ψ : spinGroup Q₄ →* H}
    {R R' : Subgroup (spinGroup Q₄)} {x x' : spinGroup Q₄}
    (hpair : TwinPairOn .POmegaPlus ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ ψ R R' x x')
    (hord : spinAction Q₄ x = spinAction Q₄ x') (s : H)
    (hs : s ∈ Subgroup.normalizer (ψ.range : Set H)) (hss : s * s = 1)
    (hsR : ∀ r ∈ R, s * ψ r = ψ r * s) (hsR' : ∀ r ∈ R', s * ψ r = ψ r * s) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have cq := Q3TY.centralQuot3_plus (m := 4) le_rfl
  have hZ3 := center_plus4_no_three
  have hlift := liftSimFr3_plus4 ψ hpair.ker
  have hRp := cq.pow3 R hpair.mem
  have hR'p := cq.pow3 R' hpair.mem'
  have hRc := cq.map_mem R hpair.mem
  have hR'c := cq.map_mem R' hpair.mem'
  have hRi := cq.inj R hpair.mem
  have hR'i := cq.inj R' hpair.mem'
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := Q3TD.swap_of_twin_pair_ord3 odd_gf3
    (fun z hz => hZ3 z (ker_spinAction_le_center Q₄ hz)) hRp hR'p hRc hR'c hRi hR'i hpair.ne
    hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hord
  exact spinGen_of_frame3 odd_gf3 card_gf3 (nondegenerate_polarBilin_quadPlus 4 _)
    (range_spinAction_quadPlus hn3) hZ3 (by omega) hpair.ker hlift F₁ hF₁ hF₁' hθx s hs hss hsR
    hsR'

theorem spinGenOn_d4_3 :
    SpinGenOn .POmegaPlus ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  intro H _ _ ψ R R' x x' hpair s hs hss hsR hsR'
  obtain ⟨hc, hc2⟩ := twinPairOn_central_div hpair
  obtain ⟨σ, hσ, hθ⟩ := ModelFacts.TG3.exists_aut_ordinary3 hadm hc hc2
  have hpair' := twinPairOn_transport hpair σ hσ
  have hord : spinAction Q₄ (σ x) = spinAction Q₄ (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hr := CFSG.ClassicalInvolution.G2D4Models.Twin.range_comp_symm ψ σ
  have hs' : s ∈ Subgroup.normalizer ((ψ.comp σ.symm.toMonoidHom).range : Set H) := by
    rw [hr]
    exact hs
  have hψx : (ψ.comp σ.symm.toMonoidHom) (σ x) = ψ x := by simp
  have hsR₂ : ∀ r ∈ R.map σ.toMonoidHom, s * (ψ.comp σ.symm.toMonoidHom) r =
      (ψ.comp σ.symm.toMonoidHom) r * s := by
    rintro _ ⟨r, hr', rfl⟩
    simpa using hsR r hr'
  have hsR'₂ : ∀ r ∈ R'.map σ.toMonoidHom, s * (ψ.comp σ.symm.toMonoidHom) r =
      (ψ.comp σ.symm.toMonoidHom) r * s := by
    rintro _ ⟨r, hr', rfl⟩
    simpa using hsR' r hr'
  have key := spinGenOn_d4_ord3 hpair' hord s hs' hss hsR₂ hsR'₂
  rw [hr, hψx] at key
  exact key

end D4

section Final

theorem spinGen3_proved : SpinGen3 := by
  intro t n hspin hadm
  rcases hspin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact spinGenOn_odd3
  · have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
        SpinGenOn .POmegaPlus M := by
      intro M hM
      subst hM
      exact spinGenOn_d4_3
    exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))
  · exact spinGenOn_minus3

end Final

end CFSG.ClassicalInvolution.Q3.Q3SPN3

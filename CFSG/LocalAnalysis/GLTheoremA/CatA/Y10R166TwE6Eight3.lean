module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.RankThree.Chevalley
open CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

namespace TwE6Eight

abbrev twE6Six : Fin Tag.E6.rank := ⟨5, by decide⟩

abbrev twE6A6 : Fin Tag.E6.rank → ℤ := Pi.single twE6Six 1

@[expose] def twE6Deg : (Fin Tag.E6.rank → ℤ) →+ ℤ where
  toFun γ := ∑ j, Tag.E6.cartan twE6Six j * γ j
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib, mul_add]

theorem twE6Deg_apply (γ : Fin Tag.E6.rank → ℤ) :
    twE6Deg γ = ∑ j, Tag.E6.cartan twE6Six j * γ j := rfl

section Certs113_114


theorem twE6Deg_A6 : twE6Deg twE6A6 = 2 := by
  rw [twE6Deg_apply]
  decide +kernel

theorem twE6Deg_pi_single_six : twE6Deg (Pi.single twE6Six 1) = 2 := by
  rw [twE6Deg_apply]
  decide +kernel

theorem twE6Deg_A6_sub {γ : Fin Tag.E6.rank → ℤ} (hdeg : twE6Deg γ = 1) :
    twE6Deg (twE6A6 - γ) = 1 := by
  rw [map_sub, twE6Deg_A6, hdeg]
  norm_num

theorem twE6Deg_bound {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    -2 ≤ twE6Deg γ ∧ twE6Deg γ ≤ 2 := by
  have hall : ∀ δ ∈ rootFinset Tag.E6, -2 ≤ twE6Deg δ ∧ twE6Deg δ ≤ 2 := by
    decide +kernel
  exact hall γ (mem_rootFinset.2 hγ)

theorem not_isRoot_of_twE6Deg_lt {γ : Fin Tag.E6.rank → ℤ} (h : twE6Deg γ < -2) :
    ¬ IsRoot Tag.E6 γ := by
  intro hr
  have := (twE6Deg_bound hr).1
  omega

theorem not_isRoot_of_twE6Deg_gt {γ : Fin Tag.E6.rank → ℤ} (h : 2 < twE6Deg γ) :
    ¬ IsRoot Tag.E6 γ := by
  intro hr
  have := (twE6Deg_bound hr).2
  omega

theorem reflect_twE6Six (v : Fin Tag.E6.rank → ℤ) :
    reflect Tag.E6 twE6Six v = v - twE6Deg v • twE6A6 := by
  funext j
  simp [reflect, twE6Deg, twE6A6, twE6Six, Pi.smul_apply]

theorem isRoot_A6_sub {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hdeg : twE6Deg γ = 1) : IsRoot Tag.E6 (twE6A6 - γ) := by
  have hall : ∀ δ ∈ rootFinset Tag.E6, twE6Deg δ = 1 → (twE6A6 - δ) ∈ rootFinset Tag.E6 := by
    decide +kernel
  exact mem_rootFinset.1 (hall γ (mem_rootFinset.2 hγ) hdeg)

theorem radicalRoots_A6 :
    radicalRoots Tag.E6 twE6A6 = {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ ∧ 0 < twE6Deg γ} := by
  have h : ∀ δ, iform δ twE6A6 = twE6Deg δ := by
    intro δ
    rw [show twE6A6 = Pi.single twE6Six 1 from rfl,
      iform_single_eq_coPair (Or.inl rfl) δ twE6Six]
    rfl
  ext γ
  rw [radicalRoots]
  simp only [Set.mem_setOf_eq]
  rw [h γ]

@[expose] def twE6Five : Fin 5 → (Fin Tag.E6.rank → ℤ)
  | ⟨0, _⟩ => -Pi.single ⟨4, by decide⟩ 1
  | ⟨1, _⟩ => -(Pi.single ⟨3, by decide⟩ 1 + Pi.single ⟨4, by decide⟩ 1)
  | ⟨2, _⟩ => -(Pi.single ⟨2, by decide⟩ 1 + Pi.single ⟨3, by decide⟩ 1 +
      Pi.single ⟨4, by decide⟩ 1)
  | ⟨3, _⟩ => -(Pi.single ⟨0, by decide⟩ 1 + Pi.single ⟨2, by decide⟩ 1 +
      Pi.single ⟨3, by decide⟩ 1 + Pi.single ⟨4, by decide⟩ 1)
  | ⟨4, _⟩ => -(Pi.single ⟨1, by decide⟩ 1 + Pi.single ⟨3, by decide⟩ 1 +
      Pi.single ⟨4, by decide⟩ 1)

theorem twE6Five_isRoot (i : Fin 5) : IsRoot Tag.E6 (twE6Five i) := by
  fin_cases i <;> exact mem_rootFinset.1 (by decide +kernel)

theorem twE6Deg_twE6Five (i : Fin 5) : twE6Deg (twE6Five i) = 1 := by
  fin_cases i <;> decide +kernel

end Certs113_114

section Certs


variable {Ω : Type} [Field Ω] [CharP Ω 2]

@[expose] def twE6UPlus (Ω : Type) [Field Ω] : Subgroup (ModGL Tag.E6 Ω) :=
  rootSpan Tag.E6 Ω (radicalRoots Tag.E6 twE6A6)

theorem isPGroup_twE6UPlus : IsPGroup 2 (twE6UPlus Ω) := by
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  obtain ⟨w, hw⟩ := exists_smul_highRoot_eq hτ
    (show IsRoot Tag.E6 (Pi.single twE6Six 1) from isRoot_single Tag.E6 twE6Six)
  have hmap : (parabolicRadical Tag.E6 Ω (perpNodes Tag.E6)).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      twE6UPlus Ω := by
    rw [twE6UPlus, show twE6A6 = w • highRoot Tag.E6 from by rw [hw]]
    exact map_conj_parabolicRadical_perpNodes hτ w
  have hU : IsPGroup 2 (posUnipotent Tag.E6 Ω) :=
    isPGroup_of_le_posFiltration (pos := Label.position) (K := Ω) 2
      (fun a => Label.position_lt_card a) (posUnipotent_le_posFiltration (τ := Tag.E6) (R := Ω))
  have hP : IsPGroup 2 (parabolicRadical Tag.E6 Ω (perpNodes Tag.E6)) :=
    hU.to_le (parabolicRadical_le_posUnipotent (perpNodes Tag.E6))
  rw [← hmap]
  exact hP.map _

@[expose] def twE6G (Ω : Type) [Field Ω] : ModGL Tag.E6 Ω :=
  pinnedX Tag.E6 Ω (-twE6A6) 1

@[expose] def twE6SBar (Fr : Ω →+* Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  (twE6UPlus Ω).map (MulAut.conj (twE6G Ω)).toMonoidHom ⊓ TwistedDiag.thetaFixed Fr

theorem isPGroup_twE6SBar (Fr : Ω →+* Ω) : IsPGroup 2 (twE6SBar Fr) :=
  ((isPGroup_twE6UPlus (Ω := Ω)).map (MulAut.conj (twE6G Ω)).toMonoidHom).to_le inf_le_left

theorem commute_pinnedX_of_deg {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hdeg : 3 ≤ (twE6Deg α + twE6Deg β).natAbs)
    (h : ¬ IsRoot Tag.E6 (α + β)) (c d : Ω) :
    Commute (pinnedX Tag.E6 Ω α c) (pinnedX Tag.E6 Ω β d) := by
  by_cases hαβ : α = β
  · subst hαβ
    rw [commute_iff_eq]
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · have hαβ' : α ≠ -β := by
      intro hneg
      subst hneg
      simp only [map_neg, neg_add_cancel, Int.natAbs_zero] at hdeg
      omega
    exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hα hβ hαβ hαβ').2 h Ω
      (pinnedX Tag.E6 Ω α c) (mem_rootSubgroup.2 ⟨c, rfl⟩)
      (pinnedX Tag.E6 Ω β d) (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commutator_neg_deg_one {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hdeg : twE6Deg γ = 1) :
    ⁅pinnedX Tag.E6 Ω (-γ) 1, pinnedX Tag.E6 Ω (γ - twE6A6) 1⁆ =
      pinnedX Tag.E6 Ω (-twE6A6) 1 := by
  have hδ : IsRoot Tag.E6 (γ - twE6A6) := by
    have h := IsRoot.neg (isRoot_A6_sub hγ hdeg)
    simpa [neg_sub] using h
  have hαβ : -γ ≠ γ - twE6A6 := by
    intro h
    have h5 := congrFun h twE6Six
    simp [twE6A6, twE6Six] at h5
    omega
  have hαβ' : -γ ≠ -(γ - twE6A6) := by
    intro h
    have h5 := congrFun h twE6Six
    simp [twE6A6, twE6Six] at h5
    omega
  have hroot : IsRoot Tag.E6 (-γ + (γ - twE6A6)) := by
    have h := IsRoot.neg (isRoot_single Tag.E6 twE6Six)
    simpa [twE6A6, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hcomm := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) (IsRoot.neg hγ)
    hδ hαβ hαβ').1 hroot
  have h := hcomm.2 Ω 1 1
  have hsum : -γ + (γ - twE6A6) = -twE6A6 := by abel
  rw [hsum] at h
  rcases hcomm.1 with hε | hε <;> rw [hε] at h <;>
    simpa [twE6A6, CharTwo.neg_eq] using h

theorem weylElt_six_conj {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (c : Ω) :
    weylElt Tag.E6 Ω twE6Six 1 * pinnedX Tag.E6 Ω β c *
        (weylElt Tag.E6 Ω twE6Six 1)⁻¹ =
      pinnedX Tag.E6 Ω (β - twE6Deg β • twE6A6) c := by
  have h := list_prod_weylElt_conj_pinnedX_of_charTwo (τ := Tag.E6) (K := Ω)
    [twE6Six] hβ c
  have hw : (coxeterSystem Tag.E6).wordProd [twE6Six] • β =
      β - twE6Deg β • twE6A6 := by
    rw [CoxeterSystem.wordProd_singleton, simple_smul, reflect_twE6Six]
  rw [hw] at h
  simpa [twE6Six, twE6A6] using h

theorem commute_pinnedX_of_not_root {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : α ≠ β) (hαβ' : α ≠ -β)
    (h : ¬ IsRoot Tag.E6 (α + β)) (c d : Ω) :
    Commute (pinnedX Tag.E6 Ω α c) (pinnedX Tag.E6 Ω β d) :=
  (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) hα hβ hαβ hαβ').2 h Ω
    (pinnedX Tag.E6 Ω α c) (mem_rootSubgroup.2 ⟨c, rfl⟩)
    (pinnedX Tag.E6 Ω β d) (mem_rootSubgroup.2 ⟨d, rfl⟩)

@[expose] def twE6U {γ : Fin Tag.E6.rank → ℤ} (e : Ω) : ModGL Tag.E6 Ω :=
  pinnedX Tag.E6 Ω γ 1 * pinnedX Tag.E6 Ω (twE6A6 - γ) 1 * pinnedX Tag.E6 Ω twE6A6 e

theorem twE6U_mem {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hdeg : twE6Deg γ = 1) (e : Ω) : twE6U (γ := γ) e ∈ twE6UPlus Ω := by
  rw [twE6U, twE6UPlus]
  have hγ' : γ ∈ radicalRoots Tag.E6 twE6A6 := by
    rw [radicalRoots_A6]
    exact ⟨hγ, by rw [hdeg]; norm_num⟩
  have hδ : IsRoot Tag.E6 (twE6A6 - γ) := isRoot_A6_sub hγ hdeg
  have hδ' : twE6A6 - γ ∈ radicalRoots Tag.E6 twE6A6 := by
    rw [radicalRoots_A6]
    exact ⟨hδ, by rw [twE6Deg_A6_sub hdeg]; norm_num⟩
  have hα : twE6A6 ∈ radicalRoots Tag.E6 twE6A6 := by
    rw [radicalRoots_A6]
    exact ⟨isRoot_single Tag.E6 twE6Six, by rw [twE6Deg_A6]; norm_num⟩
  exact Subgroup.mul_mem (H := rootSpan Tag.E6 Ω (radicalRoots Tag.E6 twE6A6))
    (Subgroup.mul_mem (H := rootSpan Tag.E6 Ω (radicalRoots Tag.E6 twE6A6))
      (pinnedX_mem_rootSpan (K := Ω) (S := radicalRoots Tag.E6 twE6A6) hγ' (1 : Ω))
      (pinnedX_mem_rootSpan (K := Ω) (S := radicalRoots Tag.E6 twE6A6) hδ' (1 : Ω)))
    (pinnedX_mem_rootSpan (K := Ω) (S := radicalRoots Tag.E6 twE6A6) hα e)


end Certs

end TwE6Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F

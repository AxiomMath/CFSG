module

public import CFSG.ClassicalInvolution.Q3.Q3OTD4Cls
public import CFSG.ClassicalInvolution.Q3.Q3OTSqCore
public import CFSG.ClassicalInvolution.Asc77.AscT7JSq

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)


section Sq

variable {H : Type} [Group H] [Finite H]

theorem twinSq_plus4 (ψ : spinGroup Q₄ →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄))
    {R R' : Subgroup (spinGroup Q₄)}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hne : R ≠ R') (hc : Commutes R R') {x : spinGroup Q₄} (hx : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) {k : spinGroup Q₄} (hk : k ∈ R) (hkk : ψ k * ψ k = ψ x)
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) :
    alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have hodd := ModelFacts.TG3.odd_natCard_galoisField_three
  have hF3 := ModelFacts.TG3.natCard_galoisField_three
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hdim : 7 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  obtain ⟨σ, fr, hσ, h1, h2, hα⟩ := exists_ordinary_data_plus4 ψ hR hR' hne hc v hvR hvR'
  have hθk : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q₄) :=
    ker_rangeRestrict_le ψ hψ
  have hθ's : Function.Surjective (ψ.rangeRestrict.comp σ.symm.toMonoidHom) :=
    ψ.rangeRestrict_surjective.comp σ.symm.surjective
  have hθ'k := ker_comp_symm_le_center ψ.rangeRestrict hθk σ
  have hθ'σ : ∀ s, (ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom s) =
      ψ.rangeRestrict s := fun s => by
    show ψ.rangeRestrict (σ.symm (σ s)) = _
    rw [MulEquiv.symm_apply_apply]
  have cq := Q3TY.centralQuot3_plus (m := 4) le_rfl
  have hRσ := hσ R hR
  have hxσ : σ.toMonoidHom x ∈ R.map σ.toMonoidHom := Subgroup.mem_map_of_mem _ hx
  have hsq1 : spinAction Q₄ (σ.toMonoidHom x) * spinAction Q₄ (σ.toMonoidHom x) = 1 := by
    rw [← map_mul, ← map_mul, hx2, map_one, map_one]
  have hne1 : spinAction Q₄ (σ.toMonoidHom x) ≠ 1 := fun h => hx1
    (σ.injective (by rw [map_one]; exact cq.inj _ hRσ _ hxσ h))
  have hord1 : orderOf (spinAction Q₄ (σ.toMonoidHom x)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq1) hne1
  have hmem1 : spinAction Q₄ (σ.toMonoidHom x) ∈ fr.La.range := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ hxσ
  have hx₀ : spinAction Q₄ (σ.toMonoidHom x) = fr.La (-1) :=
    (IsFundamental.of_frame fr).eq_of_orderOf_eq_two hodd hmem1 hord1
  have hkF : spinAction Q₄ (σ.toMonoidHom k) ∈ fr.La.range := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hk)
  have hx₀2 : σ.toMonoidHom x * σ.toMonoidHom x = 1 := by
    rw [← map_mul, hx2, map_one]
  have hkx : (ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom k) *
      (ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom k) =
      (ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom x) := by
    rw [hθ'σ, hθ'σ]
    exact Subtype.ext hkk
  have hv : ∀ s : spinGroup Q₄, spinAction Q₄ s ∈ fr.La.range ⊔ fr.swap.La.range →
      v * innL ψ.range ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) s) =
        innL ψ.range ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) s) * v := by
    intro s hs
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, innL_coe]
    exact comm_conj_of_pointwise _ _ (hα s hs)
  have e1 : innL ψ.range ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom k)) =
      FrameVertex.innerHom ψ k := by
    rw [hθ'σ]
    rfl
  have e2 : innL ψ.range ((ψ.rangeRestrict.comp σ.symm.toMonoidHom) (σ.toMonoidHom x)) =
      FrameVertex.innerHom ψ x := by
    rw [hθ'σ]
    rfl
  have hvv' : v * v = innL ψ.range ((ψ.rangeRestrict.comp σ.symm.toMonoidHom)
      (σ.toMonoidHom x)) := by
    rw [e2]
    exact hvv
  have hxc := central_involution_plus4 hR hx hx2 hx1
  have hb1 := innerHom_ne_one_plus4 ψ hψ hR hx hx1
  have hb0 := involutionOddCore_innerHom_plus4 ψ hψ hR hx hx2 hx1 hxc
  have key := alphaOf_sq_core hodd hF3 (nondegenerate_polarBilin_quadPlus 4 _)
    (range_spinAction_quadPlus hn3) (centerScalar_quadPlus hn3)
    (ModelFacts.OrthAut.plus_hker2 4) (by omega) (commutator_orthogonalGroup_quadPlus hn3).le
    ψ.range hθ's hθ'k (Q3TLK.liftSimFr3_plus4 _ hθ'k) fr hkF hx₀ hx₀2 hkx v hv hvv'
    (by rw [e2]; exact hb1) (by rw [e2]; exact hb0)
  rw [e1, e2] at key
  exact key

theorem twinSqAlphaOn_plus4_aux :
    TwinSqAlphaOn .POmegaPlus ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ := by
  intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
  exact twinSq_plus4 ψ hpair.ker hpair.mem hpair.mem' hpair.ne hpair.comm hpair.hx hpair.hx2
    hpair.hx1 hk hkk v hvR hvR' hvv

end Sq

theorem twinSqAlpha3_d4 : TwinSqAlpha 3 1 .POmegaPlus 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ (by norm_num)⟩ →
      TwinSqAlphaOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinSqAlphaOn_plus4_aux
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by norm_num))

end CFSG.ClassicalInvolution.Q3.Q3OT

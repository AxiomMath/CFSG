module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwistedE6Kernel

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)
open CFSG.LieType.Steinberg.Adjoint

section Corner


variable {K : Type} [Field K] [Finite K]

theorem twE6Corner_C0_le (σ : K ≃+* K) :
    twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K :=
  (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans
    (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom)

theorem twE6Corner_decomp (σ : K ≃+* K) (ι : MulAut (twistedE6RootGroup K σ))
    (hι : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ (g : twistedE6RootGroup K σ) (a : Fin TwistTag.E6.tag.rank → Kˣ),
      ∀ x : twistedE6RootGroup K σ,
        (ι x : ModGL TwistTag.E6.tag K) =
          ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a) *
            (x : ModGL TwistTag.E6.tag K) *
            ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a)⁻¹ := by
  obtain ⟨_, ⟨g, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hι
  refine ⟨g, compatDiag TwistTag.E6 σ.toRingHom u, fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_compatDiagAutHom, Subgroup.coe_inv]
  simp only [mul_assoc, mul_inv_rev]

theorem twE6Corner_mem_twR (σ η : K ≃+* K) (g : twistedE6RootGroup K σ)
    (hg : (g : ModGL TwistTag.E6.tag K) ∈ fixedFieldImage TwistTag.E6.tag η) :
    g ∈ twR σ η := by
  rw [mem_twR_iff]
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hg)).2

noncomputable abbrev twE6Corner_orbitProd (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    ModGL TwistTag.E6.tag K :=
  (FieldGraphFieldPointwise.orbitIdx.map fun i => xUnit TwistTag.E6.tag K i (a i : K)).prod

theorem twE6Corner_conj_regular (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    rootDiagUnit TwistTag.E6.tag a *
        (FieldGraphFieldPointwise.regularElt K : ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹ =
      twE6Corner_orbitProd a := by
  rw [FieldGraphFieldPointwise.coe_regularElt, ← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, MulAut.conj_apply]
  rw [(root_diagonal_conjugation TwistTag.E6.tag K a).1 i 1, mul_one]

theorem twE6Corner_posUnipotent_prod (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    twE6Corner_orbitProd a ∈ posUnipotent TwistTag.E6.tag K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_posUnipotent i _

theorem twE6Corner_rootCoord_prod (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (j : Fin TwistTag.E6.tag.rank) :
    rootCoord (FieldGraphFieldPointwise.single_pos j) (twE6Corner_orbitProd a) = (a j : K) :=
  (FieldGraphFieldPointwise.rootCoord_single_list_prod j FieldGraphFieldPointwise.orbitIdx
    (fun i => (a i : K))).trans (FieldGraphFieldPointwise.orbitIdx_sum j (fun i => (a i : K)))

theorem twE6Corner_kernel (σ η : K ≃+* K) (ι : MulAut (twistedE6RootGroup K σ))
    (hι : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hfix : ∀ x ∈ twR σ η, ι x = x) :
    ι = 1 := by
  obtain ⟨g, a, hdec⟩ := twE6Corner_decomp σ ι hι
  obtain ⟨G, hG⟩ : ∃ G : ModGL TwistTag.E6.tag K, G = (g : ModGL TwistTag.E6.tag K) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ModGL TwistTag.E6.tag K, D = rootDiagUnit TwistTag.E6.tag a :=
    ⟨_, rfl⟩
  have hdec' : ∀ x : twistedE6RootGroup K σ,
      (ι x : ModGL TwistTag.E6.tag K) = G * D * (x : ModGL TwistTag.E6.tag K) * (G * D)⁻¹ := by
    intro x
    rw [hG, hD]
    exact hdec x
  have hcomm : ∀ x : twistedE6RootGroup K σ, x ∈ twR σ η →
      G * D * (x : ModGL TwistTag.E6.tag K) * (G * D)⁻¹ = (x : ModGL TwistTag.E6.tag K) := by
    intro x hx
    have h := hdec' x
    rw [hfix x hx] at h
    exact h.symm
  have hG_adj : G ∈ adjointGroup TwistTag.E6.tag K := by
    rw [hG]
    exact twE6Corner_C0_le σ g.2
  obtain ⟨R0, hR0⟩ : ∃ R0 : ModGL TwistTag.E6.tag K,
      R0 = (FieldGraphFieldPointwise.regularElt K : ModGL TwistTag.E6.tag K) := ⟨_, rfl⟩
  have hR0_C0 : R0 ∈ twistedE6RootGroup K σ := by
    rw [hR0]
    exact FieldGraphFieldPointwise.regularElt_mem_graphFixedRootGroup σ.toRingHom
  have hR0_fix : R0 ∈ fixedFieldImage TwistTag.E6.tag η := by
    rw [hR0]
    exact FieldGraphFieldPointwise.regularElt_mem_fixedFieldImage η
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  have hw₀rel : w₀ ∈ relWeylTwist TwistTag.E6 := by
    obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
    rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
    exact hw₁
  obtain ⟨N0, hN0⟩ : ∃ N0 : ModGL TwistTag.E6.tag K,
      N0 = canonicalRep (coxeterSystem TwistTag.E6.tag) K w₀ := ⟨_, rfl⟩
  have hN0_C0 : N0 ∈ twistedE6RootGroup K σ := by
    rw [hN0]
    exact canonicalRep_mem_graphFixedRootGroup hw₀rel
  have hN0_adj : N0 ∈ adjointGroup TwistTag.E6.tag K := by
    rw [hN0]
    exact canonicalRep_mem_adjointGroup _ K w₀
  have hN0_fix : N0 ∈ fixedFieldImage TwistTag.E6.tag η := by
    rw [hN0]
    exact CFSG.LieType.Chevalley.canonicalRep_mem_fixedFieldImage (σ := η) w₀
  have hR0_R : (⟨R0, hR0_C0⟩ : twistedE6RootGroup K σ) ∈ twR σ η :=
    twE6Corner_mem_twR σ η ⟨R0, hR0_C0⟩ hR0_fix
  have hS_C0 : N0 * R0 * N0⁻¹ ∈ twistedE6RootGroup K σ :=
    mul_mem (mul_mem hN0_C0 hR0_C0) (inv_mem hN0_C0)
  have hS_fix : N0 * R0 * N0⁻¹ ∈ fixedFieldImage TwistTag.E6.tag η :=
    mul_mem (mul_mem hN0_fix hR0_fix) (inv_mem hN0_fix)
  have F1 : G * D * R0 * (G * D)⁻¹ = R0 := hcomm ⟨R0, hR0_C0⟩ hR0_R
  have F2 : G * D * (N0 * R0 * N0⁻¹) * (G * D)⁻¹ = N0 * R0 * N0⁻¹ :=
    hcomm ⟨N0 * R0 * N0⁻¹, hS_C0⟩ (twE6Corner_mem_twR σ η ⟨N0 * R0 * N0⁻¹, hS_C0⟩ hS_fix)
  have F3 : G ∈ borelGroup TwistTag.E6.tag K := by
    refine FieldGraphFieldPointwise.mem_borelGroup_of_conj_regular hG_adj
      (twE6Corner_posUnipotent_prod a) ?_ ?_
    · intro j
      rw [twE6Corner_rootCoord_prod]
      exact Units.ne_zero _
    · have hc : D * R0 * D⁻¹ = twE6Corner_orbitProd a := by
        rw [hD, hR0]
        exact twE6Corner_conj_regular a
      have key : G * twE6Corner_orbitProd a * G⁻¹ = R0 := by
        rw [← hc]
        calc G * (D * R0 * D⁻¹) * G⁻¹ = G * D * R0 * (G * D)⁻¹ := by group
          _ = R0 := F1
      rw [key, hR0]
      exact FieldGraphFieldPointwise.regularElt_mem_posUnipotent
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : WeylGroup TwistTag.E6.tag, w₁ = w₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨Dc, hDc⟩ : ∃ Dc : ModGL TwistTag.E6.tag K,
      Dc = rootDiagUnit TwistTag.E6.tag (weylTuple w₁ a) := ⟨_, rfl⟩
  have hNDc : N0⁻¹ * D * N0 = Dc := by
    have hw : w₀ * w₁ = 1 := by rw [hw₁, mul_inv_cancel]
    have h := canonicalRep_conj_rootDiagUnit (K := K) w₀ (weylTuple w₁ a)
    rw [weylTuple_weylTuple, hw, weylTuple_one] at h
    rw [hN0, hD, hDc, ← h]
    group
  have F4 : N0⁻¹ * G * N0 ∈ borelGroup TwistTag.E6.tag K := by
    refine FieldGraphFieldPointwise.mem_borelGroup_of_conj_regular ?_
      (twE6Corner_posUnipotent_prod (weylTuple w₁ a)) ?_ ?_
    · exact mul_mem (mul_mem (inv_mem hN0_adj) hG_adj) hN0_adj
    · intro j
      rw [twE6Corner_rootCoord_prod]
      exact Units.ne_zero _
    · have hc : Dc * R0 * Dc⁻¹ = twE6Corner_orbitProd (weylTuple w₁ a) := by
        rw [hDc, hR0]
        exact twE6Corner_conj_regular _
      have key : N0⁻¹ * G * N0 * twE6Corner_orbitProd (weylTuple w₁ a) * (N0⁻¹ * G * N0)⁻¹ = R0 := by
        rw [← hc, ← hNDc]
        calc N0⁻¹ * G * N0 * (N0⁻¹ * D * N0 * R0 * (N0⁻¹ * D * N0)⁻¹) * (N0⁻¹ * G * N0)⁻¹
            = N0⁻¹ * (G * D * (N0 * R0 * N0⁻¹) * (G * D)⁻¹) * N0 := by group
          _ = R0 := by rw [F2]; group
      rw [key, hR0]
      exact FieldGraphFieldPointwise.regularElt_mem_posUnipotent
  obtain ⟨-, hBmap, hBH, -⟩ := opposite_Borel_intersection TwistTag.E6.tag K w₀ hw₀
  rw [← hN0] at hBmap
  have hG_T : G ∈ torusGroup TwistTag.E6.tag K := by
    have h1 : G ∈ (borelGroup TwistTag.E6.tag K).map (MulAut.conj N0).toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨N0⁻¹ * G * N0, F4, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hBmap] at h1
    have h2 : G ∈ borelGroup TwistTag.E6.tag K ⊓
        (torusGroup TwistTag.E6.tag K ⊔ negUnipotent TwistTag.E6.tag K) :=
      Subgroup.mem_inf.2 ⟨F3, h1⟩
    rw [hBH] at h2
    exact h2
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hG_T
  have hY : G * D = rootDiagUnit TwistTag.E6.tag (l * a) := by
    rw [hl, hD, rootDiagUnit_mul]
  have hb : rootDiagUnit TwistTag.E6.tag (l * a) *
      (FieldGraphFieldPointwise.regularElt K : ModGL TwistTag.E6.tag K) *
      (rootDiagUnit TwistTag.E6.tag (l * a))⁻¹ =
      (FieldGraphFieldPointwise.regularElt K : ModGL TwistTag.E6.tag K) := by
    rw [← hY, ← hR0]
    exact F1
  have hb1 : ∀ j : Fin TwistTag.E6.tag.rank, ((l * a) j : K) = 1 := by
    intro j
    have h1 := congrArg (rootCoord (FieldGraphFieldPointwise.single_pos j))
      ((twE6Corner_conj_regular (l * a)).symm.trans hb)
    rw [twE6Corner_rootCoord_prod, FieldGraphFieldPointwise.rootCoord_regularElt] at h1
    exact h1
  have hla : l * a = 1 := funext fun j => Units.ext (hb1 j)
  have hGD : G * D = 1 := by
    rw [hY, hla, rootDiagUnit_one]
  refine MulEquiv.ext fun x => ?_
  show ι x = x
  refine Subtype.ext ?_
  rw [hdec' x, hGD, inv_one, one_mul, mul_one]

theorem twistedE6KernelCorner_holds : TwistedE6KernelCorner := by
  unfold TwistedE6KernelCorner
  intro K _ _ _ σ _ η _ ι hι hfix
  exact twE6Corner_kernel σ η ι hι hfix

theorem twistedE6KernelLemma_holds : TwistedE6KernelLemma :=
  twistedE6KernelLemma_of_corner twistedE6KernelCorner_holds

end Corner

end CFSG.LieType.SeitzGeneration.ExcWideThree

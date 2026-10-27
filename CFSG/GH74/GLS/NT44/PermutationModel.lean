module

public import CFSG.GH74.GLS.NT44.PermutationInputs
public import CFSG.GH74.GLS.NT44.ActualCover

public noncomputable section

namespace CFSG.GH74.GLS.NT44.PermutationModel

open CFSG.GH74.GLS.NT44
open CFSG.LieType.Multipliers
open CFSG.ComponentClassification.GrSLit
open CFSG.GH74.GLS.NT44.PermutationInputs

theorem fullTwoCover_surjection_original_model
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∃ phi : FullTwoCover →* PermutationInputs.Khat,
      Function.Surjective phi ∧
      (∀ i : Fin 2,
        phi (quotientMk (PresentedGroup.of i)) =
          PermutationInputs.presentationGenerator i) ∧
      ∀ i : Fin 2,
        phi (quotientMk
          (CFSG.ComponentClassification.GrSLit.L34Facts.cv
            (CFSG.Monster.B.Co2.toLetters 2
              (PermutationNative.inputs ()).rev[i.val]!))) =
          PermutationInputs.ksIn i := by
  let lam : CFSG.LieType.Multipliers.L34.Cover →* PermutationInputs.Khat :=
    PresentedGroup.toGroup (f := PermutationInputs.presentationGenerator)
      (PermutationInputs.presentation_relators hcheck)
  have hz : lam CFSG.ComponentClassification.GrSLit.L34Facts.z₃ = 1 := by
    change (FreeGroup.lift PermutationInputs.presentationGenerator)
      (FreeGroup.mk CFSG.LieType.Multipliers.L34.zThree) = 1
    exact PermutationInputs.presentation_zThree hcheck
  have hker : fullTwoCoverKernel ≤ lam.ker := by
    change Subgroup.normalClosure
      ({CFSG.ComponentClassification.GrSLit.L34Facts.z₃} :
        Set CFSG.LieType.Multipliers.L34.Cover) ≤ lam.ker
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact MonoidHom.mem_ker.mpr hz
  let phi : FullTwoCover →* PermutationInputs.Khat :=
    QuotientGroup.lift fullTwoCoverKernel lam hker
  have hcomp : phi.comp quotientMk = lam :=
    QuotientGroup.lift_comp_mk' fullTwoCoverKernel lam hker
  have hsurjlam : Function.Surjective lam := by
    intro a
    have hle : PermutationInputs.Khat ≤
        (PermutationInputs.Khat.subtype.comp lam).range := by
      change Subgroup.closure (Set.range PermutationInputs.ksPerm) ≤ _
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      refine ⟨CFSG.ComponentClassification.GrSLit.L34Facts.cv
        (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).rev[i.val]!), ?_⟩
      change ((FreeGroup.lift PermutationInputs.presentationGenerator)
        (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).rev[i.val]!)) :
          Equiv.Perm (Fin 2688)) = PermutationInputs.ksPerm i
      exact congrArg Subtype.val (PermutationInputs.presentation_reverse hcheck i)
    have ha : (a : Equiv.Perm (Fin 2688)) ∈
        (PermutationInputs.Khat.subtype.comp lam).range := hle a.2
    rcases ha with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  have hsurjphi : Function.Surjective phi :=
    QuotientGroup.lift_surjective_of_surjective fullTwoCoverKernel lam hsurjlam hker
  refine ⟨phi, hsurjphi, ?_, ?_⟩
  · intro i
    rw [show phi (quotientMk (PresentedGroup.of i)) =
        (phi.comp quotientMk) (PresentedGroup.of i) from rfl, hcomp]
    exact PresentedGroup.toGroup.of (PermutationInputs.presentation_relators hcheck)
  · intro i
    rw [show phi (quotientMk
        (CFSG.ComponentClassification.GrSLit.L34Facts.cv
          (CFSG.Monster.B.Co2.toLetters 2
            (PermutationNative.inputs ()).rev[i.val]!))) =
        (phi.comp quotientMk)
          (CFSG.ComponentClassification.GrSLit.L34Facts.cv
            (CFSG.Monster.B.Co2.toLetters 2
              (PermutationNative.inputs ()).rev[i.val]!)) from rfl, hcomp]
    exact PermutationInputs.presentation_reverse hcheck i

theorem restriction_surjection_original_points
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∃ ρ : PermutationInputs.Khat →* PermutationInputs.K448,
      Function.Surjective ρ ∧
      (∀ i : Fin 2,
        (ρ (PermutationInputs.ksIn i) : Equiv.Perm (Fin 448)) =
          PermutationInputs.restrictedKsPerm i) ∧
      ∀ (g : PermutationInputs.Khat) (x : Fin 448),
        PermutationInputs.pointEmbedding hcheck
          ((ρ g : Equiv.Perm (Fin 448)) x) =
        (g : Equiv.Perm (Fin 2688))
          (PermutationInputs.pointEmbedding hcheck x) := by
  let δ := PermutationInputs.pointEmbedding hcheck
  let B : Set (Fin 2688) := Set.range δ
  have hδ_inj : Function.Injective δ := δ.injective
  have hB_inv : ∀ g : PermutationInputs.Khat,
      ∀ y : Fin 2688, y ∈ B ↔ (g : Equiv.Perm (Fin 2688)) y ∈ B := by
    intro g
    refine Subgroup.closure_induction (p := fun x : Equiv.Perm (Fin 2688) =>
      fun _ => ∀ y : Fin 2688, y ∈ B ↔ x y ∈ B) ?_ ?_ ?_ ?_ g.2
    · rintro x ⟨i, rfl⟩ y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨PermutationInputs.restrictedKsPerm i z,
          PermutationInputs.ksPerm_pointEmbedding hcheck i z⟩
      · rintro ⟨z, hz⟩
        refine ⟨(PermutationInputs.restrictedKsPerm i).symm z, ?_⟩
        apply (PermutationInputs.ksPerm i).injective
        have h := PermutationInputs.ksPerm_pointEmbedding hcheck i
          ((PermutationInputs.restrictedKsPerm i).symm z)
        simp only [Equiv.apply_symm_apply] at h
        rw [← h]
        exact hz
    · intro y
      simp
    · intro x y hx hy ihx ihy z
      exact (ihy z).trans (ihx (y z))
    · intro x hx ih z
      have h := ih (x⁻¹ z)
      simpa using h.symm
  let A : SubMulAction PermutationInputs.Khat (Fin 2688) :=
    { carrier := B
      smul_mem' := fun g y hy => (hB_inv g y).1 hy }
  let ePts : Fin 448 ≃ A := Equiv.ofInjective δ δ.injective
  let ρ₀ : PermutationInputs.Khat →* Equiv.Perm (Fin 448) :=
    (Equiv.permCongrHom ePts).symm.toMonoidHom.comp
      (MulAction.toPermHom PermutationInputs.Khat A)
  have hρ₀_apply (g : PermutationInputs.Khat) (x : Fin 448) :
      δ (ρ₀ g x) = (g : Equiv.Perm (Fin 2688)) (δ x) := by
    have h := ePts.apply_symm_apply (g • ePts x)
    have hv := congrArg Subtype.val h
    change δ (ePts.symm (g • ePts x)) = (g : Equiv.Perm (Fin 2688)) (δ x)
    have hL : δ (ePts.symm (g • ePts x)) =
        (ePts (ePts.symm (g • ePts x))).val := rfl
    rw [hL, hv]
    rw [SubMulAction.val_smul, Subgroup.smul_def]
    rfl
  have hgen (i : Fin 2) : ρ₀ (PermutationInputs.ksIn i) =
      PermutationInputs.restrictedKsPerm i := by
    apply Equiv.ext
    intro x
    apply hδ_inj
    rw [hρ₀_apply]
    exact (PermutationInputs.ksPerm_pointEmbedding hcheck i x).symm
  have hle1 : PermutationInputs.K448 ≤ ρ₀.range := by
    rw [PermutationInputs.K448]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨PermutationInputs.ksIn i, hgen i⟩
  have hle2 : ρ₀.range ≤ PermutationInputs.K448 := by
    have hpre : Subgroup.subtype PermutationInputs.Khat ⁻¹'
        Set.range PermutationInputs.ksPerm = Set.range PermutationInputs.ksIn := by
      ext g
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    have htop : Subgroup.closure (Set.range PermutationInputs.ksIn) = ⊤ := by
      rw [← hpre]
      exact Subgroup.closure_closure_coe_preimage
        (k := Set.range PermutationInputs.ksPerm)
    calc
      ρ₀.range = Subgroup.map ρ₀ ⊤ := MonoidHom.range_eq_map ρ₀
      _ = Subgroup.map ρ₀ (Subgroup.closure (Set.range PermutationInputs.ksIn)) := by
        rw [htop]
      _ = Subgroup.closure (ρ₀ '' Set.range PermutationInputs.ksIn) := by
        rw [MonoidHom.map_closure]
      _ ≤ PermutationInputs.K448 := by
        rw [Subgroup.closure_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hgen i]
        exact Subgroup.subset_closure ⟨i, rfl⟩
  have hRange : ρ₀.range = PermutationInputs.K448 := le_antisymm hle2 hle1
  let ρ : PermutationInputs.Khat →* PermutationInputs.K448 :=
    (MulEquiv.subgroupCongr hRange).toMonoidHom.comp ρ₀.rangeRestrict
  refine ⟨ρ, ?_, ?_, ?_⟩
  · have h : Function.Surjective
        (⇑(MulEquiv.subgroupCongr hRange) ∘ ⇑ρ₀.rangeRestrict) :=
      Function.Surjective.comp (MulEquiv.subgroupCongr hRange).surjective
        (MonoidHom.rangeRestrict_surjective ρ₀)
    simpa [ρ, MonoidHom.coe_comp, Function.comp_def] using h
  · intro i
    simp [ρ, hgen i]
  · intro g x
    simpa [ρ] using hρ₀_apply g x

theorem fullTwoCover_equiv_original_model
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∃ (e : FullTwoCover ≃* PermutationInputs.Khat)
        (r : PermutationInputs.Khat ≃* PermutationInputs.K448),
      (∀ i : Fin 2,
        e (quotientMk (PresentedGroup.of i)) =
          PermutationInputs.presentationGenerator i) ∧
      (∀ i : Fin 2,
        e (quotientMk
          (CFSG.ComponentClassification.GrSLit.L34Facts.cv
            (CFSG.Monster.B.Co2.toLetters 2
              (PermutationNative.inputs ()).rev[i.val]!))) =
          PermutationInputs.ksIn i) ∧
      ∀ (g : PermutationInputs.Khat) (x : Fin 448),
        PermutationInputs.pointEmbedding hcheck
          ((r g : Equiv.Perm (Fin 448)) x) =
        (g : Equiv.Perm (Fin 2688))
          (PermutationInputs.pointEmbedding hcheck x) := by
  obtain ⟨φ, hφsurj, hφfwd, hφrev⟩ := fullTwoCover_surjection_original_model hcheck
  obtain ⟨ρ, hρsurj, hρgen, hρact⟩ := restriction_surjection_original_points hcheck
  have hcardK448 : Nat.card PermutationInputs.K448 = 322560 :=
    PermutationInputs.card_K448 hcheck
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfin, hcardFull, -⟩ :=
    (modelStructure : _)
  let : Finite FullTwoCover := hfin
  have hcardK448_le : Nat.card PermutationInputs.K448 ≤ Nat.card PermutationInputs.Khat :=
    Nat.card_le_card_of_surjective ρ hρsurj
  have hcardFull_le : Nat.card FullTwoCover ≤ Nat.card PermutationInputs.Khat := by
    rw [hcardFull, ← hcardK448]
    exact hcardK448_le
  have hφbij : Function.Bijective φ :=
    Function.Surjective.bijective_of_nat_card_le hφsurj hcardFull_le
  let e : FullTwoCover ≃* PermutationInputs.Khat :=
    MulEquiv.ofBijective φ hφbij
  have hcardKhat : Nat.card PermutationInputs.Khat = 322560 := by
    rw [← Nat.card_congr e.toEquiv, hcardFull]
  have hcardKhat_eq : Nat.card PermutationInputs.Khat = Nat.card PermutationInputs.K448 := by
    rw [hcardKhat, hcardK448]
  have hρbij : Function.Bijective ρ :=
    Function.Surjective.bijective_of_nat_card_le hρsurj (le_of_eq hcardKhat_eq)
  let r : PermutationInputs.Khat ≃* PermutationInputs.K448 :=
    MulEquiv.ofBijective ρ hρbij
  refine ⟨e, r, ?_, ?_, ?_⟩
  · intro i
    rw [MulEquiv.ofBijective_apply]
    exact hφfwd i
  · intro i
    rw [MulEquiv.ofBijective_apply]
    exact hφrev i
  · intro g x
    rw [MulEquiv.ofBijective_apply]
    exact hρact g x

end CFSG.GH74.GLS.NT44.PermutationModel

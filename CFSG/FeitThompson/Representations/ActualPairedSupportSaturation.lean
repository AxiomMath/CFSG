module

public import CFSG.FeitThompson.Representations.TypeIPBridgeParity
public import CFSG.FeitThompson.Representations.CyclicTIOddAxesSignedExpansion
public import CFSG.FeitThompson.Representations.TypeIINonfrobeniusCrossedColumnData

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.NormalInducedFamily
open scoped Pointwise ComplexConjugate

universe u

attribute [local instance] CFSG.FeitThompson.Proofs.subgroupFintype

section Data

variable {G : Type u} [Group G] [Fintype G] {S L U W₁ W₂ : Subgroup G} {I J : Type u}
  [Fintype I] [Fintype J]
  {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
  {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
  {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
  {η : I → J → (G → ℂ)} {δ : J → ℂ} {μ : J → (↥S → ℂ)} {γ : ↥S → ℂ}
  {bfam : J → (↥S → ℂ)}

@[expose] def irrOfIndexLeft (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (i : I) : Irr ↥W₁ := ⟨α i, by rw [← hdata.isIrrIndexing_W₁.2.1]; exact Set.mem_range_self _⟩

theorem coe_irrOfIndexLeft
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (i : I) :
    ((irrOfIndexLeft hdata i : Irr ↥W₁) : ↥W₁ → ℂ) = α i := rfl

theorem irrOfIndexLeft_injective
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    Function.Injective (irrOfIndexLeft hdata) := fun _ _ hab =>
  hdata.isIrrIndexing_W₁.1 (congrArg Subtype.val hab)

theorem irrOfIndexLeft_surjective
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    Function.Surjective (irrOfIndexLeft hdata) := by
  intro χ
  have hχ : (χ : ↥W₁ → ℂ) ∈ Set.range α := by rw [hdata.isIrrIndexing_W₁.2.1]; exact χ.2
  obtain ⟨i, hi⟩ := hχ
  exact ⟨i, Subtype.ext hi⟩

theorem irrOfIndexLeft_i₀ (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    irrOfIndexLeft hdata i₀ = principalIrr ↥W₁ :=
  Subtype.ext (by rw [coe_irrOfIndexLeft, hdata.isIrrIndexing_W₁.2.2, coe_principalIrr])

@[expose] noncomputable def equivIrrLeft
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) : I ≃ Irr ↥W₁ :=
  Equiv.ofBijective _ ⟨irrOfIndexLeft_injective hdata, irrOfIndexLeft_surjective hdata⟩

@[expose] noncomputable def equivIrrRight
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) : J ≃ Irr ↥W₂ :=
  Equiv.ofBijective _ ⟨irrOfIndex_injective hdata, irrOfIndex_surjective hdata⟩

theorem equivIrrLeft_apply
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (i : I) :
    equivIrrLeft hdata i = irrOfIndexLeft hdata i := rfl

theorem equivIrrRight_apply
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (j : J) :
    equivIrrRight hdata j = irrOfIndex hdata j := rfl

theorem eta_eq_prodCharEta_full (hodd : Odd (Nat.card G))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (i : I) (j : J) :
    η i j = (isCyclicTIPair_of_isWitnessedPConfiguration hodd hdata.isPConfig).prodCharEta
      (omegaCF ω hdata.isOmegaMap) (irrOfIndexLeft hdata i) (irrOfIndex hdata j) := by
  set hW := isCyclicTIPair_of_isWitnessedPConfiguration hodd hdata.isPConfig with hWdef
  have hwij : w i j = hW.prodChar (α i) (β j) := by
    funext z
    have hz2 : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hz2
    have hz : z = ⟨x * y, by rw [hxy]; exact z.2⟩ := Subtype.ext hxy.symm
    rw [hz, hdata.isProductCharFamily i j ⟨x, hx⟩ ⟨y, hy⟩, hW.prodChar_apply_mul]
  rw [IsCyclicTIPair.prodCharEta_eq_coe_apply, coe_omegaCF,
    IsCyclicTIPair.coe_basisProdIrr_apply, hdata.eta_eq i j, hwij, coe_irrOfIndexLeft,
    coe_irrOfIndex]

end Data

theorem saturation_of_odd_axes
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (ν : (↥L → ℂ) → (G → ℂ)) (hν : IsCoherentDade L ν)
    (φ : ↥L → ℂ) (hφ : φ ∈ calLFam L) (hφ1 : φ 1 = (hallCoreIndex L : ℂ))
    (βL : G → ℂ) (hβL : βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ))
    (hle : hallCoreIndex L ≤ Nat.card ↥W₂ * Nat.card ↥W₁)
    (hrow : ∀ i : I, i ≠ i₀ → ∃ n : ℤ, cfInnerFin βL (η i j₀) = (n : ℂ) ∧ Odd n)
    (hcol : ∀ j : J, j ≠ j₀ → ∃ n : ℤ, cfInnerFin βL (η i₀ j) = (n : ℂ) ∧ Odd n) :
    hallCoreIndex L = Nat.card ↥W₂ * Nat.card ↥W₁ ∧
      ∃ (ε : I → J → ℂ) (χ : G → ℂ),
        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
        (χ = ν φ ∨ χ = -(ν (fun x => (starRingEnd ℂ) (φ x)))) ∧
        (χ ∈ Irr G ∨ -χ ∈ Irr G) ∧
        βL = (∑ i : I, ∑ j : J, ε i j • η i j) - χ ∧
        ∀ (i : I) (j : J), cfInnerFin χ (η i j) = 0 := by
  classical
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, hsep⟩ := h₁ G hamb S U W₁ W₂ (isPConfigSetup_of_isPBridgeData hG hdata)
    L hdata.isCoatom_L hdata.isTypeI_L
  obtain ⟨-, -, hh1, he1, hhe0, hD₀, -, -, -, hIrrFam, -, hncard, -, -⟩ :=
    h₂ G hamb L hdata.isCoatom_L hdata.isTypeI_L
  have hD : IsDadeData L ((hallCoreIn L : Set G) \ {1}) Prep03.sigR := hD₀
  have hHnorm : (hallCore ↥L).Normal := hallCore_normal
  set κ := ↑(calLFam L) with hκ
  set ζ : κ → (↥L → ℂ) := fun χ => (χ : ↥L → ℂ) with hζ
  have hrange : Set.range ζ = calLFam L := Subtype.range_coe
  have hζinj : Function.Injective ζ := Subtype.val_injective
  have hSrange : Set.range ζ = indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}) := by
    rw [hrange, calLFam_eq_indFam]
  set k₀ : κ := ⟨φ, hφ⟩ with hk₀
  have hζk₀ : ζ k₀ = φ := rfl
  have hIrr : ∀ k : κ, ζ k ∈ Irr ↥L := fun k =>
    hIrrFam (by rw [hallIndFamily_eq_calLFam]; exact k.2)
  have hidxH : (hallCore ↥L).index = hallCoreIndex L := index_hallCore_eq L
  have hcardH : Nat.card ↥(hallCore ↥L) = Nat.card ↥(hallCoreIn L) := natCard_hallCore_eq L
  have hζ1 : ζ k₀ 1 = ((hallCore ↥L).index : ℂ) := by rw [hζk₀, hφ1, hidxH]
  have hfin := finite_calLFam L
  have hκfin : Finite κ := hfin.to_subtype
  have hS2 : (Set.range ζ).Nontrivial := by
    rw [hrange]
    have hfc : Finite ↑(calLFam L) := hfin.to_subtype
    refine Set.one_lt_ncard_iff_nontrivial.1 ?_
    have : 2 ≤ (calLFam L).ncard := by rw [← hallIndFamily_eq_calLFam]; exact hncard
    omega
  have hbound : 2 * (hallCore ↥L).index + 1 ≤ Nat.card ↥(hallCore ↥L) := by
    have hh1' : 1 < Nat.card ↥(hallCoreIn L) := hh1
    have he1' : 1 < (hallCoreIn L).relIndex L := he1
    have hhe0' : 2 * (hallCoreIn L).relIndex L ≤ Nat.card ↥(hallCoreIn L) - 1 := hhe0
    rw [← hallCoreIndex_eq] at he1' hhe0'
    rw [hcardH, hidxH]
    omega
  have hφ' : φ ∈ indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}) := by
    rw [← calLFam_eq_indFam]; exact hφ
  have hβLeq : βL = dadeBeta ((hallCoreIn L : Set G) \ {1}) Prep03.sigR (hallCore ↥L) (ζ k₀) := by
    rw [hβL, hζk₀, tauDade_eq_dadeBeta L hD φ hφ' (by rw [hφ1, hidxH])]
  obtain ⟨hadd, hvc, hiso, hcoh⟩ := hν
  have hspan : Submodule.span ℤ (Set.range ζ) = Submodule.span ℤ (calLFam L) := by rw [hrange]
  have hmemspan : ∀ f : ↥(Submodule.span ℤ (Set.range ζ)),
      (f : ↥L → ℂ) ∈ Submodule.span ℤ (calLFam L) := fun f => by rw [← hspan]; exact f.2
  set ν' : ↥(Submodule.span ℤ (Set.range ζ)) →+ ↥(virtualChars G) :=
    AddMonoidHom.mk' (fun f => ⟨ν (f : ↥L → ℂ), hvc _ (hmemspan f)⟩)
      (fun f g => Subtype.ext (hadd _ (hmemspan f) _ (hmemspan g))) with hν'def
  have hle' : charSpanZero (Set.range ζ) ≤ Submodule.span ℤ (Set.range ζ) := fun f hf =>
    (mem_charSpanZero.1 hf).1
  set τ : ↥(charSpanZero (Set.range ζ)) →+ ↥(virtualChars G) :=
    ν'.comp (Submodule.inclusion hle').toAddMonoidHom with hτdef
  have hcoher : IsCoherentWith (Set.range ζ) τ ν' := by
    refine ⟨fun f g => ?_, fun f => rfl⟩
    have h2 := hiso _ (hmemspan f) _ (hmemspan g)
    rw [cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner] at h2
    exact h2
  have hτeq : ∀ (f : ↥(charSpanZero (Set.range ζ)))
      (F : ↥(CFSG.FeitThompson.dadeDomain L ((hallCoreIn L : Set G) \ {1}))),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ f : ↥(virtualChars G)) : G → ℂ) = ((dadeMap hD F : ↥(classFun G)) : G → ℂ) := by
    intro f F hfF
    rw [coe_dadeMap_eq_tauDade, ← hfF]
    have hspanf : (f : ↥L → ℂ) ∈ Submodule.span ℤ (calLFam L) := by
      rw [← hspan]; exact (mem_charSpanZero.1 f.2).1
    exact hcoh _ hspanf (mem_charSpanZero.1 f.2).2
  set hW := isCyclicTIPair_of_isWitnessedPConfiguration hG.odd_natCard hdata.isPConfig with hWdef
  set ωCF := omegaCF ω hdata.isOmegaMap with hωCF
  have hωiso : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ωCF := isCyclicTIIsometry_omegaCF ω _
  have hV : ∀ F : ↥(CFSG.FeitThompson.dadeDomain L
        ((hallCoreIn L : Set G) \ {1})),
      ∀ v ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂,
        ((dadeMap hD F : ↥(classFun G)) : G → ℂ) v = 0 := by
    intro F v hv
    rw [coe_dadeMap_eq_tauDade, tauDade_eq_tauHall]
    refine hsep (F : ↥L → ℂ) (fun x hx => (mem_dadeDomain.1 F.2).2 x hx) v ?_
    exact Or.inr (Set.mem_iUnion.2 ⟨1, ⟨v, (mem_cyclicTIDiff.1 hv).1, by simp⟩⟩)
  have hWcard : Nat.card ↥(W₁ ⊔ W₂) = Nat.card ↥W₂ * Nat.card ↥W₁ := by
    rw [hW.natCard_eq_mul, Nat.mul_comm]
  have heW : (hallCore ↥L).index ≤ Nat.card ↥(W₁ ⊔ W₂) := by rw [hidxH, hWcard]; exact hle
  set eL := equivIrrLeft hdata with heL
  set eR := equivIrrRight hdata with heR
  have hηL : ∀ (i : I) (j : J), η i j = hW.prodCharEta ωCF (eL i) (eR j) := fun i j => by
    rw [eta_eq_prodCharEta_full hG.odd_natCard hdata i j, ← hWdef, ← hωCF]
    rfl
  have hrow' : ∀ i : Irr ↥W₁, i ≠ principalIrr ↥W₁ → ∃ c : ℤ, Odd c ∧
      cfInner (dadeBeta ((hallCoreIn L : Set G) \ {1}) Prep03.sigR (hallCore ↥L) (ζ k₀))
        (hW.prodCharEta ωCF i (principalIrr ↥W₂)) = (c : ℂ) := by
    intro i hi
    have hne : eL.symm i ≠ i₀ := by
      intro hcon
      refine hi ?_
      rw [← Equiv.apply_symm_apply eL i, hcon, heL, equivIrrLeft_apply, irrOfIndexLeft_i₀]
    obtain ⟨n, hn, hodd⟩ := hrow (eL.symm i) hne
    refine ⟨n, hodd, ?_⟩
    have hηeq : η (eL.symm i) j₀ = hW.prodCharEta ωCF i (principalIrr ↥W₂) := by
      rw [hηL, Equiv.apply_symm_apply, heR, equivIrrRight_apply, irrOfIndex_j₀]
    rw [← hβLeq, ← hηeq, ← hn, cfInnerFin_eq_cfInner]
  have hcol' : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → ∃ c : ℤ, Odd c ∧
      cfInner (dadeBeta ((hallCoreIn L : Set G) \ {1}) Prep03.sigR (hallCore ↥L) (ζ k₀))
        (hW.prodCharEta ωCF (principalIrr ↥W₁) j) = (c : ℂ) := by
    intro j hj
    have hne : eR.symm j ≠ j₀ := by
      intro hcon
      refine hj ?_
      rw [← Equiv.apply_symm_apply eR j, hcon, heR, equivIrrRight_apply, irrOfIndex_j₀]
    obtain ⟨n, hn, hodd⟩ := hcol (eR.symm j) hne
    refine ⟨n, hodd, ?_⟩
    have hηeq : η i₀ (eR.symm j) = hW.prodCharEta ωCF (principalIrr ↥W₁) j := by
      rw [hηL, Equiv.apply_symm_apply, heL, equivIrrLeft_apply, irrOfIndexLeft_i₀]
    rw [← hβLeq, ← hηeq, ← hn, cfInnerFin_eq_cfInner]
  obtain ⟨hdeg, ε, hεsign, χ, hχsigned, hχval, hβeq, hχperp⟩ :=
    cyclicTI_dade_saturation (H := hallCore ↥L) (ξ := ζ) (τ := τ) (ν := ν') (k₀ := k₀)
      (W := W₁ ⊔ W₂) (W1 := W₁) (W2 := W₂) (σ := ωCF)
      hG.odd_natCard hD (hallSharp_eq_image L) hSrange hζinj
      (fun _ hf => by obtain ⟨k, rfl⟩ := hf; exact hIrr k) hcoher hτeq hζ1 hS2 hbound hW hωiso
      hV heW hrow' hcol'
  have _ : Fintype (Irr ↥W₁) := Fintype.ofFinite _
  have _ : Fintype (Irr ↥W₂) := Fintype.ofFinite _
  refine ⟨by rw [← hidxH, hdeg, hWcard], fun i j => ε (eL i, eR j),
    χ, fun i j => hεsign _, ?_, mem_signedIrr.1 hχsigned, ?_, ?_⟩
  · rcases hχval with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rw [hβLeq, hβeq, hW.signedProdCharEtaSum_eq_sum, Fintype.sum_prod_type]
    refine congrArg (fun z => z - χ) (Eq.symm ?_)
    refine Fintype.sum_equiv eL _ _ fun i => ?_
    refine Fintype.sum_equiv eR _ _ fun j => ?_
    rw [hηL i j]
  · intro i j
    have hψ : ((hW.basisProdIrr (eL i, eR j) : ↥(classFun ↥(W₁ ⊔ W₂))) : ↥(W₁ ⊔ W₂) → ℂ)
        ∈ Irr ↥(W₁ ⊔ W₂) := by
      rw [hW.coe_basisProdIrr_apply]
      exact hW.prodChar_mem_Irr (eL i).2 (eR j).2
    have hor := hχperp _ hψ
    rw [isOrthogonal_iff] at hor
    rw [cfInnerFin_eq_cfInner, hηL i j, IsCyclicTIPair.prodCharEta_eq_coe_apply]
    exact hor

theorem odd_col_coeff
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (ν : (↥L → ℂ) → (G → ℂ)) (hν : IsCoherentDade L ν)
    (φ : ↥L → ℂ) (hφ : φ ∈ calLFam L) (hφ1 : φ 1 = (hallCoreIndex L : ℂ))
    (βL : G → ℂ) (hβL : βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ))
    (hlt : ((Nat.card ↥U : ℚ) - 1) / (Nat.card ↥W₁ : ℚ)
      < ((Nat.card ↥(hallCoreIn L) : ℚ) - 1) / (hallCoreIndex L : ℚ)) :
    ∀ j : J, j ≠ j₀ → ∃ n : ℤ, cfInnerFin βL (η i₀ j) = (n : ℂ) ∧ Odd n := by
  by_cases hex : ∃ j₁ : J, j₁ ≠ j₀
  · obtain ⟨j₁, hj₁⟩ := hex
    obtain ⟨-, -, hmain⟩ := FCH_type_I_P_bridge_parity h₁ h₂ h₃ G hG S L U W₁ W₂ I J
      inferInstance inferInstance α β i₀ j₀ w σ ω η δ μ γ bfam hdata
      (Nat.card ↥(hallCoreIn L)) (hallCoreIndex L) (Nat.card ↥W₂) (Nat.card ↥W₁)
      (Nat.card ↥U) rfl rfl rfl rfl rfl
    obtain ⟨-, -, -, -, -, -, hthr⟩ := hmain ν hν φ hφ hφ1 βL hβL j₁ hj₁ _ _ rfl rfl
    exact (hthr hlt).1
  · exact fun j hj => absurd ⟨j, hj⟩ hex

namespace Recip

variable {G : Type u} [Group G] [Fintype G] {T W₂ W₁ : Subgroup G}

theorem memClassFun_comp {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {f : Y → ℂ}
    (hf : f ∈ classFun Y) : f ∘ e ∈ classFun X := by
  rw [mem_classFun] at hf ⊢
  intro x y hxy
  obtain ⟨u, hu⟩ := hxy
  refine hf (e x) (e y) ⟨⟨e u, e u⁻¹, by simp, by simp⟩, ?_⟩
  simp only [SemiconjBy] at hu ⊢
  simpa using congrArg e hu

theorem mulComm_of_isCyclic {H : Type*} [Group H] (h : IsCyclic H) (a b : H) : a * b = b * a := by
  letI := h.commGroup
  exact mul_comm a b

theorem classFunTop {H : Type*} [Group H] (h : IsCyclic H) : classFun H = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [mem_classFun]
  intro x y hxy
  obtain ⟨u, hu⟩ := hxy
  simp only [SemiconjBy] at hu
  have hxy' : x = y := by
    have h2 := hu; rw [mulComm_of_isCyclic h] at h2; exact mul_right_cancel h2
  rw [hxy']

theorem isClassFun_of_mem {H : Type*} [Group H] {f : H → ℂ} (h : f ∈ classFun H) :
    IsClassFun f := by
  rw [isClassFun_iff]
  intro x g
  exact (mem_classFun.1 h _ _
    ⟨⟨x, x⁻¹, mul_inv_cancel x, inv_mul_cancel x⟩, by simp [SemiconjBy, mul_assoc]⟩).symm

theorem cfInner_comp {X Y : Type*} [Group X] [Group Y] [Fintype X] [Fintype Y]
    (e : X ≃* Y) (f g : Y → ℂ) : cfInner (f ∘ e) (g ∘ e) = cfInner f g := by
  rw [cfInner_def, cfInner_def]
  have h : Nat.card X = Nat.card Y := Nat.card_eq_of_bijective _ e.bijective
  rw [h]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)

theorem virtualChars_comp {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {f : Y → ℂ}
    (hf : f ∈ virtualChars Y) : f ∘ e ∈ virtualChars X := by
  rw [mem_virtualChars_iff] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (CFSG.FeitThompson.Proofs.irr_comp_mulEquiv hx e)
  | zero => simp
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => exact Submodule.smul_mem _ a ih

theorem indClassFun_congr' {L : Type*} [Group L] [Fintype L] {K K' : Subgroup L}
    (h : K = K') (θ : ↥K → ℂ) (θ' : ↥K' → ℂ)
    (hθ : ∀ (x : L) (hx : x ∈ K) (hx' : x ∈ K'), θ ⟨x, hx⟩ = θ' ⟨x, hx'⟩) :
    indClassFun K θ = indClassFun K' θ' := by
  subst h
  have : θ = θ' := funext fun x => hθ (x : L) x.2 x.2
  rw [this]

theorem indTop_congr_sub {K K' : Subgroup G} (h : K = K') (θ : ↥K' → ℂ) :
    indTop K (θ ∘ (MulEquiv.subgroupCongr h)) = indTop K' θ := by
  subst h; rfl

@[expose] def wR {A B : Subgroup G} {I J : Type u} (w : I → J → (↥(A ⊔ B) → ℂ)) :
    J → I → (↥(B ⊔ A) → ℂ) :=
  fun j i z => w i j (MulEquiv.subgroupCongr (sup_comm B A) z)

theorem wR_apply {A B : Subgroup G} {I J : Type u} (w : I → J → (↥(A ⊔ B) → ℂ))
    (j : J) (i : I) (z : ↥(B ⊔ A)) (z' : ↥(A ⊔ B)) (h : (z' : G) = (z : G)) :
    wR w j i z = w i j z' := by
  have he : (MulEquiv.subgroupCongr (sup_comm B A) z : ↥(A ⊔ B)) = z' :=
    Subtype.ext (by simpa using h.symm)
  rw [wR, he]

theorem isProductCharFamily_wR {A B : Subgroup G} {I J : Type u} {α : I → (↥A → ℂ)}
    {β : J → (↥B → ℂ)} {w : I → J → (↥(A ⊔ B) → ℂ)}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hw : IsProductCharFamily A B α β w) : IsProductCharFamily B A β α (wR w) := by
  intro j i y x hyx
  have hxy : (x : G) * (y : G) ∈ A ⊔ B := by
    rw [hcomm _ x.2 _ y.2]; rwa [sup_comm] at hyx
  rw [wR_apply w j i ⟨(y : G) * (x : G), hyx⟩ ⟨(x : G) * (y : G), hxy⟩ (hcomm _ x.2 _ y.2),
    hw i j x y hxy]
  ring

@[expose] noncomputable def omegaR {A B : Subgroup G} (ω : (↥(A ⊔ B) → ℂ) →ₗ[ℂ] (G → ℂ)) :
    (↥(B ⊔ A) → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ω.comp (LinearMap.funLeft ℂ ℂ (MulEquiv.subgroupCongr (sup_comm A B)))

theorem omegaR_apply {A B : Subgroup G} (ω : (↥(A ⊔ B) → ℂ) →ₗ[ℂ] (G → ℂ))
    (f : ↥(B ⊔ A) → ℂ) : omegaR ω f = ω (f ∘ (MulEquiv.subgroupCongr (sup_comm A B))) := rfl

theorem omegaR_wR {A B : Subgroup G} (ω : (↥(A ⊔ B) → ℂ) →ₗ[ℂ] (G → ℂ)) {I J : Type u}
    (w : I → J → (↥(A ⊔ B) → ℂ)) (j : J) (i : I) :
    omegaR ω (wR w j i) = ω (w i j) := rfl

theorem cyclicTIset_comm (A B : Subgroup G) : cyclicTIset B A = cyclicTIset A B := by
  ext z
  rw [mem_cyclicTIset, mem_cyclicTIset, sup_comm]
  tauto

theorem isOmegaMap_omegaR {A B : Subgroup G} {ω : (↥(A ⊔ B) → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hω : IsOmegaMap A B ω) : IsOmegaMap B A (omegaR ω) := by
  classical
  set e : ↥(A ⊔ B) ≃* ↥(B ⊔ A) := MulEquiv.subgroupCongr (sup_comm A B) with he
  refine ⟨fun f => hω.isClassFun _, ?_, ?_, ?_, ?_⟩
  · intro f g
    rw [omegaR_apply, omegaR_apply, hω.inner_eq, cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner]
    exact cfInner_comp e f g
  · intro f hf
    rw [omegaR_apply]
    exact hω.maps_virtualChars _ (virtualChars_comp e hf)
  · rw [omegaR_apply]
    have h1 : ((1 : ↥(B ⊔ A) → ℂ) ∘ e) = (1 : ↥(A ⊔ B) → ℂ) := rfl
    rw [h1, hω.map_principal]
  · intro f hf
    rw [omegaR_apply]
    have hvan : ∀ z : ↥(A ⊔ B), (z : G) ∉ cyclicTIset A B → (f ∘ e) z = 0 := by
      intro z hz
      refine hf _ ?_
      rw [cyclicTIset_comm]
      simpa [he] using hz
    rw [hω.eq_ind _ hvan]
    exact indTop_congr_sub (sup_comm A B) f

@[expose] noncomputable def supEq (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) :
    ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T) ≃* ↥(W₂ ⊔ W₁) :=
  (MulEquiv.subgroupCongr (Subgroup.subgroupOf_sup h2 h1).symm).trans
    (Subgroup.subgroupOfEquivOfLe (sup_le h2 h1))

theorem coe_supEq (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) (z : ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) :
    ((supEq h2 h1 z : ↥(W₂ ⊔ W₁)) : G) = ((z : ↥T) : G) := by
  simp [supEq, Subgroup.subgroupOfEquivOfLe]

@[expose] noncomputable def pullCF (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) :
    ↥(classFun ↥(W₂ ⊔ W₁)) →ₗ[ℂ] ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) where
  toFun f := ⟨(f : ↥(W₂ ⊔ W₁) → ℂ) ∘ supEq h2 h1, memClassFun_comp _ f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] noncomputable def sigmaT (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) (hcyc : IsCyclic ↥(W₂ ⊔ W₁))
    (τ : ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) →ₗ[ℂ] ↥(classFun ↥T)) :
    (↥(W₂ ⊔ W₁) → ℂ) →ₗ[ℂ] (↥T → ℂ) :=
  ((classFun ↥T).subtype).comp (τ.comp ((pullCF h2 h1).comp
    ((LinearEquiv.ofTop _ (classFunTop hcyc)).symm.toLinearMap)))

theorem sigmaT_apply (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) (hcyc : IsCyclic ↥(W₂ ⊔ W₁))
    (τ : ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) →ₗ[ℂ] ↥(classFun ↥T))
    (f : ↥(W₂ ⊔ W₁) → ℂ) :
    sigmaT h2 h1 hcyc τ f =
      ((τ (pullCF h2 h1 ⟨f, by rw [classFunTop hcyc]; trivial⟩) : ↥(classFun ↥T)) : ↥T → ℂ) := rfl

theorem isSigmaMap_sigmaT (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) (hcyc : IsCyclic ↥(W₂ ⊔ W₁))
    {τ : ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T)) →ₗ[ℂ] ↥(classFun ↥T)}
    (hτ : IsCyclicTIIsometry (W₂.subgroupOf T ⊔ W₁.subgroupOf T)
      (W₂.subgroupOf T) (W₁.subgroupOf T) τ) :
    IsSigmaMap T W₂ W₁ (sigmaT h2 h1 hcyc τ) := by
  classical
  refine ⟨fun f => isClassFun_of_mem (τ _).2, ?_, ?_, ?_, ?_⟩
  · intro f g
    rw [cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner, sigmaT_apply, sigmaT_apply, hτ.inner_eq]
    exact cfInner_comp (supEq h2 h1) f g
  · intro f hf
    rw [sigmaT_apply]
    exact hτ.map_virtualChars _ (virtualChars_comp (supEq h2 h1) hf)
  · have hp : pullCF h2 h1 ⟨(1 : ↥(W₂ ⊔ W₁) → ℂ), by rw [classFunTop hcyc]; trivial⟩
        = principalClassFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T) := by
      apply Subtype.ext
      rw [coe_principalClassFun]
      rfl
    rw [sigmaT_apply, hp, hτ.map_principalClassFun, coe_principalClassFun]
  · intro f hf
    set g : ↥(classFun ↥(W₂ ⊔ W₁)) := ⟨f, by rw [classFunTop hcyc]; trivial⟩ with hg
    have hvan : ∀ x : ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T),
        (x : ↥T) ∉ cyclicTIDiff (W₂.subgroupOf T ⊔ W₁.subgroupOf T)
          (W₂.subgroupOf T) (W₁.subgroupOf T) →
        ((pullCF h2 h1 g : ↥(classFun ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T))) :
          ↥(W₂.subgroupOf T ⊔ W₁.subgroupOf T) → ℂ) x = 0 := by
      intro x hx
      change f (supEq h2 h1 x) = 0
      refine hf _ ?_
      rw [coe_supEq]
      intro hmem
      refine hx ?_
      rw [mem_cyclicTIset] at hmem
      rw [mem_cyclicTIDiff]
      exact ⟨x.2, by rw [Subgroup.mem_subgroupOf]; exact hmem.2.1,
        by rw [Subgroup.mem_subgroupOf]; exact hmem.2.2⟩
    have hind := hτ.eq_indClassFun (pullCF h2 h1 g) hvan
    rw [sigmaT_apply, hind,
      CFSG.FeitThompson.Proofs.indBetween_eq_indClassFun_subgroupOf (sup_le h2 h1) f]
    refine indClassFun_congr' (Subgroup.subgroupOf_sup h2 h1).symm _ _ ?_
    intro x hx hx'
    rfl

@[expose] noncomputable def irrSub {A : Subgroup G} (hA : A ≤ T) (a : Irr ↥A) :
    Irr ↥(A.subgroupOf T) :=
  ⟨(a : ↥A → ℂ) ∘ (Subgroup.subgroupOfEquivOfLe hA),
    CFSG.FeitThompson.Proofs.irr_comp_mulEquiv a.2 _⟩

theorem coe_irrSub {A : Subgroup G} (hA : A ≤ T) (a : Irr ↥A) (y : ↥(A.subgroupOf T)) :
    ((irrSub hA a : Irr ↥(A.subgroupOf T)) : ↥(A.subgroupOf T) → ℂ) y
      = (a : ↥A → ℂ) (Subgroup.subgroupOfEquivOfLe hA y) := rfl

theorem coe_subgroupOfEquivOfLe {A : Subgroup G} (hA : A ≤ T) (y : ↥(A.subgroupOf T)) :
    ((Subgroup.subgroupOfEquivOfLe hA y : ↥A) : G) = ((y : ↥T) : G) := by
  simp [Subgroup.subgroupOfEquivOfLe]

theorem pullCF_prodChar (h2 : W₂ ≤ T) (h1 : W₁ ≤ T) (hcyc : IsCyclic ↥(W₂ ⊔ W₁))
    (hWsub : IsCyclicTIPair (W₂.subgroupOf T ⊔ W₁.subgroupOf T)
      (W₂.subgroupOf T) (W₁.subgroupOf T))
    (b : Irr ↥W₂) (a : Irr ↥W₁) (f : ↥(W₂ ⊔ W₁) → ℂ)
    (hf : ∀ (x y : G) (hx : x ∈ W₂) (hy : y ∈ W₁) (hxy : x * y ∈ W₂ ⊔ W₁),
      f ⟨x * y, hxy⟩ = (b : ↥W₂ → ℂ) ⟨x, hx⟩ * (a : ↥W₁ → ℂ) ⟨y, hy⟩) :
    pullCF h2 h1 ⟨f, by rw [classFunTop hcyc]; trivial⟩
      = hWsub.basisProdIrr (irrSub h2 b, irrSub h1 a) := by
  apply Subtype.ext
  rw [hWsub.coe_basisProdIrr_apply]
  funext z
  have hz : ((z : ↥T) : ↥T) ∈ ((W₂.subgroupOf T : Set ↥T) * (W₁.subgroupOf T : Set ↥T)) := by
    rw [hWsub.mul_eq]; exact z.2
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hz
  have hx' : x ∈ W₂.subgroupOf T := hx
  have hy' : y ∈ W₁.subgroupOf T := hy
  have hzeq : z = ⟨x * y, by rw [hxy]; exact z.2⟩ := Subtype.ext hxy.symm
  rw [hzeq, hWsub.prodChar_apply_mul _ _ hx' hy']
  change f (supEq h2 h1 ⟨x * y, _⟩) = _
  have hxG : ((x : ↥T) : G) ∈ W₂ := by have := hx'; rwa [Subgroup.mem_subgroupOf] at this
  have hyG : ((y : ↥T) : G) ∈ W₁ := by have := hy'; rwa [Subgroup.mem_subgroupOf] at this
  have hmul : ((x : ↥T) : G) * ((y : ↥T) : G) ∈ W₂ ⊔ W₁ :=
    mul_mem (le_sup_left (α := Subgroup G) hxG) (le_sup_right (α := Subgroup G) hyG)
  have hfeq : (supEq h2 h1 ⟨x * y, by rw [hxy]; exact z.2⟩ : ↥(W₂ ⊔ W₁))
      = ⟨((x : ↥T) : G) * ((y : ↥T) : G), hmul⟩ := by
    apply Subtype.ext; rw [coe_supEq]; rfl
  rw [hfeq, hf _ _ hxG hyG, coe_irrSub, coe_irrSub]
  congr 2

theorem le_of_pconfig_left {V₀ : Subgroup G} (hc : IsWitnessedPConfiguration T V₀ W₂ W₁) :
    W₂ ≤ T := by
  calc W₂ ≤ ⁅T,T⁆ ⊔ W₂ := le_sup_right
  _ = T := hc.sup_commutator_W₁

theorem le_of_pconfig_right {V₀ : Subgroup G} (hc : IsWitnessedPConfiguration T V₀ W₂ W₁) :
    W₁ ≤ T :=
  (hc.le_W₂.trans inf_le_left).trans (Subgroup.map_subtype_le _)

theorem exists_reciprocal_bridge_data
    (hodd : Odd (Nat.card G)) {L V₀ : Subgroup G} {I J : Type u} [Fintype I] [Fintype J]
    {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hT : IsCoatom T) (hcfgT : IsWitnessedPConfiguration T V₀ W₂ W₁)
    (hL : IsCoatom L) (hLI : IsTypeI L)
    (hIrr1 : IsIrrIndexing W₁ α i₀) (hIrr2 : IsIrrIndexing W₂ β j₀)
    (hprod : IsProductCharFamily W₁ W₂ α β w) (hom : IsOmegaMap W₁ W₂ ω) :
    ∃ (σT : (↥(W₂ ⊔ W₁) → ℂ) →ₗ[ℂ] (↥T → ℂ)) (δ' : I → ℂ) (μ' : I → (↥T → ℂ))
      (γ' : ↥T → ℂ) (b' : I → (↥T → ℂ)),
      IsPBridgeData T L V₀ W₂ W₁ β α j₀ i₀ (wR w) σT (omegaR ω)
        (fun j i => omegaR ω (wR w j i)) δ' μ' γ' b' := by
  classical
  have h2 : W₂ ≤ T := le_of_pconfig_left hcfgT
  have h1 : W₁ ≤ T := le_of_pconfig_right hcfgT
  have hWpair : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁ :=
    isCyclicTIPair_map_subtype_of_isWitnessedPConfiguration hodd hcfgT
  have hcyc : IsCyclic ↥(W₂ ⊔ W₁) := hWpair.isCyclic
  have hPC := hcfgT.isPrimeCyclicTIHyp_subgroupOf hodd (U := V₀)
  obtain ⟨τ, hτ⟩ := hPC.exists_isCyclicTIIsometry
  have hσT : IsSigmaMap T W₂ W₁ (sigmaT h2 h1 hcyc τ) := isSigmaMap_sigmaT h2 h1 hcyc hτ
  have hαi : ∀ i : I, α i ∈ Irr ↥W₁ := fun i => by
    rw [← hIrr1.2.1]; exact Set.mem_range_self _
  have hβj₀ : (β j₀ : ↥W₂ → ℂ) = 1 := hIrr2.2.2
  have hkey : ∀ i : I, pullCF h2 h1
      ⟨wR w j₀ i, by rw [classFunTop hcyc]; trivial⟩
      = hPC.isCyclicTIPair.basisProdIrr
          (principalIrr ↥(W₂.subgroupOf T), irrSub h1 ⟨α i, hαi i⟩) := by
    intro i
    have hpp : (principalIrr ↥(W₂.subgroupOf T)) = irrSub h2 (principalIrr ↥W₂) := by
      apply Subtype.ext
      funext y
      rw [coe_irrSub, coe_principalIrr, coe_principalIrr]
      rfl
    rw [hpp]
    refine pullCF_prodChar h2 h1 hcyc hPC.isCyclicTIPair _ _ _ ?_
    intro x y hx hy hxy
    have hxy' : y * x ∈ W₁ ⊔ W₂ := by
      rw [hWpair.commute _ hx _ hy] at hxy; rwa [sup_comm] at hxy
    rw [wR_apply w j₀ i ⟨x * y, hxy⟩ ⟨y * x, hxy'⟩ (hWpair.commute _ hx _ hy).symm,
      hprod i j₀ ⟨y, hy⟩ ⟨x, hx⟩ hxy', coe_principalIrr]
    change α i ⟨y, hy⟩ * β j₀ ⟨x, hx⟩ = (1 : ↥W₂ → ℂ) ⟨x, hx⟩ * α i ⟨y, hy⟩
    rw [hβj₀]
    ring
  have hμ'irr : ∀ i : I,
      (hPC.primeTISign τ (irrSub h1 ⟨α i, hαi i⟩)) • sigmaT h2 h1 hcyc τ (wR w j₀ i)
        ∈ Irr ↥T := by
    intro i
    have heq : (hPC.primeTISign τ (irrSub h1 ⟨α i, hαi i⟩))
          • sigmaT h2 h1 hcyc τ (wR w j₀ i)
        = hPC.primeTIirr τ (principalIrr ↥(W₂.subgroupOf T)) (irrSub h1 ⟨α i, hαi i⟩) := by
      rw [hPC.primeTIirr_principal_left]
      congr 2
      rw [sigmaT_apply, hkey i]
    rw [heq]
    exact hPC.primeTIirr_principal_left_mem_Irr hτ _
  refine ⟨sigmaT h2 h1 hcyc τ,
    fun i => hPC.primeTISign τ (irrSub h1 ⟨α i, hαi i⟩),
    fun i => (hPC.primeTISign τ (irrSub h1 ⟨α i, hαi i⟩)) • sigmaT h2 h1 hcyc τ (wR w j₀ i),
    indBetween (hallCoreIn T ⊔ W₂) T 1,
    fun i => indBetween (hallCoreIn T ⊔ W₂) T 1
      - (hPC.primeTISign τ (irrSub h1 ⟨α i, hαi i⟩)) • sigmaT h2 h1 hcyc τ (wR w j₀ i), ?_⟩
  exact ⟨hT, hcfgT, hL, hLI, hIrr2, hIrr1,
    isProductCharFamily_wR (fun x hx y hy => (hWpair.commute y hy x hx).symm) hprod,
    hσT, isOmegaMap_omegaR hom, fun j i => rfl,
    fun i => hPC.primeTISign_eq_one_or_eq_neg_one _, fun i => rfl, hμ'irr, rfl, fun i => rfl⟩

end Recip

private theorem odd_row_coeff
    (_h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (_h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (_h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (_h₄ : Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₅ : Statements.FPF_type_I_frobenius.{u})
    (_h₆ : Statements.FTS_type_I_dade_support.{u})
    (G : Type u) [Group G] [Fintype G] (_hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (_hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (T V₀ : Subgroup G) (_hT : IsCoatom T) (_hcfgT : IsWitnessedPConfiguration T V₀ W₂ W₁)
    (ν : (↥L → ℂ) → (G → ℂ)) (_hν : IsCoherentDade L ν)
    (φ : ↥L → ℂ) (_hφ : φ ∈ calLFam L) (_hφ1 : φ 1 = (hallCoreIndex L : ℂ))
    (βL : G → ℂ) (_hβL : βL = tauDade L (indBetween (hallCoreIn L) L 1 - φ))
    (_hlt : ((Nat.card ↥V₀ : ℚ) - 1) / (Nat.card ↥W₂ : ℚ)
      < ((Nat.card ↥(hallCoreIn L) : ℚ) - 1) / (hallCoreIndex L : ℚ)) :
    ∀ i : I, i ≠ i₀ → ∃ n : ℤ, cfInnerFin βL (η i j₀) = (n : ℂ) ∧ Odd n := by
  classical
  by_cases hex : ∃ i₁ : I, i₁ ≠ i₀
  · obtain ⟨i₁, hi₁⟩ := hex
    obtain ⟨σT, δ', μ', γ', b', hdataT⟩ :=
      Recip.exists_reciprocal_bridge_data _hG.odd_natCard _hT _hcfgT _hdata.isCoatom_L
        _hdata.isTypeI_L _hdata.isIrrIndexing_W₁ _hdata.isIrrIndexing_W₂
        _hdata.isProductCharFamily _hdata.isOmegaMap
    obtain ⟨-, -, hmain⟩ := FCH_type_I_P_bridge_parity _h₁ _h₂ _h₃ G _hG T L V₀ W₂ W₁ J I
      inferInstance inferInstance β α j₀ i₀ (Recip.wR w) σT (Recip.omegaR ω)
      (fun j i => Recip.omegaR ω (Recip.wR w j i)) δ' μ' γ' b' hdataT
      (Nat.card ↥(hallCoreIn L)) (hallCoreIndex L) (Nat.card ↥W₁) (Nat.card ↥W₂)
      (Nat.card ↥V₀) rfl rfl rfl rfl rfl
    obtain ⟨-, -, -, -, -, -, hthr⟩ := hmain ν _hν φ _hφ _hφ1 βL _hβL i₁ hi₁ _ _ rfl rfl
    intro i hi
    obtain ⟨n, hn, hodd⟩ := (hthr _hlt).1 i hi
    refine ⟨n, ?_, hodd⟩
    rw [_hdata.eta_eq i j₀, ← Recip.omegaR_wR ω w j₀ i]
    exact hn
  · exact fun i hi => absurd ⟨i, hi⟩ hex

theorem FCH_actual_paired_support_saturation
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₄ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₅ : Statements.FPF_type_I_frobenius.{u})
    (h₆ : Statements.FTS_type_I_dade_support.{u}) :
    Statements.FCH_actual_paired_support_saturation.{u} := by
  intro G _ _ hG S L U W₁ W₂ I J _ _ α β i₀ j₀ w σ ω η δ μ γ bfam hdata T V₀ hT hcfgT
    h e p q u v hh he hp hq hu hv ν hν φ hφ hφ1 βL hβL hle hltU hltV
  subst hh he hp hq hu hv
  exact saturation_of_odd_axes h₁ h₂ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata
    ν hν φ hφ hφ1 βL hβL hle
    (odd_row_coeff h₁ h₂ h₃ h₄ h₅ h₆ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata
      T V₀ hT hcfgT ν hν φ hφ hφ1 βL hβL hltV)
    (odd_col_coeff h₁ h₂ h₃ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata
      ν hν φ hφ hφ1 βL hβL hltU)

end CFSG.FeitThompson.Proofs

end

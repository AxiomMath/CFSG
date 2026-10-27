module

public import CFSG.FeitThompson.Representations.TypeIPBridgeOrthogonality
import CFSG.FeitThompson.Representations.BridgeDegreeBoundOrOddAxis
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.NormalInducedFamily
open CFSG.FeitThompson.CrossFamilyProjection (coherentImage coherentImage_apply)
open scoped ComplexConjugate Pointwise

universe u

attribute [local instance] CFSG.FeitThompson.Proofs.subgroupFintype

noncomputable def finEquivOfNe {ι : Type*} [Fintype ι] {p : ℕ}
    (hp : Fintype.card ι = p) {A B : ι} (hAB : A ≠ B) (h2 : 2 ≤ p) :
    {f : Fin p ≃ ι // f ⟨0, by omega⟩ = A ∧ f ⟨1, by omega⟩ = B} := by
  classical
  set h : Fin p ≃ ι := (Fintype.equivFinOfCardEq hp).symm with hh
  set e₁ : Fin p ≃ ι := h.trans (Equiv.swap (h ⟨0, by omega⟩) A) with he₁
  have he₁0 : e₁ ⟨0, by omega⟩ = A := by simp [he₁]
  refine ⟨e₁.trans (Equiv.swap (e₁ ⟨1, by omega⟩) B), ?_, by simp⟩
  have hne : A ≠ e₁ ⟨1, by omega⟩ := by
    rw [← he₁0]
    intro hcon
    exact absurd (e₁.injective hcon) (by simp [Fin.ext_iff])
  simp only [Equiv.trans_apply, he₁0]
  exact Equiv.swap_apply_of_ne_of_ne hne hAB

variable {G : Type*} [Group G]

theorem subgroupOf_hallCoreIn' (L : Subgroup G) :
    (hallCoreIn L).subgroupOf L = hallCore ↥L := by
  rw [hallCoreIn_eq]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem index_hallCore_eq [Finite G] (L : Subgroup G) :
    (hallCore ↥L).index = hallCoreIndex L := by
  rw [hallCoreIndex_eq, Subgroup.relIndex, subgroupOf_hallCoreIn']

theorem natCard_hallCore_eq (L : Subgroup G) :
    Nat.card ↥(hallCore ↥L) = Nat.card ↥(hallCoreIn L) :=
  Nat.card_eq_of_bijective _ (hallCoreEquiv L).bijective

theorem indBetween_one_eq [Fintype G] (L : Subgroup G) :
    indBetween (hallCoreIn L) L (1 : ↥(hallCoreIn L) → ℂ)
      = indClassFun (hallCore ↥L) (1 : ↥(hallCore ↥L) → ℂ) := by
  rw [indBetween_hallCoreIn]; rfl

theorem tauDade_eq_dadeBeta [Fintype G] (L : Subgroup G)
    (hD : IsDadeData L ((hallCoreIn L : Set G) \ {1}) Prep03.sigR) (φ : ↥L → ℂ)
    (hφ : φ ∈ indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}))
    (hφ1 : φ 1 = ((hallCore ↥L).index : ℂ)) :
    tauDade L (indBetween (hallCoreIn L) L 1 - φ)
      = dadeBeta ((hallCoreIn L : Set G) \ {1}) Prep03.sigR (hallCore ↥L) φ := by
  have : (hallCore ↥L).Normal := hallCore_normal
  have hdom : indClassFun (hallCore ↥L) (1 : ↥(hallCore ↥L) → ℂ) - φ
      ∈ CFSG.FeitThompson.dadeDomain L ((hallCoreIn L : Set G) \ {1}) :=
    indClassFun_one_sub_mem_dadeDomain (hallSharp_eq_image L) hφ hφ1
  rw [dadeBeta_eq_dadeMap hD hdom, coe_dadeMap_eq_tauDade, indBetween_one_eq]

theorem finite_calLFam [Finite G] (L : Subgroup G) : (calLFam L).Finite := by
  have : Fintype G := Fintype.ofFinite G
  exact Set.Finite.image _ (Set.Finite.subset (finite_Irr (G := ↥(hallCoreIn L)))
    (fun _ hθ => hθ.1))

theorem isCoherentDade_iff_isCoherentOn [Fintype G] (L : Subgroup G)
    (ν : (↥L → ℂ) → (G → ℂ)) :
    IsCoherentDade L ν ↔
      Prep03.IsCoherentOn (Prep03.hallIndFamily L) (fun f => Prep03.tauHall L f) ν := by
  rw [hallIndFamily_eq_calLFam]
  constructor
  · rintro ⟨hadd, hvc, hiso, hcoh⟩
    refine ⟨⟨hadd, hvc, fun f hf g hg => ?_⟩, fun f hf h1 => ?_⟩
    · rw [← cfInnerFin_eq_cfInner, ← cfInnerFin_eq_cfInner]; exact hiso f hf g hg
    · rw [hcoh f hf h1, tauDade_eq_tauHall]
  · rintro ⟨⟨hadd, hvc, hiso⟩, hcoh⟩
    refine ⟨hadd, hvc, fun f hf g hg => ?_, fun f hf h1 => ?_⟩
    · rw [cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner]; exact hiso f hf g hg
    · rw [hcoh f hf h1, tauDade_eq_tauHall]

section Axis

variable {G : Type u} [Group G] [Fintype G] {S L U W₁ W₂ : Subgroup G} {I J : Type u}
  [Fintype I] [Fintype J]
  {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
  {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
  {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
  {η : I → J → (G → ℂ)} {δ : J → ℂ} {μ : J → (↥S → ℂ)} {γ : ↥S → ℂ}
  {bfam : J → (↥S → ℂ)}

@[expose] def irrOfIndex (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (j : J) :
    Irr ↥W₂ := ⟨β j, by rw [← hdata.isIrrIndexing_W₂.2.1]; exact Set.mem_range_self _⟩

theorem coe_irrOfIndex (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (j : J) :
    ((irrOfIndex hdata j : Irr ↥W₂) : ↥W₂ → ℂ) = β j := rfl

theorem irrOfIndex_injective (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    Function.Injective (irrOfIndex hdata) := fun _ _ hab =>
  hdata.isIrrIndexing_W₂.1 (congrArg Subtype.val hab)

theorem irrOfIndex_j₀ (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    irrOfIndex hdata j₀ = principalIrr ↥W₂ :=
  Subtype.ext (by rw [coe_irrOfIndex, hdata.isIrrIndexing_W₂.2.2, coe_principalIrr])

theorem irrOfIndex_surjective (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    Function.Surjective (irrOfIndex hdata) := by
  intro χ
  have hχ : (χ : ↥W₂ → ℂ) ∈ Set.range β := by rw [hdata.isIrrIndexing_W₂.2.1]; exact χ.2
  obtain ⟨j, hj⟩ := hχ
  exact ⟨j, Subtype.ext hj⟩

theorem eta_eq_prodCharEta (hodd : Odd (Nat.card G))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) (j : J) :
    η i₀ j = (isCyclicTIPair_of_isWitnessedPConfiguration hodd hdata.isPConfig).prodCharEta
      (omegaCF ω hdata.isOmegaMap) (principalIrr ↥W₁) (irrOfIndex hdata j) := by
  set hW := isCyclicTIPair_of_isWitnessedPConfiguration hodd hdata.isPConfig with hWdef
  have hwij : w i₀ j = hW.prodChar (1 : ↥W₁ → ℂ) (β j) := by
    funext z
    have hz2 : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hz2
    have hz : z = ⟨x * y, by rw [hxy]; exact z.2⟩ := Subtype.ext hxy.symm
    rw [hz, hdata.isProductCharFamily i₀ j ⟨x, hx⟩ ⟨y, hy⟩, hW.prodChar_apply_mul,
      hdata.isIrrIndexing_W₁.2.2]
  rw [IsCyclicTIPair.prodCharEta_eq_coe_apply, coe_omegaCF,
    IsCyclicTIPair.coe_basisProdIrr_apply, hdata.eta_eq i₀ j, hwij, coe_principalIrr,
    coe_irrOfIndex]

theorem exists_axis (hodd : Odd (Nat.card G))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    {j₁ : J} (hj₁ : j₁ ≠ j₀) :
    ∃ Θ : ℕ → G → ℂ,
      3 ≤ Nat.card ↥W₂ ∧
      (IsOrthonormalFamily fun i : Fin (Nat.card ↥W₂) => Θ (i : ℕ)) ∧
      (∀ i < Nat.card ↥W₂, Θ i ∈ Submodule.span ℤ (Irr G)) ∧
      Θ 0 = (1 : G → ℂ) ∧
      Θ 1 = η i₀ j₁ ∧
      (Θ 1 ≠ fun x => conj (Θ 1 x)) ∧
      (∃ m, 0 < m ∧ m < Nat.card ↥W₂ ∧ (fun x => conj (Θ 1 x)) = Θ m) ∧
      (∀ i < Nat.card ↥W₂, ∃ j : J, Θ i = η i₀ j ∧ (0 < i → j ≠ j₀)) ∧
      (∀ j : J, j ≠ j₀ → ∃ i, 0 < i ∧ i < Nat.card ↥W₂ ∧ Θ i = η i₀ j) := by
  classical
  set hW := isCyclicTIPair_of_isWitnessedPConfiguration hodd hdata.isPConfig with hWdef
  set ωCF := omegaCF ω hdata.isOmegaMap with hωCF
  have hωiso := isCyclicTIIsometry_omegaCF ω hdata.isOmegaMap
  set p := Nat.card ↥W₂ with hpdef
  have hp3 : 3 ≤ p := hW.three_le_natCard_right
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have hcard : Fintype.card ↑(Irr ↥W₂) = p := by
    rw [← Nat.card_eq_fintype_card, hW.card_Irr_right]
  have hAB : principalIrr ↥W₂ ≠ irrOfIndex hdata j₁ := by
    rw [← irrOfIndex_j₀ hdata]
    exact fun hcon => hj₁ (irrOfIndex_injective hdata hcon).symm
  obtain ⟨f, hf0, hf1⟩ := finEquivOfNe hcard hAB (by omega)
  set Θ : ℕ → G → ℂ := fun i =>
    if hi : i < p then hW.prodCharEta ωCF (principalIrr ↥W₁) (f ⟨i, hi⟩) else 0 with hΘdef
  have hΘval : ∀ (i : ℕ) (hi : i < p),
      Θ i = hW.prodCharEta ωCF (principalIrr ↥W₁) (f ⟨i, hi⟩) := fun i hi => dif_pos hi
  have hfne : ∀ (i : ℕ) (hi : i < p), 0 < i → f ⟨i, hi⟩ ≠ principalIrr ↥W₂ := by
    intro i hi hi0 hcon
    rw [← hf0] at hcon
    exact absurd (f.injective hcon) (by simp [Fin.ext_iff]; omega)
  refine ⟨Θ, hp3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isOrthonormalFamily_iff]
    intro i i'
    rw [hΘval _ i.2, hΘval _ i'.2, hW.cfInner_prodCharEta_col hωiso]
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro hh
      exact Fin.ext (by simpa using congrArg Fin.val (f.injective hh))
    · intro hh
      rw [show (⟨(i : ℕ), i.2⟩ : Fin p) = ⟨(i' : ℕ), i'.2⟩ from
        Fin.ext (by simpa using congrArg Fin.val hh)]
  · intro i hi
    rw [hΘval i hi]
    exact mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hωiso _ _)
  · rw [hΘval 0 (by omega), hf0, hW.prodCharEta_principal hωiso]
  · rw [hΘval 1 (by omega), hf1, eta_eq_prodCharEta hodd hdata j₁]
  · rw [hΘval 1 (by omega), hf1]
    exact Ne.symm (hW.conj_prodCharEta_col_ne hωiso (Ne.symm hAB))
  · obtain ⟨l, hl, hlne, hlnp⟩ := hW.exists_conj_index_right (Ne.symm hAB)
    refine ⟨((f.symm l : Fin p) : ℕ), ?_, (f.symm l).2, ?_⟩
    · rcases Nat.eq_zero_or_pos ((f.symm l : Fin p) : ℕ) with h0 | h0
      · exact absurd (by rw [← hf0, ← show f.symm l = ⟨0, by omega⟩ from Fin.ext h0,
          Equiv.apply_symm_apply]) hlnp
      · exact h0
    · rw [hΘval _ (f.symm l).2, hΘval 1 (by omega), hf1,
        show f ⟨((f.symm l : Fin p) : ℕ), (f.symm l).2⟩ = l from by
          rw [show (⟨((f.symm l : Fin p) : ℕ), (f.symm l).2⟩ : Fin p) = f.symm l from rfl,
            Equiv.apply_symm_apply]]
      exact hW.conj_prodCharEta_col hωiso hl
  · intro i hi
    obtain ⟨j, hj⟩ := irrOfIndex_surjective hdata (f ⟨i, hi⟩)
    refine ⟨j, by rw [hΘval i hi, ← hj, eta_eq_prodCharEta hodd hdata j], fun hi0 hcon => ?_⟩
    refine hfne i hi hi0 ?_
    rw [← hj, hcon, irrOfIndex_j₀ hdata]
  · intro j hj
    refine ⟨((f.symm (irrOfIndex hdata j) : Fin p) : ℕ), ?_, (f.symm _).2, ?_⟩
    · rcases Nat.eq_zero_or_pos ((f.symm (irrOfIndex hdata j) : Fin p) : ℕ) with h0 | h0
      · refine absurd ?_ hj
        refine irrOfIndex_injective hdata ?_
        rw [irrOfIndex_j₀ hdata, ← hf0,
          ← show f.symm (irrOfIndex hdata j) = ⟨0, by omega⟩ from Fin.ext h0,
          Equiv.apply_symm_apply]
      · exact h0
    · rw [hΘval _ (f.symm _).2, eta_eq_prodCharEta hodd hdata j]
      congr 1
      rw [show (⟨((f.symm (irrOfIndex hdata j) : Fin p) : ℕ), (f.symm _).2⟩ : Fin p)
        = f.symm (irrOfIndex hdata j) from rfl, Equiv.apply_symm_apply]

end Axis

theorem bridge_decomposition
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (j₁ : J) (hj₁ : j₁ ≠ j₀) :
    ∃ Γ : G → ℂ,
      Γ ∈ virtualChars G ∧ (∀ x : G, (Γ x).im = 0) ∧ cfInnerFin Γ (1 : G → ℂ) = 0 ∧
      ∀ j : J, j ≠ j₀ →
        indTop S (bfam j) = (1 : G → ℂ) - η i₀ j + Γ ∧
        cfInnerFin (indTop S (bfam j)) (indTop S (bfam j))
          = ((((Nat.card ↥U : ℚ) - 1) / (Nat.card ↥W₁ : ℚ) + 2 : ℚ) : ℂ) := by
  classical
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hconf := isPConfigSetup_of_isPBridgeData hG hdata
  set eI := Fintype.equivFin I with heI
  set eJ := Fintype.equivFin J with heJ
  have hWS : W₁ ⊔ W₂ ≤ S := sup_le_of_isWitnessedPConfiguration hdata.isPConfig
  have hcoreS : hallCoreIn S ⊔ W₁ ≤ S :=
    sup_le (Subgroup.map_subtype_le _) (le_trans le_sup_left hWS)
  have hirr₁ := hdata.isIrrIndexing_W₁
  have hirr₂ := hdata.isIrrIndexing_W₂
  have key := h₃ G hamb S U W₁ W₂ hconf (Nat.card ↥U) (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl rfl
    (Fin (Fintype.card I)) (Fin (Fintype.card J)) inferInstance inferInstance
    (eI i₀) (eJ j₀) (fun i => α (eI.symm i)) (fun j => β (eJ.symm j))
    (fun i => by rw [← hirr₁.2.1]; exact Set.mem_range_self _)
    (fun j => by rw [← hirr₂.2.1]; exact Set.mem_range_self _)
    (fun a b hab => by
      have := hirr₁.1 hab
      simpa using this)
    (fun a b hab => by
      have := hirr₂.1 hab
      simpa using this)
    (fun χ hχ => by
      rw [← hirr₁.2.1] at hχ
      obtain ⟨i, hi⟩ := hχ
      exact ⟨eI i, by simpa using hi⟩)
    (fun χ hχ => by
      rw [← hirr₂.2.1] at hχ
      obtain ⟨jj, hjj⟩ := hχ
      exact ⟨eJ jj, by simpa using hjj⟩)
    (by simpa using hirr₁.2.2) (by simpa using hirr₂.2.2)
    (fun i jj => w (eI.symm i) (eJ.symm jj))
    (fun i jj x y z hz => by
      have hprod := hdata.isProductCharFamily (eI.symm i) (eJ.symm jj) x y (hz ▸ z.2)
      rw [← hprod]
      congr 1
      exact Subtype.ext hz)
    (⇑σ) (⇑ω) (isTIExtension_sigma hWS hdata.isSigmaMap) (isTIExtension_omega hdata.isOmegaMap)
    (fun jj => δ (eJ.symm jj)) (fun jj => μ (eJ.symm jj))
    (fun i jj => η (eI.symm i) (eJ.symm jj))
    (fun jj => hdata.delta_sign _) (fun jj => by simpa using hdata.mu_eq (eJ.symm jj))
    (fun jj => hdata.mu_irr _) (fun i jj => hdata.eta_eq _ _)
    (fun _ => γ) (fun jj => bfam (eJ.symm jj))
    (fun jj => by
      rw [hdata.gamma_eq, indBetween_eq_indClassFun_subgroupOf hcoreS]
      rfl)
    (fun jj => by simpa using hdata.b_eq (eJ.symm jj))
  obtain ⟨-, -, hrest⟩ := key
  have hj₁ne : eJ j₁ ≠ eJ j₀ := fun hcon => hj₁ (eJ.injective hcon)
  have hΓeq : (indTop S (bfam j₁) - 1 + η i₀ j₁)
      = Prep03.indG S (bfam (eJ.symm (eJ j₁))) - 1 + η (eI.symm (eI i₀)) (eJ.symm (eJ j₁)) := by
    simp [indTop_eq_indG]
  obtain ⟨hΓv, hΓreal, hΓ1, hlast⟩ := hrest (eJ j₁) hj₁ne _ hΓeq
  refine ⟨indTop S (bfam j₁) - 1 + η i₀ j₁, hΓv,
    fun x => Complex.conj_eq_iff_im.1 (hΓreal x), by rw [cfInnerFin_eq_cfInner]; exact hΓ1, ?_⟩
  intro j hj
  have hjne : eJ j ≠ eJ j₀ := fun hcon => hj (eJ.injective hcon)
  obtain ⟨hdec, hnorm, -⟩ := hlast (eJ j) hjne
  have hbj : bfam (eJ.symm (eJ j)) = bfam j := by simp
  have hηj : η (eI.symm (eI i₀)) (eJ.symm (eJ j)) = η i₀ j := by simp
  refine ⟨?_, ?_⟩
  · funext x
    have hx := hdec x
    rw [hbj, hηj] at hx
    simpa [indTop_eq_indG] using hx
  · rw [cfInnerFin_eq_cfInner, indTop_eq_indG]
    rw [hbj] at hnorm
    exact hnorm

theorem FCH_type_I_P_bridge_parity
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u}) :
    Statements.FCH_type_I_P_bridge_parity.{u} := by
  classical
  intro G _ _ hG S L U W₁ W₂ I J _ _ α β i₀ j₀ w σ ω η δ μ γ bfam hdata h e p q u hh he hp hq hu
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, hh1, he1, hhe0, hD₀, -, -, -, hIrrFam, -, hncard, hexν, hexφ⟩ :=
    h₂ G hamb L hdata.isCoatom_L hdata.isTypeI_L
  have hD : IsDadeData L ((hallCoreIn L : Set G) \ {1}) Prep03.sigR := hD₀
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hexν
    exact ⟨ν, (isCoherentDade_iff_isCoherentOn L ν).2 hν⟩
  · obtain ⟨φ, hφ, hφ1⟩ := hexφ
    exact ⟨φ, by rw [← hallIndFamily_eq_calLFam]; exact hφ,
      by rw [he, hallCoreIndex_eq]; exact hφ1⟩
  intro ν hν φ hφ hφ1 βL hβL j₁ hj₁ c b hc hb
  have hoddG := hG.odd_natCard
  have hHnorm : (hallCore ↥L).Normal := hallCore_normal
  have hcardH : Nat.card ↥(hallCore ↥L) = h := by rw [natCard_hallCore_eq, hh]
  have hidxH : (hallCore ↥L).index = e := by rw [index_hallCore_eq, he]
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
  have hζ1 : ζ k₀ 1 = ((hallCore ↥L).index : ℂ) := by
    rw [hζk₀, hφ1, hidxH]
  have hfin := finite_calLFam L
  have hκfin : Finite κ := hfin.to_subtype
  have hS2 : (Set.range ζ).Nontrivial := by
    rw [hrange]
    have hfc : Finite ↑(calLFam L) := hfin.to_subtype
    refine Set.one_lt_ncard_iff_nontrivial.1 ?_
    have : 2 ≤ (calLFam L).ncard := by rw [← hallIndFamily_eq_calLFam]; exact hncard
    omega
  have hhe : 2 * (hallCore ↥L).index + 1 ≤ Nat.card ↥(hallCore ↥L) := by
    have hh1' : 1 < Nat.card ↥(hallCoreIn L) := hh1
    have he1' : 1 < (hallCoreIn L).relIndex L := he1
    have hhe0' : 2 * (hallCoreIn L).relIndex L ≤ Nat.card ↥(hallCoreIn L) - 1 := hhe0
    rw [← hallCoreIndex_eq, ← he] at he1' hhe0'
    rw [← hh] at hh1' hhe0'
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
  have hle : charSpanZero (Set.range ζ) ≤ Submodule.span ℤ (Set.range ζ) := fun f hf =>
    (mem_charSpanZero.1 hf).1
  set τ : ↥(charSpanZero (Set.range ζ)) →+ ↥(virtualChars G) :=
    ν'.comp (Submodule.inclusion hle).toAddMonoidHom with hτdef
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
    have h1 : (f : ↥L → ℂ) ∈ Submodule.span ℤ (calLFam L) := by
      rw [← hspan]; exact (mem_charSpanZero.1 f.2).1
    exact hcoh _ h1 (mem_charSpanZero.1 f.2).2
  have himg : ∀ k : κ, coherentImage ζ ν' k = ν (ζ k) := fun k => by
    rw [coherentImage_apply]; rfl
  have horth : ∀ ξ ∈ calLFam L, ∀ (i : I) (j : J), cfInnerFin (ν ξ) (η i j) = 0 :=
    cfInner_nu_eta_eq_zero h₁ h₂ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata ν
      ⟨hadd, hvc, hiso, hcoh⟩
  have hbridge0 := cfInner_indTop_tauDade_eq_zero h₁ h₃ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ
    μ γ bfam hdata
  obtain ⟨Θ, hp3, hΘorth, hΘmem, hΘ0, hΘ1, hΘnr, hconj, hΘj, hjΘ⟩ :=
    exists_axis hoddG hdata hj₁
  obtain ⟨Γ, hΓv, hΓreal, hΓ1, hdec⟩ := bridge_decomposition h₃ G hG S L U W₁ W₂ I J α β i₀ j₀ w
    σ ω η δ μ γ bfam hdata j₁ hj₁
  have hB1 : (1 : G → ℂ) - Θ 1 + Γ = indTop S (bfam j₁) := by
    rw [hΘ1, (hdec j₁ hj₁).1]
  set r : ℝ := ((u : ℝ) - 1) / (q : ℝ) with hrdef
  have hBnorm : cfInner ((1 : G → ℂ) - Θ 1 + Γ) ((1 : G → ℂ) - Θ 1 + Γ) = (r : ℂ) + 2 := by
    rw [hB1, ← cfInnerFin_eq_cfInner, (hdec j₁ hj₁).2, hrdef, hu, hq]
    push_cast
    ring
  have hbridge : ∀ F : ↥(CFSG.FeitThompson.dadeDomain L
        ((hallCoreIn L : Set G) \ {1})), ∀ i, 0 < i → i < Nat.card ↥W₂ →
      cfInner ((1 : G → ℂ) - Θ i + Γ) ((dadeMap hD F : ↥(classFun G)) : G → ℂ) = 0 := by
    intro F i hi0 hip
    obtain ⟨j, hΘij, hjne⟩ := hΘj i hip
    have hcf : IsClassFun (F : ↥L → ℂ) := by
      have hmc := (mem_dadeDomain.1 F.2).1
      rw [mem_classFun] at hmc
      rw [isClassFun_iff]
      intro x g
      exact hmc _ _ (isConj_iff.2 ⟨x⁻¹, by group⟩)
    rw [hΘij, coe_dadeMap_eq_tauDade, ← cfInnerFin_eq_cfInner, ← (hdec j (hjne hi0)).1]
    exact hbridge0 j (hjne hi0) (F : ↥L → ℂ) hcf (mem_dadeDomain.1 F.2).2
  have hνΘ : ∀ k : κ, ∀ i < Nat.card ↥W₂, cfInner (coherentImage ζ ν' k) (Θ i) = 0 := by
    intro k i hi
    obtain ⟨j, hΘij, -⟩ := hΘj i hi
    rw [himg k, hΘij, ← cfInnerFin_eq_cfInner]
    exact horth (ζ k) (by rw [← hrange]; exact Set.mem_range_self k) i₀ j
  obtain ⟨bZ, cZ, hcZ, hbZ, hrow, hxor, halt⟩ :=
    DadeBridgeParity.bridge_parity_alternative (Θ := Θ) (Γ := Γ) (r := r) (k₀ := k₀)
      (p := Nat.card ↥W₂) hoddG hD (hallSharp_eq_image L) hSrange hζinj hcoher hτeq hIrr hζ1
      hS2 hhe hp3 hΘorth hΘmem hΘ0 hΘnr hconj hνΘ
      (mem_span_Irr_of_mem_virtualChars hΓv) hΓreal (by rw [← cfInnerFin_eq_cfInner]; exact hΓ1)
      hBnorm hbridge
  have hcc : c = (cZ : ℂ) := by
    rw [hc, cfInnerFin_eq_cfInner, ← hcZ, hB1, himg k₀, hζk₀]
  have hbb : b = (bZ : ℂ) := by
    rw [hb, cfInnerFin_eq_cfInner, ← hbZ, hβLeq, hΘ1]
  refine ⟨⟨cZ, hcc⟩, ⟨bZ, hbb⟩, horth, ?_, ?_, ?_, ?_⟩
  ·
    intro j hj
    obtain ⟨i, hi0, hip, hΘi⟩ := hjΘ j hj
    rw [hbb, cfInnerFin_eq_cfInner, hβLeq, ← hΘi]
    exact hrow i hi0 hip
  ·
    intro m n hm hn
    have hmc : m = cZ := by
      have : ((m : ℂ)) = ((cZ : ℂ)) := by rw [← hm, hcc]
      exact_mod_cast this
    have hnb : n = bZ := by
      have : ((n : ℂ)) = ((bZ : ℂ)) := by rw [← hn, hbb]
      exact_mod_cast this
    subst hmc hnb
    unfold Xor at hxor
    tauto
  ·
    rw [hcardH, hidxH] at halt
    rcases halt with ⟨hcodd, hlee⟩ | ⟨hbodd, hple⟩
    · refine Or.inl ⟨⟨cZ, hcc, hcodd⟩, ?_⟩
      have hR : ((((h : ℚ) - 1) / (e : ℚ) : ℚ) : ℝ) ≤ ((((u : ℚ) - 1) / (q : ℚ) : ℚ) : ℝ) := by
        push_cast
        rw [hrdef] at hlee
        exact hlee
      exact_mod_cast hR
    · exact Or.inr ⟨⟨bZ, hbb, hbodd⟩, by rw [hp]; exact hple⟩
  ·
    intro hlt
    have hrlt : r < ((Nat.card ↥(hallCore ↥L) : ℝ) - 1) / ((hallCore ↥L).index : ℝ) := by
      rw [hcardH, hidxH, hrdef]
      have hR : ((((u : ℚ) - 1) / (q : ℚ) : ℚ) : ℝ) < ((((h : ℚ) - 1) / (e : ℚ) : ℚ) : ℝ) := by
        exact_mod_cast hlt
      push_cast at hR
      exact hR
    obtain ⟨hoddrow, hple⟩ :=
      DadeBridgeParity.odd_row_and_le_index_of_lt (Θ := Θ) (Γ := Γ) (r := r) (k₀ := k₀)
        (p := Nat.card ↥W₂) hoddG hD (hallSharp_eq_image L) hSrange hζinj hcoher hτeq hIrr hζ1
        hS2 hhe hp3 hΘorth hΘmem hΘ0 hΘnr hconj hνΘ
        (mem_span_Irr_of_mem_virtualChars hΓv) hΓreal
        (by rw [← cfInnerFin_eq_cfInner]; exact hΓ1) hBnorm hbridge hrlt
    refine ⟨fun j hj => ?_, by rw [hp, ← hidxH]; exact hple⟩
    obtain ⟨i, hi0, hip, hΘi⟩ := hjΘ j hj
    obtain ⟨n, hnodd, hn⟩ := hoddrow i hi0 hip
    exact ⟨n, by rw [cfInnerFin_eq_cfInner, hβLeq, ← hΘi]; exact hn, hnodd⟩

end CFSG.FeitThompson.Proofs

end

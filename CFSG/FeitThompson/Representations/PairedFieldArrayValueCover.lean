module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.OrderedFieldPairOrderEstimates
import CFSG.FeitThompson.Local.FieldPConfigurationPrimeSupport
public import CFSG.FeitThompson.Representations.TypeIPBridgeOrthogonality
public import CFSG.FeitThompson.Representations.SignedCyclicTIArrayCoprimeNonvanishing

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open CFSG.FeitThompson
open _root_.CFSG.FeitThompson.Proofs
open scoped Pointwise

attribute [local instance] _root_.CFSG.FeitThompson.Proofs.subgroupFintype

variable {G : Type*} [Group G]

@[expose] def irrOfIrrIndexing {X : Subgroup G} {I : Type*} {α : I → (↥X → ℂ)} {i₀ : I}
    (hα : IsIrrIndexing X α i₀) (i : I) : Irr ↥X :=
  ⟨α i, by rw [← hα.2.1]; exact Set.mem_range_self _⟩

theorem coe_irrOfIrrIndexing {X : Subgroup G} {I : Type*} {α : I → (↥X → ℂ)} {i₀ : I}
    (hα : IsIrrIndexing X α i₀) (i : I) :
    ((irrOfIrrIndexing hα i : Irr ↥X) : ↥X → ℂ) = α i := rfl

@[expose] noncomputable def equivIrrOfIrrIndexing {X : Subgroup G} {I : Type*}
    {α : I → (↥X → ℂ)} {i₀ : I} (hα : IsIrrIndexing X α i₀) : I ≃ Irr ↥X :=
  Equiv.ofBijective (irrOfIrrIndexing hα)
    ⟨fun _ _ h => hα.1 (congrArg Subtype.val h), fun χ => by
      obtain ⟨i, hi⟩ : (χ : ↥X → ℂ) ∈ Set.range α := by rw [hα.2.1]; exact χ.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem equivIrrOfIrrIndexing_apply {X : Subgroup G} {I : Type*}
    {α : I → (↥X → ℂ)} {i₀ : I} (hα : IsIrrIndexing X α i₀) (i : I) :
    equivIrrOfIrrIndexing hα i = irrOfIrrIndexing hα i := rfl

theorem eta_eq_prodCharEta_of_isWitnessedPConfiguration
    [Fintype G] {S U W₁ W₂ : Subgroup G} {I J : Type*}
    {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    {η : I → J → (G → ℂ)}
    (hodd : Odd (Nat.card G)) (hc : IsWitnessedPConfiguration S U W₁ W₂)
    (hα : IsIrrIndexing W₁ α i₀) (hβ : IsIrrIndexing W₂ β j₀)
    (hw : IsProductCharFamily W₁ W₂ α β w) (hω : IsOmegaMap W₁ W₂ ω)
    (hη : ∀ i j, η i j = ω (w i j)) (i : I) (j : J) :
    η i j = (isCyclicTIPair_of_isWitnessedPConfiguration hodd hc).prodCharEta
      (omegaCF ω hω) (irrOfIrrIndexing hα i) (irrOfIrrIndexing hβ j) := by
  set hW := isCyclicTIPair_of_isWitnessedPConfiguration hodd hc with hWdef
  have hwij : w i j = hW.prodChar (α i) (β j) := by
    funext z
    have hz2 : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hz2
    have hz : z = ⟨x * y, by rw [hxy]; exact z.2⟩ := Subtype.ext hxy.symm
    rw [hz, hw i j ⟨x, hx⟩ ⟨y, hy⟩, hW.prodChar_apply_mul]
  rw [IsCyclicTIPair.prodCharEta_eq_coe_apply, coe_omegaCF,
    IsCyclicTIPair.coe_basisProdIrr_apply, hη i j, hwij, coe_irrOfIrrIndexing,
    coe_irrOfIrrIndexing]

theorem sum_eq_signedProdCharEtaSum [Fintype G] {S U W₁ W₂ : Subgroup G} {I J : Type*}
    [Fintype I] [Fintype J]
    {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    {η : I → J → (G → ℂ)}
    (hodd : Odd (Nat.card G)) (hc : IsWitnessedPConfiguration S U W₁ W₂)
    (hα : IsIrrIndexing W₁ α i₀) (hβ : IsIrrIndexing W₂ β j₀)
    (hw : IsProductCharFamily W₁ W₂ α β w) (hω : IsOmegaMap W₁ W₂ ω)
    (hη : ∀ i j, η i j = ω (w i j)) (ε : I → J → ℂ) (g : G) :
    ∑ i : I, ∑ j : J, ε i j * η i j g
      = (isCyclicTIPair_of_isWitnessedPConfiguration hodd hc).signedProdCharEtaSum
          (omegaCF ω hω)
          (fun pr => ε ((equivIrrOfIrrIndexing hα).symm pr.1)
            ((equivIrrOfIrrIndexing hβ).symm pr.2)) g := by
  have hW := isCyclicTIPair_of_isWitnessedPConfiguration hodd hc
  have hfl := hW.finite_left
  have hfr := hW.finite_right
  have : Fintype (Irr ↥W₁ × Irr ↥W₂) := Fintype.ofFinite _
  have h1 : ∑ i : I, ∑ j : J, ε i j * η i j g
      = ∑ pr : I × J, ε pr.1 pr.2 * η pr.1 pr.2 g := by rw [Fintype.sum_prod_type]
  have h2 : ∑ pr : I × J, ε pr.1 pr.2 * η pr.1 pr.2 g
      = ∑ pr : Irr ↥W₁ × Irr ↥W₂,
          ε ((equivIrrOfIrrIndexing hα).symm pr.1) ((equivIrrOfIrrIndexing hβ).symm pr.2) *
            (isCyclicTIPair_of_isWitnessedPConfiguration hodd hc).prodCharEta
              (omegaCF ω hω) pr.1 pr.2 g := by
    refine Fintype.sum_equiv
      (Equiv.prodCongr (equivIrrOfIrrIndexing hα) (equivIrrOfIrrIndexing hβ)) _ _ (fun pr => ?_)
    obtain ⟨i, j⟩ := pr
    simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply]
    rw [eta_eq_prodCharEta_of_isWitnessedPConfiguration hodd hc hα hβ hw hω hη i j]
    rfl
  rw [IsCyclicTIPair.signedProdCharEtaSum_apply]
  exact h1.trans h2

theorem satSet_subset_satSet {A B : Set G} (h : A ⊆ B) : satSet A ⊆ satSet B := by
  intro x hx
  obtain ⟨g, y, hy, rfl⟩ := mem_satSet_iff.1 hx
  exact mem_satSet_iff.2 ⟨g, ⟨y, h hy, rfl⟩⟩

theorem satSet_union (A B : Set G) : satSet (A ∪ B) = satSet A ∪ satSet B := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨g, y, hy, rfl⟩ := mem_satSet_iff.1 hx
    rcases hy with hy | hy
    · exact Or.inl (mem_satSet_iff.2 ⟨g, ⟨y, hy, rfl⟩⟩)
    · exact Or.inr (mem_satSet_iff.2 ⟨g, ⟨y, hy, rfl⟩⟩)
  · exact Set.union_subset (satSet_subset_satSet Set.subset_union_left)
      (satSet_subset_satSet Set.subset_union_right)

theorem sharp_subset_sharp {X Y : Subgroup G} (h : X ≤ Y) :
    CFSG.FeitThompson.sharp X ⊆ CFSG.FeitThompson.sharp Y :=
  fun _ hx => ⟨h hx.1, hx.2⟩

theorem sharp_sup_subset (W₁ W₂ : Subgroup G) :
    CFSG.FeitThompson.sharp (W₁ ⊔ W₂) ⊆
      CFSG.FeitThompson.sharp W₁ ∪ CFSG.FeitThompson.sharp W₂ ∪ cyclicTIset W₁ W₂ := by
  rintro x ⟨hxW, hx1⟩
  by_cases h1 : x ∈ W₁
  · exact Or.inl (Or.inl ⟨h1, hx1⟩)
  by_cases h2 : x ∈ W₂
  · exact Or.inl (Or.inr ⟨h2, hx1⟩)
  · exact Or.inr (mem_cyclicTIset.2 ⟨hxW, h1, h2⟩)

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson CFSG.FeitThompson
open scoped Pointwise

universe u

attribute [local instance] CFSG.FeitThompson.Proofs.subgroupFintype

theorem FBG_paired_field_array_value_cover
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FBG_paired_field_array_value_cover.{u} := by
  intro G _ _ hG S T U V W₁ W₂ hS hT hST hcS hcT P Q hP hQ p q u v hp hq _hu _hv
    hpp hqp hpo hqo hlt hEA hirr I J _ _ α β i₀ j₀ hα hβ w hw ω hω η hη E hE D f _hf ε hε hfD g hg
  have hFBG : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsetup : IsOppositeSupportingSetup S T U V W₁ W₂ p q :=
    { isCoatom_S := hS, isCoatom_T := hT, ne := hST, pconfig_S := hcS, pconfig_T := hcT
      natCard_W₂ := hp.symm, natCard_W₁ := hq.symm, prime_p := hpp, prime_q := hqp
      odd_p := hpo, odd_q := hqo, lt := hlt
      irreducible := by rw [← hP]; exact ⟨hEA, hirr⟩ }
  have hirrT : IsIrreducibleConjAction V (hallCoreIn T) q :=
    (FBG_ordered_field_pair_order_estimates.{u} h₁ h₂ G hFBG S T U V W₁ W₂ p q hsetup).1
  have hdet := FBG_field_p_configuration_prime_support.{u} h₁ h₂ G hFBG
  have hW₂P : W₂ ≤ P := by rw [hP]; exact hcS.le_hallCore_W₂
  have hW₁Q : W₁ ≤ Q := by rw [hQ]; exact hcT.le_hallCore_W₂
  rw [Set.mem_union, not_or] at hg
  obtain ⟨hgD, hgE⟩ := hg
  rw [hE, Set.mem_union, not_or, Set.mem_union, not_or] at hgE
  obtain ⟨⟨hgP, hgQ⟩, hgV⟩ := hgE
  have hgW : g ∉ CFSG.FeitThompson.sat (CFSG.FeitThompson.sharp (W₁ ⊔ W₂)) := by
    intro hc
    have h3 := satSet_subset_satSet (sharp_sup_subset W₁ W₂) hc
    rw [satSet_union, satSet_union] at h3
    rcases h3 with (h4 | h4) | h4
    · exact hgQ (satSet_subset_satSet (sharp_subset_sharp hW₁Q) h4)
    · exact hgP (satSet_subset_satSet (sharp_subset_sharp hW₂P) h4)
    · exact hgV h4
  have hcopP : Nat.Coprime (orderOf g) p :=
    hdet S U W₁ W₂ p hS hcS hp.symm hpp (by rw [← hP]; exact ⟨hEA, hirr⟩) g
      (by rw [hP] at hgP; exact hgP) hgW
  have hcopQ : Nat.Coprime (orderOf g) q :=
    hdet T V W₂ W₁ q hT hcT hq.symm hqp hirrT g (by rw [hQ] at hgQ; exact hgQ)
      (by rw [sup_comm]; exact hgW)
  have hW := isCyclicTIPair_of_isWitnessedPConfiguration hG.odd_natCard hcS
  have hcopW : (orderOf g).Coprime (Nat.card ↥(W₁ ⊔ W₂)) := by
    rw [hW.natCard_eq_mul, ← hq, ← hp]
    exact Nat.Coprime.mul_right hcopQ hcopP
  have hεpsign : ∀ pr : Irr ↥W₁ × Irr ↥W₂,
      ε ((equivIrrOfIrrIndexing hα).symm pr.1) ((equivIrrOfIrrIndexing hβ).symm pr.2) = 1 ∨
      ε ((equivIrrOfIrrIndexing hα).symm pr.1) ((equivIrrOfIrrIndexing hβ).symm pr.2) = -1 :=
    fun _ => hε _ _
  have hkey := hW.one_le_sq_norm_signedProdCharEtaSum_apply
    (isCyclicTIIsometry_omegaCF ω hω) hεpsign hcopW
  rw [hfD g hgD, sum_eq_signedProdCharEtaSum hG.odd_natCard hcS hα hβ hw hω hη ε g]
  exact hkey

end

end CFSG.FeitThompson.Proofs

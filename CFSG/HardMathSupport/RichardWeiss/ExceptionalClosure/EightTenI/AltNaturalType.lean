module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.Helpers
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.KerTheta
public import CFSG.HardMathSupport.Cooperstein.Proving.BlockVNormal
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalSectionLS
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.PerfectCommutator

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV barM)
open CFSG.Open (pCoreOf)
open CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein
open CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isAltNaturalType_of_natural_section_core
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {N : ℕ} (hN : 5 ≤ N)
    (hcz : (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) = pCoreOf 2 (L ⊔ S))
    (hsec : AlternatingGeometry.NaturalSectionLSL S L N)
    (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) (hshort : IsShort2 L) :
    IsAltNaturalType L N := by
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : CFSG.AGLEmbedding.IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  have hcore : L ⊓ pCoreOf 2 (L ⊔ S) = pCoreOf 2 L := hLs.inf_twoCore
  obtain ⟨π, θ, hπ, hker, hAθ, hequiv, hθker⟩ := hsec
  have hperf : ⁅L, L⁆ = L := hL.perfect
  let θL : ↥L →* Equiv.Perm (Fin N) := θ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ S))
  have hθalt : ∀ l : ↥L, θL l ∈ alternatingGroup (Fin N) :=
    AltSocle.perm_mem_alternatingGroup_of_perfect hperf θL
  let α : ↥L →* alternatingGroup (Fin N) := θL.codRestrict _ hθalt
  have hαθ : ∀ l : ↥L, (α l : Equiv.Perm (Fin N)) =
      θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ := fun l => rfl
  have hαsurj : Function.Surjective α := by
    intro σ
    obtain ⟨l, hl⟩ := hAθ σ.1 σ.2
    exact ⟨l, Subtype.ext hl⟩
  have hUV' : ⁅blockV S L, L⁆ ≤ blockV S L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (le_sup_left.trans (CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L))
  have hkerθ : ∀ g : ↥(L ⊔ S), θ g = 1 ↔ (g : G) ∈ pCoreOf 2 (L ⊔ S) := by
    intro g
    rw [AlternatingGeometry.theta_eq_one_iff hN hπ hequiv hUV' hθker g, ← hcz]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = 1 := by
        rw [← hαθ, h]; rfl
      have h2 := (hkerθ _).mp h1
      have h3 : (l : G) ∈ pCoreOf 2 L := hcore ▸ ⟨l.2, h2⟩
      obtain ⟨y, hy, hyl⟩ := exists_mem_pCore_of_mem_pCoreOf h3
      have : y = l := Subtype.ext hyl
      exact this ▸ hy
    · intro h
      have h3 : (l : G) ∈ pCoreOf 2 L := mem_pCoreOf_of_mem_pCore h
      have h2 : (l : G) ∈ pCoreOf 2 (L ⊔ S) := (hcore ▸ h3 : (l : G) ∈ L ⊓ pCoreOf 2 (L ⊔ S)).2
      have h1 := (hkerθ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩).mpr h2
      exact Subtype.ext (by rw [hαθ, h1]; rfl)
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := hcore.symm.le.trans inf_le_right
  have hUV : blockU L ≤ blockV S L := by
    have h1 : blockU L ≤ ⁅pCoreOf 2 (L ⊔ S), L⁆ :=
      Subgroup.commutator_mono hQL le_rfl
    exact h1.trans hQV
  have hUU : blockU L ≤ ⁅blockV S L, L⁆ := by
    have h1 := hUV
    calc blockU L = ⁅blockU L, L⁆ := (AGLEmbeddingD2.McLaughlin.OrdinaryProofs.commutator_blockU_eq
          hperf).symm
      _ ≤ ⁅blockV S L, L⁆ := Subgroup.commutator_mono hUV le_rfl
  let ι₀ : ↥(blockU L) →* ↥⁅blockV S L, L⁆ := Subgroup.inclusion hUU
  let β : ↥(blockU L) →* Multiplicative (altHeart N) := π.comp ι₀
  have hβker : β.ker = (blockZ L).subgroupOf (blockU L) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have : β u = 1 ↔ ι₀ u ∈ π.ker := by rw [MonoidHom.mem_ker]; rfl
    rw [this, hker, Subgroup.mem_subgroupOf]
    constructor
    · intro h; exact ⟨u.2, h.2⟩
    · intro h; exact ⟨hUU u.2, h.2⟩
  have hβeq : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ → ∀ x : evenWeight N,
      Multiplicative.toAdd (β u) = (x : altHeart N) →
      Multiplicative.toAdd (β v) =
        (evenWeightPerm (α ℓ : Equiv.Perm (Fin N)) x : altHeart N) := by
    intro ℓ u v huv x hx
    rw [hαθ]
    exact hequiv ⟨(ℓ : G), (le_sup_left : L ≤ L ⊔ S) ℓ.2⟩ (ι₀ u) (ι₀ v) huv x hx
  have hβsurj : Function.Surjective β := by
    let W : AddSubgroup (altHeart N) := (MonoidHom.toAdditive β).range
    have hW : ∀ a : altHeart N, a ∈ W ↔ ∃ u : ↥(blockU L), Multiplicative.toAdd (β u) = a := by
      intro a
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨Additive.toMul u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨Additive.ofMul u, hu⟩
    have hLU : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := fun ℓ hℓ =>
      CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_commutator
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L hℓ)
        (Subgroup.le_normalizer hℓ)
    have hinv : ∀ σ ∈ alternatingGroup (Fin N), ∀ x : evenWeight N,
        (QuotientAddGroup.mk x : altHeart N) ∈ W →
          (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart N) ∈ W := by
      intro σ hσ x hx
      obtain ⟨u, hu⟩ := (hW _).mp hx
      obtain ⟨ℓ, hℓ⟩ := hαsurj ⟨σ, hσ⟩
      have hv : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (hLU ℓ.2) (u : G)).mp u.2
      have h1 := hβeq ℓ u ⟨_, hv⟩ rfl x hu
      refine (hW _).mpr ⟨⟨_, hv⟩, ?_⟩
      rw [h1, hℓ]
    rcases AlternatingGeometry.altHeart_irreducible (by omega) W hinv with hbot | htop
    · exfalso
      have hle : blockU L ≤ blockZ L := by
        intro g hg
        have h1 : β ⟨g, hg⟩ = 1 := by
          have : Multiplicative.toAdd (β ⟨g, hg⟩) ∈ W := (hW _).mpr ⟨⟨g, hg⟩, rfl⟩
          rw [hbot, AddSubgroup.mem_bot] at this
          exact Multiplicative.toAdd.injective this
        have h2 : (⟨g, hg⟩ : ↥(blockU L)) ∈ β.ker := h1
        rw [hβker, Subgroup.mem_subgroupOf] at h2
        exact h2
      exact (hshort.2.2.2.2.1).not_ge hle
    · intro b
      have : Multiplicative.toAdd b ∈ W := by rw [htop]; trivial
      obtain ⟨u, hu⟩ := (hW _).mp this
      exact ⟨u, Multiplicative.toAdd.injective hu⟩
  exact ⟨α, hαsurj, hαker, β, hβsurj, hβker, hβeq⟩

theorem isAltNaturalType_of_natural_section
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {N : ℕ} (hN : 9 ≤ N)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin N))
    (hsec : AlternatingGeometry.NaturalSectionLSL S L N)
    (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) (hshort : IsShort2 L) :
    IsAltNaturalType L N :=
  isAltNaturalType_of_natural_section_core hX hA hL (by omega)
    (Coordinator.inf_centralizer_blockV_eq_pCoreOf hX hA hL (by omega) e) hsec hQV hshort

theorem isAltNaturalType_of_natural_section_of_center_bot
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {N : ℕ} (hN : 5 ≤ N)
    (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥)
    (hsec : AlternatingGeometry.NaturalSectionLSL S L N)
    (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) (hshort : IsShort2 L) :
    IsAltNaturalType L N := by
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : CFSG.AGLEmbedding.IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  refine isAltNaturalType_of_natural_section_core hX hA hL hN ?_ hsec hQV hshort
  refine le_antisymm (AlternatingGeometry.inf_centralizer_blockV_le_pCoreOf hA' hLs hSL
    (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ) ?_
  exact le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (L ⊔ S))
    (fun x hx => CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end

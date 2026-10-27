module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Center582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Orbit58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46W
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFrattini
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Central
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_omegaOne {H : Subgroup G} {g w : G} (hHg : conjugate H g ≤ H)
    (hw : w ∈ omegaOne H) : g⁻¹ * w * g ∈ omegaOne H := by
  have h1 : g⁻¹ * w * g ∈ (omegaOne H).map (MulAut.conj g⁻¹).toMonoidHom :=
    ⟨w, hw, by simp⟩
  rw [omegaOne, MonoidHom.map_closure] at h1
  refine (closure_le _).mpr ?_ h1
  rintro _ ⟨h, ⟨hh, hh2⟩, rfl⟩
  refine subset_closure ⟨hHg ⟨h, hh, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [show g⁻¹ * h * g * (g⁻¹ * h * g) = g⁻¹ * (h * h) * g by group, hh2]
  group

theorem exists_unbalancing_commutator_sylow
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput)
    (hElem : L34ElementaryCenterSylowFact) (hNE : L34NonelementaryCenterCommutatorFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (hZ : S ⊓ coreActionKernel L ⊓ L ≠ ⊥) :
    ∃ u ∈ L34UnbalancingSet L t S, (∃ w ∈ omegaOne (S ⊓ coreActionKernel L), w ≠ 1 ∧
      w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆) ∧
      IsSylowTwoIn (S ⊓ centralizer ({u} : Set G))
        (centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, w, hwΩ, hw1, hwc⟩ :=
    exists_unbalancing_commutator hS hU hheld hSol hGW hElem hNE hset hZ
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, -, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hSC : S ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hZS s hs)
  have hSt : IsSylowTwoIn S (centralizer ({t} : Set G)) := isSylowTwoIn_of_le_of_le hSyl hSC hCN
  have hu' := hu
  obtain ⟨huS₀, hu2, hUu⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  set Cu := centralizer ({u} : Set G) with hCu
  set Ct := centralizer ({t} : Set G) with hCt
  obtain ⟨P, hPH, hQ0P⟩ := L34Central.exists_isSylowTwoIn_le (inf_le_inf_right Cu hSC)
    (hS2.to_le inf_le_left)
  have hP2 : IsPGroup 2 P := IsSylowTwoIn.isPGroup hPH
  obtain ⟨g, hgC, hPg⟩ := exists_conjugate_le_of_isSylowTwoIn hSt (hPH.1.trans inf_le_left) hP2
  have hgN : g ∈ normalizer (L : Set G) := hCN hgC
  have hgt : g * t = t * g := mem_centralizer_singleton_iff.mp hgC
  have hCtg : conjugate Ct g = Ct := conjugate_eq_of_mem_normalizer (le_normalizer hgC)
  have hLg : conjugate L g = L := conjugate_eq_of_mem_normalizer hgN
  have hXg : conjugate (oddIn L) g = oddIn L :=
    conjugate_eq_of_mem_normalizer (normalizer_le_normalizer_oddIn L hgN)
  have hKg : conjugate (coreActionKernel L) g = coreActionKernel L :=
    conjugate_eq_of_mem_normalizer (normalizer_le_normalizer_coreActionKernel L hgN)
  have hPS : ∀ x ∈ S ⊓ Cu, g⁻¹ * x * g ∈ S := fun x hx => hPg (conj_mem_conjugate (hQ0P hx) g)
  set u₁ := g⁻¹ * u * g with hu₁
  have hCu₁ : conjugate Cu g = centralizer ({u₁} : Set G) := conjugate_centralizer_singleton u g
  have hu₁S : u₁ ∈ S := hPS u (mem_inf.mpr ⟨huS, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hgti : ∀ i : ℤ, g⁻¹ * t ^ i * g = t ^ i := fun i => by
    have h := (Commute.zpow_right (show Commute g t from hgt) i).eq
    rw [mul_assoc, ← h]
    group
  have hu₁S₀ : u₁ ∈ S ⊓ L ⊔ zpowers t := by
    have huS₀' := huS₀
    rw [sup_comm] at huS₀'
    obtain ⟨i, l, hl, rfl⟩ :=
      mem_zpowers_sup (fun y hy => (hZS y (mem_inf.mp hy).1).symm) huS₀'
    have he : u₁ = t ^ i * (g⁻¹ * l * g) := by
      rw [hu₁, show g⁻¹ * (t ^ i * l) * g = (g⁻¹ * t ^ i * g) * (g⁻¹ * l * g) by group, hgti]
    have hlL : g⁻¹ * l * g ∈ L := by
      rw [← hLg]
      exact conj_mem_conjugate (mem_inf.mp hl).2 g
    have hlS : g⁻¹ * l * g ∈ S := by
      rw [show g⁻¹ * l * g = (t ^ i)⁻¹ * u₁ by rw [he]; group]
      exact mul_mem (inv_mem (zpow_mem htS i)) hu₁S
    rw [he]
    exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers t) i))
      (mem_sup_left (mem_inf.mpr ⟨hlS, hlL⟩))
  have hu₁2 : orderOf u₁ = 2 := by rw [hu₁, GSLit.orderOf_conj_inv, hu2]
  have hUu₁ : ¬ oddIn L ⊓ centralizer ({u₁} : Set G) ≤ oddIn (centralizer ({u₁} : Set G)) := by
    intro h
    apply hUu
    intro x hx
    have h1 : g⁻¹ * x * g ∈ oddIn L ⊓ centralizer ({u₁} : Set G) := by
      rw [← hXg, ← hCu₁, ← GSThmB.conjugate_inf]
      exact conj_mem_conjugate hx g
    have h2 := h h1
    rw [← hCu₁, oddIn_conjugate_eq] at h2
    have h3 := mem_conjugate_iff.mp h2
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h3
  refine ⟨u₁, ⟨hu₁S₀, hu₁2, hUu₁⟩, ⟨g⁻¹ * w * g, ?_, ?_, ?_⟩, ?_⟩
  ·
    have hQu : S ⊓ coreActionKernel L ≤ S ⊓ Cu := fun y hy =>
      mem_inf.mpr ⟨(mem_inf.mp hy).1, mem_centralizer_singleton_iff.mpr
        (commute_of_mem_unbalancingSet hS hU hheld hSol hGW hset hy huS₀)⟩
    have hQg : conjugate (S ⊓ coreActionKernel L) g ≤ S ⊓ coreActionKernel L := by
      intro x hx
      have hy := mem_conjugate_iff.mp hx
      have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [hx']
        exact hPS _ (hQu hy)
      · rw [← hKg, hx']
        exact conj_mem_conjugate (mem_inf.mp hy).2 g
    exact conj_mem_omegaOne hQg hwΩ
  · intro h
    apply hw1
    rw [show w = g * (g⁻¹ * w * g) * g⁻¹ by group, h]
    group
  ·
    have hle : conjugate (S ⊓ L ⊓ Cu) g ≤ S ⊓ L ⊓ centralizer ({u₁} : Set G) := by
      intro x hx
      have hy := mem_conjugate_iff.mp hx
      have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      obtain ⟨hy1, hyC⟩ := mem_inf.mp hy
      obtain ⟨hyS, hyL⟩ := mem_inf.mp hy1
      rw [hx']
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨hPS _ (mem_inf.mpr ⟨hyS, hyC⟩), ?_⟩, ?_⟩
      · rw [← hLg]
        exact conj_mem_conjugate hyL g
      · rw [← hCu₁]
        exact conj_mem_conjugate hyC g
    have h1 : g⁻¹ * w * g ∈ conjugate ⁅S ⊓ L ⊓ Cu, S ⊓ L ⊓ Cu⁆ g := conj_mem_conjugate hwc g
    rw [conjugate_commutator] at h1
    exact commutator_mono hle hle h1
  ·
    have hPgH : conjugate P g ≤ Ct ⊓ centralizer ({u₁} : Set G) := by
      rw [← hCtg, ← hCu₁, ← GSThmB.conjugate_inf]
      exact map_mono hPH.1
    have hcardH : Nat.card ↥(Ct ⊓ centralizer ({u₁} : Set G)) =
        Nat.card ↥(conjugate P g) * P.relIndex (Ct ⊓ Cu) := by
      have hc : ∀ K : Subgroup G, Nat.card ↥(conjugate K g) = Nat.card K := fun K => by
        rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
      have hH : Ct ⊓ centralizer ({u₁} : Set G) = conjugate (Ct ⊓ Cu) g := by
        rw [GSThmB.conjugate_inf, hCtg, hCu₁]
      rw [hH, hc, hc, ← relIndex_mul_card_of_le hPH.1, mul_comm]
    have hPgSyl : IsSylowTwoIn (conjugate P g) (Ct ⊓ centralizer ({u₁} : Set G)) :=
      L34Facts.isSylowTwoIn_of_card hPgH (hP2.map _) hcardH
        (GrS4.not_two_dvd_relIndex_of_isSylowTwoIn hPH)
    have hle : conjugate P g ≤ S ⊓ centralizer ({u₁} : Set G) :=
      le_inf hPg (hPgH.trans inf_le_right)
    have heq := hPgSyl.eq_of_le hle (inf_le_inf_right _ hSC) (hS2.to_le inf_le_left)
    rw [heq]
    exact hPgSyl

end CFSG.ComponentClassification.GrSLit.GrS5

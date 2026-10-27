module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import Mathlib.GroupTheory.Coset.Card
public import CFSG.GroupTheory.FixedCosetCard
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.Dihedral.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic
public import Certificates.Certificate7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public meta import Certificates.Data.ASeven

public section

namespace CFSG.GorensteinWalter

open scoped Pointwise

abbrev ASevenCosetGroup := alternatingGroup (Fin 7)

theorem a7U_eq_zpowers : a7U = Subgroup.zpowers a7a := by
  apply le_antisymm
  · intro x hx
    change x = 1 ∨ x = a7a ∨ x = a7a ^ 2 at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact (Subgroup.zpowers _).pow_mem (Subgroup.mem_zpowers _) _
  · exact Subgroup.zpowers_le.mpr (by change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2; tauto)

theorem a7U_normalizer_mem_iff (g : ASevenCosetGroup) :
    g ∈ Subgroup.normalizer (a7U : Set ASevenCosetGroup) ↔
      g * a7a * g⁻¹ = a7a ∨ g * a7a * g⁻¹ = a7a ^ 2 := by
  have ha : a7a ≠ 1 := by decide
  constructor
  · intro hg
    have hmem := (Subgroup.mem_normalizer_iff.mp hg a7a).mp
      (show a7a ∈ a7U by change a7a = 1 ∨ a7a = a7a ∨ a7a = a7a ^ 2; tauto)
    change g * a7a * g⁻¹ = 1 ∨ g * a7a * g⁻¹ = a7a ∨ g * a7a * g⁻¹ = a7a ^ 2 at hmem
    rcases hmem with h | h | h
    · exfalso
      apply ha
      have hinj := (MulAut.conj g).injective
      exact hinj (by simpa only [MulAut.conj_apply, map_one] using h)
    · exact Or.inl h
    · exact Or.inr h
  · intro hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [a7U_eq_zpowers, MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * a7a * g⁻¹) = Subgroup.zpowers a7a
    rcases hg with h | h
    · rw [h]
    · rw [h]
      have hinv : a7a ^ 2 = a7a⁻¹ := by decide
      rw [hinv, Subgroup.zpowers_inv]

@[expose] def a7ThreeNormalizer : Subgroup ASevenCosetGroup :=
  Subgroup.normalizer (a7U : Set ASevenCosetGroup)

private instance : DecidablePred (fun g : ASevenCosetGroup => g ∈ a7ThreeNormalizer) :=
  fun g => decidable_of_iff _ (a7U_normalizer_mem_iff g).symm

theorem a7ThreeNormalizer_card : Nat.card a7ThreeNormalizer = 72 := by
  let : Fintype a7ThreeNormalizer := Subtype.fintype _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [a7ThreeNormalizer, a7U_normalizer_mem_iff]
  decide +kernel

theorem a7ThreeNormalizer_centralizer_count :
    ∀ x : ASevenCosetGroup,
    (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) → x ^ 2 = 1 → x ≠ 1 →
    (Finset.univ.filter fun y : ASevenCosetGroup =>
      (y * a7a * y⁻¹ = a7a ∨ y * a7a * y⁻¹ = a7a ^ 2) ∧ y * x = x * y).card =
      if x * a7a = a7a * x then 24 else 4 := by
  decide +kernel

theorem a7ThreeNormalizer_centralizer_card (x : ASevenCosetGroup)
    (hx : x ∈ a7ThreeNormalizer) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    Nat.card (a7ThreeNormalizer ⊓ Subgroup.centralizer ({x} : Set ASevenCosetGroup) :
      Subgroup ASevenCosetGroup) =
      if x * a7a = a7a * x then 24 else 4 := by
  let : DecidablePred (fun y : ASevenCosetGroup =>
      y ∈ a7ThreeNormalizer ⊓ Subgroup.centralizer ({x} : Set ASevenCosetGroup)) := fun y => by
    apply decidable_of_iff (y ∈ a7ThreeNormalizer ∧ y * x = x * y)
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  let : Fintype (a7ThreeNormalizer ⊓ Subgroup.centralizer ({x} : Set ASevenCosetGroup) :
      Subgroup ASevenCosetGroup) :=
    Subtype.fintype _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    a7ThreeNormalizer, a7U_normalizer_mem_iff] using
    a7ThreeNormalizer_centralizer_count x ((a7U_normalizer_mem_iff x).mp hx) hx2 hx1

theorem a7ThreeNormalizer_involution_representatives :
    ∀ x : ASevenCosetGroup,
    (x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2) → x ^ 2 = 1 → x ≠ 1 →
    ∃ g : ASevenCosetGroup,
      (g * a7a * g⁻¹ = a7a ∨ g * a7a * g⁻¹ = a7a ^ 2) ∧
      g * x * g⁻¹ = if x * a7a = a7a * x then a7t else a7s := by
  decide +kernel

theorem a7ThreeNormalizer_involution_fusion (u : ASevenCosetGroup)
    (hu : u ∈ a7ThreeNormalizer) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (huouter : u * a7a ≠ a7a * u) (x : ASevenCosetGroup)
    (hx : x ∈ a7ThreeNormalizer) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ a7ThreeNormalizer, g * x * g⁻¹ = a7t ∨ g * x * g⁻¹ = u := by
  obtain ⟨gx, hgx, hxeq⟩ := a7ThreeNormalizer_involution_representatives x
    ((a7U_normalizer_mem_iff x).mp hx) hx2 hx1
  have hgxN := (a7U_normalizer_mem_iff gx).mpr hgx
  by_cases hxinner : x * a7a = a7a * x
  · exact ⟨gx, hgxN, Or.inl (by simpa only [ite_eq_left hxinner] using hxeq)⟩
  · obtain ⟨gu, hgu, hueq⟩ := a7ThreeNormalizer_involution_representatives u
      ((a7U_normalizer_mem_iff u).mp hu) hu2 hu1
    have hguN := (a7U_normalizer_mem_iff gu).mpr hgu
    have hxrep : gx * x * gx⁻¹ = a7s := by simpa only [ite_eq_right hxinner] using hxeq
    have hurep : gu * u * gu⁻¹ = a7s := by simpa only [ite_eq_right huouter] using hueq
    refine ⟨gu⁻¹ * gx, a7ThreeNormalizer.mul_mem (a7ThreeNormalizer.inv_mem hguN) hgxN,
      Or.inr ?_⟩
    calc
      (gu⁻¹ * gx) * x * (gu⁻¹ * gx)⁻¹ = gu⁻¹ * (gx * x * gx⁻¹) * gu := by group
      _ = gu⁻¹ * a7s * gu := by rw [hxrep]
      _ = u := by rw [← hurep]; group

set_option maxHeartbeats 1000000 in
theorem a7ThreeNormalizer_fixed_representatives :
    (Finset.univ.filter fun g : ASevenCosetGroup =>
      let x := g⁻¹ * a7t * g
      x * a7a * x⁻¹ = a7a ∨ x * a7a * x⁻¹ = a7a ^ 2).card = 504 := by
  decide +kernel

theorem a7ThreeNormalizer_fixedCoset_card :
    Set.ncard {x : ASevenCosetGroup ⧸ a7ThreeNormalizer | a7t • x = x} = 7 := by
  let : DecidablePred (fun g : ASevenCosetGroup =>
      g⁻¹ * a7t * g ∈ a7ThreeNormalizer) := fun g => inferInstance
  let : Fintype {g : ASevenCosetGroup // g⁻¹ * a7t * g ∈ a7ThreeNormalizer} :=
    Subtype.fintype _
  have hcount : Nat.card {g : ASevenCosetGroup // g⁻¹ * a7t * g ∈ a7ThreeNormalizer} = 504 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [a7ThreeNormalizer, a7U_normalizer_mem_iff] using
      a7ThreeNormalizer_fixed_representatives
  have h := CFSG.fixedCoset_card_mul a7ThreeNormalizer a7t
  rw [a7ThreeNormalizer_card, hcount] at h
  omega

end CFSG.GorensteinWalter

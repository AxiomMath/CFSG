module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XTabLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XEnumLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

open scoped commutatorElement

@[expose] noncomputable def XP : Subgroup (Equiv.Perm (Fin 1408)) :=
  P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))

theorem mem_XP_iff {g : Equiv.Perm (Fin 1408)} :
    g ∈ XP ↔ g ∈ P1408 ∧ g * elemZ = elemZ * g := by
  rw [XP, mem_inf, mem_centralizer_singleton_iff]

theorem closure_xU (hX : ClassSpec classz elemZ) :
    closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))) = XP := by
  have h := hX.cent_eq
  rw [classz_centGens] at h
  have himg : elemW '' {w | w ∈ [xU1, xU2]} = ({elemW xU1, elemW xU2} : Set _) := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw | hw, rfl⟩
      · exact Or.inl (by rw [hw])
      · exact Or.inr (by rw [hw])
    · rintro (rfl | rfl)
      · exact ⟨xU1, Or.inl rfl, rfl⟩
      · exact ⟨xU2, Or.inr rfl, rfl⟩
  rw [himg] at h
  exact h

theorem mem_XP_of_commTT (hg : gensOK = true) {w : List ℕ} (hw : wordOK w = true)
    (h : commTT 1408 (tabW w) (tabW wordZ) = true) : elemW w ∈ XP := by
  rw [mem_XP_iff]
  refine ⟨elemW_mem w, ?_⟩
  have hz : Rep 1408 (tabW wordZ) elemZ := rep_elemW_of_gensOK hg (by decide)
  exact (commTT_iff (rep_elemW_of_gensOK hg hw) hz).1 h

theorem commute_of_mem_closure {Γ : Type*} [Group Γ] {s : Set Γ} {a : Γ}
    (h : ∀ g ∈ s, g * a = a * g) {x : Γ} (hx : x ∈ closure s) : x * a = a * x := by
  have hle : closure s ≤ centralizer ({a} : Set Γ) := by
    rw [closure_le]
    intro y hy
    exact mem_centralizer_singleton_iff.2 (h y hy)
  exact mem_centralizer_singleton_iff.1 (hle hx)

theorem mem_derivedOf_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} {p q : Γ} (hp : p ∈ K)
    (hq : q ∈ K) : p * q * p⁻¹ * q⁻¹ ∈ derivedOf K := by
  refine mem_derivedOf_iff.mpr ⟨K.mul_mem (K.mul_mem (K.mul_mem hp hq) (K.inv_mem hp))
    (K.inv_mem hq), ?_⟩
  have h : ⁅(⟨p, hp⟩ : ↥K), ⟨q, hq⟩⁆ ∈ _root_.commutator ↥K := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  exact h

theorem enum_N (h : enumW invCap 7680 [xC1, xC2] = true) :
    IsEnumSet 1408 (subgroupList invCap [xC1, xC2])
      (closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) : Set _) := by
  have h1 := (enumW_spec h).2
  have himg : elemW '' {w | w ∈ [xC1, xC2]} = ({elemW xC1, elemW xC2} : Set _) := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw | hw, rfl⟩
      · exact Or.inl (by rw [hw])
      · exact Or.inr (by rw [hw])
    · rintro (rfl | rfl)
      · exact ⟨xC1, Or.inl rfl, rfl⟩
      · exact ⟨xC2, Or.inr rfl, rfl⟩
  rw [himg] at h1
  exact h1

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

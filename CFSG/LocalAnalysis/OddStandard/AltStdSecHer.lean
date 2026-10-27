module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerQuot
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section KGroup

theorem isKGroupCat_sec {X : Type} [Group X]
    (hK : ∀ H : Subgroup X, H ≠ ⊤ → CFSG.SectionRank.IsKGroupCat H)
    {R : Subgroup X} (hR : centralizer (R : Set X) ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat (Sec X R) :=
  (hK _ hR).quotient _

theorem oddCore_sec_eq_bot {X : Type} [Group X] [Finite X] (R : Subgroup X) :
    CFSG.oddCore (Sec X R) = ⊥ :=
  ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _

theorem isKGroupCat_of_kProper {X : Type} [Group X] [Finite X]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog X) :
    ∀ H : Subgroup X, H ≠ ⊤ → CFSG.SectionRank.IsKGroupCat H :=
  CFSG.KCore.KProperNonab.kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hK

end KGroup

section Section

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {n : ℕ}

theorem exactShape_section (h : ExactShape t A n) {R B : Subgroup X}
    (hBA : B ≤ A ⊓ centralizer (R : Set X)) {m : ℕ}
    (hBiso : Nonempty (B ≃* alternatingGroup (Fin m)))
    (hm : 5 ≤ m)
    (hnorm : centralizer ({t} : Set X) ⊓ centralizer (R : Set X) ≤ normalizer (B : Set X))
    (hcc : centralizer (B : Set X) ⊓ centralizer ({t} : Set X) ⊓ centralizer (R : Set X) ≤
      zpowers t ⊔ oddCoreOf (centralizer (R : Set X)))
    (ht : t ∈ centralizer (R : Set X)) :
    ExactShape (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (R : Set X))) : Sec X R)
      ((B.subgroupOf (centralizer (R : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (R : Set X))))) m := by
  obtain ⟨e⟩ := hBiso
  set C := centralizer (R : Set X) with hC
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  have hBt : ∀ b ∈ B, b * t = t * b := fun b hb =>
    mem_centralizer_singleton_iff.1 (h.le_cent (hBA hb).1)
  let t₀ : ↥C := ⟨t, ht⟩
  have ht₀ : orderOf t₀ = 2 := by rw [Subgroup.orderOf_mk]; exact h.order
  let e₀ : B.subgroupOf C ≃* alternatingGroup (Fin m) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans e
  refine exactShape_quotient_oddCore (t := t₀) (B := B.subgroupOf C) ht₀ hm e₀ ?_ ?_ ?_
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hBt x (Subgroup.mem_subgroupOf.1 hx)
  · intro c hc
    have hcX : (c : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    have hcN : (c : X) ∈ normalizer (B : Set X) := hnorm (Subgroup.mem_inf.2 ⟨hcX, c.2⟩)
    rw [mem_normalizer_iff]
    intro b
    have := mem_normalizer_iff.1 hcN b
    simpa [Subgroup.mem_subgroupOf] using this
  · intro c hc
    obtain ⟨hcB, hct⟩ := Subgroup.mem_inf.1 hc
    have hcX : (c : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hct ⊢
      exact congrArg Subtype.val hct
    have hcBX : (c : X) ∈ centralizer (B : Set X) := by
      rw [mem_centralizer_iff]
      intro b hb
      have := mem_centralizer_iff.1 hcB ⟨b, hBC hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      exact congrArg Subtype.val this
    have hmem := hcc (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcBX, hcX⟩, c.2⟩)
    have hsub : zpowers t ⊔ oddCoreOf C =
        (zpowers t₀ ⊔ CFSG.oddCore ↥C).map C.subtype := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    rw [hsub] at hmem
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).1 hmem

end Section

end CFSG.OddStandard.AltStdSec

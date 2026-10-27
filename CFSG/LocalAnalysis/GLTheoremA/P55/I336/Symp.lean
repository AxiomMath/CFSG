module

public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Basic
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.ClassTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem class_two_of_inf_centralizer_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G}
    {z : G} (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hrk : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥ →
      ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G) → IsElemAbelian 2 U →
        Nat.card U ≤ 2)
    (hTD : (⁅T, D⁆ : Subgroup G) ≠ ⊥) (hzT : z ∈ T) (hz : orderOf z = 2)
    (hcent : T ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z) :
    (∀ g ∈ T, g * z = z * g) ∧ ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Subgroup.zpowers z := by
  have hTne : T ≠ ⊥ := by
    rintro rfl
    exact hTD (Subgroup.commutator_bot_left D)
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
  set z' : ↥T := ⟨z, hzT⟩ with hz'
  have hz'ord : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk, hz]
  have hchar : ∀ A : Subgroup ↥T, A.Characteristic → IsMulCommutative ↥A →
      A ≤ Subgroup.zpowers z' := by
    intro A hAc hAab a ha
    set R : Subgroup G := A.map T.subtype with hR
    have hRT : R ≤ T := Subgroup.map_subtype_le A
    have hRab : IsMulCommutative ↥R :=
      ⟨⟨fun r s => by
        obtain ⟨r', hr', hrr⟩ := r.2
        obtain ⟨s', hs', hss⟩ := s.2
        apply Subtype.ext
        have h := hAab.is_comm.comm ⟨r', hr'⟩ ⟨s', hs'⟩
        have h' := congrArg (fun x : ↥A => ((x : ↥T) : G)) h
        simp only [Subgroup.coe_mul] at h'
        simp only [Subgroup.coe_mul]
        rw [← hrr, ← hss]
        exact h'⟩⟩
    have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
      refine le_normalizer_of_forall_mem fun d hd r hr => ?_
      obtain ⟨r', hr', rfl⟩ := hr
      have hσ := CFSG.SectionRank.Ccomm.char_apply_mem hAc
        (T.normalizerMonoidHom ⟨d, hDT hd⟩) hr'
      refine ⟨_, hσ, ?_⟩
      simp
    have hRc := abelian_le_centralizer hp hp2 hT hD hDne hDT hrk hRT hRab hDR
    have haR : (a : G) ∈ R := ⟨a, ha, rfl⟩
    have hmem : (a : G) ∈ T ⊓ Subgroup.centralizer (D : Set G) := ⟨a.2, hRc haR⟩
    rw [hcent] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hz', Subgroup.coe_zpow]
    exact hk
  obtain ⟨hzc, hcomm⟩ := class_two_of_char_abelian_le (P := ↥T) hT hz'ord hchar
  refine ⟨fun g hg => ?_, fun x hx y hy => ?_⟩
  · have h := Subgroup.mem_center_iff.mp hzc ⟨g, hg⟩
    exact congrArg Subtype.val h
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h := congrArg Subtype.val hk
    rw [hz', Subgroup.coe_zpow] at h
    rw [h]
    simp [commutatorElement_def]

end CFSG.LocalAnalysis.GLTheoremA.P55.I336

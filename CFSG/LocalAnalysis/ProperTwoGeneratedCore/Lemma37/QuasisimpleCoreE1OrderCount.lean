module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Omega

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3 CFSG.ShultStronglyClosedTI.InvolutionCounting

theorem thompsonPairCount_eq_of_injective {G H : Type*} [Group G] [Group H] {u z w : G}
    {u' z' w' : H} (hu : u * u = 1) (hz : z * z = 1) (hw : w * w = 1) (hu' : u' * u' = 1)
    (hz' : z' * z' = 1) (hw' : w' * w' = 1) (φ : Subgroup.centralizer {w} →* H)
    (hinj : Function.Injective φ) (hrange : φ.range = Subgroup.centralizer {w'})
    (hφw : φ ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = w')
    (hlu : ∀ c : Subgroup.centralizer {w}, IsConj u (c : G) ↔ IsConj u' (φ c))
    (hlz : ∀ c : Subgroup.centralizer {w}, IsConj z (c : G) ↔ IsConj z' (φ c)) :
    thompsonPairCount u z w = thompsonPairCount u' z' w' := by
  have key : ∀ c₁ c₂ : Subgroup.centralizer {w}, w ∈ Subgroup.zpowers ((c₁ : G) * c₂) ↔
      w' ∈ Subgroup.zpowers (φ c₁ * φ c₂) := by
    intro c₁ c₂
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hφw, ← map_mul, ← map_zpow]
      exact congrArg φ (Subtype.ext (by simpa using hk))
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← map_mul, ← map_zpow, ← hφw] at hk
      simpa using congrArg Subtype.val (hinj hk)
  let F : thompsonPairs u z w → thompsonPairs u' z' w' := fun p =>
    ⟨(φ ⟨p.1.1, (mem_centralizer_of_mem_thompsonPairs hu hz hw p.2).1⟩,
      φ ⟨p.1.2, (mem_centralizer_of_mem_thompsonPairs hu hz hw p.2).2⟩),
      (hlu _).mp p.2.1, (hlz _).mp p.2.2.1, (key _ _).mp p.2.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hq⟩ h
      have h' := congrArg Subtype.val h
      simp only [F, Prod.mk.injEq] at h'
      have h1 := congrArg Subtype.val (hinj h'.1)
      have h2 := congrArg Subtype.val (hinj h'.2)
      simp only at h1 h2
      subst h1 h2
      rfl
    · rintro ⟨⟨a, b⟩, hq⟩
      have hq' := mem_centralizer_of_mem_thompsonPairs hu' hz' hw' hq
      rw [← hrange] at hq'
      obtain ⟨c₁, rfl⟩ := hq'.1
      obtain ⟨c₂, rfl⟩ := hq'.2
      exact ⟨⟨((c₁ : G), (c₂ : G)), (hlu c₁).mpr hq.1, (hlz c₂).mpr hq.2.1,
        (key c₁ c₂).mpr hq.2.2⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective F hF)

theorem altRep2A_mul_self : altRep2A * altRep2A = 1 := Subtype.ext (by decide)

theorem altRep4A_mul_self : altRep4A * altRep4A = 1 := Subtype.ext (by decide)

theorem isConj_of_cycleType {σ : alternatingGroup (Fin 9)} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ((σ : Perm (Fin 9)).cycleType = {2, 2} → IsConj altRep2A σ) ∧
      ((σ : Perm (Fin 9)).cycleType = {2, 2, 2, 2} → IsConj altRep4A σ) := by
  have hord : orderOf (σ : Perm (Fin 9)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσ) hσ1
  obtain ⟨g, hg, hgσ⟩ := exists_conj_eq_of_orderOf_eq_two σ.2 hord
  have hconj : ∀ r : alternatingGroup (Fin 9), g * (σ : Perm (Fin 9)) * g⁻¹ = r → IsConj r σ :=
    fun r hr => isConj_iff.mpr ⟨⟨g, hg⟩⁻¹, Subtype.ext (by
      change g⁻¹ * (r : Perm (Fin 9)) * g⁻¹⁻¹ = σ
      rw [← hr]
      group)⟩
  have hct : ∀ r : Perm (Fin 9), g * (σ : Perm (Fin 9)) * g⁻¹ = r →
      (σ : Perm (Fin 9)).cycleType = r.cycleType := fun r hr => by rw [← hr, cycleType_conj]
  refine ⟨fun h2 => ?_, fun h4 => ?_⟩
  · rcases hgσ with h | h
    · exact hconj altRep2A h
    · rw [hct _ h, cycleType_altRep4] at h2
      exact absurd h2 (by decide)
  · rcases hgσ with h | h
    · rw [hct _ h, cycleType_altRep2] at h4
      exact absurd h4 (by decide)
    · exact hconj altRep4A h

theorem isConj_altRep2A_iff (σ : alternatingGroup (Fin 9)) :
    IsConj altRep2A σ ↔ σ * σ = 1 ∧ (σ : Perm (Fin 9)).cycleType = {2, 2} := by
  refine ⟨fun h => ?_, fun ⟨hσ, h2⟩ => (isConj_of_cycleType hσ ?_).1 h2⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.mp h
    refine ⟨by rw [show c * altRep2A * c⁻¹ * (c * altRep2A * c⁻¹) =
      c * (altRep2A * altRep2A) * c⁻¹ by group, altRep2A_mul_self]; group, ?_⟩
    change ((c : Perm (Fin 9)) * altRep2 * (c : Perm (Fin 9))⁻¹).cycleType = _
    rw [cycleType_conj, cycleType_altRep2]
  · rintro rfl
    rw [OneMemClass.coe_one, cycleType_one] at h2
    exact absurd h2 (by decide)

theorem isConj_altRep4A_iff (σ : alternatingGroup (Fin 9)) :
    IsConj altRep4A σ ↔ σ * σ = 1 ∧ (σ : Perm (Fin 9)).cycleType = {2, 2, 2, 2} := by
  refine ⟨fun h => ?_, fun ⟨hσ, h4⟩ => (isConj_of_cycleType hσ ?_).2 h4⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.mp h
    refine ⟨by rw [show c * altRep4A * c⁻¹ * (c * altRep4A * c⁻¹) =
      c * (altRep4A * altRep4A) * c⁻¹ by group, altRep4A_mul_self]; group, ?_⟩
    change ((c : Perm (Fin 9)) * altRep4 * (c : Perm (Fin 9))⁻¹).cycleType = _
    rw [cycleType_conj, cycleType_altRep4]
  · rintro rfl
    rw [OneMemClass.coe_one, cycleType_one] at h4
    exact absurd h4 (by decide)

theorem orderOf_altRep2A : orderOf altRep2A = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact altRep2A_mul_self) (fun h => by
    have h' := congrArg (fun σ : alternatingGroup (Fin 9) => (σ : Perm (Fin 9)) 0) h
    exact absurd h' (by decide))

theorem orderOf_altRep4A : orderOf altRep4A = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact altRep4A_mul_self) (fun h => by
    have h' := congrArg (fun σ : alternatingGroup (Fin 9) => (σ : Perm (Fin 9)) 0) h
    exact absurd h' (by decide))

theorem card_alternatingGroup_nine_eq :
    Nat.card (alternatingGroup (Fin 9)) =
      Nat.card (Subgroup.centralizer {altRep4A}) *
          thompsonPairCount altRep2A altRep4A altRep2A +
        Nat.card (Subgroup.centralizer {altRep2A}) *
          thompsonPairCount altRep2A altRep4A altRep4A := by
  refine card_eq_of_thompsonPairCount_support orderOf_altRep2A orderOf_altRep4A ?_ ?_
  · rw [isConj_altRep2A_iff]
    rintro ⟨-, h⟩
    rw [show (altRep4A : Perm (Fin 9)) = altRep4 from rfl, cycleType_altRep4] at h
    exact absurd h (by decide)
  · intro σ hσ h2 h4
    exfalso
    have hσσ : σ * σ = 1 := mul_self_eq_one_of_orderOf_eq_two hσ
    have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσ; exact absurd hσ (by decide)
    have hord : orderOf (σ : Perm (Fin 9)) = 2 := by rwa [Subgroup.orderOf_coe]
    rcases cycleType_of_orderOf_eq_two hord (mem_alternatingGroup.mp σ.2) with h | h
    · exact h2 ((isConj_of_cycleType hσσ hσ1).1 h)
    · exact h4 ((isConj_of_cycleType hσσ hσ1).2 h)

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

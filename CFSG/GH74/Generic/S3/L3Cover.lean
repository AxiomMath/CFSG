module

public import CFSG.GH74.Generic.S3.SL3Pair
public import CFSG.GH74.Generic.GKFLinear
public import CFSG.GH74.Generic.GKFBridge

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
  CFSG.RankThree.PerfectCover CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Lift

theorem exists_lift_of_card_eq
    {S₀ E J : Type} [Group S₀] [Group E] [Group J] [Finite S₀] [Finite E]
    (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E)
    (p₀ : S₀ →* J) (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ center S₀)
    (p : E →* J) (hp : Function.Surjective p) (hk : p.ker ≤ center E)
    (hcard : Nat.card (hopfMultiplier J) = Nat.card p₀.ker) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ := by
  set h₀ := hopfLift p₀ hp₀ hk₀ with hh₀
  set h := hopfLift p hp hk with hh
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective p hp hk
  have hcomp₀ : p₀.comp h₀ = hopfCoverMap J := comp_hopfLift p₀ hp₀ hk₀
  have hcomp : p.comp h = hopfCoverMap J := comp_hopfLift p hp hk
  have hmap₀ : (hopfMultiplier J).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hker₀ : ∀ u ∈ h₀.ker, u = 1 := by
    let ψ : hopfMultiplier J →* p₀.ker :=
      (h₀.comp (hopfMultiplier J).subtype).codRestrict p₀.ker fun x ↦ by
        rw [← hmap₀]
        exact ⟨x, x.2, rfl⟩
    have hψs : Function.Surjective ψ := by
      rintro ⟨c, hc⟩
      rw [← hmap₀] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfin : Finite (hopfMultiplier J) := Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact Nat.card_pos.ne')
    have hcardk : Nat.card ψ.ker * Nat.card p₀.ker = Nat.card (hopfMultiplier J) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
      rw [mul_comm]
      exact h1.symm
    have hkm : Nat.card ψ.ker = 1 := by
      have hpos : 0 < Nat.card p₀.ker := Nat.card_pos
      have h2 : Nat.card ψ.ker * Nat.card p₀.ker = 1 * Nat.card p₀.ker := by
        rw [hcardk, hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    intro u hu
    have hum : u ∈ hopfMultiplier J := by
      change hopfCoverMap J u = 1
      rw [← hcomp₀, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hu, map_one]
    have hψu : ψ ⟨u, hum⟩ = 1 := Subtype.ext (MonoidHom.mem_ker.1 hu)
    have hmem : (⟨u, hum⟩ : hopfMultiplier J) ∈ ψ.ker := hψu
    have hsub : Subsingleton ψ.ker := (Nat.card_eq_one_iff_unique.1 hkm).1
    have h3 : (⟨⟨u, hum⟩, hmem⟩ : ψ.ker) = 1 := Subsingleton.elim _ _
    exact congrArg (fun z : ψ.ker ↦ ((z : hopfMultiplier J) : HopfCover J)) h3
  have hle : h₀.ker ≤ h.ker := fun u hu => by
    rw [hker₀ u hu]
    exact one_mem _
  let α : S₀ →* E := (h₀.liftOfRightInverse (Function.surjInv h₀s)
    (Function.rightInverse_surjInv h₀s)) ⟨h, hle⟩
  have hα : ∀ u, α (h₀ u) = h u := fun u ↦
    h₀.liftOfRightInverse_comp_apply (Function.surjInv h₀s) (Function.rightInverse_surjInv h₀s)
      ⟨h, hle⟩ u
  refine ⟨α, ?_, ?_⟩
  · intro e
    obtain ⟨u, rfl⟩ := hs e
    exact ⟨h₀ u, hα u⟩
  · refine MonoidHom.ext fun x ↦ ?_
    obtain ⟨u, rfl⟩ := h₀s x
    rw [MonoidHom.comp_apply, hα, ← MonoidHom.comp_apply, hcomp, ← MonoidHom.comp_apply, hcomp₀]

end Lift

section Transport

@[expose] noncomputable def statedSUFieldEquiv {K F : Type} [Field K] [Field F] (σ : K ≃+* F) (n q : ℕ) :
    ↥(StatedSU n q K) ≃* ↥(StatedSU n q F) :=
  ((StatedSU n q K).equivMapOfInjective (CFSG.Adapters.RankTwoModelTransports.glCongr
      (ι := Fin n) σ).toMonoidHom (CFSG.Adapters.RankTwoModelTransports.glCongr σ).injective).trans
    (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU σ n q))

theorem exists_ringEquiv_of_card_eq {K F : Type} [Field K] [Finite K] [Field F] [Finite F]
    (h : Nat.card K = Nat.card F) : Nonempty (K ≃+* F) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card])⟩

theorem exists_hom_range_of_lift {G S X : Type} [Group G] [Group S] [Group X] (L : Subgroup G)
    (q : ↥L →* X) (β : S →* X) (α₀ : S →* ↥L) (hα₀s : Function.Surjective α₀)
    (hα₀ : q.comp α₀ = β) :
    ∃ α : S →* G, α.ker ≤ β.ker ∧ α.range = L := by
  refine ⟨L.subtype.comp α₀, fun x hx => ?_, ?_⟩
  · have h1 : α₀ x = 1 := Subtype.ext (MonoidHom.mem_ker.1 hx)
    rw [MonoidHom.mem_ker, ← hα₀, MonoidHom.comp_apply, h1, map_one]
  · ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (α₀ s).2
    · intro hx
      obtain ⟨s, hs⟩ := hα₀s ⟨x, hx⟩
      exact ⟨s, congrArg Subtype.val hs⟩

end Transport

section Linear

variable (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
include hGA

theorem card_hopfMultiplier_psl_three {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : CFSG.Models.LieModel X .PSL 3 p f) :
    Nat.card (hopfMultiplier X) = Nat.gcd 3 (p ^ f - 1) := by
  have h := card_hopfMultiplier_of_griess hGA hm
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [h, hgen, hexc]
  simp

theorem linear_cover_of_griess {G : Type} [Group G] [Finite G] {p f : ℕ} (hp2 : p ≠ 2)
    {L : Subgroup G} (hL : IsQuasisimple ↥L) (hmod : LieModel (↥L ⧸ center ↥L) .PSL 3 p f)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f) :
    ∃ α : SL(3, F) →* G, α.ker ≤ Subgroup.center SL(3, F) ∧ α.range = L := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := lieModel_psl_data hmod
  have hm : CFSG.Models.LieModel (↥L ⧸ center ↥L) .PSL 3 p f :=
    models_of_blueprint_of_ne_zero (by norm_num) hmod
  have hcardM := card_hopfMultiplier_psl_three hGA hp2 hm
  let β : SL(3, K) →* (↥L ⧸ center ↥L) := e.symm.toMonoidHom.comp (pLin 3 K)
  have hβs : Function.Surjective β := e.symm.surjective.comp (pLin_surjective 3 K)
  have hβker : β.ker = center SL(3, K) := by
    rw [← pLin_ker 3 K]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact map_eq_one_iff e.symm e.symm.injective
  have hS₀ : Group.IsPerfect SL(3, K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨α₀, hα₀s, hα₀⟩ := exists_lift_of_card_eq hS₀ hL.1 β hβs hβker.le
    (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by
      rw [hcardM, hβker, CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 3
        (by norm_num), hK])
  obtain ⟨α, hαker, hαrange⟩ := exists_hom_range_of_lift L _ β α₀ hα₀s hα₀
  obtain ⟨σ⟩ := exists_ringEquiv_of_card_eq (K := K) (F := F) (hK.trans hF.symm)
  obtain ⟨θ, hθker, hθrange⟩ := exists_hom_of_mulEquiv
    (CFSG.ClassicalModels.specialLinearFieldEquiv σ (Fin 3)) α (hαker.trans hβker.le)
  exact ⟨θ, hθker, hθrange.trans hαrange⟩

end Linear

section Unitary

variable (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
include hGA

theorem card_hopfMultiplier_psu_three {X : Type} [Group X] {p f : ℕ}
    (hm : CFSG.Models.LieModel X .PSU 3 p f) :
    Nat.card (hopfMultiplier X) = Nat.gcd 3 (p ^ f + 1) := by
  have h := card_hopfMultiplier_of_griess hGA hm
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [h, hgen, hexc]
  simp

theorem unitary_cover_of_griess {G : Type} [Group G] [Finite G] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    {L : Subgroup G} (hL : IsQuasisimple ↥L) (hmod : LieModel (↥L ⧸ center ↥L) .PSU 3 p f)
    (F₂ : Type) [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = (p ^ f) ^ 2) :
    ∃ α : ↥(StatedSU 3 (p ^ f) F₂) →* G,
      α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F₂) ∧ α.range = L := by
  obtain ⟨hp, hf, K, _, _, hK, ⟨e⟩⟩ := lieModel_psu_data hmod
  have hm : CFSG.Models.LieModel (↥L ⧸ center ↥L) .PSU 3 p f :=
    models_of_blueprint_of_ne_zero (by norm_num) hmod
  have hcardM := card_hopfMultiplier_psu_three hGA hm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := hU.charP
  let ε : unitaryPSU hU 3 ≃* (↥L ⧸ center ↥L) := (unitaryPSUEquiv hU (by norm_num)).trans e.symm
  let β : ↥(StatedSU 3 (p ^ f) K) →* (↥L ⧸ center ↥L) := ε.toMonoidHom.comp (unitaryProj hU 3)
  have hβs : Function.Surjective β := ε.surjective.comp (unitaryProj_surjective hU 3)
  have hβker : β.ker = unitaryScalars hU 3 := by
    rw [← ker_unitaryProj hU 3]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact map_eq_one_iff ε ε.injective
  have hcen : β.ker ≤ center ↥(StatedSU 3 (p ^ f) K) := hβker ▸ unitaryScalars_le_center hU 3
  have hS₀ : Group.IsPerfect ↥(StatedSU 3 (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK le_rfl fun h => by
      have := (Prod.mk.inj h).2
      omega
  obtain ⟨α₀, hα₀s, hα₀⟩ := exists_lift_of_card_eq hS₀ hL.1 β hβs hcen
    (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (by
      rw [hcardM, hβker, card_unitaryScalars hU (by norm_num)])
  obtain ⟨α, hαker, hαrange⟩ := exists_hom_range_of_lift L _ β α₀ hα₀s hα₀
  obtain ⟨σ⟩ := exists_ringEquiv_of_card_eq (K := K) (F := F₂) (hK.trans hF₂.symm)
  obtain ⟨θ, hθker, hθrange⟩ := exists_hom_of_mulEquiv (statedSUFieldEquiv σ 3 (p ^ f)) α
    (hαker.trans hcen)
  exact ⟨θ, hθker, hθrange.trans hαrange⟩

end Unitary

theorem b_L3_cover_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    B_L3_cover := by
  intro G _ _ p f _ hp2 h5 L hL _
  exact ⟨fun hmod F _ _ hF => linear_cover_of_griess hGA hp2 hL hmod F hF,
    fun hmod F₂ _ _ hF₂ => unitary_cover_of_griess hGA h5 hL hmod F₂ hF₂⟩

end CFSG.GH74.Generic.S3

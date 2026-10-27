module

public import CFSG.RankThree.PartOne.KE8F.E8Arith5
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourGrp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveFourLift

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Rat

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ] [IsAlgClosure K L]

theorem exists_isLift (F : E8P4Frame0 K L ℓ f) (hFn : F.n = canonicalRep (coxeterSystem .E8) L vElt)
    (hK : Nat.card K = ℓ ^ f) : ∃ m : ModGL .E8 L, IsLift F m := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨m, hm, hmaps, hfix⟩ := exists_fixed_lift (τ := .E8) (L := L)
    (Fr := iterateFrobenius L ℓ f) hq hFr vElt cElt vElt_mul_cElt
  exact ⟨m, ⟨hm, hmaps, mem_twistFixed.2 (by rw [hFn]; exact hfix)⟩⟩

@[expose] def sylowRat (F : E8P4Frame0 K L ℓ f) (m : ModGL .E8 L) :
    Subgroup (adjointGroup .E8 K) :=
  ((sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom).comap (adjEmb .E8 K L)

variable {F : E8P4Frame0 K L ℓ f} {m : ModGL .E8 L}

theorem sylowGrp_conj_le_range (hm : IsLift F m) (hK : Nat.card K = ℓ ^ f)
    [Finite (sylowGrp F m)] :
    (sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom ≤ (adjEmb .E8 K L).range := by
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hfin : Finite ((sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom) :=
    Finite.of_surjective ((MulAut.conj F.g0).toMonoidHom.subgroupMap (sylowGrp F m))
      ((MulAut.conj F.g0).toMonoidHom.subgroupMap_surjective (sylowGrp F m))
  have hXC : (sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom ≤ adjointGroup .E8 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem F.hg0C (sylowGrp_le_adjoint hm hx)) (inv_mem F.hg0C)
  have hXF : ∀ y ∈ (sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom,
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) y = y := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := mem_twistFixed.1 (sylowGrp_le_twistFixed hm hx)
    show Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (F.g0 * x * F.g0⁻¹) =
      F.g0 * x * F.g0⁻¹
    rw [map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * (F.g0 * F.n)⁻¹
        = F.g0 * (F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x * F.n⁻¹) *
          F.g0⁻¹ := by group
      _ = F.g0 * x * F.g0⁻¹ := by rw [hxfix]
  have h := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) (iterateFrobenius L ℓ f) hFr
    ((sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom) hXC hXF).1
  rw [adjEmb_range]
  exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 h)

theorem card_sylowRat (hm : IsLift F m) (hK : Nat.card K = ℓ ^ f) [Finite (sylowGrp F m)] :
    Nat.card (sylowRat F m) = Nat.card (sylowGrp F m) := by
  have hle := sylowGrp_conj_le_range hm hK
  have h1 : (((sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom).comap (adjEmb .E8 K L)).map
      (adjEmb .E8 K L) = (sylowGrp F m).map (MulAut.conj F.g0).toMonoidHom := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hle
  unfold sylowRat
  rw [← Subgroup.card_map_of_injective (adjEmb_injective (τ := .E8) (K := K) (L := L)), h1,
    Subgroup.card_map_of_injective (MulAut.conj F.g0).injective]

theorem exists_conj_into_sylowRat (hm : IsLift F m) (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f)
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1) {Q : Subgroup (adjointGroup .E8 K)}
    (hQ : IsPGroup 5 Q) :
    ∃ c : adjointGroup .E8 K, ∀ x ∈ Q, c * x * c⁻¹ ∈ sylowRat F m := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (ModGL .E8 K) := finite_modGL
  have hT0 := card_twistedTorus F hK hf
  haveI : Finite (sylowGrp F m) := Nat.finite_of_card_ne_zero (by
    rw [card_sylowGrp hm, hT0]
    positivity)
  refine exists_conj_le_of_factorization_eq 5 (sylowRat F m) ?_ hQ
  have hN : Nat.card (sylowRat F m) = (Nat.card K * Nat.card K + 1) ^ 4 * 5 := by
    rw [card_sylowRat hm hK, card_sylowGrp hm, hT0]
    ring
  exact factorization_five_eq_of_ordProj _ _ (e8P4_ordProj_five h5) hN

end Rat

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

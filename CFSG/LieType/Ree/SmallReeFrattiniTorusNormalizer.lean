module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.LieType.Ree

open CFSG.OrderReductions.FrattiniAutomorphisms CFSG.LocalAnalysis.ComponentInitial

variable {P : Type*} [Group P] {K : Type*} [Field K]

@[expose] def frattiniScalarRep (e : Additive (P ⧸ frattini P) ≃+ K) :
    MulAut P →* Multiplicative (AddAut K) where
  toFun α := Multiplicative.ofAdd
    ((e.symm.trans (MulEquiv.toAdditive (quotientAutomorphism (frattini P) α))).trans e)
  map_one' := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    ext x
    simp [map_one]
  map_mul' α β := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    ext x
    simp [map_mul]

theorem frattiniScalarRep_apply (e : Additive (P ⧸ frattini P) ≃+ K) (α : MulAut P) (x : K) :
    (frattiniScalarRep e α).toAdd x =
      e (Additive.ofMul (quotientAutomorphism (frattini P) α (Additive.toMul (e.symm x)))) :=
  rfl

theorem mem_ker_of_frattiniScalarRep_eq_one (e : Additive (P ⧸ frattini P) ≃+ K)
    {α : MulAut P} (h : frattiniScalarRep e α = 1) :
    α ∈ (quotientAutomorphism (frattini P)).ker := by
  rw [MonoidHom.mem_ker]
  refine MulEquiv.ext fun q => ?_
  have hq := congrArg (fun f : Multiplicative (AddAut K) => f.toAdd (e (Additive.ofMul q))) h
  simp only [frattiniScalarRep_apply, AddEquiv.symm_apply_apply, toMul_ofMul] at hq
  exact Additive.ofMul.injective (e.injective hq)

theorem small_Ree_Frattini_torus_normalizer_solvable (p : ℕ) [Fact p.Prime] [Finite P]
    (hP : IsPGroup p P) (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = p ^ n)
    (e : Additive (P ⧸ frattini P) ≃+ K) (T : Subgroup (MulAut P))
    (hT : T.map (frattiniScalarRep e) = scalarAddAut K) :
    IsPGroup p (derivedSeries (Subgroup.normalizer (T : Set (MulAut P))) 2) ∧
      Group.IsSolvable (Subgroup.normalizer (T : Set (MulAut P))) := by
  set N := Subgroup.normalizer (T : Set (MulAut P))
  set ρ := frattiniScalarRep e
  have hNS : ∀ α ∈ N,
      ρ α ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) := by
    intro α hα
    rw [Subgroup.mem_normalizer_iff] at hα ⊢
    intro y
    rw [← hT]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨α * s * α⁻¹, (hα s).1 hs, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨s, hs, hseq⟩
      refine ⟨α⁻¹ * s * α, ?_, ?_⟩
      · have h := (hα (α⁻¹ * s * α)).2
        rw [show α * (α⁻¹ * s * α) * α⁻¹ = s by group] at h
        exact h hs
      · rw [map_mul, map_mul, map_inv, hseq]
        group
  let ρN : N →* Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) :=
    (ρ.comp N.subtype).codRestrict _ fun α => hNS α α.2
  have hder := (small_Ree_additive_scalar_normalizer p n Fact.out hn K hK).2
  have hmap := map_derivedSeries_le_derivedSeries ρN 2
  rw [hder, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
  have hmem : ∀ x : derivedSeries N 2,
      ((x : N) : MulAut P) ∈ (quotientAutomorphism (frattini P)).ker := fun x =>
    mem_ker_of_frattiniScalarRep_eq_one e (congrArg Subtype.val (MonoidHom.mem_ker.1 (hmap x.2)))
  let φ : derivedSeries N 2 →* (quotientAutomorphism (frattini P)).ker :=
    (N.subtype.comp (derivedSeries N 2).subtype).codRestrict _ hmem
  have hφ : Function.Injective φ := fun x y h => by
    have h' : ((φ x : (quotientAutomorphism (frattini P)).ker) : MulAut P) =
        ((φ y : (quotientAutomorphism (frattini P)).ker) : MulAut P) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hp : IsPGroup p (derivedSeries N 2) :=
    (CFSG.GroupTheory.frattini_automorphism_kernel hP).2.of_injective φ hφ
  refine ⟨hp, ?_⟩
  have : Group.IsNilpotent (derivedSeries N 2) := hp.isNilpotent
  have hQ : Group.IsSolvable (N ⧸ derivedSeries N 2) := by
    refine (Group.isSolvable_def _).2 ⟨2, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries N 2)) 2,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact Group.isSolvable_of_ker_le_range (derivedSeries N 2).subtype
    (QuotientGroup.mk' (derivedSeries N 2)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end CFSG.LieType.Ree

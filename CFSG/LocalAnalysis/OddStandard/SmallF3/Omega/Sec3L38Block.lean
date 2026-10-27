module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L38Four
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkOmega
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def omegaFixEmb (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp s)) :
    omegaGroup (nondegenerate_restrict_fixSp hQ hs) →* omegaGroup hQ :=
  (((blockHom hs).comp (MonoidHom.inl _ _)).comp
    (omegaGroup (nondegenerate_restrict_fixSp hQ hs)).subtype).codRestrict (omegaGroup hQ)
    (fun a => blockHom_left_mem_omegaGroup hQ hs hW a.2)

theorem omegaFixEmb_injective (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp s)) : Function.Injective (omegaFixEmb hQ hs hW) := by
  intro a b h
  have h' : blockHom hs ((a : OGroup (Q.restrict (fixSp s))), 1) =
      blockHom hs ((b : OGroup (Q.restrict (fixSp s))), 1) := congrArg Subtype.val h
  exact Subtype.ext (congrArg Prod.fst (blockHom_injective hs h'))

theorem omegaFixEmb_commute (hQ : Q.Nondegenerate) {z : omegaGroup hQ}
    (hz : (z : OGroup Q) * z = 1) (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp (z : OGroup Q)))
    (a : omegaGroup (nondegenerate_restrict_fixSp hQ hz)) :
    omegaFixEmb hQ hz hW a * z = z * omegaFixEmb hQ hz hW a := by
  apply Subtype.ext
  have hs := blockHom_one_piOrth hz
  change blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) * (z : OGroup Q) =
    (z : OGroup Q) * blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1)
  calc blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) * (z : OGroup Q)
      = blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) *
          blockHom hz (1, piOrth (Q.restrict (commSp (z : OGroup Q)))) := by rw [hs]
    _ = blockHom hz (((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) *
          (1, piOrth (Q.restrict (commSp (z : OGroup Q))))) := (map_mul _ _ _).symm
    _ = blockHom hz ((1, piOrth (Q.restrict (commSp (z : OGroup Q)))) *
          ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1)) := by
        congr 1
    _ = blockHom hz (1, piOrth (Q.restrict (commSp (z : OGroup Q)))) *
          blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) := map_mul _ _ _
    _ = (z : OGroup Q) * blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) := by
        rw [hs]

theorem omegaFixEmb_range_normal (hQ : Q.Nondegenerate) {z : omegaGroup hQ}
    (hz : (z : OGroup Q) * z = 1) (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp (z : OGroup Q))) :
    ((omegaFixEmb hQ hz hW).range.subgroupOf
      (Subgroup.centralizer ({z} : Set (omegaGroup hQ)))).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
  have hg : ((g : omegaGroup hQ) : OGroup Q) ∈ (blockHom hz).range := by
    rw [range_blockHom hQ hz]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2))
  obtain ⟨p, hp⟩ := hg
  have hxa : ((x : omegaGroup hQ) : OGroup Q) =
      blockHom hz ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1) :=
    (congrArg Subtype.val ha).symm
  refine ⟨⟨p.1 * (a : OGroup (Q.restrict (fixSp (z : OGroup Q)))) * p.1⁻¹,
    (omegaGroup_normal _).conj_mem _ a.2 p.1⟩, ?_⟩
  apply Subtype.ext
  change blockHom hz (p.1 * (a : OGroup (Q.restrict (fixSp (z : OGroup Q)))) * p.1⁻¹, 1) =
    ((g : omegaGroup hQ) : OGroup Q) * ((x : omegaGroup hQ) : OGroup Q) *
      ((g : omegaGroup hQ) : OGroup Q)⁻¹
  rw [hxa, ← hp, ← map_inv (blockHom hz) p, ← map_mul (blockHom hz) p,
    ← map_mul (blockHom hz) (p * ((a : OGroup (Q.restrict (fixSp (z : OGroup Q)))), 1)) p⁻¹]
  congr 1
  exact Prod.ext (by simp) (by simp)

theorem isComponentIn_range_omegaFixEmb (hQ : Q.Nondegenerate) {z : omegaGroup hQ}
    (hz : (z : OGroup Q) * z = 1) (hW : 2 ≤ Module.finrank (ZMod 3) (fixSp (z : OGroup Q)))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_fixSp hQ hz))) :
    IsComponentIn (omegaFixEmb hQ hz hW).range
      (Subgroup.centralizer ({z} : Set (omegaGroup hQ))) := by
  have hle : (omegaFixEmb hQ hz hW).range ≤ Subgroup.centralizer ({z} : Set (omegaGroup hQ)) := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (omegaFixEmb_commute hQ hz hW a)
  refine ⟨hle, ?_, (omegaFixEmb_range_normal hQ hz hW).isSubnormal⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((MonoidHom.ofInjective (omegaFixEmb_injective hQ hz hW)).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm) hq

theorem exists_involution_component_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = -1) :
    ∃ z : omegaGroup hQ, orderOf z = 2 ∧ IsI4PlusIn (⊤ : Subgroup (omegaGroup hQ)) z ∧
      ∃ X : Subgroup (omegaGroup hQ),
        IsComponentIn X (Subgroup.centralizer ({z} : Set (omegaGroup hQ))) ∧
          LieModel ↥X .PSL 2 3 2 ∧ oddCore ↥X = ⊥ := by
  obtain ⟨z, hzz, hty, hfix⟩ := exists_omega_involution_four_plus hQ (by omega)
  have hcdim : Module.finrank (ZMod 3) (commSp (z : OGroup Q)) = 4 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hcsign : quadSign (Q.restrict (commSp (z : OGroup Q))) = 1 := by
    simpa only [invType, invSign] using congrArg Prod.snd hty
  have hfdim : Module.finrank (ZMod 3) (fixSp (z : OGroup Q)) = 4 := by
    have := finrank_fixSp_add_finrank_commSp (z : OGroup Q)
    omega
  have hfsign : quadSign (Q.restrict (fixSp (z : OGroup Q))) = -1 := by
    have h := quadSign_eq_fixSp_commSp hQ hzz
    have h16 : (-1 : ℤˣ) ^ (4 * 4) = 1 := by decide
    rw [hs, hcsign, hfdim, hcdim, h16, mul_one, mul_one] at h
    exact h.symm
  have hz2 : orderOf z = 2 := by
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, Subgroup.coe_one, invType_one] at hty
      exact absurd (congrArg Prod.fst hty) (by decide)
    exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hzz) hz1
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp (z : OGroup Q)) := by omega
  have hQW := nondegenerate_restrict_fixSp hQ hzz
  have hqs := isQuasisimple_omegaGroup_four_minus hQW hfdim hfsign
  have hinj := omegaFixEmb_injective hQ hzz hW
  refine ⟨z, hz2, asc82PocketCover_holds V Q hQ z (Subtype.ext hzz) hty,
    (omegaFixEmb hQ hzz hW).range, isComponentIn_range_omegaFixEmb hQ hzz hW hqs, ?_, ?_⟩
  · exact LieModel.of_mulEquiv (MonoidHom.ofInjective hinj)
      (lieModel_omegaGroup_four_minus hQW hfdim hfsign)
  · exact oddCore_eq_bot_of_mulEquiv (MonoidHom.ofInjective hinj)
      (oddCore_omegaGroup_four_minus hQW hfdim hfsign)

end CFSG.OddStandard.SmallF3.Omega

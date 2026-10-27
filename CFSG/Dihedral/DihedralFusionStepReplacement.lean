module

public import CFSG.Dihedral.DihedralFusionAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.X.ConjugationFamily

public noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u v

theorem hom_to_pGroup_image_on_sylow
    {N : Type u} {A : Type v} [Group N] [Finite N] [Group A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A)
    (f : N →* A) (Q : Sylow p N) (n : N) :
    ∃ q : N, q ∈ (Q : Subgroup N) ∧ f q = f n := by
  let T : Sylow p f.range := Q.mapSurjective f.rangeRestrict_surjective
  have htop : (T : Subgroup f.range) = ⊤ := by
    exact (T.is_maximal' ((hA.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hn : (⟨f n, ⟨n, rfl⟩⟩ : f.range) ∈ (T : Subgroup f.range) := by
    rw [htop]
    trivial
  change (⟨f n, ⟨n, rfl⟩⟩ : f.range) ∈
    (Q : Subgroup N).map f.rangeRestrict at hn
  obtain ⟨q, hq, heq⟩ := Subgroup.mem_map.mp hn
  exact ⟨q, hq, congrArg Subtype.val heq⟩

theorem dihedral_extremal_normalizer_step_replacement
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) {m : ℕ} (hm : 1 ≤ m)
    (e : S ≃* DihedralGroup (2 ^ m))
    (U : Subgroup G) (hUext : HuppertExtremal S U)
    (hU : ¬ IsKleinFour U) (h : G)
    (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    ∃ s : G, s ∈ (S : Subgroup G) ∧
      s ∈ Subgroup.normalizer (U : Set G) ∧
      ∀ x ∈ U, s⁻¹ * x * s = h⁻¹ * x * h := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hUext.exists_sylow_normalizer
  let N := Subgroup.normalizer (U : Set G)
  have hAut : IsPGroup 2 (MulAut U) :=
    dihedral_subgroup_automorphism_isTwoGroup S hm e U hUext.1 hU
  obtain ⟨q, hq, hqeq⟩ := hom_to_pGroup_image_on_sylow hAut
    U.normalizerMonoidHom Q (⟨h, hh⟩ : N)
  have hqS : (q : G) ∈ (S : Subgroup G) := by
    have hmem : (q : G) ∈ (Q : Subgroup N).map N.subtype :=
      Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hQ] at hmem
    exact hmem.1
  refine ⟨q, hqS, q.property, ?_⟩
  intro x hx
  have heq := DFunLike.congr_fun
    (congrArg MulEquiv.symm hqeq) (⟨x, hx⟩ : U)
  have hval := congrArg Subtype.val heq
  simpa only [Subgroup.normalizerMonoidHom_apply_symm_apply_coe] using hval

end CFSG.GorensteinWalter

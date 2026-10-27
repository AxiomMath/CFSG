module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_exists_lift_five (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    {w : ↥(omegaProj hQ)} (hw : orderOf w = 5) :
    ∃ (f : OGroup Q) (hf : f ∈ omegaGroup hQ),
      omegaToProj hQ ⟨f, hf⟩ = w ∧ f ^ 5 = 1 ∧ f ≠ 1 := by
  have hinj := omegaToProj_injective_of_not_mem hQ hπ
  obtain ⟨f', hf'⟩ := omegaToProj_surjective hQ w
  refine ⟨f'.1, f'.2, by simpa using hf', ?_, ?_⟩
  · have hw5 : w ^ 5 = 1 := by
      have h := pow_orderOf_eq_one w
      rwa [hw] at h
    have h5 : f' ^ 5 = 1 := by
      apply hinj
      rw [map_pow, hf', map_one]
      exact hw5
    simpa using congrArg Subtype.val h5
  · intro h1
    have h2 : f' = 1 := Subtype.ext h1
    rw [h2, map_one] at hf'
    rw [← hf'] at hw
    simp at hw

theorem fg_elemAb2_ffLift (hQ : Q.Nondegenerate) (hπ : piOrth Q ∉ omegaGroup hQ)
    {U : Subgroup ↥(omegaProj hQ)} (hU : IsElemAb2 U 4) : IsElemAb2 (ffLift hQ U) 4 := by
  have hinj := omegaToProj_injective_of_not_mem hQ hπ
  refine ⟨⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩, ?_⟩
  · obtain ⟨ha, hua⟩ := (mem_ffLift_iff hQ).1 a.2
    obtain ⟨hb, hub⟩ := (mem_ffLift_iff hQ).1 b.2
    have hc := congrArg Subtype.val (hU.1.1.is_comm.comm (⟨_, hua⟩ : ↥U) ⟨_, hub⟩)
    have h2 : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥(omegaGroup hQ)) = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply hinj
      rw [map_mul, map_mul]
      exact hc
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  · intro x hx
    obtain ⟨hxΩ, hxU⟩ := (mem_ffLift_iff hQ).1 hx
    have h2 : (⟨x, hxΩ⟩ : ↥(omegaGroup hQ)) ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      exact hU.1.2 _ hxU
    simpa using congrArg Subtype.val h2
  · rw [ffLift_card_of_not_mem hQ hπ U, hU.2]

theorem fg_mem_ffLift_conj_iff (hQ : Q.Nondegenerate) {U : Subgroup ↥(omegaProj hQ)}
    {f : OGroup Q} (hfΩ : f ∈ omegaGroup hQ)
    (hw : omegaToProj hQ ⟨f, hfΩ⟩ ∈ normalizer (U : Set ↥(omegaProj hQ))) (g : OGroup Q) :
    g ∈ ffLift hQ U ↔ f * g * f⁻¹ ∈ ffLift hQ U := by
  have hw' := Subgroup.mem_normalizer_iff.mp hw
  have himg : ∀ (g : OGroup Q) (hgΩ : g ∈ omegaGroup hQ)
      (hΩ' : f * g * f⁻¹ ∈ omegaGroup hQ), omegaToProj hQ ⟨f * g * f⁻¹, hΩ'⟩ =
        omegaToProj hQ ⟨f, hfΩ⟩ * omegaToProj hQ ⟨g, hgΩ⟩ * (omegaToProj hQ ⟨f, hfΩ⟩)⁻¹ := by
    intro g hgΩ hΩ'
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  constructor
  · intro hg
    obtain ⟨hgΩ, hgU⟩ := (mem_ffLift_iff hQ).1 hg
    have hΩ' : f * g * f⁻¹ ∈ omegaGroup hQ :=
      (omegaGroup hQ).mul_mem ((omegaGroup hQ).mul_mem hfΩ hgΩ) ((omegaGroup hQ).inv_mem hfΩ)
    refine (mem_ffLift_iff hQ).2 ⟨hΩ', ?_⟩
    rw [himg g hgΩ hΩ']
    exact (hw' _).1 hgU
  · intro hg
    obtain ⟨hΩ', hgU⟩ := (mem_ffLift_iff hQ).1 hg
    have hgΩ : g ∈ omegaGroup hQ := by
      have h := (omegaGroup hQ).mul_mem
        ((omegaGroup hQ).mul_mem ((omegaGroup hQ).inv_mem hfΩ) hΩ') hfΩ
      have heq : f⁻¹ * (f * g * f⁻¹) * f = g := by group
      rwa [heq] at h
    refine (mem_ffLift_iff hQ).2 ⟨hgΩ, ?_⟩
    rw [himg g hgΩ hΩ'] at hgU
    exact (hw' _).2 hgU

theorem fg_ffStar_map_simAct (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (γ : simGroup Q) {S : Subgroup (OGroup Q)} (hS : S ≤ omegaGroup hQ) :
    ffStar hQ (S.map (simAct Q γ).toMonoidHom) =
      (ffStar hQ S).map (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom := by
  ext w
  rw [mem_ffStar_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp hg
    refine ⟨omegaToProj hQ ⟨s, hS hs⟩, (mem_ffStar_iff hQ).2 ⟨⟨s, hS hs⟩, hs, rfl⟩, ?_⟩
    show ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) (omegaToProj hQ ⟨s, hS hs⟩) = omegaToProj hQ g
    rw [ff_simOmegaAct_omegaToProj]
    congr 1
    exact Subtype.ext hsg
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (mem_ffStar_iff hQ).1 hu
    refine ⟨⟨simAct Q γ (s : OGroup Q), ff_simAct_mem_omegaGroup hQ h2 γ s.2⟩,
      Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    exact (ff_simOmegaAct_omegaToProj hQ h2 γ s).symm

end CFSG.OddStandard.SmallF3.Omega

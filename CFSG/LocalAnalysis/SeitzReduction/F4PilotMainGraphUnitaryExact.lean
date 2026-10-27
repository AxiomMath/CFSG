module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusModel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotMainGraphUnitaryExactNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Exact


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {k : Type} [Field k] [Finite k] [CharP k 2]

theorem exists_exact_of_cover_model (e : L ≃* adjointGroup .F4 K) (ε : k ≃+* K)
    {M : Type} [Group M] [Finite M] {ι : StatedSp 3 k →* M} (hι : Function.Injective ι)
    (hιρ : ∀ ρ : k ≃+* k, ∃ ρ' : MulAut M, ∀ g, ρ' (ι g) = ι (statedSpMap (ρ : k →+* k) 3 g))
    {βC : MulAut M} (hfix : fixedSubgroup βC = ι.range) {t : G}
    (Φ₁ : M →* G) (hker : Φ₁.ker ≤ center M) (hc : ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ (βC g))
    (hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X) :
    ∃ Φ' : M →* G, Φ'.range = Φ₁.range ∧ Φ'.ker ≤ center M ∧
      ((sp6TorusA (⊤ : Subgroup kˣ)).map ι).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM2 (⊤ : Subgroup kˣ)).map ι).map Φ' = leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      ((sp6TorusM3 (⊤ : Subgroup kˣ)).map ι).map Φ' = leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have hιperf : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hcore : perfectCore (fixedSubgroup βC) = ι.range := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hβ : ∀ g, Φ₁ (βC g) = t * Φ₁ g * t⁻¹ := fun g => (hc g).symm
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₁ hker hβ
  rw [hcore, hD] at hmap
  set κ : StatedSp 3 k →* G := Φ₁.comp ι with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : ι g ∈ center M := hker hg
    have hgc' : g ∈ center (StatedSp 3 k) := by
      rw [mem_center_iff]
      intro x
      apply hι
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hgc (ι x)
    rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot] at hgc'
    exact (mem_bot.mp hgc')
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 k) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  obtain ⟨ρ', hρ'⟩ := hιρ ρ
  set δh : MulAut M := MulAut.conj (ι s) * ρ' with hδh
  set Φ' : M →* G := Φ₁.comp δh.toMonoidHom with hΦ'
  have hΦ'ι : Φ'.comp ι = levi6Hom e ε := by
    ext1 g
    rw [← hκδ, hsρ, hκdef]
    change Φ₁ (δh (ι g)) = Φ₁ (ι (s * statedSpMap (ρ : k →+* k) 3 g * s⁻¹))
    rw [hδh, MulAut.mul_apply, MulAut.conj_apply, hρ']
    simp only [map_mul, map_inv]
  refine ⟨Φ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 δh.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : δh g ∈ center M := hker hg
    rw [← Subgroup.map_center_eq (δh.symm : M ≃* M)]
    exact ⟨δh g, h1, δh.symm_apply_apply g⟩
  · rw [Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusA]
  · rw [Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusM2]
  · rw [Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusM3]

end Exact

end CFSG.SeitzReduction.F4Pilot

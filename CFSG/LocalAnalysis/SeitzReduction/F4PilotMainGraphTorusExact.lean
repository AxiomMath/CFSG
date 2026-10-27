module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotMainGraphTorusExactNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SLField

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def graphTorusSLFieldAut (ρ : F ≃+* F) :
    MulAut (SpecialLinearGroup (Fin n) F) :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map (ρ : F →+* F))
    (SpecialLinearGroup.map (ρ.symm : F →+* F))
    (by
      ext g i j
      simp [SpecialLinearGroup.map_apply_coe])
    (by
      ext g i j
      simp [SpecialLinearGroup.map_apply_coe])

theorem graphTorusSLFieldAut_apply (ρ : F ≃+* F) (g : SpecialLinearGroup (Fin n) F) :
    graphTorusSLFieldAut ρ g = SpecialLinearGroup.map (ρ : F →+* F) g :=
  rfl

end SLField

section ModelTori

variable {n : ℕ} {F : Type} [Field F]

theorem linTorusA_eq_map {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {ι : StatedSp 3 F →* SpecialLinearGroup (Fin n) F} (hιτ : ∀ t, ι (sp6Diag F t) = τ t)
    (A : Subgroup Fˣ) : linTorusA τ A = (sp6TorusA A).map ι := by
  rw [linTorusA, sp6TorusA, Subgroup.map_map]
  congr 1
  ext1 a
  exact (hιτ _).symm

theorem linTorusM2_eq_map {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {ι : StatedSp 3 F →* SpecialLinearGroup (Fin n) F} (hιτ : ∀ t, ι (sp6Diag F t) = τ t)
    (A : Subgroup Fˣ) : linTorusM2 τ A = (sp6TorusM2 A).map ι := by
  rw [linTorusM2, sp6TorusM2, Subgroup.map_map]
  congr 1
  ext1 a
  exact (hιτ _).symm

theorem linTorusM3_eq_map {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {ι : StatedSp 3 F →* SpecialLinearGroup (Fin n) F} (hιτ : ∀ t, ι (sp6Diag F t) = τ t)
    (A : Subgroup Fˣ) : linTorusM3 τ A = (sp6TorusM3 A).map ι := by
  rw [linTorusM3, sp6TorusM3, Subgroup.map_map]
  congr 1
  ext1 a
  exact (hιτ _).symm

end ModelTori

section Exact


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_exact_of_cover (e : L ≃* adjointGroup .F4 K) (ε : F ≃+* K)
    {τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F}
    {ι : StatedSp 3 F →* SpecialLinearGroup (Fin n) F} (hι : Function.Injective ι)
    (hιτ : ∀ t, ι (sp6Diag F t) = τ t)
    (hιρ : ∀ (ρ : F →+* F) g, ι (statedSpMap ρ 3 g) = SpecialLinearGroup.map ρ (ι g))
    {βC : MulAut (SpecialLinearGroup (Fin n) F)} (hfix : fixedSubgroup βC = ι.range) {t : G}
    (Φ₁ : SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ₁.ker ≤ center (SpecialLinearGroup (Fin n) F))
    (hc : ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ (βC g))
    (hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X) :
    ∃ Φ' : SpecialLinearGroup (Fin n) F →* G, Φ'.range = Φ₁.range ∧
      Φ'.ker ≤ center (SpecialLinearGroup (Fin n) F) ∧
      (linTorusA τ ⊤).map Φ' = leviTorusG e {1, 2} ⊓ neighbourLeviG e .X ∧
      (linTorusM2 τ ⊤).map Φ' = leviTorusG e {1} ⊓ neighbourLeviG e .X ∧
      (linTorusM3 τ ⊤).map Φ' = leviTorusG e {2} ⊓ neighbourLeviG e .X := by
  have hιperf : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hcore : perfectCore (fixedSubgroup βC) = ι.range := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hβ : ∀ g, Φ₁ (βC g) = t * Φ₁ g * t⁻¹ := fun g => (hc g).symm
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₁ hker hβ
  rw [hcore, hD] at hmap
  set κ : StatedSp 3 F →* G := Φ₁.comp ι with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : ι g ∈ center (SpecialLinearGroup (Fin n) F) := hker hg
    have hgc' : g ∈ center (StatedSp 3 F) := by
      rw [mem_center_iff]
      intro h
      apply hι
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hgc (ι h)
    rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot] at hgc'
    exact (mem_bot.mp hgc')
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 F) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  set δh : MulAut (SpecialLinearGroup (Fin n) F) :=
    MulAut.conj (ι s) * graphTorusSLFieldAut ρ with hδh
  set Φ' : SpecialLinearGroup (Fin n) F →* G := Φ₁.comp δh.toMonoidHom with hΦ'
  have hΦ'ι : Φ'.comp ι = levi6Hom e ε := by
    ext1 g
    rw [← hκδ, hsρ, hκdef]
    change Φ₁ (δh (ι g)) = Φ₁ (ι (s * statedSpMap (ρ : F →+* F) 3 g * s⁻¹))
    rw [hδh, MulAut.mul_apply, MulAut.conj_apply, graphTorusSLFieldAut_apply, ← hιρ]
    simp only [map_mul, map_inv]
  refine ⟨Φ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 δh.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : δh g ∈ center (SpecialLinearGroup (Fin n) F) := hker hg
    rw [← Subgroup.map_center_eq (δh.symm : SpecialLinearGroup (Fin n) F ≃* _)]
    exact ⟨δh g, h1, δh.symm_apply_apply g⟩
  · rw [linTorusA_eq_map hιτ, Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusA]
  · rw [linTorusM2_eq_map hιτ, Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusM2]
  · rw [linTorusM3_eq_map hιτ, Subgroup.map_map, hΦ'ι, map_levi6Hom_sp6TorusM3]

end Exact

end CFSG.SeitzReduction.F4Pilot

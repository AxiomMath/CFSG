module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMap
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

open CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.AGLEmbedding.LeviBlock
open scoped Pointwise

structure UniCover {A : Type} [Group A] (Y P : Subgroup A) {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (r ε : ℕ) (I : Set ℕ) where
  σ : hypSU h r ε →* ↥Y
  e : ↥Y ⧸ Subgroup.center ↥Y ≃* hypPSU h r ε
  surjective : Function.Surjective σ
  ker_le : σ.ker ≤ hypScalars h r ε
  compat : ∀ g, e (QuotientGroup.mk (σ g)) = hypProj h r ε g
  comap_eq : (P.subgroupOf Y).comap σ = flagStabilizer h r ε I

theorem exists_uniCover
    {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hodd : Odd (Nat.card (Subgroup.center ↥Y)))
    (hF : IsLieOf IdxTwistedA (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P)
    (hne : P ≠ Y) :
    ∃ (K : Type) (_ : Field K) (f t s ε : ℕ) (h : UnitaryFieldData 2 f K) (I : Finset ℕ),
      ε ≤ 1 ∧ IsTopCut I t ∧ Nonempty (UniCover Y P h (t + s) ε ↑I) := by
  classical
  obtain ⟨d, hd, ⟨e₀⟩⟩ := hF
  have hL : IsComponentOf (⊤ : Subgroup ↥Y) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hY
  let eT : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup ↥Y)).map eT.toMonoidHom = Subgroup.center ↥Y :=
    Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup ↥Y)) = Nat.card (Subgroup.center ↥Y) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup ↥Y) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥Y) ≃*
      ↥Y ⧸ Subgroup.center ↥Y := QuotientGroup.congr _ _ eT hcT
  obtain ⟨K, hK, hKfin, f, h, r, ε, ρ₀, hr, hε, -, hρ₀s, hρ₀Z⟩ :=
    exists_hypCover_dim hL (hcard ▸ hodd) d hd (eQ.trans e₀)
  let ρ : hypSU h r ε →* ↥Y := eT.toMonoidHom.comp ρ₀
  have hρs : Function.Surjective ρ := eT.surjective.comp hρ₀s
  have hρZ : ∀ g, ρ g ∈ Subgroup.center ↥Y ↔ g ∈ hypScalars h r ε := fun g => by
    rw [← hρ₀Z g]
    have : ρ g ∈ (Subgroup.center ↥(⊤ : Subgroup ↥Y)).map eT.toMonoidHom ↔
        ρ₀ g ∈ Subgroup.center ↥(⊤ : Subgroup ↥Y) := by
      rw [Subgroup.mem_map_equiv]
      simp [ρ]
    rw [← hcT]
    exact this
  obtain ⟨T, hT⟩ := ToralCensus.exists_sylow_normalizer_le_comap_of_surjective (ρ := ρ) hρs hpar
  obtain ⟨g, I₀, hI₀, hJ⟩ :=
    ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h hr hε T _ hT
  have hne' := ToralCensus.comap_ne_top_of_ne (ρ := ρ) hρs hpar.1 hne
  have hfin : I₀.Finite := (Set.finite_Icc 1 r).subset hI₀
  obtain ⟨I, rfl⟩ : ∃ I : Finset ℕ, (↑I : Set ℕ) = I₀ := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hIne : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne' (eq_top_iff.mpr fun y _ => (hJ y).mpr fun i hi => absurd hi (by simp))
  obtain ⟨t, htI, htmax⟩ : ∃ t ∈ I, ∀ i ∈ I, i ≤ t :=
    ⟨I.max' hIne, I.max'_mem hIne, fun i hi => I.le_max' i hi⟩
  have htr : t ≤ r := (hI₀ (Finset.mem_coe.mpr htI)).2
  obtain ⟨s, rfl⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  refine ⟨K, hK, f, t, s, ε, h, I, hε,
    ⟨htI, fun i hi => ⟨(hI₀ (Finset.mem_coe.mpr hi)).1, htmax i hi⟩⟩, ?_⟩
  let σ : hypSU h (t + s) ε →* ↥Y := ρ.comp (MulAut.conj g).toMonoidHom
  have hσs : Function.Surjective σ := hρs.comp (MulAut.conj g).surjective
  have hσZ : ∀ x, σ x ∈ Subgroup.center ↥Y ↔ x ∈ hypScalars h (t + s) ε := fun x => by
    rw [MonoidHom.comp_apply, hρZ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      have := (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hx g⁻¹
      simpa [mul_assoc] using this
    · intro hx
      exact (inferInstance : (hypScalars h (t + s) ε).Normal).conj_mem _ hx g
  let φ : hypSU h (t + s) ε →* ↥Y ⧸ Subgroup.center ↥Y :=
    (QuotientGroup.mk' (Subgroup.center ↥Y)).comp σ
  have hφker : ∀ x, φ x = 1 ↔ x ∈ hypScalars h (t + s) ε := fun x => by
    rw [← hσZ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let e' : hypPSU h (t + s) ε →* ↥Y ⧸ Subgroup.center ↥Y :=
    QuotientGroup.lift (hypScalars h (t + s) ε) φ fun x hx => (hφker x).mpr hx
  have he'inj : Function.Injective e' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g', rfl⟩ := hypProj_surjective h (t + s) ε x
    have : φ g' = 1 := hx
    have h2 := (hφker g').mp this
    rw [← ker_hypProj] at h2
    exact MonoidHom.mem_ker.mp h2
  have he'surj : Function.Surjective e' := by
    intro y
    obtain ⟨g', hg'⟩ := (QuotientGroup.mk'_surjective _).comp hσs y
    exact ⟨hypProj h (t + s) ε g', hg'⟩
  let e : ↥Y ⧸ Subgroup.center ↥Y ≃* hypPSU h (t + s) ε :=
    (MulEquiv.ofBijective e' ⟨he'inj, he'surj⟩).symm
  refine ⟨⟨σ, e, hσs, fun x hx => (hσZ x).mp ?_, fun x => ?_, ?_⟩⟩
  · have : σ x = 1 := hx
    rw [this]
    exact Subgroup.one_mem _
  · rw [MulEquiv.symm_apply_eq]
    rfl
  · have hmem : ∀ y : hypSU h (t + s) ε, y ∈ (P.subgroupOf Y).comap ρ ↔
        g⁻¹ * y * g ∈ flagStabilizer h (t + s) ε ↑I := fun y => by
      rw [hJ, mem_flagStabilizer]
      refine forall₂_congr fun i _ => ?_
      rw [mul_smul, mul_smul, inv_smul_eq_iff]
    ext x
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    change g * x * g⁻¹ ∈ (P.subgroupOf Y).comap ρ ↔ _
    rw [hmem]
    simp [mul_assoc]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni

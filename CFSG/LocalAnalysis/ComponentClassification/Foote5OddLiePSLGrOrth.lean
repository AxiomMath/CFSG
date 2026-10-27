module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrSp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrth

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Gr

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL

variable {n : ℕ} {K : Type} [Field K]

theorem conj_mem_commutator_self {G : Type*} [Group G] {I : Subgroup G} {H X : G} (hH : H ∈ I)
    (hX : X ∈ ⁅I, I⁆) : H * X * H⁻¹ ∈ ⁅I, I⁆ := by
  have hle : I.map (MulAut.conj H).toMonoidHom ≤ I := by
    rintro _ ⟨Y, hY, rfl⟩
    exact mul_mem (mul_mem hH hY) (inv_mem hH)
  have h1 : (⁅I, I⁆).map (MulAut.conj H).toMonoidHom ≤ ⁅I, I⁆ := by
    rw [map_commutator]
    exact commutator_mono hle hle
  exact h1 ⟨X, hX, rfl⟩

variable [Finite K]

theorem eq_one_orth_data (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {w : Fin n → K} (hw : OrthNF w) (hdata : OrthComponentData n K (diagGL hw.1))
    {R : Subgroup (MulAut (projectiveSL n K))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ r ∈ R, r * (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) =
      conjAut n K (diagGL hw.1)⁻¹ * dualAut n K * r)
    (hRc : ∀ s, (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) s = s → Odd (orderOf s) →
      ∀ r ∈ R, MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r ∈ R, r = 1 := by
  set R₀ := diagGL hw.1 with hR₀
  set A := R₀⁻¹ with hA
  have hAR : A⁻¹ = R₀ := inv_inv R₀
  set I := CatalogueBGraphForm.isometryGroup n K R₀ with hI
  set Ω := ⁅I, I⁆ with hΩ
  obtain ⟨hperf, m, L, hsup, hL⟩ := hdata
  set ΩS := Ω.comap SpecialLinearGroup.toGL with hΩS
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hΩfix : ΩS ≤ ClassicalInvolution.Balance.fixedGroup (graphLiftAut A) := by
    rw [fixedGroup_graphLiftAut, hAR]
    exact comap_mono (commutator_le_self I)
  have hΩsub : Open.IsSubnormal ΩS (ClassicalInvolution.Balance.fixedGroup (graphLiftAut A)) := by
    refine Open.IsSubnormal.step hΩfix ?_ (Open.IsSubnormal.refl _)
    rw [normal_subgroupOf_iff hΩfix]
    intro h k hh hk
    have hk' : SpecialLinearGroup.toGL k ∈ I := by
      have := hk
      rw [fixedGroup_graphLiftAut, hAR] at this
      exact this
    change SpecialLinearGroup.toGL (k * h * k⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_commutator_self hk' hh
  have hcomp : ∀ i, Open.IsComponentOf ((L i).comap SpecialLinearGroup.toGL)
      (ClassicalInvolution.Balance.fixedGroup (graphLiftAut A)) := by
    intro i
    obtain ⟨hq, hLΩ, hLn⟩ := hL i
    set F := (L i).comap SpecialLinearGroup.toGL with hF
    have hFΩ : F ≤ ΩS := comap_mono hLΩ
    have hFq : IsQuasisimple F := by
      have hmap : F.map SpecialLinearGroup.toGL = L i := map_comap_toGL_of_le_commutator hLΩ
      exact LocalCores.isQuasisimple_of_mulEquiv ((F.equivMapOfInjective _
        SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm hq
    refine ⟨hFΩ.trans hΩfix, Open.IsSubnormal.step hFΩ ?_ hΩsub,
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hFq)⟩
    rw [normal_subgroupOf_iff hFΩ]
    intro h k hh hk
    change SpecialLinearGroup.toGL (k * h * k⁻¹) ∈ L i
    rw [map_mul, map_mul, map_inv]
    exact hLn _ hk _ hh
  have hΩsup : ΩS ≤ ⨆ i, (L i).comap SpecialLinearGroup.toGL := by
    have h1 : (⨆ i, (L i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL = Ω := by
      rw [Subgroup.map_iSup]
      exact (iSup_congr fun i => map_comap_toGL_of_le_commutator (hL i).2.1).trans hsup
    intro g hg
    have hmem : SpecialLinearGroup.toGL g ∈
        (⨆ i, (L i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL := by
      rw [h1]
      exact hg
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [SpecialLinearGroup.toGL_injective hgg'] at hg'
  have hperfS : ⁅ΩS, ΩS⁆ = ΩS := by
    apply Subgroup.map_injective SpecialLinearGroup.toGL_injective
    rw [map_commutator, hmapΩ, hperf]
  intro r hr
  have hodd := odd_orderOf_of_mem hRodd hr
  have hfix : ∀ g ∈ ΩS, r (proj n K g) = proj n K g := fun g hg =>
    fix_of_le_iSup (fun i g hg => fix_of_component hinj (graphLiftAut A)
      (conjAut_mul_dualAut_proj A) (hcomp i) hRodd hRi hRc hr hg) (hΩsup hg)
  obtain ⟨D, τ, rfl⟩ := Burgoyne.PSL.exists_semilinear_of_odd hn hodd
  have hex : ∀ G ∈ Ω, (D : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K).map τ *
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G := by
    intro G hG
    set g : SpecialLinearGroup (Fin n) K := ⟨(G : Matrix (Fin n) (Fin n) K),
      det_eq_one_of_mem_commutator hG⟩
    have hg : g ∈ ΩS := by
      change SpecialLinearGroup.toGL g ∈ Ω
      have : SpecialLinearGroup.toGL g = G := Units.ext rfl
      rw [this]
      exact hG
    have h := slConj_map_eq_of_commutator_eq hperfS hfix hg
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at this
    exact this
  exact orth_centralizer hK hn hw hodd (hRi _ hr) hex

end CFSG.ComponentClassification.Foote5.OddLieCore.Gr

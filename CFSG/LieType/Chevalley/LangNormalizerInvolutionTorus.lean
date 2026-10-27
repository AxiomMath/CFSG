module

public import CFSG.LieType.Chevalley.LangWeylInvolutionStrong
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem WSL_mul_HSL (c : Kˣ) : WSL * HSL c = HSL c⁻¹ * WSL := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [WSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootWeylSL2_one_mul_rootTorusSL2
    (β : Fin τ.rank → ℤ) (c : Kˣ) :
    rootWeylSL2 τ K β 1 * rootTorusSL2 τ K β c = rootWeylSL2 τ K β c⁻¹ := by
  rw [rootWeylSL2, rootWeylSL2, rootTorusSL2, nSL_one, ← map_mul, WSL_mul_HSL, nSL_eq_HSL_mul]

theorem exists_rootTorusSL2_eq_rootDiagUnit
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (c : Kˣ) :
    ∃ a, rootTorusSL2 τ K β c = rootDiagUnit τ a ∧ rootChar a β = c ^ 2 := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  refine ⟨a, ha, ?_⟩
  have h1 := (hv c).2 β hβ
  rw [ha] at h1
  change rootDiag a (rootVec τ K β) = _ at h1
  rw [rootDiag_rootVec a hβ] at h1
  have hexp : 2 * iform β β / iform β β = 2 :=
    Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hβ).ne'
  rw [hexp] at h1
  have hne : rootVec τ K β ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hβ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective K hne h1
  refine Units.ext ?_
  rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]

theorem exists_rankOne_conj_mem_torusGroup
    [IsAlgClosed K] (hK : ringChar K ≠ 2)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {t : ModGL τ K} (ht : t ∈ torusGroup τ K) :
    ∃ y ∈ rootRankOneGroup τ K β, y * (rootWeylSL2 τ K β 1 * t) * y⁻¹ ∈ torusGroup τ K := by
  obtain ⟨-, hdH, -, -, -, hH, -, hcent⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβ
  obtain ⟨b, hb, -⟩ := hH t ht
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq ((rootChar b β : Kˣ) : K) (n := 2)
    (by norm_num)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hc₀
    exact (rootChar b β).ne_zero hc₀.symm
  set c : Kˣ := Units.mk0 c₀ hc₀0 with hc
  have hcsq : c ^ 2 = rootChar b β :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_mk0, hc₀])
  obtain ⟨a, ha, hac⟩ := exists_rootTorusSL2_eq_rootDiagUnit (K := K) hβ c
  set t₀ := (rootTorusSL2 τ K β c)⁻¹ * t with ht₀def
  have ht₀ : t₀ = rootDiagUnit τ (a⁻¹ * b) := by
    rw [ht₀def, ha, hb, rootDiagUnit_inv, ← rootDiagUnit_mul]
  have ht₀H : t₀ ∈ torusGroup τ K := mul_mem (inv_mem (hdH c)) ht
  have hχ : (∏ i, (a⁻¹ * b) i ^ β i) = 1 := by
    have e : (∏ i, (a⁻¹ * b) i ^ β i) = (rootChar a β)⁻¹ * rootChar b β := by
      simp only [rootChar, Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow,
        Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [e, hac, ← hcsq, inv_mul_cancel]
  have hcomm := hcent (a⁻¹ * b) hχ
  have e : rootWeylSL2 τ K β 1 * t = rootWeylSL2 τ K β c⁻¹ * t₀ := by
    rw [← rootWeylSL2_one_mul_rootTorusSL2, ht₀def]
    group
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (n := 2) (by norm_num)
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hζ₀
    exact one_ne_zero hζ₀
  set ζ : Kˣ := Units.mk0 ζ₀ hζ₀0 with hζ
  have hζsq : (ζ : K) ^ 2 = -1 := by rw [hζ, Units.val_mk0, hζ₀]
  set Q := qSL c⁻¹ ζ h2 with hQ
  set y := rootSL2 τ K β Q⁻¹ with hy
  refine ⟨y, ⟨Q⁻¹, rfl⟩, ?_⟩
  have hyn : y * rootWeylSL2 τ K β c⁻¹ * y⁻¹ = rootTorusSL2 τ K β ζ := by
    have e2 : Q⁻¹ * nSL c⁻¹ * Q = HSL ζ := by
      rw [mul_assoc, hQ, nSL_mul_qSL c⁻¹ ζ h2 hζsq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hy, rootWeylSL2, ← map_inv, inv_inv, ← map_mul, ← map_mul, e2, rootTorusSL2]
  have hyt : y * t₀ * y⁻¹ = t₀ := by
    have h3 := hcomm y ⟨Q⁻¹, rfl⟩
    rw [← ht₀] at h3
    rw [← h3]
    group
  rw [e]
  have e3 : y * (rootWeylSL2 τ K β c⁻¹ * t₀) * y⁻¹ =
      (y * rootWeylSL2 τ K β c⁻¹ * y⁻¹) * (y * t₀ * y⁻¹) := by group
  rw [e3, hyn, hyt]
  exact mul_mem (hdH ζ) ht₀H

theorem exists_conj_mem_torusGroup_of_pairwise
    [IsAlgClosed K] (hK : ringChar K ≠ 2) :
    ∀ (βs : List (Fin τ.rank → ℤ)), (∀ β ∈ βs, IsRoot τ β) →
      βs.Pairwise (fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) →
      ∀ (n : ModGL τ K) (hn : n ∈ monomialSubgroup τ K),
        weylQuotientHom τ K ⟨n, hn⟩ = (βs.map rootReflection).prod →
        ∃ g ∈ Subgroup.closure (⋃ β ∈ βs, (rootRankOneGroup τ K β : Set (ModGL τ K))),
          g * n * g⁻¹ ∈ torusGroup τ K := by
  intro βs
  induction βs with
  | nil =>
    intro _ _ n hn hπ
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    obtain ⟨w₀, h, hh, he⟩ := monomialSubgroup_le_torusWeylCosets hn
    have hw₀ : weylQuotientHom τ K ⟨n, hn⟩ = w₀ := weylQuotientHom_eq (by
      change MapsRootLines n w₀
      rw [he]
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w₀))
    rw [hπ, List.map_nil, List.prod_nil] at hw₀
    rw [he, ← hw₀, canonicalRep_one, mul_one]
    exact hh
  | cons β γs ih =>
    intro hroots hpair n hn hπ
    have hβ := hroots β List.mem_cons_self
    obtain ⟨-, -, hnN, -, -, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβ
    obtain ⟨hn1, hn1π⟩ := hnN 1
    set n' := (rootWeylSL2 τ K β 1)⁻¹ * n with hn'def
    have hn' : n' ∈ monomialSubgroup τ K := mul_mem (inv_mem hn1) hn
    have hπ' : weylQuotientHom τ K ⟨n', hn'⟩ = (γs.map rootReflection).prod := by
      have e : (⟨n', hn'⟩ : monomialSubgroup τ K) = (⟨_, hn1⟩)⁻¹ * ⟨n, hn⟩ := rfl
      rw [e, map_mul, map_inv, hn1π, hπ, List.map_cons, List.prod_cons, rootReflection_inv hβ,
        ← mul_assoc, rootReflection_mul_self hβ, one_mul]
    obtain ⟨g', hg', hg'n⟩ := ih (fun γ hγ => hroots γ (List.mem_cons_of_mem _ hγ))
      (List.Pairwise.of_cons hpair) n' hn' hπ'
    have hn1L : rootWeylSL2 τ K β 1 ∈ rootRankOneGroup τ K β := ⟨nSL 1, rfl⟩
    have hle : Subgroup.closure (⋃ γ ∈ γs, (rootRankOneGroup τ K γ : Set (ModGL τ K))) ≤
        Subgroup.centralizer {rootWeylSL2 τ K β 1} := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨γ, hγ, hx⟩ := hx
      obtain ⟨h0, hp, hm⟩ := List.rel_of_pairwise_cons hpair hγ
      have hcomm := exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hβ
        (hroots γ (List.mem_cons_of_mem _ hγ)) h0 hp hm
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm _ hn1L x hx).symm
    have hcommute : g' * rootWeylSL2 τ K β 1 = rootWeylSL2 τ K β 1 * g' :=
      Subgroup.mem_centralizer_singleton_iff.1 (hle hg')
    obtain ⟨y, hy, hyt⟩ := exists_rankOne_conj_mem_torusGroup hK hβ hg'n
    have hyC : y ∈ Subgroup.closure
        (⋃ δ ∈ β :: γs, (rootRankOneGroup τ K δ : Set (ModGL τ K))) :=
      Subgroup.subset_closure (Set.mem_biUnion List.mem_cons_self hy)
    have hg'C : g' ∈ Subgroup.closure
        (⋃ δ ∈ β :: γs, (rootRankOneGroup τ K δ : Set (ModGL τ K))) :=
      Subgroup.closure_mono (Set.biUnion_subset_biUnion_left fun δ hδ =>
        List.mem_cons_of_mem _ hδ) hg'
    refine ⟨y * g', mul_mem hyC hg'C, ?_⟩
    have e : y * g' * n * (y * g')⁻¹ =
        y * (rootWeylSL2 τ K β 1 * (g' * n' * g'⁻¹)) * y⁻¹ := by
      have hn : n = rootWeylSL2 τ K β 1 * n' := by rw [hn'def]; group
      calc y * g' * n * (y * g')⁻¹ = y * (g' * rootWeylSL2 τ K β 1) * n' * g'⁻¹ * y⁻¹ := by
            rw [hn]; group
        _ = y * (rootWeylSL2 τ K β 1 * (g' * n' * g'⁻¹)) * y⁻¹ := by rw [hcommute]; group
    rw [e]
    exact hyt

theorem exceptional_Lang_normalizer_Weyl_involution_torus_conjugacy
    (τ : Tag) (L : Type)
    [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 2) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (hw : weylQuotientHom τ L ⟨n, hn⟩ ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ L, g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨βs, -, hroots, hprod, hpair⟩ :=
    exceptional_Lang_Weyl_involution_strongly_orthogonal_reflections τ _ hw
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_pairwise hL βs hroots hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  have hle : Subgroup.closure (⋃ β ∈ βs, (rootRankOneGroup τ L β : Set (ModGL τ L))) ≤
      adjointGroup τ L := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨β, -, hx⟩ := hx
    exact (exceptional_Lang_root_rank_one_data τ L β).2.2.2.2.2.1 hx
  exact hle hg

end CFSG.LieType.Chevalley

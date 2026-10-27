module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PE16ClAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffV4g_card : ffV4g.card = 4 := by
  decide +kernel

theorem ff_g0_fixed_even_E0 {J : Finset (Fin 5)} (hJ : Even J.card)
    (h : ffAct ffD8g J = J) : J ∈ ffE0s := by
  revert J
  decide +kernel

@[expose] noncomputable def ffS2p (fr : PFrame Q (Option (Fin 5)) ffC) : Set (OGroup Q) :=
  {g | ∃ σ ∈ ffV4g, ∃ J ∈ ffE0s, g = ffHat fr σ * fr.signChange (ffOpt J)}

private theorem ffOutFF6PE16Cl_S2_eq_image (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffS2p fr = (fun p : Equiv.Perm (Fin 5) × Finset (Fin 5) =>
      ffHat fr p.1 * fr.signChange (ffOpt p.2)) '' (↑(ffV4g ×ˢ ffE0s) : Set _) := by
  ext g
  constructor
  · rintro ⟨σ, hσ, J, hJ, rfl⟩
    exact ⟨(σ, J), by simpa [Finset.mem_product] using ⟨hσ, hJ⟩, rfl⟩
  · rintro ⟨⟨σ, J⟩, hp, rfl⟩
    have hp' : σ ∈ ffV4g ∧ J ∈ ffE0s := by simpa [Finset.mem_product] using hp
    exact ⟨σ, hp'.1, J, hp'.2, rfl⟩

theorem ffS2p_finite (fr : PFrame Q (Option (Fin 5)) ffC) : (ffS2p fr).Finite := by
  rw [ffOutFF6PE16Cl_S2_eq_image]
  exact (Finset.finite_toSet (ffV4g ×ˢ ffE0s)).image _

theorem ffS2p_ncard_le (fr : PFrame Q (Option (Fin 5)) ffC) : (ffS2p fr).ncard ≤ 16 := by
  rw [ffOutFF6PE16Cl_S2_eq_image]
  calc ((fun p : Equiv.Perm (Fin 5) × Finset (Fin 5) =>
          ffHat fr p.1 * fr.signChange (ffOpt p.2)) ''
            (↑(ffV4g ×ˢ ffE0s) : Set (Equiv.Perm (Fin 5) × Finset (Fin 5)))).ncard
      ≤ (↑(ffV4g ×ˢ ffE0s) : Set (Equiv.Perm (Fin 5) × Finset (Fin 5))).ncard :=
        Set.ncard_image_le
          (s := (↑(ffV4g ×ˢ ffE0s) : Set (Equiv.Perm (Fin 5) × Finset (Fin 5))))
          (f := fun p : Equiv.Perm (Fin 5) × Finset (Fin 5) =>
            ffHat fr p.1 * fr.signChange (ffOpt p.2))
          (hs := Finset.finite_toSet (ffV4g ×ˢ ffE0s))
    _ = (ffV4g ×ˢ ffE0s).card := Set.ncard_coe_finset (ffV4g ×ˢ ffE0s)
    _ = 16 := by rw [Finset.card_product, ffV4g_card, ffE0s_card]

theorem ff6p_E16_many_signChanges (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) :
    4 ≤ Nat.card {J : Finset (Fin 5) // Even J.card ∧ fr.signChange (ffOpt J) ∈ U} := by
  classical
  have hPU : U ≤ ffMonoP fr := hU.1.trans (ffP0p_le_ffMonoP hQ fr)
  let R : ↥U →* Equiv.Perm (Fin 5) := (ffMonoPRho fr).comp (Subgroup.inclusion hPU)
  have hRmono : R.range ≤ ffD8p := by
    rintro r ⟨x, rfl⟩
    obtain ⟨σ, hσ, J, -, heq⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp (hU.1 x.2)
    have hxe : (Subgroup.inclusion hPU x : OGroup Q) = ffHat fr σ * fr.signChange (ffOpt J) := by
      rw [Subgroup.coe_inclusion]; exact heq
    show R x ∈ ffD8p
    rw [show R x = ffMonoPRho fr (Subgroup.inclusion hPU x) from rfl,
      ffMonoPRho_eq_of_hat fr hxe]
    exact hσ
  have hR2 : ∀ r ∈ R.range, r * r = 1 := by
    rintro r ⟨x, rfl⟩
    have hx2 : (x : ↥U) * x = 1 := by
      apply Subtype.ext
      have h := hU.2.1.1.2 (x : OGroup Q) x.2
      simpa [pow_two] using h
    rw [← map_mul, hx2, map_one]
  have hRcard : Nat.card R.range ≤ 4 := ffD8p_elemAb_card_le R.range hRmono hR2
  have hker4 : 4 ≤ Nat.card R.ker := by
    have h := Subgroup.card_ker_mul_card_range R
    have hU16 : Nat.card ↥U = 16 := by rw [hU.2.1.2]; norm_num
    rw [hU16] at h
    have hle : Nat.card R.ker * Nat.card R.range ≤ Nat.card R.ker * 4 :=
      Nat.mul_le_mul_left _ hRcard
    omega
  have hker_exists : ∀ x : ↥R.ker, ∃ J : Finset (Fin 5), Even J.card ∧
      (x.1 : OGroup Q) = fr.signChange (ffOpt J) := by
    intro x
    obtain ⟨σ, -, J, hJe, heq⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp (hU.1 x.1.2)
    have hxe : (Subgroup.inclusion hPU x.1 : OGroup Q) = ffHat fr σ * fr.signChange (ffOpt J) := by
      rw [Subgroup.coe_inclusion]; exact heq
    have hσ1 : σ = 1 := by
      have h : R x.1 = 1 := x.2
      rw [show R x.1 = ffMonoPRho fr (Subgroup.inclusion hPU x.1) from rfl,
        ffMonoPRho_eq_of_hat fr hxe] at h
      exact h
    refine ⟨J, hJe, ?_⟩
    rw [hσ1, ffHat_one, one_mul] at heq
    exact heq
  let φ : ↥R.ker → {J : Finset (Fin 5) // Even J.card ∧ fr.signChange (ffOpt J) ∈ U} :=
    fun x => ⟨Classical.choose (hker_exists x), (Classical.choose_spec (hker_exists x)).1,
      by rw [← (Classical.choose_spec (hker_exists x)).2]; exact x.1.2⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hJ : Classical.choose (hker_exists x) = Classical.choose (hker_exists y) :=
      congrArg Subtype.val hxy
    have hx := (Classical.choose_spec (hker_exists x)).2
    have hy := (Classical.choose_spec (hker_exists y)).2
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, hy, hJ]
  exact hker4.trans (Nat.card_le_card_of_injective φ hφinj)

theorem ff6p_signChange_act (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : U ≤ ffP0p hQ fr) (hn : (U.subgroupOf (ffP0p hQ fr)).Normal)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ ffD8p) {J : Finset (Fin 5)}
    (hJ : fr.signChange (ffOpt J) ∈ U) : fr.signChange (ffOpt (ffAct τ J)) ∈ U := by
  have hHat : ffHat fr τ ∈ ffP0p hQ fr := ffOutFF6PE16Cl_hat_mem_P hQ fr hτ
  have hconj := (Subgroup.normal_subgroupOf_iff hU).mp hn (fr.signChange (ffOpt J))
    (ffHat fr τ) hJ hHat
  rwa [ffHat_conj_signChange_ffOpt fr τ J] at hconj

theorem ff6p_E16_hat_mem_V4 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) {J : Finset (Fin 5)}
    (hu : ffHat fr σ * fr.signChange (ffOpt J) ∈ U) : σ ∈ ffV4g := by
  classical
  by_cases hσ1 : σ = 1
  · rw [hσ1]; simp [ffV4g]
  · obtain ⟨hsq, -, hfix⟩ := ffOutFF6PE16Cl_sq_fix hQ fr hU hσ hu
    have hmany := ff6p_E16_many_signChanges hQ fr hU
    have hJcard : 4 ≤ (Finset.univ.filter (fun J : Finset (Fin 5) =>
        Even J.card ∧ fr.signChange (ffOpt J) ∈ U)).card := by
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hmany
    have hnotsub : ¬ (Finset.univ.filter (fun J : Finset (Fin 5) =>
        Even J.card ∧ fr.signChange (ffOpt J) ∈ U)) ⊆
        ({∅, {0, 1, 2, 3}} : Finset (Finset (Fin 5))) := by
      intro hsub
      have h2 : ({∅, {0, 1, 2, 3}} : Finset (Finset (Fin 5))).card ≤ 2 := by decide
      exact absurd ((Finset.card_le_card hsub).trans h2) (by omega)
    obtain ⟨J', hJ'mem, hJ'not⟩ := Finset.not_subset.mp hnotsub
    have hJ'even : Even J'.card := (Finset.mem_filter.mp hJ'mem).2.1
    have hJ'U : fr.signChange (ffOpt J') ∈ U := (Finset.mem_filter.mp hJ'mem).2.2
    have hJ'ne : J' ≠ ∅ ∧ J' ≠ {0, 1, 2, 3} := by
      constructor <;> intro h
      · exact hJ'not (by rw [h]; simp)
      · exact hJ'not (by rw [h]; simp)
    have hfixJ' : ∀ τ ∈ ffD8p, ffAct σ (ffAct τ J') = ffAct τ J' := by
      intro τ hτ
      exact hfix (ffAct τ J') (ff6p_signChange_act hQ fr hU.1 hU.2.2 hτ hJ'U)
    rcases ffD8_fixed_orbit hσ hσ1 hsq hJ'even hfixJ' with h1 | h2 | ⟨hV, -⟩
    · exact absurd h1 hJ'ne.1
    · exact absurd h2 hJ'ne.2
    · exact hV

theorem ff6p_E16_signChanges_E0 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) (hne : U ≠ ffB0p fr)
    {J : Finset (Fin 5)} (hJe : Even J.card) (hJ : fr.signChange (ffOpt J) ∈ U) :
    J ∈ ffE0s := by
  classical
  have hnotle : ¬ U ≤ ffB0p fr := by
    intro hle
    have hcard : Nat.card (ffB0p fr) ≤ Nat.card U := by
      rw [ffB0p_card, hU.2.1.2]; norm_num
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard)
  obtain ⟨u0, hu0U, hu0B0⟩ := Set.not_subset.mp (show ¬ (U : Set (OGroup Q)) ⊆
    (ffB0p fr : Set (OGroup Q)) from hnotle)
  obtain ⟨σ0, hσ0D, J0, hJ0e, hu0eq⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp (hU.1 hu0U)
  have hσ0ne : σ0 ≠ 1 := by
    intro h
    apply hu0B0
    rw [hu0eq, h, ffHat_one, one_mul]
    exact (mem_ffB0p_iff_ffOpt fr).mpr ⟨J0, hJ0e, rfl⟩
  have hu0form : ffHat fr σ0 * fr.signChange (ffOpt J0) ∈ U := hu0eq ▸ hu0U
  obtain ⟨hsq0, -, hfix0⟩ := ffOutFF6PE16Cl_sq_fix hQ fr hU hσ0D hu0form
  have hfixJ : ∀ τ ∈ ffD8p, ffAct σ0 (ffAct τ J) = ffAct τ J := by
    intro τ hτ
    exact hfix0 (ffAct τ J) (ff6p_signChange_act hQ fr hU.1 hU.2.2 hτ hJ)
  rcases ffD8_fixed_orbit hσ0D hσ0ne hsq0 hJe hfixJ with h1 | h2 | ⟨-, hE⟩
  · rw [h1]; simp [ffE0s]
  · rw [h2]; simp [ffE0s]
  · exact hE

theorem ff6p_E16_hat_E0 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) (hne : U ≠ ffB0p fr)
    {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ ffD8p) {J : Finset (Fin 5)} (hJe : Even J.card)
    (hu : ffHat fr σ * fr.signChange (ffOpt J) ∈ U) : J ∈ ffE0s := by
  classical
  have hσV : σ ∈ ffV4g := ff6p_E16_hat_mem_V4 hQ fr hU hσ hu
  rcases (by simpa [ffV4g] using hσV) with h1 | h2 | h3 | h4
  · rw [h1, ffHat_one] at hu
    exact ff6p_E16_signChanges_E0 hQ fr hU hne hJe (by simpa using hu)
  · exact ffOutFF6PE16Cl_E0_of_swap02 hQ fr hU hJe (h2 ▸ hu)
  · have hu'U : ffHat fr ffRot * (ffHat fr (Equiv.swap 1 3) * fr.signChange (ffOpt J)) *
        (ffHat fr ffRot)⁻¹ ∈ U :=
      (Subgroup.normal_subgroupOf_iff hU.1).mp hU.2.2 _ _ (h3 ▸ hu)
        (ffOutFF6PE16Cl_hat_mem_P hQ fr ffRot_mem_ffD8p)
    have hrotconj : ffRot * Equiv.swap 1 3 * ffRot⁻¹ = Equiv.swap 0 2 := by decide +kernel
    have hu'eq : ffHat fr ffRot * (ffHat fr (Equiv.swap 1 3) * fr.signChange (ffOpt J)) *
        (ffHat fr ffRot)⁻¹ =
        ffHat fr (Equiv.swap 0 2) * fr.signChange (ffOpt (ffAct ffRot J)) := by
      rw [ffOutFF6PE16Cl_conj_hat, hrotconj]
    have hEvenRot : Even (ffAct ffRot J).card := by rw [ffAct_card]; exact hJe
    have hE0rot : ffAct ffRot J ∈ ffE0s :=
      ffOutFF6PE16Cl_E0_of_swap02 hQ fr hU hEvenRot (hu'eq ▸ hu'U)
    have hrotinvD : ffRot⁻¹ ∈ ffD8p := Subgroup.inv_mem _ ffRot_mem_ffD8p
    have hJeq : ffAct ffRot⁻¹ (ffAct ffRot J) = J := by
      rw [← ffAct_mul, inv_mul_cancel, ffAct_one]
    rw [← hJeq]
    exact ffE0s_act hrotinvD hE0rot
  · have h4' : σ = ffD8g := h4
    exact ffOutFF6PE16Cl_E0_of_ffD8g hQ fr hU hJe (h4' ▸ hu)

theorem ff6p_E16_le_S2 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) (hne : U ≠ ffB0p fr) :
    (U : Set (OGroup Q)) ⊆ ffS2p fr := by
  intro u hu
  obtain ⟨σ, hσ, J, hJe, heq⟩ := (mem_ffP0p_iff_hatOpt hQ fr).mp (hU.1 hu)
  have huform : ffHat fr σ * fr.signChange (ffOpt J) ∈ U := heq ▸ hu
  exact ⟨σ, ff6p_E16_hat_mem_V4 hQ fr hU hσ huform, J,
    ff6p_E16_hat_E0 hQ fr hU hne hσ hJe huform, heq⟩

theorem ff6p_E16_eq_S2 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) (hne : U ≠ ffB0p fr) :
    (U : Set (OGroup Q)) = ffS2p fr := by
  refine Set.eq_of_subset_of_ncard_le (ff6p_E16_le_S2 hQ fr hU hne) ?_
  have hUcard : (U : Set (OGroup Q)).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    show Nat.card U = 16
    rw [hU.2.1.2]; norm_num
  rw [hUcard]
  exact ffS2p_ncard_le fr

theorem ff6p_E16_unique (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U W : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U)
    (hW : IsNormalE16In (ffP0p hQ fr) W) (hUne : U ≠ ffB0p fr) (hWne : W ≠ ffB0p fr) :
    U = W := by
  have hUeq := ff6p_E16_eq_S2 hQ fr hU hUne
  have hWeq := ff6p_E16_eq_S2 hQ fr hW hWne
  exact SetLike.ext'_iff.mpr (hUeq.trans hWeq.symm)

theorem ffZ0p_mem_E16 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {U : Subgroup (OGroup Q)} (hU : IsNormalE16In (ffP0p hQ fr) U) : ffZ0p fr ∈ U := by
  by_cases h : U = ffB0p fr
  · rw [h]; exact ffZ0p_mem_ffB0p fr
  · have hsub := ff6p_E16_eq_S2 hQ fr hU h
    have hZ : ffZ0p fr ∈ ffS2p fr := by
      refine ⟨1, by simp [ffV4g], {0, 1, 2, 3}, by simp [ffE0s], ?_⟩
      rw [ffZ0p, ffHat_one, one_mul]
    rwa [← hsub] at hZ

end CFSG.OddStandard.SmallF3.Omega

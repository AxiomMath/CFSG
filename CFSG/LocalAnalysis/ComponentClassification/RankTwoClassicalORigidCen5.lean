module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Cen

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

theorem noNormalTwo_centralizer_oBarTwo_sup_oBarOne (hinj : Function.Injective (oProj Q))
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hO₂ : NoNormalTwo (StatedOmega Q₂))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0) :
    NoNormalTwo (centralizer ((oBarTwo oe hQ hSL ⊔ oBarOne oe hQ hSL : Subgroup _) :
      Set (StatedProj (StatedOmega Q)))) := by
  intro R hRC hR2 hCN
  obtain ⟨f, hf⟩ : ∃ f : StatedOmega Q₂ →* StatedProj (StatedOmega Q),
      f = (oProj Q).comp (oKappa oe hQ) := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by
    rw [hf]
    exact hinj.comp oKappa_injective
  have hCκ : ∀ r ∈ centralizer ((oBarTwo oe hQ hSL ⊔ oBarOne oe hQ hSL : Subgroup _) :
      Set (StatedProj (StatedOmega Q))), ∃ g : StatedOmega Q, oProj Q g = r ∧
        ∃ Y : GL ι₂ K, (g : GL ι K) = oKappaGL oe Y ∧
          ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := by
    intro r hr
    obtain ⟨g, rfl⟩ := oProj_surjective Q r
    refine ⟨g, rfl, exists_oKappaGL_of_commute (hQ := hQ) (hSL := hSL) ht0 ht1
      (fun A => hinj ?_) (fun B => hinj ?_)⟩
    · rw [map_mul, map_mul]
      exact (mem_centralizer_iff.mp hr _ (mem_sup_left ⟨A, rfl⟩)).symm
    · rw [map_mul, map_mul]
      exact (mem_centralizer_iff.mp hr _ (mem_sup_right ⟨B, rfl⟩)).symm
  have hLC : f.range ≤ centralizer ((oBarTwo oe hQ hSL ⊔ oBarOne oe hQ hSL : Subgroup _) :
      Set (StatedProj (StatedOmega Q))) := by
    rw [le_centralizer_iff]
    refine sup_le (fun x hx => mem_centralizer_iff.mpr fun y hy => ?_)
      (fun x hx => mem_centralizer_iff.mpr fun y hy => ?_)
    · obtain ⟨Z, rfl⟩ := hy
      rw [hf]
      exact (oBarTwo_commute_oBarL hx ⟨Z, rfl⟩).symm
    · obtain ⟨Z, rfl⟩ := hy
      rw [hf]
      exact (oBarOne_commute_oBarL hx ⟨Z, rfl⟩).symm
  have hRL : ∀ Z : StatedOmega Q₂, f Z ∈ R → Z = 1 := by
    have hMn : (R.comap f).Normal := ⟨fun z hz Z => by
      rw [mem_comap, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (hCN (hLC ⟨Z, rfl⟩)) (f z)).mp hz⟩
    have hN : (R.comap f).map (StatedOmega Q₂).subtype = ⊥ := by
      refine hO₂ _ (map_subtype_le _) ?_ ?_
      · rintro ⟨_, z, hz, rfl⟩
        obtain ⟨k, hk⟩ := hR2 ⟨f z, hz⟩
        have h1 : f (z ^ 2 ^ k) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val hk
        have h2 : z ^ 2 ^ k = 1 := hfinj (by rw [h1, map_one])
        refine ⟨k, Subtype.ext ?_⟩
        rw [SubmonoidClass.coe_pow, Subgroup.coe_one]
        show ((z : GL ι₂ K)) ^ 2 ^ k = 1
        rw [← SubmonoidClass.coe_pow, h2, Subgroup.coe_one]
      · refine le_trans ?_ (le_normalizer_map (StatedOmega Q₂).subtype)
        rw [normalizer_eq_top_iff.mpr hMn, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    intro Z hZ
    have h1 : (Z : GL ι₂ K) ∈ (R.comap f).map (StatedOmega Q₂).subtype := ⟨Z, hZ, rfl⟩
    rw [hN, mem_bot] at h1
    exact Subtype.ext h1
  have hκinj : Function.Injective (oKappaGL (K := K) oe) := fun Y Y' h => by
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
    simp only [coe_oKappaGL] at h1
    exact Units.ext (oblk_injective h1).1
  have hRc : ∀ r ∈ R, ∀ Z : StatedOmega Q₂, f Z * r = r * f Z := by
    intro r hr Z
    have h2 : f Z * r * (f Z)⁻¹ * r⁻¹ ∈ R :=
      mul_mem ((mem_normalizer_iff.mp (hCN (hLC ⟨Z, rfl⟩)) _).mp hr) (inv_mem hr)
    obtain ⟨g, rfl, Y, hgY, hY⟩ := hCκ _ (hRC hr)
    have hYZ : Y * ((Z⁻¹ : StatedOmega Q₂) : GL ι₂ K) * Y⁻¹ ∈ StatedOmega Q₂ :=
      conj_mem_statedOmega hY (Z⁻¹).2
    have h1' : oKappa oe hQ Z * g * (oKappa oe hQ Z)⁻¹ * g⁻¹ =
        oKappa oe hQ (Z * ⟨_, hYZ⟩) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv, hgY]
      show oKappaGL oe (Z : GL ι₂ K) * oKappaGL oe Y * (oKappaGL oe (Z : GL ι₂ K))⁻¹ *
        (oKappaGL oe Y)⁻¹ = oKappaGL oe ((Z : GL ι₂ K) * (Y * ((Z⁻¹ : StatedOmega Q₂) :
          GL ι₂ K) * Y⁻¹))
      simp only [map_mul, map_inv, Subgroup.coe_inv]
      group
    have h1 : f Z * oProj Q g * (f Z)⁻¹ * (oProj Q g)⁻¹ = f (Z * ⟨_, hYZ⟩) := by
      rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, ← h1', map_mul, map_mul, map_mul,
        map_inv, map_inv]
    rw [h1] at h2
    rw [hRL _ h2, map_one] at h1
    calc f Z * oProj Q g =
        f Z * oProj Q g * (f Z)⁻¹ * (oProj Q g)⁻¹ * (oProj Q g * f Z) := by group
      _ = oProj Q g * f Z := by rw [h1, one_mul]
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  obtain ⟨g, rfl, Y, hgY, hY⟩ := hCκ _ (hRC hr)
  have hYc : ∀ Z ∈ StatedOmega Q₂,
      (Y : Matrix ι₂ ι₂ K) * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y := by
    intro Z hZ
    have h0 := hRc _ hr ⟨Z, hZ⟩
    rw [hf, MonoidHom.comp_apply, ← map_mul, ← map_mul] at h0
    have h1 := congrArg (fun x : StatedOmega Q => (x : GL ι K)) (hinj h0)
    simp only [Subgroup.coe_mul, hgY] at h1
    have h2 : oKappaGL oe (Z * Y) = oKappaGL oe (Y * Z) := by
      rw [map_mul, map_mul]
      exact h1
    have h3 := congrArg Units.val (hκinj h2)
    rw [Units.val_mul, Units.val_mul] at h3
    exact h3.symm
  obtain ⟨d, hd⟩ := hcomm (Y : Matrix ι₂ ι₂ K) hYc
  have hd1 : d = 1 := by
    have h1 := hY w₀
    rw [hd, smul_mulVec, one_mulVec, hsm] at h1
    have h2 : d * d = 1 * 1 := by
      rw [one_mul]
      exact (mul_eq_right₀ hw₀).mp h1
    exact eq_of_mul_self_eq h2
  have hY1 : Y = 1 := Units.ext (by rw [hd, hd1, one_smul, Units.val_one])
  have hg1 : g = 1 := Subtype.ext (by rw [hgY, hY1, map_one, Subgroup.coe_one])
  rw [hg1, map_one]

end Cen

end CFSG.ComponentClassification.RankTwoClassical.ORigid

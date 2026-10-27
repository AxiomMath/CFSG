module

public import CFSG.GH74.GLS.Stage4.T2F1LocGlue
public import CFSG.GH74.GLS.Stage4.T2F1LocActs
public import CFSG.GH74.GLS.Stage4.T2F1LocDesc
public import CFSG.GH74.GLS.Stage4.T2F1LocG
public import CFSG.GH74.GLS.Stage4.T2F1LocSyl
public import CFSG.GH74.GLS.Stage4.T2F1LocCoord
public import CFSG.GH74.GLS.Stage4.T2Ctx

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.Assembly.LowTwoRank

section Aux

theorem mem_oPrimeResidualOf_of_pow {G : Type} [Group G] {X : Subgroup G} {y : G} (hy : y ∈ X)
    (h : ∃ k : ℕ, y ^ (2 ^ k) = 1) : y ∈ oPrimeResidualOf 2 X := by
  obtain ⟨k, hk⟩ := h
  exact ⟨⟨y, hy⟩, Subgroup.subset_closure ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem slFixIncl_negOne {F : Type} [Field F] (σ : F ≃+* F) :
    slFixIncl σ (negOne (fixF σ)) = negOne F := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slFixIncl_apply]

end Aux


section Charts

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {z t : G} {K₁ K₂ : Subgroup G}
  {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem f1_charts {n : ℕ} (hn : 3 ≤ n)
    (hSet : Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    {N : T2N3 G} {u : G} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = 3 ^ n) (hq₂ : N.q₂ = 3 ^ n) (hSec : Ch6Sec5 N u)
    {r : ℕ} (hodd : Odd r) {f : G} (hfr : f ^ r = 1) (hf : f ∈ N.F)
    (hfS : ∀ s ∈ N.S, f * s = s * f)
    {φ₁ : SL2 F₁ →* G} (hφ₁ : Function.Injective φ₁) (hrange₁ : φ₁.range = K₁)
    (hneg₁ : φ₁ (negOne F₁) = z) {σ₁ : F₁ ≃+* F₁}
    (hσ₁ : ∀ M : SL2 F₁, f * φ₁ M * f⁻¹ = φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M))
    {φ₂ : SL2 F₂ →* G} (hφ₂ : Function.Injective φ₂) (hrange₂ : φ₂.range = K₂)
    (hneg₂ : φ₂ (negOne F₂) = z) {σ₂ : F₂ ≃+* F₂}
    (hσ₂ : ∀ M : SL2 F₂, f * φ₂ M * f⁻¹ = φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M)) :
    ∃ t' : G, t' ∈ N.S ∧ ∃ (g₁ : GL (Fin 2) (fixF σ₁)) (g₂ : GL (Fin 2) (fixF σ₂)),
      GChart f z (φ₁.comp (slFixIncl σ₁)) (φ₂.comp (slFixIncl σ₂)) g₁ g₂ t' := by
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have : Finite F₁ := hSet.finite₁
  have : Finite F₂ := hSet.finite₂
  have hctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have hzz : z * z = 1 := hctx.zz
  have hz1 : z ≠ 1 := hctx.z_ne
  have hfz : f * z = z * f := by rw [← hz]; exact hfS _ hLoc.z_mem_S
  have hgen : K₁ ⊔ K₂ ⊔ Subgroup.zpowers t = oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    hRem.gen
  have hfK₁ : ∀ x ∈ K₁, f * x * f⁻¹ ∈ K₁ := by
    have := conj_mem_sup (hF5.F_normX₁ f hf) (hF5.F_normX₁' f hf)
    rw [← hLoc.K₁_eq, hK₁] at this
    exact this
  have hfK₂ : ∀ x ∈ K₂, f * x * f⁻¹ ∈ K₂ := by
    have := conj_mem_sup (hF5.F_normX₂ f hf) (hF5.F_normX₂' f hf)
    rw [← hLoc.K₂_eq, hK₂] at this
    exact this
  have htz : t * z = z * t := hRem.comm_z
  have htC : t ∈ oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    hgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  let S₂ : Sylow 2 G := hLoc.S_pGroup.toSylow hLoc.S_sylow
  have hS₂ : (S₂ : Subgroup G) = N.S := IsPGroup.toSylow_coe _ _
  have hS₂C : (S₂ : Subgroup G) ≤ oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    rw [hS₂]
    have := hctx.SC₁
    exact this
  obtain ⟨c, hcC, hct⟩ := exists_conj_into_sylow S₂ hS₂C htC hRem.sq
  have ht'S : c⁻¹ * t * c ∈ N.S := by rw [← hS₂]; exact hct
  have ht'2 : (c⁻¹ * t * c) * (c⁻¹ * t * c) = 1 := by
    calc (c⁻¹ * t * c) * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c := by group
      _ = 1 := by rw [hRem.sq]; group
  have hnK : ∀ x ∈ K₁ ⊔ K₂, t * x * t⁻¹ ∈ K₁ ⊔ K₂ := fun x hx =>
    hctx.Kn t (Subgroup.mem_centralizer_singleton_iff.2 htz) x hx
  obtain ⟨k, hk, hk'⟩ := exists_conj_eq_mul hRem.sq hnK (hgen ▸ hcC)
  generalize c⁻¹ * t * c = t' at ht'S ht'2 hk'
  have hft : f * t' = t' * f := hfS t' ht'S
  have ht'z : t' * z = z * t' := by rw [← hz]; exact hLoc.z_cent_S t' ht'S
  have hnK' : ∀ x ∈ K₁ ⊔ K₂, t' * x * t'⁻¹ ∈ K₁ ⊔ K₂ := fun x hx =>
    hctx.Kn t' (Subgroup.mem_centralizer_singleton_iff.2 ht'z) x hx
  have hgen' : K₁ ⊔ K₂ ⊔ Subgroup.zpowers t' =
      oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    apply le_antisymm
    · exact sup_le hSet.le_residual (Subgroup.zpowers_le.2 (hctx.SC₁ ht'S))
    · rw [← hgen]
      refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
      have : t = t' * k⁻¹ := by rw [hk']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t'))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hk))
  have h27 : 27 ≤ 3 ^ n := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact Odd.pow (by decide)
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact Odd.pow (by decide)
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; omega
  have h3₂ : 3 < Nat.card F₂ := by rw [hSet.card₂]; omega
  obtain ⟨g₁', hns₁, hact₁⟩ := actsAsConj_in_coord hodd₁ h3₁ φ₁ hφ₁ hrange₁ hSet.comm
    (by rw [hgen]; exact (t2C_C₁_normalizes hRem hSet.comm).1) hRem.diag₁ ⟨k, hk, hk'⟩
  obtain ⟨g₂', hns₂, hact₂⟩ := actsAsConj_in_coord hodd₂ h3₂ φ₂ hφ₂ hrange₂
    (fun x hx y hy => (hSet.comm y hy x hx).symm)
    (by rw [sup_comm K₂ K₁, hgen]; exact (t2C_C₁_normalizes hRem hSet.comm).2) hRem.diag₂
    ⟨k, by rw [sup_comm]; exact hk, hk'⟩
  have hcomm₁ : ∀ M : SL2 F₁, Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) (slConj g₁' M) =
      slConj g₁' (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M) := by
    intro M
    apply hφ₁
    calc φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) (slConj g₁' M))
        = f * φ₁ (slConj g₁' M) * f⁻¹ := (hσ₁ _).symm
      _ = f * (t' * φ₁ M * t'⁻¹) * f⁻¹ := by rw [hact₁ M]
      _ = (f * t') * φ₁ M * (f * t')⁻¹ := by group
      _ = (t' * f) * φ₁ M * (t' * f)⁻¹ := by rw [hft]
      _ = t' * (f * φ₁ M * f⁻¹) * t'⁻¹ := by group
      _ = t' * φ₁ (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M) * t'⁻¹ := by rw [hσ₁]
      _ = φ₁ (slConj g₁' (Matrix.SpecialLinearGroup.map (σ₁ : F₁ →+* F₁) M)) := hact₁ _
  have hcomm₂ : ∀ M : SL2 F₂, Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) (slConj g₂' M) =
      slConj g₂' (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M) := by
    intro M
    apply hφ₂
    calc φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) (slConj g₂' M))
        = f * φ₂ (slConj g₂' M) * f⁻¹ := (hσ₂ _).symm
      _ = f * (t' * φ₂ M * t'⁻¹) * f⁻¹ := by rw [hact₂ M]
      _ = (f * t') * φ₂ M * (f * t')⁻¹ := by group
      _ = (t' * f) * φ₂ M * (t' * f)⁻¹ := by rw [hft]
      _ = t' * (f * φ₂ M * f⁻¹) * t'⁻¹ := by group
      _ = t' * φ₂ (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M) * t'⁻¹ := by rw [hσ₂]
      _ = φ₂ (slConj g₂' (Matrix.SpecialLinearGroup.map (σ₂ : F₂ →+* F₂) M)) := hact₂ _
  obtain ⟨g₀₁, hns₁', hdesc₁⟩ := exists_fixedGL_of_commute σ₁ g₁' hcomm₁ hns₁
  obtain ⟨g₀₂, hns₂', hdesc₂⟩ := exists_fixedGL_of_commute σ₂ g₂' hcomm₂ hns₂
  have hmem₁ : ∀ M : SL2 F₁, φ₁ M ∈ K₁ := fun M => hrange₁ ▸ MonoidHom.mem_range.2 ⟨M, rfl⟩
  have hmem₂ : ∀ M : SL2 F₂, φ₂ M ∈ K₂ := fun M => hrange₂ ▸ MonoidHom.mem_range.2 ⟨M, rfl⟩
  have hodd' : Odd r := hodd
  have htwo : ∀ y : G, y * f = f * y → y * z = z * y → (∃ k : ℕ, y ^ (2 ^ k) = 1) →
      y ∈ ChartData.Y₀ (φ₁.comp (slFixIncl σ₁)) (φ₂.comp (slFixIncl σ₂)) t' := by
    intro y hyf hyz ⟨kk, hkk⟩
    have hyC : y ∈ oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set G)) :=
      mem_oPrimeResidualOf_of_pow (Subgroup.mem_centralizer_singleton_iff.2 hyz) ⟨kk, hkk⟩
    rw [← hgen'] at hyC
    obtain ⟨k₀, hk₀, h | h⟩ := exists_mul_of_mem_sup_zpowers ht'2 hnK' hyC
    all_goals
      have hkf : k₀ * f = f * k₀ := by
        first
        | (rw [h] at hyf; exact hyf)
        | (rw [h] at hyf
           have h1 : k₀ * f * t' = f * k₀ * t' := by
             calc k₀ * f * t' = k₀ * (f * t') := by group
               _ = k₀ * (t' * f) := by rw [hft]
               _ = (k₀ * t') * f := by group
               _ = f * (k₀ * t') := hyf
               _ = f * k₀ * t' := by group
           exact mul_right_cancel h1)
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hSet.comm hk₀
      obtain ⟨hfa, hfb⟩ := fixed_of_prod_fixed hSet.inter_eq.le hzz hz1 hfK₁ hfK₂ hfz hfr hodd' ha hb
        (by rw [← hkf]; group)
      have ha' : a ∈ (φ₁.comp (slFixIncl σ₁)).range := by
        rw [range_comp_slFixIncl φ₁ f σ₁ hφ₁ hσ₁, hrange₁]
        refine ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc a * f = (f * a * f⁻¹) * f := by rw [hfa]
          _ = f * a := by group
      have hb' : b ∈ (φ₂.comp (slFixIncl σ₂)).range := by
        rw [range_comp_slFixIncl φ₂ f σ₂ hφ₂ hσ₂, hrange₂]
        refine ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc b * f = (f * b * f⁻¹) * f := by rw [hfb]
          _ = f * b := by group
      have hab : a * b ∈ ChartData.Y₀ (φ₁.comp (slFixIncl σ₁)) (φ₂.comp (slFixIncl σ₂)) t' :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha'))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb'))
      first
      | (rw [h]; exact hab)
      | (rw [h]; exact Subgroup.mul_mem _ hab (Subgroup.mem_sup_right (Subgroup.mem_zpowers t')))
  have hψ₁inj : Function.Injective (φ₁.comp (slFixIncl σ₁)) := hφ₁.comp (slFixIncl_injective σ₁)
  have hψ₂inj : Function.Injective (φ₂.comp (slFixIncl σ₂)) := hφ₂.comp (slFixIncl_injective σ₂)
  refine ⟨t', ht'S, g₀₁, g₀₂, ⟨hψ₁inj, hψ₂inj, ?_, ?_, ?_, hzz, hz1, ?_, ht'2, ?_, ?_, hns₁', hns₂'⟩,
    ?_, ?_, hft.symm, hfz.symm, htwo⟩
  · intro M N
    exact hSet.comm _ (hmem₁ _) _ (hmem₂ _)
  · show φ₁ (slFixIncl σ₁ (negOne (fixF σ₁))) = z
    rw [slFixIncl_negOne, hneg₁]
  · show φ₂ (slFixIncl σ₂ (negOne (fixF σ₂))) = z
    rw [slFixIncl_negOne, hneg₂]
  · intro M N h
    have h1 : φ₁ (slFixIncl σ₁ M) ∈ K₁ ⊓ K₂ :=
      ⟨hmem₁ _, by have : φ₂ (slFixIncl σ₂ N) = φ₁ (slFixIncl σ₁ M) := h.symm
                   rw [← this]; exact hmem₂ _⟩
    rw [hSet.inter_eq] at h1
    rcases mem_zpowers_sq_cases hzz h1 with h2 | h2
    · left; exact h2
    · right; exact h2
  · intro M
    show t' * φ₁ (slFixIncl σ₁ M) * t'⁻¹ = φ₁ (slFixIncl σ₁ (slConj g₀₁ M))
    rw [hact₁, hdesc₁]
  · intro N
    show t' * φ₂ (slFixIncl σ₂ N) * t'⁻¹ = φ₂ (slFixIncl σ₂ (slConj g₀₂ N))
    rw [hact₂, hdesc₂]
  · intro M
    show φ₁ (slFixIncl σ₁ M) * f = f * φ₁ (slFixIncl σ₁ M)
    have := (centralizes_iff φ₁ hφ₁ f σ₁ hσ₁ (slFixIncl σ₁ M)).2
      ((mem_range_slFixIncl σ₁ _).1 ⟨M, rfl⟩)
    calc φ₁ (slFixIncl σ₁ M) * f = (f * φ₁ (slFixIncl σ₁ M) * f⁻¹) * f := by rw [this]
      _ = f * φ₁ (slFixIncl σ₁ M) := by group
  · intro M
    show φ₂ (slFixIncl σ₂ M) * f = f * φ₂ (slFixIncl σ₂ M)
    have := (centralizes_iff φ₂ hφ₂ f σ₂ hσ₂ (slFixIncl σ₂ M)).2
      ((mem_range_slFixIncl σ₂ _).1 ⟨M, rfl⟩)
    calc φ₂ (slFixIncl σ₂ M) * f = (f * φ₂ (slFixIncl σ₂ M) * f⁻¹) * f := by rw [this]
      _ = f * φ₂ (slFixIncl σ₂ M) := by group

end Charts

end CFSG.GH74.GLS.Stage4.Rest.F1Loc

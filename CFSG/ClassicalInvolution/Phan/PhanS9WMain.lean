module

public import CFSG.ClassicalInvolution.Phan.PhanS9WCorr
public import CFSG.ClassicalInvolution.Phan.PhanS9WNorm
public import CFSG.ClassicalInvolution.Phan.PhanS9WPlane

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] (D : KDat F K)

theorem exists_spin_move_normalized (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    {R : Submodule F (W7 F)} (hR : ((quadOdd 3 F).restrict R).Nondegenerate)
    (hdim : Module.finrank F R ≤ 4) {α : F} (hα : α ≠ 0) {a b a' b' : W7 F}
    (hRa : ∀ r ∈ R, polar (quadOdd 3 F) r a = 0) (hRb : ∀ r ∈ R, polar (quadOdd 3 F) r b = 0)
    (hab : polar (quadOdd 3 F) a b = 0) (ha : quadOdd 3 F a = α) (hb : quadOdd 3 F b = α)
    (hRa' : ∀ r ∈ R, polar (quadOdd 3 F) r a' = 0)
    (hRb' : ∀ r ∈ R, polar (quadOdd 3 F) r b' = 0)
    (hab' : polar (quadOdd 3 F) a' b' = 0) (ha' : quadOdd 3 F a' = α)
    (hb' : quadOdd 3 F b' = α) :
    ∃ g : spinGroup (quadOdd 3 F), (∀ r ∈ R, spinAction (quadOdd 3 F) g r = r) ∧
      ∃ c : K, c ≠ 0 ∧ actK (K := K) g (emb a + D.θ • emb b) = c • (emb a' + D.θ • emb b') := by
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by
    have := congrArg (algebraMap F K) h
    rwa [map_ofNat, map_zero] at this)
  have : Invertible (2 : F) := invertibleOfNonzero h2F
  have hQ : (quadOdd 3 F).Nondegenerate :=
    nondegenerate_of_nondegenerate_polarBilin (nondegenerate_polarBilin_quadOdd 3 F h2F)
  obtain ⟨Θ, hΘR, hΘa, hΘb⟩ := exists_isometry_plane (quadOdd 3 F) hR hα hRa hRb hab ha hb
    hRa' hRb' hab' ha' hb'
  let g₀ : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 F) :=
    ⟨Θ.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => Θ.map_app v⟩
  have hfin : Module.finrank F (W7 F) = 7 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hdim' : Module.finrank F R + 2 < Module.finrank F (W7 F) := by
    rw [hfin]
    omega
  obtain ⟨n, hn0, hnR, hna, hnb⟩ := exists_perp_vector (quadOdd 3 F) hQ hR hα hRa' hRb' hab' ha'
    hb' hdim'
  obtain ⟨g₁, hg₁R, hg₁a, hg₁b, hdet₁⟩ := exists_det_one_move hQ g₀ hΘR hΘa hΘb hn0 hnR hna hnb
  obtain ⟨h, hhR, hhdet, hhsn, c₀, hc₀, hhx⟩ := exists_rotation_correction D hodd hQ hα hRa'
    hRb' hab' ha' hb' (CliffordAlgebra.orthogonalSpinorNorm (quadOdd 3 F) hQ g₁)⁻¹
  have hd : QuadraticMap.orthogonalDet (quadOdd 3 F) (h * g₁) = 1 := by
    rw [map_mul, hhdet, hdet₁, one_mul]
  have hs : CliffordAlgebra.orthogonalSpinorNorm (quadOdd 3 F) hQ (h * g₁) = 1 := by
    rw [map_mul, hhsn, inv_mul_cancel]
  obtain ⟨y, hy⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spinAction_eq hQ (h * g₁) hd hs
  refine ⟨y, fun r hr => ?_, c₀, hc₀, ?_⟩
  · rw [hy, Subgroup.coe_mul, LinearEquiv.mul_apply, hg₁R r hr, hhR r hr]
  · have hcomp : actK (K := K) y = extK (h : W7 F ≃ₗ[F] W7 F).toLinearMap ∘ₗ
        extK (g₁ : W7 F ≃ₗ[F] W7 F).toLinearMap := by
      rw [actK, hy, ← extK_comp]
      rfl
    have h1 : extK (K := K) (g₁ : W7 F ≃ₗ[F] W7 F).toLinearMap (emb a + D.θ • emb b) =
        emb a' + D.θ • emb b' := by
      rw [map_add, map_smul, extK_emb, extK_emb, LinearEquiv.coe_coe, hg₁a, hg₁b]
    rw [hcomp, LinearMap.comp_apply, h1]
    exact hhx

theorem exists_spin_move_ff (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hn1 : ¬ IsSquare (-1 : F)) {R : Submodule F (W7 F)}
    (hR : ((quadOdd 3 F).restrict R).Nondegenerate) (hdim : Module.finrank F R ≤ 4)
    {x y : W7 K} (hx : IsFF7 D x) (hy : IsFF7 D y)
    (hxR : ∀ r ∈ R, polar (quadOdd 3 K) x (emb r) = 0)
    (hyR : ∀ r ∈ R, polar (quadOdd 3 K) y (emb r) = 0) :
    ∃ g : spinGroup (quadOdd 3 F), (∀ r ∈ R, spinAction (quadOdd 3 F) g r = r) ∧
      ∃ c : K, c ≠ 0 ∧ actK g x = c • y := by
  have _hn1 := hn1
  obtain ⟨a, b, rfl⟩ := exists_re_im_vec D h2 x
  obtain ⟨a', b', rfl⟩ := exists_re_im_vec D h2 y
  obtain ⟨hq, hab, ha0⟩ := ff_parts D h2 hx
  obtain ⟨hq', hab', ha0'⟩ := ff_parts D h2 hy
  have hxa : ∀ r ∈ R, polar (quadOdd 3 F) r a = 0 ∧ polar (quadOdd 3 F) r b = 0 :=
    fun r hr => by
      obtain ⟨h1, h3⟩ := polar_re_im_eq_zero D h2 (hxR r hr)
      exact ⟨by rw [QuadraticMap.polar_comm]; exact h1, by rw [QuadraticMap.polar_comm]; exact h3⟩
  have hya : ∀ r ∈ R, polar (quadOdd 3 F) a' r = 0 ∧ polar (quadOdd 3 F) b' r = 0 :=
    fun r hr => polar_re_im_eq_zero D h2 (hyR r hr)
  obtain ⟨μ, a'', b'', hμ, hμy, hqa, hqb, hab'', hperp⟩ :=
    exists_normalize D hodd h2 hab' hq' ha0' ha0
  have hya'' : ∀ r ∈ R, polar (quadOdd 3 F) r a'' = 0 ∧ polar (quadOdd 3 F) r b'' = 0 :=
    fun r hr => by
      obtain ⟨h1, h3⟩ := hperp r (hya r hr).1 (hya r hr).2
      exact ⟨by rw [QuadraticMap.polar_comm]; exact h1, by rw [QuadraticMap.polar_comm]; exact h3⟩
  obtain ⟨g, hgR, c, hc, hgx⟩ := exists_spin_move_normalized D hodd h2 hR hdim ha0
    (fun r hr => (hxa r hr).1) (fun r hr => (hxa r hr).2) hab rfl hq.symm
    (fun r hr => (hya'' r hr).1) (fun r hr => (hya'' r hr).2) hab'' hqa hqb
  refine ⟨g, hgR, c * μ, mul_ne_zero hc hμ, ?_⟩
  rw [hgx, ← hμy, smul_smul]

end CFSG.ClassicalInvolution.PhanB3.S

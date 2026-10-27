module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U3Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23Wit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CF23U3Mat
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_coset_fusion [Finite K] (hp2 : p ≠ 2) {G : Type} [Group G] {N : Subgroup G}
    (φ : N ≃* StatedProj (StatedSU 3 (p ^ f) K))
    {ρ : G →* MulAut (StatedProj (StatedSU 3 (p ^ f) K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : N, ρ w = MulAut.conj (φ w))
    (hZ : center (StatedProj (StatedSU 3 (p ^ f) K)) = ⊥) {α : G} (hα : orderOf α = 2)
    {A : GL (Fin 3) K}
    (hAu : uStar h (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1)
    {ψ : unitarySU p f K 3 →* unitarySU p f K 3}
    (hψ : ∀ g, ρ α (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 3) (Fin 3) K))
    {c : K} (hAA : (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K).map h.bar =
      c • 1) :
    ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x := by
  classical
  intro x hx hαx
  set β := GeneralLinearGroup.map (n := Fin 3) h.bar with hβ
  have hβv : ∀ Y : GL (Fin 3) K, ((β Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (Y : Matrix (Fin 3) (Fin 3) K).map h.bar := fun Y => GeneralLinearGroup.val_map_apply _ _
  have hββ : ∀ Y : GL (Fin 3) K, β (β Y) = Y := fun Y => by
    apply Units.ext
    rw [hβv, hβv]
    ext i j
    simp [h.bar_bar]
  have hψG : ∀ g, (ψ g : GL (Fin 3) K) = A * β (g : GL (Fin 3) K) * A⁻¹ := fun g =>
    Units.ext (by rw [hψA, Units.val_mul, Units.val_mul, hβv])
  obtain ⟨M, hM⟩ := QuotientGroup.mk_surjective (φ ⟨α⁻¹ * x, hαx⟩)
  have hρn : ρ (α⁻¹ * x) = MulAut.conj (QuotientGroup.mk M) := by
    rw [hM]
    exact hρW ⟨α⁻¹ * x, hαx⟩
  have hα2 : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hψM : ψ M * M ∈ scal3 p f K := by
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    have e1 : ρ α * MulAut.conj (QuotientGroup.mk M) * ρ α * MulAut.conj (QuotientGroup.mk M) =
        1 := by
      rw [← hρn, ← map_mul, ← map_mul, ← map_mul]
      have : α * (α⁻¹ * x) * α * (α⁻¹ * x) = x * x := by group
      rw [this, hx2, map_one]
    have e2 : ρ α * MulAut.conj (QuotientGroup.mk M) * ρ α =
        MulAut.conj (ρ α (QuotientGroup.mk M)) := by
      have hραρα : ρ α * ρ α = 1 := by rw [← map_mul, hα2, map_one]
      ext y
      have hy : ρ α (ρ α y) = y := by
        rw [← MulAut.mul_apply, hραρα, MulAut.one_apply]
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hy]
    rw [e2, hψ, ← map_mul] at e1
    have e3 := OddClassSelector.conj_injective hZ (e1.trans (map_one _).symm)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at e3
    exact e3
  obtain ⟨s, hs⟩ := val_of_mem_scal3 hψM
  set A' := A * β (M : GL (Fin 3) K) with hA'
  have hMu : uStar h ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    ((mem_unitarySU_iff h).mp M.2).2
  have hMbu : uStar h ((β (M : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((β (M : GL (Fin 3) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h1 := congrArg (fun Y : Matrix (Fin 3) (Fin 3) K => Y.map h.bar) hMu
    simp only [CatFactsL4U4.UnitaryOut.uStar, Matrix.map_mul, Matrix.transpose_map,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at h1
    rw [hβv, CatFactsL4U4.UnitaryOut.uStar]
    exact h1
  have hA'u : uStar h (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hA', Units.val_mul]
    exact Catalog7U4.unitary_mul h hAu hMbu
  have hcen : ∀ (t : Kˣ) (Y : GL (Fin 3) K), GeneralLinearGroup.scalar (Fin 3) t * Y =
      Y * GeneralLinearGroup.scalar (Fin 3) t := by
    intro t Y
    have hz : GeneralLinearGroup.scalar (Fin 3) t ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨t, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz Y).symm
  have hc0 : c ≠ 0 := ne_zero_of_mul_bar h hAA (by norm_num)
  have hAAg : A * β A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := Units.ext (by
    rw [Units.val_mul, hβv, hAA, GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl)
  have hψMg : (ψ M : GL (Fin 3) K) * M = GeneralLinearGroup.scalar (Fin 3) s := Units.ext (by
    have hs' := hs
    rw [Subgroup.coe_mul] at hs'
    rw [hs', GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl)
  have hA'A' : (A' : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K).map h.bar =
      ((c : K) * s) • 1 := by
    have e1 : A' * β A' = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0 * s) := by
      have e2 : A' * β A' = (A * β (M : GL (Fin 3) K) * A⁻¹) * (A * β A) * M := by
        rw [hA', map_mul, hββ]
        group
      rw [e2, ← hψG, hAAg, mul_assoc, hcen, ← mul_assoc, hψMg, ← map_mul, mul_comm]
    have e3 := congrArg (fun Y : GL (Fin 3) K => (Y : Matrix (Fin 3) (Fin 3) K)) e1
    simp only [Units.val_mul, hβv, GeneralLinearGroup.coe_scalar] at e3
    rw [e3, Units.val_mk0, Matrix.smul_one_eq_diagonal]
    rfl
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = (A : Matrix (Fin 3) (Fin 3) K).det := by
    rw [hA', Units.val_mul, det_mul, hβv, show ((M : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).map h.bar = h.bar.mapMatrix ((M : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) from rfl, ← RingHom.map_det, ((mem_unitarySU_iff h).mp M.2).1,
      map_one, mul_one]
  obtain ⟨G₁, hG₁⟩ := exists_su_conj_three h hp2 hAu hA'u hAA hA'A' hdet
  have hG₁g : (G₁ : GL (Fin 3) K) * A * β ((G₁ : GL (Fin 3) K)⁻¹) = A' :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, hβv]; exact hG₁)
  set θ : unitarySU p f K 3 →* StatedProj (StatedSU 3 (p ^ f) K) :=
    QuotientGroup.mk' (scal3 p f K) with hθ
  have hψθ : ∀ g, ρ α (θ g) = θ (ψ g) := hψ
  have hMθ : (QuotientGroup.mk M : StatedProj (StatedSU 3 (p ^ f) K)) = θ M := rfl
  refine ⟨φ.symm (θ G₁⁻¹), (φ.symm (θ G₁⁻¹)).2, ?_⟩
  apply hinj
  have ex : x = α * (α⁻¹ * x) := by group
  rw [map_mul, map_mul, map_inv, hρW, MulEquiv.apply_symm_apply, ex, map_mul, hρn, hMθ]
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scal3 p f K) y
  have e1 : MulAut.conj (θ G₁⁻¹) (θ g) = θ (G₁⁻¹ * g * G₁) := by
    rw [MulAut.conj_apply, ← map_inv θ, inv_inv, ← map_mul, ← map_mul]
  have eL : ((MulAut.conj (θ G₁⁻¹))⁻¹ * ρ α * MulAut.conj (θ G₁⁻¹)) (θ g) =
      θ (G₁ * ψ (G₁⁻¹ * g * G₁) * G₁⁻¹) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, e1, hψθ, MulAut.conj_inv_apply, ← map_inv θ, inv_inv,
      ← map_mul, ← map_mul]
  have eR : (ρ α * MulAut.conj (θ M)) (θ g) = θ (ψ (M * g * M⁻¹)) := by
    rw [MulAut.mul_apply, MulAut.conj_apply, ← map_inv θ, ← map_mul, ← map_mul, hψθ]
  rw [eL, eR]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hψG, hψG, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
  have hA'i : A'⁻¹ = β (G₁ : GL (Fin 3) K) * A⁻¹ * (G₁ : GL (Fin 3) K)⁻¹ := by
    rw [← hG₁g, map_inv]
    group
  simp only [map_mul, map_inv]
  calc (G₁ : GL (Fin 3) K) * (A * ((β (G₁ : GL (Fin 3) K))⁻¹ * β (g : GL (Fin 3) K) *
        β (G₁ : GL (Fin 3) K)) * A⁻¹) * (G₁ : GL (Fin 3) K)⁻¹ =
      ((G₁ : GL (Fin 3) K) * A * (β (G₁ : GL (Fin 3) K))⁻¹) * β (g : GL (Fin 3) K) *
        (β (G₁ : GL (Fin 3) K) * A⁻¹ * (G₁ : GL (Fin 3) K)⁻¹) := by group
    _ = A' * β (g : GL (Fin 3) K) * A'⁻¹ := by rw [← map_inv, hG₁g, hA'i]
    _ = A * (β (M : GL (Fin 3) K) * β (g : GL (Fin 3) K) * (β (M : GL (Fin 3) K))⁻¹) * A⁻¹ := by
        rw [hA']
        group

theorem cf23InnerFusionFor_PSU3 :
    CF23InnerFusionFor fun Y _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel Y .PSU 3 p f := by
  intro G _ _ N hN hC hτ α J hα hJN hJα hJ hstd hsm hZ hexc
  classical
  obtain ⟨p, f, hp, hp2, hf, hM⟩ := hτ
  have := hN
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hM
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := hud.finite
  have hnq : (3, p ^ f) ≠ (3, 2) := fun h3 => by
    have h2 := congrArg Prod.snd h3
    simp only at h2
    have : p ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 (le_refl 3) hnq
  have hnab : ∃ x y : StatedProj (StatedSU 3 (p ^ f) K), x * y ≠ y * x := by
    by_contra hc
    push Not at hc
    have hWle : N ≤ centralizer (N : Set G) := by
      intro w hw
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := hc (φ ⟨v, hv⟩) (φ ⟨w, hw⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (φ.injective h1)
    rw [hC] at hWle
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSU 3 (p ^ f) K))
    apply hx
    have hw := hWle (φ.symm x).2
    rw [mem_bot] at hw
    have h1 : φ.symm x = 1 := Subtype.ext hw
    rw [← φ.apply_symm_apply x, h1, map_one]
  have hZP := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hC φ hZP
  have hLCW := isComponentOf_of_cf23 hJN hJα hJ
  obtain ⟨-, hCWimg, -⟩ := OutcomeLocal.socle_images hinj φ hρW α
  have hL₁ := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hLCW
  rw [hCWimg] at hL₁
  have hcj := OddClassSelector.conj_injective hZP
  obtain ⟨hX, hXmap⟩ := OddClassSelector.isComponentOf_comap_conj hcj hL₁
  let eLX : J ≃* (J.map ρ).comap MulAut.conj :=
    (J.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      (((J.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)
  have hsX : SmallSource ((J.map ρ).comap MulAut.conj) :=
    OddClassSelector.smallSource_of_mulEquiv eLX (smallSource_of_cf23 hsm hZ)
  have hα2 : α * α = 1 := by rw [← pow_two, ← hα, pow_orderOf_eq_one]
  have hσ : ∀ y, ρ α (ρ α y) = y := by
    intro y
    rw [← MulAut.mul_apply, ← map_mul, hα2, map_one, MulAut.one_apply]
  have hσ1 : ρ α ≠ 1 := by
    intro h1
    have h2 : orderOf (ρ α) = orderOf α := orderOf_injective ρ hinj α
    rw [h1, orderOf_one, hα] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := exists_lift3 hud hp2 (ρ α) hσ
  rcases hcase with ⟨hψA, c₀, hAA⟩ | ⟨hψA, c, hAA⟩
  · exact (u3_inner_false hud hp2 hσ1 hX hsX hAu hψ hψA hAA).elim
  · exact concl_of_coset hα hJN hJα hZ
      (u3_coset_fusion hud hp2 φ hinj hρW hZP hα hAu hψ hψA hAA)

end CFSG.ComponentClassification.GSThmB.CF23I

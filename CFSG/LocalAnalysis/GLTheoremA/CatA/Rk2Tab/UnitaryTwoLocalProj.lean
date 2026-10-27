module

public import CFSG.Walter.Bender1970.S2.OddFitting
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryLeviCount

public section


namespace CFSG.LocalAnalysis.GLTheoremA

open Module CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KFU
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {f d : ℕ}

theorem center_statedSU_eq_scalars (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d) :
    Subgroup.center (StatedSU d (2 ^ f) F) =
      (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ f) F) := by
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (K := F) (p := 2) (f := f) hK
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK d]
  exact CFSG.ClassicalInvolution.Phan.center_SUid_eq hσ hd

theorem odd_card_center_le (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (C : Subgroup (StatedSU d (2 ^ f) F))
    (hC : C ≤ Subgroup.center (StatedSU d (2 ^ f) F)) : Odd (Nat.card C) := by
  have hdvd : Nat.card C ∣ Nat.gcd d (2 ^ f + 1) := by
    refine (Subgroup.card_dvd_of_le hC).trans ?_
    rw [center_statedSU_eq_scalars hK hd]
    exact (CFSG.LinearGroups.unitary_scalar_kernel (K := F) Nat.prime_two hK (by omega : 1 ≤ d)).2.2 ▸
      dvd_rfl
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · exfalso
      rw [h0, pow_zero] at hK
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hq : Odd (2 ^ f + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
    rw [pow_succ]
    exact ⟨2 ^ k, by ring⟩
  exact Odd.of_dvd_nat hq (hdvd.trans (Nat.gcd_dvd_right d (2 ^ f + 1)))

abbrev ProjectiveRankLemma (F : Type) [Field F] (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (R : Subgroup (V ≃ₗ[F] V)), IsPGroup r R →
    (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
    (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ r) v = a • v) →
    Nat.card R ≤ r ^ (Module.finrank F V - 1) *
      Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}

structure ProjectiveSetup (F : Type) [Field F] (f d r : ℕ)
    (Ff : ReflForm F (Fin d → F))
    (ρ : StatedSU d (2 ^ f) F →* Module.End F (Fin d → F))
    (Er : Subgroup (StatedSU d (2 ^ f) F)) (CrE : Subgroup Er) where
  W : Submodule F (Fin d → F)
  hU : UnitaryFieldData 2 f F
  hWiso : Ff.IsTotallyIsotropic W
  hWE : ∀ g ∈ Er, ∀ w ∈ W, ρ g w ∈ W
  hPE : ∀ g ∈ Er, ∀ v ∈ Ff.perp W, ρ g v ∈ Ff.perp W
  ρW : Er →* (W ≃ₗ[F] W)
  ρM : Er →* (FlagSplit.perpQuot Ff W ≃ₗ[F] FlagSplit.perpQuot Ff W)
  hρW_apply : ∀ (x : Er) (w : W), (ρW x w : Fin d → F) = ρ x w
  hρM_mk : ∀ (x : Er) (v : Ff.perp W),
    ρM x (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (⟨ρ x (v : Fin d → F), hPE x x.2 (v : Fin d → F) v.2⟩ : Ff.perp W)
  k : ℕ
  m : ℕ
  hk_eq : k = Module.finrank F W
  hm_eq : m = Module.finrank F (FlagSplit.perpQuot Ff W)
  hk : 1 ≤ k
  h2k : 2 * k ≤ d
  hm : m = d - 2 * k
  N : Subgroup Er
  hNcomm : ∀ x y : N, x * y = y * x
  hNr : ∀ x : N, x ^ r ∈ CrE.subgroupOf N
  lam : N → F
  mu : N → F
  lam_spec : ∀ (x : N) (w : W), ρW (x : Er) w = lam x • w
  mu_spec : ∀ (x : N) (q : FlagSplit.perpQuot Ff W), ρM (x : Er) q = mu x • q
  hpair : Function.Injective fun x : N => (lam x, mu x)
  hlam_root : ∀ x : N, (x : Er) ^ r = 1 → lam x ^ r = 1
  hmu_root : ∀ x : N, m ≠ 0 → (x : Er) ^ r = 1 → mu x ^ r = 1
  hlam_inj0 : m = 0 → Function.Injective lam
  hErN : N.index ≤ r ^ (k - 1) * r ^ (m - 1)
  hfac : CrE.index = N.index * (CrE.subgroupOf N).index

theorem projective_setup_exists
    (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (C : Subgroup (StatedSU d (2 ^ f) F))
    (hC : C ≤ Subgroup.center (StatedSU d (2 ^ f) F))
    {R Er : Subgroup (StatedSU d (2 ^ f) F)} (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hErNormR : Er ≤ Subgroup.normalizer (R : Set (StatedSU d (2 ^ f) F)))
    (hEr2 : IsPGroup r Er)
    (CrE : Subgroup Er) [CrE.Normal] (hB : ∀ a : Er, a ^ r ∈ CrE)
    (hErDer : commutator Er ≤ CrE)
    (hCrC : ∀ c ∈ CrE, (c : StatedSU d (2 ^ f) F) ∈ C)
    (hPRL : ProjectiveRankLemma F r) :
    ∃ D : ProjectiveSetup F f d r (unitaryForm 2 f hK d)
      (natRep (StatedSU d (2 ^ f) F)) Er CrE, True := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  let S : Subgroup (GL (Fin d) F) := StatedSU d (2 ^ f) F
  have hCS : C ≤ Subgroup.center S := hC
  let Ff : ReflForm F (Fin d → F) := unitaryForm 2 f hK d
  let ρ : S →* Module.End F (Fin d → F) := natRep S
  have hρ : IsIsometric Ff ρ := isIsometric_natRep_statedSU hK d
  have hinj : Function.Injective ρ := natRep_injective S
  have hD : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · exfalso
      rw [h0, pow_zero, one_pow] at hK
      have := Finite.one_lt_card (α := F)
      omega
    · exact h
  have hU : UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨W, hW0, hWiso, hWE⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_invariant_isotropic Ff ρ hρ hinj hR2 hR1 hErNormR
  let k : ℕ := Module.finrank F W
  let M : Type := FlagSplit.perpQuot Ff W
  let m : ℕ := Module.finrank F M
  have hm : m = d - 2 * k := by
    dsimp only [m, M, k]
    rw [FlagSplit.finrank_perpQuot Ff hWiso, hD]
  have hkpos : 1 ≤ k := Submodule.one_le_finrank_iff.mpr hW0
  have h2k : 2 * k ≤ d := by
    have h1 := Ff.finrank_perp W
    have h2 : Module.finrank F W ≤ Module.finrank F (Ff.perp W) := Submodule.finrank_mono hWiso
    rw [hD] at h1
    omega
  let ρEr : Er →* Module.End F (Fin d → F) := ρ.comp Er.subtype
  have hWE' : ∀ g : Er, ∀ w ∈ W, ρEr g w ∈ W := fun g w hw => hWE g g.2 w hw
  have hPE : ∀ g : Er, ∀ v ∈ Ff.perp W, ρEr g v ∈ Ff.perp W := by
    intro g v hv
    exact hρ.apply_mem_perp_of_forall (fun w hw => hWE g⁻¹ (Er.inv_mem g.2) w hw) hv
  let ρW : Er →* (W ≃ₗ[F] W) :=
    CFSG.RankThree.PartOne.LIT.restrictAction (FlagSplit.repAut ρEr) W hWE'
  let ρM : Er →* (M ≃ₗ[F] M) :=
    FlagSplit.repAut (FlagSplit.quotRep ρEr W (Ff.perp W) hWE' hPE)

  have hodd : ∀ g : Er, Odd (orderOf g) := by
    intro g
    obtain ⟨j, hj⟩ := hEr2.exists_orderOf_eq_pow g
    rw [hj]
    exact (hr.odd_of_ne_two hr2).pow

  have hker : ∀ g : Er, ρW g = 1 → ρM g = 1 → g = 1 := by
    intro g h1 h2
    have hoddS : Odd (orderOf ((g : Er) : S)) := by
      rw [Subgroup.orderOf_coe]
      exact hodd g
    refine Subtype.ext (eq_one_of_fixes_flag_of_odd (g := ((g : Er) : S)) (W := W)
      Ff ρ hρ hinj hoddS ?_ ?_)
    · intro w hw
      have hw' := congrArg (fun e : W ≃ₗ[F] W => e ⟨w, hw⟩) h1
      exact congrArg Subtype.val hw'
    · intro v hv
      have h3 : (Submodule.Quotient.mk ⟨ρEr g v, hPE g v hv⟩ : M) =
          Submodule.Quotient.mk ⟨v, hv⟩ :=
        LinearEquiv.congr_fun h2 (Submodule.Quotient.mk ⟨v, hv⟩)
      exact (Submodule.Quotient.eq (W.comap (Ff.perp W).subtype)).mp h3

  have hCW : ∀ c : Er, c ∈ CrE → ∃ a : F, ∀ w : W, ρW c w = a • w := by
    intro c hc
    have hcS : (c : S) ∈ C := hCrC c hc
    have hcen : (c : S) ∈ Subgroup.center S := hCS hcS
    have hsc : (c : S) ∈ (StatedScalars (Fin d) F).subgroupOf S := by
      rwa [← center_statedSU_eq_scalars hK hd]
    obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.Census.exists_natRep_eq_smul hsc
    refine ⟨a, fun w => ?_⟩
    apply Subtype.ext
    change (natRep S) (c : S) (w : Fin d → F) = a • (w : Fin d → F)
    simpa using LinearMap.congr_fun ha (w : Fin d → F)
  have hCM : ∀ c : Er, c ∈ CrE → ∃ a : F, ∀ q : M, ρM c q = a • q := by
    intro c hc
    have hcS : (c : S) ∈ C := hCrC c hc
    have hcen : (c : S) ∈ Subgroup.center S := hCS hcS
    have hsc : (c : S) ∈ (StatedScalars (Fin d) F).subgroupOf S := by
      rwa [← center_statedSU_eq_scalars hK hd]
    obtain ⟨a, ha⟩ := CFSG.RankThree.PartTwo.Census.exists_natRep_eq_smul hsc
    refine ⟨a, fun q => ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H v =>
        have hv : (v : Fin d → F) ∈ Ff.perp W := v.2
        have hmv : a • (v : Fin d → F) ∈ Ff.perp W := by
          rw [Ff.mem_perp]
          intro w hw
          rw [Ff.smul_right, (Ff.mem_perp.mp v.2) w hw, mul_zero]
        have h1 : (ρM c) (Submodule.Quotient.mk v) =
            (Submodule.Quotient.mk (⟨ρEr c (v : Fin d → F), hPE c (v : Fin d → F) hv⟩ :
              Ff.perp W) : M) := rfl
        rw [h1]
        have h2 : ρEr c (v : Fin d → F) = a • (v : Fin d → F) := by
          change (natRep S) (c : S) (v : Fin d → F) = a • (v : Fin d → F)
          simpa using LinearMap.congr_fun ha (v : Fin d → F)
        have hsub : (⟨ρEr c (v : Fin d → F), hPE c (v : Fin d → F) hv⟩ : Ff.perp W) =
            ⟨a • (v : Fin d → F), hmv⟩ := Subtype.ext h2
        rw [hsub, ← Submodule.Quotient.mk_smul]
        rfl

  let AW : Subgroup (W ≃ₗ[F] W) := ρW.range
  let BW : Subgroup (M ≃ₗ[F] M) := ρM.range
  let AWs : Subgroup (W ≃ₗ[F] W) := AW ⊓ scalars F W
  let BWs : Subgroup (M ≃ₗ[F] M) := BW ⊓ scalars F M
  haveI : Finite (W ≃ₗ[F] W) := FlagSplit.finite_linearEquiv (K := F)
  haveI : Finite (M ≃ₗ[F] M) := FlagSplit.finite_linearEquiv (K := F)
  have hAWr : IsPGroup r AW :=
    hEr2.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
  have hBWr : IsPGroup r BW :=
    hEr2.of_surjective ρM.rangeRestrict ρM.rangeRestrict_surjective
  have hcommW : ∀ x ∈ AW, ∀ y ∈ AW, ∃ a : F, ∀ v : W,
      (x * y * x⁻¹ * y⁻¹) v = a • v := by
    rintro x ⟨xg, rfl⟩ y ⟨yg, rfl⟩
    have hmem : (xg * yg * xg⁻¹ * yg⁻¹) ∈ CrE := by
      have h1 : ⁅xg, yg⁆ ∈ commutator Er :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top xg) (Subgroup.mem_top yg)
      have h2 : ⁅xg, yg⁆ ∈ CrE := hErDer h1
      rwa [commutatorElement_def] at h2
    obtain ⟨a, ha⟩ := hCW _ hmem
    refine ⟨a, fun v => ?_⟩
    have h1 : (ρW xg * ρW yg * (ρW xg)⁻¹ * (ρW yg)⁻¹) =
        ρW (xg * yg * xg⁻¹ * yg⁻¹) := by
      simp only [map_mul, map_inv]
    rw [h1]
    exact ha v
  have hpowW : ∀ x ∈ AW, ∃ a : F, ∀ v : W, (x ^ r) v = a • v := by
    rintro x ⟨xg, rfl⟩
    obtain ⟨a, ha⟩ := hCW _ (hB xg)
    refine ⟨a, fun v => ?_⟩
    have h1 : (ρW xg) ^ r = ρW (xg ^ r) := (map_pow ρW xg r).symm
    rw [h1]
    exact ha v
  have hcommM : ∀ x ∈ BW, ∀ y ∈ BW, ∃ a : F, ∀ v : M,
      (x * y * x⁻¹ * y⁻¹) v = a • v := by
    rintro x ⟨xg, rfl⟩ y ⟨yg, rfl⟩
    have hmem : (xg * yg * xg⁻¹ * yg⁻¹) ∈ CrE := by
      have h1 : ⁅xg, yg⁆ ∈ commutator Er :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top xg) (Subgroup.mem_top yg)
      have h2 : ⁅xg, yg⁆ ∈ CrE := hErDer h1
      rwa [commutatorElement_def] at h2
    obtain ⟨a, ha⟩ := hCM _ hmem
    refine ⟨a, fun v => ?_⟩
    have h1 : (ρM xg * ρM yg * (ρM xg)⁻¹ * (ρM yg)⁻¹) =
        ρM (xg * yg * xg⁻¹ * yg⁻¹) := by
      simp only [map_mul, map_inv]
    rw [h1]
    exact ha v
  have hpowM : ∀ x ∈ BW, ∃ a : F, ∀ v : M, (x ^ r) v = a • v := by
    rintro x ⟨xg, rfl⟩
    obtain ⟨a, ha⟩ := hCM _ (hB xg)
    refine ⟨a, fun v => ?_⟩
    have h1 : (ρM xg) ^ r = ρM (xg ^ r) := (map_pow ρM xg r).symm
    rw [h1]
    exact ha v
  have hAq : Nat.card (AW ⧸ AWs.subgroupOf AW) ≤ r ^ (k - 1) := by
    refine card_quotient_scalar_le_of_card_le AW ?_
    have h := hPRL W AW hAWr hcommW hpowW
    exact h
  have hBq : Nat.card (BW ⧸ BWs.subgroupOf BW) ≤ r ^ (m - 1) := by
    refine card_quotient_scalar_le_of_card_le BW ?_
    have h := hPRL M BW hBWr hcommM hpowM
    exact h

  let φW : Er →* AW ⧸ AWs.subgroupOf AW :=
    (QuotientGroup.mk' (AWs.subgroupOf AW)).comp ρW.rangeRestrict
  let φM : Er →* BW ⧸ BWs.subgroupOf BW :=
    (QuotientGroup.mk' (BWs.subgroupOf BW)).comp ρM.rangeRestrict
  let N : Subgroup Er := φW.ker ⊓ φM.ker
  have hNmem : ∀ x : Er, x ∈ N ↔ ρW x ∈ scalars F W ∧
      ρM x ∈ scalars F M := by
    intro x
    constructor
    · intro hx
      have h1 : φW x = 1 := (Subgroup.mem_inf.mp hx).1
      have h2 : φM x = 1 := (Subgroup.mem_inf.mp hx).2
      constructor
      · have hx1 : ρW.rangeRestrict x ∈ AWs.subgroupOf AW :=
          (QuotientGroup.eq_one_iff _).mp h1
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx1)).2
      · have hx2 : ρM.rangeRestrict x ∈ BWs.subgroupOf BW :=
          (QuotientGroup.eq_one_iff _).mp h2
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx2)).2
    · rintro ⟨h1, h2⟩
      exact Subgroup.mem_inf.mpr ⟨by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(ρW.rangeRestrict x).2, h1⟩, by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(ρM.rangeRestrict x).2, h2⟩⟩
  have hErN : Nat.card (Er ⧸ N) ≤ r ^ (k - 1) * r ^ (m - 1) := by
    have hφW : Function.Surjective φW :=
      (QuotientGroup.mk'_surjective _).comp ρW.rangeRestrict_surjective
    have hφM : Function.Surjective φM :=
      (QuotientGroup.mk'_surjective _).comp ρM.rangeRestrict_surjective
    have hrangeW : Nat.card φW.range = Nat.card (AW ⧸ AWs.subgroupOf AW) := by
      rw [MonoidHom.range_eq_top.mpr hφW]
      simp
    have hrangeM : Nat.card φM.range = Nat.card (BW ⧸ BWs.subgroupOf BW) := by
      rw [MonoidHom.range_eq_top.mpr hφM]
      simp
    change (φW.ker ⊓ φM.ker).index ≤ r ^ (k - 1) * r ^ (m - 1)
    have h : (φW.ker ⊓ φM.ker).index ≤ φW.ker.index * φM.ker.index :=
      Subgroup.index_inf_le
    rw [Subgroup.index_ker, Subgroup.index_ker, hrangeW, hrangeM] at h
    exact h.trans (Nat.mul_le_mul hAq hBq)
  have hCrN : CrE ≤ N := by
    intro c hc
    rw [hNmem]
    exact ⟨mem_scalars.mpr (hCW c hc), mem_scalars.mpr (hCM c hc)⟩
  have hNcomm : ∀ x y : N, x * y = y * x := by
    intro x y
    have hxW : ρW (x : Er) ∈ scalars F W :=
      ((hNmem (x : Er)).mp x.2).1
    have hyW : ρW (y : Er) ∈ scalars F W :=
      ((hNmem (y : Er)).mp y.2).1
    have hxM : ρM (x : Er) ∈ scalars F M :=
      ((hNmem (x : Er)).mp x.2).2
    have hyM : ρM (y : Er) ∈ scalars F M :=
      ((hNmem (y : Er)).mp y.2).2
    have hmem : ((x : Er) * (y : Er) * (x : Er)⁻¹ * (y : Er)⁻¹) ∈ CrE := by
      have h1 : ⁅(x : Er), (y : Er)⁆ ∈ commutator Er :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top (x : Er)) (Subgroup.mem_top (y : Er))
      have h2 : ⁅(x : Er), (y : Er)⁆ ∈ CrE := hErDer h1
      rwa [commutatorElement_def] at h2
    have h1 : ρW ((x : Er) * (y : Er) * (x : Er)⁻¹ * (y : Er)⁻¹) = 1 := by
      have hcomm : ρW (x : Er) * ρW (y : Er) = ρW (y : Er) * ρW (x : Er) :=
        (Subgroup.mem_center_iff.mp ((scalars_le_center F W) hyW))
          (ρW (x : Er))
      have hz : ⁅ρW (x : Er), ρW (y : Er)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      simpa only [commutatorElement_def, map_mul, map_inv] using hz
    have h2 : ρM ((x : Er) * (y : Er) * (x : Er)⁻¹ * (y : Er)⁻¹) = 1 := by
      have hcomm : ρM (x : Er) * ρM (y : Er) = ρM (y : Er) * ρM (x : Er) :=
        (Subgroup.mem_center_iff.mp ((scalars_le_center F M) hyM))
          (ρM (x : Er))
      have hz : ⁅ρM (x : Er), ρM (y : Er)⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      simpa only [commutatorElement_def, map_mul, map_inv] using hz
    have hz : (x : Er) * (y : Er) * (x : Er)⁻¹ * (y : Er)⁻¹ = 1 := hker _ h1 h2
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp (by
      simpa [commutatorElement_def] using hz))
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hNcomm }
  have hNr : ∀ x : N, x ^ r ∈ CrE.subgroupOf N := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    simpa using hB (x : Er)
  have hNquot : Nat.card (N ⧸ CrE.subgroupOf N) ≤
      Nat.card (MonoidHom.ker (powMonoidHom r : N →* N)) :=
    CFSG.GroupTheory.card_quotient_le_card_pow_torsion (CrE.subgroupOf N) hNr

  have hlam : ∀ x : N, ∃ a : F, ∀ w : W, ρW (x : Er) w = a • w :=
    fun x => mem_scalars.mp ((hNmem (x : Er)).mp x.2).1
  have hmu : ∀ x : N, ∃ a : F, ∀ w : M, ρM (x : Er) w = a • w :=
    fun x => mem_scalars.mp ((hNmem (x : Er)).mp x.2).2
  let lam : N → F := fun x => Classical.choose (hlam x)
  have lam_spec : ∀ (x : N) (w : W), ρW (x : Er) w = lam x • w :=
    fun x => Classical.choose_spec (hlam x)
  let mu : N → F := fun x => Classical.choose (hmu x)
  have mu_spec : ∀ (x : N) (w : M), ρM (x : Er) w = mu x • w :=
    fun x => Classical.choose_spec (hmu x)
  have hpair : Function.Injective (fun x : N => (lam x, mu x)) := by
    rintro x y hxy
    have hxy1 : lam x = lam y := congrArg Prod.fst hxy
    have hxy2 : mu x = mu y := congrArg Prod.snd hxy
    have hWxy : ρW (x : Er) = ρW (y : Er) := by
      refine LinearEquiv.ext fun w => ?_
      rw [lam_spec, lam_spec, hxy1]
    have hMxy : ρM (x : Er) = ρM (y : Er) := by
      refine LinearEquiv.ext fun w => ?_
      rw [mu_spec, mu_spec, hxy2]
    have hz : (x : Er) * (y : Er)⁻¹ = 1 := by
      apply hker
      · rw [map_mul, map_inv, hWxy, mul_inv_cancel]
      · rw [map_mul, map_inv, hMxy, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp hz)
  have hlam_root : ∀ x : N, (x : Er) ^ r = 1 → lam x ^ r = 1 := by
    intro x hx
    obtain ⟨w0, hw0W, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have h1 : (ρW (x : Er)) ^ r = 1 := by rw [← map_pow, hx, map_one]
    have hpow : ∀ n : ℕ, ((ρW (x : Er)) ^ n) (⟨w0, hw0W⟩ : W) =
        (lam x ^ n) • (⟨w0, hw0W⟩ : W) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ']
          change (ρW (x : Er)) (((ρW (x : Er)) ^ n) ⟨w0, hw0W⟩) = _
          rw [ih, map_smul, lam_spec, smul_smul, ← pow_succ]
    have h3' : (lam x ^ r) • (⟨w0, hw0W⟩ : W) = ⟨w0, hw0W⟩ := by
      rw [← hpow r, h1]
      rfl
    have h4 : (lam x ^ r - 1) • (⟨w0, hw0W⟩ : W) = 0 := by
      apply Subtype.ext
      change (lam x ^ r - 1) • (w0 : Fin d → F) = 0
      rw [sub_smul, one_smul]
      have h3v : (lam x ^ r) • (w0 : Fin d → F) = w0 := congrArg Subtype.val h3'
      rw [h3v, sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (Subtype.ext_iff.mp h) hw0ne
  have hmu_root : ∀ x : N, m ≠ 0 → (x : Er) ^ r = 1 → mu x ^ r = 1 := by
    intro x hm0 hx
    have hpos : 0 < Module.finrank F M := by omega
    letI : Nontrivial M := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨w0, hw0⟩ := exists_ne (0 : M)
    have h1 : (ρM (x : Er)) ^ r = 1 := by rw [← map_pow, hx, map_one]
    have hpow : ∀ n : ℕ, ((ρM (x : Er)) ^ n) w0 = (mu x ^ n) • w0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ']
          change (ρM (x : Er)) (((ρM (x : Er)) ^ n) w0) = _
          rw [ih, map_smul, mu_spec, smul_smul, ← pow_succ]
    have h3' : (mu x ^ r) • w0 = w0 := by
      rw [← hpow r, h1]
      rfl
    have h4 : (mu x ^ r - 1) • w0 = 0 := by
      rw [sub_smul, one_smul, h3', sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0

  have hfac : CrE.index = N.index * (CrE.subgroupOf N).index := by
    have h := Subgroup.relIndex_mul_index hCrN
    rw [show CrE.relIndex N = (CrE.subgroupOf N).index from rfl, mul_comm] at h
    exact h.symm
  have hPE' : ∀ g ∈ Er, ∀ v ∈ Ff.perp W, ρ g v ∈ Ff.perp W := by
    intro g hg v hv
    exact hPE ⟨g, hg⟩ v hv
  have hlam_inj0 : m = 0 → Function.Injective lam := by
    intro hm0 x y hxy
    have hWxy : ρW (x : Er) = ρW (y : Er) := by
      refine LinearEquiv.ext fun w => ?_
      rw [lam_spec, lam_spec, hxy]
    have hMxy : ρM (x : Er) = ρM (y : Er) := by
      refine LinearEquiv.ext fun w => ?_
      have hsub : Subsingleton M := Module.finrank_zero_iff.mp (by simpa [m] using hm0)
      exact Subsingleton.elim _ _
    have hz : (x : Er) * (y : Er)⁻¹ = 1 := by
      apply hker
      · rw [map_mul, map_inv, hWxy, mul_inv_cancel]
      · rw [map_mul, map_inv, hMxy, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp hz)
  have hρW_apply : ∀ (x : Er) (w : W), (ρW x w : Fin d → F) = ρ x w := by
    intro x w
    exact CFSG.RankThree.PartOne.LIT.restrictAction_apply (FlagSplit.repAut ρEr) W hWE'
      x w
  have hρM_mk : ∀ (x : Er) (v : Ff.perp W),
      ρM x (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (⟨ρ x (v : Fin d → F), hPE' x x.2 (v : Fin d → F) v.2⟩ :
          Ff.perp W) := by
    intro x v
    rfl
  exact ⟨
    { W := W, hU := hU, hWiso := hWiso, hWE := hWE, hPE := hPE', ρW := ρW, ρM := ρM,
      hρW_apply := hρW_apply, hρM_mk := hρM_mk,
      k := k, m := m, hk_eq := rfl, hm_eq := rfl, hk := hkpos, h2k := h2k, hm := hm,
      N := N, hNcomm := hNcomm, hNr := hNr,
      lam := lam, mu := mu, lam_spec := lam_spec, mu_spec := mu_spec,
      hpair := hpair, hlam_root := hlam_root, hmu_root := hmu_root,
      hlam_inj0 := hlam_inj0, hErN := by simpa only [Subgroup.index_eq_card] using hErN,
      hfac := hfac }, trivial⟩

@[expose] noncomputable def projective_gx {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE) (x : D.N) :
    LinearMap.GeneralLinearGroup F (Fin d → F) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (FlagSplit.repAut (natRep (StatedSU d (2 ^ f) F)) (x : Er))

theorem projective_gx_apply {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE) (x : D.N) (v : Fin d → F) :
    (projective_gx D x : Module.End F (Fin d → F)) v =
      natRep (StatedSU d (2 ^ f) F) (x : Er) v := rfl

theorem projective_gx_mem {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE) (x : D.N) :
    projective_gx D x ∈ CFSG.HardMathSupport.Curtis.UnitaryLevi.isoStab
      (unitaryForm 2 f hK d).toDual D.W := by
  classical
  have hρ : IsIsometric (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) :=
    isIsometric_natRep_statedSU hK d
  refine ⟨?_, ?_⟩
  · intro u v
    rw [projective_gx_apply, projective_gx_apply]
    exact hρ (x : Er) u v
  · intro v
    constructor
    · intro hv
      have hv' : natRep (StatedSU d (2 ^ f) F) (x : Er) v ∈ D.W := by
        rwa [projective_gx_apply] at hv
      have h1 : natRep (StatedSU d (2 ^ f) F) ((x : Er)⁻¹)
          (natRep (StatedSU d (2 ^ f) F) (x : Er) v) ∈ D.W :=
        D.hWE ((x : Er)⁻¹) (Er.inv_mem (x : Er).2) _ hv'
      have h3 : natRep (StatedSU d (2 ^ f) F) ((x : Er)⁻¹)
          (natRep (StatedSU d (2 ^ f) F) (x : Er) v) = v := by
        rw [← Module.End.mul_apply, ← map_mul]
        have hxx : (((x : Er) : StatedSU d (2 ^ f) F))⁻¹ *
            ((x : Er) : StatedSU d (2 ^ f) F) = 1 := inv_mul_cancel _
        rw [hxx, map_one, Module.End.one_apply]
      rwa [h3] at h1
    · intro hv
      simpa only [projective_gx_apply] using D.hWE (x : Er) (x : Er).2 v hv

theorem projective_gx_scalars {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE) (x : D.N) :
    (∀ w ∈ D.W, (projective_gx D x : Module.End F (Fin d → F)) w = D.lam x • w) ∧
    (∀ v ∈ (unitaryForm 2 f hK d).perp D.W,
      (projective_gx D x : Module.End F (Fin d → F)) v - D.mu x • v ∈ D.W) := by
  classical
  constructor
  · intro w hw
    rw [projective_gx_apply]
    have h := congrArg Subtype.val (D.lam_spec x ⟨w, hw⟩)
    rw [D.hρW_apply x ⟨w, hw⟩] at h
    exact h
  · intro v hv
    have hq : (Submodule.Quotient.mk
        (⟨natRep (StatedSU d (2 ^ f) F) (x : Er) v,
          D.hPE (x : Er) (x : Er).2 v hv⟩ : (unitaryForm 2 f hK d).perp D.W) :
          FlagSplit.perpQuot (unitaryForm 2 f hK d) D.W) =
        D.mu x • (Submodule.Quotient.mk
          (⟨v, hv⟩ : (unitaryForm 2 f hK d).perp D.W) :
            FlagSplit.perpQuot (unitaryForm 2 f hK d) D.W) := by
      rw [← D.hρM_mk x ⟨v, hv⟩]
      exact D.mu_spec x (Submodule.Quotient.mk
        (⟨v, hv⟩ : (unitaryForm 2 f hK d).perp D.W))
    rw [← Submodule.Quotient.mk_smul] at hq
    have hdiff := (Submodule.Quotient.eq
      (D.W.comap ((unitaryForm 2 f hK d).perp D.W).subtype)).mp hq
    rw [projective_gx_apply]
    have hdiff' : natRep (StatedSU d (2 ^ f) F) (x : Er) v - D.mu x • v ∈ D.W := by
      change ((unitaryForm 2 f hK d).perp D.W).subtype
        (⟨natRep (StatedSU d (2 ^ f) F) (x : Er) v,
          D.hPE (x : Er) (x : Er).2 v hv⟩ - D.mu x • (⟨v, hv⟩ : (unitaryForm 2 f hK d).perp D.W)) ∈ D.W
      exact hdiff
    exact hdiff'

theorem projective_detrel {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE) (hrq : r ∣ 2 ^ f + 1) :
    ∀ x : D.N, (x : Er) ^ r = 1 → D.lam x ^ (2 * D.k) * D.mu x ^ D.m = 1 := by
  classical
  intro x hx
  have hg := projective_gx_mem D x
  have hsc := projective_gx_scalars D x
  have hdet : LinearMap.det ((projective_gx D x :
      LinearMap.GeneralLinearGroup F (Fin d → F)) : Module.End F (Fin d → F)) = 1 := by
    rw [show ((projective_gx D x : LinearMap.GeneralLinearGroup F (Fin d → F)) :
        Module.End F (Fin d → F)) = natRep (StatedSU d (2 ^ f) F) (x : Er) from
      LinearMap.ext (fun v => rfl)]
    exact CFSG.RankThree.PartTwo.Census.det_natRep_statedSU D.hU ((x : Er) : StatedSU d (2 ^ f) F)
  have hσ : (((unitaryForm 2 f hK d).σ : F →+* F) (D.lam x)) = D.lam x ^ (2 ^ f) := by
    rw [show (unitaryForm 2 f hK d).σ =
      CFSG.LieType.BorelTits.unitaryInvolution F 2 f from rfl]
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply (K := F) (p := 2) (f := f) (D.lam x)
  have hq : D.lam x ^ (2 ^ f + 1) = 1 := by
    obtain ⟨s, hs⟩ := hrq
    rw [hs, pow_mul, D.hlam_root x hx, one_pow]
  have h := det_scalar_action (unitaryForm 2 f hK d) D.hWiso (projective_gx D x) hg hdet
    (D.lam x) (D.mu x) hsc.1 hsc.2 hσ hq
  have hfin : Module.finrank F
      (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot (unitaryForm 2 f hK d).toDual D.W) =
      Module.finrank F (FlagSplit.perpQuot (unitaryForm 2 f hK d) D.W) := by
    rw [show Module.finrank F
        (CFSG.HardMathSupport.Curtis.UnitaryLevi.perpQuot (unitaryForm 2 f hK d).toDual D.W) =
      Module.finrank F (FlagSplit.perpQuot (unitaryForm 2 f hK d) D.W) from rfl]
  rw [hfin] at h
  simpa [D.hk_eq, D.hm_eq] using h

theorem projective_torsion {F : Type} [Field F] [Finite F] [CharP F 2] {f d r : ℕ}
    {hK : Nat.card F = (2 ^ f) ^ 2}
    {Er : Subgroup (StatedSU d (2 ^ f) F)} {CrE : Subgroup Er}
    (hr : r.Prime) (hd : 3 ≤ d)
    (D : ProjectiveSetup F f d r (unitaryForm 2 f hK d) (natRep (StatedSU d (2 ^ f) F)) Er CrE)
    (hdetrel : ∀ x : D.N, (x : Er) ^ r = 1 → D.lam x ^ (2 * D.k) * D.mu x ^ D.m = 1) :
    (D.m ≠ 0 → (CrE.subgroupOf D.N).index ≤ r ^ 2) ∧
    ((D.m = 0 ∨ D.k = 1) → (CrE.subgroupOf D.N).index ≤ r) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  letI : CommGroup D.N := { (inferInstance : Group D.N) with mul_comm := D.hNcomm }
  haveI : Finite D.N := Subtype.finite
  have hxr : ∀ x : D.N, (x : D.N) ^ r = 1 → (x : Er) ^ r = 1 := by
    intro x hx
    simpa using congrArg (fun z : D.N => (z : Er)) hx
  constructor
  · intro hm0
    have h := card_quotient_le_pow_two_of_scalar_pair (CrE.subgroupOf D.N) D.hNr D.lam D.mu
      D.hpair (fun x hx => D.hlam_root x (hxr x hx))
      (fun x hx => D.hmu_root x hm0 (hxr x hx))
    simpa only [Subgroup.index_eq_card] using h
  · intro hcase
    rcases hcase with hm0 | hk1
    · have h := card_quotient_le_prime_of_scalar (CrE.subgroupOf D.N) D.hNr D.lam
        (D.hlam_inj0 hm0) (fun x hx => D.hlam_root x (hxr x hx))
      simpa only [Subgroup.index_eq_card] using h
    · have h := card_quotient_le_prime_of_pair_det (CrE.subgroupOf D.N) D.hNr D.lam D.mu
        D.hpair (fun x hx => D.hlam_root x (hxr x hx))
        (fun x hx => D.hmu_root x (by
          have hmpos : 0 < D.m := by
            have h := D.hm
            rw [hk1] at h
            omega
          exact Nat.pos_iff_ne_zero.mp hmpos) (hxr x hx))
        (fun x hx => by
          have hd := hdetrel x (hxr x hx)
          rw [hk1] at hd
          simpa using hd)
      simpa only [Subgroup.index_eq_card] using h

theorem projective_bound_statedSU_quot
    (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (C : Subgroup (StatedSU d (2 ^ f) F))
    (hC : C ≤ Subgroup.center (StatedSU d (2 ^ f) F))
    {R Er : Subgroup (StatedSU d (2 ^ f) F)} (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hErNormR : Er ≤ Subgroup.normalizer (R : Set (StatedSU d (2 ^ f) F)))
    (hEr2 : IsPGroup r Er)
    (CrE : Subgroup Er) [CrE.Normal] (hB : ∀ a : Er, a ^ r ∈ CrE)
    (hErDer : commutator Er ≤ CrE)
    (hCrC : ∀ c ∈ CrE, (c : StatedSU d (2 ^ f) F) ∈ C)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup r R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ r) v = a • v) →
      Nat.card R ≤ r ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}) :
    Nat.card (Er ⧸ CrE) ≤ r ^ (d - 2) := by
  obtain ⟨D, -⟩ :=
    projective_setup_exists hK hd hr hr2 hrq C hC hR1 hR2 hErNormR hEr2 CrE hB hErDer hCrC hPRL
  have hdetrel := projective_detrel (f := f) (d := d) (hK := hK) (Er := Er) (CrE := CrE) D hrq
  obtain ⟨htorsion2, htorsion1⟩ := projective_torsion (f := f) (d := d) (hK := hK) (Er := Er) (CrE := CrE) hr hd D hdetrel
  rw [← Subgroup.index_eq_card]
  exact card_le_pow_sub_two_of_factor_bounds hr hd D.hk D.h2k D.hm D.hErN htorsion2
    htorsion1 D.hfac

theorem card_le_pow_sub_two_of_normalizes_statedSU_quot
    (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (C : Subgroup (StatedSU d (2 ^ f) F)) [C.Normal]
    (hC : C ≤ Subgroup.center (StatedSU d (2 ^ f) F))
    {E X : Subgroup (StatedSU d (2 ^ f) F ⧸ C)}
    (hX1 : X ≠ ⊥) (hX2 : IsPGroup 2 X)
    (hEX : E ≤ Subgroup.normalizer (X : Set (StatedSU d (2 ^ f) F ⧸ C)))
    (hE : CFSG.Open.IsElemAbelian r E)
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup r R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ r) v = a • v) →
      Nat.card R ≤ r ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}) :
    Nat.card E ≤ r ^ (d - 2) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hEel : CFSG.IsElementaryAbelian r E := hE.isElementaryAbelian
  have hE2 : IsPGroup r E := CFSG.IsElementaryAbelian.isPGroup r E
  let S : Subgroup (GL (Fin d) F) := StatedSU d (2 ^ f) F
  have hCS : C ≤ Subgroup.center S := hC
  let π : S →* S ⧸ C := QuotientGroup.mk' C
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective C
  let Et : Subgroup S := E.comap π
  let Xt : Subgroup S := X.comap π
  have hEtmap : Et.map π = E := Subgroup.map_comap_eq_self (by simp [MonoidHom.range_eq_top.mpr hπsurj])
  have hXtmap : Xt.map π = X := Subgroup.map_comap_eq_self (by simp [MonoidHom.range_eq_top.mpr hπsurj])
  have hXt_ne : Xt ≠ ⊥ := by
    intro h
    rw [← hXtmap, h, Subgroup.map_bot] at hX1
    exact hX1 rfl
  have hCEt : C ≤ Et := by
    intro c hc
    rw [Subgroup.mem_comap]
    rw [show π c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    exact E.one_mem
  have hEtR : Et ≤ Subgroup.normalizer (Xt : Set S) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg x hx
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    have hgE : π g ∈ E := by
      rw [← hEtmap]
      exact Subgroup.mem_map_of_mem π hg
    have hxX : π x ∈ X := by
      rw [← hXtmap]
      exact Subgroup.mem_map_of_mem π hx
    exact ((Subgroup.mem_normalizer_iff.mp (hEX hgE)) (π x)).mp hxX
  have hCodd : Odd (Nat.card C) := odd_card_center_le hK hd C hC
  have hCcentral : C.subgroupOf Xt ≤ Subgroup.center Xt := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxS : (x : S) ∈ C := hx
    have hcen := hCS hxS
    rw [Subgroup.mem_center_iff] at hcen
    exact hcen (y : S)
  have hkerXt : (π.comp Xt.subtype).ker = C.subgroupOf Xt := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : S)).mp h
    · intro h
      exact (QuotientGroup.eq_one_iff (x : S)).mpr h
  have hquotXt : Xt ⧸ (C.subgroupOf Xt) ≃* X := by
    have hmap : MonoidHom.range (π.comp Xt.subtype) = X := by
      rw [← hXtmap]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map_of_mem π y.2
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨y, hy⟩, rfl⟩
    exact (QuotientGroup.quotientMulEquivOfEq hkerXt.symm).trans
      ((QuotientGroup.quotientKerEquivRange (π.comp Xt.subtype)).trans
        (MulEquiv.subgroupCongr hmap))
  have hindexXt : (C.subgroupOf Xt).index = Nat.card X := by
    rw [Subgroup.index_eq_card (C.subgroupOf Xt), Nat.card_congr hquotXt.toEquiv]
  obtain ⟨k, hk⟩ := hX2.exists_card_eq
  have hkpos : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    have : X = ⊥ := Subgroup.card_eq_one.mp hk
    exact hX1 this
  have hCXt : C ≤ Xt := by
    intro c hc
    rw [Subgroup.mem_comap]
    rw [show π c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    exact X.one_mem
  have hcop : Nat.Coprime (Nat.card (C.subgroupOf Xt)) (C.subgroupOf Xt).index := by
    have hcardC : Nat.card (C.subgroupOf Xt) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCXt).toEquiv
    rw [hcardC, hindexXt, hk]
    exact (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hCodd)).pow_right k
  obtain ⟨K, hKchar, hKcard, -, hKsup, hKinf, -, -, -, -⟩ :=
    CFSG.Semidihedral.central_hall_subgroup_direct_complement (C.subgroupOf Xt) hCcentral hcop
  let R : Subgroup S := K.map Xt.subtype
  have hRcard : Nat.card R = 2 ^ k := by
    rw [show Nat.card R = Nat.card K from Subgroup.card_map_of_injective Xt.subtype_injective,
      hKcard, hindexXt, hk]
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := k) hRcard
  have hR1 : R ≠ ⊥ := by
    intro h
    have h1 : Nat.card R = 1 := by rw [h, Subgroup.card_bot]
    rw [hRcard] at h1
    have h2 : 2 ≤ 2 ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < 2) j]
    omega
  have hEtNormR : Et ≤ Subgroup.normalizer (R : Set S) :=
    hEtR.trans (CFSG.Walter.normalizer_le_normalizer_map_of_characteristic K)
  let P : Sylow r Et := default
  let Er : Subgroup S := P.1.map Et.subtype
  have hEr2 : IsPGroup r Er := P.2.map Et.subtype
  let φ : Et →* E := (π.comp Et.subtype).codRestrict E (fun x => by
    rw [← hEtmap]
    exact Subgroup.mem_map_of_mem π x.2)
  have hφsurj : Function.Surjective φ := by
    intro e
    have he : (e : S ⧸ C) ∈ Et.map π := by rw [hEtmap]; exact e.2
    rw [Subgroup.mem_map] at he
    obtain ⟨x, hx, hxe⟩ := he
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxe
  have hPtop : (P.mapSurjective hφsurj : Subgroup E) = ⊤ := by
    have htop : IsPGroup r (⊤ : Subgroup E) :=
      hE2.of_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup E) ≃* E).symm
    exact ((P.mapSurjective hφsurj).is_maximal' (Q := ⊤) htop le_top).symm
  have hErmap : Er.map π = E := by
    have hmapφ : (P.1.map φ).map E.subtype = P.1.map (π.comp Et.subtype) := by
      rw [Subgroup.map_map]
      rfl
    have h1 : (P.1.map φ).map E.subtype = E := by
      rw [show (P.1.map φ) = ⊤ from hPtop, Subgroup.map_top, Subgroup.range_subtype]
    change (P.1.map Et.subtype).map π = E
    rw [Subgroup.map_map]
    exact hmapφ ▸ h1
  let Cr : Subgroup S := Er ⊓ C
  let CrE : Subgroup Er := Cr.subgroupOf Er
  have hCr_le : Cr ≤ Er := inf_le_left
  have hErCr : Er ⧸ (CrE) ≃* E := by
    have hker : MonoidHom.ker (π.comp Er.subtype) = CrE := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        rw [Subgroup.mem_inf]
        refine ⟨x.2, ?_⟩
        change (QuotientGroup.mk (x : S) : S ⧸ C) = 1 at h
        exact (QuotientGroup.eq_one_iff (x : S)).mp h
      · intro h
        have h1 : (x : S) ∈ C := h.2
        change π (x : S) = 1
        exact (QuotientGroup.eq_one_iff (x : S)).mpr h1
    have hrange : MonoidHom.range (π.comp Er.subtype) = E := by
      rw [← hErmap]
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map_of_mem π y.2
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨y, hy⟩, rfl⟩
    exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (π.comp Er.subtype)).trans
        (MulEquiv.subgroupCongr hrange))
  have hcard_E : Nat.card E = Nat.card (Er ⧸ (CrE)) := Nat.card_congr hErCr.toEquiv |>.symm
  have hErNormR : Er ≤ Subgroup.normalizer (R : Set S) :=
    (Subgroup.map_subtype_le P.1).trans hEtNormR
  have hB : ∀ a : Er, a ^ r ∈ CrE := by
    intro a
    have hx : (QuotientGroup.mk a : Er ⧸ (CrE)) ^ r = 1 := by
      have hExp : Monoid.exponent E ∣ r := CFSG.IsElementaryAbelian.exponent_dvd_p r E
      have h1 : (hErCr (QuotientGroup.mk a)) ^ r = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp _
      have h2 : (QuotientGroup.mk a : Er ⧸ (CrE)) ^ r = 1 := by
        simpa using congrArg hErCr.symm h1
      exact h2
    exact (QuotientGroup.eq_one_iff (a ^ r)).mp (by
      rw [show (QuotientGroup.mk (a ^ r) : Er ⧸ (CrE)) =
        ((QuotientGroup.mk' (CrE)) a) ^ r from
          (map_pow (QuotientGroup.mk' (CrE)) a r).symm]
      exact hx)
  haveI hErCr_el : CFSG.IsElementaryAbelian r (Er ⧸ (CrE)) :=
    CFSG.IsElementaryAbelian.of_mulEquiv hErCr.symm hEel
  haveI hErCr_comm : IsMulCommutative (Er ⧸ (CrE)) := inferInstance
  have hErDer : commutator Er ≤ CrE :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hErCr_comm
  have hCrC : ∀ c ∈ CrE, (c : S) ∈ C := by
    intro c hc
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
  have hbound := projective_bound_statedSU_quot hK hd hr hr2 hrq C hC hR1 hR2 hErNormR hEr2
    CrE hB hErDer hCrC hPRL
  rwa [hcard_E]

theorem twoLocalPrimeRank_statedSU_quot_le
    (hK : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ f + 1)
    (C : Subgroup (StatedSU d (2 ^ f) F)) [C.Normal]
    (hC : C ≤ Subgroup.center (StatedSU d (2 ^ f) F))
    (hPRL : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (R : Subgroup (V ≃ₗ[F] V)), IsPGroup r R →
      (∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v) →
      (∀ x ∈ R, ∃ a : F, ∀ v, (x ^ r) v = a • v) →
      Nat.card R ≤ r ^ (Module.finrank F V - 1) *
        Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v}) :
    CFSG.Open.twoLocalPrimeRank r (StatedSU d (2 ^ f) F ⧸ C) ≤ d - 2 := by
  refine CFSG.LocalAnalysis.GLTheoremA.twoLocalPrimeRank_le_of_card_le hr ?_
  intro R E hR1 hR2 hER hE
  haveI : CFSG.IsElementaryAbelian r E := hE.isElementaryAbelian
  exact card_le_pow_sub_two_of_normalizes_statedSU_quot hK hd hr hr2 hrq C hC hR1 hR2 hER hE hPRL

end CFSG.LocalAnalysis.GLTheoremA

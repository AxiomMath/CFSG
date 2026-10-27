module

public import CFSG.ClassicalInvolution.Uniform.U8Adj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD (conjSub_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2 commute_of_map_commute_of_gen3)
open scoped MatrixGroups commutatorElement


section Cover

variable {G C : Type*} [Group G] [Group C]

theorem mem_of_pow_three_of_map_mem [Finite G] (θ : G →* C) (hker : θ.ker ≤ Subgroup.center G)
    (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1) {N : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hx : θ x ∈ N.map θ) : x ∈ N := by
  obtain ⟨n, hn, hnx⟩ := hx
  set c : G := n⁻¹ * x with hc
  have hcker : c ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hnx, inv_mul_cancel]
  have hcc : ∀ y : G, y * c = c * y := fun y => Subgroup.mem_center_iff.mp (hker hcker) y
  have hxnc : x = n * c := by rw [hc]; group
  have hc3N : c ^ 3 ∈ N := by
    have h1 : n ^ 3 * c ^ 3 = 1 := by
      rw [← (Commute.mul_pow (show Commute n c from hcc n) 3), ← hxnc]
      exact hx3
    have : c ^ 3 = (n ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact N.inv_mem (N.pow_mem hn 3)
  have hcop : Nat.Coprime 3 (orderOf c) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    obtain ⟨r, hr⟩ := h3
    set c' : G := c ^ r with hc'
    have hc'ker : c' ∈ θ.ker := Subgroup.pow_mem _ hcker r
    have hc'3 : c' ^ 3 = 1 := by
      rw [hc', ← pow_mul, mul_comm, ← hr]
      exact pow_orderOf_eq_one c
    have hc'1 := hk3 c' hc'ker hc'3
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · have := orderOf_pos c
        rw [h0] at hr
        omega
      · exact h0
    have hdvd := orderOf_dvd_of_pow_eq_one (hc'1 : c ^ r = 1)
    have := Nat.le_of_dvd hr0 hdvd
    have := orderOf_pos c
    omega
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  have hcN : c ∈ N := by
    rw [← hu]
    exact N.pow_mem hc3N u
  rw [hxnc]
  exact N.mul_mem hn hcN

theorem StdLayer3.of_central_cover [Finite G] (θ : G →* C) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center G) (hk3 : ∀ x ∈ θ.ker, x ^ 3 = 1 → x = 1)
    {R₀ R₂ : Subgroup G} (hR₀ : Gen3 R₀) (hR₂ : Gen3 R₂) {R₀' R₂' : Subgroup C}
    (h₀ : R₀.map θ = R₀') (h₂ : R₂.map θ = R₂') (h : StdLayer3 R₀' R₂') : StdLayer3 R₀ R₂ := by
  obtain ⟨L, hLq, hLC, hL3, hR₂L, hne⟩ := h
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := ⟨hLq.1⟩
    exact Subgroup.isPerfect_iff.mp this
  set M := L.comap θ with hM
  set N := ⁅M, M⁆ with hN
  have hmapN : N.map θ = L := map_commutator_comap_eq θ hθ hLperf
  have hNM : N ≤ M := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hMC : M ≤ Subgroup.centralizer (R₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact commute_of_map_commute_of_gen3 θ hker hk3 hR₀ (b := x) (fun a ha =>
      Subgroup.mem_centralizer_iff.mp (hLC hx) (θ a) (h₀ ▸ Subgroup.mem_map_of_mem θ ha)) r hr
  refine ⟨N, isQuasisimple_commutator_comap θ hθ hker hLq, hNM.trans hMC, ?_, ?_, ?_⟩
  · intro x hx hx3
    have h1 : θ x ∈ Subgroup.centralizer (R₀' : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← h₀] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx r hr]
    have h2 : θ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have h4 : θ x ∈ N.map θ := by
      rw [hmapN]
      exact hL3 (θ x) h1 h2
    exact mem_of_pow_three_of_map_mem θ hker hk3 hx3 h4
  · obtain ⟨S, hSR, hS3, hRS⟩ := hR₂
    refine hRS.trans ((Subgroup.closure_le _).2 fun s hs => ?_)
    have hs' : θ s ∈ N.map θ := by
      rw [hmapN]
      exact hR₂L (h₂ ▸ Subgroup.mem_map_of_mem θ (hSR hs))
    exact mem_of_pow_three_of_map_mem θ hker hk3 (hS3 s hs) hs'
  · intro heq
    apply hne
    rw [← h₂, heq, hmapN]

end Cover

section Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

variable {n : ℕ}

theorem hasLayer3_E6 (hadm : StatedLieAdmissible .E6 n 3 1) : HasLayer3 .E6 n := by
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E6 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E6
  have hfin : Finite (modelUniv .E6 0 3 1 Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E6 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E6 0 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      IsLongestRoot (modelUniv .E6 0 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 3 1)).2 hγ)
  have hqs := isQuasisimple_e6 (GaloisField 3 1)
  have hθ := e6Isogeny_surjective (GaloisField 3 1)
  have hker : (e6Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField 3 1))
  have hk3 : ∀ x ∈ (e6Isogeny (GaloisField 3 1)).ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
    CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime .E6 0 3 1 Nat.prime_three
      hp2 hfund hadm x (hker hx) hx3
  set e : Fin Tag.E6.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1)) :=
    (e6Datum (GaloisField 3 1)).rootGroup e ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-e) with hRstd
  set R₂ : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1)) :=
    (e6Datum (GaloisField 3 1)).rootGroup δ₂ ⊔
      (e6Datum (GaloisField 3 1)).rootGroup (-δ₂) with hR₂
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have hR₂mem : R₂ ∈ fundamentalSubgroups .E6 (modelUniv .E6 0 3 1 Fact.out).D :=
    ⟨1, δ₂, Or.inl (hall δ₂ hS.mem₂.1), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ((e6Datum (GaloisField 3 1)).rootGroup γ ⊔
          (e6Datum (GaloisField 3 1)).rootGroup (-γ)).map
        (e6Isogeny (GaloisField 3 1)) =
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup _ (IsRoot.neg hγ))
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstdmem
  obtain ⟨eR₂⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hR₂mem
  have hgR : Gen3 Rstd := gen3_of_equiv_sl2 eR
  have hgR₂ : Gen3 R₂ := gen3_of_equiv_sl2 eR₂
  have hinj : ∀ x ∈ Rstd, (e6Isogeny (GaloisField 3 1)) x = 1 → x = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 .E6 0 1 hfund hadm
        (by simp) Rstd hRstdmem r hr hcen
  have hZ : ∀ a ∈ (rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) e ⊔
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-e)),
      (∀ y ∈ (rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) e ⊔
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-e)), a * y = y * a) →
        a * a = 1 := by
    intro a ha hcen
    rw [← himg e (IsRoot.basis _)] at ha hcen
    obtain ⟨r, hr, rfl⟩ := ha
    have hr' : r ∈ Rstd := hr
    have hrc : ∀ y ∈ Rstd, r * y = y * r := by
      intro y hy
      have hc := hcen ((e6Isogeny (GaloisField 3 1)) y) (Subgroup.mem_map_of_mem _ hy)
      have hcomm : (e6Isogeny (GaloisField 3 1)) (r * y * r⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      have hmem : r * y * r⁻¹ * y⁻¹ ∈ Rstd :=
        Rstd.mul_mem (Rstd.mul_mem (Rstd.mul_mem hr' hy) (Rstd.inv_mem hr')) (Rstd.inv_mem hy)
      have h1 := hinj _ hmem hcomm
      calc r * y = (r * y * r⁻¹ * y⁻¹) * (y * r) := by group
        _ = y * r := by rw [h1, one_mul]
    have hsq := central_sq_of_equiv_sl2 odd_natCard_galoisField_three_one eR r hr' hrc
    rw [← map_mul]
    exact (congrArg _ hsq).trans (map_one _)
  have hstd := stdLayer3_adjoint (K := GaloisField 3 1) (ringChar_galoisField_ne_two hp2)
    natCard_galoisField_three_one (⟨0, by decide⟩ : Fin Tag.E6.rank) hS hZ
  exact hasLayer3_of_std3 hfin hsingle hRstdmem hR₂mem
    (StdLayer3.of_central_cover (e6Isogeny (GaloisField 3 1)) hθ hker hk3 hgR hgR₂
      (himg e (IsRoot.basis _)) (himg δ₂ hS.mem₂.1) hstd)

theorem hasLayer3_E7 (hadm : StatedLieAdmissible .E7 n 3 1) : HasLayer3 .E7 n := by
  obtain rfl : n = 0 := hadm.2.2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfund : IsFundTag .E7 := trivial
  obtain ⟨δ₂, δ₃, hS⟩ := layerShape_E7
  have hfin : Finite (modelUniv .E7 0 3 1 Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out trivial hadm
  have hsingle := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .E7 0 3 1
    Fact.out trivial hadm (by decide) (by decide)
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .E7 0 3 1 Fact.out
    trivial hadm
  have hall : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      IsLongestRoot (modelUniv .E7 0 3 1 Fact.out).D γ := fun γ hγ =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_of_mem_roots_of_forall_single _ rfl
      (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 3 1)).2 hγ)
  have hqs := isQuasisimple_e7 (GaloisField 3 1)
  have hθ := e7Isogeny_surjective (GaloisField 3 1)
  have hker : (e7Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (exists_e7Isogeny_ne_one (GaloisField 3 1))
  have hk3 : ∀ x ∈ (e7Isogeny (GaloisField 3 1)).ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
    CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime .E7 0 3 1 Nat.prime_three
      hp2 hfund hadm x (hker hx) hx3
  set e : Fin Tag.E7.rank → ℤ := Pi.single ⟨0, by decide⟩ 1 with he
  set Rstd : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1)) :=
    (e7Datum (GaloisField 3 1)).rootGroup e ⊔
      (e7Datum (GaloisField 3 1)).rootGroup (-e) with hRstd
  set R₂ : Subgroup ↥(e7Data_valid.minGroup (GaloisField 3 1)) :=
    (e7Datum (GaloisField 3 1)).rootGroup δ₂ ⊔
      (e7Datum (GaloisField 3 1)).rootGroup (-δ₂) with hR₂
  have hRstdmem : Rstd ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D :=
    ⟨1, e, Or.inl (hall e (IsRoot.basis _)), (conjSub_one _).symm⟩
  have hR₂mem : R₂ ∈ fundamentalSubgroups .E7 (modelUniv .E7 0 3 1 Fact.out).D :=
    ⟨1, δ₂, Or.inl (hall δ₂ hS.mem₂.1), (conjSub_one _).symm⟩
  have himg : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot .E7 γ →
      ((e7Datum (GaloisField 3 1)).rootGroup γ ⊔
          (e7Datum (GaloisField 3 1)).rootGroup (-γ)).map
        (e7Isogeny (GaloisField 3 1)) =
        rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) γ ⊔
          rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-γ) := fun γ hγ => by
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ hγ)
      (CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup _ (IsRoot.neg hγ))
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hRstdmem
  obtain ⟨eR₂⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 hfund hadm (by decide) (by decide) hR₂mem
  have hgR : Gen3 Rstd := gen3_of_equiv_sl2 eR
  have hgR₂ : Gen3 R₂ := gen3_of_equiv_sl2 eR₂
  have hinj : ∀ x ∈ Rstd, (e7Isogeny (GaloisField 3 1)) x = 1 → x = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 .E7 0 1 hfund hadm
        (by simp) Rstd hRstdmem r hr hcen
  have hZ : ∀ a ∈ (rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) e ⊔
        rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-e)),
      (∀ y ∈ (rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) e ⊔
        rootGroup (rootOperatorFamily .E7) (GaloisField 3 1) (-e)), a * y = y * a) →
        a * a = 1 := by
    intro a ha hcen
    rw [← himg e (IsRoot.basis _)] at ha hcen
    obtain ⟨r, hr, rfl⟩ := ha
    have hr' : r ∈ Rstd := hr
    have hrc : ∀ y ∈ Rstd, r * y = y * r := by
      intro y hy
      have hc := hcen ((e7Isogeny (GaloisField 3 1)) y) (Subgroup.mem_map_of_mem _ hy)
      have hcomm : (e7Isogeny (GaloisField 3 1)) (r * y * r⁻¹ * y⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      have hmem : r * y * r⁻¹ * y⁻¹ ∈ Rstd :=
        Rstd.mul_mem (Rstd.mul_mem (Rstd.mul_mem hr' hy) (Rstd.inv_mem hr')) (Rstd.inv_mem hy)
      have h1 := hinj _ hmem hcomm
      calc r * y = (r * y * r⁻¹ * y⁻¹) * (y * r) := by group
        _ = y * r := by rw [h1, one_mul]
    have hsq := central_sq_of_equiv_sl2 odd_natCard_galoisField_three_one eR r hr' hrc
    rw [← map_mul]
    exact (congrArg _ hsq).trans (map_one _)
  have hstd := stdLayer3_adjoint (K := GaloisField 3 1) (ringChar_galoisField_ne_two hp2)
    natCard_galoisField_three_one (⟨0, by decide⟩ : Fin Tag.E7.rank) hS hZ
  exact hasLayer3_of_std3 hfin hsingle hRstdmem hR₂mem
    (StdLayer3.of_central_cover (e7Isogeny (GaloisField 3 1)) hθ hker hk3 hgR hgR₂
      (himg e (IsRoot.basis _)) (himg δ₂ hS.mem₂.1) hstd)

end Isogeny

end CFSG.ClassicalInvolution.Uniform

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinCover

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover

open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

theorem reflection_one_eq : (reflection 3 F 1 (by norm_num) (by norm_num) :
    Matrix.SpecialLinearGroup (Fin 3) F) = s₁₂Mat := by
  apply Subtype.ext
  rw [coe_reflection]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [reflectionMatrix, s₁₂Mat, s₁₂M, CharTwo.neg_eq]

theorem reflection_two_eq : (reflection 3 F 2 (by norm_num) (by norm_num) :
    Matrix.SpecialLinearGroup (Fin 3) F) = s₂₃Mat := by
  apply Subtype.ext
  rw [coe_reflection]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [reflectionMatrix, s₂₃Mat, s₂₃M, CharTwo.neg_eq]

theorem normalizer_V1_sup_V2 :
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ⊔
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) = ⊤ := by
  set Q := Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ⊔
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) with hQ
  set M := Q.comap (proj 3 F) with hM
  have hU : unitriangular 3 F ≤ M := fun u hu =>
    Subgroup.mem_sup_left (U_le_normalizer_V1 (Subgroup.mem_map_of_mem _ hu))
  have hcut : borelOvergroupCuts M = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨hi1, hin, hnot⟩ := hi
    apply hnot
    have h1 : i = 1 ∨ i = 2 := by omega
    rcases h1 with rfl | rfl
    · change proj 3 F _ ∈ Q
      rw [reflection_one_eq]
      exact Subgroup.mem_sup_right s12P_mem_normalizer_V2
    · change proj 3 F _ ∈ Q
      rw [reflection_two_eq]
      exact Subgroup.mem_sup_left s23P_mem_normalizer_V1
  have htop := CFSG.QuasithinUnique.Setup.X7a.eq_top_of_borelOvergroupCuts_eq_empty M hU hcut
  rw [eq_top_iff]
  intro p _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F p
  have : g ∈ M := htop ▸ Subgroup.mem_top g
  exact this

theorem proj_dMat_mem_normalizer_U [Finite F] (t₁ t₂ : Fˣ) :
    proj 3 F (dMat t₁ t₂) ∈ Subgroup.normalizer ((projUnitriangular 3 F :
      Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rw [(sylow_normalizers (K := F) (n := 3) 2 (by norm_num)).2.1]
  refine ⟨dMat t₁ t₂, ?_, rfl⟩
  intro i j hij
  exact isDiag_dMat (F := F) t₁ t₂ (ne_of_gt hij)

theorem hfix_L3 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ∀ w ∈ (V1 : Subgroup (projectiveSL 3 F)) ⊓ V2,
      (∀ b ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)), b * w = w * b) → w = 1 := by
  intro w hw hb
  rw [V1_inf_V2] at hw
  obtain ⟨c, rfl⟩ := mem_Wg.mp hw
  have : Fintype F := Fintype.ofFinite F
  have h4 : 4 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
    (by simpa using h4)
  obtain ⟨t, ht⟩ := CFSG.LinearGroups.field_scalar_with_nontrivial_square ⟨s, hs⟩
  have hbt := hb _ (proj_dMat_mem_normalizer_U t 1)
  have h1 : proj 3 F (dMat t 1) * wP c * (proj 3 F (dMat t 1))⁻¹ = wP c := by
    rw [hbt]
    group
  rw [dP_conj_wP] at h1
  have h2 := wP_injective h1
  have h3 : ((t : F) * t - 1) * c = 0 := by
    simp only [Units.val_one, mul_one] at h2
    linear_combination h2
  have h4' : ((t : F) * t - 1) ≠ 0 := by
    intro h
    apply ht
    apply Units.ext
    rw [pow_two, Units.val_mul, Units.val_one]
    linear_combination h
  have hc : c = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h4'
    · exact h
  rw [hc, wP_zero]


open LinearFieldFourKernel in
theorem exists_wxComm_ne_one (hk : Nat.card F = 4) {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (η : X →* projectiveSL 3 F) (hη : Function.Surjective η)
    (hker : ∀ z, η z = 1 → z ∈ Subgroup.center X) (h2 : IsPGroup 2 η.ker)
    (hne : ¬ ∀ z, η z = 1 → z * z = 1) : ∃ z : F, wxComm η hη z 1 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hne
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
  have hω3 : ω * ω * ω = 1 := omega_cube hk hω0
  have hω4 : 1 + ω + ω * ω = 0 := by
    rw [omega_mul_omega hk hω0 hω1]
    linear_combination (1 + ω) * (CharP.cast_eq_zero F 2)
  obtain ⟨u, hu⟩ := hη (hP ω hω3)
  have hsq1 : ∀ a b, normComm η hη ω a b * normComm η hη ω a b = 1 := by
    intro a b
    have := normComm_sq η hη hker hω3 u hu hk hω0 hω1 a b
    rw [pow_two, hcon] at this
    exact this
  let Ω : Subgroup X :=
    { carrier := {z | η z = 1 ∧ z * z = 1}
      one_mem' := ⟨map_one η, one_mul 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
        have hc := Subgroup.mem_center_iff.mp (hker b hb) a
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hc]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨by rw [map_inv, ha, inv_one], ?_⟩
        calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          _ = 1 := by rw [ha2, inv_one] }
  have hclos : Subgroup.closure {normComm η hη ω 1 1, normComm η hη ω ω 1} ≤ Ω := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨map_normComm η hη hω3 hω4 1 1, hsq1 1 1⟩
    · exact ⟨map_normComm η hη hω3 hω4 ω 1, hsq1 ω 1⟩
  intro z hz
  have hn : ∃ n : ℕ, z ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := h2 ⟨z, MonoidHom.mem_ker.mpr hz⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  exact (hclos (twoPart_le_closure_normComm η hη hker hω3 u hu hk hω0 hω1 z hz hn)).2

open LinearFieldFourKernel in
theorem eq_one_of_commutes_over_U (hk : Nat.card F = 4) {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (η : X →* projectiveSL 3 F) (hη : Function.Surjective η)
    (hker : ∀ z, η z = 1 → z ∈ Subgroup.center X) (h2 : IsPGroup 2 η.ker)
    (hne : ¬ ∀ z, η z = 1 → z * z = 1) (x : X)
    (hx : η x ∈ (V1 : Subgroup (projectiveSL 3 F)) ⊓ V2)
    (hcomm : ∀ y : X, η y ∈ projUnitriangular 3 F → x * y = y * x) : η x = 1 := by
  obtain ⟨z₀, hz₀⟩ := exists_wxComm_ne_one hk η hη hker h2 hne
  rw [V1_inf_V2] at hx
  obtain ⟨c, hc⟩ := mem_Wg.mp hx
  by_cases hc0 : c = 0
  · rw [hc, hc0, wP_zero]
  · exfalso
    apply hz₀
    obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
    have hω3 : ω * ω * ω = 1 := omega_cube hk hω0
    obtain ⟨u, hu⟩ := hη (hP ω hω3)
    have key : ∀ a, wxComm η hη c a = 1 := by
      intro a
      have hy : η (lift η hη (xP a)) ∈ projUnitriangular 3 F := by
        rw [map_lift]
        exact (projRoots (K := F)).x_mem a
      have h1 : wxComm η hη c a = ⁅x, lift η hη (xP a)⁆ :=
        comm_eq η hker (by rw [map_lift, hc]) rfl
      rw [h1, commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ hy)]
    have := key (z₀ / c)
    rwa [wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 c (z₀ / c), mul_div_cancel₀ _ hc0] at this

end L3

open CFSG.Open CFSG.Quasithin

theorem isElemAbelian_centerOf {G : Type} [Group G] {K : Subgroup G} {M : Type} [Group M]
    {π : ↥K →* M} (hker : ∀ x : ↥K, (∀ y : ↥K, x * y = y * x) → π x = 1)
    (hsq : ∀ z : ↥K, π z = 1 → z * z = 1) : IsElemAbelian 2 (centerOf K) := by
  refine ⟨isMulCommutative_iff_of_setLike.mpr fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  · have hc : ∀ y : ↥K, (⟨x, hx.1⟩ : ↥K) * y = y * ⟨x, hx.1⟩ := fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2).symm
    have := hsq ⟨x, hx.1⟩ (hker _ hc)
    rw [pow_two]
    exact congrArg Subtype.val this

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearCover in
theorem cover257a : Cover257a := by
  intro G _ _ K P n hq hM _ hP hZ g hgK hgP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥K := hq.1
  obtain ⟨hn2, hmodel⟩ := hM
  rcases hmodel with hL | hS
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    let e' : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* LinearFlag.projectiveSL 3 F := e.trans (statedSLEquiv F)
    have hdata := L3.modelData_L3 (F := F) hn2 hcard
    obtain ⟨π, hred⟩ := reduceP hq hdata e' hP
    have hker : ∀ z, π z = 1 → z ∈ Subgroup.center ↥K := fun z hz =>
      Subgroup.mem_center_iff.mpr fun y => (hred.ker_central z hz y).symm
    by_cases hn : n = 2
    · subst hn
      have hk : Nat.card F = 4 := by rw [hcard]; norm_num
      have hne : ¬ ∀ z : ↥K, π z = 1 → z * z = 1 := fun hsq =>
        hZ (isElemAbelian_centerOf hred.center_le hsq)
      refine cover_aux hq hred hdata L3.normalizer_V1_sup_V2 (L3.hfix_L3 hn2 hcard) ?_ hgK hgP
      intro x hx hcomm
      exact L3.eq_one_of_commutes_over_U hk π hred.surj hker hred.ker_two hne x hx hcomm
    · exfalso
      have hn3 : 3 ≤ n := by omega
      have hC : π.ker ≤ Subgroup.center ↥K := fun z hz => hker z (MonoidHom.mem_ker.mp hz)
      obtain ⟨-, hbij⟩ := even_linear_three_large_field_catalog_central_two_cover_trivial π
        hred.surj hC hred.ker_two hn3 (L3.lieModel_L3 (by omega) hcard)
      refine hZ (isElemAbelian_centerOf hred.center_le fun z hz => ?_)
      have := hbij.1 (hz.trans (map_one π).symm)
      rw [this, mul_one]
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hS.2
    have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    let e' : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ComponentClassification.UnbalancedCatalog.SpChain.antiSp F :=
      e.trans (QuasithinUnique.Setup.X7b.antiProjEquiv F).symm
    have hdata := Sp4.modelData_Sp (K := F) hn2 hcard
    obtain ⟨π, hred⟩ := reduceP hq hdata e' hP
    have hker : ∀ z, π z = 1 → z ∈ Subgroup.center ↥K := fun z hz =>
      Subgroup.mem_center_iff.mpr fun y => (hred.ker_central z hz y).symm
    exfalso
    have hC : π.ker ≤ Subgroup.center ↥K := fun z hz => hker z (MonoidHom.mem_ker.mp hz)
    obtain ⟨-, hbij⟩ := SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
      π hred.surj hC hred.ker_two hn2 (Sp4.lieModel_Sp hn2 hcard)
    refine hZ (isElemAbelian_centerOf hred.center_le fun z hz => ?_)
    have := hbij.1 (hz.trans (map_one π).symm)
    rw [this, mul_one]

end CFSG.QuasithinUnique.Fin257

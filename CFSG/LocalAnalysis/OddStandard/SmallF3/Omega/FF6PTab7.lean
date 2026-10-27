module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSyl1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PStarTypes
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6p_hyp62_of_sylow (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      (∀ n ∈ normalizer (L : Set G), ∃ h ∈ H, ∃ c ∈ centralizer (L : Set G), n = h * c) →
      ∀ B : Subgroup G, IsNormalE16In (S₁ ⊓ L) B →
        (∀ y ∈ S₁, y ∉ centralizer (L : Set G) → (∀ b ∈ B, y * b = b * y) →
          ¬ ∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α) → Hyp62At L := by
  intro G _ _ L hL H S₁ hLH hHN hS hNC B hB hno
  intro V _ _ _ Q hQ e hdim hsgn s x hs hxG
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  obtain ⟨e₁, he₁⟩ := ff6p_model_of_oddCore hL hQ e
  have hs₁ : InducesViaP L (Subgroup.center ↥L) hQ e₁ s x := he₁ s x hs
  obtain ⟨fr⟩ := exists_pframe_six_plus hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := ff6p_odd_center hL
  have hP : IsSylow2Of (S₁ ⊓ L) L :=
    sec8t84_sylow_inf_normal hS hLH
      (fun h hh n hn => (Subgroup.mem_normalizer_iff.mp (hHN hh) n).mp hn)
  obtain ⟨y, hyP, hyB⟩ := ff6p_adapt_PB hQ hdim hsgn h2 e₁ hodd fr hP hB
  have hs₂ : InducesViaP L (Subgroup.center ↥L) hQ (ffAdapt h2 e₁ y) s (y⁻¹ * x * y) :=
    inducesViaP_ffAdapt h2 e₁ y hs₁
  have hx₂G : SimInGStar (y⁻¹ * x * y) := (simInGStar_conj_iff x y).mpr hxG
  have hθs : ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨s, hs.1⟩ = y⁻¹ * x * y :=
    (ffTheta6P_eq_iff hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨s, hs.1⟩ _).mpr hs₂
  have hclaim : SimInOmegaStar hQ (y⁻¹ * x * y) := by
    by_contra hxΩ
    obtain ⟨h', hh'H, c, hcC, hsc⟩ := hNC s hs.1
    have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer (L : Set G) hcC
    have hs_eq : (⟨s, hs.1⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨h', hHN hh'H⟩ * ⟨c, hcN⟩ := Subtype.ext hsc
    have hθc : ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨c, hcN⟩ = 1 :=
      (ff6p_theta_eq_one_iff hL hQ hdim hsgn (ffAdapt h2 e₁ y) hcN).mpr hcC
    have hθh : ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨h', hHN hh'H⟩ = y⁻¹ * x * y := by
      have h := hθs
      rw [hs_eq, map_mul, hθc, mul_one] at h
      exact h
    have hh'Ω : ¬ SimInOmegaStar hQ
        (ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨h', hHN hh'H⟩) := by
      rw [hθh]; exact hxΩ
    have hh'G : SimInGStar
        (ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨h', hHN hh'H⟩) := by
      rw [hθh]; exact hx₂G
    obtain ⟨y', hy'N, hy'S, hy'θ⟩ := ff6p_outer_in_sylow hQ hdim hsgn
      (ffAdapt h2 e₁ y) fr hLH hHN hS hyP hh'H hh'G hh'Ω
    have hy'notC : y' ∉ Subgroup.centralizer (L : Set G) := by
      intro hyc
      have h1 : ffTheta6P hQ hdim hsgn (ffAdapt h2 e₁ y) ⟨y', hy'N⟩ = 1 :=
        (ff6p_theta_eq_one_iff hL hQ hdim hsgn (ffAdapt h2 e₁ y) hy'N).mpr hyc
      rw [hy'θ] at h1
      exact ffTs_ne_one fr h1
    have hBL : B ≤ L := hB.1.trans inf_le_right
    have hy'comm : ∀ b ∈ B, y' * b = b * y' := by
      refine (ff6p_commute_img_iff hQ hdim hsgn hz (ffAdapt h2 e₁ y) hy'N hBL).mpr ?_
      rw [hyB]
      intro w hw
      rw [hy'θ]
      exact ffTs_comm_normalizer hQ h2 (ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn)
        fr (Subgroup.le_normalizer hw)
    exact hno y' hy'S hy'notC hy'comm ⟨-1, ff6p_induces_type hQ hdim hsgn
      (ffAdapt h2 e₁ y) hy'N (by rw [hy'θ]; exact ffTs_hasType hQ fr)⟩
  rw [show x = y * (y⁻¹ * x * y) * y⁻¹ from by group]
  exact sec9u_simInOmegaStar_conj hQ h2 y hclaim

theorem ff6p_aut_B_types (hc : FF6PCls)
    (hpocket : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
      ∀ z : G, z ∈ L → (IsI4PlusIn L z ↔ orderOf z = 2 ∧ InducesTypeSome L z 6 1 4 1)) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ φ : (Fin 5 → ZMod 2) → G,
        IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤ →
          (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 2 →
            InducesTypeSome L (φ v) 6 1 2 (-1)) ∧
          (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L (φ v)) := by
  intro G _ _ L hL P hP B hB φ hφ
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ := ff6p_exists_model_PB hL hP hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hBL : B ≤ L := hB.1.trans hP.1
  have hΦ : (ffPhi hz e).toMonoidHom = ff6mPhi e := ff6p_ffPhi_eq hQ hz e
  obtain ⟨ψ, hψ, hψval⟩ := ffIso_permModule_of (ffPhi hz e) hBL hφ
  have hψ' : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr)
      (Subgroup.normalizer
        ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) ⊤ := by
    simpa only [hΦ, hBφ] using hψ
  have htypes := ff6p_star_types_hasType hQ hdim hsgn fr ψ hψ'
  have htheta : ∀ (v : Fin 5 → ZMod 2) (hv : IsEvenVec v) (hvL : φ v ∈ L),
      ffTheta6P hQ hdim hsgn e ⟨φ v, Subgroup.le_normalizer hvL⟩ =
        ffOmegaToSim hQ (ψ v) := by
    intro v hv hvL
    obtain ⟨hvL', hψv⟩ := hψval v hv
    have hsub : (⟨φ v, hvL⟩ : ↥L) = ⟨φ v, hvL'⟩ := Subtype.ext rfl
    have hφψ : ff6mPhi e ⟨φ v, hvL⟩ = ψ v := by
      rw [hψv]
      calc ff6mPhi e ⟨φ v, hvL⟩ = ffPhi hz e ⟨φ v, hvL⟩ := by
            rw [ff6mPhi_apply, ffPhi_apply]
        _ = ffPhi hz e ⟨φ v, hvL'⟩ := by rw [hsub]
    rw [ffTheta6P_of_mem (l := ⟨φ v, hvL⟩), hφψ]
  refine ⟨?_, ?_⟩
  · intro v hv hw
    have hvB : φ v ∈ B := (hφ.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
    have hvL : φ v ∈ L := hBL hvB
    exact ff6p_induces_type hQ hdim hsgn e (Subgroup.le_normalizer hvL)
      (by rw [htheta v hv hvL]; exact htypes.1 v hv hw)
  · intro v hv hw
    have hvB : φ v ∈ B := (hφ.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
    have hvL : φ v ∈ L := hBL hvB
    have h0even : IsEvenVec (0 : Fin 5 → ZMod 2) := by
      unfold IsEvenVec
      simp
    have hφ0 : φ 0 = 1 := by
      have h := hφ.1 0 0 h0even h0even
      rw [add_zero] at h
      exact mul_eq_left.mp h.symm
    have hvv : v + v = 0 := by
      funext i
      exact CharTwo.add_self_eq_zero (v i)
    have hφsq : φ v * φ v = 1 := by
      have h := hφ.1 v v hv hv
      rw [hvv, hφ0] at h
      exact h.symm
    have hφne : φ v ≠ 1 := by
      intro h1
      have hz0 : φ v = φ 0 := h1.trans hφ0.symm
      have hv0 : v = 0 := hφ.2.1 v 0 hv h0even hz0
      have hw0 : vecWeight v = 0 := by rw [hv0]; simp [vecWeight]
      omega
    have hord : orderOf (φ v) = 2 :=
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hφsq) hφne
    have htype : InducesTypeSome L (φ v) 6 1 4 1 :=
      ff6p_induces_type hQ hdim hsgn e (Subgroup.le_normalizer hvL)
        (by rw [htheta v hv hvL]; exact htypes.2 v hv hw)
    exact (hpocket G L hL (φ v) hvL).mpr ⟨hord, htype⟩

end CFSG.OddStandard.SmallF3.Omega

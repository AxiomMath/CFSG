module

public import CFSG.ClassicalInvolution.Asc77.AscT3R10aMain
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bQ8
public import CFSG.ClassicalInvolution.Asc77.AscT3R9Main
public import CFSG.ClassicalInvolution.Asc77.AscT3RInvA
public import CFSG.ClassicalInvolution.Asc77.AscT3R10bSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Pure

theorem mulAut_mul_conj_mul_inv {M : Type*} [Group M] (φ : MulAut M) (x : M) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.conj_apply]

variable {F : Type} [Field F] [Finite F]

theorem mulAut_neg_one (hF : Odd (Nat.card F)) (φ : MulAut SL(2, F)) : φ (-1) = -1 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  have hsq : φ (-1) * φ (-1) = 1 := by
    rw [← map_mul]
    have : (-1 : SL(2, F)) * -1 = 1 := by
      calc (-1 : SL(2, F)) * -1 = -1 * (-1)⁻¹ := by rw [neg_one_inv]
        _ = 1 := mul_inv_cancel _
    rw [this, map_one]
  rcases sl2_sq_eq_one h2 hsq with h | h
  · exfalso
    have : φ (-1) = φ 1 := by rw [h, map_one]
    exact sl2_neg_one_ne_one hF (φ.injective this)
  · exact h

end Pure

section Quat

variable {G : Type} [Group G]

theorem exists_order_four_of_quat {P : Subgroup G}
    (hq : ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ k))) :
    ∃ u₁ ∈ P, u₁ ^ 4 = 1 ∧ u₁ * u₁ ≠ 1 := by
  obtain ⟨k, hk, ⟨φ⟩⟩ := hq
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hq4 : orderOf (QuaternionGroup.xa 0 : QuaternionGroup (2 ^ k)) = 4 :=
    QuaternionGroup.orderOf_xa (n := 2 ^ k) 0
  set x : ↥P := φ.symm (QuaternionGroup.xa 0) with hx
  have hx4 : orderOf x = 4 := by
    rw [hx, MulEquiv.orderOf_eq]
    exact hq4
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · have : x ^ 4 = 1 := by
      rw [← hx4]
      exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  · intro h
    have h1 : x * x = 1 := Subtype.ext (by simpa using h)
    have h2 : x ^ 2 = 1 := by rwa [pow_two]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hx4] at this
    omega

theorem InducesFAut.congr_card {K R R₁ : Subgroup G} {a : G} (h : InducesFAut K R a)
    (hR : Nat.card R = Nat.card R₁) : InducesFAut K R₁ a := by
  obtain ⟨hN, h2, P, hP, hq, hc⟩ := h
  exact ⟨hN, h2, P, hP, hq, hc.trans hR⟩

end Quat

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.r10a_RR'_le_z (d : Std20 p f K K' J S R R' W V z t) {y : G} (hyR : y ∈ R)
    (hyR' : y ∈ R') : y = 1 ∨ y = z := by
  have hzS : z ∈ (S : Subgroup G) := d.hWS d.late_z_mem_W
  have hzR : z ∈ R := by
    rw [d.late_R_eq]
    exact ⟨d.viol.hzK.mem, hzS⟩
  have hzR' : z ∈ R' := by
    rw [d.late_R'_eq]
    exact ⟨d.late_hzK'.mem, hzS⟩
  have hA2 : IsPGroup 2 ↥(R ⊓ R') := S.isPGroup'.to_le (inf_le_left.trans d.hRS)
  have hcard := Sec6Gen.card_le_two_of_le_inf d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm hA2
    (inf_le_left.trans d.hR.1) (inf_le_right.trans d.hR'.1)
  have hz1 := d.viol.hzK.ne_one
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d.viol.hzK.sq) hz1
  have hzeq : Subgroup.zpowers z = R ⊓ R' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzR, hzR'⟩)
      (by rw [Nat.card_zpowers, hzord]; exact hcard)
  have hy : y ∈ Subgroup.zpowers z := hzeq ▸ (⟨hyR, hyR'⟩ : y ∈ R ⊓ R')
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact z_zpow_cases d.viol.hzK.sq k

end Std

variable (p f : ℕ) [Fact p.Prime]

theorem res10aInv : Res10aInv p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  classical
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have h3 : ∀ w ∈ (S : Subgroup G), w * w ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      w ∈ Subgroup.normalizer (K : Set G) := (c9 h8).2.2
  obtain ⟨-, eK, u, a₂, γ, γ', σ, hu, huK, ha₂S, ha₂X, hNa₂, hNb₂, hσ2, hσ1, hphi₁, hphi₂,
    ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩ := d.r9_aux c3 c8 h3
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hK'u := d.late_swap_data hu huK
  obtain ⟨hsq₁, P₁, hP₁, hq₁, hc₁⟩ := field_involution_data hFodd hσ2 hσ1 hNa₂ hn₁ hphi₁ d.hR
  obtain ⟨hsq₂, P₂, hP₂, hq₂, hc₂⟩ := field_involution_data hFodd hσ2 hσ1 hNb₂ hn₂ hphi₂ d.hR
  have hFA₁ : InducesFAut K R a₂ :=
    ⟨hNa₂, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₁, P₁, hP₁, hq₁, hc₁⟩
  have hFA₂ : InducesFAut K R (u⁻¹ * a₂ * u) :=
    ⟨hNb₂, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₂, P₂, hP₂, hq₂, hc₂⟩
  have hFA₂' : InducesFAut K' R' a₂ := by
    have h := hFA₂.conj u
    have e : u * (u⁻¹ * a₂ * u) * u⁻¹ = a₂ := by group
    rwa [huK, hK'u.2.1, e] at h
  have hR'conj : conjSub u R' = R := by
    rw [d.late_R'_eq, late_conjSub_inf, hK'u.1, hK'u.2.2.2, d.late_R_eq]
  have hb₂S : u⁻¹ * a₂ * u ∈ (S : Subgroup G) := S.mul_mem (S.mul_mem (S.inv_mem hu) ha₂S) hu
  have ha₂sq' : a₂ * a₂ ∈ R' := d.r9_cStar_S c8 hu huK (S.mul_mem ha₂S ha₂S) hsq₁
  have hb₂sq' : (u⁻¹ * a₂ * u) * (u⁻¹ * a₂ * u) ∈ R' :=
    d.r9_cStar_S c8 hu huK (S.mul_mem hb₂S hb₂S) hsq₂
  have ha₂sq : a₂ * a₂ ∈ R := by
    have h1 : u * ((u⁻¹ * a₂ * u) * (u⁻¹ * a₂ * u)) * u⁻¹ ∈ conjSub u R' :=
      conj_mem_conjSub hb₂sq'
    rw [hR'conj] at h1
    have e : u * ((u⁻¹ * a₂ * u) * (u⁻¹ * a₂ * u)) * u⁻¹ = a₂ * a₂ := by group
    rwa [e] at h1
  rcases d.r10a_RR'_le_z ha₂sq ha₂sq' with h1 | hz
  · exact ⟨a₂, ha₂S, h1, ha₂X, hFA₁, hFA₂'⟩
  obtain ⟨u₁, hu₁P, hu₁4, hu₁2⟩ := exists_order_four_of_quat hq₁
  have hu₁K : u₁ ∈ K := (inf_le_left : K ⊓ Subgroup.centralizer ({a₂} : Set G) ≤ K) (hP₁.1 hu₁P)
  have hu₁C : a₂ * u₁ = u₁ * a₂ :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      ((inf_le_right : K ⊓ Subgroup.centralizer ({a₂} : Set G) ≤ _) (hP₁.1 hu₁P))).symm
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hu₁sq : u₁ * u₁ = z := by
    have h4 : (u₁ * u₁) * (u₁ * u₁) = 1 := by
      rw [show (u₁ * u₁) * (u₁ * u₁) = u₁ ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
        hu₁4]
    rcases d.viol.hzK.unique (u₁ * u₁) (K.mul_mem hu₁K hu₁K) h4 with h | h
    · exact absurd h hu₁2
    · exact h
  have ha₃sq : (a₂ * u₁) * (a₂ * u₁) = 1 := by
    calc (a₂ * u₁) * (a₂ * u₁) = a₂ * (u₁ * a₂) * u₁ := by group
      _ = a₂ * (a₂ * u₁) * u₁ := by rw [← hu₁C]
      _ = (a₂ * a₂) * (u₁ * u₁) := by group
      _ = 1 := by rw [hz, hu₁sq]; exact hz2
  have hu₁N : u₁ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hu₁K
  have ha₃N : a₂ * u₁ ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hNa₂ hu₁N
  set sb : SL(2, GaloisField p f) := eta K eK ⟨u₁, hu₁K⟩ with hsb
  have hzK : z ∈ K := d.viol.hzK.mem
  have hsb_sq : sb * sb = -1 := by
    have e1 : sb * sb = eta K eK ⟨z, hzK⟩ := by
      rw [hsb, ← map_mul]
      congr 1
      exact Subtype.ext hu₁sq
    rw [e1]
    have h2 : (2 : GaloisField p f) ≠ 0 :=
      CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hFodd
    have hz1 : eta K eK ⟨z, hzK⟩ * eta K eK ⟨z, hzK⟩ = 1 := by
      rw [← map_mul, ← map_one (eta K eK)]
      congr 1
      exact Subtype.ext hz2
    rcases sl2_sq_eq_one h2 hz1 with h | h
    · exfalso
      have hmem := (eta_eq_one_iff K eK ⟨z, hzK⟩).mp h
      have hzG : z ∈ oddCoreOf K := ⟨⟨z, hzK⟩, hmem, rfl⟩
      have hzord : orderOf z = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hz2) d.viol.hzK.ne_one
      have hz2g : IsPGroup 2 (Subgroup.zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; rfl)
      exact d.viol.hzK.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hzG hz2g)
    · exact h
  have hfix : phiG K eK a₂ sb = sb := by
    rw [hsb, phiG_apply_eta hNa₂]
    congr 1
    apply Subtype.ext
    show a₂ * u₁ * a₂⁻¹ = u₁
    rw [hu₁C]
    group
  have hsσ : slFieldAut (GaloisField p f) σ (γ⁻¹ sb) = γ⁻¹ sb := by
    have h := hfix
    rw [hphi₁] at h
    have h' : γ (slFieldAut (GaloisField p f) σ (γ⁻¹ sb)) = sb := h
    apply γ.injective
    rw [h', MulAut.apply_inv_self]
  have hss' : (γ⁻¹ sb) * (γ⁻¹ sb) = -1 := by
    rw [← map_mul, hsb_sq, mulAut_neg_one hFodd]
  obtain ⟨γh, hγh⟩ := exists_conj_eq_conj_mul hFodd hσ2 hσ1 hsσ hss'
  have hphi₃ : phiG K eK (a₂ * u₁) =
      (γ * γh) * slFieldAut (GaloisField p f) σ * (γ * γh)⁻¹ := by
    rw [phiG_mul hNa₂ hu₁N, hphi₁, phiG_of_mem_L hu₁K, ← hsb]
    have e1 : MulAut.conj sb = γ * MulAut.conj (γ⁻¹ sb) * γ⁻¹ := by
      rw [mulAut_mul_conj_mul_inv, MulAut.apply_inv_self]
    have e2 : slFieldAut (GaloisField p f) σ * MulAut.conj (γ⁻¹ sb) =
        MulAut.conj (γ⁻¹ sb) * slFieldAut (GaloisField p f) σ := by
      have h := mulAut_mul_conj_mul_inv (slFieldAut (GaloisField p f) σ) (γ⁻¹ sb)
      rw [hsσ] at h
      calc slFieldAut (GaloisField p f) σ * MulAut.conj (γ⁻¹ sb)
          = (slFieldAut (GaloisField p f) σ * MulAut.conj (γ⁻¹ sb) *
              (slFieldAut (GaloisField p f) σ)⁻¹) * slFieldAut (GaloisField p f) σ := by group
        _ = MulAut.conj (γ⁻¹ sb) * slFieldAut (GaloisField p f) σ := by rw [h]
    calc γ * slFieldAut (GaloisField p f) σ * γ⁻¹ * MulAut.conj sb
        = γ * slFieldAut (GaloisField p f) σ * γ⁻¹ * (γ * MulAut.conj (γ⁻¹ sb) * γ⁻¹) := by
          rw [e1]
      _ = γ * (slFieldAut (GaloisField p f) σ * MulAut.conj (γ⁻¹ sb)) * γ⁻¹ := by group
      _ = γ * (MulAut.conj (γ⁻¹ sb) * slFieldAut (GaloisField p f) σ) * γ⁻¹ := by rw [e2]
      _ = γ * (γh * slFieldAut (GaloisField p f) σ * γh⁻¹) * γ⁻¹ := by rw [hγh]
      _ = (γ * γh) * slFieldAut (GaloisField p f) σ * (γ * γh)⁻¹ := by group
  have hn₃ : (a₂ * u₁) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact ha₃sq
  obtain ⟨hsq₃, P₃, hP₃, hq₃, hc₃⟩ := field_involution_data hFodd hσ2 hσ1 ha₃N hn₃ hphi₃ d.hR
  have hFA₃ : InducesFAut K R (a₂ * u₁) :=
    ⟨ha₃N, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₃, P₃, hP₃, hq₃, hc₃⟩
  have hu₁' : u⁻¹ * u₁ * u ∈ K' := by
    have h1 : u₁ ∈ conjSub u K' := by
      rw [hK'u.1]
      exact hu₁K
    exact mem_conjSub_iff.mp h1
  have hb₃ : u⁻¹ * (a₂ * u₁) * u = (u⁻¹ * a₂ * u) * (u⁻¹ * u₁ * u) := by group
  have hu₁'N : u⁻¹ * u₁ * u ∈ Subgroup.normalizer (K : Set G) := d.late_K'_le hu₁'
  have hu₁'c : phiG K eK (u⁻¹ * u₁ * u) = 1 :=
    (phiG_eq_one_iff hu₁'N).mpr (d.r9_K'_le_cStar hu₁')
  have hb₃N : u⁻¹ * (a₂ * u₁) * u ∈ Subgroup.normalizer (K : Set G) := by
    rw [hb₃]
    exact Subgroup.mul_mem _ hNb₂ hu₁'N
  have hphi₃' : phiG K eK (u⁻¹ * (a₂ * u₁) * u) =
      γ' * slFieldAut (GaloisField p f) σ * γ'⁻¹ := by
    rw [hb₃, phiG_mul hNb₂ hu₁'N, hu₁'c, mul_one]
    exact hphi₂
  have hn₃' : (u⁻¹ * (a₂ * u₁) * u) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    calc u⁻¹ * (a₂ * u₁) * u * (u⁻¹ * (a₂ * u₁) * u)
        = u⁻¹ * ((a₂ * u₁) * (a₂ * u₁)) * u := by group
      _ = 1 := by rw [ha₃sq]; group
  obtain ⟨hsq₃', P₃', hP₃', hq₃', hc₃'⟩ :=
    field_involution_data hFodd hσ2 hσ1 hb₃N hn₃' hphi₃' d.hR
  have hFA₃b : InducesFAut K R (u⁻¹ * (a₂ * u₁) * u) :=
    ⟨hb₃N, (mem_centralizerModOdd_top_iff (L := K)).mpr hsq₃', P₃', hP₃', hq₃', hc₃'⟩
  have hFA₃' : InducesFAut K' R' (a₂ * u₁) := by
    have h := hFA₃b.conj u
    have e : u * (u⁻¹ * (a₂ * u₁) * u) * u⁻¹ = a₂ * u₁ := by group
    rwa [huK, hK'u.2.1, e] at h
  have hu₁C' : u₁ ∈ Subgroup.centralizer ({z} : Set G) := d.r10a_X_le_C (le_sec20X_left hu₁K)
  have ha₃C : a₂ * u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (d.hSz ha₂S) (d.r10a_X_le_C (le_sec20X_left hu₁K))
  have ha₃4 : (a₂ * u₁) ^ 4 = 1 := by
    rw [show (a₂ * u₁) ^ 4 = ((a₂ * u₁) * (a₂ * u₁)) * ((a₂ * u₁) * (a₂ * u₁)) by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc], ha₃sq, one_mul]
  obtain ⟨y, hyC, hyS⟩ := d.exists_conj_into_S ha₃C (isPGroup_zpowers_of_pow_four ha₃4)
  refine ⟨y * (a₂ * u₁) * y⁻¹, hyS, ?_, ?_, ?_⟩
  · calc y * (a₂ * u₁) * y⁻¹ * (y * (a₂ * u₁) * y⁻¹) = y * ((a₂ * u₁) * (a₂ * u₁)) * y⁻¹ := by
          group
      _ = 1 := by rw [ha₃sq]; group
  · intro hX
    have hn := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins (Subgroup.inv_mem _ hyC)
    have h1 : y⁻¹ * (y * (a₂ * u₁) * y⁻¹) * y⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hn _).mp hX
    have e : y⁻¹ * (y * (a₂ * u₁) * y⁻¹) * y⁻¹⁻¹ = a₂ * u₁ := by group
    rw [e] at h1
    apply ha₂X
    have := X.mul_mem h1 (X.inv_mem (le_sec20X_left hu₁K))
    simpa using this
  · have hcardRR' : Nat.card R = Nat.card R' :=
      Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K d.late_mem_K' d.hR d.hR'
    have hK1 := hFA₃.conj y
    have hK2 := hFA₃'.conj y
    rcases d.late_conj_K hyC with h | h
    · have h' : conjSub y K' = K' := (d.late_conj_iff hyC).mp h
      rw [h] at hK1
      rw [h'] at hK2
      exact ⟨hK1.congr_card (late_natCard_conjSub y R),
        hK2.congr_card (late_natCard_conjSub y R')⟩
    · have h' : conjSub y K' = K := by
        rcases d.late_conj_K' hyC with h'' | h''
        · exact h''
        · exact absurd (conjSub_injective y (h.trans h''.symm)) d.ne.symm
      rw [h] at hK1
      rw [h'] at hK2
      exact ⟨hK2.congr_card ((late_natCard_conjSub y R').trans hcardRR'.symm),
        hK1.congr_card ((late_natCard_conjSub y R).trans hcardRR')⟩

theorem c20_10a_of_Y (hY : Res10aY p f) : C20_10a p f :=
  c20_10a_of_res p f (res10aInv p f) hY

end CFSG.ClassicalInvolution.Asc77.T3CII

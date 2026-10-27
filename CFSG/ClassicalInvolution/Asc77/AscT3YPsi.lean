module

public import CFSG.ClassicalInvolution.Asc77.AscT3RStd

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

section Psi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.y_psi (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) :
    ∃ ψ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) →*
        RingAut (GaloisField p f),
      ∀ x : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)),
        ψ x = 1 ↔ (x : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  classical
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hKop : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.one_le_iff_ne_zero.mpr hf, hFcard⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hFcard]
    omega
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.late_mem_K
  obtain ⟨eK⟩ := hz₀.nonempty_equiv
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  obtain ⟨v, hv, hord, hvN⟩ := d.r9_vdata
  obtain ⟨hεv, hρv⟩ := d.r9_eps_v c8 hu huK eK hFodd hKop h4 hv hord hvN
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.to_le inf_le_left
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hRT : R ≤ T := le_inf d.hRS (d.hR.1.trans Subgroup.le_normalizer)
  have hR'T : R' ≤ T := le_inf d.hR'S (d.hR'.1.trans d.late_K'_le)
  have hVT : V ≤ T := le_inf d.hVS (d.hVW.trans d.late_W_le_N_K)
  have hvT : v ∈ T := hVT hvV
  have hRp : ∀ y ∈ T, phiG K eK y = 1 → y ∈ R' := fun y hyT hy1 =>
    d.r9_cStar_S c8 hu huK hyT.1 ((phiG_eq_one_iff hyT.2).mp hy1)
  have hRp' : ∀ y ∈ R', phiG K eK y = 1 := fun y hy =>
    (phiG_eq_one_iff (hTN (hR'T hy))).mpr (d.r9_K'_le_cStar (d.hR'.1 hy))
  have hRR'V_le_X : R ⊔ R' ⊔ V ≤ X :=
    sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX
  have hψker : ∀ x ∈ T, psi hKop K eK v x = 1 → x ∈ X := fun x hxT hψ =>
    hRR'V_le_X (mem_of_psi_eq_one hFodd h4 hT2 hTN hRT d.hR hRp hvV hvT hεv hxT hψ)
  have hψone : ∀ x ∈ (S : Subgroup G) ⊓ X, psi hKop K eK v x = 1 := by
    intro x hx
    have hx' : x ∈ R ⊔ R' ⊔ V := (d.late_SX c3).symm ▸ hx
    exact psi_eq_one_of_mem hρv hεv hTN d.hR.1 hRT hR'T hRp' hvT hv hx'
  have hXT : ∀ x ∈ T, x ∈ X → psi hKop K eK v x = 1 := fun x hxT hxX => hψone x ⟨hxT.1, hxX⟩
  refine ⟨{ toFun := fun x => psi hKop K eK v (x : G)
            map_one' := psi_one v
            map_mul' := fun x y => psi_mul hρv (hTN x.2) (hTN y.2) }, fun x => ?_⟩
  exact ⟨fun h => hψker x x.2 h, fun h => hXT x x.2 h⟩

theorem y_eq_of_sq_eq_one {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {x y : Q}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have : Fintype Q := Fintype.ofFinite Q
  have hcard := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset Q) ⊆ Finset.univ.filter (fun a : Q => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx
    · exact hy
  have h3 : ({1, x, y} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hxy
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem Std20.y_comm_T (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) {x y : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))
    (hy : y ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) :
    ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨ψ, hψ⟩ := d.y_psi c3 c8
  have h1 : ψ ⁅(⟨x, hx⟩ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))),
      (⟨y, hy⟩ : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)))⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm _ _ _
  have h2 := (hψ _).mp h1
  simpa [commutatorElement_def] using h2

theorem Std20.y_sq_mem_X (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R) (hf : f % 4 = 2) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) :
    x * x ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨ψ, hψ⟩ := d.y_psi c3 c8
  have hT2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) :=
    S.isPGroup'.to_le inf_le_left
  set x' : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) := ⟨x, hx⟩ with hx'
  obtain ⟨n, hn⟩ := hT2 x'
  have hψn : (ψ x') ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
  have hf0 : f ≠ 0 := by omega
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    (Fact.out : p.Prime) (GaloisField p f) (GaloisField.card p f hf0)).1
  have hdvd1 : orderOf (ψ x') ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hψn
  have hdvd2 : orderOf (ψ x') ∣ f := by
    have h := orderOf_dvd_natCard (ψ x')
    rwa [hcard] at h
  have hsq : (ψ x') ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [hk']; simp
      · rw [hk']; simp
    · exfalso
      have h4 : 4 ∣ f := by
        have h1 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 h
        rw [hk'] at hdvd2
        exact (by simpa using h1 : 4 ∣ 2 ^ k).trans hdvd2
      omega
  have h1 : ψ (x' * x') = 1 := by rw [map_mul, ← sq, hsq]
  exact (hψ _).mp h1

theorem Std20.y_psi_eq (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (c8 : Concl20_8 S K' R)
    (hsq : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G),
      x * x ∈ sec20X (CoreAssembly.conjClass K) z K K') {x y : G}
    (hx : x ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))
    (hy : y ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G))
    (hxX : x ∉ sec20X (CoreAssembly.conjClass K) z K K')
    (hyX : y ∉ sec20X (CoreAssembly.conjClass K) z K K') :
    x⁻¹ * y ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨ψ, hψ⟩ := d.y_psi c3 c8
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcc := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    (Fact.out : p.Prime) (GaloisField p f) (GaloisField.card p f hf)
  have : IsCyclic (RingAut (GaloisField p f)) := hcc.2
  have : Finite (RingAut (GaloisField p f)) := Nat.finite_of_card_ne_zero (by
    rw [hcc.1]; exact hf)
  set x' : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) := ⟨x, hx⟩ with hx'
  set y' : ↥((S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G)) := ⟨y, hy⟩ with hy'
  have h1 : ψ x' ≠ 1 := fun h => hxX ((hψ x').mp h)
  have h2 : ψ y' ≠ 1 := fun h => hyX ((hψ y').mp h)
  have h1' : (ψ x') ^ 2 = 1 := by
    rw [sq, ← map_mul]
    exact (hψ _).mpr (hsq x hx)
  have h2' : (ψ y') ^ 2 = 1 := by
    rw [sq, ← map_mul]
    exact (hψ _).mpr (hsq y hy)
  have h3 : ψ x' = ψ y' := y_eq_of_sq_eq_one h1' h2' h1 h2
  have h4 : ψ (x'⁻¹ * y') = 1 := by rw [map_mul, map_inv, h3, inv_mul_cancel]
  have h5 := (hψ _).mp h4
  simpa using h5

end Psi

end CFSG.ClassicalInvolution.Asc77.T3CII

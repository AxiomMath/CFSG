module

public import CFSG.ClassicalInvolution.Asc77.AscSCH04
public import CFSG.RankThree.CentralLift.ClassicalExactScalarCover
public import CFSG.ClassicalInvolution.Asc77.AscT7Z15

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralLift

open Matrix

theorem det_eq_one_of_mem_closure {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {S : Set (GL ι K)} (hS : ∀ g ∈ S, (g : Matrix ι ι K).det = 1) {x : GL ι K}
    (hx : x ∈ Subgroup.closure S) : (x : Matrix ι ι K).det = 1 := by
  have hle : Subgroup.closure S ≤ (Matrix.GeneralLinearGroup.det (n := ι) (R := K)).ker := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hS g hg]; rfl)
  have := MonoidHom.mem_ker.1 (hle hx)
  have h2 := congrArg Units.val this
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2

theorem pow_four_eq_one_of_scalar {K : Type} [Field K] {H : Subgroup (GL (Fin 4) K)}
    (hdet : ∀ g ∈ H, (g : Matrix (Fin 4) (Fin 4) K).det = 1) :
    ∀ d ∈ (StatedScalars (Fin 4) K).subgroupOf H, d ^ 4 = 1 := by
  intro d hd
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hd
  have h1 : (c : K) ^ 4 = 1 := by
    have := hdet d.1 d.2
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal] at this
    simpa using this
  have h2 : c ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow, h2, map_one]
  rfl

theorem split_SL_large {K : Type} [Field K] [Finite K] {ℓ f r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (E : Type) [Group E] [Finite E] (π : E →* StatedSL 4 K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup r π.ker) :
    ∃ s : StatedSL 4 K →* E, ∀ x, π (s x) = x := by
  refine CFSG.RankThree.CentralLiftU.forall_section_of_mulEquiv
    (specialLinearGroupEquivStatedSL 4 K).symm (fun ρ hρ hρC hρp => ?_) π hπ hC hCp
  obtain ⟨⟨s, hs, -⟩, -⟩ := LinearRoots.odd_field_linear_central_large_prime_extension_splitting
    hr hr3 hℓ hℓodd hf hK (n := 4) (by norm_num) ρ hρ hρC hρp
  exact ⟨s, DFunLike.congr_fun hs⟩

theorem split_SU_large {K : Type} [Field K] {ℓ f r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (E : Type) [Group E] [Finite E] (π : E →* StatedSU 4 (ℓ ^ f) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup r π.ker) :
    ∃ s : StatedSU 4 (ℓ ^ f) K →* E, ∀ x, π (s x) = x :=
  statedSU_forall_section hr hr3 hℓ hℓodd hf hK (n := 4) (by norm_num) (Or.inr (Or.inl ⟨2, rfl⟩))
    π hπ hC hCp

theorem split_Sp_large {K : Type} [Field K] [Finite K] {ℓ f r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hℓ : ℓ.Prime) (hℓodd : Odd ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (E : Type) [Group E] [Finite E] (π : E →* StatedSp 2 K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup r π.ker) :
    ∃ s : StatedSp 2 K →* E, ∀ x, π (s x) = x :=
  statedSp_forall_section hr hr3 hℓ hℓodd hf hK (n := 2) (by norm_num) π hπ hC hCp

@[expose] def Split3SL : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 5 ≤ ℓ ^ f →
    Nat.card K = ℓ ^ f → ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 4 K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 3 π.ker →
        ∃ s : StatedSL 4 K →* E, ∀ x, π (s x) = x

@[expose] def Split3SU : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 5 ≤ ℓ ^ f →
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ (E : Type) [Group E] [Finite E]
      (π : E →* StatedSU 4 (ℓ ^ f) K), Function.Surjective π → π.ker ≤ Subgroup.center E →
        IsPGroup 3 π.ker → ∃ s : StatedSU 4 (ℓ ^ f) K →* E, ∀ x, π (s x) = x

@[expose] def Split3Sp : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 5 ≤ ℓ ^ f →
    Nat.card K = ℓ ^ f → ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp 2 K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 3 π.ker →
        ∃ s : StatedSp 2 K →* E, ∀ x, π (s x) = x

theorem oddCenterClassical_of_split_three (hSL : Split3SL) (hSU : Split3SU) (hSp : Split3Sp) :
    T7Z.OddCenterClassical := by
  intro L _ _ hL t n p f hp hp2 hq ht hmodel N hN hNodd
  by_contra hNne
  have hperf : Group.IsPerfect L := ⟨hL.1⟩
  have hN1 : Nat.card N ≠ 1 := fun h => hNne (Subgroup.card_eq_one.1 h)
  obtain ⟨r, hr, hrN⟩ := Nat.exists_prime_and_dvd hN1
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 hrN)
  have hrZ : r ∣ Nat.card (Subgroup.center L) := hrN.trans (Subgroup.card_dvd_of_le hN)
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    refine not_dvd_card_center_of_split (H := StatedSL 4 K)
      (pow_four_eq_one_of_scalar fun g hg => ?_) hr2 ?_ e hrZ
    · exact det_eq_one_of_mem_closure (fun g hg => hg) hg
    · intro E _ _ π hπ hC hCp
      by_cases hr3 : r = 3
      · subst hr3
        exact hSL K p f hp hp2 hq hK E π hπ hC hCp
      · exact split_SL_large hr (by have := hr.two_le; omega) hp hpodd hf1 hK E π hπ hC hCp
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    refine not_dvd_card_center_of_split (H := StatedSU 4 (p ^ f) K)
      (pow_four_eq_one_of_scalar fun g hg => ?_) hr2 ?_ e hrZ
    · exact det_eq_one_of_mem_closure (fun g hg => hg.1) hg
    · intro E _ _ π hπ hC hCp
      by_cases hr3 : r = 3
      · subst hr3
        exact hSU K p f hp hp2 hq hK E π hπ hC hCp
      · exact split_SU_large hr (by have := hr.two_le; omega) hp hpodd hf1 hK E π hπ hC hCp
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
    refine not_dvd_card_center_of_split (H := StatedSp 2 K) ?_ hr2 ?_ e hrZ
    · intro d hd
      have hcard := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two 2 K
      have h1 : (⟨d, hd⟩ : (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) ^
          Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) = 1 :=
        pow_card_eq_one'
      have hpos : 0 < Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) :=
        Nat.card_pos
      have hdvd : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) ∣ 4 := by
        have h12 : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) = 1 ∨
            Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) = 2 := by
          omega
        rcases h12 with h | h <;> rw [h] <;> norm_num
      obtain ⟨k, hk⟩ := hdvd
      have h2 : (⟨d, hd⟩ : (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) ^ 4 =
          1 := by rw [hk, pow_mul, h1, one_pow]
      exact congrArg Subtype.val h2
    · intro E _ _ π hπ hC hCp
      by_cases hr3 : r = 3
      · subst hr3
        exact hSp K p f hp hp2 hq hK E π hπ hC hCp
      · exact split_Sp_large hr (by have := hr.two_le; omega) hp hpodd hf1 hK E π hπ hC hCp

theorem split_of_perfect_ker_eq_bot {G : Type} [Group G] [Finite G] [Group.IsPerfect G] {r : ℕ}
    (hperf : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* G),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup r π.ker → π.ker = ⊥)
    (E : Type) [Group E] [Finite E] (π : E →* G) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup r π.ker) :
    ∃ s : G →* E, ∀ x, π (s x) = x := by
  obtain ⟨⟨s, hs, -⟩, -⟩ := splitting_of_perfect_case π hπ hC fun D hD hDs => by
    have : Group.IsPerfect D := hD
    exact hperf D (π.comp D.subtype) hDs (ker_comp_subtype_le_center π hC D)
      (isPGroup_ker_comp_subtype π hCp D)
  exact ⟨s, DFunLike.congr_fun hs⟩

end CFSG.ClassicalInvolution.Asc77.SCH

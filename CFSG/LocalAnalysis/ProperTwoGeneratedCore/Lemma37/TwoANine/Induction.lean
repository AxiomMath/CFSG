module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionMaximal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly CFSG.Semidihedral.Principal.PrimewiseScalar

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_le_isPGroup {p : ℕ} [Fact p.Prime] {C A B : Subgroup X} (hA : IsPGroup p A)
    (hB : IsPGroup p B) (hAC : A ≤ C) (hBC : B ≤ C) :
    ∃ c ∈ C, ∃ T : Subgroup X, IsPGroup p T ∧ T ≤ C ∧ A ≤ T ∧
      B.map (MulAut.conj c).toMonoidHom ≤ T := by
  obtain ⟨T₀, hT₀⟩ := (hA.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨T₁, hT₁⟩ := (hB.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T₁ T₀
  refine ⟨c, c.2, (T₀ : Subgroup C).map C.subtype, T₀.isPGroup'.map _, Subgroup.map_subtype_le _,
    ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hAC]
    exact Subgroup.map_mono hT₀
  · rintro _ ⟨b, hb, rfl⟩
    have h := Subgroup.smul_mem_pointwise_smul (⟨b, hBC hb⟩ : C) (MulAut.conj c)
      (T₁ : Subgroup C) (hT₁ (Subgroup.mem_subgroupOf.mpr hb))
    rw [← Sylow.coe_subgroup_smul, hc] at h
    exact ⟨_, h, rfl⟩

namespace MinimalCounterexample

variable {S : Sylow 2 X} {t : X}

theorem isSylowOf_signalizerJoin (hX : MinimalCounterexample X S t) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsCandidate S t p P)
    (hmax : ∀ Q, IsCandidate S t p Q → Nat.card Q ≤ Nat.card P) {A : Subgroup X}
    (hAS : A ≤ S) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16) :
    IsSylowOf (signalizerJoin A) p P := by
  obtain ⟨g, hgS, hgt⟩ := hX.exists_conj
  obtain ⟨hWodd, -, hWmax, hSW, -⟩ :=
    signalizerJoin_of_conj_ne S hX.central hX.twoANine hgS hgt hAS hA2 hA
  have hPW : P ≤ signalizerJoin A :=
    hWmax P (odd_card_of_isPGroup hp2 hP.isPGroup) (hAS.trans hP.le_normalizer)
  have hNodd : Odd (Nat.card (signalizerJoin A ⊓ normalizer (P : Set X) : Subgroup X)) :=
    hWodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hSN : (S : Subgroup X) ≤
      normalizer ((signalizerJoin A ⊓ normalizer (P : Set X) : Subgroup X) : Set X) :=
    fun s hs => inf_mem_normalizer (hSW hs) (Subgroup.le_normalizer (hP.le_normalizer hs))
  obtain ⟨P₁, hP₁, hSP₁⟩ := exists_isSylowOf_le_normalizer (p := p) hNodd S.isPGroup' hSN
  have hPP₁ : P ≤ P₁ := le_isSylowOf_of_le_normalizer hP₁ hP.isPGroup
    (le_inf hPW Subgroup.le_normalizer) inf_le_right
  rw [hX.eq_of_le_of_isPGroup hp2 hP hmax (isPGroup_of_isSylowOf hP₁) hPP₁ hSP₁] at hP₁
  exact isSylowOf_of_isSylowOf_inf_normalizer hPW hP₁

theorem exists_mem_normalizer_signalizerJoin (hX : MinimalCounterexample X S t) {A : Subgroup X}
    (hAS : A ≤ S) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16) :
    ∃ y ∈ normalizer (signalizerJoin A : Set X), y * t * y⁻¹ ∈ (S : Subgroup X) ∧
      y * t * y⁻¹ ≠ t := by
  obtain ⟨u, huA, hu1, hut⟩ : ∃ u ∈ A, u ≠ 1 ∧ u ≠ t := by
    by_contra h
    have hle : A ≤ zpowers t := fun u hu => by
      by_cases hu1 : u = 1
      · rw [hu1]
        exact one_mem _
      · by_cases hut : u = t
        · rw [hut]
          exact mem_zpowers t
        · exact absurd ⟨u, hu, hu1, hut⟩ h
    have h16 := Subgroup.card_le_of_le hle
    rw [hA, Nat.card_zpowers, hX.central.2.1] at h16
    norm_num at h16
  have hu : orderOf u = 2 := orderOf_eq_prime (hA2 u huA) hu1
  obtain ⟨x, hxu⟩ := isConj_iff.mp (hX.isConj hu)
  have hAC : A ≤ centralizer ({u} : Set X) := le_centralizer_of_sq_eq_one hA2 huA
  have hSC : (S : Subgroup X).map (MulAut.conj x).toMonoidHom ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxu]
    have hst := hX.central.2.2 s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * s * x⁻¹ * (x * t * x⁻¹) = x * (s * t) * x⁻¹ := by group
      _ = x * (t * s) * x⁻¹ := by rw [hst]
      _ = x * t * x⁻¹ * (x * s * x⁻¹) := by group
  obtain ⟨c, hcC, T, hT, hTC, hAT, hST⟩ :=
    exists_conj_le_isPGroup (isPGroup_of_sq_eq_one hA2) (S.isPGroup'.map _) hAC hSC
  have hA'T : A.map (MulAut.conj (c * x)).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    refine hST ⟨x * a * x⁻¹, ⟨a, hAS ha, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hW := signalizerJoin_eq_of_le_isPGroup (fun b hb => hX.isTwoANine hb) hu hA2 hA
    (A' := A.map (MulAut.conj (c * x)).toMonoidHom)
    (by rintro _ ⟨a, ha, rfl⟩; rw [← map_pow, hA2 a ha, map_one])
    (by rw [Subgroup.card_map_of_injective (MulAut.conj (c * x)).injective, hA]) hT hTC hAT hA'T
  have hyt : c * x * t * (c * x)⁻¹ = u := by
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c * x * t * (c * x)⁻¹ = c * (x * t * x⁻¹) * c⁻¹ := by group
      _ = u := by rw [hxu, hcu, mul_inv_cancel_right]
  refine ⟨c * x, mem_normalizer_of_map_conj_eq (by rw [map_conj_signalizerJoin, ← hW]), ?_, ?_⟩
  · rw [hyt]
    exact hAS huA
  · rw [hyt]
    exact hut

theorem conj_eq_of_mem_normalizer_signalizerJoin (hX : MinimalCounterexample X S t) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {P : Subgroup X} (hP : IsCandidate S t p P)
    (hmax : ∀ Q, IsCandidate S t p Q → Nat.card Q ≤ Nat.card P) {A : Subgroup X}
    (hAS : A ≤ S) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16) {y : X}
    (hy : y ∈ normalizer (signalizerJoin A : Set X)) (hyS : y * t * y⁻¹ ∈ (S : Subgroup X)) :
    y * t * y⁻¹ = t := by
  obtain ⟨g, hgS, hgt⟩ := hX.exists_conj
  obtain ⟨hWodd, -, -, hSW, -⟩ :=
    signalizerJoin_of_conj_ne S hX.central hX.twoANine hgS hgt hAS hA2 hA
  obtain ⟨w, hwW, hwy⟩ :=
    exists_mem_inv_mul_mem_normalizer (hX.isSylowOf_signalizerJoin hp2 hP hmax hAS hA2 hA) hy
  set W := signalizerJoin A
  set K := oddCoreOf (normalizer (P : Set X))
  have htW : t ∈ normalizer (W : Set X) := hSW hX.central.1
  have hwN : w ∈ normalizer (W : Set X) := Subgroup.le_normalizer hwW
  have hnN : w⁻¹ * y ∈ normalizer (W : Set X) :=
    (normalizer _).mul_mem ((normalizer _).inv_mem hwN) hy
  have hk : w⁻¹ * y * t * (w⁻¹ * y)⁻¹ * t⁻¹ ∈ K :=
    hX.commutator_mem_oddCoreOf hP.le_normalizer hP.covered (hP.normalizer_ne_top hX hp2) hwy
  have hkN : w⁻¹ * y * t * (w⁻¹ * y)⁻¹ * t⁻¹ ∈ normalizer (W : Set X) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).mul_mem hnN htW)
      ((normalizer _).inv_mem hnN)) ((normalizer _).inv_mem htW)
  have hLodd : Odd (Nat.card ((K ⊓ normalizer (W : Set X)) ⊔ W : Subgroup X)) :=
    odd_card_sup_of_le_normalizer inf_le_right
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)) hWodd
  have hmem : y * t * y⁻¹ * t⁻¹ ∈ ((K ⊓ normalizer (W : Set X)) ⊔ W : Subgroup X) := by
    rw [show y * t * y⁻¹ * t⁻¹ = w * (w⁻¹ * y * t * (w⁻¹ * y)⁻¹ * t⁻¹) * (t * w⁻¹ * t⁻¹) by
      group]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hwW)
      (Subgroup.mem_sup_left ⟨hk, hkN⟩)) (Subgroup.mem_sup_right ?_)
    exact (Subgroup.mem_normalizer_iff.mp htW _).mp (W.inv_mem hwW)
  have h := eq_one_of_mem_of_isPGroup_of_odd S.isPGroup' hLodd
    ((S : Subgroup X).mul_mem hyS ((S : Subgroup X).inv_mem hX.central.1)) hmem
  rwa [mul_inv_eq_one] at h

theorem oddCentralizer_eq_bot (hX : MinimalCounterexample X S t) : oddCentralizer t = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd ((Subgroup.one_lt_card_iff_ne_bot _).mpr hne).ne'
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCentralizer t)) (even_iff_two_dvd.mpr hpdvd)
  obtain ⟨P₀, h₀⟩ := exists_isCandidate hX.central hpdvd
  obtain ⟨P, hP, hmax⟩ := exists_isCandidate_max h₀
  obtain ⟨A, hAS, hA2, hA, -⟩ :=
    exists_le_sylow_of_isCentralInvolution S hX.central hX.twoANine
  obtain ⟨y, hy, hyS, hyt⟩ := hX.exists_mem_normalizer_signalizerJoin hAS hA2 hA
  exact hyt (hX.conj_eq_of_mem_normalizer_signalizerJoin hp2 hP hmax hAS hA2 hA hy hyS)

end MinimalCounterexample

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

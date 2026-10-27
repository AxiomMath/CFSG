module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS4
public import CFSG.ClassicalInvolution.Asc77.AscFusionS3

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups Pointwise

section Pure

variable {G : Type} [Group G]

section TwinDiag

variable {z t a a' : G}

theorem twin_diag_identities (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    (ha2 : a * a = z) (ha' : a' = t * a * t⁻¹) (haa' : a * a' = a' * a) :
    a' * a' = z ∧ (a * a') * (a * a') = 1 ∧ z * (a * a') = (a * a') * z ∧
      t * (a * a') = (a * a') * t ∧ a⁻¹ * t * a = t * (a * a') * z ∧ a⁻¹ * a' = z * (a * a') ∧
      a' * t = t * a ∧ t * a' = a * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hza : a * z = z * a := by
    calc a * z = a * (a * a) := by rw [ha2]
      _ = (a * a) * a := by group
      _ = z * a := by rw [ha2]
  have hai : a⁻¹ = a * z := by
    apply inv_eq_of_mul_eq_one_right
    calc a * (a * z) = (a * a) * z := by group
      _ = 1 := by rw [ha2, hz2]
  have hta : a' * t = t * a := by
    rw [ha', hti]
    calc t * a * t * t = t * a * (t * t) := by group
      _ = t * a := by rw [ht2, mul_one]
  have hta' : t * a' = a * t := by
    rw [ha', hti]
    calc t * (t * a * t) = (t * t) * a * t := by group
      _ = a * t := by rw [ht2, one_mul]
  have ha'2 : a' * a' = z := by
    calc a' * a' = (a' * t) * (t * a') := by
          calc a' * a' = a' * (t * t) * a' := by rw [ht2, mul_one]
            _ = (a' * t) * (t * a') := by group
      _ = (t * a) * (a * t) := by rw [hta, hta']
      _ = t * (a * a) * t := by group
      _ = t * z * t := by rw [ha2]
      _ = z * (t * t) := by rw [← hzt]; group
      _ = z := by rw [ht2, mul_one]
  have hzaa : z * a' = a' * z := by
    calc z * a' = z * (t * a * t) := by rw [ha', hti]
      _ = (z * t) * a * t := by group
      _ = (t * z) * a * t := by rw [hzt]
      _ = t * (z * a) * t := by group
      _ = t * (a * z) * t := by rw [hza]
      _ = (t * a * t) * z := by
          calc t * (a * z) * t = t * a * (z * t) := by group
            _ = t * a * (t * z) := by rw [hzt]
            _ = (t * a * t) * z := by group
      _ = a' * z := by rw [ha', hti]
  have hd2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← haa']
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha2, ha'2, hz2]
  have hzd : z * (a * a') = (a * a') * z := by
    calc z * (a * a') = (z * a) * a' := by group
      _ = (a * z) * a' := by rw [hza]
      _ = a * (z * a') := by group
      _ = a * (a' * z) := by rw [hzaa]
      _ = (a * a') * z := by group
  have htd : t * (a * a') = (a * a') * t := by
    calc t * (a * a') = (t * a) * a' := by group
      _ = (a' * t) * a' := by rw [hta]
      _ = a' * (t * a') := by group
      _ = a' * (a * t) := by rw [hta']
      _ = (a' * a) * t := by group
      _ = (a * a') * t := by rw [haa']
  have hat : a⁻¹ * t * a = t * (a * a') * z := by
    calc a⁻¹ * t * a = a⁻¹ * (t * a) := by group
      _ = a⁻¹ * (a' * t) := by rw [hta]
      _ = (a * z) * a' * t := by rw [hai]; group
      _ = (z * a) * a' * t := by rw [hza]
      _ = z * (a * a') * t := by group
      _ = t * (a * a') * z := by
          calc z * (a * a') * t = (a * a') * z * t := by rw [hzd]
            _ = (a * a') * (z * t) := by group
            _ = (a * a') * (t * z) := by rw [hzt]
            _ = ((a * a') * t) * z := by group
            _ = (t * (a * a')) * z := by rw [htd]
  have hai' : a⁻¹ * a' = z * (a * a') := by
    calc a⁻¹ * a' = (a * z) * a' := by rw [hai]
      _ = (z * a) * a' := by rw [hza]
      _ = z * (a * a') := by group
  exact ⟨ha'2, hd2, hzd, htd, hat, hai', hta, hta'⟩

end TwinDiag

theorem kappa_conj_eq {z t κ : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    (hκ2 : κ * κ = t) (hκz : z⁻¹ * κ * z = κ⁻¹) : κ⁻¹ * z * κ = z * t := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  rw [hzi] at hκz
  have h1 : z * κ = κ⁻¹ * z := by
    calc z * κ = (z * κ * z) * z⁻¹ := by group
      _ = κ⁻¹ * z⁻¹ := by rw [hκz]
      _ = κ⁻¹ * z := by rw [hzi]
  calc κ⁻¹ * z * κ = κ⁻¹ * (z * κ) := by group
    _ = κ⁻¹ * (κ⁻¹ * z) := by rw [h1]
    _ = (κ * κ)⁻¹ * z := by group
    _ = t⁻¹ * z := by rw [hκ2]
    _ = t * z := by rw [inv_eq_of_mul_eq_one_right ht2]
    _ = z * t := hzt.symm

theorem conj_chain_t_to_d {z t d a κ c : G} (hz2 : z * z = 1) (ht2 : t * t = 1)
    (hzt : z * t = t * z) (hzd : z * d = d * z) (htd : t * d = d * t)
    (hat : a⁻¹ * t * a = t * d * z) (hκ2 : κ * κ = t) (hκz : z⁻¹ * κ * z = κ⁻¹)
    (hκd : κ * d = d * κ) (hc : c * d * c⁻¹ = z * d) :
    (a * κ * c)⁻¹ * t * (a * κ * c) = d := by
  have hκt : κ * t = t * κ := by
    calc κ * t = κ * (κ * κ) := by rw [hκ2]
      _ = (κ * κ) * κ := by group
      _ = t * κ := by rw [hκ2]
  have hκ'z : κ⁻¹ * z * κ = z * t := kappa_conj_eq hz2 ht2 hzt hκ2 hκz
  have hκ't : κ⁻¹ * t * κ = t := by
    calc κ⁻¹ * t * κ = κ⁻¹ * (t * κ) := by group
      _ = κ⁻¹ * (κ * t) := by rw [hκt]
      _ = t := by group
  have hκ'd : κ⁻¹ * d * κ = d := by
    calc κ⁻¹ * d * κ = κ⁻¹ * (d * κ) := by group
      _ = κ⁻¹ * (κ * d) := by rw [hκd]
      _ = d := by group
  have h1 : κ⁻¹ * (t * d * z) * κ = d * z := by
    calc κ⁻¹ * (t * d * z) * κ = (κ⁻¹ * t * κ) * (κ⁻¹ * d * κ) * (κ⁻¹ * z * κ) := by group
      _ = t * d * (z * t) := by rw [hκ't, hκ'd, hκ'z]
      _ = d * z * (t * t) := by
          calc t * d * (z * t) = (t * d) * (z * t) := rfl
            _ = d * t * (z * t) := by rw [htd]
            _ = d * (t * z) * t := by group
            _ = d * (z * t) * t := by rw [← hzt]
            _ = d * z * (t * t) := by group
      _ = d * z := by rw [ht2, mul_one]
  have e : (a * κ * c)⁻¹ * t * (a * κ * c) = c⁻¹ * (κ⁻¹ * (a⁻¹ * t * a) * κ) * c := by group
  rw [e, hat, h1]
  have hdz : d * z = z * d := hzd.symm
  rw [hdz]
  have hcz : c⁻¹ * (z * d) * c = d := by
    have := congrArg (fun x => c⁻¹ * x * c) hc
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
    calc c⁻¹ * (z * d) * c = c⁻¹ * (c * d * c⁻¹) * c := by rw [hc]
      _ = d := by group
  exact hcz

theorem conj_chain_c0 {z d ι c : G} (hz2 : z * z = 1) (hd2 : d * d = 1) (hzd : z * d = d * z)
    (hι2 : ι * ι = d) (hιz : z⁻¹ * ι * z = ι⁻¹) (hιd : ι * d = d * ι)
    (hcz : c * z = z * c) (hc : c * d * c⁻¹ = z * d) :
    (ι * c)⁻¹ * z * (ι * c) = d ∧ (ι * c)⁻¹ * d * (ι * c) = z * d := by
  have hι'z : ι⁻¹ * z * ι = z * d := kappa_conj_eq hz2 hd2 hzd hι2 hιz
  have hι'd : ι⁻¹ * d * ι = d := by
    calc ι⁻¹ * d * ι = ι⁻¹ * (d * ι) := by group
      _ = ι⁻¹ * (ι * d) := by rw [hιd]
      _ = d := by group
  have hcz' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := by group
  have hzd' : c⁻¹ * (z * d) * c = d := by
    calc c⁻¹ * (z * d) * c = c⁻¹ * (c * d * c⁻¹) * c := by rw [hc]
      _ = d := by group
  have hdd : c⁻¹ * d * c = z * d := by
    calc c⁻¹ * d * c = (c⁻¹ * z * c) * (c⁻¹ * (z * d) * c) := by
          have hd' : d = z * (z * d) := by rw [← mul_assoc, hz2, one_mul]
          calc c⁻¹ * d * c = c⁻¹ * (z * (z * d)) * c := by rw [← hd']
            _ = (c⁻¹ * z * c) * (c⁻¹ * (z * d) * c) := by group
      _ = z * d := by rw [hcz', hzd']
  constructor
  · calc (ι * c)⁻¹ * z * (ι * c) = c⁻¹ * (ι⁻¹ * z * ι) * c := by group
      _ = d := by rw [hι'z, hzd']
  · calc (ι * c)⁻¹ * d * (ι * c) = c⁻¹ * (ι⁻¹ * d * ι) * c := by group
      _ = z * d := by rw [hι'd, hdd]


end Pure

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_kappa_centralized (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {J : Subgroup G} {t z d : G}
    (hJ : IsClassicalMember p f J t) (hz2 : z * z = 1) (hd2 : d * d = 1) (hzd : z * d = d * z)
    (hzN : z ∈ Subgroup.normalizer (J : Set G)) (hdN : d ∈ Subgroup.normalizer (J : Set G))
    (hznt : ¬ ∀ k ∈ J, ⁅z, k⁆ ∈ oddCoreOf J) (hdtriv : ∀ k ∈ J, ⁅d, k⁆ ∈ oddCoreOf J) :
    ∃ κ ∈ J, κ * κ = t ∧ z⁻¹ * κ * z = κ⁻¹ ∧ κ * d = d * κ := by
  classical
  have hE2 : IsPGroup 2 (Subgroup.closure {z, d}) := isPGroup_closure_pair hz2 hd2 hzd
  have hEN : Subgroup.closure {z, d} ≤ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzN
    · exact hdN
  obtain ⟨R, hR2, hER, hRJ⟩ := exists_sylow_normalized hE2 hEN
  have hzR : z ∈ R := hER (Subgroup.subset_closure (by simp))
  have hdR : d ∈ R := hER (Subgroup.subset_closure (by simp))
  obtain ⟨κ, hκ, hκ2, hκz⟩ :=
    exists_inverted_involution_member hp2 hJ hq hR2 hRJ hzR hz2 hzN hznt
  refine ⟨κ, hκ.2, hκ2, hκz, ?_⟩
  have h1 : ⁅d, κ⁆ ∈ oddCoreOf J := hdtriv κ hκ.2
  have h2 : ⁅d, κ⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hdR hκ.1) (R.inv_mem hdR)) (R.inv_mem hκ.1)
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅d, κ⁆) := hR2.to_le (Subgroup.zpowers_le.mpr h2)
  have h4 : ⁅d, κ⁆ = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) h1 h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm


theorem exists_twin_diag_element (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {K : Subgroup G} {z t : G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hKz : IsUniqueInvolution K z) (ht2 : t * t = 1)
    (hzt : z * t = t * z) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    ∃ a ∈ K, a * a = z ∧ a * (t * a * t⁻¹) = (t * a * t⁻¹) * a := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht2' : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_of_sq_sq (by rw [ht2, one_mul])
  have hvK : conjSub t⁻¹ K ≠ K := fun h =>
    htK (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  have hn : t * t ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht2]
    exact (Subgroup.normalizer (K : Set G)).one_mem
  obtain ⟨R, hR2, htR, -, hRK, -, hcomm, hinv⟩ :=
    exists_twin_sylow hp2 hq h₀ hK hKz ht2' hzt.symm hvK hn
  have hKmem : IsClassicalMember p f K z := isClassicalMember_of_mem_conjClass hp2 hq h₀ hK hKz
  obtain ⟨a, haR, ha2⟩ := exists_sq_eq_of_isSylow2In hp2 hq hKmem hRK
  have h1 := hinv a haR
  have h2 := hcomm a haR _ h1
  rw [hti] at h1 h2
  refine ⟨a, haR.2, ha2, ?_⟩
  rw [hti]
  simpa [hti] using h2


theorem twin_product_action (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {A B : Subgroup G} {d : G}
    (hA : A ∈ CoreAssembly.conjClass K₀) (hB : B ∈ CoreAssembly.conjClass K₀)
    (hAd : IsUniqueInvolution A d) (hBd : IsUniqueInvolution B d) (hne : A ≠ B)
    {t u v : G} (ht2 : t * t = 1) (hu : u ∈ A) (hv : v ∈ B) (htuv : t = u * v) :
    (∀ y ∈ A, t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ ∈ oddCoreOf A) ∧
      ∀ y ∈ A, ⁅u * u, y⁆ ∈ oddCoreOf A := by
  obtain ⟨hBA, hAB, hcomm⟩ := twin_facts_general hq hp2 h₀ hA hB hAd hBd hne
  have hOA : ∀ x ∈ A, ∀ w ∈ oddCoreOf A, x * w * x⁻¹ ∈ oddCoreOf A := fun x hx w hw =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) hw
  have hact : ∀ y ∈ A, t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ ∈ oddCoreOf A := by
    intro y hy
    have h1 : ⁅y, v⁆ ∈ oddCoreOf A := (hcomm (Subgroup.commutator_mem_commutator hy hv)).1
    have h2 : ⁅v, y⁆ ∈ oddCoreOf A := by
      rw [← commutatorElement_inv]
      exact (oddCoreOf A).inv_mem h1
    have h3 := hOA u hu _ h2
    have e : t * y * t⁻¹ * (u * y * u⁻¹)⁻¹ = u * ⁅v, y⁆ * u⁻¹ := by
      rw [htuv, commutatorElement_def]
      group
    rw [e]
    exact h3
  refine ⟨hact, fun y hy => ?_⟩
  have htN : t ∈ Subgroup.normalizer (A : Set G) := by
    rw [htuv]
    exact (Subgroup.normalizer (A : Set G)).mul_mem (Subgroup.le_normalizer hu) (hBA hv)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hy' : t * y * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htN y).mp hy
  set y' : G := t * y * t⁻¹ with hy'def
  set o₁ : G := y' * (u * y * u⁻¹)⁻¹ with ho₁
  set o₂ : G := y * (u * y' * u⁻¹)⁻¹ with ho₂
  have hο₁ : o₁ ∈ oddCoreOf A := hact y hy
  have hο₂ : o₂ ∈ oddCoreOf A := by
    have := hact y' hy'
    have e : t * y' * t⁻¹ = y := by
      rw [hy'def, hti]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [ht2]; group
    rwa [e] at this
  have hy1 : y' = o₁ * (u * y * u⁻¹) := by rw [ho₁]; group
  have hy2 : y = o₂ * (u * y' * u⁻¹) := by rw [ho₂]; group
  set P : G := o₂ * (u * o₁ * u⁻¹) with hP
  have hPO : P ∈ oddCoreOf A := (oddCoreOf A).mul_mem hο₂ (hOA u hu _ hο₁)
  have hyP : y = P * ((u * u) * y * (u * u)⁻¹) := by
    calc y = o₂ * (u * y' * u⁻¹) := hy2
      _ = o₂ * (u * (o₁ * (u * y * u⁻¹)) * u⁻¹) := by rw [← hy1]
      _ = P * ((u * u) * y * (u * u)⁻¹) := by rw [hP]; group
  have e : ⁅u * u, y⁆ = P⁻¹ := by
    have h1 : (u * u) * y * (u * u)⁻¹ = P⁻¹ * y := by
      have := congrArg (fun x => P⁻¹ * x) hyP
      simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact this.symm
    rw [commutatorElement_def, h1]
    group
  rw [e]
  exact (oddCoreOf A).inv_mem hPO


theorem mem_oddCoreOf_or_mul_mem (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {d : G}
    (hK : IsClassicalMember p f K d) {g : G} (hgK : g ∈ K)
    (hg : ∀ y ∈ K, ⁅g, y⁆ ∈ oddCoreOf K) : g ∈ oddCoreOf K ∨ d * g ∈ oddCoreOf K := by
  classical
  obtain ⟨e⟩ := hK.nonempty_equiv
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hK
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp2 hq
  have hF2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ hodd
  have hdK : d ∈ K := hKz.mem
  have hcen := (comm_mem_oddCoreOf_iff_central e hgK).mp hg
  rw [mem_center_sl2_iff] at hcen
  have hφd1 : chartMap e ⟨d, hdK⟩ ≠ 1 := by
    intro h
    have hmem : d ∈ oddCoreOf K := (mem_oddCoreOf_iff_chart e).mpr ⟨hdK, h⟩
    exact hKz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
      (isPGroup_zpowers_of_mul_self_eq_one hKz.sq hKz.ne_one))
  have hφd : chartMap e ⟨d, hdK⟩ = -1 := by
    have hinv : (chartMap e ⟨d, hdK⟩)⁻¹ = chartMap e ⟨d, hdK⟩ := by
      rw [← map_inv]
      congr 1
      exact inv_eq_of_mul_eq_one_right (Subtype.ext hKz.sq)
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self _ hF2 _ hinv with
      h | h
    · exact absurd h hφd1
    · exact h
  rcases hcen with h | h
  · left
    exact (mem_oddCoreOf_iff_chart e).mpr ⟨hgK, h⟩
  · right
    refine (mem_oddCoreOf_iff_chart e).mpr ⟨K.mul_mem hdK hgK, ?_⟩
    have e1 : (⟨d * g, K.mul_mem hdK hgK⟩ : ↥K) = ⟨d, hdK⟩ * ⟨g, hgK⟩ := rfl
    rw [e1, map_mul, hφd, h]
    apply Subtype.ext
    simp

theorem eq_one_of_sq_eq_one_of_mem_odd {N : Subgroup G} (hodd : Odd (Nat.card N)) {x : G}
    (hx : x ∈ N) (hx2 : x * x = 1) : x = 1 := by
  have : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_sq_sq (by rw [hx2, one_mul])
  exact eq_one_of_isPGroup_of_mem_odd hodd hx this


theorem false_of_mem_twin_product (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K₀ : Subgroup G} {z₀ : G}
    (h₀ : IsClassicalMember p f K₀ z₀) {I₁ I₂ J : Subgroup G} {d t : G}
    (hI₁ : I₁ ∈ CoreAssembly.conjClass K₀) (hI₂ : I₂ ∈ CoreAssembly.conjClass K₀)
    (hJ : J ∈ CoreAssembly.conjClass K₀) (hI₁d : IsUniqueInvolution I₁ d)
    (hI₂d : IsUniqueInvolution I₂ d) (hne : I₁ ≠ I₂) (hJt : IsUniqueInvolution J t)
    (hdt : d * t = t * d) (htd : t ≠ d) (hdJ : d ∈ Subgroup.normalizer (J : Set G))
    (hdtriv : ∀ y ∈ J, ⁅d, y⁆ ∈ oddCoreOf J) (htM : t ∈ I₁ ⊔ I₂) : False := by
  classical
  have ht2 : t * t = 1 := hJt.sq
  have hd2 : d * d = 1 := hI₁d.sq
  obtain ⟨h21, h12, hcomm⟩ := twin_facts_general hq hp2 h₀ hI₁ hI₂ hI₁d hI₂d hne
  have hset : ((I₁ ⊔ I₂ : Subgroup G) : Set G) = (I₁ : Set G) * (I₂ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left I₁ I₂ h21
  have htM' : t ∈ (I₁ : Set G) * (I₂ : Set G) := by
    rw [← hset]
    exact htM
  obtain ⟨u₁, hu₁, u₂, hu₂, htu⟩ := htM'
  have hI₁m : IsClassicalMember p f I₁ d := isClassicalMember_of_mem_conjClass hp2 hq h₀ hI₁ hI₁d
  have hI₂m : IsClassicalMember p f I₂ d := isClassicalMember_of_mem_conjClass hp2 hq h₀ hI₂ hI₂d
  obtain ⟨hact₁, hg2₁⟩ := twin_product_action hp2 hq h₀ hI₁ hI₂ hI₁d hI₂d hne ht2 hu₁ hu₂ htu.symm
  have hc₁ : ∀ y ∈ I₁, ⁅u₁, y⁆ ∈ oddCoreOf I₁ := by
    by_contra hcon
    exact inner_action_false hp2 hq h₀ hI₁ hJ hI₁d hJt hdt hdJ hdtriv hu₁ hact₁ hg2₁ hcon
  have hw : u₁ * u₂ * u₁⁻¹ ∈ I₂ := by
    have := (Subgroup.mem_normalizer_iff.mp (h12 hu₁) u₂).mp hu₂
    exact this
  obtain ⟨hact₂, hg2₂⟩ := twin_product_action hp2 hq h₀ hI₂ hI₁ hI₂d hI₁d (Ne.symm hne) ht2 hw hu₁
    (by rw [← htu]; group)
  have hc₂ : ∀ y ∈ I₂, ⁅u₁ * u₂ * u₁⁻¹, y⁆ ∈ oddCoreOf I₂ := by
    by_contra hcon
    exact inner_action_false hp2 hq h₀ hI₂ hJ hI₂d hJt hdt hdJ hdtriv hw hact₂ hg2₂ hcon
  have hOM : ∀ m ∈ I₁ ⊔ I₂, m ∈ Subgroup.normalizer (oddCoreOf I₁ : Set G) ∧
      m ∈ Subgroup.normalizer (oddCoreOf I₂ : Set G) := by
    intro m hm
    have hmN1 : m ∈ Subgroup.normalizer (I₁ : Set G) := (sup_le Subgroup.le_normalizer h21) hm
    have hmN2 : m ∈ Subgroup.normalizer (I₂ : Set G) := (sup_le h12 Subgroup.le_normalizer) hm
    exact ⟨mem_normalizer_oddCoreOf_of_mem_normalizer' hmN1,
      mem_normalizer_oddCoreOf_of_mem_normalizer' hmN2⟩
  have hO₁ : oddCoreOf I₁ ≤ oddCoreOf (I₁ ⊔ I₂) :=
    le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self I₁).trans le_sup_left)
      (fun m hm => (hOM m hm).1) (oddCoreOf_odd_natCard I₁)
  have hO₂ : oddCoreOf I₂ ≤ oddCoreOf (I₁ ⊔ I₂) :=
    le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self I₂).trans le_sup_right)
      (fun m hm => (hOM m hm).2) (oddCoreOf_odd_natCard I₂)
  set N' : Subgroup G := oddCoreOf (I₁ ⊔ I₂) with hN'
  have hN'odd : Odd (Nat.card N') := oddCoreOf_odd_natCard _
  have hdI₁ : ∀ y ∈ I₁, d * y = y * d := fun y hy => hI₁d.commute_of_mem hy
  have hdI₂ : ∀ y ∈ I₂, d * y = y * d := fun y hy => hI₂d.commute_of_mem hy
  have hdI₂' : ∀ y ∈ I₂, d * y = y * d := hdI₂
  have hdw : d * (u₁ * u₂ * u₁⁻¹) = (u₁ * u₂ * u₁⁻¹) * d := hdI₂ _ hw
  have hdu₁ : d * u₁ = u₁ * d := hdI₁ _ hu₁
  have htw : t = (u₁ * u₂ * u₁⁻¹) * u₁ := by rw [← htu]; group
  have hdtN : t ∈ N' ∨ d * t ∈ N' := by
    rcases mem_oddCoreOf_or_mul_mem hp2 hq hI₁m hu₁ hc₁ with h₁ | h₁ <;>
    rcases mem_oddCoreOf_or_mul_mem hp2 hq hI₂m hw hc₂ with h₂ | h₂
    · left
      rw [htw]
      exact N'.mul_mem (hO₂ h₂) (hO₁ h₁)
    · right
      have : d * t = (d * (u₁ * u₂ * u₁⁻¹)) * u₁ := by rw [htw]; group
      rw [this]
      exact N'.mul_mem (hO₂ h₂) (hO₁ h₁)
    · right
      have : d * t = (u₁ * u₂ * u₁⁻¹) * (d * u₁) := by
        rw [htw]
        calc d * ((u₁ * u₂ * u₁⁻¹) * u₁) = (d * (u₁ * u₂ * u₁⁻¹)) * u₁ := by group
          _ = ((u₁ * u₂ * u₁⁻¹) * d) * u₁ := by rw [hdw]
          _ = (u₁ * u₂ * u₁⁻¹) * (d * u₁) := by group
      rw [this]
      exact N'.mul_mem (hO₂ h₂) (hO₁ h₁)
    · left
      have : t = (d * (u₁ * u₂ * u₁⁻¹)) * (d * u₁) := by
        calc t = (u₁ * u₂ * u₁⁻¹) * u₁ := htw
          _ = (d * d) * (u₁ * u₂ * u₁⁻¹) * u₁ := by rw [hd2, one_mul]
          _ = d * ((d * (u₁ * u₂ * u₁⁻¹))) * u₁ := by group
          _ = d * ((u₁ * u₂ * u₁⁻¹) * d) * u₁ := by rw [hdw]
          _ = (d * (u₁ * u₂ * u₁⁻¹)) * (d * u₁) := by group
      rw [this]
      exact N'.mul_mem (hO₂ h₂) (hO₁ h₁)
  rcases hdtN with h | h
  · exact hJt.ne_one (eq_one_of_sq_eq_one_of_mem_odd hN'odd h ht2)
  · have hdt2 : (d * t) * (d * t) = 1 := by
      calc (d * t) * (d * t) = d * (t * d) * t := by group
        _ = d * (d * t) * t := by rw [← hdt]
        _ = (d * d) * (t * t) := by group
        _ = 1 := by rw [hd2, ht2, one_mul]
    have h1 := eq_one_of_sq_eq_one_of_mem_odd hN'odd h hdt2
    apply htd
    have : t = d⁻¹ := by
      have := congrArg (fun x => d⁻¹ * x) h1
      simpa [mul_assoc] using this
    rw [this]
    exact inv_eq_of_mul_eq_one_right hd2


end Members

end CFSG.ClassicalInvolution.Asc77.AscFusion

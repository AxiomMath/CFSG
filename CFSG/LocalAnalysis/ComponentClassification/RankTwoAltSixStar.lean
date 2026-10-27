module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixA7
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixRelabel

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

namespace Six

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 6)} {ψB : B ≃* alternatingGroup (Fin 6)}

theorem star_quot6
    [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G)) :
    (⟨(c1 ψA * cr ψB) ^ 2, pow_mem (mul_mem c1_mem_H (B_le_H hco cr_mem)) 2⟩ : H ψA) ∈
        pPrimeCore 2 (H ψA) ∨
      (⟨(c1 ψA * (cr ψB)⁻¹) ^ 2,
        pow_mem (mul_mem c1_mem_H (inv_mem (B_le_H hco cr_mem))) 2⟩ : H ψA) ∈
        pPrimeCore 2 (H ψA) := by
  obtain ⟨θ, hθ⟩ := exists_label hco hN ht1A
  have hr := B_le_H hco (cr_mem (ψB := ψB))
  set cb := ((⟨c1 ψA, c1_mem_H⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) with hcb
  set rb := ((⟨cr ψB, hr⟩ : H ψA) : H ψA ⧸ pPrimeCore 2 (H ψA)) with hrb
  have hc1 := c1_not_mem_core hco hN ht1A
  have hcb1 : cb ≠ 1 := fun h => hc1 ((QuotientGroup.eq_one_iff _).mp h)
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← QuotientGroup.mk_pow, show (⟨c1 ψA, c1_mem_H⟩ : H ψA) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact c1_pow_three), QuotientGroup.mk_one]
  have hrbθ : ((θ rb : alternatingGroup (Fin 7)) : Perm (Fin 7)) = t450 := by
    rw [← ι67_e450, ← hθ e450]
    rfl
  set X := ((θ cb : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hX
  have hcomm : ∀ σ ∈ rootAlt 6, X * ((ι67 σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((ι67 σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * X := by
    intro σ hσ
    have h1 := congrArg (fun q => ((θ q : alternatingGroup (Fin 7)) : Perm (Fin 7)))
      (commute_c1bar hco hσ)
    simp only [map_mul, Subgroup.coe_mul, hθ] at h1
    exact h1
  have h012 := hcomm _ a6c012_mem_rootAlt
  have h013 := hcomm _ a6c013_mem_rootAlt
  rw [ι67_a6c012] at h012
  rw [ι67_a6c013] at h013
  have hfix := fix_of_commute_t012_t013 h012 h013
  have hX3 : X ^ 3 = 1 := by
    rw [hX, ← Subgroup.coe_pow, ← map_pow, hcb3, map_one, Subgroup.coe_one]
  have hX1 : X ≠ 1 := fun h => hcb1 (θ.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hθinj : ∀ q, ((θ q : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1 → q = 1 := fun q h =>
    θ.injective (Subtype.ext (by rw [map_one]; exact h))
  rcases eq_t456_of_fix hfix hX3 hX1 with h | h
  · left
    rw [← QuotientGroup.eq_one_iff]
    have e : (⟨(c1 ψA * cr ψB) ^ 2, pow_mem (mul_mem c1_mem_H hr) 2⟩ : H ψA) =
        ((⟨c1 ψA, c1_mem_H⟩ : H ψA) * ⟨cr ψB, hr⟩) ^ 2 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul])
    rw [e, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
    apply hθinj
    rw [map_pow, map_mul, Subgroup.coe_pow, Subgroup.coe_mul, ← hX, h, hrbθ]
    exact t456_t450_sq
  · right
    rw [← QuotientGroup.eq_one_iff]
    have e : (⟨(c1 ψA * (cr ψB)⁻¹) ^ 2, pow_mem (mul_mem c1_mem_H (inv_mem hr)) 2⟩ : H ψA) =
        ((⟨c1 ψA, c1_mem_H⟩ : H ψA) * (⟨cr ψB, hr⟩ : H ψA)⁻¹) ^ 2 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv])
    rw [e, QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    apply hθinj
    rw [map_pow, map_mul, map_inv, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, ← hX, h,
      hrbθ]
    exact t456_t450_inv_sq

theorem y0_conj_of_mem_centralizer {k : G} (hk : k ∈ centralizer (B : Set G)) :
    y0 ψB * k * (y0 ψB)⁻¹ = k := by
  rw [(mem_centralizer_iff.mp hk) _ (y0_mem (ψB := ψB)), mul_inv_cancel_right]

theorem lift_star [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G)))
    {d : G} (hd : d ∈ H ψA) (hyd : y0 ψB * d * (y0 ψB)⁻¹ = d⁻¹)
    (hO : (⟨(c1 ψA * d) ^ 2, pow_mem (mul_mem c1_mem_H hd) 2⟩ : H ψA) ∈ pPrimeCore 2 (H ψA)) :
    (c1 ψA * d) ^ 2 = 1 := by
  obtain ⟨k, hk, a, b, hkab⟩ := core_le hco hN ht1A ⟨_, hO, rfl⟩
  have hu : (c1 ψA * d) ^ 2 = k * w ψA ^ a * c1 ψA ^ b := hkab
  have hkA := (mem_inf.mp hk).1
  have hkB := (mem_inf.mp hk).2
  have hkw : Commute k (w ψA) := ((mem_centralizer_iff.mp hkA) _ (w_mem (ψA := ψA))).symm
  have hkc : Commute k (c1 ψA) := ((mem_centralizer_iff.mp hkA) _ (c1_mem (ψA := ψA))).symm
  have hwc : Commute (w ψA) (c1 ψA) := w_comm_c1
  have hcu : Commute (c1 ψA) ((c1 ψA * d) ^ 2) := by
    rw [hu]
    exact (hkc.symm.mul_right (hwc.symm.zpow_right a)).mul_right ((Commute.refl _).zpow_right b)
  have h1 : y0 ψB * (c1 ψA * d) ^ 2 * (y0 ψB)⁻¹ = ((c1 ψA * d) ^ 2)⁻¹ := by
    have e1 : y0 ψB * (c1 ψA * d) ^ 2 * (y0 ψB)⁻¹ = ((c1 ψA)⁻¹ * d⁻¹) ^ 2 := by
      rw [← y0_conj_c1 hco, ← hyd]
      simp only [sq]
      group
    have e2 : ((c1 ψA)⁻¹ * d⁻¹) ^ 2 = (c1 ψA)⁻¹ * ((c1 ψA * d) ^ 2)⁻¹ * c1 ψA := by
      simp only [sq]
      group
    rw [e1, e2, mul_assoc, (hcu.inv_right.symm).eq, inv_mul_cancel_left]
  have h2 : y0 ψB * (c1 ψA * d) ^ 2 * (y0 ψB)⁻¹ = k * w ψA ^ a * c1 ψA ^ (-b) := by
    have e : ∀ x y : G, y0 ψB * (x * y) * (y0 ψB)⁻¹ =
        (y0 ψB * x * (y0 ψB)⁻¹) * (y0 ψB * y * (y0 ψB)⁻¹) := fun x y => by group
    rw [hu, e, e, y0_conj_of_mem_centralizer hkB, ← conj_zpow, ← conj_zpow,
      y0_conj_of_mem_centralizer (w_mem_centralizer_B hco), y0_conj_c1 hco, inv_zpow, zpow_neg]
  have h3 : k * w ψA ^ a * c1 ψA ^ (-b) = k⁻¹ * w ψA ^ (-a) * c1 ψA ^ (-b) := by
    rw [← h2, h1, hu, mul_inv_rev, mul_inv_rev, ← zpow_neg, ← zpow_neg]
    have c1' : Commute (c1 ψA ^ (-b)) (w ψA ^ (-a)) := (hwc.zpow_zpow (-a) (-b)).symm
    have c2' : Commute (c1 ψA ^ (-b)) k⁻¹ := (hkc.zpow_right (-b)).inv_left.symm
    have c3' : Commute (w ψA ^ (-a)) k⁻¹ := (hkw.zpow_right (-a)).inv_left.symm
    calc c1 ψA ^ (-b) * (w ψA ^ (-a) * k⁻¹) = w ψA ^ (-a) * k⁻¹ * c1 ψA ^ (-b) := by
          rw [← mul_assoc, c1'.eq, mul_assoc, c2'.eq, ← mul_assoc]
      _ = k⁻¹ * w ψA ^ (-a) * c1 ψA ^ (-b) := by rw [c3'.eq]
  have h4 : k * w ψA ^ a = k⁻¹ * w ψA ^ (-a) := mul_right_cancel h3
  have hkk : k * k = w ψA ^ (-a) * w ψA ^ (-a) := by
    calc k * k = k * (k * w ψA ^ a) * (w ψA ^ a)⁻¹ := by group
      _ = k * (k⁻¹ * w ψA ^ (-a)) * (w ψA ^ a)⁻¹ := by rw [h4]
      _ = w ψA ^ (-a) * w ψA ^ (-a) := by rw [zpow_neg]; group
  have hk2 : k * k = 1 := eq_one_of_mem_centralizer_six ψA
    (hkk ▸ mul_mem (zpow_mem w_mem _) (zpow_mem w_mem _)) (mul_mem hkA hkA)
  have hk1 : k = 1 := by
    have hd2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hk2)
    have hko : Odd (orderOf k) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hk)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hko
      exact absurd hko (by decide)
  have hwa : w ψA ^ a = 1 := by
    rw [hk1, one_mul, inv_one, one_mul, zpow_neg] at h4
    have h5 : w ψA ^ a * w ψA ^ a = 1 := by
      calc w ψA ^ a * w ψA ^ a = w ψA ^ a * (w ψA ^ a)⁻¹ := by rw [← h4]
        _ = 1 := mul_inv_cancel _
    have h6 : (w ψA ^ a) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, w_pow_three, one_zpow]
    calc w ψA ^ a = (w ψA ^ a) ^ 3 * (w ψA ^ a * w ψA ^ a)⁻¹ := by group
      _ = 1 := by rw [h6, h5]; group
  have hub : (c1 ψA * d) ^ 2 = c1 ψA ^ b := by rw [hu, hk1, hwa, one_mul, one_mul]
  by_contra hne
  apply c1_not_mem_core hco hN ht1A
  have hb3 : b % 3 ≠ 0 := fun h => hne (by
    rw [hub, zpow_eq_zpow_emod' b c1_pow_three, show b % ((3 : ℕ) : ℤ) = 0 from h, zpow_zero])
  have hbb : c1 ψA ^ (b * b) = c1 ψA := by
    rw [zpow_eq_zpow_emod' _ c1_pow_three]
    have : b * b % ((3 : ℕ) : ℤ) = 1 := by
      rw [Int.mul_emod]
      rcases (by omega : b % 3 = 1 ∨ b % 3 = 2) with h | h <;> push_cast <;> rw [h] <;> norm_num
    rw [this, zpow_one]
  have hcb : (⟨c1 ψA ^ b, zpow_mem c1_mem_H b⟩ : H ψA) ∈ pPrimeCore 2 (H ψA) := by
    have e : (⟨c1 ψA ^ b, zpow_mem c1_mem_H b⟩ : H ψA) =
        ⟨(c1 ψA * d) ^ 2, pow_mem (mul_mem c1_mem_H hd) 2⟩ := Subtype.ext hub.symm
    rw [e]
    exact hO
  have e2 : (⟨c1 ψA, c1_mem_H⟩ : H ψA) = (⟨c1 ψA ^ b, zpow_mem c1_mem_H b⟩ : H ψA) ^ b :=
    Subtype.ext (by rw [Subgroup.coe_zpow, ← zpow_mul, hbb])
  rw [e2]
  exact zpow_mem hcb b

theorem star_six
    [Finite G] (hco : AltCoords 6 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1A : ∀ t ∈ centralizer (A : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    (c1 ψA * cr ψB) ^ 2 = 1 ∨ (c1 ψA * (cr ψB)⁻¹) ^ 2 = 1 := by
  have hr := B_le_H hco (cr_mem (ψB := ψB))
  rcases star_quot6 hco hN ht1A with h | h
  · exact Or.inl (lift_star hco hN ht1A hodd hr y0_conj_cr h)
  · refine Or.inr (lift_star hco hN ht1A hodd (inv_mem hr) ?_ h)
    rw [show y0 ψB * (cr ψB)⁻¹ * (y0 ψB)⁻¹ = (y0 ψB * cr ψB * (y0 ψB)⁻¹)⁻¹ by group,
      y0_conj_cr]

end Six

theorem AltPair.star_six
    {G : Type} [Group G] [Finite G] {A B : Subgroup G} (hp : AltPair 6 A B) :
    ∃ (ψA : A ≃* alternatingGroup (Fin 6)) (ψB : B ≃* alternatingGroup (Fin 6)),
      AltCoords 6 A B ψA ψB ∧ ((ψA.symm e450 : G) * (ψB.symm e450 : G)) ^ 2 = 1 := by
  obtain ⟨ψA, ψB, hco⟩ := hp.exists_altCoords
  rcases Six.star_six hco hp.normalizer_le hp.centralizer_le_A hp.odd_inf with h | h
  · exact ⟨ψA, ψB, hco, h⟩
  · refine ⟨ψA, ψB.trans (conjPerm 6 (swap 4 5)), altCoords_relabel45 hco, ?_⟩
    have e : (conjPerm 6 (swap 4 5)).symm e450 = e450⁻¹ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by rw [conjPerm_apply]; decide)
    have e2 : ((ψB.trans (conjPerm 6 (swap 4 5))).symm e450 : G) = (Six.cr ψB)⁻¹ := by
      rw [MulEquiv.symm_trans_apply, e, map_inv]
      rfl
    rw [e2]
    exact h

end CFSG.ComponentClassification.RankTwoAlt

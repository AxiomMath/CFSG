module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerC
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

theorem commutator_mul_central {G : Type*} [Group G] {z z' e e' : G} (h1 : Commute z e)
    (h2 : Commute z e') (h3 : Commute z' e) (h4 : Commute z' e') (h5 : Commute z z') :
    ⁅z * e, z' * e'⁆ = ⁅e, e'⁆ := by
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
  have a1 : e * z' = z' * e := h3.eq.symm
  have a2 : e⁻¹ * z⁻¹ = z⁻¹ * e⁻¹ := (Commute.inv_inv h1).eq.symm
  have a3 : e' * z⁻¹ = z⁻¹ * e' := (Commute.inv_left h2).eq.symm
  have a4 : e⁻¹ * z'⁻¹ = z'⁻¹ * e⁻¹ := (Commute.inv_inv h3).eq.symm
  have a5 : e' * z'⁻¹ = z'⁻¹ * e' := (Commute.inv_left h4).eq.symm
  have a6 : e'⁻¹ * z'⁻¹ = z'⁻¹ * e'⁻¹ := (Commute.inv_inv h4).eq.symm
  have a7 : z * z' * z⁻¹ * z'⁻¹ = 1 := by rw [h5.eq]; group
  calc z * e * (z' * e') * (e⁻¹ * z⁻¹) * (e'⁻¹ * z'⁻¹)
      = z * (e * z') * e' * (e⁻¹ * z⁻¹) * (e'⁻¹ * z'⁻¹) := by group
    _ = z * (z' * e) * e' * (z⁻¹ * e⁻¹) * (z'⁻¹ * e'⁻¹) := by rw [a1, a2, a6]
    _ = z * z' * e * (e' * z⁻¹) * e⁻¹ * z'⁻¹ * e'⁻¹ := by group
    _ = z * z' * e * (z⁻¹ * e') * e⁻¹ * z'⁻¹ * e'⁻¹ := by rw [a3]
    _ = z * z' * (e * z⁻¹) * e' * (e⁻¹ * z'⁻¹) * e'⁻¹ := by group
    _ = z * z' * (z⁻¹ * e) * e' * (z'⁻¹ * e⁻¹) * e'⁻¹ := by
        rw [a4, show e * z⁻¹ = z⁻¹ * e from (Commute.inv_left h1).eq.symm]
    _ = z * z' * z⁻¹ * e * (e' * z'⁻¹) * e⁻¹ * e'⁻¹ := by group
    _ = z * z' * z⁻¹ * e * (z'⁻¹ * e') * e⁻¹ * e'⁻¹ := by rw [a5]
    _ = z * z' * z⁻¹ * (e * z'⁻¹) * e' * e⁻¹ * e'⁻¹ := by group
    _ = z * z' * z⁻¹ * (z'⁻¹ * e) * e' * e⁻¹ * e'⁻¹ := by
        rw [show e * z'⁻¹ = z'⁻¹ * e from (Commute.inv_left h3).eq.symm]
    _ = (z * z' * z⁻¹ * z'⁻¹) * (e * e' * e⁻¹ * e'⁻¹) := by group
    _ = e * e' * e⁻¹ * e'⁻¹ := by rw [a7, one_mul]

variable {K : Type} [Field K]

theorem E1_sup_E2 (h2 : (2 : K) ≠ 0) : E1 K ⊔ E2 K = X0 K := by
  refine le_antisymm (sup_le (E1_le_X0 h2) (E2_le_X0 h2)) fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_X0 h2 hx
  exact mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem eq_one_or_u1_of_central_E1 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ E1 K) (hc : ∀ y ∈ E1 K, x * y = y * x) : x = 1 ∨ x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  have hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro h
    apply injective_E1 h2
    have := hc (proj 2 K (blkSL K (h, 1))) (mem_E1.mpr ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one] at this
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
    exact this.symm
  rcases eq_one_or_neg_of_mem_center hg with h | h
  · left
    have : g = 1 := Subtype.ext h
    rw [this, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K), (1 : Matrix.SpecialLinearGroup
      (Fin 2) K)) = 1 from rfl, map_one, map_one]
  · right
    have : g = negOneSL := Subtype.ext h
    rw [this, u1_eq_proj_blkSL']

theorem eq_one_or_u1_of_central_E2 (h2 : (2 : K) ≠ 0) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ E2 K) (hc : ∀ y ∈ E2 K, x * y = y * x) : x = 1 ∨ x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E2.mp hx
  have hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [mem_center_iff]
    intro h
    apply injective_E2 h2
    have := hc (proj 2 K (blkSL K (1, h))) (mem_E2.mpr ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one] at this
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
    exact this.symm
  rcases eq_one_or_neg_of_mem_center hg with h | h
  · left
    have : g = 1 := Subtype.ext h
    rw [this, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K), (1 : Matrix.SpecialLinearGroup
      (Fin 2) K)) = 1 from rfl, map_one, map_one]
  · right
    have : g = negOneSL := Subtype.ext h
    rw [this, u1_eq_proj_blkSL]

theorem u1_comm_of_mem_X0 {x : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K) :
    u1 K * x = x * u1 K := by
  have := mem_centralizer_singleton_iff.mp (X0_le_centralizer hx)
  exact this.symm

variable [Finite K]

theorem inf_central_of_oddByTwo (h2 : (2 : K) ≠ 0) {Q R R₁ : Subgroup (StatedProj (StatedSp 2 K))}
    (hQ : CFSG.IsQuasisimple Q) (hQX : Q ≤ X0 K)
    (hQc : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = u1 K) (hu1Q : u1 K ∈ Q)
    (hRn : ∀ x ∈ X0 K, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hR₁R : R₁ ≤ R)
    (hR₁n : (R₁.subgroupOf R).Normal) (hR₁o : Odd (Nat.card R₁))
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁) :
    ∀ x ∈ R ⊓ Q, x = 1 ∨ x = u1 K := by
  have hN : ((R ⊓ Q).subgroupOf Q).Normal := by
    refine ⟨fun x hx q => ?_⟩
    have hxR : (x : StatedProj (StatedSp 2 K)) ∈ R := (Subgroup.mem_inf.mp hx).1
    have hxQ : (x : StatedProj (StatedSp 2 K)) ∈ Q := (Subgroup.mem_inf.mp hx).2
    exact Subgroup.mem_inf.mpr ⟨hRn _ (hQX q.2) _ hxR,
      Q.mul_mem (Q.mul_mem q.2 hxQ) (Q.inv_mem q.2)⟩
  rcases quasisimple_normal_subgroups hQ hN with ht | hc
  · exfalso
    have hQR : Q ≤ R := fun q hq => by
      have : (⟨q, hq⟩ : Q) ∈ (R ⊓ Q).subgroupOf Q := ht ▸ mem_top _
      exact this.1
    have hN₁ : ((R₁ ⊓ Q).subgroupOf Q).Normal := by
      refine ⟨fun x hx q => ?_⟩
      have hxR : (x : StatedProj (StatedSp 2 K)) ∈ R₁ := (Subgroup.mem_inf.mp hx).1
      have hxQ : (x : StatedProj (StatedSp 2 K)) ∈ Q := (Subgroup.mem_inf.mp hx).2
      refine Subgroup.mem_inf.mpr ⟨?_, Q.mul_mem (Q.mul_mem q.2 hxQ) (Q.inv_mem q.2)⟩
      have := hR₁n.conj_mem ⟨x, hR₁R hxR⟩ hxR ⟨q, hQR q.2⟩
      exact this
    rcases quasisimple_normal_subgroups hQ hN₁ with ht₁ | hc₁
    ·
      have hu : u1 K ∈ R₁ := by
        have : (⟨u1 K, hu1Q⟩ : Q) ∈ (R₁ ⊓ Q).subgroupOf Q := ht₁ ▸ mem_top _
        exact this.1
      have hdvd := orderOf_dvd_natCard (⟨u1 K, hu⟩ : R₁)
      rw [Subgroup.orderOf_mk, orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1)
        (u1_ne_one h2)] at hdvd
      exact (Nat.not_even_iff_odd.mpr hR₁o) (even_iff_two_dvd.mpr hdvd)
    · have hR₁Q : ∀ x ∈ R₁ ⊓ Q, x = 1 := by
        intro x hx
        have hxc : (⟨x, hx.2⟩ : Q) ∈ center Q := hc₁ hx
        rcases hQc x hx.2 (fun y hy => congrArg Subtype.val
          ((mem_center_iff.mp hxc ⟨y, hy⟩).symm)) with h | h
        · exact h
        · exfalso
          have hu : u1 K ∈ R₁ := h ▸ hx.1
          have hdvd := orderOf_dvd_natCard (⟨u1 K, hu⟩ : R₁)
          rw [Subgroup.orderOf_mk, orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1)
            (u1_ne_one h2)] at hdvd
          exact (Nat.not_even_iff_odd.mpr hR₁o) (even_iff_two_dvd.mpr hdvd)
      have hp : IsPGroup 2 Q := by
        rintro ⟨q, hq⟩
        obtain ⟨k, hk⟩ := hR2 q (hQR hq)
        refine ⟨k, Subtype.ext ?_⟩
        exact hR₁Q _ ⟨hk, pow_mem hq _⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent Q := hp.isNilpotent
      have : Group.IsSolvable Q := inferInstance
      have : Group.IsPerfect Q := hQ.1
      have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
      exact Group.IsPerfect.not_isSolvable Q ‹_›
  · intro x hx
    have hxc : (⟨x, hx.2⟩ : Q) ∈ center Q := hc hx
    exact hQc x hx.2 fun y hy => congrArg Subtype.val ((mem_center_iff.mp hxc ⟨y, hy⟩).symm)

omit [Finite K] in
theorem commute_of_inf_central {Q R : Subgroup (StatedProj (StatedSp 2 K))}
    (hQ : CFSG.IsQuasisimple Q) (hQX : Q ≤ X0 K) (hRX : R ≤ X0 K)
    (hQn : ∀ x ∈ X0 K, ∀ e ∈ Q, x * e * x⁻¹ ∈ Q) (hRn : ∀ x ∈ X0 K, ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hRQ : ∀ x ∈ R ⊓ Q, x = 1 ∨ x = u1 K) {r : StatedProj (StatedSp 2 K)} (hr : r ∈ R) :
    ∀ q ∈ Q, r * q = q * r := by
  have hc : ∀ e ∈ Q, ∃ z, (z = 1 ∨ z = u1 K) ∧ r * e * r⁻¹ = z * e := by
    intro e he
    refine ⟨r * e * r⁻¹ * e⁻¹, hRQ _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩), by group⟩
    · have := hRn e (hQX he) r⁻¹ (R.inv_mem hr)
      have h' : r * (e * r⁻¹ * e⁻¹) ∈ R := R.mul_mem hr (by simpa using this)
      simpa [mul_assoc] using h'
    · exact Q.mul_mem (hQn r (hRX hr) e he) (Q.inv_mem he)
  have hz : ∀ z, (z = 1 ∨ z = u1 K) → ∀ x ∈ X0 K, z * x = x * z := by
    rintro z (rfl | rfl) x hx
    · rw [one_mul, mul_one]
    · exact u1_comm_of_mem_X0 hx
  have hcomm : ⁅Q, Q⁆ ≤ centralizer ({r} : Set (StatedProj (StatedSp 2 K))) := by
    rw [commutator_le]
    intro e he e' he'
    rw [mem_centralizer_singleton_iff]
    obtain ⟨z, hz1, hze⟩ := hc e he
    obtain ⟨z', hz1', hze'⟩ := hc e' he'
    have h1 : r * ⁅e, e'⁆ * r⁻¹ = ⁅e, e'⁆ := by
      have hconj : r * ⁅e, e'⁆ * r⁻¹ = ⁅r * e * r⁻¹, r * e' * r⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [hconj, hze, hze']
      have he0 := hQX he
      have he0' := hQX he'
      have hzz' : Commute z z' := by
        rcases hz1 with rfl | rfl <;> rcases hz1' with rfl | rfl
        · exact Commute.one_left _
        · exact Commute.one_left _
        · exact Commute.one_right _
        · exact Commute.refl _
      exact commutator_mul_central (hz z hz1 e he0) (hz z hz1 e' he0') (hz z' hz1' e he0)
        (hz z' hz1' e' he0') hzz'
    calc ⁅e, e'⁆ * r = r * ⁅e, e'⁆ * r⁻¹ * r := by rw [h1]
      _ = r * ⁅e, e'⁆ := by group
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.mp hQ.1
  intro q hq
  have := hcomm (hperf.symm ▸ hq)
  exact (mem_centralizer_singleton_iff.mp this).symm

theorem relIndex_gt_of_u1 (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    {R R₁ : Subgroup (StatedProj (StatedSp 2 K))} (hRX : R ≤ X0 K)
    (hRn : (R.subgroupOf (X0 K)).Normal) (hR₁R : R₁ ≤ R) (hR₁n : (R₁.subgroupOf R).Normal)
    (hR₁o : Odd (Nat.card R₁)) (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ R₁) :
    Nat.card K * (Nat.card K ^ 2 - 1) / 2 < R.relIndex (X0 K) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have h4 : 4 ≤ Nat.card K := by omega
  have hRn' : ∀ x ∈ X0 K, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr => by
    have := hRn.conj_mem ⟨r, hRX hr⟩ hr ⟨x, hx⟩
    exact this
  have hQ1 := inf_central_of_oddByTwo h2 (isQuasisimple_E1 h2 h4) (E1_le_X0 h2)
    (fun x hx hc => eq_one_or_u1_of_central_E1 h2 hx hc) u1_mem_E1 hRn' hR₁R hR₁n hR₁o hR2
  have hQ2 := inf_central_of_oddByTwo h2 (isQuasisimple_E2 h2 h4) (E2_le_X0 h2)
    (fun x hx hc => eq_one_or_u1_of_central_E2 h2 hx hc) u1_mem_E2 hRn' hR₁R hR₁n hR₁o hR2
  have hR : ∀ r ∈ R, r = 1 ∨ r = u1 K := by
    intro r hr
    have hc2 := commute_of_inf_central (isQuasisimple_E2 h2 h4) (E2_le_X0 h2) hRX
      (fun x hx e he => conj_mem_E2 h2 hx he) hRn' hQ2 hr
    have hrE1 : r ∈ E1 K := mem_E1_of_commute_E2 h2 (hRX hr) hc2
    exact hQ1 r (Subgroup.mem_inf.mpr ⟨hr, hrE1⟩)
  have hRc : Nat.card R ≤ 2 := card_le_two_of_forall hR
  have hE12 : Nat.card (E1 K ⊓ E2 K : Subgroup (StatedProj (StatedSp 2 K))) ≤ 2 := by
    refine card_le_two_of_forall (u := u1 K) fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact eq_one_or_u1_of_central_E1 h2 hx1 fun y hy => (commute_E1_E2 hy hx2).symm
  set s := Nat.card K * (Nat.card K ^ 2 - 1) with hs
  have hE1c : Nat.card (E1 K) = s := by
    rw [← Nat.card_congr (E1Equiv h2).toEquiv, card_SL2]
  have hE2c : Nat.card (E2 K) = s := by
    rw [← Nat.card_congr (E2Equiv h2).toEquiv, card_SL2]
  have c1 := Subgroup.relIndex_mul_card (H := E1 K) (K := E2 K)
  have c2 := Subgroup.relIndex_mul_card (H := E1 K) (K := X0 K)
  rw [inf_of_le_left (E1_le_X0 h2), hE1c] at c2
  have c3 := Subgroup.relIndex_mul_card (H := R) (K := X0 K)
  rw [inf_of_le_left hRX] at c3
  have hne : (E1 K).relIndex (X0 K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at c2
    exact Nat.card_pos.ne' c2.symm
  have hle : (E1 K).relIndex (E2 K) ≤ (E1 K).relIndex (X0 K) :=
    Subgroup.relIndex_le_of_le_right (E2_le_X0 h2) hne
  rw [hE2c] at c1
  have hs5 : 120 ≤ s := by
    have h1 : 24 ≤ Nat.card K ^ 2 - 1 := by
      have : 25 ≤ Nat.card K ^ 2 := by nlinarith
      omega
    calc 120 = 5 * 24 := by norm_num
      _ ≤ s := Nat.mul_le_mul h5 h1
  by_contra hcon
  push Not at hcon
  have k1 : s ≤ 2 * (E1 K).relIndex (E2 K) := by
    calc s = (E1 K).relIndex (E2 K) * Nat.card (E1 K ⊓ E2 K : Subgroup _) := c1.symm
      _ ≤ (E1 K).relIndex (E2 K) * 2 := Nat.mul_le_mul_left _ hE12
      _ = 2 * (E1 K).relIndex (E2 K) := by ring
  have k2 : Nat.card (X0 K) ≤ 2 * R.relIndex (X0 K) := by
    calc Nat.card (X0 K) = R.relIndex (X0 K) * Nat.card R := c3.symm
      _ ≤ R.relIndex (X0 K) * 2 := Nat.mul_le_mul_left _ hRc
      _ = 2 * R.relIndex (X0 K) := by ring
  have k3 : (E1 K).relIndex (E2 K) * s ≤ Nat.card (X0 K) := by
    rw [← c2]
    exact Nat.mul_le_mul_right _ hle
  have k4 : 2 * (s / 2) ≤ s := Nat.mul_div_le s 2
  nlinarith

end CFSG.ComponentClassification.CatFactsSp4

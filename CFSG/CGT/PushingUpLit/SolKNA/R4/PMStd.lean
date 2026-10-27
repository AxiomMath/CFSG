module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMArith
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

section Transport

variable {G : Type} [Group G]

private theorem pmStd_conj_cancel {a b n : G} (h : n * a * n⁻¹ = n * b * n⁻¹) : a = b :=
  mul_left_cancel (mul_right_cancel h)

private theorem pmStd_mem_normalizer_conjSub (E : Subgroup G) (n z : G) :
    z ∈ Subgroup.normalizer ((conjSub n E : Subgroup G) : Set G) ↔
      n⁻¹ * z * n ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h u
    have hu := h (n * u * n⁻¹)
    rw [mem_conjSub_iff, mem_conjSub_iff] at hu
    rw [show n⁻¹ * (n * u * n⁻¹) * n = u by group,
      show n⁻¹ * (z * (n * u * n⁻¹) * z⁻¹) * n = n⁻¹ * z * n * u * (n⁻¹ * z * n)⁻¹ by group] at hu
    exact hu
  · intro h x
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have hx := h (n⁻¹ * x * n)
    rw [show n⁻¹ * z * n * (n⁻¹ * x * n) * (n⁻¹ * z * n)⁻¹ = n⁻¹ * (z * x * z⁻¹) * n by group]
      at hx
    exact hx

private theorem pmStd_actsPM_of_factor {C : Subgroup G} {n z w : G} (hn : ActsPM C n)
    (hw : w = n * z) : ActsPM C w ↔ ActsPM C z := by
  subst hw
  constructor
  · intro h
    have h' := ActsPM.mul (ActsPM.inv hn) h
    rwa [inv_mul_cancel_left] at h'
  · intro h
    exact ActsPM.mul hn h

theorem actsPM_conjSub_iff (D : Subgroup G) (n y : G) :
    ActsPM (conjSub n D) (n * y * n⁻¹) ↔ ActsPM D y := by
  constructor
  · rintro (h | h)
    · refine Or.inl fun x hx => pmStd_conj_cancel (n := n) ?_
      have h1 := h (n * x * n⁻¹) (conj_mem_conjSub hx)
      rw [show n * y * n⁻¹ * (n * x * n⁻¹) * (n * y * n⁻¹)⁻¹ = n * (y * x * y⁻¹) * n⁻¹ by group]
        at h1
      exact h1
    · refine Or.inr fun x hx => pmStd_conj_cancel (n := n) ?_
      have h1 := h (n * x * n⁻¹) (conj_mem_conjSub hx)
      rw [show n * y * n⁻¹ * (n * x * n⁻¹) * (n * y * n⁻¹)⁻¹ = n * (y * x * y⁻¹) * n⁻¹ by group,
        show (n * x * n⁻¹)⁻¹ = n * x⁻¹ * n⁻¹ by group] at h1
      exact h1
  · rintro (h | h)
    · refine Or.inl fun x' hx' => ?_
      rw [mem_conjSub_iff] at hx'
      have h1 := h (n⁻¹ * x' * n) hx'
      rw [show n * y * n⁻¹ * x' * (n * y * n⁻¹)⁻¹ = n * (y * (n⁻¹ * x' * n) * y⁻¹) * n⁻¹ by group,
        h1]
      group
    · refine Or.inr fun x' hx' => ?_
      rw [mem_conjSub_iff] at hx'
      have h1 := h (n⁻¹ * x' * n) hx'
      rw [show n * y * n⁻¹ * x' * (n * y * n⁻¹)⁻¹ = n * (y * (n⁻¹ * x' * n) * y⁻¹) * n⁻¹ by group,
        h1]
      group

theorem natCard_conjSub (D : Subgroup G) (n : G) : Nat.card ↥(conjSub n D) = Nat.card ↥D :=
  (Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).toEquiv).symm

theorem isCyclic_conjSub {D : Subgroup G} (hD : IsCyclic ↥D) (n : G) : IsCyclic ↥(conjSub n D) :=
  (MulEquiv.isCyclic (Subgroup.equivMapOfInjective D (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective)).mp hD

theorem nonempty_equiv_conjSub {Q : Subgroup G} {M : Type*} [Group M] (e : ↥Q ≃* M) (n : G) :
    Nonempty (↥(conjSub n Q) ≃* M) :=
  ⟨(Subgroup.equivMapOfInjective Q (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).symm.trans e⟩

end Transport

section Sylow

variable {G : Type} [Group G] [Finite G] {r : ℕ}

private theorem pmStd_natCard_quat {T : Type*} [Group T] {n : ℕ} (hn : 0 < n)
    (e : T ≃* QuaternionGroup n) : Nat.card T = 4 * n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem pmStd_relIndex_two (hr : 4 ≤ r) {D S : Subgroup G} (hDS : D ≤ S)
    (hS : Nat.card ↥S = 4 * 2 ^ (r - 2)) (hD : Nat.card ↥D = 2 ^ (r - 1)) :
    D.relIndex S = 2 := by
  have h := Subgroup.relIndex_mul_card D S
  rw [inf_eq_left.mpr hDS, hS, hD] at h
  have hpow : (2 : ℕ) ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ (r - 2) := by positivity
  rw [hpow] at h
  have h2 : D.relIndex S * 2 = 4 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    linarith
  omega

theorem exists_conjSub_eq_of_isCyclic (hr : 4 ≤ r) {K Q : Subgroup G} (hQ : IsSylow2In Q K)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {D₁ D₂ : Subgroup G} (hD₁ : D₁ ≤ K) (hD₂ : D₂ ≤ K)
    (hc₁ : IsCyclic ↥D₁) (hc₂ : IsCyclic ↥D₂) (hn₁ : Nat.card ↥D₁ = 2 ^ (r - 1))
    (hn₂ : Nat.card ↥D₂ = 2 ^ (r - 1)) : ∃ k ∈ K, conjSub k D₁ = D₂ := by
  have key : ∀ {D : Subgroup G}, D ≤ K → Nat.card ↥D = 2 ^ (r - 1) →
      ∃ x ∈ K, D ≤ conjSub x Q := by
    intro D hDK hDn
    have hD2 : IsPGroup 2 ↥D := IsPGroup.iff_card.mpr ⟨r - 1, hDn⟩
    obtain ⟨V, hV, hDV⟩ := IsSylow2In.exists_ge hD2 hDK
    obtain ⟨x, hxK, hx⟩ := exists_conjSub_eq_of_isSylow2In hQ hV
    exact ⟨x, hxK, by rw [hx]; exact hDV⟩
  obtain ⟨x₁, hx₁K, hD₁x⟩ := key hD₁ hn₁
  obtain ⟨x₂, hx₂K, hD₂x⟩ := key hD₂ hn₂
  have hE₁Q : conjSub x₁⁻¹ D₁ ≤ Q :=
    (conjSub_mono (n := x₁⁻¹) hD₁x).trans (conjSub_inv_conjSub x₁ Q).le
  have hE₂Q : conjSub x₂⁻¹ D₂ ≤ Q :=
    (conjSub_mono (n := x₂⁻¹) hD₂x).trans (conjSub_inv_conjSub x₂ Q).le
  have hQn : Nat.card ↥Q = 4 * 2 ^ (r - 2) := pmStd_natCard_quat (by positivity) e
  have hE₁i : (conjSub x₁⁻¹ D₁).relIndex Q = 2 :=
    pmStd_relIndex_two hr hE₁Q hQn ((natCard_conjSub D₁ x₁⁻¹).trans hn₁)
  have hE₂i : (conjSub x₂⁻¹ D₂).relIndex Q = 2 :=
    pmStd_relIndex_two hr hE₂Q hQn ((natCard_conjSub D₂ x₂⁻¹).trans hn₂)
  have hEq : conjSub x₁⁻¹ D₁ = conjSub x₂⁻¹ D₂ :=
    eq_of_isCyclic_of_relIndex_eq_two hr e hE₁Q (isCyclic_conjSub hc₁ _) hE₁i hE₂Q
      (isCyclic_conjSub hc₂ _) hE₂i
  refine ⟨x₂ * x₁⁻¹, Subgroup.mul_mem _ hx₂K (Subgroup.inv_mem _ hx₁K), ?_⟩
  rw [conjSub_mul, hEq, conjSub_conjSub_inv]

theorem le_pmSubgroup_of_isPGroup (hr : 4 ≤ r) {K Q : Subgroup G} (hQ : IsSylow2In Q K)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {D P : Subgroup G} (hPK : P ≤ K)
    (hP : IsPGroup 2 ↥P) (hDP : D ≤ P) (hDc : IsCyclic ↥D) (hDn : Nat.card ↥D = 2 ^ (r - 1)) :
    P ≤ pmSubgroup D := by
  obtain ⟨V, hV, hPV⟩ := IsSylow2In.exists_ge hP hPK
  obtain ⟨x, -, hx⟩ := exists_conjSub_eq_of_isSylow2In hQ hV
  subst hx
  obtain ⟨e'⟩ := nonempty_equiv_conjSub e x
  have hDS : D ≤ conjSub x Q := hDP.trans hPV
  have hS : Nat.card ↥(conjSub x Q) = 4 * 2 ^ (r - 2) :=
    pmStd_natCard_quat (by positivity) e'
  exact hPV.trans (le_pmSubgroup_of_quat hr e' hDS hDc (pmStd_relIndex_two hr hDS hS hDn))

theorem normalizer_inf_le_pmSubgroup (hr : 4 ≤ r) {K Q : Subgroup G} (hQ : IsSylow2In Q K)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {D : Subgroup G} (hDK : D ≤ K) (hDc : IsCyclic ↥D)
    (hDn : Nat.card ↥D = 2 ^ (r - 1)) : Subgroup.normalizer (D : Set G) ⊓ K ≤ pmSubgroup D := by
  rintro n ⟨hnN, hnK⟩
  obtain ⟨a, b, hab, ha, hb, ha2, hbodd⟩ := exists_mul_eq_isPGroup_odd n
  have hzN : Subgroup.zpowers n ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.mpr hnN
  have hzK : Subgroup.zpowers n ≤ K := Subgroup.zpowers_le.mpr hnK
  have haN : a ∈ Subgroup.normalizer (D : Set G) := hzN ha
  have hbN : b ∈ Subgroup.normalizer (D : Set G) := hzN hb
  have haK : a ∈ K := hzK ha
  have hbC : b ∈ pmSubgroup D :=
    centralizer_le_pmSubgroup D (mem_centralizer_of_odd_orderOf hDc hDn hbN hbodd)
  have hD2 : IsPGroup 2 ↥D := IsPGroup.iff_card.mpr ⟨r - 1, hDn⟩
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ D) :=
    IsPGroup.to_sup_of_normal_right' ha2 hD2 (Subgroup.zpowers_le.mpr haN)
  have hPK : Subgroup.zpowers a ⊔ D ≤ K := sup_le (Subgroup.zpowers_le.mpr haK) hDK
  have haP : a ∈ pmSubgroup D :=
    le_pmSubgroup_of_isPGroup hr hQ e hPK hP2 le_sup_right hDc hDn
      ((le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ D) (Subgroup.mem_zpowers a))
  rw [hab]
  exact Subgroup.mul_mem _ haP hbC

theorem actsPM_conj_iff_of_sylow (hr : 4 ≤ r) {K Q : Subgroup G} (hQ : IsSylow2In Q K)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) {D₁ D₂ : Subgroup G} (hD₁ : D₁ ≤ K) (hD₂ : D₂ ≤ K)
    (hc₁ : IsCyclic ↥D₁) (hc₂ : IsCyclic ↥D₂) (hn₁ : Nat.card ↥D₁ = 2 ^ (r - 1))
    (hn₂ : Nat.card ↥D₂ = 2 ^ (r - 1)) {g y : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hyD₁ : y ∈ Subgroup.normalizer (D₁ : Set G))
    (hyD₂ : g⁻¹ * y * g ∈ Subgroup.normalizer (D₂ : Set G)) :
    ActsPM D₁ y ↔ ActsPM D₂ (g⁻¹ * y * g) := by
  have hgK : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hE₁K : conjSub g⁻¹ D₁ ≤ K :=
    (conjSub_mono (n := g⁻¹) hD₁).trans (conjSub_eq_of_mem_normalizer hgK).le
  have hE₁c : IsCyclic ↥(conjSub g⁻¹ D₁) := isCyclic_conjSub hc₁ g⁻¹
  have hE₁n : Nat.card ↥(conjSub g⁻¹ D₁) = 2 ^ (r - 1) := (natCard_conjSub D₁ g⁻¹).trans hn₁
  obtain ⟨k, hkK, hk⟩ := exists_conjSub_eq_of_isCyclic hr hQ e hE₁K hD₂ hE₁c hc₂ hE₁n hn₂
  have hy₂K : g⁻¹ * y * g ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgK hy) hg
  have hy₂E : g⁻¹ * y * g ∈ Subgroup.normalizer ((conjSub g⁻¹ D₁ : Subgroup G) : Set G) := by
    rw [pmStd_mem_normalizer_conjSub, show (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y by group]
    exact hyD₁
  have hy₃E : k⁻¹ * (g⁻¹ * y * g) * k ∈
      Subgroup.normalizer ((conjSub g⁻¹ D₁ : Subgroup G) : Set G) := by
    rw [← hk] at hyD₂
    exact (pmStd_mem_normalizer_conjSub _ k _).mp hyD₂
  have hy₂kK : (g⁻¹ * y * g) * k * (g⁻¹ * y * g)⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hy₂K k).mp hkK
  have hn₀K : (k⁻¹ * (g⁻¹ * y * g) * k) * (g⁻¹ * y * g)⁻¹ ∈ K := by
    rw [show (k⁻¹ * (g⁻¹ * y * g) * k) * (g⁻¹ * y * g)⁻¹
        = k⁻¹ * ((g⁻¹ * y * g) * k * (g⁻¹ * y * g)⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkK) hy₂kK
  have hn₀N : (k⁻¹ * (g⁻¹ * y * g) * k) * (g⁻¹ * y * g)⁻¹ ∈
      Subgroup.normalizer ((conjSub g⁻¹ D₁ : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hy₃E (Subgroup.inv_mem _ hy₂E)
  have hn₀ : ActsPM (conjSub g⁻¹ D₁) ((k⁻¹ * (g⁻¹ * y * g) * k) * (g⁻¹ * y * g)⁻¹) :=
    mem_pmSubgroup.mp
      (normalizer_inf_le_pmSubgroup hr hQ e hE₁K hE₁c hE₁n (Subgroup.mem_inf.mpr ⟨hn₀N, hn₀K⟩))
  have hact : ActsPM (conjSub g⁻¹ D₁) (k⁻¹ * (g⁻¹ * y * g) * k) ↔
      ActsPM (conjSub g⁻¹ D₁) (g⁻¹ * y * g) :=
    pmStd_actsPM_of_factor hn₀ (by group)
  have step1 : ActsPM D₁ y ↔ ActsPM (conjSub g⁻¹ D₁) (g⁻¹ * y * g) := by
    have h := actsPM_conjSub_iff D₁ g⁻¹ y
    rw [inv_inv] at h
    exact h.symm
  have step3 : ActsPM (conjSub k (conjSub g⁻¹ D₁)) (k * (k⁻¹ * (g⁻¹ * y * g) * k) * k⁻¹) ↔
      ActsPM (conjSub g⁻¹ D₁) (k⁻¹ * (g⁻¹ * y * g) * k) := actsPM_conjSub_iff _ k _
  rw [hk, show k * (k⁻¹ * (g⁻¹ * y * g) * k) * k⁻¹ = g⁻¹ * y * g by group] at step3
  exact step1.trans (hact.symm.trans step3.symm)

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA.R4

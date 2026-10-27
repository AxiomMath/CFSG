module

public import CFSG.LargeExtraspecial.AS35WOne

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

variable {X Y : Type} [Group X] [Group Y]

theorem card_centralizer_map (e : X ≃* Y) (x : X) :
    Nat.card (centralizer ({e x} : Set Y)) = Nat.card (centralizer ({x} : Set X)) := by
  rw [centralizer_map e x, Subgroup.card_map_of_injective e.injective]

theorem natCard_centralizer_eq_of_isConj {x y : X} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({y} : Set X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hy : MulAut.conj c x = y := by rw [MulAut.conj_apply, hc]
  rw [← hy, card_centralizer_map]

theorem QuatLike.pow_four_eq_one {z : X} {R : Subgroup X} (hq : QuatLike z R) {r : X}
    (hr : r ∈ R) : r ^ 4 = 1 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact hq.z_mul_z
  rcases hq.cases r hr with rfl | rfl | h1
  · exact one_pow 4
  · rw [h4, pow_mul, hz2, one_pow]
  · rw [h4, pow_mul, h1, hz2]

theorem QuatLike.card_dvd_eight [Finite X] {z : X} {R : Subgroup X} (hq : QuatLike z R)
    (hR2 : IsPGroup 2 R) {a b : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z)
    (hb : b ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z) : Nat.card R ∣ 8 := by
  classical
  set l : List X := [1, z, a, a * z, b, b * z, a * b, a * b * z] with hl
  have hsub : ∀ r ∈ R, r ∈ l.toFinset := by
    intro r hr
    rw [List.mem_toFinset]
    rcases hq.mem_eight haR hbR ha hb hne hr with h | h | h | h | h | h | h | h <;> simp [hl, h]
  have hle : Nat.card R ≤ 8 :=
    (card_le_of_forall_mem R _ hsub).trans (List.toFinset_card_le l)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hR2
  rw [hn] at hle ⊢
  have hn3 : n ≤ 3 := by
    by_contra hc
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact Nat.pow_dvd_pow 2 hn3

variable {z : X}

theorem W2Data.centralizer_le_of_four (h : W2Data X z) (hq : QuatLike z (oTwoCent z)) {a : X}
    (hR : ∀ r ∈ oTwoCent z, r = 1 ∨ r = z ∨ r = a ∨ r = a * z) :
    centralizer ({z} : Set X) ≤ oTwoCent z := by
  set R := oTwoCent z with hRdef
  have hsq : ∀ c ∈ centralizer ({z} : Set X), c ^ 2 ∈ R := by
    intro c hc
    have hcz : Commute c z := mem_centralizer_singleton_iff.1 hc
    have key : a ∈ R → Commute (c ^ 2) a := by
      intro haR
      rcases hR _ (conj_mem_oTwoCent hc haR) with h1 | h1 | h1 | h1
      · have ha1 : a = 1 := by
          have := congrArg (fun t => c⁻¹ * t * c) h1
          simpa [mul_assoc] using this
        rw [ha1]
        exact Commute.one_right _
      · have haz : a = z := by
          have h2 : a = c⁻¹ * (c * a * c⁻¹) * c := by group
          rw [h2, h1, mul_assoc, ← hcz.eq, inv_mul_cancel_left]
        rw [haz]
        exact hcz.pow_left 2
      · have hca : Commute c a := by
          change c * a = a * c
          calc c * a = c * a * c⁻¹ * c := by group
            _ = a * c := by rw [h1]
        exact hca.pow_left 2
      · change c ^ 2 * a = a * c ^ 2
        rw [sq]
        have hz' : c * z * c⁻¹ = z := by rw [hcz.eq, mul_inv_cancel_right]
        have e1 : c * c * a * (c * c)⁻¹ = c * (c * a * c⁻¹) * c⁻¹ := by group
        have e2 : c * (a * z) * c⁻¹ = c * a * c⁻¹ * (c * z * c⁻¹) := by group
        have e3 : c * c * a * (c * c)⁻¹ = a := by
          rw [e1, h1, e2, h1, hz', mul_assoc, hq.z_mul_z, mul_one]
        calc c * c * a = c * c * a * (c * c)⁻¹ * (c * c) := by group
          _ = a * (c * c) := by rw [e3]
    refine h.selfCentralizing _ (pow_mem hc 2) fun r hr => ?_
    rcases hR r hr with rfl | rfl | rfl | rfl
    · rw [mul_one, one_mul]
    · exact (hcz.pow_left 2).eq
    · exact (key hr).eq
    · have haR : a ∈ R := by
        have := R.mul_mem hr hq.z_mem
        rwa [mul_assoc, hq.z_mul_z, mul_one] at this
      exact ((key haR).mul_right (hcz.pow_left 2)).eq
  have hP : IsPGroup 2 (centralizer ({z} : Set X)) := by
    intro c
    refine ⟨3, Subtype.ext ?_⟩
    have h8 : (2 : ℕ) ^ 3 = 2 * 4 := rfl
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [h8, pow_mul]
    exact hq.pow_four_eq_one (hsq c c.2)
  exact le_oTwoCent le_rfl (fun c hc p hp => mul_mem (mul_mem hc hp) (inv_mem hc)) hP

theorem W2Data.false_of_four (h : W2Data X z) (hq : QuatLike z (oTwoCent z)) {a : X}
    (hR : ∀ r ∈ oTwoCent z, r = 1 ∨ r = z ∨ r = a ∨ r = a * z) (E : Subgroup X)
    (hE : Open.IsElemAbelian 2 E) (hEz : E ≤ centralizer ({z} : Set X))
    (hcard : Nat.card E = 4) : False := by
  classical
  have hle := h.centralizer_le_of_four hq hR
  have hsub : ∀ e ∈ E, e ∈ ({1, z} : Finset X) := by
    intro e he
    rcases hq.cases e (hle (hEz he)) with h1 | h1 | h1
    · simp [h1]
    · simp [h1]
    · exact absurd (h1.symm.trans (hE.2 e he)) hq.z_ne_one
  have := card_le_of_forall_mem E _ hsub
  have h2 : ({1, z} : Finset X).card ≤ 2 := Finset.card_le_two
  omega

@[reducible] noncomputable def cycAction {R : Subgroup X} (h : QuatLike z R) {a b : X}
    (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z)
    (E : Subgroup X) (hEz : ∀ e ∈ E, e * z = z * e) (hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R) :
    MulAction E (Fin 3) where
  smul e i := cls z a b ((e : X) * rep a b i * (e : X)⁻¹)
  one_smul i := by
    change cls z a b ((1 : X) * rep a b i * (1 : X)⁻¹) = i
    rw [one_mul, inv_one, mul_one, h.cls_rep hbR ha hb hne]
  mul_smul e₁ e₂ i := by
    change cls z a b ((e₁ * e₂ : X) * rep a b i * (e₁ * e₂ : X)⁻¹) =
      cls z a b ((e₁ : X) * rep a b (cls z a b ((e₂ : X) * rep a b i * (e₂ : X)⁻¹)) *
        (e₁ : X)⁻¹)
    have hy := h.inSix_conj haR hbR ha hb hne (hEz _ e₂.2) (hER _ e₂.2) (inSix_rep i)
    have he : (e₁ * e₂ : X) * rep a b i * (e₁ * e₂ : X)⁻¹ =
        (e₁ : X) * ((e₂ : X) * rep a b i * (e₂ : X)⁻¹) * (e₁ : X)⁻¹ := by group
    rw [he]
    rcases h.rep_cls hbR ha hb hne hy with e | e
    · rw [← e]
    · have hw := h.inSix_conj haR hbR ha hb hne (hEz _ e₁.2) (hER _ e₁.2)
        (inSix_rep (cls z a b ((e₂ : X) * rep a b i * (e₂ : X)⁻¹)))
      have hz1 := conj_mul_z (hEz _ e₁.2) (rep a b (cls z a b ((e₂ : X) * rep a b i *
        (e₂ : X)⁻¹)))
      conv_lhs => rw [e]
      rw [hz1, h.cls_mul_z hbR ha hb hne hw]

theorem W2Data.card_centralizer_dvd [Finite X] (h : W2Data X z) (hq : QuatLike z (oTwoCent z))
    {a b : X} (haR : a ∈ oTwoCent z) (hbR : b ∈ oTwoCent z) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hne : b ≠ a ∧ b ≠ a * z) : Nat.card (centralizer ({z} : Set X)) ∣ 48 := by
  set R := oTwoCent z with hRdef
  set E := centralizer ({z} : Set X) with hEdef
  have hEz : ∀ e ∈ E, e * z = z * e := fun e he => mem_centralizer_singleton_iff.1 he
  have hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := fun e he r hr => conj_mem_oTwoCent he hr
  have hfs : ∀ c : X, c * z = z * c → (∀ r ∈ R, c * r = r * c) → c ∈ R := fun c hc hcr =>
    h.selfCentralizing c (mem_centralizer_singleton_iff.2 hc) hcr
  let _ := cycAction hq haR hbR ha hb hne E hEz hER
  set φ := MulAction.toPermHom E (Fin 3) with hφ
  have hfix : ∀ k ∈ φ.ker, ∀ i : Fin 3,
      (k : X) * rep a b i * (k : X)⁻¹ = rep a b i ∨
        (k : X) * rep a b i * (k : X)⁻¹ = rep a b i * z := by
    intro k hk i
    have hki : k • i = i := by
      have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) (MonoidHom.mem_ker.1 hk)
      simpa [hφ] using this
    have hki' : cls z a b ((k : X) * rep a b i * (k : X)⁻¹) = i := hki
    have hy := hq.inSix_conj haR hbR ha hb hne (hEz _ k.2) (hER _ k.2) (inSix_rep i)
    have hr := hq.rep_cls hbR ha hb hne hy
    rwa [hki'] at hr
  have hker : φ.ker.map E.subtype ≤ R := by
    rintro _ ⟨k, hk, rfl⟩
    exact hq.mem_of_fixes haR hbR ha hb hne (hEz _ k.2) hfs (hfix k hk 0) (hfix k hk 1)
  have hkdvd : Nat.card φ.ker ∣ 8 := by
    have h1 := Subgroup.card_dvd_of_le hker
    rw [Subgroup.card_map_of_injective E.subtype_injective] at h1
    exact h1.trans (hq.card_dvd_eight (isPGroup_oTwoCent z) haR hbR ha hb hne)
  have hr6 : Nat.card φ.range ∣ 6 := by
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [h6] at this
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hmul
  rw [← hmul]
  exact Nat.mul_dvd_mul hkdvd hr6

theorem oTwoCent_le_sylow [Finite X] (P : Sylow 2 X)
    (hP : (P : Subgroup X) ≤ centralizer ({z} : Set X)) : oTwoCent z ≤ P := by
  have hN : (P : Subgroup X) ≤ Subgroup.normalizer (oTwoCent z : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact fun hr => conj_mem_oTwoCent (hP hg) hr
    · intro hr
      have := conj_mem_oTwoCent (inv_mem (hP hg)) hr
      simpa [mul_assoc] using this
  have h2 := P.isPGroup'.to_sup_of_normal_right' (isPGroup_oTwoCent z) hN
  rw [← P.is_maximal' h2 le_sup_left]
  exact le_sup_right

theorem commute_of_dihedral {P : Type*} [Group P] {N : ℕ} (e : P ≃* DihedralGroup N)
    {a b : P} (ha : a ^ 2 ≠ 1) (hb : b ^ 2 ≠ 1) : a * b = b * a := by
  have hrot : ∀ x : P, x ^ 2 ≠ 1 → ∃ i, e x = DihedralGroup.r i := by
    intro x hx
    rcases hex : e x with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      apply hx
      apply e.injective
      rw [map_pow, hex, map_one, sq, DihedralGroup.sr_mul_self]
  obtain ⟨i, hi⟩ := hrot a ha
  obtain ⟨j, hj⟩ := hrot b hb
  apply e.injective
  rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

theorem W2Data.four_mul_card_le [Finite X] (h : W2Data X z)
    (hc : ∀ x : X, (∀ y : X, x * y = y * x) → x = 1) (hR : Nat.card (oTwoCent z) ≤ 8) :
    4 * Nat.card X ≤ Nat.card (MulAut X) := by
  classical
  obtain ⟨A, hA, -, hAc⟩ := h.aut
  have : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) fun φ ψ hφψ =>
      MulEquiv.ext (congrFun hφψ)
  set I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hIdef
  have hIn : I.Normal := ⟨by
    rintro _ ⟨x, rfl⟩ g
    refine ⟨g x, MulEquiv.ext fun y => ?_⟩
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine hc x fun y => ?_
    have := congrArg (fun φ : MulAut X => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [this]
  have hIcard : Nat.card I = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  set φ := (QuotientGroup.mk' I).comp A.subtype with hφ
  have hker : Nat.card φ.ker ≤ 8 := by
    have hmem : ∀ k : φ.ker, ∃ x : X, MulAut.conj x = ((k : A) : MulAut X) := by
      intro k
      have hk : QuotientGroup.mk' I ((k : A) : MulAut X) = 1 := k.2
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      obtain ⟨x, hx⟩ := hk
      exact ⟨x, hx⟩
    choose g hg using hmem
    have hgR : ∀ k, g k ∈ oTwoCent z := fun k => hAc _ (by rw [hg]; exact (k : A).2)
    have hinj' : Function.Injective (fun k : φ.ker => (⟨g k, hgR k⟩ : oTwoCent z)) := by
      intro k₁ k₂ hk
      have h12 : g k₁ = g k₂ := congrArg Subtype.val hk
      apply Subtype.ext
      apply Subtype.ext
      rw [← hg k₁, ← hg k₂, h12]
    exact (Nat.card_le_card_of_injective _ hinj').trans hR
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hA] at hmul
  have hrange : Nat.card φ.range ≤ I.index := Subgroup.card_le_card_group φ.range
  have hidx := Subgroup.card_mul_index I
  rw [hIcard] at hidx
  have hr4 : 4 ≤ Nat.card φ.range := by
    by_contra hlt
    have : Nat.card φ.ker * Nat.card φ.range ≤ 8 * 3 :=
      Nat.mul_le_mul hker (by omega)
    omega
  rw [← hidx, mul_comm]
  exact Nat.mul_le_mul_left _ (hr4.trans hrange)

end AS35W

end CFSG.LargeExtraspecial

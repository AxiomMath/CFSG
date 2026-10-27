module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusNormalizer

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

variable {E : Type*} [Group E]

theorem mem_sup_zpowers_cases {U : Subgroup E} {w : E} (hw2 : w * w = 1)
    (hinv : ∀ u ∈ U, w * u * w⁻¹ = u⁻¹) {z : E} (hz : z ∈ U ⊔ Subgroup.zpowers w) :
    z ∈ U ∨ z * w ∈ U := by
  have hwi : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  let X : Subgroup E :=
    { carrier := {x | x ∈ U ∨ x * w ∈ U}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (U.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact U.mul_mem ha hb)
        · right
          have hbw : w⁻¹ * b * w ∈ U := by
            have := hinv b hb
            rw [hwi] at this ⊢
            rw [this]
            exact U.inv_mem hb
          have : a * b * w = a * w * (w⁻¹ * b * w) := by group
          rw [this]
          exact U.mul_mem ha hbw
        · left
          have hbw : w⁻¹ * (b * w) * w⁻¹ ∈ U := by
            have := hinv (b * w) hb
            rw [hwi] at this ⊢
            rw [this]
            exact U.inv_mem hb
          have : a * b = a * w * (w⁻¹ * (b * w) * w⁻¹) := by group
          rw [this]
          exact U.mul_mem ha hbw
      one_mem' := Or.inl U.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (U.inv_mem ha)
        · right
          have : a⁻¹ * w = w * (a * w)⁻¹ * w⁻¹ := by rw [hwi]; group
          rw [this, hinv _ (U.inv_mem ha), inv_inv]
          exact ha }
  have hle : U ⊔ Subgroup.zpowers w ≤ X := by
    refine sup_le (fun u hu => Or.inl hu) ?_
    rw [Subgroup.zpowers_le]
    right
    rw [hw2]
    exact U.one_mem
  exact hle hz

theorem card_map_mk_mul [Finite E] (O A : Subgroup E) [O.Normal] :
    Nat.card (A.map (QuotientGroup.mk' O)) * Nat.card (O.subgroupOf A) = Nat.card A := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((QuotientGroup.mk' O).domRestrict A).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
    MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk'] at h1
  exact h1.symm

theorem centralizer_map_mk [Finite E] {O : Subgroup E} [O.Normal] (hO : Odd (Nat.card O))
    {u : E} (hu : u * u = 1) :
    (Subgroup.centralizer ({u} : Set E)).map (QuotientGroup.mk' O) =
      Subgroup.centralizer ({QuotientGroup.mk' O u} : Set (E ⧸ O)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hx'])
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hP : IsPGroup 2 (Subgroup.zpowers u) := fun p => ⟨1, by
      apply Subtype.ext
      rcases zpowers_cases_of_mul_self hu p p.2 with h | h <;> simp [h, pow_two, hu]⟩
    have hxO : ∀ p ∈ Subgroup.zpowers u, x⁻¹ * p * x * p⁻¹ ∈ O := by
      intro p hp
      rcases zpowers_cases_of_mul_self hu p hp with h | h
      · rw [h]
        simp
      · rw [h]
        apply (QuotientGroup.eq_one_iff _).mp
        have hy' : (x : E ⧸ O) * (u : E ⧸ O) = (u : E ⧸ O) * (x : E ⧸ O) := hy
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv]
        calc ((x : E ⧸ O))⁻¹ * (u : E ⧸ O) * (x : E ⧸ O) * ((u : E ⧸ O))⁻¹ =
            ((x : E ⧸ O))⁻¹ * ((u : E ⧸ O) * (x : E ⧸ O)) * ((u : E ⧸ O))⁻¹ := by group
          _ = ((x : E ⧸ O))⁻¹ * ((x : E ⧸ O) * (u : E ⧸ O)) * ((u : E ⧸ O))⁻¹ := by rw [hy']
          _ = 1 := by group
    obtain ⟨o, ho, hxo⟩ := exists_mem_centralizer_of_commutator_mem
      (fun g o ho => (inferInstance : O.Normal).conj_mem o ho g) hO hP hxO
    refine ⟨x * o, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxo u (Subgroup.mem_zpowers u)).symm
    · have ho' : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      rw [map_mul, ho', mul_one]

theorem map_centralizer_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (y : X) :
    (Subgroup.centralizer ({y} : Set X)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ y} : Set Y) := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg φ h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h

theorem dihedral_odd_core [Finite E] {U D : Subgroup E} (hU : IsCyclic U) {m : ℕ} (hm : Odd m)
    (hcard : Nat.card U = 2 * m) {w : E} (hw2 : w * w = 1)
    (hinv : ∀ u ∈ U, w * u * w⁻¹ = u⁻¹) (hD : D = U ⊔ Subgroup.zpowers w) :
    IsCyclic (CFSG.pPrimeCore 2 D) ∧ Nat.card (CFSG.pPrimeCore 2 D) = m ∧
      (∀ z : D, (z : E) ∉ U → ∀ o ∈ CFSG.pPrimeCore 2 D, z * o * z⁻¹ = o⁻¹) ∧
      (∀ y ∈ U, ∀ y' ∈ U, y * y = 1 → y' * y' = 1 → y ≠ 1 → y' ≠ 1 → y = y') := by
  classical
  obtain ⟨g, hg⟩ := hU.exists_generator
  have hgo : orderOf (g : E) = 2 * m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hgen : ∀ y ∈ U, ∃ k : ℤ, y = (g : E) ^ k := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := hgen a ha
    obtain ⟨j, rfl⟩ := hgen b hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hwi : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  set O₁ : Subgroup E := Subgroup.zpowers ((g : E) ^ 2) with hO₁def
  have hO₁U : O₁ ≤ U := Subgroup.zpowers_le.mpr (U.pow_mem g.2 2)
  have hO₁card : Nat.card O₁ = m := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) (by rw [hgo]; exact dvd_mul_right 2 m),
      hgo]
    omega
  have hUD : U ≤ D := hD ▸ le_sup_left
  have hO₁D : O₁ ≤ D := hO₁U.trans hUD
  have hout : ∀ z ∈ D, z ∉ U → ∀ u ∈ U, z * u * z⁻¹ = u⁻¹ := by
    intro z hz hzU u hu
    rcases mem_sup_zpowers_cases hw2 hinv (hD ▸ hz) with h | h
    · exact absurd h hzU
    · have hwu : w⁻¹ * u * w = u⁻¹ := by
        have h1 := hinv u hu
        rw [hwi] at h1 ⊢
        exact h1
      calc z * u * z⁻¹ = (z * w) * (w⁻¹ * u * w) * (z * w)⁻¹ := by group
        _ = (z * w) * u⁻¹ * (z * w)⁻¹ := by rw [hwu]
        _ = u⁻¹ := by rw [hUcomm _ h _ (U.inv_mem hu)]; group
  have hsq : ∀ z ∈ D, z ∉ U → z * z = 1 := by
    intro z hz hzU
    rcases mem_sup_zpowers_cases hw2 hinv (hD ▸ hz) with h | h
    · exact absurd h hzU
    · have h1 := hout z hz hzU (z * w) h
      calc z * z = z * (z * w) * z⁻¹ * z * w⁻¹ := by group
        _ = (z * w)⁻¹ * z * w⁻¹ := by rw [h1]
        _ = w⁻¹ * w⁻¹ := by group
        _ = 1 := by rw [← mul_inv_rev, hw2, inv_one]
  have hO₁n : (O₁.subgroupOf D).Normal := by
    refine ⟨fun y hy z => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    by_cases hzU : (z : E) ∈ U
    · have heq : ((z * y * z⁻¹ : D) : E) = y := by
        push_cast
        rw [hUcomm _ hzU _ (hO₁U hy)]
        group
      rw [heq]
      exact hy
    · have heq : ((z * y * z⁻¹ : D) : E) = (y : E)⁻¹ := by
        push_cast
        exact hout z z.2 hzU y (hO₁U hy)
      rw [heq]
      exact O₁.inv_mem hy
  have hle1 : O₁.subgroupOf D ≤ CFSG.pPrimeCore 2 D := le_sSup ⟨hO₁n, by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO₁D).toEquiv, hO₁card]
    exact Nat.coprime_two_left.mpr hm⟩
  have hle2 : CFSG.pPrimeCore 2 D ≤ O₁.subgroupOf D := by
    intro o ho
    rw [Subgroup.mem_subgroupOf]
    have hodd : Odd (orderOf (o : E)) := by
      rw [Subgroup.orderOf_coe]
      exact (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := D))).of_dvd_nat
        (Subgroup.orderOf_dvd_natCard _ ho)
    by_cases hoU : (o : E) ∈ U
    · obtain ⟨k, hk⟩ := hgen _ hoU
      have hpow : (g : E) ^ (k * (orderOf (o : E) : ℤ)) = 1 := by
        rw [zpow_mul, ← hk, zpow_natCast, pow_orderOf_eq_one]
      rw [← orderOf_dvd_iff_zpow_eq_one, hgo] at hpow
      have h2k : (2 : ℤ) ∣ k := by
        have h2 : (2 : ℤ) ∣ k * (orderOf (o : E) : ℤ) :=
          (dvd_mul_right (2 : ℤ) (m : ℤ)).trans (by exact_mod_cast hpow)
        rcases hodd with ⟨r, hr⟩
        rw [hr] at h2
        push_cast at h2
        have h3 : (2 : ℤ) ∣ k * (2 * r + 1) - 2 * (k * r) := dvd_sub h2 (dvd_mul_right 2 _)
        have h4 : k * (2 * (r : ℤ) + 1) - 2 * (k * r) = k := by ring
        rwa [h4] at h3
      obtain ⟨j, hj⟩ := h2k
      rw [hk, hj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← zpow_natCast, ← zpow_mul]; push_cast; ring_nf⟩
    · exfalso
      exact hoU (by
        rw [eq_one_of_mul_self_eq_one_of_odd hodd (hsq o o.2 hoU)]
        exact U.one_mem)
  have hOeq : CFSG.pPrimeCore 2 D = O₁.subgroupOf D := le_antisymm hle2 hle1
  have key : ∀ y ∈ U, y * y = 1 → y ≠ 1 → y = (g : E) ^ m := by
    intro y hy hy2 hy1
    obtain ⟨k, rfl⟩ := hgen y hy
    have h1 : (g : E) ^ (2 * k) = 1 := by rw [two_mul, zpow_add]; exact hy2
    rw [← orderOf_dvd_iff_zpow_eq_one, hgo] at h1
    have hmk : (m : ℤ) ∣ k := by
      push_cast at h1
      exact (mul_dvd_mul_iff_left two_ne_zero).mp h1
    obtain ⟨a, rfl⟩ := hmk
    have hgm : (g : E) ^ ((2 * m : ℕ) : ℤ) = 1 := by rw [zpow_natCast, ← hgo, pow_orderOf_eq_one]
    rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exfalso
      apply hy1
      rw [show (m : ℤ) * (b + b) = ((2 * m : ℕ) : ℤ) * b by push_cast; ring, zpow_mul, hgm,
        one_zpow]
    · rw [show (m : ℤ) * (2 * b + 1) = ((2 * m : ℕ) : ℤ) * b + m by push_cast; ring, zpow_add,
        zpow_mul, hgm, one_zpow, one_mul, zpow_natCast]
  refine ⟨?_, ?_, ?_, fun y hy y' hy' hy2 hy'2 hy1 hy'1 =>
    (key y hy hy2 hy1).trans (key y' hy' hy'2 hy'1).symm⟩
  · rw [hOeq]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hO₁D).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hO₁D).symm.surjective
  · rw [hOeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO₁D).toEquiv, hO₁card]
  · intro z hzU o ho
    rw [hOeq, Subgroup.mem_subgroupOf] at ho
    apply Subtype.ext
    push_cast
    exact hout z z.2 hzU o (hO₁U ho)

variable {G : Type} [Group G] {t s d : G} {J B W : Subgroup G}

theorem LocalData.card_sup_dihedral [Finite G] (h : LocalData t s d J B W)
    (hWodd : Odd (Nat.card W)) (hBodd : Odd (Nat.card B)) :
    Nat.card (W ⊔ B ⊔ (Subgroup.zpowers d ⊔ Subgroup.zpowers s) : Subgroup G) =
      8 * (Nat.card W * Nat.card B) := by
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := h.B_le_normalizer W le_rfl
  have hWB : Disjoint W B := by
    rw [Subgroup.disjoint_def]
    intro x hxW hxB
    have hx : x ∈ J ⊓ B := ⟨h.W_le_J hxW, hxB⟩
    rw [h.JB_disj] at hx
    exact Subgroup.mem_bot.mp hx
  have hWBcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W B hBN hWB
  have hcomm : ∀ x ∈ W, ∀ y ∈ B, x * y = y * x := fun x hx y hy => (h.B_comm_W y hy x hx).symm
  have hnorm : ∀ x, (∀ w ∈ W, x * w * x⁻¹ ∈ W) → (∀ b ∈ B, x * b * x⁻¹ ∈ B) →
      x ∈ Subgroup.normalizer ((W ⊔ B : Subgroup G) : Set G) := by
    intro x hxW hxB
    apply mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨w, hw, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hy
    have heq : x * (w * b) * x⁻¹ = (x * w * x⁻¹) * (x * b * x⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem_sup (hxW w hw) (hxB b hb)
  have hdN : d ∈ Subgroup.normalizer ((W ⊔ B : Subgroup G) : Set G) := by
    refine hnorm d (fun w hw => ?_) (fun b hb => ?_)
    · rw [h.d_inv w hw]
      exact W.inv_mem hw
    · rw [h.JB_comm d h.d_mem b hb, mul_inv_cancel_right]
      exact hb
  have hsN : s ∈ Subgroup.normalizer ((W ⊔ B : Subgroup G) : Set G) := by
    refine hnorm s (fun w hw => ?_) (fun b hb => ?_)
    · rw [← h.W_comm_s w hw, mul_inv_cancel_right]
      exact hw
    · rw [h.s_inv b hb]
      exact B.inv_mem hb
  have hPN : Subgroup.zpowers d ⊔ Subgroup.zpowers s ≤
      Subgroup.normalizer ((W ⊔ B : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hdN) (Subgroup.zpowers_le.mpr hsN)
  have hoddWB : Odd (Nat.card (W ⊔ B : Subgroup G)) := by
    rw [hWBcard]
    exact hWodd.mul hBodd
  have hdisj : Disjoint (W ⊔ B) (Subgroup.zpowers d ⊔ Subgroup.zpowers s) := by
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    exact eq_one_of_mem_of_odd h.dihedral_isPGroup hx2
      (hoddWB.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx1))
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hPN hdisj,
    hWBcard, h.dihedral_card]
  ring

end CFSG.Semidihedral.FixedCoreNontrivial

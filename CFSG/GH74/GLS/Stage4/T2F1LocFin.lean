module

public import CFSG.GH74.GLS.Stage4.T2F1LocShapeO
public import CFSG.GH74.GLS.Stage4.T2F1LocQuot
public import CFSG.GH74.GLS.Stage4.T2F1LocTor
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GH74.GLS.Stage4.T2SL2A
public import CFSG.GH74.GLS.Stage4.T2SL2B
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

structure ChartData {X : Type} [Group X] {A B : Type} [Field A] [Field B]
    (ψ₁ : SL2 A →* X) (ψ₂ : SL2 B →* X) (g₁ : GL (Fin 2) A) (g₂ : GL (Fin 2) B) (z t : X) : Prop where
  inj₁ : Function.Injective ψ₁
  inj₂ : Function.Injective ψ₂
  comm : ∀ (M : SL2 A) (N : SL2 B), ψ₁ M * ψ₂ N = ψ₂ N * ψ₁ M
  neg₁ : ψ₁ (negOne A) = z
  neg₂ : ψ₂ (negOne B) = z
  zz : z * z = 1
  z_ne : z ≠ 1
  inter : ∀ (M : SL2 A) (N : SL2 B), ψ₁ M = ψ₂ N → ψ₁ M = 1 ∨ ψ₁ M = z
  tt : t * t = 1
  act₁ : ∀ M : SL2 A, t * ψ₁ M * t⁻¹ = ψ₁ (slConj g₁ M)
  act₂ : ∀ N : SL2 B, t * ψ₂ N * t⁻¹ = ψ₂ (slConj g₂ N)
  ns₁ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₁ : Aˣ) : A)
  ns₂ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g₂ : Bˣ) : B)

@[expose] def ChartData.Y₀ {X : Type} [Group X] {A B : Type} [Field A] [Field B]
    (ψ₁ : SL2 A →* X) (ψ₂ : SL2 B →* X) (t : X) : Subgroup X :=
  ψ₁.range ⊔ ψ₂.range ⊔ Subgroup.zpowers t

theorem negOne_eq_neg_one {F : Type} [Field F] : (negOne F : SL2 F) = -1 := by
  apply Subtype.ext
  simp only [coe_negOne, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


theorem coprime_two_card_of_odd {Y : Type} [Group Y] (K : Subgroup Y) [Finite K]
    (h : ∀ x ∈ K, Odd (orderOf x)) : Nat.Coprime 2 (Nat.card K) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have := h x.1 x.2
  rw [Subgroup.orderOf_coe, hx] at this
  exact absurd this (by decide)

variable {X : Type} [Group X] {A B : Type} [Field A] [Field B]
  {ψ₁ : SL2 A →* X} {ψ₂ : SL2 B →* X} {g₁ : GL (Fin 2) A} {g₂ : GL (Fin 2) B} {z t : X}

theorem ChartData.mem₁ (M : SL2 A) : ψ₁ M ∈ ChartData.Y₀ ψ₁ ψ₂ t :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨M, rfl⟩)

theorem ChartData.mem₂ (N : SL2 B) : ψ₂ N ∈ ChartData.Y₀ ψ₁ ψ₂ t :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨N, rfl⟩)

theorem ChartData.mem_t : t ∈ ChartData.Y₀ ψ₁ ψ₂ t :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem ChartData.R_inf_Y₀ [Finite X] [Finite A] [Finite B]
    (D : ChartData ψ₁ ψ₂ g₁ g₂ z t) (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B))
    {R : Subgroup X} [R.Normal] (hR : ∀ x ∈ R, Odd (orderOf x)) :
    ∀ y ∈ R, y ∈ ChartData.Y₀ ψ₁ ψ₂ t → y = 1 := by
  set Y₀ := ChartData.Y₀ ψ₁ ψ₂ t with hY₀
  let fA : SL2 A →* ↥Y₀ := ψ₁.codRestrict Y₀ ChartData.mem₁
  let fB : SL2 B →* ↥Y₀ := ψ₂.codRestrict Y₀ ChartData.mem₂
  have hfA : Function.Injective fA := fun a b h => D.inj₁ (congrArg Subtype.val h)
  have hfB : Function.Injective fB := fun a b h => D.inj₂ (congrArg Subtype.val h)
  have hzY : z ∈ Y₀ := D.neg₁ ▸ ChartData.mem₁ (negOne A)
  let z' : ↥Y₀ := ⟨z, hzY⟩
  let t' : ↥Y₀ := ⟨t, ChartData.mem_t⟩
  have hgen : fA.range ⊔ fB.range ⊔ Subgroup.zpowers t' = ⊤ := by
    apply Subgroup.map_injective Y₀.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range,
      MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have S : IVK.Proofs2.Ivk47ab.Shape ↥Y₀ A B :=
    IVK.Proofs2.Ivk47ab.Shape.ofCharts fA fB hfA hfB
      (fun a b => Subtype.ext (D.comm a b)) z'
      (Subtype.ext (by simp [fA, z', negOne_eq_neg_one.symm, D.neg₁]))
      (Subtype.ext (by simp [fB, z', negOne_eq_neg_one.symm, D.neg₂]))
      (Subtype.ext D.zz) (fun h => D.z_ne (congrArg Subtype.val h))
      (fun a b h => by
        rcases D.inter a b (congrArg Subtype.val h) with h1 | h1
        · left; exact Subtype.ext h1
        · right; exact Subtype.ext h1)
      t' (Subtype.ext D.tt) hgen g₁ g₂ D.ns₁ D.ns₂
      (fun a => Subtype.ext (D.act₁ a)) (fun b => Subtype.ext (D.act₂ b))
  have hbot := S.pPrimeCore_eq_bot hA hB
  intro y hy hyY
  let N'' : Subgroup ↥Y₀ := R.comap Y₀.subtype
  have : N''.Normal := Subgroup.Normal.comap inferInstance _
  have hN : N'' ≤ pPrimeCore 2 ↥Y₀ :=
    le_sSup ⟨inferInstance, coprime_two_card_of_odd N'' (fun x hx => by
      have := hR (x : X) hx
      rwa [Subgroup.orderOf_coe] at this)⟩
  have : (⟨y, hyY⟩ : ↥Y₀) ∈ N'' := hy
  have h1 := hN this
  rw [hbot, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1


section Acts

variable {Q : Type} [Group Q] {F : Type} [Field F]

theorem actsAsConj_of_chart (ψ : SL2 F →* Q) (hψ : Function.Injective ψ) (t : Q) (g : GL (Fin 2) F)
    (h : ∀ M : SL2 F, t * ψ M * t⁻¹ = ψ (slConj g M)) :
    CFSG.GH74.GLS.Stage4.Rest.ActsAsConj t ψ.range (MonoidHom.ofInjective hψ).symm g := by
  rintro ⟨x, M, rfl⟩
  refine ⟨⟨ψ (slConj g M), slConj g M, rfl⟩, (h M).symm, ?_⟩
  have e1 : ((MonoidHom.ofInjective hψ).symm ⟨ψ M, M, rfl⟩ : SL2 F) = M := by
    rw [MulEquiv.symm_apply_eq]; rfl
  have e2 : ((MonoidHom.ofInjective hψ).symm ⟨ψ (slConj g M), slConj g M, rfl⟩ : SL2 F) = slConj g M := by
    rw [MulEquiv.symm_apply_eq]; rfl
  rw [e1, e2]
  rfl

end Acts



section Four

theorem isFourSubgroup_sup_zpowers {Q : Type} [Group Q] [Finite Q] {x y : Q} (hxy : x * y = y * x)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    CFSG.GH74.GLS.IVK.IsFourSubgroup (Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((Commute.zpow_zpow (show Commute x y from hxy) i j).eq)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgx, hgy⟩
    rcases mem_zpowers_of_sq hx2 hgx with h | h
    · exact h ▸ Subgroup.one_mem _
    · exfalso
      rcases mem_zpowers_of_sq hy2 (h ▸ hgy) with h' | h'
      · exact hx1 h'
      · exact hne h'
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers x)
    (Subgroup.zpowers y) hcomm).1
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo] at hcard
  refine ⟨?_, by omega⟩
  have hel : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm hg
    have hab : a * b = b * a := hcomm a ha b hb
    have ha2 : a * a = 1 := by
      rcases mem_zpowers_of_sq hx2 ha with h | h
      · rw [h, one_mul]
      · rw [h, hx2]
    have hb2 : b * b = 1 := by
      rcases mem_zpowers_of_sq hy2 hb with h | h
      · rw [h, one_mul]
      · rw [h, hy2]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hcommV : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
      ∀ g' ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y, g * g' = g' * g := by
    intro g hg g' hg'
    have h1 := hel g hg
    have h2 := hel g' hg'
    have h3 := hel (g * g') (Subgroup.mul_mem _ hg hg')
    calc g * g' = (g * g')⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
      _ = g'⁻¹ * g⁻¹ := mul_inv_rev g g'
      _ = g' * g := by
        rw [inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]
  have hc : IsMulCommutative ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    ⟨⟨fun a b => Subtype.ext (hcommV a a.2 b b.2)⟩⟩
  have hexp : Monoid.exponent ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => Subtype.ext (by
      simpa [pow_two] using hel g g.2))
  exact { toIsMulCommutative := hc, exponent_dvd_p := hexp }

end Four

section Quot

theorem hyp94Loc_of_charts
    {X : Type} [Group X] [Finite X] {Gs : Type} [Group Gs] {z u t : X} {m : ℕ} (hm : 1 ≤ m)
    {A B : Type} [Field A] [Field B] [Finite A] [Finite B] (hA : Nat.card A = 3 ^ m)
    (hB : Nat.card B = 3 ^ m) {ψ₁ : SL2 A →* X} {ψ₂ : SL2 B →* X} {g₁ : GL (Fin 2) A}
    {g₂ : GL (Fin 2) B} (D : ChartData ψ₁ ψ₂ g₁ g₂ z t)
    (htwo : ∀ y : X, y * z = z * y → (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ ChartData.Y₀ ψ₁ ψ₂ t)
    (S : Sylow 2 X) (hzS : z ∈ (S : Subgroup X)) (hzc : ∀ s ∈ (S : Subgroup X), z * s = s * z)
    (hZS : ∀ x ∈ (S : Subgroup X), (∀ s ∈ (S : Subgroup X), x * s = s * x) → x ∈ Subgroup.zpowers z)
    (hu : u ∈ (S : Subgroup X)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hne : u ≠ z) (hzu : z * u = u * z)
    (hSiso : ∃ S' : Sylow 2 Gs, Nonempty (↥(S : Subgroup X) ≃* ↥(S' : Subgroup Gs)))
    (hlie : ∃ p fe : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel Gs .G2 0 p fe)
    (hfuse : ∃ a : X, a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u) :
    CFSG.GH74.GLS.IVK.Hyp94Loc (X ⧸ pPrimeCore 2 X) Gs (QuotientGroup.mk z) .G2 3 m := by
  have hAodd : Odd (Nat.card A) := by rw [hA]; exact Odd.pow (by decide)
  have hBodd : Odd (Nat.card B) := by rw [hB]; exact Odd.pow (by decide)
  set R : Subgroup X := pPrimeCore 2 X with hRdef
  have hRodd : ∀ x ∈ R, Odd (orderOf x) := by
    intro x hx
    have h1 : Nat.Coprime 2 (Nat.card R) := pPrimeCore_coprime_card
    have h2 : orderOf x ∣ Nat.card R := by
      have := Subgroup.orderOf_dvd_natCard R (show x ∈ R from hx)
      exact this
    exact Nat.coprime_two_left.1 (h1.coprime_dvd_right h2)
  have hY := D.R_inf_Y₀ hAodd hBodd hRodd
  let π : X →* X ⧸ R := QuotientGroup.mk' R
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hker : ∀ y ∈ ChartData.Y₀ ψ₁ ψ₂ t, π y = 1 → y = 1 := fun y hy h =>
    hY y ((QuotientGroup.eq_one_iff y).1 h) hy
  have hinj₁ : Function.Injective (π.comp ψ₁) := by
    rw [injective_iff_map_eq_one]
    intro M hM
    have h1 : ψ₁ M = 1 := hker _ (ChartData.mem₁ M) hM
    exact D.inj₁ (by rw [h1, map_one])
  have hinj₂ : Function.Injective (π.comp ψ₂) := by
    rw [injective_iff_map_eq_one]
    intro M hM
    have h1 : ψ₂ M = 1 := hker _ (ChartData.mem₂ M) hM
    exact D.inj₂ (by rw [h1, map_one])
  have hact₁ : ∀ M : SL2 A, π t * (π.comp ψ₁) M * (π t)⁻¹ = (π.comp ψ₁) (slConj g₁ M) := by
    intro M
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, D.act₁]
  have hact₂ : ∀ M : SL2 B, π t * (π.comp ψ₂) M * (π t)⁻¹ = (π.comp ψ₂) (slConj g₂ M) := by
    intro M
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, D.act₂]
  have hcomm : ∀ x ∈ (π.comp ψ₁).range, ∀ y ∈ (π.comp ψ₂).range, x * y = y * x := by
    rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.comm]
  have hz1 : π z ≠ 1 := fun h => D.z_ne (hker z (D.neg₁ ▸ ChartData.mem₁ (negOne A)) h)
  have hz2 : orderOf (π z) = 2 := by
    refine orderOf_eq_prime ?_ hz1
    rw [← map_pow, pow_two, D.zz, map_one]
  have hinter : (π.comp ψ₁).range ⊓ (π.comp ψ₂).range = Subgroup.zpowers (π z) := by
    apply le_antisymm
    · rintro x ⟨⟨M, rfl⟩, ⟨N, hN⟩⟩
      have hMN : ψ₁ M = ψ₂ N := by
        have h1 : (ψ₁ M)⁻¹ * ψ₂ N ∈ R := by
          rw [← QuotientGroup.eq]
          exact hN.symm
        have h2 : (ψ₁ M)⁻¹ * ψ₂ N ∈ ChartData.Y₀ ψ₁ ψ₂ t :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ (ChartData.mem₁ M)) (ChartData.mem₂ N)
        have h3 := hY _ h1 h2
        exact (inv_mul_eq_one.1 h3)
      rcases D.inter M N hMN with h | h
      · simp only [MonoidHom.comp_apply, h, map_one]; exact Subgroup.one_mem _
      · simp only [MonoidHom.comp_apply, h]; exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨negOne A, by simp [D.neg₁]⟩, ⟨negOne B, by simp [D.neg₂]⟩⟩
  have hYC : ChartData.Y₀ ψ₁ ψ₂ t ≤ Subgroup.centralizer ({z} : Set X) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨M, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← D.neg₁, ← map_mul, ← map_mul]
      congr 1
      exact (negOne_central M).symm
    · rintro _ ⟨N, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← D.neg₁]
      exact (D.comm _ N).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have h1 := D.act₁ (negOne A)
      rw [slConj_negOne, D.neg₁] at h1
      calc t * z = (t * z * t⁻¹) * t := by group
        _ = z * t := by rw [h1]
  have hgen : oPrimeResidualOf 2 ((π.comp ψ₁).range ⊔ (π.comp ψ₂).range ⊔ Subgroup.zpowers (π t)) =
      oPrimeResidualOf 2 (Subgroup.centralizer ({π z} : Set (X ⧸ R))) := by
    have hK : (π.comp ψ₁).range ⊔ (π.comp ψ₂).range ⊔ Subgroup.zpowers (π t) =
        (ChartData.Y₀ ψ₁ ψ₂ t).map π := by
      simp only [ChartData.Y₀, Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_zpowers]
    rw [hK, oPrimeResidualOf_map_mk R, show π z = QuotientGroup.mk z from rfl,
      centralizer_mk_eq_map R hRodd D.zz, oPrimeResidualOf_map_mk R]
    congr 1
    refine oPrimeResidualOf_eq_of_two_elements hYC ?_
    intro b hb h2
    refine htwo b ?_ h2
    exact Subgroup.mem_centralizer_singleton_iff.1 hb
  have hinvcent := CFSG.GH74.GLS.IVK.Proofs2.ivk_4_7ab_G2_involutionCentralizer_of_diag
    (H := X ⧸ R) (z := π z) (K₁ := (π.comp ψ₁).range) (K₂ := (π.comp ψ₂).range)
    (F₁ := A) (F₂ := B) (t := π t) (by rw [← map_mul, D.tt, map_one])
    ⟨(MonoidHom.ofInjective hinj₁).symm, g₁, D.ns₁, actsAsConj_of_chart _ hinj₁ (π t) g₁ hact₁⟩
    ⟨(MonoidHom.ofInjective hinj₂).symm, g₂, D.ns₂, actsAsConj_of_chart _ hinj₂ (π t) g₂ hact₂⟩
    hcomm hinter hz2 hgen (p := 3) (f := m) Nat.prime_three (by norm_num)
    (by calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm) hA hB
  obtain ⟨p, fe, hp, hp2, hmodel⟩ := hlie
  obtain ⟨S', ⟨eS'⟩⟩ := hSiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSinj : ∀ x ∈ (S : Subgroup X), π x = 1 → x = 1 := by
    intro x hx h
    have hxR : x ∈ R := (QuotientGroup.eq_one_iff x).1 h
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have hodd := hRodd x hxR
    rw [hi] at hodd
    have hi0 : i = 0 := by
      by_contra hne
      exact absurd hodd (by
        rw [Nat.not_odd_iff_even]
        exact (Nat.even_pow.2 ⟨even_two, hne⟩))
    rw [hi0, pow_zero] at hi
    exact orderOf_eq_one_iff.1 hi
  let ι : ↥(S : Subgroup X) →* X ⧸ R := π.comp (S : Subgroup X).subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hSinj x.1 x.2 hx)
  have hrange : ι.range = (S : Subgroup X).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let Sb : Sylow 2 (X ⧸ R) := S.mapSurjective hπsurj
  have hSb : (Sb : Subgroup (X ⧸ R)) = (S : Subgroup X).map π := rfl
  let eS : ↥(S : Subgroup X) ≃* ↥(Sb : Subgroup (X ⧸ R)) :=
    (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr (hrange.trans hSb.symm))
  have heS : ∀ x : ↥(S : Subgroup X), ((eS x : ↥(Sb : Subgroup (X ⧸ R))) : X ⧸ R) = π x :=
    fun x => rfl
  have hcenter : Subgroup.zpowers (π z) =
      (Subgroup.center ↥(Sb : Subgroup (X ⧸ R))).map (Sb : Subgroup (X ⧸ R)).subtype := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      have hzk : z ^ k ∈ (S : Subgroup X) := Subgroup.zpow_mem _ hzS k
      refine ⟨eS ⟨z ^ k, hzk⟩, Subgroup.mem_center_iff.2 ?_, ?_⟩
      · intro w
        obtain ⟨w', rfl⟩ := eS.surjective w
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show (w' : X) * z ^ k = z ^ k * (w' : X)
        exact ((Commute.zpow_left (show Commute z (w' : X) from hzc _ w'.2) k).eq).symm
      · show π (z ^ k) = (π z) ^ k
        rw [map_zpow]
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨x, rfl⟩ := eS.surjective c
      have hxc : ∀ s ∈ (S : Subgroup X), (x : X) * s = s * x := by
        intro s hs
        have := (Subgroup.mem_center_iff.1 hc) (eS ⟨s, hs⟩)
        rw [← map_mul, ← map_mul] at this
        have := eS.injective this
        exact congrArg Subtype.val this.symm
      obtain ⟨k, hk⟩ := hZS x x.2 hxc
      refine ⟨k, ?_⟩
      show (π z) ^ k = π x
      rw [← hk, map_zpow]
  have hzS' : π z ∈ (Sb : Subgroup (X ⧸ R)) := ⟨z, hzS, rfl⟩
  have huS' : π u ∈ (Sb : Subgroup (X ⧸ R)) := ⟨u, hu, rfl⟩
  have hu1' : π u ≠ 1 := fun h => hu1 (hSinj u hu h)
  have hzu' : π z ≠ π u := by
    intro h
    have h1 : π (z⁻¹ * u) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hSinj _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzS) hu) h1
    exact hne (inv_mul_eq_one.1 h2).symm
  have hfour := isFourSubgroup_sup_zpowers (x := π z) (y := π u)
    (by rw [← map_mul, ← map_mul, hzu]) (by rw [← map_mul, D.zz, map_one])
    (by rw [← map_mul, hu2, map_one]) hz1 hu1' hzu'
  obtain ⟨a, haz, hau⟩ := hfuse
  have hc₁ : IsConj (π z) (π u) := isConj_iff.2 ⟨(π a)⁻¹, by
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← haz]; simp⟩
  have hc₂ : IsConj (π u) (π z * π u) := isConj_iff.2 ⟨(π a)⁻¹, by
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← hau]; simp⟩
  have hcl : ∀ x ∈ Subgroup.zpowers (π z) ⊔ Subgroup.zpowers (π u), orderOf x = 2 →
      IsConj (π z) x := by
    intro x hx hx2
    have hcomm' : ∀ a ∈ Subgroup.zpowers (π z), ∀ b ∈ Subgroup.zpowers (π u), a * b = b * a := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.zpow_zpow (show Commute (π z) (π u) by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hzu]) i j).eq
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm' hx
    have hzsq : π z * π z = 1 := by rw [← map_mul, D.zz, map_one]
    have husq : π u * π u = 1 := by rw [← map_mul, hu2, map_one]
    rcases mem_zpowers_of_sq hzsq ha₁ with h1 | h1 <;>
      rcases mem_zpowers_of_sq husq hb₁ with h2 | h2
    · rw [h1, h2, one_mul, orderOf_one] at hx2; omega
    · rw [h1, h2, one_mul]; exact hc₁
    · rw [h1, h2, mul_one]
    · rw [h1, h2]; exact hc₁.trans hc₂
  have hconj : ∀ u₁ ∈ Subgroup.zpowers (π z) ⊔ Subgroup.zpowers (π u),
      ∀ v ∈ Subgroup.zpowers (π z) ⊔ Subgroup.zpowers (π u), orderOf u₁ = 2 → orderOf v = 2 →
        IsConj u₁ v := fun u₁ h₁ v h₂ o₁ o₂ => (hcl u₁ h₁ o₁).symm.trans (hcl v h₂ o₂)
  unfold CFSG.GH74.GLS.IVK.Hyp94Loc
  refine ⟨Or.inl rfl, Nat.prime_three, by norm_num, p, fe, Sb,
    Subgroup.zpowers (π z) ⊔ Subgroup.zpowers (π u), hp, hp2, hmodel,
    ⟨S', ⟨eS.symm.trans eS'⟩⟩, hcenter, le_sup_left, ?_, hfour, hinvcent, hconj⟩
  exact sup_le (Subgroup.zpowers_le.2 hzS') (Subgroup.zpowers_le.2 huS')

end Quot

end CFSG.GH74.GLS.Stage4.Rest.F1Loc

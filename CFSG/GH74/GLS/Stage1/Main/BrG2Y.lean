module

public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift
public import CFSG.GH74.GLS.Stage1.Main.BrFusedAbs
public import CFSG.GH74.GLS.Stage1.Main.BrG2Ctx
public import CFSG.GH74.GLS.Stage1.Main.BrG2Shape
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section YLevel

variable {Y : Type} [Group Y] [Finite Y]

theorem y_mem_sup_of_commute {A B : Subgroup Y} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have : x ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hx
  rw [h] at this
  obtain ⟨a, ha, b, hb, hab⟩ := this
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem y_center_cases {K₁ K₂ : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) {ζ : Y} (hζ₁ : ζ ∈ K₁) (hζ₂ : ζ ∈ K₂)
    (hζo : orderOf ζ = 2) {γ : Y} (hγ : γ ∈ K₁ ⊔ K₂) (hcen : ∀ l ∈ K₁ ⊔ K₂, l * γ = γ * l) :
    γ = 1 ∨ γ = ζ := by
  let ε₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    e₁.trans (specialLinearGroupEquivStatedSL 2 F₁).symm
  let ε₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂ :=
    e₂.trans (specialLinearGroupEquivStatedSL 2 F₂).symm
  obtain ⟨x, hx, y, hy, rfl⟩ := y_mem_sup_of_commute hc hγ
  have hx1 : (⟨x, hx⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * x = x * g
    have h1 := hcen g (Subgroup.mem_sup_left g.2)
    have h2 := hc g g.2 y hy
    have h3 : (g : Y) * x * y = x * g * y := by
      calc (g : Y) * x * y = (g : Y) * (x * y) := by rw [mul_assoc]
        _ = (x * y) * g := h1
        _ = x * (y * g) := by rw [mul_assoc]
        _ = x * (g * y) := by rw [← h2]
        _ = x * g * y := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hy1 : (⟨y, hy⟩ : ↥K₂) ∈ Subgroup.center ↥K₂ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * y = y * g
    have h1 := hcen g (Subgroup.mem_sup_right g.2)
    have h2 := hc x hx g g.2
    have h3 : x * ((g : Y) * y) = x * (y * g) := by
      calc x * ((g : Y) * y) = x * g * y := by rw [mul_assoc]
        _ = g * x * y := by rw [← h2]
        _ = g * (x * y) := by rw [mul_assoc]
        _ = (x * y) * g := h1
        _ = x * (y * g) := by rw [mul_assoc]
    exact mul_left_cancel h3
  have ht₁ : orderOf (⟨ζ, hζ₁⟩ : ↥K₁) = 2 := by rw [orderOf_mk]; exact hζo
  have ht₂ : orderOf (⟨ζ, hζ₂⟩ : ↥K₂) = 2 := by rw [orderOf_mk]; exact hζo
  have hζsq : ζ * ζ = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζo, pow_two] at this
  rcases kabs_center_cases hodd₁ ε₁ ht₁ hx1 with h1 | h1 <;>
  rcases kabs_center_cases hodd₂ ε₂ ht₂ hy1 with h2 | h2
  · left
    have hx' : x = 1 := congrArg Subtype.val h1
    have hy' : y = 1 := congrArg Subtype.val h2
    rw [hx', hy', one_mul]
  · right
    have hx' : x = 1 := congrArg Subtype.val h1
    have hy' : y = ζ := congrArg Subtype.val h2
    rw [hx', hy', one_mul]
  · right
    have hx' : x = ζ := congrArg Subtype.val h1
    have hy' : y = 1 := congrArg Subtype.val h2
    rw [hx', hy', mul_one]
  · left
    have hx' : x = ζ := congrArg Subtype.val h1
    have hy' : y = ζ := congrArg Subtype.val h2
    rw [hx', hy', hζsq]


theorem y_exists_zeta {K₁ K₂ : Subgroup Y} (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2) :
    ∃ ζ : Y, ζ ∈ K₁ ∧ ζ ∈ K₂ ∧ orderOf ζ = 2 := by
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(K₁ ⊓ K₂)) 2 (by rw [hinf])
  refine ⟨(t₀ : Y), t₀.2.1, t₀.2.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact ht₀

theorem y_factorization_K {K₁ K₂ : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] {n : ℕ} (hv₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1)
    (hv₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1)
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2) :
    (Nat.card ↥(K₁ ⊔ K₂)).factorization 2 = 2 * n + 1 := by
  have hK1 : Nat.card ↥K₁ = Nat.card ↥(StatedSL 2 F₁) := Nat.card_congr e₁.toEquiv
  have hK2 : Nat.card ↥K₂ = Nat.card ↥(StatedSL 2 F₂) := Nat.card_congr e₂.toEquiv
  have hmul := card_sup_mul_two hc hinf
  have h : (Nat.card ↥(K₁ ⊔ K₂) * 2).factorization 2 =
      (Nat.card ↥K₁ * Nat.card ↥K₂).factorization 2 := by rw [hmul]
  rw [Nat.factorization_mul Nat.card_pos.ne' two_ne_zero,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', hK1, hK2] at h
  simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, hv₁, hv₂] at h
  omega

omit [Finite Y] in
theorem y_card_le_two {P : Subgroup Y} {ζ : Y} (h : ∀ x ∈ P, x = 1 ∨ x = ζ) : Nat.card ↥P ≤ 2 := by
  classical
  have hinj : Function.Injective (fun x : ↥P => if (x : Y) = 1 then (0 : Fin 2) else 1) := by
    intro x x' hxx
    by_cases hx : (x : Y) = 1 <;> by_cases hx' : (x' : Y) = 1
    · exact Subtype.ext (hx.trans hx'.symm)
    · simp [hx, hx'] at hxx
    · simp [hx, hx'] at hxx
    · rcases h x x.2 with h1 | h1
      · exact absurd h1 hx
      rcases h x' x'.2 with h2 | h2
      · exact absurd h2 hx'
      exact Subtype.ext (h1.trans h2.symm)
  calc Nat.card ↥P ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem g2_cent_inf {K₁ K₂ T : Subgroup Y} {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
    [Finite F₂] {n : ℕ} (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    (hv₁ : (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = n + 1)
    (hv₂ : (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = n + 1)
    (e₁ : ↥K₁ ≃* StatedSL 2 F₁) (e₂ : ↥K₂ ≃* StatedSL 2 F₂)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : Nat.card ↥(K₁ ⊓ K₂) = 2)
    (hT2 : IsPGroup 2 ↥T) (hTcard : Nat.card ↥T = 2 ^ (2 * n + 2))
    (hidx : ((K₁ ⊔ K₂).subgroupOf (oPrimeResidual 2 Y)).index = 2)
    (hZ : ∀ P : Subgroup Y, P ≤ T → (∀ x ∈ P, ∀ s ∈ T, s * x = x * s) → Nat.card ↥P ≤ 2) :
    ∃ ζ : Y, ζ ∈ K₁ ∧ ζ ∈ K₂ ∧ orderOf ζ = 2 ∧ ζ ∈ T ∧
      ∀ γ ∈ T, (∀ l ∈ K₁ ⊔ K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRcard, hrel⟩ := g2_sylow_inf hv₁ hv₂ e₁ e₂ hc hinf hT2 hTcard hidx
  obtain ⟨ζ, hζ₁, hζ₂, hζo⟩ := y_exists_zeta hinf
  have hζsq : ζ * ζ = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζo, pow_two] at this
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    omega
  have hKfac := y_factorization_K hv₁ hv₂ e₁ e₂ hc hinf
  have hRK : T ⊓ (K₁ ⊔ K₂) ≤ K₁ ⊔ K₂ := inf_le_right
  have hSyl : IsSylowOf 2 (T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    isSylowOf_of_card hRK (by rw [hRcard, hKfac])
  have hζcen : ∀ l ∈ K₁ ⊔ K₂, l * ζ = ζ * l := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute hc hl
    have h1 := hc a ha ζ hζ₂
    have h2 := hc ζ hζ₁ b hb
    calc a * b * ζ = a * (b * ζ) := by rw [mul_assoc]
      _ = a * (ζ * b) := by rw [← h2.symm]
      _ = (a * ζ) * b := by rw [mul_assoc]
      _ = (ζ * a) * b := by rw [h1]
      _ = ζ * (a * b) := by rw [mul_assoc]
  have hζR : ζ ∈ T ⊓ (K₁ ⊔ K₂) := by
    obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
    have hnormal : ((zpowers ζ).subgroupOf (K₁ ⊔ K₂)).Normal := by
      constructor
      intro x hx g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (x : Y) ∈ zpowers ζ from hx)
      have hxk : (x : Y) = ζ ^ k := hk.symm
      have : (g : Y) * x * (g : Y)⁻¹ = x := by
        rw [hxk]
        have hg := hζcen g g.2
        have hgk : (g : Y) * ζ ^ k = ζ ^ k * g := (Commute.zpow_right (show Commute (g : Y) ζ from hg) k).eq
        rw [hgk]
        group
      show (g : Y) * x * (g : Y)⁻¹ ∈ zpowers ζ
      rw [this, hxk]
      exact Subgroup.zpow_mem _ (mem_zpowers ζ) k
    have hpg : IsPGroup 2 ↥((zpowers ζ).subgroupOf (K₁ ⊔ K₂)) := by
      have hzp : IsPGroup 2 ↥(zpowers ζ) := by
        apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, hζo, pow_one]
      exact hzp.of_equiv (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 (Subgroup.mem_sup_left hζ₁))).symm
    have hle := hpg.le_sylow_of_normal Q
    have hζK : ζ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left hζ₁
    have hmem : (⟨ζ, hζK⟩ : ↥(K₁ ⊔ K₂)) ∈ (Q : Subgroup ↥(K₁ ⊔ K₂)) :=
      hle (show (⟨ζ, hζK⟩ : ↥(K₁ ⊔ K₂)) ∈ (zpowers ζ).subgroupOf (K₁ ⊔ K₂) from mem_zpowers ζ)
    rw [hQ] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hζT : ζ ∈ T := hζR.1
  refine ⟨ζ, hζ₁, hζ₂, hζo, hζT, ?_⟩
  intro γ hγT hγc
  by_contra hne
  push Not at hne
  set Q : Subgroup Y := Subgroup.closure ({ζ, γ} : Set Y) with hQdef
  have hQT : Q ≤ T := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hζT
    · exact hγT
  have hγζ : γ * ζ = ζ * γ := by
    have := hγc ζ (Subgroup.mem_sup_left hζ₁)
    exact this.symm
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    have hcomm : Commute ζ γ := hγζ.symm
    have : IsMulCommutative ↥(Subgroup.closure ({ζ, γ} : Set Y)) := by
      apply Subgroup.isMulCommutative_closure
      intro a ha b hb _
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Commute.refl _
      · exact hcomm
      · exact hcomm.symm
      · exact Commute.refl _
    intro x hx y hy
    have := this.is_comm.comm (⟨x, hx⟩ : ↥Q) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hgen : ∀ x ∈ Q, ∀ r ∈ K₁ ⊔ K₂, x * r = r * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · intro r hr
        exact (hζcen r hr).symm
      · intro r hr
        exact (hγc r hr).symm
    | one => intro r hr; simp
    | mul x y _ _ hx hy =>
      intro r hr
      rw [mul_assoc, hy r hr, ← mul_assoc, hx r hr, mul_assoc]
    | inv x _ hx =>
      intro r hr
      have := hx r hr
      calc x⁻¹ * r = x⁻¹ * (r * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * r) * x⁻¹ := by rw [this]
        _ = r * x⁻¹ := by group
  have hQR : ∀ x ∈ Q, ∀ r ∈ T ⊓ (K₁ ⊔ K₂), x * r = r * x := fun x hx r hr => hgen x hx r hr.2
  have hQRinf : Nat.card ↥(Q ⊓ (T ⊓ (K₁ ⊔ K₂))) ≤ 2 := by
    have hsub : ∀ x ∈ Q ⊓ (T ⊓ (K₁ ⊔ K₂)), x = 1 ∨ x = ζ := by
      intro x hx
      refine y_center_cases hodd₁ hodd₂ e₁ e₂ hc hζ₁ hζ₂ hζo hx.2.2 ?_
      intro l hl
      exact (hgen x hx.1 l hl).symm
    exact y_card_le_two hsub
  have hQp : IsPGroup 2 ↥Q :=
    (hT2.to_subgroup (Q.subgroupOf T)).of_equiv (Subgroup.subgroupOfEquivOfLe hQT)
  have hQ4 : 4 ≤ Nat.card ↥Q := by
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hQp
    have hζQ : ζ ∈ Q := Subgroup.subset_closure (Or.inl rfl)
    have hγQ : γ ∈ Q := Subgroup.subset_closure (Or.inr rfl)
    have hne2 : Nat.card ↥Q ≠ 2 := by
      intro h2
      have hle : zpowers ζ ≤ Q := zpowers_le.2 hζQ
      have hcz : Nat.card ↥(zpowers ζ) = 2 := by rw [Nat.card_zpowers, hζo]
      have heq : zpowers ζ = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, h2])
      have hγz : γ ∈ zpowers ζ := heq ▸ hγQ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hγz
      have hk2 : ζ ^ k = 1 ∨ ζ ^ k = ζ := ShapeModel.zpow_eq_one_or_self hζsq k
      rcases hk2 with h | h
      · exact hne.1 (by rw [← hk, h])
      · exact hne.2 (by rw [← hk, h])
    have hpos : 0 < Nat.card ↥Q := Nat.card_pos
    have : j ≠ 0 := by
      rintro rfl
      have : Nat.card ↥Q = 1 := by simpa using hj
      have hζQ' : (⟨ζ, hζQ⟩ : ↥Q) = ⟨γ, hγQ⟩ ∨ True := Or.inr trivial
      have : Subsingleton ↥Q := (Nat.card_eq_one_iff_unique.1 this).1
      exact hζ1 (congrArg Subtype.val (Subsingleton.elim (⟨ζ, hζQ⟩ : ↥Q) 1))
    have : j ≠ 1 := by
      rintro rfl
      exact hne2 (by simpa using hj)
    have hj2 : 2 ≤ j := by omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
      _ = Nat.card ↥Q := hj.symm
  have hcardsup := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Q (T ⊓ (K₁ ⊔ K₂)) hQR).1
  have hsupT : Q ⊔ (T ⊓ (K₁ ⊔ K₂)) = T := by
    have hle : Q ⊔ (T ⊓ (K₁ ⊔ K₂)) ≤ T := sup_le hQT inf_le_left
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hTcard]
    have h1 : Nat.card ↥(Q ⊔ (T ⊓ (K₁ ⊔ K₂))) * 2 ≥ 4 * 2 ^ (2 * n + 1) := by
      have h2 : Nat.card ↥(Q ⊔ (T ⊓ (K₁ ⊔ K₂))) * Nat.card ↥(Q ⊓ (T ⊓ (K₁ ⊔ K₂))) =
          Nat.card ↥Q * 2 ^ (2 * n + 1) := by rw [hcardsup, hRcard]
      calc Nat.card ↥(Q ⊔ (T ⊓ (K₁ ⊔ K₂))) * 2
          ≥ Nat.card ↥(Q ⊔ (T ⊓ (K₁ ⊔ K₂))) * Nat.card ↥(Q ⊓ (T ⊓ (K₁ ⊔ K₂))) :=
            Nat.mul_le_mul_left _ hQRinf
        _ = Nat.card ↥Q * 2 ^ (2 * n + 1) := h2
        _ ≥ 4 * 2 ^ (2 * n + 1) := Nat.mul_le_mul_right _ hQ4
    have h3 : 2 ^ (2 * n + 2) = 2 * 2 ^ (2 * n + 1) := by ring
    omega
  have hQcen : ∀ x ∈ Q, ∀ s ∈ T, s * x = x * s := by
    intro x hx s hs
    rw [← hsupT] at hs
    obtain ⟨q, hq, r, hr, rfl⟩ := y_mem_sup_of_commute hQR hs
    calc q * r * x = q * (r * x) := by rw [mul_assoc]
      _ = q * (x * r) := by rw [← hQR x hx r hr]
      _ = (q * x) * r := by rw [mul_assoc]
      _ = (x * q) * r := by rw [hQcomm q hq x hx]
      _ = x * (q * r) := by rw [mul_assoc]
  have := hZ Q hQT hQcen
  omega

end YLevel


section YCtx

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.hZ (hcen : Cen2 G z S) :
    ∀ P : Subgroup (CentralizerBar z), P ≤ barOf z S →
      (∀ x ∈ P, ∀ s ∈ barOf z S, s * x = x * s) → Nat.card ↥P ≤ 2 := by
  have hSC : S ≤ Cen z := hcen.sylow.le
  have hSN : S ⊓ OddCore z = ⊥ := cen2_S_inf_oddCore hcen
  set β : ↥S ≃* ↥(barOf z S) := barEquiv z S hSC hSN with hβdef
  obtain ⟨ζ', hζ'S, hζ'⟩ := ShapeConds.center_le C.shape C.two_le
  intro P hPT hPcen
  set ι : ↥(barOf z S) ≃* ↥C.S' := β.symm.trans C.eS with hι
  apply y_card_le_two (ζ := ((ι.symm ⟨ζ', hζ'S⟩ : ↥(barOf z S)) : CentralizerBar z))
  intro x hx
  have hxT : x ∈ barOf z S := hPT hx
  set u : ↥C.S' := ι ⟨x, hxT⟩ with hu
  have hucen : ∀ s ∈ C.S', s * (u : C.Gs) = (u : C.Gs) * s := by
    intro s hs
    obtain ⟨t, ht⟩ := ι.surjective ⟨s, hs⟩
    have h1 := hPcen x hx (t : CentralizerBar z) t.2
    have h2 : t * (⟨x, hxT⟩ : ↥(barOf z S)) = ⟨x, hxT⟩ * t := Subtype.ext h1
    have h3 := congrArg ι h2
    rw [map_mul, map_mul, ht] at h3
    exact congrArg Subtype.val h3
  rcases hζ' u u.2 hucen with h | h
  · left
    have : ι ⟨x, hxT⟩ = 1 := Subtype.ext h
    have := ι.injective (this.trans (map_one ι).symm)
    exact congrArg Subtype.val this
  · right
    have h5 : ι ⟨x, hxT⟩ = ⟨ζ', hζ'S⟩ := Subtype.ext h
    have h4 : (⟨x, hxT⟩ : ↥(barOf z S)) = ι.symm ⟨ζ', hζ'S⟩ := ι.eq_symm_apply.2 h5
    exact congrArg Subtype.val h4


theorem G2Ctx.exists_zeta (hcen : Cen2 G z S) :
    ∃ ζ : CentralizerBar z, ζ ∈ C.K₁ ∧ ζ ∈ C.K₂ ∧ orderOf ζ = 2 ∧ ζ ∈ barOf z S ∧
      ∀ γ ∈ barOf z S, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ :=
  g2_cent_inf C.odd₁ C.odd₂ C.v₁ C.v₂ C.e₁ C.e₂ C.comm C.inf_card (C.sylow_bar hcen).1
    (C.sylow_bar hcen).2 C.idx (C.hZ hcen)

theorem G2Ctx.normal_K (hcen : Cen2 G z S) : (C.K₁ ⊔ C.K₂).Normal := by
  rw [← C.oPrime_eq hcen]
  exact Stage1.Thm6.Prod.oPrimePResidual_normal Nat.prime_two _

theorem G2Ctx.centralizer_K (hcen : Cen2 G z S) {ζ : CentralizerBar z} (hζ₁ : ζ ∈ C.K₁)
    (hζ₂ : ζ ∈ C.K₂) (hζo : orderOf ζ = 2)
    (hT : ∀ γ ∈ barOf z S, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ) :
    ∀ γ : CentralizerBar z, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ := by
  have hO : pPrimeCore 2 (CentralizerBar z) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _
  have hLn := C.normal_K hcen
  have hSyl : IsSylowOf 2 (barOf z S) ⊤ := isSylowOf_barOf hcen.sylow
  have hζK : ζ ∈ C.K₁ ⊔ C.K₂ := Subgroup.mem_sup_left hζ₁
  have hζsq : ζ * ζ = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζo, pow_two] at this
  intro γ hγ
  have hγK : γ ∈ C.K₁ ⊔ C.K₂ :=
    centralizer_le_of_sylow_inf hO hLn hSyl hζK hζsq hT γ hγ
  exact y_center_cases C.odd₁ C.odd₂ C.e₁ C.e₂ C.comm hζ₁ hζ₂ hζo hγK hγ


omit [Finite G] in
theorem y_normal_zpowers_of_central {H : Type} [Group H] {a : H} (h : ∀ g : H, g * a = a * g) :
    (zpowers a).Normal := by
  constructor
  intro x hx g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have : g * a ^ k * g⁻¹ = a ^ k := by
    have hg : g * a ^ k = a ^ k * g := (Commute.zpow_right (show Commute g a from h g) k).eq
    rw [hg]; group
  rw [this]
  exact Subgroup.zpow_mem _ (mem_zpowers a) k

theorem cen2_z_mem (hcen : Cen2 G z S) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hcen.sylow.exists_sylow_eq_subgroupOf
  set zz : ↥(Cen z) := ⟨z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with hzz
  have hzo : orderOf zz = 2 := by rw [hzz, orderOf_mk]; exact hcen.central.1
  have hcentral : ∀ g : ↥(Cen z), g * zz = zz * g := by
    intro g
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact this
  have hnormal : (zpowers zz).Normal := y_normal_zpowers_of_central hcentral
  have hp : IsPGroup 2 ↥(zpowers zz) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hzo, pow_one]
  have hle := hp.le_sylow_of_normal Q
  have hmem : zz ∈ (Q : Subgroup ↥(Cen z)) := hle (mem_zpowers zz)
  rw [hQ] at hmem
  exact hmem

omit [Finite G] in
theorem zbar_central (z : G) (y : CentralizerBar z) : y * zBar z = zBar z * y := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
  show (QuotientGroup.mk c) * (QuotientGroup.mk (zElt z)) = (QuotientGroup.mk (zElt z)) * (QuotientGroup.mk c)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.1 c.2)

include C in
theorem G2Ctx.zbar_eq (hcen : Cen2 G z S) {ζ : CentralizerBar z}
    (hT : ∀ γ ∈ barOf z S, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ) :
    zBar z = ζ := by
  have hzS : z ∈ S := cen2_z_mem hcen
  have hSC : S ≤ Cen z := hcen.sylow.le
  have hzT : zBar z ∈ barOf z S := ⟨zElt z, hzS, rfl⟩
  rcases hT (zBar z) hzT (fun l _ => (zbar_central z l)) with h | h
  · exfalso
    have hSN : S ⊓ OddCore z = ⊥ := cen2_S_inf_oddCore hcen
    set β : ↥S ≃* ↥(barOf z S) := barEquiv z S hSC hSN with hβdef
    have h1 : β ⟨z, hzS⟩ = 1 := Subtype.ext (by rw [hβdef, barEquiv_apply]; exact h)
    have h2 : (⟨z, hzS⟩ : ↥S) = 1 := β.injective (h1.trans (map_one β).symm)
    have h3 : z = 1 := congrArg Subtype.val h2
    have := hcen.central.1
    rw [h3, orderOf_one] at this
    omega
  · exact h


include C in
theorem G2Ctx.quasi₁ : IsQuasisimple ↥C.K₁ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (C.e₁.trans (specialLinearGroupEquivStatedSL 2 C.F₁).symm).symm
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by have := C.five; omega))

include C in
theorem G2Ctx.quasi₂ (h5 : 5 ≤ Nat.card C.F₂) : IsQuasisimple ↥C.K₂ :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (C.e₂.trans (specialLinearGroupEquivStatedSL 2 C.F₂).symm).symm
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by omega))

theorem G2Ctx.sup_top (hcen : Cen2 G z S) :
    (C.K₁ ⊔ C.K₂).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) ⊔
      (barOf z S).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) = ⊤ := by
  obtain ⟨h2, hcard⟩ := C.sylow_bar hcen
  obtain ⟨-, hrel⟩ := C.sylow_inf hcen
  have hTΓ : barOf z S ≤ oPrimeResidual 2 (CentralizerBar z) := pgroup_le_oPrimeResidual h2
  have hTnot : ¬ barOf z S ≤ C.K₁ ⊔ C.K₂ := by
    intro hle
    have : (C.K₁ ⊔ C.K₂).relIndex (barOf z S) = 1 := Subgroup.relIndex_eq_one.2 hle
    omega
  have hTnot' : ¬ (barOf z S).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) ≤
      (C.K₁ ⊔ C.K₂).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) := by
    intro hle
    apply hTnot
    intro x hx
    exact hle (show (⟨x, hTΓ hx⟩ : ↥(oPrimeResidual 2 (CentralizerBar z))) ∈
      (barOf z S).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) from hx)
  set N := (C.K₁ ⊔ C.K₂).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) with hNdef
  set T' := (barOf z S).subgroupOf (oPrimeResidual 2 (CentralizerBar z)) with hT'def
  have hdvd : (N ⊔ T').index ∣ N.index := Subgroup.index_dvd_of_le le_sup_left
  rw [C.idx] at hdvd
  have hne : (N ⊔ T').index ≠ 2 := by
    intro h2'
    have h3 := Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T')
    rw [h2', C.idx] at h3
    have h4 : N.relIndex (N ⊔ T') = 1 := by omega
    exact hTnot' ((le_sup_right : T' ≤ N ⊔ T').trans (Subgroup.relIndex_eq_one.1 h4))
  have h1 : (N ⊔ T').index = 1 := by
    have := (Nat.dvd_prime Nat.prime_two).1 hdvd
    tauto
  exact Subgroup.index_eq_one.1 h1

include C in
theorem G2Ctx.comps (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂) :
    {K : Subgroup (CentralizerBar z) | IsComponent K} = {C.K₁, C.K₂} := by
  have hΓn : (oPrimeResidual 2 (CentralizerBar z)).Normal :=
    Stage1.Thm6.Prod.oPrimeResidual_normal 2 _
  have hK₁Γ : C.K₁ ≤ oPrimeResidual 2 (CentralizerBar z) := le_sup_left.trans C.le_Γ
  have hK₂Γ : C.K₂ ≤ oPrimeResidual 2 (CentralizerBar z) := le_sup_right.trans C.le_Γ
  have hq₁ := C.quasi₁
  have hq₂ := C.quasi₂ h5
  have hnormal : (C.K₁ ⊔ C.K₂).Normal := C.normal_K hcen
  obtain ⟨h2, -⟩ := C.sylow_bar hcen
  have hTΓ : barOf z S ≤ oPrimeResidual 2 (CentralizerBar z) := pgroup_le_oPrimeResidual h2
  set Γ := oPrimeResidual 2 (CentralizerBar z) with hΓ
  have hE₁q : IsQuasisimple ↥(C.K₁.subgroupOf Γ) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hK₁Γ)).2 hq₁
  have hE₂q : IsQuasisimple ↥(C.K₂.subgroupOf Γ) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hK₂Γ)).2 hq₂
  have hcomm : ∀ a ∈ C.K₁.subgroupOf Γ, ∀ b ∈ C.K₂.subgroupOf Γ, a * b = b * a :=
    fun a ha b hb => Subtype.ext (C.comm _ ha _ hb)
  have hN : (C.K₁.subgroupOf Γ ⊔ C.K₂.subgroupOf Γ).Normal := by
    rw [← Subgroup.subgroupOf_sup hK₁Γ hK₂Γ]
    exact hnormal.subgroupOf _
  have hT' : IsPGroup 2 ↥((barOf z S).subgroupOf Γ) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe hTΓ).symm
  have hY : C.K₁.subgroupOf Γ ⊔ C.K₂.subgroupOf Γ ⊔ (barOf z S).subgroupOf Γ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK₁Γ hK₂Γ]
    exact C.sup_top hcen
  have hc := comps_of_sup_pgroup hE₁q hE₂q hcomm hN hT' hY
  have hmap : ∀ K : Subgroup (CentralizerBar z), K ≤ Γ → IsComponent (K.subgroupOf Γ) →
      IsComponent K := by
    intro K hKΓ hK
    have := isComponent_map_subtype_of_normal hΓn hK
    rwa [Subgroup.map_subgroupOf_eq_of_le hKΓ] at this
  ext K
  constructor
  · intro hK
    have hKΓ : K ≤ Γ := (le_sSup hK).trans (LayerFD.layer_le_oPrimeResidual _)
    have hK' : IsComponent (K.subgroupOf Γ) :=
      ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hKΓ)).2 hK.1, hK.2.subgroupOf⟩
    have hmem : K.subgroupOf Γ ∈ ({C.K₁.subgroupOf Γ, C.K₂.subgroupOf Γ} : Set (Subgroup ↥Γ)) := by
      rw [← hc]; exact hK'
    rcases hmem with h | h
    · left
      rw [← Subgroup.map_subgroupOf_eq_of_le hKΓ, h, Subgroup.map_subgroupOf_eq_of_le hK₁Γ]
    · right
      rw [← Subgroup.map_subgroupOf_eq_of_le hKΓ, Set.mem_singleton_iff.1 h,
        Subgroup.map_subgroupOf_eq_of_le hK₂Γ]
      exact Set.mem_singleton _
  · rintro (rfl | rfl)
    · exact hmap _ hK₁Γ (by
        have : C.K₁.subgroupOf Γ ∈ {K : Subgroup ↥Γ | IsComponent K} := by rw [hc]; exact Or.inl rfl
        exact this)
    · exact hmap _ hK₂Γ (by
        have : C.K₂.subgroupOf Γ ∈ {K : Subgroup ↥Γ | IsComponent K} := by rw [hc]; exact Or.inr rfl
        exact this)


omit [Finite G] in
theorem barOf_zpowers_self (z : G) : barOf z (zpowers z) = zpowers (zBar z) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (c : G) ∈ zpowers z from hc)
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have : c = (zElt z) ^ k := by
      apply Subtype.ext
      rw [← hk]
      simp [zElt]
    rw [this, map_zpow]
    rfl
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨(zElt z) ^ k, ?_, ?_⟩
    · show (((zElt z) ^ k : ↥(Cen z)) : G) ∈ zpowers z
      simp [zElt]
    · rw [map_zpow]; rfl

include C in
theorem G2Ctx.fitting_le (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂) {ζ : CentralizerBar z}
    (hcen' : ∀ γ : CentralizerBar z, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ) :
    ∀ f ∈ fittingSubgroup (CentralizerBar z), f = 1 ∨ f = ζ := by
  have hlayer : layer (CentralizerBar z) = C.K₁ ⊔ C.K₂ := by
    show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
    rw [C.comps hcen h5, sSup_pair]
  intro f hf
  apply hcen'
  intro l hl
  have hm : ⁅f, l⁆ ∈ ⁅fittingSubgroup (CentralizerBar z), layer (CentralizerBar z)⁆ :=
    Subgroup.commutator_mem_commutator hf (by rw [hlayer]; exact hl)
  rw [CFSG.LocalCores.fitting_layer_commute] at hm
  have h1 : ⁅f, l⁆ = 1 := by simpa using hm
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

include C in
theorem G2Ctx.generalizedFitting_eq (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂)
    {ζ : CentralizerBar z} (hζ₁ : ζ ∈ C.K₁)
    (hcen' : ∀ γ : CentralizerBar z, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ) :
    generalizedFitting (CentralizerBar z) = LBar z := by
  have hlayer : layer (CentralizerBar z) = C.K₁ ⊔ C.K₂ := by
    show sSup {K : Subgroup (CentralizerBar z) | IsComponent K} = _
    rw [C.comps hcen h5, sSup_pair]
  show fittingSubgroup (CentralizerBar z) ⊔ layer (CentralizerBar z) = LBar z
  have hF : fittingSubgroup (CentralizerBar z) ≤ C.K₁ ⊔ C.K₂ := by
    intro f hf
    rcases C.fitting_le hcen h5 hcen' f hf with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_sup_left hζ₁
  rw [hlayer, C.LBar_eq hcen]
  exact sup_eq_right.2 hF


include C in
theorem G2Ctx.WBar_eq_zpowers (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂)
    {ζ : CentralizerBar z} (hζ₁ : ζ ∈ C.K₁) (hζo : orderOf ζ = 2)
    (hcen' : ∀ γ : CentralizerBar z, (∀ l ∈ C.K₁ ⊔ C.K₂, l * γ = γ * l) → γ = 1 ∨ γ = ζ)
    (hzeta : zBar z = ζ) : WBar z = barOf z (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [barOf_zpowers_self, hzeta]
  apply le_antisymm
  · intro w hw
    have hWn : (WBar z).Normal := Stage2.Final.L26.WBar_normal z
    have hWp : IsPGroup 2 ↥(WBar z) := by
      rintro ⟨w, hw⟩
      obtain ⟨a, ha⟩ := Stage2.Final.L26.WBar_two_pow z w hw
      exact ⟨a, Subtype.ext ha⟩
    have hle : WBar z ≤ pCore 2 (CentralizerBar z) := le_sSup ⟨hWn, hWp⟩
    have hf : w ∈ fittingSubgroup (CentralizerBar z) := (pCore_le_fitting (CentralizerBar z) 2) (hle hw)
    rcases C.fitting_le hcen h5 hcen' w hf with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact mem_zpowers ζ
  · rw [Subgroup.zpowers_le, Stage1.Thm6.Prod.WBar_eq z]
    have hN : C.K₁ ≤ oResidual 2 (CentralizerBar z) := hasSL2_le_oResidual C.odd₁ C.e₁
    have hζN : ζ ∈ oResidual 2 (CentralizerBar z) := hN hζ₁
    refine Subgroup.mem_map.2 ⟨⟨ζ, hζN⟩, ?_, rfl⟩
    have hcentral : ∀ g : ↥(oResidual 2 (CentralizerBar z)), g * (⟨ζ, hζN⟩ : ↥(oResidual 2 (CentralizerBar z))) =
        ⟨ζ, hζN⟩ * g := by
      intro g
      apply Subtype.ext
      show (g : CentralizerBar z) * ζ = ζ * g
      rw [← hzeta]
      exact zbar_central z g
    have hnormal : (zpowers (⟨ζ, hζN⟩ : ↥(oResidual 2 (CentralizerBar z)))).Normal :=
      y_normal_zpowers_of_central hcentral
    have hp : IsPGroup 2 ↥(zpowers (⟨ζ, hζN⟩ : ↥(oResidual 2 (CentralizerBar z)))) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, orderOf_mk, hζo, pow_one]
    have hle : zpowers (⟨ζ, hζN⟩ : ↥(oResidual 2 (CentralizerBar z))) ≤
        pCore 2 ↥(oResidual 2 (CentralizerBar z)) := le_sSup ⟨hnormal, hp⟩
    exact hle (mem_zpowers _)

end YCtx

end CFSG.GH74.GLS.Stage1.Main

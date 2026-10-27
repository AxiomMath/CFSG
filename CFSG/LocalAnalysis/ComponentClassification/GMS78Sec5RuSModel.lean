module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSModelD8

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS RuSModel

namespace RuSModel

theorem adMat_sixteen : ∀ j < 8, maskApply (adMat (dCode (fin8Of j))) 16 = sBasis.getD j 0 := by
  intro j hj
  rw [adMat_dCode]
  interval_cases j <;> decide

theorem dCode_injective : ∀ d e : Fin 8, dCode d = dCode e → d = e := by decide

theorem dPart_zero : ∀ d : Fin 8, dPart d 0 = (0, 0) := by decide

theorem gam_zero_right (c : ℕ) : gam c 0 = 0 := by
  have h : ∀ n, sMaskN 0 n = 0 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [sMaskN, ih]
  have h2 : ∀ n, gamN c 0 n = 0 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [gamN, ih, h, RuQCode.bC_zero_right]
  exact h2 8

theorem dOvf_zero_right : ∀ d : Fin 8, dOvf d 0 = false := by decide

theorem dMul_zero_right : ∀ d : Fin 8, dMul d 0 = d := by decide

end RuSModel

namespace Sec3.SzR

variable {G : Type} [Group G]

structure SModel (L T R : Subgroup G) (μ : G → ℕ) (ν : G → Fin 8) (ε : Bool)
    (Φ : ℕ × Fin 8 × Fin 8 → G) : Prop where
  mul : ∀ p q, Φ (sMul ε p q) = Φ p * Φ q
  inj : ∀ p q, p.1 < 256 → q.1 < 256 → Φ p = Φ q → p = q
  mem : ∀ p, Φ p ∈ normalizer (R : Set G)
  code : ∀ p, ∀ b ∈ gmsA L T, ν (Φ p * b * (Φ p)⁻¹) = linApply (dCode p.2.2) (ν b)
  mem_R : ∀ c t, Φ (c, t, 0) ∈ R
  μ_eq : ∀ c t, μ (Φ (c, t, 0)) = sMask c
  mem_A : ∀ t, Φ (0, t, 0) ∈ gmsA L T
  ν_eq : ∀ t, ν (Φ (0, t, 0)) = t
  surj : ∀ g ∈ normalizer (R : Set G), ∀ d : Fin 8,
    (∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply (dCode d) (ν b)) →
      ∃ p : ℕ × Fin 8 × Fin 8, p.1 < 256 ∧ p.2.2 = d ∧ Φ p = g

end Sec3.SzR

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

theorem exists_sModel [Finite G]
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) :
    ∃ (ε : Bool) (Φ : ℕ × Fin 8 × Fin 8 → G), SModel L T R μ ν ε Φ := by
  classical
  obtain ⟨X, U, z, hXN, hUN, hXA, hUA, hXX, hXU, hU4, hzA, hνz, hzX, hzU, hzz⟩ :=
    hM.exists_xu hNC hidx
  choose a ha hνa using hM.ν_surj
  obtain ⟨ε, hz⟩ : ∃ ε : Bool, z = a (if ε then 1 else 0) := by
    refine ⟨decide (ν z = 1), hM.eq_of_ν_eq hzA (ha _) ?_⟩
    rw [hνa]
    rcases hνz with h | h <;> simp [h]
  obtain ⟨ℓ₀, hℓ₀, hμℓ₀⟩ := hM.surj 16 (by norm_num)
  have hℓ₀2 : ℓ₀ * ℓ₀ = 1 := by
    have := (hM.sq_eq_one_iff hℓ₀).mpr (by rw [hμℓ₀]; rfl)
    rwa [pow_two] at this
  set D : Fin 8 → G := dElt X U with hD
  have hDN : ∀ d, D d ∈ normalizer (R : Set G) := dElt_mem hXN hUN
  have hDA := hM.code_dElt hXN hUN hXA hUA
  set ℓ : ℕ → G := fun j => D (fin8Of j) * ℓ₀ * (D (fin8Of j))⁻¹ with hℓdef
  have hℓ : ∀ j, ℓ j ∈ R := fun j => (mem_normalizer_iff.mp (hDN _) ℓ₀).mp hℓ₀
  have hℓμ : ∀ j < 8, μ (ℓ j) = sBasis.getD j 0 := fun j hj => by
    rw [hM.act_of_code (hDN _) (hDA _) ℓ₀ hℓ₀, hμℓ₀, adMat_sixteen j hj]
  have hℓ2 : ∀ j, ℓ j * ℓ j = 1 := fun j => by
    calc ℓ j * ℓ j = D (fin8Of j) * (ℓ₀ * ℓ₀) * (D (fin8Of j))⁻¹ := by
          simp only [hℓdef]; group
      _ = 1 := by rw [hℓ₀2, mul_one, mul_inv_cancel]
  have hDmul := dElt_mul hXX hXU hU4 hzX hzU hzz
  have hzcomm : ∀ x ∈ R, z * x = x * z := fun x hx => (hM.central x hx z hzA).symm
  have hDℓ : ∀ d : Fin 8, ∀ j < 8, D d * ℓ j * (D d)⁻¹ = ℓ (dMul d (fin8Of j)).val := by
    intro d j _
    have h1 := hDmul d (fin8Of j)
    have hc : ∀ c : G, c = z ∨ c = 1 → c * ℓ₀ * c⁻¹ = ℓ₀ := by
      rintro c (rfl | rfl)
      · rw [hzcomm ℓ₀ hℓ₀, mul_inv_cancel_right]
      · group
    simp only [hℓdef, fin8Of_val]
    calc D d * (D (fin8Of j) * ℓ₀ * (D (fin8Of j))⁻¹) * (D d)⁻¹ =
        (D d * D (fin8Of j)) * ℓ₀ * (D d * D (fin8Of j))⁻¹ := by group
      _ = D (dMul d (fin8Of j)) * ((if dOvf d (fin8Of j) then z else 1) * ℓ₀ *
          (if dOvf d (fin8Of j) then z else 1)⁻¹) * (D (dMul d (fin8Of j)))⁻¹ := by
          rw [hD, h1]; group
      _ = D (dMul d (fin8Of j)) * ℓ₀ * (D (dMul d (fin8Of j)))⁻¹ := by
          rw [hc _ (by split_ifs <;> simp)]
  have hDa : ∀ d t, D d * a t * (D d)⁻¹ = a (linApply (dCode d) t) := fun d t =>
    hM.eq_of_ν_eq (hM.normA _ (hDN d) _ (ha t)) (ha _) (by rw [hDA d _ (ha t), hνa, hνa])
  have hzD : ∀ d, z * D d = D d * z := by
    intro d
    have hzX' : ∀ n : ℕ, z * X ^ n = X ^ n * z := fun n => (Commute.pow_right hzX n).eq
    have hzU' : ∀ n : ℕ, z * U ^ n = U ^ n * z := fun n => (Commute.pow_right hzU n).eq
    rw [hD, dElt, ← mul_assoc, hzU', mul_assoc, hzX', mul_assoc]
  set Φ : ℕ × Fin 8 × Fin 8 → G := fun p => secN ℓ p.1 8 * a p.2.1 * D p.2.2 with hΦ
  have hPR : ∀ c, secN ℓ c 8 ∈ R := fun c => secN_mem hℓ c 8
  have hPa : ∀ c t, secN ℓ c 8 * a t ∈ R := fun c t => mul_mem (hPR c) (hM.le (ha t))
  have hμPa : ∀ c t, μ (secN ℓ c 8 * a t) = sMask c := fun c t => by
    rw [hM.mul _ (hPR c) _ (hM.le (ha t)), hM.μ_secN hℓ hℓμ c le_rfl,
      (hM.ker _ (hM.le (ha t))).mpr (ha t), Nat.xor_zero]
    rfl
  have hac : ∀ s t : Fin 8, a s * a t = a t * a s := fun s t =>
    hM.sec_comm ha (hM.le (ha t)) s
  have hΦA : ∀ p, ∀ b ∈ gmsA L T, ν (Φ p * b * (Φ p)⁻¹) = linApply (dCode p.2.2) (ν b) := by
    intro p b hb
    rw [(hM.act_mul_left (hDN _) (hPa p.1 p.2.1)).1 b hb]
    exact hDA _ b hb
  have hD0 : D 0 = 1 := by simp [hD, dElt]
  refine ⟨ε, Φ, ⟨?_, ?_, fun p => mul_mem (le_normalizer (hPa _ _)) (hDN _), hΦA,
    fun c t => ?_, fun c t => ?_, fun t => ?_, fun t => ?_, ?_⟩⟩
  ·
    rintro ⟨c₁, t₁, d₁⟩ ⟨c₂, t₂, d₂⟩
    have hconj : D d₁ * secN ℓ c₂ 8 * (D d₁)⁻¹ =
        secN ℓ (dPart d₁ c₂).1 8 * a (dPart d₁ c₂).2 :=
      hM.conj_secN hℓ ha hνa hℓμ hℓ2 (hDℓ d₁) c₂ le_rfl
    have hmul := hM.sec_mul hℓ ha hνa hℓμ hℓ2 c₁ (dPart d₁ c₂).1
    simp only [hΦ, sMul]
    set e : Fin 8 := if ε && dOvf d₁ d₂ then 1 else 0 with he
    have hze : (if dOvf d₁ d₂ then z else 1) = a e := by
      rw [he, hz]
      cases dOvf d₁ d₂ <;> cases ε <;> simp [hM.sec_zero ha hνa]
    have hDD : D d₁ * D d₂ = D (dMul d₁ d₂) * a e := by rw [hD, hDmul, hze]
    have heD : D (dMul d₁ d₂) * a e = a e * D (dMul d₁ d₂) := by
      rw [← hze]
      split_ifs
      · exact (hzD _).symm
      · group
    set c₂' := (dPart d₁ c₂).1
    set δ := (dPart d₁ c₂).2
    set r := linApply (dCode d₁) t₂
    have hcomm1 : a t₁ * secN ℓ c₂' 8 = secN ℓ c₂' 8 * a t₁ := hM.sec_comm ha (hPR c₂') t₁
    have hA : a (gam c₁ c₂') * (a t₁ * a δ * a r * a e) =
        a (t₁ ^^^ r ^^^ δ ^^^ gam c₁ c₂' ^^^ e) := by
      rw [hM.sec_xor ha hνa, hM.sec_xor ha hνa, hM.sec_xor ha hνa, hM.sec_xor ha hνa]
      simp only [mul_assoc]
      rw [← mul_assoc (a (gam c₁ c₂')) (a t₁), hac (gam c₁ c₂') t₁, mul_assoc,
        ← mul_assoc (a (gam c₁ c₂')) (a δ), hac (gam c₁ c₂') δ, mul_assoc,
        ← mul_assoc (a (gam c₁ c₂')) (a r), hac (gam c₁ c₂') r, mul_assoc,
        ← mul_assoc (a δ) (a r), hac δ r, mul_assoc]
    symm
    calc secN ℓ c₁ 8 * a t₁ * D d₁ * (secN ℓ c₂ 8 * a t₂ * D d₂)
        = secN ℓ c₁ 8 * a t₁ * (D d₁ * secN ℓ c₂ 8 * (D d₁)⁻¹) * (D d₁ * a t₂ * (D d₁)⁻¹) *
          (D d₁ * D d₂) := by group
      _ = secN ℓ c₁ 8 * (a t₁ * secN ℓ c₂' 8) * a δ * a r * (D (dMul d₁ d₂) * a e) := by
          rw [hconj, hDa, hDD]; simp only [mul_assoc]; rfl
      _ = secN ℓ c₁ 8 * (secN ℓ c₂' 8 * a t₁) * a δ * a r * (a e * D (dMul d₁ d₂)) := by
          rw [hcomm1, heD]
      _ = (secN ℓ c₁ 8 * secN ℓ c₂' 8) * (a t₁ * a δ * a r * a e) * D (dMul d₁ d₂) := by
          simp only [mul_assoc]
      _ = secN ℓ (c₁ ^^^ c₂') 8 * a (t₁ ^^^ r ^^^ δ ^^^ gam c₁ c₂' ^^^ e) * D (dMul d₁ d₂) := by
          rw [hmul, mul_assoc (secN ℓ (c₁ ^^^ c₂') 8), hA]
  ·
    rintro ⟨c, t, d⟩ ⟨c', t', d'⟩ hc hc' h
    simp only at hc hc'
    have hdd : d = d' := by
      refine RuSModel.dCode_injective _ _ (hM.code_unique (hΦA (c, t, d)) ?_)
      rw [h]
      exact hΦA (c', t', d')
    subst hdd
    have h1 : secN ℓ c 8 * a t = secN ℓ c' 8 * a t' := mul_right_cancel h
    have hcc : c = c' := by
      have h2 := congrArg μ h1
      rw [hμPa, hμPa] at h2
      rw [← RuSModel.cOf_sMask hc, ← RuSModel.cOf_sMask hc', h2]
    subst hcc
    have h3 : a t = a t' := mul_left_cancel h1
    have h4 := congrArg ν h3
    rw [hνa, hνa] at h4
    rw [h4]
  · simp only [hΦ, hD0, mul_one]
    exact hPa c t
  · simp only [hΦ, hD0, mul_one]
    exact hμPa c t
  · simp only [hΦ, hD0, mul_one, secN_zero_left, one_mul]
    exact ha t
  · simp only [hΦ, hD0, mul_one, secN_zero_left, one_mul]
    exact hνa t
  ·
    intro g hgN d hgd
    set x := g * (D d)⁻¹ with hx
    have hxN : x ∈ normalizer (R : Set G) := mul_mem hgN (inv_mem (hDN d))
    have hxR : x ∈ R := by
      refine hM.mem_of_code_linId hNC hxN fun b hb => ?_
      have hb' : (D d)⁻¹ * b * D d ∈ gmsA L T := hM.inv_conj_mem (hDN d) hb
      have e1 := hDA d _ hb'
      rw [show D d * ((D d)⁻¹ * b * D d) * (D d)⁻¹ = b by group] at e1
      rw [show x * b * x⁻¹ = g * ((D d)⁻¹ * b * D d) * g⁻¹ by rw [hx]; group, hgd _ hb',
        RuSimCode.linApply_linId, e1]
    set c := cOf (μ x) with hcdef
    have hc : c < 256 := RuSModel.cOf_lt _
    have hyR : (secN ℓ c 8)⁻¹ * x ∈ R := mul_mem (inv_mem (hPR c)) hxR
    have hyA : (secN ℓ c 8)⁻¹ * x ∈ gmsA L T := by
      rw [← hM.ker _ hyR, hM.mul _ (inv_mem (hPR c)) _ hxR, hM.μ_inv (hPR c),
        hM.μ_secN hℓ hℓμ c le_rfl]
      have : sMaskN c 8 = μ x := RuSModel.sMask_cOf (hM.lt x hxR)
      rw [this, Nat.xor_self]
    refine ⟨(c, ν ((secN ℓ c 8)⁻¹ * x), d), hc, rfl, ?_⟩
    have hay : a (ν ((secN ℓ c 8)⁻¹ * x)) = (secN ℓ c 8)⁻¹ * x :=
      hM.eq_of_ν_eq (ha _) hyA (hνa _)
    show secN ℓ c 8 * a (ν ((secN ℓ c 8)⁻¹ * x)) * D d = g
    rw [hay, hx]
    group

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78

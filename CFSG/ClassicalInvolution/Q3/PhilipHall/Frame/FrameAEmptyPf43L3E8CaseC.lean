module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43EndGame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8CaseA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Fac

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

section Prod

variable {T : Type} [Group T]

@[expose] def L3E8ProdP (K : Subgroup T) (z : T) : Set T :=
  {a | ∃ h : T, h⁻¹ * z * h ≠ z ∧ z * (h⁻¹ * z * h) = h⁻¹ * z * h * z ∧
    h⁻¹ * z * h ∉ firstFactor K ∧ a = z * (h⁻¹ * z * h)}

@[expose] def L3E8ProdPM (K : Subgroup T) (z : T) : Set T :=
  {p | ∃ a ∈ L3E8ProdP K z, ∃ m ∈ sigmaNorm K, p = m⁻¹ * a * m}

@[expose] def L3E8CentLe (K : Subgroup T) (z : T) : Prop :=
  ∀ a ∈ L3E8ProdP K z, Subgroup.centralizer ({a} : Set T) ≤ sigmaNorm K

theorem cent_le_of_mem_prodPM {K : Subgroup T} {z : T} (hC : L3E8CentLe K z) {p : T}
    (hp : p ∈ L3E8ProdPM K z) : Subgroup.centralizer ({p} : Set T) ≤ sigmaNorm K := by
  obtain ⟨a, ha, m, hm, rfl⟩ := hp
  intro c hc
  have hc' : m * c * m⁻¹ ∈ Subgroup.centralizer ({a} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc m * c * m⁻¹ * a = m * (c * (m⁻¹ * a * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * a * m) * c) * m⁻¹ := by rw [hc]
      _ = a * (m * c * m⁻¹) := by group
  have h1 := hC a ha hc'
  have h2 : c = m⁻¹ * (m * c * m⁻¹) * m := by group
  rw [h2]
  exact (sigmaNorm K).mul_mem ((sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem hm) h1) hm

end Prod

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem normalizer_rightConjugate_ht_le (cfg : L3E8Cfg K z J zJ H Q E S) (x : T) :
    Subgroup.normalizer (rightConjugate (firstFactor K) x : Set T) ≤
      Subgroup.normalizer (rightConjugate Q x : Set T) := by
  intro y hy
  have h1 : x * y * x⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) := by
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro w
    have := hy (x⁻¹ * w * x)
    simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
    rw [show x * (x⁻¹ * w * x) * x⁻¹ = w by group,
      show x * (y * (x⁻¹ * w * x) * y⁻¹) * x⁻¹ = x * y * x⁻¹ * w * (x * y * x⁻¹)⁻¹ by group]
      at this
    exact this
  have h2 := cfg.normalizer_ht_le h1
  rw [Subgroup.mem_normalizer_iff] at h2 ⊢
  intro w
  have := h2 (x * w * x⁻¹)
  simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
  rw [show x * y * x⁻¹ * (x * w * x⁻¹) * (x * y * x⁻¹)⁻¹ = x * (y * w * y⁻¹) * x⁻¹ by group]
    at this
  exact this

private theorem exists_involution_comm_of_mem_normalizer {A : Subgroup T} {y : T}
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hyN : y ∈ Subgroup.normalizer (A : Set T))
    (hA : 2 ∣ Nat.card A) : ∃ f ∈ A, f * f = 1 ∧ f ≠ 1 ∧ f * y = y * f := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set T) := Subgroup.zpowers_le.mpr hyN
  letI : MulDistribMulAction (Subgroup.zpowers y) A :=
    MulDistribMulAction.compHom A (Subgroup.inclusion hle)
  have hdvd : 2 ∣ Nat.card (FixedPoints.subgroup (Subgroup.zpowers y) A) :=
    Nat.modEq_zero_iff_dvd.mp ((hy2.card_modEq_card_fixedPoints A).symm.trans hA.modEq_zero_nat)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hg' : orderOf ((g : A) : T) = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  have hfix : ∀ m : Subgroup.zpowers y, m • (g : A) = g := g.2
  have hfix' : y * ((g : A) : T) * y⁻¹ = ((g : A) : T) :=
    congrArg Subtype.val (hfix ⟨y, Subgroup.mem_zpowers y⟩)
  refine ⟨((g : A) : T), (g : A).2, ?_, ?_, ?_⟩
  · rw [← pow_two, ← hg']
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at hg'
    exact absurd hg' (by norm_num)
  · calc ((g : A) : T) * y = (y * ((g : A) : T) * y⁻¹) * y := by rw [hfix']
      _ = y * ((g : A) : T) := by group

theorem clash (cfg : L3E8Cfg K z J zJ H Q E S) (hU : UniqueCosetZ K z) {y : T}
    (hy : Subgroup.centralizer ({y} : Set T) ≤ sigmaNorm K)
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) {x : T} (hx : x ∉ sigmaNorm K) :
    y ∉ Subgroup.normalizer (rightConjugate Q x : Set T) := by
  intro hyN
  have hz := cfg.datum.unique
  have hzQ : z ∈ Q := cfg.E_le_Q cfg.z_mem_E
  have hu : x⁻¹ * z * x ∈ rightConjugate Q x := by
    rw [mem_rightConjugate_iff, show x * (x⁻¹ * z * x) * x⁻¹ = z by group]
    exact hzQ
  have hu2 : orderOf (x⁻¹ * z * x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      calc x⁻¹ * z * x * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
        _ = 1 := by rw [hz.sq]; group
    · intro h
      apply hz.ne_one
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
  have hA : 2 ∣ Nat.card (rightConjugate Q x) := hu2 ▸ Subgroup.orderOf_dvd_natCard _ hu
  obtain ⟨f, hfA, hf2, hf1, hfy⟩ := exists_involution_comm_of_mem_normalizer hy2 hyN hA
  obtain ⟨w, hw, rfl⟩ := cfg.inv_Qconj hx hfA hf2 hf1
  exact hw (hU w (hy (Subgroup.mem_centralizer_singleton_iff.mpr hfy)))

theorem prod_mem_P (cfg : L3E8Cfg K z J zJ H Q E S) {m₁ m₂ : T} (hm₁ : m₁ ∈ sigmaNorm K)
    (hm₂ : m₂ ∈ sigmaNorm K) (hne : conjSub m₁ (firstFactor K) ≠ conjSub m₂ (firstFactor K))
    {x y : T} (hx : x ∈ conjSub m₁ Q) (hy : y ∈ conjSub m₂ Q) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) : x * y ∈ L3E8ProdPM K z := by
  have hz := cfg.datum.unique
  have hzHt : z ∈ firstFactor K := cfg.Q_le_ht (cfg.E_le_Q cfg.z_mem_E)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hx' : m₁⁻¹ * x * m₁ ∈ Q := mem_conjSub_iff.mp hx
  have hx'2 : (m₁⁻¹ * x * m₁) * (m₁⁻¹ * x * m₁) = 1 := by
    calc (m₁⁻¹ * x * m₁) * (m₁⁻¹ * x * m₁) = m₁⁻¹ * (x * x) * m₁ := by group
      _ = 1 := by rw [hx2]; group
  have hx'1 : m₁⁻¹ * x * m₁ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun w => m₁ * w * m₁⁻¹) h
    simpa [mul_assoc] using this)
  obtain ⟨l, hl, hlx⟩ := cfg.Q_conj cfg.efacts hx' hx'2 hx'1
  obtain ⟨m, hmM, hxm⟩ : ∃ m ∈ sigmaNorm K, x = m⁻¹ * z * m :=
    ⟨l * m₁⁻¹, (sigmaNorm K).mul_mem (cfg.ht_le_sigmaNorm hl) ((sigmaNorm K).inv_mem hm₁), by
      calc x = m₁ * (m₁⁻¹ * x * m₁) * m₁⁻¹ := by group
        _ = m₁ * (l⁻¹ * z * l) * m₁⁻¹ := by rw [hlx]
        _ = (l * m₁⁻¹)⁻¹ * z * (l * m₁⁻¹) := by group⟩
  have hy' : m₂⁻¹ * y * m₂ ∈ Q := mem_conjSub_iff.mp hy
  have hy'2 : (m₂⁻¹ * y * m₂) * (m₂⁻¹ * y * m₂) = 1 := by
    calc (m₂⁻¹ * y * m₂) * (m₂⁻¹ * y * m₂) = m₂⁻¹ * (y * y) * m₂ := by group
      _ = 1 := by rw [hy2]; group
  have hy'1 : m₂⁻¹ * y * m₂ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun w => m₂ * w * m₂⁻¹) h
    simpa [mul_assoc] using this)
  obtain ⟨l', hl', hly⟩ := cfg.Q_conj cfg.efacts hy' hy'2 hy'1
  have hyh : m * y * m⁻¹ = (l' * m₂⁻¹ * m⁻¹)⁻¹ * z * (l' * m₂⁻¹ * m⁻¹) := by
    calc m * y * m⁻¹ = m * m₂ * (m₂⁻¹ * y * m₂) * m₂⁻¹ * m⁻¹ := by group
      _ = m * m₂ * (l'⁻¹ * z * l') * m₂⁻¹ * m⁻¹ := by rw [hly]
      _ = (l' * m₂⁻¹ * m⁻¹)⁻¹ * z * (l' * m₂⁻¹ * m⁻¹) := by group
  have hzm : z = m * x * m⁻¹ := by rw [hxm]; group
  have hzF : z ∈ conjSub (m * m₁) (firstFactor K) := by
    have hxHt : x ∈ conjSub m₁ (firstFactor K) := conjSub_mono cfg.Q_le_ht hx
    have := conj_mem_conjSub (n := m) hxHt
    rw [← conjSub_mul] at this
    rw [hzm]
    exact this
  have hzO : z ∉ oddCoreOf (sigmaGen K) := not_mem_oddCoreOf_of_sq _ hz.sq hz.ne_one
  have hF1 : conjSub (m * m₁) (firstFactor K) = conjSub (1 : T) (firstFactor K) :=
    cfg.factor_eq_of_mem ((sigmaNorm K).mul_mem hmM hm₁) (Subgroup.one_mem _) hzF
      (by rw [h1Ht]; exact hzHt) hzO
  have hF2 : conjSub (m * m₂) (firstFactor K) ≠ conjSub (1 : T) (firstFactor K) := by
    intro h
    apply hne
    have := congrArg (conjSub m⁻¹) (hF1.trans h.symm)
    rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    exact this
  have hy'F : m * y * m⁻¹ ∈ conjSub (m * m₂) (firstFactor K) := by
    have hyHt : y ∈ conjSub m₂ (firstFactor K) := conjSub_mono cfg.Q_le_ht hy
    have := conj_mem_conjSub (n := m) hyHt
    rw [← conjSub_mul] at this
    exact this
  have hyy2 : (m * y * m⁻¹) * (m * y * m⁻¹) = 1 := by
    calc (m * y * m⁻¹) * (m * y * m⁻¹) = m * (y * y) * m⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hyy1 : m * y * m⁻¹ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun w => m⁻¹ * w * m) h
    simpa [mul_assoc] using this)
  have hy'Ht : m * y * m⁻¹ ∉ firstFactor K := by
    intro h
    exact hF2 (cfg.factor_eq_of_mem ((sigmaNorm K).mul_mem hmM hm₂) (Subgroup.one_mem _) hy'F
      (by rw [h1Ht]; exact h) (not_mem_oddCoreOf_of_sq _ hyy2 hyy1))
  have hcomm : z * (m * y * m⁻¹) = m * y * m⁻¹ * z := by
    rw [hzm]
    calc m * x * m⁻¹ * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := by group
      _ = m * (y * x) * m⁻¹ := by rw [hxy]
      _ = m * y * m⁻¹ * (m * x * m⁻¹) := by group
  have hne' : m * y * m⁻¹ ≠ z := fun h => hy'Ht (h ▸ hzHt)
  refine ⟨z * (m * y * m⁻¹), ⟨l' * m₂⁻¹ * m⁻¹, ?_, ?_, ?_, ?_⟩, m, hmM, ?_⟩
  · rw [← hyh]; exact hne'
  · rw [← hyh]; exact hcomm
  · rw [← hyh]; exact hy'Ht
  · rw [← hyh]
  · rw [hxm]; group

theorem prod_mem (cfg : L3E8Cfg K z J zJ H Q E S) {h : T} (hmem : h⁻¹ * z * h ∈ firstFactor K)
    (hne : h⁻¹ * z * h ≠ z) (hc : z * (h⁻¹ * z * h) = h⁻¹ * z * h * z) :
    ∃ l ∈ firstFactor K, l⁻¹ * z * l = z * (h⁻¹ * z * h) := by
  have hz := cfg.datum.unique
  have hzQ : z ∈ Q := cfg.E_le_Q cfg.z_mem_E
  have hcz : h⁻¹ * z * h ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc.symm
  have hhM : h ∈ sigmaNorm K := cfg.zconj_cent hcz
  have hw2 : (h⁻¹ * z * h) * (h⁻¹ * z * h) = 1 := by
    calc (h⁻¹ * z * h) * (h⁻¹ * z * h) = h⁻¹ * (z * z) * h := by group
      _ = 1 := by rw [hz.sq]; group
  have hw1 : h⁻¹ * z * h ≠ 1 := fun e => hz.ne_one (by
    have := congrArg (fun w => h * w * h⁻¹) e
    simpa [mul_assoc] using this)
  have h1Ht : conjSub (1 : T) (firstFactor K) = firstFactor K :=
    conjSub_eq_self_of_mem (Subgroup.one_mem _)
  have hw₁ : h⁻¹ * z * h ∈ conjSub (1 : T) (firstFactor K) := by rw [h1Ht]; exact hmem
  have hw₂ : h⁻¹ * z * h ∈ conjSub h⁻¹ (firstFactor K) := by
    have := conj_mem_conjSub (n := h⁻¹) (cfg.Q_le_ht hzQ)
    simpa using this
  have heq := cfg.factor_eq_of_mem (Subgroup.one_mem _) ((sigmaNorm K).inv_mem hhM) hw₁ hw₂
    (not_mem_oddCoreOf_of_sq _ hw2 hw1)
  have hN : h⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) :=
    mem_normalizer_iff_conjSub_eq.mpr (heq.symm.trans h1Ht)
  have hwQ : h⁻¹ * z * h ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (cfg.normalizer_ht_le hN) z).mp hzQ
    simpa using this
  have haQ : z * (h⁻¹ * z * h) ∈ Q := Q.mul_mem hzQ hwQ
  have ha2 : z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) = 1 := by
    calc z * (h⁻¹ * z * h) * (z * (h⁻¹ * z * h)) = z * ((h⁻¹ * z * h) * z) * (h⁻¹ * z * h) := by
          group
      _ = z * (z * (h⁻¹ * z * h)) * (h⁻¹ * z * h) := by rw [hc]
      _ = (z * z) * ((h⁻¹ * z * h) * (h⁻¹ * z * h)) := by group
      _ = 1 := by rw [hz.sq, hw2, one_mul]
  have ha1 : z * (h⁻¹ * z * h) ≠ 1 := by
    intro h1
    apply hne
    have : h⁻¹ * z * h = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hz.sq
  exact cfg.Q_conj cfg.efacts haQ ha2 ha1

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

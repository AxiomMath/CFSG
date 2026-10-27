module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveClasses

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_centralizer (A : Subgroup G) :
    A ≤ normalizer (centralizer (A : Set G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [mem_centralizer_iff] at hk ⊢
    intro b hb
    have h1 := hk _ (mul_mem (mul_mem (inv_mem ha) hb) ha)
    calc b * (a * k * a⁻¹) = a * ((a⁻¹ * b * a) * k) * a⁻¹ := by group
      _ = a * (k * (a⁻¹ * b * a)) * a⁻¹ := by rw [h1]
      _ = a * k * a⁻¹ * b := by group
  · intro hk
    rw [mem_centralizer_iff] at hk ⊢
    intro b hb
    have h1 := hk _ (mul_mem (mul_mem ha hb) (inv_mem ha))
    calc b * k = a⁻¹ * ((a * b * a⁻¹) * (a * k * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * k * a⁻¹) * (a * b * a⁻¹)) * a := by rw [h1]
      _ = k * b := by group

omit [Finite G] in
theorem exists_mul_of_mem_sup {A : Subgroup G} {w : G} (hw : w ∈ A ⊔ centralizer (A : Set G)) :
    ∃ a ∈ A, ∃ k ∈ centralizer (A : Set G), a * k = w := by
  have h1 : w ∈ ((A ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_centralizer A)] at h1
  obtain ⟨a, ha, k, hk, rfl⟩ := h1
  exact ⟨a, ha, k, hk, rfl⟩

omit [Finite G] in
theorem mem_sup_iff_sign {A : Subgroup G} (e : ↥A ≃* A5) (x : ↥(normalizer (A : Set G))) :
    (x : G) ∈ A ⊔ centralizer (A : Set G) ↔ Perm.sign (autPerm e x) = 1 := by
  constructor
  · intro hx
    obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hx
    have hkN : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hk
    have hxe : x = ⟨a, le_normalizer ha⟩ * ⟨k, hkN⟩ := Subtype.ext hak.symm
    rw [hxe, map_mul, (autPerm_eq_one_iff e ⟨k, hkN⟩).mpr hk, mul_one, autPerm_of_mem e ha]
    exact Equiv.Perm.mem_alternatingGroup.mp (e ⟨a, ha⟩).2
  · intro hs
    obtain ⟨a, ha⟩ := e.surjective ⟨autPerm e x, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
    have haN : (a : G) ∈ normalizer (A : Set G) := le_normalizer a.2
    have h1 : autPerm e ⟨a, haN⟩ = autPerm e x := by
      rw [autPerm_of_mem e a.2]
      exact congrArg Subtype.val ha
    have h2 : ((⟨a, haN⟩ : ↥(normalizer (A : Set G)))⁻¹ * x : ↥(normalizer (A : Set G))) ∈
        (autPerm e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := (autPerm_eq_one_iff e _).mp h2
    have : (x : G) = (a : G) * ((a : G)⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_left a.2) (mem_sup_right h3)

omit [Finite G] in
theorem mem_sup_of_centralizer_four {A W : Subgroup G} (e : ↥A ≃* A5) (hWA : W ≤ A)
    (hW : Nat.card W = 4) {x : G} (hxN : x ∈ normalizer (A : Set G))
    (hxW : ∀ w ∈ W, w * x = x * w) : x ∈ W ⊔ centralizer (A : Set G) := by
  have hWA' : Nat.card (W.subgroupOf A) = 4 := by
    rw [← hW]
    exact Nat.card_congr (subgroupOfEquivOfLe hWA).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_P0 e hWA'
  set e' : ↥A ≃* A5 := ψ.symm with he'
  have hψW : ∀ q ∈ P0, ((ψ q : ↥A) : G) ∈ W := fun q hq => by
    have : ψ q ∈ W.subgroupOf A := hψ ▸ ⟨q, hq, rfl⟩
    exact mem_subgroupOf.mp this
  set σ := autPerm e' ⟨x, hxN⟩ with hσ
  have hcomm : ∀ q ∈ P0, σ * ((q : A5) : Perm (Fin 5)) = (q : Perm (Fin 5)) * σ := by
    intro q hq
    have hqA : ((ψ q : ↥A) : G) ∈ A := (ψ q).2
    have h1 : autPerm e' ⟨((ψ q : ↥A) : G), le_normalizer hqA⟩ = ((q : A5) : Perm (Fin 5)) := by
      rw [autPerm_of_mem e' hqA]
      congr 2
      rw [he']
      exact ψ.symm_apply_apply q
    rw [← h1, hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxW _ (hψW q hq)).symm
  have hk1 : k1 ∈ P0 := by rw [mem_P0]; decide
  have hk2 : k2 ∈ P0 := by rw [mem_P0]; decide
  have hk12 : k1 * k2 ∈ P0 := by rw [mem_P0]; decide
  obtain ⟨q, hq, hσq⟩ : ∃ q ∈ P0, σ = ((q : A5) : Perm (Fin 5)) := by
    rcases perm5_centralizer_P0 σ (hcomm k1 hk1) (hcomm k2 hk2) with h1 | h1 | h1 | h1
    · exact ⟨1, one_mem _, by rw [h1]; rfl⟩
    · exact ⟨k1, hk1, h1⟩
    · exact ⟨k2, hk2, h1⟩
    · exact ⟨k1 * k2, hk12, h1⟩
  set w₀ : G := ((ψ q : ↥A) : G) with hw₀
  have hw₀W : w₀ ∈ W := hψW q hq
  have hw₀A : w₀ ∈ A := (ψ q).2
  have hσw : autPerm e' ⟨w₀, le_normalizer hw₀A⟩ = σ := by
    rw [autPerm_of_mem e' hw₀A, hσq]
    congr 2
    rw [he']
    exact ψ.symm_apply_apply q
  have hxw : x * w₀⁻¹ ∈ centralizer (A : Set G) := by
    have h1 : autPerm e' (⟨x, hxN⟩ * (⟨w₀, le_normalizer hw₀A⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, hσw, ← hσ, mul_inv_cancel]
    exact (autPerm_eq_one_iff e' _).mp h1
  have : x = (x * w₀⁻¹) * w₀ := by group
  rw [this, sup_comm]
  exact mul_mem (mem_sup_left hxw) (mem_sup_right hw₀W)

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

theorem normalizer_le_sup_of_eps_one {P : Subgroup G}
    (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀)) (hε : EpsOne (R ⊔ T) P) :
    normalizer (A : Set G) ≤ A ⊔ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hε' : IsSylowOf 2 P (normalizer ((R ⊔ T : Subgroup G) : Set G)) := hε
  obtain ⟨eA⟩ := h.equiv
  intro t ht
  by_contra hout
  have hsign : Perm.sign (autPerm eA ⟨t, ht⟩) = -1 := by
    rcases Int.units_eq_one_or (Perm.sign (autPerm eA ⟨t, ht⟩)) with h1 | h1
    · exact absurd ((mem_sup_iff_sign eA ⟨t, ht⟩).mpr h1) hout
    · exact h1
  have htK : t ∈ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq h.hyp.standard]
    exact ht
  obtain ⟨k, hk, hkt⟩ := exists_mul_mem_normalizer h.sylowR htK
  have hkN : k ∈ normalizer (A : Set G) := centralizer_le_normalizer _ hk
  obtain ⟨a, ha, hat⟩ := exists_mul_mem_normalizer h.loc.sylowV₀ (mul_mem hkN ht)
  set t₂ := a * (k * t) with ht₂
  have ht₂A : t₂ ∈ normalizer (A : Set G) := mul_mem (le_normalizer ha) (mul_mem hkN ht)
  have haR : a ∈ normalizer (R : Set G) :=
    centralizer_le_normalizer _ (le_centralizer_iff.mp h.sylowR.le ha)
  have ht₂R : t₂ ∈ normalizer (R : Set G) := mul_mem haR hkt
  have ht₂V : t₂ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    rw [← h.sup_R_V₀]
    exact mem_normalizer_sup ht₂R hat
  have hsign₂ : Perm.sign (autPerm eA ⟨t₂, ht₂A⟩) = -1 := by
    have he : (⟨t₂, ht₂A⟩ : ↥(normalizer (A : Set G))) =
        ⟨a, le_normalizer ha⟩ * (⟨k, hkN⟩ * ⟨t, ht⟩) := rfl
    have hap : autPerm eA ⟨t₂, ht₂A⟩ = autPerm eA ⟨a, le_normalizer ha⟩ * autPerm eA ⟨t, ht⟩ := by
      rw [he, map_mul, map_mul, (autPerm_eq_one_iff eA ⟨k, hkN⟩).mpr hk, one_mul]
    rw [hap, map_mul, autPerm_of_mem eA ha, Equiv.Perm.mem_alternatingGroup.mp (eA ⟨a, ha⟩).2,
      one_mul, hsign]
  obtain ⟨n, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t₂).ne'
  set t₃ := t₂ ^ m with ht₃
  have ht₃A : t₃ ∈ normalizer (A : Set G) := pow_mem ht₂A m
  have ht₃V : t₃ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := pow_mem ht₂V m
  have hsign₃ : Perm.sign (autPerm eA ⟨t₃, ht₃A⟩) = -1 := by
    have he : (⟨t₃, ht₃A⟩ : ↥(normalizer (A : Set G))) = ⟨t₂, ht₂A⟩ ^ m := rfl
    rw [he, map_pow, map_pow, hsign₂, hm.neg_one_pow]
  have ht₃2 : t₃ ^ 2 ^ n = 1 := by
    rw [ht₃, ← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have ht₃P₀ : t₃ ∉ transvGroup (R ⊔ T) V₀ := by
    intro hmem
    have hC := (mem_transvGroup.mp hmem).2.1
    have h1 := mem_sup_of_centralizer_four eA h.V₀_le_A h.card_V₀ ht₃A
      (fun w hw => (mem_centralizer_iff.mp hC w hw))
    have h2 : t₃ ∈ A ⊔ centralizer (A : Set G) := (sup_le_sup_right h.V₀_le_A _) h1
    rw [mem_sup_iff_sign eA ⟨t₃, ht₃A⟩, hsign₃] at h2
    exact absurd h2 (by decide)
  set P₀ := transvGroup (R ⊔ T) V₀ with hP₀
  set Z := zpowers t₃ with hZ
  have hZp : IsPGroup 2 Z := by
    have h1 : orderOf t₃ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one ht₃2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hZN : Z ≤ normalizer (P₀ : Set G) := zpowers_le.mpr (h.le_normalizer_transvGroup ht₃V)
  have hP₀V : P₀ ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := fun x hx =>
    (mem_transvGroup.mp hx).1
  set H := Z ⊔ P₀ with hH
  have hHV : H ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) :=
    sup_le (zpowers_le.mpr ht₃V) hP₀V
  have hPH : IsSylowOf 2 P H := hε'.of_le (hP.le.trans le_sup_right) hHV
  have hodd := (isSylowOf_iff.mp hPH).2.2
  have hmul := Subgroup.relIndex_mul_relIndex P P₀ H hP.le le_sup_right
  have h1 : Nat.card H * Nat.card (Z ⊓ P₀ : Subgroup G) = Nat.card Z * Nat.card P₀ :=
    card_sup_mul_card_inf_of_le hZN
  have h2 := Subgroup.relIndex_mul_card P₀ H
  rw [inf_eq_left.mpr (le_sup_right : P₀ ≤ H)] at h2
  have h3 := Subgroup.relIndex_mul_card (Z ⊓ P₀) Z
  rw [inf_eq_left.mpr (inf_le_left : Z ⊓ P₀ ≤ Z)] at h3
  have hpos₀ : 0 < Nat.card P₀ := Nat.card_pos
  have hposZ : 0 < Nat.card (Z ⊓ P₀ : Subgroup G) := Nat.card_pos
  have hidx : P₀.relIndex H = (Z ⊓ P₀).relIndex Z := by
    have e1 : P₀.relIndex H * Nat.card P₀ * Nat.card (Z ⊓ P₀ : Subgroup G) =
        (Z ⊓ P₀).relIndex Z * Nat.card (Z ⊓ P₀ : Subgroup G) * Nat.card P₀ := by
      rw [h2, h1, h3]
    have e2 : P₀.relIndex H * Nat.card (Z ⊓ P₀ : Subgroup G) =
        (Z ⊓ P₀).relIndex Z * Nat.card (Z ⊓ P₀ : Subgroup G) := by
      apply Nat.eq_of_mul_eq_mul_right hpos₀
      calc P₀.relIndex H * Nat.card (Z ⊓ P₀ : Subgroup G) * Nat.card P₀ =
          P₀.relIndex H * Nat.card P₀ * Nat.card (Z ⊓ P₀ : Subgroup G) := by ring
        _ = _ := e1
    exact Nat.eq_of_mul_eq_mul_right hposZ e2
  have heven : 2 ∣ (Z ⊓ P₀).relIndex Z := by
    obtain ⟨j, hj⟩ := hZp.index ((Z ⊓ P₀).subgroupOf Z)
    have hj' : (Z ⊓ P₀).relIndex Z = 2 ^ j := hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hj'
      exact ht₃P₀ (mem_inf.mp (hj' (mem_zpowers t₃))).2
    · rw [hj']
      exact dvd_pow_self 2 h0.ne'
  exact hodd (by rw [← hmul, hidx]; exact dvd_mul_of_dvd_right heven _)

section Inner

variable (hNA : normalizer (A : Set G) ≤ A ⊔ centralizer (A : Set G))
include hNA

theorem centralizer_le_sup_conj (x : G) {r : G}
    (hrK : r ∈ centralizer (rightConjugate A x : Set G)) (hr1 : r ≠ 1) (hr2 : r * r = 1) :
    centralizer ({r} : Set G) ≤
      rightConjugate A x ⊔ centralizer (rightConjugate A x : Set G) := by
  intro c hc
  have h1 := centralizer_le_normalizer_conj h.hyp.standard x hrK hr1 hr2 hc
  rw [mem_normalizer_rightConjugate_iff] at h1
  have h3 : c ∈ rightConjugate (A ⊔ centralizer (A : Set G)) x := by
    rw [mem_rightConjugate_iff]
    exact hNA h1
  rw [centralizer_rightConjugate]
  rwa [show rightConjugate (A ⊔ centralizer (A : Set G)) x =
    rightConjugate A x ⊔ rightConjugate (centralizer (A : Set G)) x from Subgroup.map_sup _ _ _]
    at h3

theorem mem_of_isConj_of_commute {z₀ : G} (hz₀ : z₀ ∈ V₀) (hz₀1 : z₀ ≠ 1) (x : G) {r w : G}
    (hrK : r ∈ centralizer (rightConjugate A x : Set G)) (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hw2 : w * w = 1) (hwr : w * r = r * w) (hwz : IsConj z₀ w) :
    w ∈ rightConjugate A x := by
  obtain ⟨eA⟩ := h.equiv
  rw [mem_rightConjugate_iff]
  have hr'K : x * r * x⁻¹ ∈ centralizer (A : Set G) := by
    rw [centralizer_rightConjugate, mem_rightConjugate_iff] at hrK
    exact hrK
  have hr'1 : x * r * x⁻¹ ≠ 1 := fun he => hr1 (by
    calc r = x⁻¹ * (x * r * x⁻¹) * x := by group
      _ = 1 := by rw [he]; group)
  have hr'2 : x * r * x⁻¹ * (x * r * x⁻¹) = 1 := by
    calc x * r * x⁻¹ * (x * r * x⁻¹) = x * (r * r) * x⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hw'r : x * w * x⁻¹ ∈ centralizer ({x * r * x⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x * w * x⁻¹ * (x * r * x⁻¹) = x * (w * r) * x⁻¹ := by group
      _ = x * (r * w) * x⁻¹ := by rw [hwr]
      _ = x * r * x⁻¹ * (x * w * x⁻¹) := by group
  have hw'z : IsConj z₀ (x * w * x⁻¹) := hwz.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have hw'2 : x * w * x⁻¹ * (x * w * x⁻¹) = 1 := by
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hmem := h.centralizer_le_sup_conj hNA 1 (by rw [rightConjugate_one]; exact hr'K) hr'1 hr'2
    hw'r
  rw [rightConjugate_one] at hmem
  obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hmem
  rw [← hak] at hw'z hw'2 ⊢
  have hka : k * a = a * k := (mem_centralizer_iff.mp hk a ha).symm
  have hsq : a * a * (k * k) = 1 := by
    calc a * a * (k * k) = a * k * (a * k) := by
          calc a * a * (k * k) = a * (a * k) * k := by group
            _ = a * (k * a) * k := by rw [hka]
            _ = a * k * (a * k) := by group
      _ = 1 := hw'2
  have haa : a * a ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.mpr ⟨mul_mem ha ha, ?_⟩
    have : a * a = (k * k)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact inv_mem (mul_mem hk hk)
  rw [inf_centralizer_eq_bot eA, mem_bot] at haa
  have hkk : k * k = 1 := by rw [haa, one_mul] at hsq; exact hsq
  by_cases hk1 : k = 1
  · rw [hk1, mul_one]
    exact ha
  exfalso
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  obtain ⟨κ, hκ, hκk⟩ := exists_conj_mem_of_isSylowOf h.sylowR hk (n := 1)
    (by rw [pow_one, sq]; exact hkk)
  have hκk1 : κ * k * κ⁻¹ ≠ 1 := fun he => hk1 (by
    calc k = κ⁻¹ * (κ * k * κ⁻¹) * κ := by group
      _ = 1 := by rw [he]; group)
  by_cases ha1 : a = 1
  · rw [ha1, one_mul] at hw'z
    exact h.not_isConj_of_mem_R hz₀ hz₀1 hκk hκk1
      (hw'z.trans (isConj_iff.mpr ⟨κ, rfl⟩))
  obtain ⟨α, hα, hαa⟩ := exists_conj_mem_of_isSylowOf h.loc.sylowV₀ ha (n := 1)
    (by rw [pow_one, sq]; exact haa)
  have hαa1 : α * a * α⁻¹ ≠ 1 := fun he => ha1 (by
    calc a = α⁻¹ * (α * a * α⁻¹) * α := by group
      _ = 1 := by rw [he]; group)
  have hκK' : κ * k * κ⁻¹ ∈ centralizer (A : Set G) :=
    mul_mem (mul_mem hκ hk) (inv_mem hκ)
  have hconj : α * κ * (a * k) * (α * κ)⁻¹ = α * a * α⁻¹ * (κ * k * κ⁻¹) := by
    have h1 : κ * a = a * κ := (mem_centralizer_iff.mp hκ a ha).symm
    have h2 : κ * k * κ⁻¹ * α⁻¹ = α⁻¹ * (κ * k * κ⁻¹) :=
      (mem_centralizer_iff.mp hκK' α⁻¹ (inv_mem hα)).symm
    calc α * κ * (a * k) * (α * κ)⁻¹ = α * (κ * a) * k * κ⁻¹ * α⁻¹ := by group
      _ = α * (a * κ) * k * κ⁻¹ * α⁻¹ := by rw [h1]
      _ = α * a * (κ * k * κ⁻¹ * α⁻¹) := by group
      _ = α * a * (α⁻¹ * (κ * k * κ⁻¹)) := by rw [h2]
      _ = α * a * α⁻¹ * (κ * k * κ⁻¹) := by group
  have hvV : α * a * α⁻¹ * (κ * k * κ⁻¹) ∈ R ⊔ T :=
    mul_mem (h.V₀_le hαa) (mem_sup_left hκk)
  have hv0 : α * a * α⁻¹ * (κ * k * κ⁻¹) ∉ V₀ := by
    intro hv
    have h1 : κ * k * κ⁻¹ ∈ R ⊓ V₀ := by
      refine mem_inf.mpr ⟨hκk, ?_⟩
      have h2 := mul_mem (inv_mem hαa) hv
      have e : (α * a * α⁻¹)⁻¹ * (α * a * α⁻¹ * (κ * k * κ⁻¹)) = κ * k * κ⁻¹ := by group
      rwa [e] at h2
    rw [h.inf_R_V₀, mem_bot] at h1
    exact hκk1 h1
  exact h.not_isConj_of_mem_V₀ hz₀ hz₀1 hvV hv0
    (hw'z.trans (isConj_iff.mpr ⟨α * κ, hconj⟩))

theorem isConj_mul_of_commute {z₀ r₀ : G} (hz₀ : z₀ ∈ V₀) (hz₀1 : z₀ ≠ 1) (hr₀ : r₀ ∈ R)
    (hcls : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → IsConj z₀ x ∨ IsConj r₀ x) {w₁ w₂ : G}
    (h1 : IsConj z₀ w₁) (h2 : IsConj z₀ w₂) (h12 : w₁ * w₂ = w₂ * w₁) (hne : w₁ ≠ w₂) :
    IsConj z₀ (w₁ * w₂) := by
  obtain ⟨eA⟩ := h.equiv
  have hz₀2 : z₀ * z₀ = 1 := h.mul_self (h.V₀_le hz₀)
  have hsq : ∀ w, IsConj z₀ w → w * w = 1 := fun w hw => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hw
    calc c * z₀ * c⁻¹ * (c * z₀ * c⁻¹) = c * (z₀ * z₀) * c⁻¹ := by group
      _ = 1 := by rw [hz₀2]; group
  have hw₁2 := hsq w₁ h1
  have hw₂2 := hsq w₂ h2
  have h22 : (w₁ * w₂) ^ 2 = 1 := by
    rw [sq]
    calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [h12]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁2, hw₂2, one_mul]
  have h21 : w₁ * w₂ ≠ 1 := fun he => hne (by
    calc w₁ = w₁ * (w₂ * w₂) := by rw [hw₂2, mul_one]
      _ = (w₁ * w₂) * w₂ := by group
      _ = w₂ := by rw [he, one_mul])
  rcases hcls _ h22 h21 with hc | hc
  · exact hc
  exfalso
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hK : w₁ * w₂ ∈ centralizer (rightConjugate A c⁻¹ : Set G) := by
    rw [centralizer_rightConjugate, mem_rightConjugate_iff, ← hc]
    have : c⁻¹ * (c * r₀ * c⁻¹) * c⁻¹⁻¹ = r₀ := by group
    rw [this]
    exact h.sylowR.le hr₀
  have h222 : w₁ * w₂ * (w₁ * w₂) = 1 := by rw [← sq]; exact h22
  have hm₁ := h.mem_of_isConj_of_commute hNA hz₀ hz₀1 c⁻¹ hK h21 h222 hw₁2
    (by calc w₁ * (w₁ * w₂) = (w₁ * w₁) * w₂ := by group
          _ = w₂ := by rw [hw₁2, one_mul]
          _ = w₁ * w₂ * w₁ := by
            calc w₂ = (w₁ * w₁) * w₂ := by rw [hw₁2, one_mul]
              _ = w₁ * (w₁ * w₂) := by group
              _ = w₁ * (w₂ * w₁) := by rw [h12]
              _ = w₁ * w₂ * w₁ := by group) h1
  have hm₂ := h.mem_of_isConj_of_commute hNA hz₀ hz₀1 c⁻¹ hK h21 h222 hw₂2
    (by calc w₂ * (w₁ * w₂) = (w₂ * w₁) * w₂ := by group
          _ = (w₁ * w₂) * w₂ := by rw [h12]
          _ = w₁ * w₂ * w₂ := rfl) h2
  have hmem : w₁ * w₂ ∈ rightConjugate A c⁻¹ ⊓ centralizer (rightConjugate A c⁻¹ : Set G) :=
    mem_inf.mpr ⟨mul_mem hm₁ hm₂, hK⟩
  rw [inf_centralizer_eq_bot ((conjEquiv A c⁻¹).trans eA), mem_bot] at hmem
  exact h21 hmem

end Inner

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive

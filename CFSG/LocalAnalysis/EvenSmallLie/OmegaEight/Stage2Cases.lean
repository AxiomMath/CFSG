module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2End

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Subgroup

structure CaseData where
  b : GL12
  C2 : Subgroup GL12
  P3 : Subgroup GL12

@[expose] def CaseI (M : Model) (b m : GL12) : Prop :=
  m * M.tbar * m⁻¹ = M.tbar * b ∧ m * b * m⁻¹ = b

@[expose] def CaseII (M : Model) (b m : GL12) : Prop :=
  m * M.tbar * m⁻¹ = b ∧ m * b * m⁻¹ = M.tbar

structure CaseFacts (M : Model) (D : CaseData) : Prop where
  tbar_sq : M.tbar * M.tbar = 1
  tbar_ne_one : M.tbar ≠ 1
  b_sq : D.b * D.b = 1
  b_ne_one : D.b ≠ 1
  b_ne_tbar : D.b ≠ M.tbar
  b_comm : D.b * M.tbar = M.tbar * D.b
  tbar_mem_TC : M.tbar ∈ M.TC
  TC_le_CC : M.TC ≤ M.CC
  TC_pgroup : IsPGroup 2 M.TC
  TC_max : ∀ Y : Subgroup GL12, IsPGroup 2 Y → M.TC ≤ Y → Y ≤ M.CC → Y = M.TC
  tbar_central : ∀ x ∈ M.TC, M.tbar * x = x * M.tbar
  b_central : ∀ x ∈ M.TC, D.b * x = x * D.b
  b_mem_TC : D.b ∈ M.TC
  center : ∀ z ∈ M.TC, (∀ x ∈ M.TC, z * x = x * z) →
    z = 1 ∨ z = M.tbar ∨ z = D.b ∨ z = M.tbar * D.b
  C2_le : D.C2 ≤ M.CC
  C2_comm : ∀ c ∈ D.C2, c * M.tbar = M.tbar * c ∧ c * D.b = D.b * c
  C2_ge : ∀ c ∈ M.CC, c * D.b = D.b * c → c ∈ D.C2
  P3_le : D.P3 ≤ D.C2
  P3_pgroup : IsPGroup 3 D.P3
  P3_index : ¬ 3 ∣ (D.P3.subgroupOf D.C2).index
  card_C2_dvd : Nat.card D.C2 ∣ 2 ^ 7 * 9

section General

variable {H : Type*} [Group H]

theorem exists_mul_normalizes [Finite H] {p : ℕ} [Fact p.Prime] {K P : Subgroup H}
    (hPK : P ≤ K) (hP : IsPGroup p P) (hi : ¬ p ∣ (P.subgroupOf K).index) {m : H}
    (hm : ∀ k ∈ K, m * k * m⁻¹ ∈ K) : ∃ c ∈ K, ∀ y ∈ P, (c * m) * y * (c * m)⁻¹ ∈ P := by
  set P' := P.map (MulAut.conj m).toMonoidHom with hP'
  have hP'K : P' ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hm y (hPK hy)
  have hcard : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hS : IsPGroup p (P.subgroupOf K) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hS' : IsPGroup p (P'.subgroupOf K) :=
    (hP.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hP'K).symm
  have hi' : ¬ p ∣ (P'.subgroupOf K).index := by
    have e1 := Subgroup.card_mul_index (P.subgroupOf K)
    have e2 := Subgroup.card_mul_index (P'.subgroupOf K)
    have c1 : Nat.card (P.subgroupOf K) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    have c2 : Nat.card (P'.subgroupOf K) = Nat.card P' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv
    have : (P'.subgroupOf K).index = (P.subgroupOf K).index := by
      have hpos : 0 < Nat.card P := Nat.card_pos
      rw [c1] at e1
      rw [c2, hcard] at e2
      exact Nat.eq_of_mul_eq_mul_left hpos (e2.trans e1.symm)
    rwa [this]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K (hS'.toSylow hi') (hS.toSylow hi)
  refine ⟨c, c.2, fun y hy => ?_⟩
  have hyK : m * y * m⁻¹ ∈ K := hP'K ⟨y, hy, by simp⟩
  have h1 : (⟨m * y * m⁻¹, hyK⟩ : K) ∈ ((hS'.toSylow hi' : Sylow p K) : Subgroup K) := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.mem_subgroupOf.2 ⟨y, hy, by simp⟩
  have h2 : c * (⟨m * y * m⁻¹, hyK⟩ : K) * c⁻¹ ∈
      ((c • hS'.toSylow hi' : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, h1, by simp [MulAut.conj_apply]⟩
  rw [hc, IsPGroup.toSylow_coe] at h2
  have h3 := Subgroup.mem_subgroupOf.1 h2
  have e : (c : H) * m * y * ((c : H) * m)⁻¹ = c * (m * y * m⁻¹) * (c : H)⁻¹ := by group
  rw [e]
  simpa using h3

theorem exists_odd_pow [Finite H] (g : H) : ∃ r : ℕ, Odd r ∧ ∃ a : ℕ, (g ^ r) ^ (2 ^ a) = 1 := by
  obtain ⟨a, r, hr, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨r, hr, a, ?_⟩
  rw [← pow_mul, mul_comm, ← he, pow_orderOf_eq_one]

theorem pow_conj_of_swap {m u v : H} (hu : m * u * m⁻¹ = v) (hv : m * v * m⁻¹ = u) :
    ∀ n : ℕ, m ^ n * u * (m ^ n)⁻¹ = if Even n then u else v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : m ^ (n + 1) * u * (m ^ (n + 1))⁻¹ = m * (m ^ n * u * (m ^ n)⁻¹) * m⁻¹ := by group
    rw [e, ih]
    by_cases hn : Even n
    · have h1 : ¬ Even (n + 1) := Nat.not_even_iff_odd.2 hn.add_one
      simp only [hn, h1, ↓reduceIte, hu]
    · have h1 : Even (n + 1) := (Nat.not_even_iff_odd.1 hn).add_one
      simp only [hn, h1, ↓reduceIte, hv]

theorem not_three_cycle {m x₀ x₁ x₂ : H} {k : ℕ} (hk : m ^ (2 ^ k) = 1)
    (h0 : m * x₀ * m⁻¹ = x₁) (h1 : m * x₁ * m⁻¹ = x₂) (h2 : m * x₂ * m⁻¹ = x₀)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) : False := by
  have key : ∀ n : ℕ, m ^ n * x₀ * (m ^ n)⁻¹ =
      if n % 3 = 0 then x₀ else if n % 3 = 1 then x₁ else x₂ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : m ^ (n + 1) * x₀ * (m ^ (n + 1))⁻¹ = m * (m ^ n * x₀ * (m ^ n)⁻¹) * m⁻¹ := by
        group
      rw [e, ih]
      rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with hn | hn | hn
      · simp [hn, h0, show (n + 1) % 3 = 1 by omega]
      · simp [hn, h1, show (n + 1) % 3 = 2 by omega]
      · simp [hn, h2, show (n + 1) % 3 = 0 by omega]
  have h3 := key (2 ^ k)
  rw [hk, one_mul, inv_one, mul_one] at h3
  have h4 : (2 ^ k) % 3 ≠ 0 := by
    intro h
    have h5 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    omega
  simp only [h4, ↓reduceIte] at h3
  split_ifs at h3
  · exact h01 h3
  · exact h02 h3

end General

namespace Stage2Hyp

variable {G : Type*} [Group G] {M : Model} {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {D : CaseData}

theorem TC_le_X (h : Stage2Hyp M t TH W φ) : M.TC ≤ Xof W φ := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := h.TC_le y hy
  exact rhoG_mem_Xof (h.TH_le_normalizer hx)

theorem CC_le_X (h : Stage2Hyp M t TH W φ) : M.CC ≤ Xof W φ := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := h.CC_le y hy
  exact rhoG_mem_Xof hg

theorem mem_CC_of_commute (h : Stage2Hyp M t TH W φ) {x : GL12} (hx : x ∈ Xof W φ)
    (hc : x * M.tbar = M.tbar * x) : x ∈ M.CC := by
  obtain ⟨g, hg, rfl⟩ := mem_Xof.1 hx
  exact h.centralizer_le g hg hc

theorem mem_C2_of_commute (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D) {x : GL12}
    (hx : x ∈ Xof W φ) (h1 : x * M.tbar = M.tbar * x) (h2 : x * D.b = D.b * x) : x ∈ D.C2 :=
  hF.C2_ge x (h.mem_CC_of_commute hx h1) h2

theorem C2_le_X (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D) : D.C2 ≤ Xof W φ :=
  hF.C2_le.trans h.CC_le_X

theorem conj_mem_C2 (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D) {x : GL12}
    (hx : x ∈ Xof W φ) (ht : ∀ c ∈ D.C2, c * (x⁻¹ * M.tbar * x) = (x⁻¹ * M.tbar * x) * c)
    (hb : ∀ c ∈ D.C2, c * (x⁻¹ * D.b * x) = (x⁻¹ * D.b * x) * c) {c : GL12} (hc : c ∈ D.C2) :
    x * c * x⁻¹ ∈ D.C2 := by
  refine h.mem_C2_of_commute hF ((Xof W φ).mul_mem ((Xof W φ).mul_mem hx (h.C2_le_X hF hc))
    ((Xof W φ).inv_mem hx)) ?_ ?_
  · calc x * c * x⁻¹ * M.tbar = x * (c * (x⁻¹ * M.tbar * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * M.tbar * x) * c) * x⁻¹ := by rw [ht c hc]
      _ = M.tbar * (x * c * x⁻¹) := by group
  · calc x * c * x⁻¹ * D.b = x * (c * (x⁻¹ * D.b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * D.b * x) * c) * x⁻¹ := by rw [hb c hc]
      _ = D.b * (x * c * x⁻¹) := by group

theorem comm_tb (hF : CaseFacts M D) {c : GL12} (hc : c ∈ D.C2) :
    c * (M.tbar * D.b) = (M.tbar * D.b) * c := by
  obtain ⟨h1, h2⟩ := hF.C2_comm c hc
  calc c * (M.tbar * D.b) = (c * M.tbar) * D.b := by group
    _ = M.tbar * (c * D.b) := by rw [h1]; group
    _ = (M.tbar * D.b) * c := by rw [h2]; group

theorem caseI_inv (hF : CaseFacts M D) {m : GL12} (hm : CaseI M D.b m) :
    m⁻¹ * M.tbar * m = M.tbar * D.b ∧ m⁻¹ * D.b * m = D.b := by
  obtain ⟨h1, h2⟩ := hm
  have hb : m⁻¹ * D.b * m = D.b := by
    calc m⁻¹ * D.b * m = m⁻¹ * (m * D.b * m⁻¹) * m := by rw [h2]
      _ = D.b := by group
  refine ⟨?_, hb⟩
  have e : m * (M.tbar * D.b) * m⁻¹ = M.tbar := by
    calc m * (M.tbar * D.b) * m⁻¹ = (m * M.tbar * m⁻¹) * (m * D.b * m⁻¹) := by group
      _ = M.tbar := by rw [h1, h2, mul_assoc, hF.b_sq, mul_one]
  calc m⁻¹ * M.tbar * m = m⁻¹ * (m * (M.tbar * D.b) * m⁻¹) * m := by rw [e]
    _ = M.tbar * D.b := by group

theorem caseII_inv {m : GL12} (hm : CaseII M D.b m) :
    m⁻¹ * M.tbar * m = D.b ∧ m⁻¹ * D.b * m = M.tbar := by
  obtain ⟨h1, h2⟩ := hm
  constructor
  · calc m⁻¹ * M.tbar * m = m⁻¹ * (m * D.b * m⁻¹) * m := by rw [h2]
      _ = D.b := by group
  · calc m⁻¹ * D.b * m = m⁻¹ * (m * M.tbar * m⁻¹) * m := by rw [h1]
      _ = M.tbar := by group

theorem conj_mem_C2_of_case (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D) {m : GL12}
    (hmX : m ∈ Xof W φ) (hm : CaseI M D.b m ∨ CaseII M D.b m) {c : GL12} (hc : c ∈ D.C2) :
    m * c * m⁻¹ ∈ D.C2 := by
  rcases hm with hm | hm
  · obtain ⟨e1, e2⟩ := caseI_inv hF hm
    exact h.conj_mem_C2 hF hmX (fun c hc => by rw [e1]; exact comm_tb hF hc)
      (fun c hc => by rw [e2]; exact (hF.C2_comm c hc).2) hc
  · obtain ⟨e1, e2⟩ := caseII_inv hm
    exact h.conj_mem_C2 hF hmX (fun c hc => by rw [e1]; exact (hF.C2_comm c hc).2)
      (fun c hc => by rw [e2]; exact (hF.C2_comm c hc).1) hc

theorem exists_case [Finite G] (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D)
    (hnd : ¬ ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → M.TC ≤ Z → Z = M.TC) :
    ∃ m ∈ Xof W φ, CaseI M D.b m ∨ CaseII M D.b m := by
  push Not at hnd
  obtain ⟨Y, hYX, hY2, hTCY, hne⟩ := hnd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmY, hmT, hmN⟩ := exists_mem_normalizer_of_lt hY2 hTCY (Ne.symm hne)
  have hmX := hYX hmY
  obtain ⟨k, hk⟩ := hY2 ⟨m, hmY⟩
  have hk' : m ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcent : ∀ z ∈ M.TC, (∀ x ∈ M.TC, z * x = x * z) →
      m * z * m⁻¹ ∈ M.TC ∧ ∀ x ∈ M.TC, (m * z * m⁻¹) * x = x * (m * z * m⁻¹) := by
    intro z hz hzc
    refine ⟨(Subgroup.mem_normalizer_iff.1 hmN z).1 hz, fun x hx => ?_⟩
    have hx' : m⁻¹ * x * m ∈ M.TC := by
      refine (Subgroup.mem_normalizer_iff.1 hmN (m⁻¹ * x * m)).2 ?_
      have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rw [e]
      exact hx
    have e2 := hzc _ hx'
    calc m * z * m⁻¹ * x = m * (z * (m⁻¹ * x * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * x * m) * z) * m⁻¹ := by rw [e2]
      _ = x * (m * z * m⁻¹) := by group
  obtain ⟨huT, huc⟩ := hcent M.tbar hF.tbar_mem_TC hF.tbar_central
  obtain ⟨hvT, hvc⟩ := hcent D.b hF.b_mem_TC hF.b_central
  have hu := hF.center _ huT huc
  have hv := hF.center _ hvT hvc
  have hinj : ∀ x y : GL12, m * x * m⁻¹ = m * y * m⁻¹ → x = y := fun x y e => by
    simpa using e
  have hu1 : m * M.tbar * m⁻¹ ≠ 1 := fun e => hF.tbar_ne_one (hinj _ _ (e.trans (by group)))
  have hut : m * M.tbar * m⁻¹ ≠ M.tbar := by
    intro e
    have hmC : m ∈ M.CC := h.mem_CC_of_commute hmX (by
      calc m * M.tbar = m * M.tbar * m⁻¹ * m := by group
        _ = M.tbar * m := by rw [e])
    have h2 : IsPGroup 2 (M.TC ⊔ zpowers m : Subgroup GL12) :=
      IsPGroup.to_sup_of_normal_left' hF.TC_pgroup (hY2.to_le ((zpowers_le).2 hmY))
        ((zpowers_le).2 hmN)
    have h3 := hF.TC_max _ h2 le_sup_left (sup_le hF.TC_le_CC ((zpowers_le).2 hmC))
    exact hmT (h3 ▸ (le_sup_right : zpowers m ≤ M.TC ⊔ zpowers m) (mem_zpowers m))
  have hv1 : m * D.b * m⁻¹ ≠ 1 := fun e => hF.b_ne_one (hinj _ _ (e.trans (by group)))
  have hvu : m * D.b * m⁻¹ ≠ m * M.tbar * m⁻¹ := fun e => hF.b_ne_tbar (hinj _ _ e)
  have htb : m * (M.tbar * D.b) * m⁻¹ = (m * M.tbar * m⁻¹) * (m * D.b * m⁻¹) := by group
  have hbb : D.b ≠ M.tbar * D.b := fun e => hF.tbar_ne_one (by
    calc M.tbar = M.tbar * D.b * D.b := by rw [mul_assoc, hF.b_sq, mul_one]
      _ = 1 := by rw [← e, hF.b_sq])
  have htt : M.tbar ≠ M.tbar * D.b := fun e => hF.b_ne_one (by
    calc D.b = M.tbar * (M.tbar * D.b) := by rw [← mul_assoc, hF.tbar_sq, one_mul]
      _ = 1 := by rw [← e, hF.tbar_sq])
  refine ⟨m, hmX, ?_⟩
  rcases hu with hu | hu | hu | hu
  · exact absurd hu hu1
  · exact absurd hu hut
  ·
    rcases hv with hv | hv | hv | hv
    · exact absurd hv hv1
    · exact Or.inr ⟨hu, hv⟩
    · exact absurd (hv.trans hu.symm) hvu
    · exfalso
      refine not_three_cycle hk' hu hv ?_ hF.b_ne_tbar.symm htt
      rw [htb, hu, hv, ← mul_assoc, hF.b_comm, mul_assoc, hF.b_sq, mul_one]
  ·
    rcases hv with hv | hv | hv | hv
    · exact absurd hv hv1
    · exfalso
      have h5 : m * (M.tbar * D.b) * m⁻¹ = D.b := by
        rw [htb, hu, hv, mul_assoc, hF.b_comm, ← mul_assoc, hF.tbar_sq, one_mul]
      exact not_three_cycle hk' hu h5 hv htt hF.b_ne_tbar.symm
    · exact Or.inl ⟨hu, hv⟩
    · exact absurd (hv.trans hu.symm) hvu

theorem case_mul (hF : CaseFacts M D) {c m : GL12} (hc : c ∈ D.C2)
    (hm : CaseI M D.b m ∨ CaseII M D.b m) : CaseI M D.b (c * m) ∨ CaseII M D.b (c * m) := by
  obtain ⟨h1, h2⟩ := hF.C2_comm c hc
  have hct : c * M.tbar * c⁻¹ = M.tbar := by rw [h1]; group
  have hcb : c * D.b * c⁻¹ = D.b := by rw [h2]; group
  have hctb : c * (M.tbar * D.b) * c⁻¹ = M.tbar * D.b := by rw [comm_tb hF hc]; group
  have e : ∀ x : GL12, c * m * x * (c * m)⁻¹ = c * (m * x * m⁻¹) * c⁻¹ := fun x => by group
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨by rw [e, e1, hctb], by rw [e, e2, hcb]⟩
  · exact Or.inr ⟨by rw [e, e1, hcb], by rw [e, e2, hct]⟩

theorem case_swaps (hF : CaseFacts M D) {m : GL12} (hm : CaseI M D.b m ∨ CaseII M D.b m) :
    ∃ u v : GL12, (m * M.tbar * m⁻¹ = u ∧ m * u * m⁻¹ = M.tbar) ∧
      (m * D.b * m⁻¹ = v ∧ m * v * m⁻¹ = D.b) ∧
      ((u = M.tbar * D.b ∧ v = D.b) ∨ (u = D.b ∧ v = M.tbar)) := by
  rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨M.tbar * D.b, D.b, ⟨e1, ?_⟩, ⟨e2, e2⟩, Or.inl ⟨rfl, rfl⟩⟩
    have : m * (M.tbar * D.b) * m⁻¹ = (m * M.tbar * m⁻¹) * (m * D.b * m⁻¹) := by group
    rw [this, e1, e2, mul_assoc, hF.b_sq, mul_one]
  · exact ⟨D.b, M.tbar, ⟨e1, e2⟩, ⟨e2, e1⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem case_pow (hF : CaseFacts M D) {m : GL12} (hm : CaseI M D.b m ∨ CaseII M D.b m) {r : ℕ}
    (hr : Odd r) : CaseI M D.b (m ^ r) ∨ CaseII M D.b (m ^ r) := by
  obtain ⟨u, v, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩, huv⟩ := case_swaps hF hm
  have h1 := pow_conj_of_swap hu1 hu2 r
  have h2 := pow_conj_of_swap hv1 hv2 r
  have hne : ¬ Even r := Nat.not_even_iff_odd.2 hr
  simp only [hne, ↓reduceIte] at h1 h2
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

theorem sq_commute_of_case (hF : CaseFacts M D) {m : GL12}
    (hm : CaseI M D.b m ∨ CaseII M D.b m) :
    m * m * M.tbar = M.tbar * (m * m) ∧ m * m * D.b = D.b * (m * m) := by
  obtain ⟨u, v, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩, -⟩ := case_swaps hF hm
  have h1 := pow_conj_of_swap hu1 hu2 2
  have h2 := pow_conj_of_swap hv1 hv2 2
  simp only [even_two, ↓reduceIte, sq] at h1 h2
  constructor
  · calc m * m * M.tbar = m * m * M.tbar * (m * m)⁻¹ * (m * m) := by group
      _ = M.tbar * (m * m) := by rw [h1]
  · calc m * m * D.b = m * m * D.b * (m * m)⁻¹ * (m * m) := by group
      _ = D.b * (m * m) := by rw [h2]

theorem pow_normalizes {P : Subgroup GL12} {m : GL12} (hm : ∀ y ∈ P, m * y * m⁻¹ ∈ P) :
    ∀ n : ℕ, ∀ y ∈ P, m ^ n * y * (m ^ n)⁻¹ ∈ P := by
  intro n
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    have e : m ^ (n + 1) * y * (m ^ (n + 1))⁻¹ = m * (m ^ n * y * (m ^ n)⁻¹) * m⁻¹ := by group
    rw [e]
    exact hm _ (ih y hy)

theorem pow_256_eq_one (hF : CaseFacts M D) {m : GL12} (hm2 : m * m ∈ D.C2) {a : ℕ}
    (ha : m ^ (2 ^ a) = 1) : m ^ 256 = 1 := by
  have h1 : (m * m) ^ Nat.card D.C2 = 1 := by
    have h := pow_card_eq_one' (G := D.C2) (x := ⟨m * m, hm2⟩)
    have h' := congrArg (fun z : D.C2 => (z : GL12)) h
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    exact h'
  obtain ⟨q, hq⟩ := hF.card_C2_dvd
  have h2 : m ^ (2 ^ 8 * 9) = 1 := by
    have e : 2 ^ 8 * 9 = 2 * Nat.card D.C2 * q := by rw [mul_assoc, ← hq]; norm_num
    rw [e, pow_mul, pow_mul, sq, h1, one_pow]
  have h3 : orderOf m ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
  have h4 : orderOf m ∣ 2 ^ 8 * 9 := orderOf_dvd_of_pow_eq_one h2
  rw [hj] at h4
  have hcop : Nat.Coprime (2 ^ j) 9 := Nat.Coprime.pow_left _ (by norm_num)
  have h5 : 2 ^ j ∣ 2 ^ 8 := hcop.dvd_of_dvd_mul_right h4
  rw [← hj] at h5
  exact orderOf_dvd_iff_pow_eq_one.1 (by simpa using h5)

theorem degenerate_or_exists [Finite G] (h : Stage2Hyp M t TH W φ) (hF : CaseFacts M D) :
    (∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → M.TC ≤ Z → Z = M.TC) ∨
    ∃ m ∈ Xof W φ, (CaseI M D.b m ∨ CaseII M D.b m) ∧ (∀ y ∈ D.P3, m * y * m⁻¹ ∈ D.P3) ∧
      m * m ∈ D.C2 ∧ m ^ 256 = 1 ∧ ∀ c ∈ D.C2, m * c * m⁻¹ ∈ D.C2 := by
  by_cases hnd : ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → M.TC ≤ Z → Z = M.TC
  · exact Or.inl hnd
  right
  obtain ⟨m₀, hm₀X, hm₀⟩ := h.exists_case hF hnd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hcC, hc⟩ := exists_mul_normalizes hF.P3_le hF.P3_pgroup hF.P3_index
    (fun k hk => h.conj_mem_C2_of_case hF hm₀X hm₀ hk)
  have hm₁X : c * m₀ ∈ Xof W φ := (Xof W φ).mul_mem (h.C2_le_X hF hcC) hm₀X
  have hm₁ := case_mul hF hcC hm₀
  obtain ⟨r, hr, a, ha⟩ := exists_odd_pow (c * m₀)
  have hm₂X : (c * m₀) ^ r ∈ Xof W φ := (Xof W φ).pow_mem hm₁X r
  have hm₂ := case_pow hF hm₁ hr
  have hsq := sq_commute_of_case hF hm₂
  have hm₂2 : (c * m₀) ^ r * (c * m₀) ^ r ∈ D.C2 :=
    h.mem_C2_of_commute hF ((Xof W φ).mul_mem hm₂X hm₂X) hsq.1 hsq.2
  exact ⟨_, hm₂X, hm₂, pow_normalizes hc r, hm₂2, pow_256_eq_one hF hm₂2 ha,
    fun c' hc' => h.conj_mem_C2_of_case hF hm₂X hm₂ hc'⟩

end Stage2Hyp

end CFSG.EvenSmallLie.OmegaEight.Stage2

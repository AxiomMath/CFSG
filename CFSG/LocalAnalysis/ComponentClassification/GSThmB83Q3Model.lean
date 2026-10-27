module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Odd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Q3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8A6
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuot
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem card_of_isSec8JType_three {Y : Type} [Group Y] (hY : IsSec8JType Y 3 1) :
    Nat.card Y = 360 := by
  rcases hY with h | ⟨-, -, ⟨e⟩⟩
  · rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · rw [Nat.card_congr e.toEquiv,
        Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
      decide
    all_goals omega
  · have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h2
    rw [Nat.card_congr e.toEquiv]
    have : Nat.factorial 6 = 720 := by decide
    omega

theorem sylow_subgroupOf_iff {G : Type*} [Group G] [Finite G] {M Y R : Subgroup G}
    (hYM : Y ≤ M) :
    (∃ T : Sylow 2 ↥Y, (T : Subgroup Y) = R.subgroupOf Y) ↔
      ∃ T : Sylow 2 ↥(Y.subgroupOf M),
        (T : Subgroup _) = (R.subgroupOf M).subgroupOf (Y.subgroupOf M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥(Y.subgroupOf M) ≃* ↥Y := subgroupOfEquivOfLe hYM
  have key : ∀ (y : ↥(Y.subgroupOf M)), (y ∈ (R.subgroupOf M).subgroupOf (Y.subgroupOf M) ↔
      e y ∈ R.subgroupOf Y) := fun y => Iff.rfl
  have hf1 : Function.Surjective e.symm.toMonoidHom := fun y => ⟨e y, by simp⟩
  have hf2 : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, by simp⟩
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T.mapSurjective hf1, ?_⟩
    rw [Sylow.coe_mapSurjective, hT]
    ext y
    simp only [mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [key]
      simpa using hw
    · intro hy
      exact ⟨e y, (key y).mp hy, by simp⟩
  · rintro ⟨T, hT⟩
    refine ⟨T.mapSurjective hf2, ?_⟩
    rw [Sylow.coe_mapSurjective, hT]
    ext y
    simp only [mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (key w).mp hw
    · intro hy
      exact ⟨e.symm y, (key _).mpr (by simpa using hy), by simp⟩

theorem isPGroup_zpowers_of_mul_self {G : Type*} [Group G] {g : G} (hg : g * g = 1) :
    IsPGroup 2 (zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  change (g ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hg, one_zpow]

theorem isPGroup_sup_zpowers {G : Type*} [Group G] {Q : Subgroup G} {g : G} (hQ : IsPGroup 2 Q)
    (hg : g ∈ normalizer (Q : Set G)) (hg2 : g * g ∈ Q) : IsPGroup 2 ↥(Q ⊔ zpowers g) := by
  have hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hg q).mp hq
  have hginvQ : ∀ q ∈ Q, g⁻¹ * q * g ∈ Q := fun q hq => by
    have := (mem_normalizer_iff.mp (inv_mem hg) q).mp hq
    rwa [inv_inv] at this
  let N : Subgroup G :=
    { carrier := {y | ∃ q ∈ Q, y = q ∨ y = q * g}
      mul_mem' := by
        rintro y z ⟨q, hq, hy⟩ ⟨r, hr, hz⟩
        rcases hy with hy | hy <;> rcases hz with hz | hz <;> rw [hy, hz]
        · exact ⟨q * r, mul_mem hq hr, Or.inl rfl⟩
        · exact ⟨q * r, mul_mem hq hr, Or.inr (by group)⟩
        · exact ⟨q * (g * r * g⁻¹), mul_mem hq (hgQ r hr), Or.inr (by group)⟩
        · refine ⟨q * (g * r * g⁻¹) * (g * g), mul_mem (mul_mem hq (hgQ r hr)) hg2, Or.inl ?_⟩
          group
      one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
      inv_mem' := by
        rintro y ⟨q, hq, hy⟩
        rcases hy with hy | hy <;> rw [hy]
        · exact ⟨q⁻¹, inv_mem hq, Or.inl rfl⟩
        · refine ⟨(g⁻¹ * q⁻¹ * g) * (g * g)⁻¹, mul_mem (hginvQ _ (inv_mem hq)) (inv_mem hg2),
            Or.inr ?_⟩
          group }
  have hle : Q ⊔ zpowers g ≤ N := by
    refine sup_le (fun q hq => ⟨q, hq, Or.inl rfl⟩) ?_
    rw [zpowers_le]
    exact ⟨1, one_mem _, Or.inr (one_mul g).symm⟩
  rintro ⟨y, hy⟩
  obtain ⟨q, hq, hyq⟩ := hle hy
  have hy2 : y * y ∈ Q := by
    rcases hyq with hyq | hyq <;> rw [hyq]
    · exact mul_mem hq hq
    · rw [show q * g * (q * g) = q * (g * q * g⁻¹) * (g * g) by group]
      exact mul_mem (mul_mem hq (hgQ q hq)) hg2
  obtain ⟨k, hk⟩ := hQ ⟨y * y, hy2⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  change y ^ 2 ^ (k + 1) = 1
  have := congrArg Subtype.val hk
  simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
  rw [pow_succ', pow_mul, pow_two]
  exact this

theorem eq_of_sylow_of_le {G : Type*} [Group G] [Finite G] {S Y R : Subgroup G}
    (hS : ∃ T : Sylow 2 ↥Y, (T : Subgroup Y) = S.subgroupOf Y) (hSR : S ≤ R) (hRY : R ≤ Y)
    (hR : IsPGroup 2 R) : R = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hS
  have hSY : S ≤ Y := hSR.trans hRY
  have h1 := T.is_maximal' (Q := R.subgroupOf Y) hR.comap_subtype (by
    rw [hT]
    exact fun x hx => hSR hx)
  rw [hT] at h1
  apply le_antisymm _ hSR
  intro x hx
  have : (⟨x, hRY hx⟩ : Y) ∈ R.subgroupOf Y := hx
  rw [h1] at this
  exact this

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

@[expose] def IsQ3 : Prop :=
  IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) 3 1 ∧ IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) 3 1

abbrev M3 : Subgroup X := h.K ⊔ zpowers h.a

theorem a_mem_M3 : h.a ∈ h.M3 := mem_sup_right (mem_zpowers h.a)

abbrev aM : ↥h.M3 := ⟨h.a, h.a_mem_M3⟩

theorem M3_le_normalizer : h.M3 ≤ normalizer (h.B : Set X) :=
  sup_le h.isPComponent_K.1 (zpowers_le.mpr h.a_mem_normalizer)

theorem subgroupOf_centralizer_eq :
    (h.M3 ⊓ centralizer ({h.a} : Set X)).subgroupOf h.M3 =
      centralizer ({h.aM} : Set ↥h.M3) := by
  ext m
  rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hm⟩
    exact Subtype.ext hm
  · intro hm
    exact ⟨m.2, congrArg Subtype.val hm⟩

theorem sec8_isPGroup_Q : IsPGroup 2 h.Q := (Six.isPGroup_S h).to_le inf_le_left

theorem aM_mul_self : h.aM * h.aM = 1 := Subtype.ext (Six.a_mul_a_self h)

namespace L83Hyp

variable {h} (H : L83Hyp h)
include H

noncomputable abbrev rho : ↥h.M3 →* MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  Eight.modelHom h.K H.a_mem_normalizer_K

theorem rho_aM : H.rho h.aM = H.rhoA := rfl

theorem rhoA_mul_self : H.rhoA * H.rhoA = 1 := by
  rw [← rho_aM, ← map_mul]
  rw [show (h.aM : ↥h.M3) * h.aM = 1 from Subtype.ext (Six.a_mul_a_self h), map_one]

theorem rhoA_adm (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    Cat8.IsAdm (h.K ⧸ pPrimeCore 2 h.K) H.rhoA where
  sq := H.rhoA_mul_self
  out := H.rhoA_not_mem_inner hCF1 hCF2
  dvd := by
    have h1 := H.card_J_dvd_card_fix
    rwa [card_of_isSec8JType_three hq.2] at h1

theorem rho_of_mem_K {k : X} (hk : k ∈ h.K) :
    H.rho ⟨k, mem_sup_left hk⟩ = MulAut.conj (((⟨k, hk⟩ : h.K)) : h.K ⧸ pPrimeCore 2 h.K) :=
  Eight.modelHom_of_mem_K h.K H.a_mem_normalizer_K ⟨k, hk⟩

theorem mem_K_iff (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (m : ↥h.M3) :
    (m : X) ∈ h.K ↔ H.rho m ∈ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) := by
  constructor
  · intro hm
    have : m = ⟨(m : X), mem_sup_left hm⟩ := rfl
    rw [this, H.rho_of_mem_K hm]
    exact ⟨_, rfl⟩
  · intro hm
    obtain ⟨k, hk, hmk⟩ := Eight.mem_sup_zpowers_cases H.a_mem_normalizer_K (Six.a_mul_a_self h)
      m.2
    rcases hmk with hmk | hmk
    · rw [hmk]
      exact hk
    · exfalso
      apply H.rhoA_not_mem_inner hCF1 hCF2
      have hm' : m = ⟨k, mem_sup_left hk⟩ * h.aM := Subtype.ext hmk
      rw [hm', map_mul, H.rho_of_mem_K hk, rho_aM] at hm
      obtain ⟨y, hy⟩ := hm
      refine ⟨(((⟨k, hk⟩ : h.K)) : h.K ⧸ pPrimeCore 2 h.K)⁻¹ * y, ?_⟩
      rw [map_mul, hy, map_inv, inv_mul_cancel_left]

theorem rho_range (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : H.rho.range = ⊤ := by
  rw [Eight.range_modelHom h.K H.a_mem_normalizer_K (Six.a_mul_a_self h)]
  exact hOut _ hq.1 _ (H.rhoA_adm hq hCF1 hCF2)

theorem rho_surjective (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : Function.Surjective H.rho :=
  MonoidHom.range_eq_top.mp (H.rho_range hq hCF1 hCF2 hOut)

theorem normalizer_le_normalizer_K : normalizer (h.B : Set X) ≤ normalizer (h.K : Set X) := by
  have := OddQuot.le_normalizer_layerIn (normalizer (h.B : Set X))
  rwa [show layerIn (normalizer (h.B : Set X)) = h.K from H.V_eq_K] at this

theorem Q1_sylow :
    h.Q.subgroupOf h.M3 ≤ centralizer ({h.aM} : Set ↥h.M3) ∧
      ∃ T : Sylow 2 ↥(centralizer ({h.aM} : Set ↥h.M3)),
        (T : Subgroup _) = (h.Q.subgroupOf h.M3).subgroupOf (centralizer ({h.aM} : Set ↥h.M3)) := by
  obtain ⟨hQY, hQ⟩ := h.sec8_Q_sylow H.J_normal
  set N := centralizer ({h.a} : Set X) ⊓ normalizer (h.B : Set X) with hN
  set C := h.M3 ⊓ centralizer ({h.a} : Set X) with hCdef
  have hCN : C ≤ N := le_inf inf_le_right (inf_le_left.trans h.M3_le_normalizer)
  have hNC : N ≤ normalizer (C : Set X) := by
    refine le_normalizer_of_conj fun y hy w hw => ?_
    have hyK : y ∈ normalizer (h.K : Set X) := H.normalizer_le_normalizer_K hy.2
    have hya : y * h.a = h.a * y := mem_centralizer_singleton_iff.mp hy.1
    have hwa : w * h.a = h.a * w := mem_centralizer_singleton_iff.mp hw.2
    refine ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · obtain ⟨k, hk, hwk⟩ := Eight.mem_sup_zpowers_cases H.a_mem_normalizer_K
        (Six.a_mul_a_self h) hw.1
      have hyk : y * k * y⁻¹ ∈ h.K := (mem_normalizer_iff.mp hyK k).mp hk
      rcases hwk with rfl | rfl
      · exact mem_sup_left hyk
      · rw [show y * (k * h.a) * y⁻¹ = (y * k * y⁻¹) * (y * h.a * y⁻¹) by group,
          show y * h.a * y⁻¹ = h.a by rw [hya, mul_inv_cancel_right]]
        exact mul_mem (mem_sup_left hyk) h.a_mem_M3
    · calc y * w * y⁻¹ * h.a = y * w * (y⁻¹ * h.a * y) * y⁻¹ := by group
        _ = y * w * h.a * y⁻¹ := by
            rw [show y⁻¹ * h.a * y = h.a by rw [mul_assoc, ← hya, inv_mul_cancel_left]]
        _ = y * h.a * w * y⁻¹ := by rw [mul_assoc y w, hwa, ← mul_assoc]
        _ = h.a * (y * w * y⁻¹) := by rw [hya]; group
  obtain ⟨T, hT⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hQY hQ hCN
    hNC
  have hQa : h.Q ≤ centralizer ({h.a} : Set X) := hQY.trans inf_le_left
  have hQC : h.Q ⊓ C = h.Q ⊓ h.M3 := by
    rw [hCdef, ← inf_assoc, inf_right_comm, inf_eq_left.mpr hQa]
  rw [hQC] at hT
  have h1 := (sylow_subgroupOf_iff (M := h.M3) (Y := C) (R := h.Q ⊓ h.M3) inf_le_left).mp ⟨T, hT⟩
  rw [h.subgroupOf_centralizer_eq] at h1
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [← h.subgroupOf_centralizer_eq]
    exact ⟨m.2, hQa hm⟩
  · rw [inf_subgroupOf_right] at h1
    exact h1

theorem map_centralizer_aM (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) :
    (centralizer ({h.aM} : Set ↥h.M3)).map H.rho =
      centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
  have hA : IsPGroup 2 (zpowers h.aM) := isPGroup_zpowers_of_mul_self h.aM_mul_self
  have h1 := Eight.map_centralizer_eq (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) hA
  rw [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq,
    H.rho_range hq hCF1 hCF2 hOut, top_inf_eq] at h1
  exact h1

theorem Q1hat_sylow (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) :
    (h.Q.subgroupOf h.M3).map H.rho ≤
        centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) ∧
      ∃ T : Sylow 2 ↥(centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))),
        (T : Subgroup _) = ((h.Q.subgroupOf h.M3).map H.rho).subgroupOf
          (centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))) := by
  obtain ⟨hle, hS⟩ := H.Q1_sylow
  have h1 := OddQuot.exists_sylow_map H.rho hle hS
  rw [H.map_centralizer_aM hq hCF1 hCF2 hOut] at h1
  refine ⟨?_, h1⟩
  rw [← H.map_centralizer_aM hq hCF1 hCF2 hOut]
  exact map_mono hle

theorem exists_g (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (hF2 : CFQ3F2) :
    ∃ g : ↥h.M3, (g : X) ∈ h.K ∧ g ∈ normalizer ((h.Q.subgroupOf h.M3 : Subgroup ↥h.M3) :
        Set ↥h.M3) ∧ g ∉ h.Q.subgroupOf h.M3 ∧ g * g ∈ h.Q.subgroupOf h.M3 ∧
      ((h.aM * (g⁻¹ * h.aM * g) : ↥h.M3) : X) ∈ h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  set Q1 : Subgroup ↥h.M3 := h.Q.subgroupOf h.M3 with hQ1
  have hQ1₂ : IsPGroup 2 Q1 := h.sec8_isPGroup_Q.comap_subtype
  obtain ⟨hQle, hQS⟩ := H.Q1hat_sylow hq hCF1 hCF2 hOut
  obtain ⟨gh, hgInn, hgN, hgQ, hgsq, htau⟩ :=
    hF2 _ hq.1 _ (H.rhoA_adm hq hCF1 hCF2) (Q1.map H.rho) hQle hQS
  have hgmem : gh ∈ (normalizer (Q1 : Set ↥h.M3)).map H.rho := by
    rw [Eight.map_normalizer_eq hker hQ1₂, H.rho_range hq hCF1 hCF2 hOut, top_inf_eq]
    exact hgN
  obtain ⟨g₁, hg₁N, hg₁⟩ := mem_map.mp hgmem
  set T₁ : Subgroup ↥h.M3 := Q1 ⊔ zpowers g₁ with hT₁
  have hT₁N : T₁ ≤ normalizer (Q1 : Set ↥h.M3) := sup_le le_normalizer (zpowers_le.mpr hg₁N)
  have hT₁map : T₁.map H.rho = Q1.map H.rho ⊔ zpowers gh := by
    rw [hT₁, Subgroup.map_sup, MonoidHom.map_zpowers, hg₁]
  have hT₁map₂ : IsPGroup 2 (T₁.map H.rho) := by
    rw [hT₁map]
    exact isPGroup_sup_zpowers (hQ1₂.map H.rho) hgN hgsq
  obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow 2 ↥T₁))
  set T₂ : Subgroup ↥h.M3 := (P₂ : Subgroup ↥T₁).map T₁.subtype with hT₂
  have hT₂₂ : IsPGroup 2 T₂ := P₂.isPGroup'.map T₁.subtype
  have hT₂T₁ : T₂ ≤ T₁ := map_subtype_le _
  have hQT₂ : Q1 ≤ T₂ := by
    have hn : (Q1.subgroupOf T₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer (le_sup_left : Q1 ≤ T₁)).mpr hT₁N
    have : (Q1.comap T₁.subtype).Normal := hn
    have h1 := (hQ1₂.comap_subtype (K := T₁)).le_sylow_of_normal P₂
    intro x hx
    exact ⟨⟨x, (le_sup_left : Q1 ≤ T₁) hx⟩, h1 hx, rfl⟩
  have hT₂map : T₂.map H.rho = T₁.map H.rho := by
    have hS : ∃ T : Sylow 2 ↥T₁, (T : Subgroup T₁) = T₂.subgroupOf T₁ :=
      ⟨P₂, (comap_map_eq_self_of_injective T₁.subtype_injective _).symm⟩
    obtain ⟨T, hT⟩ := OddQuot.exists_sylow_map H.rho hT₂T₁ hS
    exact (eq_of_sylow_of_le ⟨T, hT⟩ (map_mono hT₂T₁) le_rfl hT₁map₂).symm
  have hgT₁ : gh ∈ T₁.map H.rho := by
    rw [hT₁map]
    exact mem_sup_right (mem_zpowers gh)
  rw [← hT₂map] at hgT₁
  obtain ⟨g, hgT₂, hgg⟩ := mem_map.mp hgT₁
  have hgN' : g ∈ normalizer (Q1 : Set ↥h.M3) := hT₁N (hT₂T₁ hgT₂)
  refine ⟨g, (H.mem_K_iff hCF1 hCF2 g).mpr (hgg ▸ hgInn), hgN', fun hgQ1 => hgQ ?_, ?_, ?_⟩
  · rw [← hgg]
    exact mem_map_of_mem _ hgQ1
  · refine Eight.mem_of_map_mem hker hT₂₂ hQT₂ (mul_mem hgT₂ hgT₂) ?_
    rw [map_mul, hgg]
    exact hgsq
  · rw [H.mem_K_iff hCF1 hCF2, map_mul, map_mul, map_mul, map_inv, hgg, H.rho_aM]
    exact htau

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

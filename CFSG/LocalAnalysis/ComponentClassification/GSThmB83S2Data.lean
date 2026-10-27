module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83P4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

theorem rho_range_eq (H : L83Hyp h) :
    H.rho.range = Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA :=
  Eight.range_modelHom h.K H.a_mem_normalizer_K (Six.a_mul_a_self h)

theorem rhoA_admQ (H : L83Hyp h) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hJ : IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f) :
    Cat8.IsAdmQ (h.K ⧸ pPrimeCore 2 h.K) (p ^ f) H.rhoA where
  sq := H.rhoA_mul_self
  out := H.rhoA_not_mem_inner hCF1 hCF2
  dvd := by
    have h1 := H.card_J_dvd_card_fix
    rwa [hJo _ p f hp hp2 hf hJ] at h1

theorem map_centralizer_aM_gen (H : L83Hyp h) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) :
    (centralizer ({h.aM} : Set ↥h.M3)).map H.rho =
      (Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA) ⊓
        centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
  have hA : IsPGroup 2 (zpowers h.aM) := isPGroup_zpowers_of_mul_self h.aM_mul_self
  have h1 := Eight.map_centralizer_eq (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) hA
  rw [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq,
    H.rho_range_eq] at h1
  exact h1

theorem Q1hat_sylow_gen (H : L83Hyp h) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    (h.Q.subgroupOf h.M3).map H.rho ≤ (Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA) ⊓
        centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) ∧
      ∃ T : Sylow 2 ↥((Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA) ⊓
        centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))),
        (T : Subgroup _) = ((h.Q.subgroupOf h.M3).map H.rho).subgroupOf
          ((Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA) ⊓
            centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))) := by
  obtain ⟨hle, hS⟩ := H.Q1_sylow
  have h1 := OddQuot.exists_sylow_map H.rho hle hS
  rw [H.map_centralizer_aM_gen hCF1 hCF2] at h1
  refine ⟨?_, h1⟩
  rw [← H.map_centralizer_aM_gen hCF1 hCF2]
  exact map_mono hle

theorem exists_g_gen (H : L83Hyp h) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hF2 : CFSp4F2) :
    ∃ g : ↥h.M3, (g : X) ∈ h.K ∧ g ∈ normalizer ((h.Q.subgroupOf h.M3 : Subgroup ↥h.M3) :
        Set ↥h.M3) ∧ g ∉ h.Q.subgroupOf h.M3 ∧ g * g ∈ h.Q.subgroupOf h.M3 ∧
      ((h.aM * (g⁻¹ * h.aM * g) : ↥h.M3) : X) ∈ h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.sec8Case
  set Q1 : Subgroup ↥h.M3 := h.Q.subgroupOf h.M3 with hQ1
  have hQ1₂ : IsPGroup 2 Q1 := h.sec8_isPGroup_Q.comap_subtype
  obtain ⟨hQle, hQS⟩ := H.Q1hat_sylow_gen hCF1 hCF2
  obtain ⟨gh, hgInn, hgN, hgQ, hgsq, htau⟩ :=
    hF2 _ p f hp hp2 hf hK _ (H.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ) (Q1.map H.rho) hQle hQS
  have hgmem : gh ∈ (normalizer (Q1 : Set ↥h.M3)).map H.rho := by
    rw [Eight.map_normalizer_eq hker hQ1₂, H.rho_range_eq]
    exact Subgroup.mem_inf.mpr ⟨mem_sup_left hgInn, hgN⟩
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

structure S2Data (H : L83Hyp h) extends PData H where
  g : X
  g_M : g ∈ h.M3
  g_K : g ∈ h.K
  g_norm : g ∈ normalizer ((h.Q ⊓ h.M3 : Subgroup X) : Set X)
  g_not_mem : g ∉ h.Q
  g_sq : g * g ∈ h.Q
  tau_K : h.a * (g⁻¹ * h.a * g) ∈ h.K

theorem nonempty_S2Data (H : L83Hyp h) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hF2 : CFSp4F2) : Nonempty (S2Data H) := by
  obtain ⟨d⟩ := H.nonempty_PData
  obtain ⟨g, hgK, hgN, hgQ, hgsq, htau⟩ := H.exists_g_gen hCF1 hCF2 hJo hF2
  exact ⟨{
    toPData := d
    g := (g : X)
    g_M := g.2
    g_K := hgK
    g_norm := mem_normalizer_inf_of_subgroupOf hgN
    g_not_mem := fun h1 => hgQ h1
    g_sq := hgsq
    tau_K := htau }⟩

namespace S2Data

variable (d : S2Data H)
include d

abbrev tau : X := h.a * (d.g⁻¹ * h.a * d.g)

theorem conj_a_mem : d.g⁻¹ * h.a * d.g ∈ h.Q ⊓ h.M3 := by
  have haQ : h.a ∈ h.Q ⊓ h.M3 := Subgroup.mem_inf.mpr ⟨H.a_mem_Q, h.a_mem_M3⟩
  have := (mem_normalizer_iff.mp (inv_mem d.g_norm) h.a).mp haQ
  rwa [inv_inv] at this

theorem tau_mem : d.tau ∈ h.Q ⊓ h.M3 :=
  mul_mem (Subgroup.mem_inf.mpr ⟨H.a_mem_Q, h.a_mem_M3⟩) d.conj_a_mem

theorem a_g : d.g⁻¹ * h.a * d.g = h.a * d.tau := by
  rw [tau, ← mul_assoc, Six.a_mul_a_self h, one_mul]

theorem tau_comm_a : d.tau * h.a = h.a * d.tau :=
  H.comm_a_of_mem_Q (Subgroup.mem_inf.mp d.tau_mem).1

theorem tau_sq : d.tau * d.tau = 1 := by
  have hc := H.comm_a_of_mem_Q (Subgroup.mem_inf.mp d.conj_a_mem).1
  have haa := Six.a_mul_a_self h
  have hga : d.g⁻¹ * h.a * d.g * (d.g⁻¹ * h.a * d.g) = 1 := by
    rw [show d.g⁻¹ * h.a * d.g * (d.g⁻¹ * h.a * d.g) = d.g⁻¹ * (h.a * h.a) * d.g by group, haa]
    group
  calc d.tau * d.tau = h.a * ((d.g⁻¹ * h.a * d.g) * h.a) * (d.g⁻¹ * h.a * d.g) := by
        rw [tau]; group
    _ = h.a * (h.a * (d.g⁻¹ * h.a * d.g)) * (d.g⁻¹ * h.a * d.g) := by rw [hc]
    _ = (h.a * h.a) * ((d.g⁻¹ * h.a * d.g) * (d.g⁻¹ * h.a * d.g)) := by group
    _ = 1 := by rw [haa, hga, one_mul]

theorem tau_ne_one : d.tau ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h1
  have hga : d.g⁻¹ * h.a * d.g = h.a := by
    have := eq_inv_of_mul_eq_one_right h1
    rwa [inv_eq_of_mul_eq_one_right (Six.a_mul_a_self h)] at this
  obtain ⟨hle, ⟨T, hT⟩⟩ := H.Q1_sylow
  set g' : ↥h.M3 := ⟨d.g, d.g_M⟩ with hg'
  have hgC : g' ∈ centralizer ({h.aM} : Set ↥h.M3) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    show d.g * h.a = h.a * d.g
    calc d.g * h.a = d.g * (d.g⁻¹ * h.a * d.g) := by rw [hga]
      _ = h.a * d.g := by group
  have hgN : g' ∈ normalizer ((h.Q.subgroupOf h.M3 : Subgroup ↥h.M3) : Set ↥h.M3) := by
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact (Subgroup.mem_inf.mp ((mem_normalizer_iff.mp d.g_norm q).mp
        (Subgroup.mem_inf.mpr ⟨hq, q.2⟩))).1
    · intro hq
      have := (mem_normalizer_iff.mp d.g_norm q).mpr (Subgroup.mem_inf.mpr ⟨hq,
        mul_mem (mul_mem d.g_M q.2) (inv_mem d.g_M)⟩)
      exact (Subgroup.mem_inf.mp this).1
  have hQ1₂ : IsPGroup 2 (h.Q.subgroupOf h.M3) := h.sec8_isPGroup_Q.comap_subtype
  have hp : IsPGroup 2 ↥(h.Q.subgroupOf h.M3 ⊔ zpowers g') :=
    isPGroup_sup_zpowers hQ1₂ hgN (show g' * g' ∈ h.Q.subgroupOf h.M3 from d.g_sq)
  have hle' : h.Q.subgroupOf h.M3 ⊔ zpowers g' ≤ centralizer ({h.aM} : Set ↥h.M3) :=
    sup_le hle (zpowers_le.mpr hgC)
  have heq := eq_of_sylow_of_le ⟨T, hT⟩ le_sup_left hle' hp
  apply d.g_not_mem
  have : g' ∈ h.Q.subgroupOf h.M3 := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers g')
  exact this

theorem b_comm_of_mem_M3 {m : X} (hm : m ∈ h.M3) : m * d.b = d.b * m := by
  have hM : h.M3 ≤ centralizer ({d.b} : Set X) := by
    rw [← d.normalizer_B]
    exact h.M3_le_normalizer
  exact mem_centralizer_singleton_iff.mp (hM hm)

theorem tau_not_mem_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.tau ∉ h.P := by
  intro htP
  have htK := d.tau_K
  rcases d.P_mem _ htP with h1 | h1 | h1 | h1
  · exact d.tau_ne_one h1
  · exact H.a_not_mem_K hCF1 hCF2 (h1 ▸ htK)
  · exact d.b_not_mem_M3 hCF1 hCF2 (mem_sup_left (h1 ▸ htK))
  · apply d.b_not_mem_M3 hCF1 hCF2
    have := mul_mem (inv_mem h.a_mem_M3) (mem_sup_left (h1 ▸ htK) : h.a * d.b ∈ h.M3)
    rwa [inv_mul_cancel_left] at this

end S2Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

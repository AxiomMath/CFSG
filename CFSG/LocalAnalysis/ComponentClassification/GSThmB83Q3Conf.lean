module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Model

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem commutator_map_pLayer_eq {G : Type*} [Group G] (Y : Subgroup G) :
    ⁅(pLayer ↥Y 2).map Y.subtype, (pLayer ↥Y 2).map Y.subtype⁆ = (pLayer ↥Y 2).map Y.subtype := by
  rw [← map_commutator]
  congr 1
  refine le_antisymm (commutator_le_self _) ?_
  refine sSup_le fun L hL => ?_
  have hLp : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hL)
  rw [← hLp]
  exact commutator_mono (le_sSup hL) (le_sSup hL)

theorem commutator_fixedLayer_eq {G : Type*} [Group G] (J E : Subgroup G) :
    ⁅GSLit.fixedLayer J E, GSLit.fixedLayer J E⁆ = GSLit.fixedLayer J E :=
  commutator_map_pLayer_eq _

theorem card_quotient_dvd_card_map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (φ : G →* G')
    (hφ : ¬ 2 ∣ Nat.card φ.ker) (L : Subgroup G) :
    Nat.card (L ⧸ pPrimeCore 2 L) ∣ Nat.card (L.map φ) := by
  obtain ⟨e, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv φ L
    (OddQuot.not_two_dvd_card_ker_domRestrict φ hφ L)
  rw [Nat.card_congr e.toEquiv]
  exact card_quotient_dvd_card _

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

abbrev JB : Subgroup X := GSLit.fixedLayer h.J h.B

theorem sec8_quasisimple_Jbar : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) :=
  ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.J _ h.J_le).1 h.isPComponent_J).2.2

theorem card_JB_quotient :
    Nat.card (h.JB ⧸ pPrimeCore 2 h.JB) = Nat.card (h.J ⧸ pPrimeCore 2 h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (Six.isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.sec8_quasisimple_Jbar hBJ hB2).1
  have hJBJ : h.JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨-, e1, -⟩ := restriction_quotient_mulEquiv hJBJ hsup
  exact Nat.card_congr e1.toEquiv

theorem sec8_B_le_kernel_J : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right

theorem sec8_isPGroup_B : IsPGroup 2 h.B := (Six.isPGroup_S h).to_le (h.B_le.trans inf_le_left)

theorem sec8_D_le_centralizer_B : h.D ≤ centralizer (h.B : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d hd
  rw [mem_centralizer_iff]
  intro b hb
  have hbS : b ∈ h.S := (h.B_le hb).1
  have hbK : b ∈ coreActionKernel h.J := h.sec8_B_le_kernel_J hb
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  have h1 : d⁻¹ * b⁻¹ * d * b ∈ (pPrimeCore 2 h.J).map h.J.subtype := hbc d hd.2
  have h2 : d⁻¹ * b⁻¹ * d * b ∈ h.S :=
    mul_mem (mul_mem (mul_mem (inv_mem hd.1) (inv_mem hbS)) hd.1) hbS
  have hS2 : IsPGroup 2 h.S := Six.isPGroup_S h
  have hO : Odd (Nat.card ((pPrimeCore 2 h.J).map h.J.subtype)) := by
    rw [card_map_of_injective h.J.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h3 := eq_bot_of_le_two_group_of_le_odd hS2 hO (inf_le_left : h.S ⊓ _ ≤ h.S)
    (inf_le_right : h.S ⊓ (pPrimeCore 2 h.J).map h.J.subtype ≤ _)
  have h4 : d⁻¹ * b⁻¹ * d * b = 1 := by
    have : d⁻¹ * b⁻¹ * d * b ∈ h.S ⊓ (pPrimeCore 2 h.J).map h.J.subtype := mem_inf.mpr ⟨h2, h1⟩
    rw [h3, mem_bot] at this
    exact this
  have h5 : d * b = b * d := by
    have := congrArg (fun t => b * d * t) h4
    simp only [mul_one] at this
    rw [← this]
    group
  exact h5.symm

theorem D_le_JB : h.D ≤ h.JB := by
  rw [JB, GSLit.fixedLayer_eq_closure h.sec8_quasisimple_Jbar h.sec8_B_le_kernel_J
    h.sec8_isPGroup_B]
  intro d hd
  refine subset_closure ⟨⟨hd.2, h.sec8_D_le_centralizer_B hd⟩, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D)
    ⟨d, hd⟩
  exact ⟨k, (Subgroup.orderOf_coe (⟨d, hd⟩ : h.D)).trans hk⟩

theorem sec8_D_sylow : ∃ T : Sylow 2 ↥h.J, (T : Subgroup h.J) = h.D.subgroupOf h.J :=
  UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer h.S_le h.S_sylow
    (le_inf h.J_le le_normalizer) inf_le_right

theorem card_Jbar_dvd : Nat.card (h.J ⧸ pPrimeCore 2 h.J) ∣ Nat.card h.J :=
  card_quotient_dvd_card _

theorem eight_dvd_card_D (hq : h.IsQ3) : 8 ∣ Nat.card h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := h.sec8_D_sylow
  have h1 : 2 ^ 3 ∣ Nat.card h.J := by
    refine dvd_trans ?_ h.card_Jbar_dvd
    rw [card_of_isSec8JType_three hq.2]
    norm_num
  have h2 := T.pow_dvd_card_of_pow_dvd_card h1
  rw [hT] at h2
  have h3 : Nat.card (h.D.subgroupOf h.J) = Nat.card h.D := by
    rw [← card_map_of_injective h.J.subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_right]
  rw [h3] at h2
  simpa using h2

theorem card_le_eight_of_dvd {G : Type*} [Group G] {A : Subgroup G} (hA : IsPGroup 2 A)
    (h360 : Nat.card A ∣ 360) : Nat.card A ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card A := Nat.pos_of_dvd_of_pos h360 (by norm_num)
  have : Finite A := Nat.finite_of_card_ne_zero hpos.ne'
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [hk] at h360 ⊢
  by_contra hlt
  have hk4 : 4 ≤ k := by
    by_contra h4
    interval_cases k <;> norm_num at hlt
  have : 2 ^ 4 ∣ 360 := (pow_dvd_pow 2 hk4).trans h360
  norm_num at this

theorem sec8_D_le_Q : h.D ≤ h.Q :=
  le_inf inf_le_left (h.sec8_D_le_centralizer_B.trans (centralizer_le_normalizer _))

theorem exists_z (hq : h.IsQ3) :
    ∃ z ∈ h.D, z * z = 1 ∧ z ≠ 1 ∧ ∀ d ∈ h.D, z * d = d * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 h.D := (Six.isPGroup_S h).to_le inf_le_left
  have hnt : Nontrivial h.D := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos (h.eight_dvd_card_D hq)
    omega
  have hZ := hD2.center_nontrivial
  have h2 : 2 ∣ Nat.card (center h.D) := by
    obtain ⟨k, hk⟩ := (hD2.to_subgroup (center h.D)).exists_card_eq
    have h1 : 1 < Nat.card (center h.D) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨⟨⟨z, hzD⟩, hzc⟩, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨z, hzD, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one (⟨⟨z, hzD⟩, hzc⟩ : center h.D)
    rw [hz, pow_two] at this
    exact congrArg (fun t : center h.D => ((t : h.D) : X)) this
  · intro h1
    have : (⟨⟨z, hzD⟩, hzc⟩ : center h.D) = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    norm_num at hz
  · intro d hd
    have := Subgroup.mem_center_iff.mp hzc ⟨d, hd⟩
    exact (congrArg Subtype.val this).symm

namespace L83Hyp

variable {h} (H : L83Hyp h)
include H

theorem JB_le_M3 : h.JB ≤ h.M3 := H.fixedLayer_le_K.trans le_sup_left

theorem rho_mem_inn_of_mem_K {m : ↥h.M3} (hm : (m : X) ∈ h.K) :
    H.rho m ∈ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) := by
  have : m = ⟨(m : X), mem_sup_left hm⟩ := rfl
  rw [this, H.rho_of_mem_K hm]
  exact ⟨_, rfl⟩

theorem map_JB_le_innFix :
    (h.JB.subgroupOf h.M3).map H.rho ≤ Cat8.innFix (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  rintro _ ⟨m, hm, rfl⟩
  have hmJB : (m : X) ∈ h.JB := hm
  have hmJ : (m : X) ∈ h.J := ((GSLit.fixedLayer_le_inf h.J h.B) hmJB).1
  refine ⟨H.rho_mem_inn_of_mem_K (H.fixedLayer_le_K hmJB), ?_⟩
  show H.rho m ∈ centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))
  rw [mem_centralizer_singleton_iff, ← H.rho_aM, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_singleton_iff.mp (h.J_le hmJ))

theorem commutator_JB_subgroupOf :
    ⁅h.JB.subgroupOf h.M3, h.JB.subgroupOf h.M3⁆ = h.JB.subgroupOf h.M3 := by
  apply map_injective h.M3.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le H.JB_le_M3]
  exact commutator_fixedLayer_eq h.J h.B

theorem map_JB_eq (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) :
    (h.JB.subgroupOf h.M3).map H.rho = Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hle : (h.JB.subgroupOf h.M3).map H.rho ≤ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
    rw [← H.commutator_JB_subgroupOf, map_commutator]
    exact commutator_mono H.map_JB_le_innFix H.map_JB_le_innFix
  refine eq_of_le_of_card_ge hle ?_
  rw [(hL0 _ hq.1 _ (H.rhoA_adm hq hCF1 hCF2)).1]
  have h1 := card_quotient_dvd_card_map H.rho hker (h.JB.subgroupOf h.M3)
  let e2 : h.JB ≃* h.JB.subgroupOf h.M3 := (subgroupOfEquivOfLe H.JB_le_M3).symm
  let e3 : h.JB ⧸ pPrimeCore 2 h.JB ≃* (h.JB.subgroupOf h.M3) ⧸
      pPrimeCore 2 (h.JB.subgroupOf h.M3) :=
    QuotientGroup.congr (pPrimeCore 2 h.JB) (pPrimeCore 2 (h.JB.subgroupOf h.M3)) e2
      (pPrimeCore_map_iso 2 e2)
  rw [← Nat.card_congr e3.toEquiv, h.card_JB_quotient, card_of_isSec8JType_three hq.2] at h1
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h0 => by
    have := Nat.card_pos (α := ↥((h.JB.subgroupOf h.M3).map H.rho))
    omega)) h1

theorem D_le_M3 : h.D ≤ h.M3 := h.D_le_JB.trans H.JB_le_M3

theorem map_D_eq (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) :
    (h.D.subgroupOf h.M3).map H.rho =
      (h.Q.subgroupOf h.M3).map H.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hD2 : IsPGroup 2 (h.D.subgroupOf h.M3) :=
    ((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype
  have hle : (h.D.subgroupOf h.M3).map H.rho ≤
      (h.Q.subgroupOf h.M3).map H.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
    refine le_inf (map_mono fun m hm => h.sec8_D_le_Q hm) ?_
    rw [← H.map_JB_eq hq hCF1 hCF2 hL0]
    exact map_mono fun m hm => h.D_le_JB hm
  refine eq_of_le_of_card_ge hle ?_
  have hcD : Nat.card ((h.D.subgroupOf h.M3).map H.rho) = Nat.card h.D := by
    rw [Eight.card_map_of_isPGroup hker hD2, ← card_map_of_injective h.M3.subtype_injective,
      subgroupOf_map_subtype, inf_eq_left.mpr H.D_le_M3]
  rw [hcD]
  have h8 : 8 ≤ Nat.card h.D := Nat.le_of_dvd Nat.card_pos (h.eight_dvd_card_D hq)
  refine le_trans ?_ h8
  apply card_le_eight_of_dvd
  · exact (h.sec8_isPGroup_Q.comap_subtype.map H.rho).to_le inf_le_left
  · rw [← (hL0 _ hq.1 _ (H.rhoA_adm hq hCF1 hCF2)).1]
    exact card_dvd_of_le inf_le_right

theorem exists_conf (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) (hF2 : CFQ3F2) (hL0 : CFQ3L0) :
    ∃ (g : ↥h.M3) (z : X) (hzD : z ∈ h.D) (RM : Subgroup ↥h.M3)
      (c : Cat8.Q3Conf (h.K ⧸ pPrimeCore 2 h.K)),
      (g : X) ∈ h.K ∧ g ∈ normalizer ((h.Q.subgroupOf h.M3 : Subgroup ↥h.M3) : Set ↥h.M3) ∧
      g ∉ h.Q.subgroupOf h.M3 ∧ g * g ∈ h.Q.subgroupOf h.M3 ∧
      ((h.aM * (g⁻¹ * h.aM * g) : ↥h.M3) : X) ∈ h.K ∧
      z * z = 1 ∧ z ≠ 1 ∧ (∀ d ∈ h.D, z * d = d * z) ∧
      h.Q.subgroupOf h.M3 ⊔ zpowers g ≤ RM ∧ (∃ T : Sylow 2 ↥h.M3, (T : Subgroup _) = RM) ∧
      c.a = H.rhoA ∧ c.Q = (h.Q.subgroupOf h.M3).map H.rho ∧ c.g = H.rho g ∧
      c.R = RM.map H.rho ∧ c.z = H.rho ⟨z, H.D_le_M3 hzD⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨g, hgK, hgN, hgQ, hgsq, htau⟩ := H.exists_g hq hCF1 hCF2 hOut hF2
  obtain ⟨z, hzD, hz2, hz1, hzc⟩ := h.exists_z hq
  set Q1 : Subgroup ↥h.M3 := h.Q.subgroupOf h.M3 with hQ1
  have hQ1₂ : IsPGroup 2 Q1 := h.sec8_isPGroup_Q.comap_subtype
  have hT₂ : IsPGroup 2 ↥(Q1 ⊔ zpowers g) := isPGroup_sup_zpowers hQ1₂ hgN hgsq
  obtain ⟨RM, hRM⟩ := hT₂.exists_le_sylow
  have hsurj := H.rho_surjective hq hCF1 hCF2 hOut
  obtain ⟨hQle, hQS⟩ := H.Q1hat_sylow hq hCF1 hCF2 hOut
  have hzM : z ∈ h.M3 := H.D_le_M3 hzD
  have hzQ : H.rho ⟨z, hzM⟩ ∈ Q1.map H.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
    rw [← H.map_D_eq hq hCF1 hCF2 hL0]
    exact mem_map_of_mem _ hzD
  refine ⟨g, z, hzD, RM, {
    a := H.rhoA
    Q := Q1.map H.rho
    g := H.rho g
    R := (RM : Subgroup ↥h.M3).map H.rho
    z := H.rho ⟨z, hzM⟩
    adm := H.rhoA_adm hq hCF1 hCF2
    Q_le := hQle
    Q_sylow := hQS
    g_inn := H.rho_mem_inn_of_mem_K hgK
    g_norm := le_normalizer_map H.rho (mem_map_of_mem _ hgN)
    g_not_mem := fun hg => hgQ (Eight.mem_of_map_mem hker hT₂ le_sup_left
      (mem_sup_right (mem_zpowers g)) hg)
    g_sq := by rw [← map_mul]; exact mem_map_of_mem _ hgsq
    tau_inn := by
      rw [← H.rho_aM, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact H.rho_mem_inn_of_mem_K htau
    Q_le_R := map_mono (le_sup_left.trans hRM)
    g_mem_R := mem_map_of_mem _ (hRM (mem_sup_right (mem_zpowers g)))
    R_sylow := ⟨RM.mapSurjective hsurj, Sylow.coe_mapSurjective _ _⟩
    z_mem := hzQ
    z_comm := by
      intro w hw
      rw [← H.map_D_eq hq hCF1 hCF2 hL0] at hw
      obtain ⟨d, hd, rfl⟩ := mem_map.mp hw
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc d hd)
    z_sq := by rw [← map_mul]; rw [show (⟨z, hzM⟩ : ↥h.M3) * ⟨z, hzM⟩ = 1 from Subtype.ext hz2,
      map_one]
    z_ne := by
      intro h1
      apply hz1
      have hzz : (⟨z, hzM⟩ : ↥h.M3) ∈ h.D.subgroupOf h.M3 := hzD
      have := Eight.injOn_of_isPGroup hker
        (((Six.isPGroup_S h).to_le inf_le_left : IsPGroup 2 h.D).comap_subtype (K := h.M3)) hzz
        (one_mem _) (h1.trans (map_one _).symm)
      exact congrArg Subtype.val this }, hgK, hgN, hgQ, hgsq, htau, hz2, hz1, hzc, hRM, ⟨RM, rfl⟩,
    rfl, rfl, rfl, rfl, rfl⟩

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

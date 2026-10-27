module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

structure KLoc (h : Hyp52 X) : Prop where
  case8 : h.Sec8Case
  B_eq : ∃ b : X, h.B = zpowers b ∧ orderOf b = 2
  C_eq : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  J_normal : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal
  B_sylow_kernel : h.B ≤ coreActionKernel h.V ∧ ∃ R : Sylow 2 ↥(coreActionKernel h.V),
    (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V)

variable {h : Hyp52 X}

namespace KLoc

variable (H : KLoc h)
include H

theorem K_conj : conjugate h.K h.a = h.K := (Sec8Case.exists_params h H.case8).1

theorem V_eq_K : h.V = h.K := by
  show layerIn (normalizer (h.B : Set X)) = h.K
  rw [← h.layer_eq_K, H.K_conj, sup_idem]

theorem a_mem_normalizer_K : h.a ∈ normalizer (h.K : Set X) :=
  mem_normalizer_of_conjugate_eq H.K_conj

theorem fixedLayer_le_K : GSLit.fixedLayer h.J h.B ≤ h.K := by
  rw [← H.V_eq_K]
  show GSLit.fixedLayer h.J h.B ≤ layerIn (normalizer (h.B : Set X))
  rw [← h.conjClosure_eq]
  refine le_trans ?_ (le_iSup₂_of_le (1 : X) (one_mem _) le_rfl)
  intro z hz
  refine ⟨z, hz, ?_⟩
  simp

theorem a_not_mem_coreActionKernel : h.a ∉ coreActionKernel h.K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro haK
  obtain ⟨b, hBb, hb2⟩ := H.B_eq
  have hab : b * h.a = h.a * b :=
    Six.comm_a H.C_eq ((mem_inf.mp (h.B_le (hBb ▸ mem_zpowers b))).1)
  rw [← H.V_eq_K] at haK
  obtain ⟨hBV, R, hR⟩ := H.B_sylow_kernel
  have hbV : b ∈ coreActionKernel h.V := hBV (hBb ▸ mem_zpowers b)
  set E : Subgroup X := closure {h.a, b} with hE
  have hEV : E ≤ coreActionKernel h.V := by
    rw [hE, closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact haK
    · exact hbV
  have haa := Six.a_mul_a_self h
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hE2 : IsPGroup 2 E := by
    intro w
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two]
    change (w : X) * w = 1
    rcases Six.mem_closure_pair_cases haa hbb hab w.2 with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [mul_one]
    · exact haa
    · exact hbb
    · rw [show h.a * b * (h.a * b) = h.a * (b * h.a) * b by group, hab,
        show h.a * (h.a * b) * b = (h.a * h.a) * (b * b) by group, haa, hbb, one_mul]
  have haB := Six.a_not_mem_B H.C_eq
  have hBE : h.B ≤ E := by
    rw [hBb, zpowers_le]
    exact subset_closure (by simp)
  have haE : h.a ∈ E := subset_closure (by simp)
  obtain ⟨R', hR'⟩ := (hE2.comap_subtype : IsPGroup 2 (E.subgroupOf (coreActionKernel h.V)))
    |>.exists_le_sylow
  have hcardR : Nat.card (R' : Subgroup ↥(coreActionKernel h.V)) = Nat.card h.B := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity R, hR,
      Six.card_subgroupOf_eq, inf_eq_left.mpr hBV]
  have hle := card_le_of_le hR'
  rw [hcardR] at hle
  change Nat.card ↥(E.subgroupOf (coreActionKernel h.V)) ≤ _ at hle
  rw [Six.card_subgroupOf_eq, inf_eq_left.mpr hEV] at hle
  exact haB ((eq_of_le_of_card_ge hBE hle) ▸ haE)

noncomputable abbrev rhoA : MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  Eight.modelHom h.K H.a_mem_normalizer_K ⟨h.a, mem_sup_right (mem_zpowers _)⟩

theorem card_J_dvd_card_fix :
    Nat.card (h.J ⧸ pPrimeCore 2 h.J) ∣ Nat.card (Eight.fixSubgroup H.rhoA) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK := H.fixedLayer_le_K
  have hJq : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 h.J _ h.J_le).1 h.isPComponent_J).2.2
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (Six.isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore hJq hBJ hB2).1
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨-, e1, -⟩ := restriction_quotient_mulEquiv hJBJ hsup
  set JB' := JB.subgroupOf h.K with hJB'
  let e2 : JB ≃* JB' := (subgroupOfEquivOfLe hJBK).symm
  let e3 : JB ⧸ pPrimeCore 2 JB ≃* JB' ⧸ pPrimeCore 2 JB' :=
    QuotientGroup.congr (pPrimeCore 2 JB) (pPrimeCore 2 JB') e2 (pPrimeCore_map_iso 2 e2)
  set π := QuotientGroup.mk' (pPrimeCore 2 h.K) with hπ
  have hπker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (pPrimeCore_coprime_card (p := 2) (G := h.K)) h2
  obtain ⟨e4, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv π JB'
    (OddQuot.not_two_dvd_card_ker_domRestrict π hπker JB')
  have hIfix : JB'.map π ≤ Eight.fixSubgroup H.rhoA := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Eight.mem_fixSubgroup]
    have hjJ : (j : X) ∈ h.J := hJBJ hj
    have hja : h.a * (j : X) = j * h.a :=
      (mem_centralizer_singleton_iff.mp (h.J_le hjJ)).symm
    exact Eight.mem_fixedPoints_oddBarAction _ hja
  calc Nat.card (h.J ⧸ pPrimeCore 2 h.J) = Nat.card (JB ⧸ pPrimeCore 2 JB) :=
        (Nat.card_congr e1.toEquiv).symm
    _ = Nat.card (JB' ⧸ pPrimeCore 2 JB') := Nat.card_congr e3.toEquiv
    _ = Nat.card (JB'.map π ⧸ pPrimeCore 2 (JB'.map π)) := Nat.card_congr e4.toEquiv
    _ ∣ Nat.card (JB'.map π) := card_quotient_dvd_card _
    _ ∣ Nat.card (Eight.fixSubgroup H.rhoA) := card_dvd_of_le hIfix

theorem center_eq_bot (hCF1 : CFSec8Simple) : center (h.K ⧸ pPrimeCore 2 h.K) = ⊥ := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, -⟩ := Sec8Case.exists_params h H.case8
  obtain ⟨hsimp, u, v, huv⟩ := hCF1 _ p f hp hp2 hf hK
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (h.K ⧸ pPrimeCore 2 h.K)) with h1 | h1
  · exact h1
  · exfalso
    apply huv
    have hu : u ∈ center (h.K ⧸ pPrimeCore 2 h.K) := h1 ▸ mem_top u
    exact (Subgroup.mem_center_iff.mp hu v).symm

theorem rhoA_not_mem_inner (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    H.rhoA ∉ (MulAut.conj : (h.K ⧸ pPrimeCore 2 h.K) →* MulAut (h.K ⧸ pPrimeCore 2 h.K)).range := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.case8
  rintro ⟨k, hk⟩
  have hZ := H.center_eq_bot hCF1
  have haM : h.a ∈ h.K ⊔ zpowers h.a := mem_sup_right (mem_zpowers _)
  have hρ2 : H.rhoA * H.rhoA = 1 := by
    show Eight.modelHom h.K H.a_mem_normalizer_K ⟨h.a, haM⟩ *
      Eight.modelHom h.K H.a_mem_normalizer_K ⟨h.a, haM⟩ = 1
    rw [← map_mul]
    rw [show (⟨h.a, haM⟩ : ↥(h.K ⊔ zpowers h.a)) * ⟨h.a, haM⟩ = 1 from
      Subtype.ext (Six.a_mul_a_self h), map_one]
  have hkk : k * k = 1 := by
    have h1 : MulAut.conj (k * k) = 1 := by rw [map_mul, hk, hρ2]
    have hc : k * k ∈ center (h.K ⧸ pPrimeCore 2 h.K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun φ : MulAut (h.K ⧸ pPrimeCore 2 h.K) => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * (k * k) = (k * k) * y * (k * k)⁻¹ * (k * k) := by rw [h2]
        _ = (k * k) * y := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, map_one] at hk
    apply H.a_not_mem_coreActionKernel
    have h2 : (⟨h.a, H.a_mem_normalizer_K⟩ : normalizer (h.K : Set X)) ∈
        (Eight.oddBarAction h.K).ker := hk.symm
    exact Eight.mem_ker_oddBarAction.mp h2
  have hko : orderOf k = 2 := orderOf_eq_prime (by rw [pow_two, hkk]) hk1
  have hfix : Eight.fixSubgroup H.rhoA = centralizer ({k} : Set (h.K ⧸ pPrimeCore 2 h.K)) := by
    ext y
    rw [Eight.mem_fixSubgroup, ← hk, MulAut.conj_apply, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      calc y * k = k * y * k⁻¹ * k := by rw [h1]
        _ = k * y := by group
    · intro h1
      rw [← h1, mul_inv_cancel_right]
  have := H.card_J_dvd_card_fix
  rw [hfix] at this
  exact hCF2 _ _ p f hp hp2 hf hK hJ k hko this

theorem not_two_dvd_card_ker_modelHom (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    ¬ 2 ∣ Nat.card (Eight.modelHom h.K H.a_mem_normalizer_K).ker :=
  Eight.not_two_dvd_card_ker_modelHom h.K H.a_mem_normalizer_K (Six.a_mul_a_self h)
    (H.center_eq_bot hCF1) (H.rhoA_not_mem_inner hCF1 hCF2)

noncomputable abbrev rho : ↥h.M3 →* MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  Eight.modelHom h.K H.a_mem_normalizer_K

theorem rho_aM : H.rho h.aM = H.rhoA := rfl

theorem rhoA_mul_self : H.rhoA * H.rhoA = 1 := by
  rw [← rho_aM, ← map_mul]
  rw [show (h.aM : ↥h.M3) * h.aM = 1 from Subtype.ext (Six.a_mul_a_self h), map_one]

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

theorem rho_range_eq :
    H.rho.range = Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA :=
  Eight.range_modelHom h.K H.a_mem_normalizer_K (Six.a_mul_a_self h)

theorem rhoA_admQ (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hJ : IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f) :
    Cat8.IsAdmQ (h.K ⧸ pPrimeCore 2 h.K) (p ^ f) H.rhoA where
  sq := H.rhoA_mul_self
  out := H.rhoA_not_mem_inner hCF1 hCF2
  dvd := by
    have h1 := H.card_J_dvd_card_fix
    rwa [hJo _ p f hp hp2 hf hJ] at h1

theorem map_centralizer_aM_gen (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) :
    (centralizer ({h.aM} : Set ↥h.M3)).map H.rho =
      (Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) ⊔ zpowers H.rhoA) ⊓
        centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := by
  have hA : IsPGroup 2 (zpowers h.aM) := isPGroup_zpowers_of_mul_self h.aM_mul_self
  have h1 := Eight.map_centralizer_eq (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) hA
  rw [centralizer_zpowers_eq, MonoidHom.map_zpowers, centralizer_zpowers_eq,
    H.rho_range_eq] at h1
  exact h1

theorem Q1hat_sylow_gen (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
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

theorem exists_g_gen (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hJo : CFSec8JOrder) (hF2 : CFSp4F2) :
    ∃ g : ↥h.M3, (g : X) ∈ h.K ∧ g ∈ normalizer ((h.Q.subgroupOf h.M3 : Subgroup ↥h.M3) :
        Set ↥h.M3) ∧ g ∉ h.Q.subgroupOf h.M3 ∧ g * g ∈ h.Q.subgroupOf h.M3 ∧
      ((h.aM * (g⁻¹ * h.aM * g) : ↥h.M3) : X) ∈ h.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.case8
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


end KLoc

end Hyp52

end CFSG.ComponentClassification.GSThmB

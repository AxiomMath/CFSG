module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Local
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

structure L83Hyp (h : Hyp52 X) : Prop where
  setting : Sec8Setting X h
  card_P : Nat.card h.P = 4
  T_eq : h.T = h.B ⊔ zpowers h.a
  C_eq : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  J_normal : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal
  S_sylow_C : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
    (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X))
  B_sylow_kernel : h.B ≤ coreActionKernel h.V ∧ ∃ R : Sylow 2 ↥(coreActionKernel h.V),
    (R : Subgroup _) = h.B.subgroupOf (coreActionKernel h.V)

variable {h : Hyp52 X}

namespace L83Hyp

variable (H : L83Hyp h)
include H

theorem sec8Case : h.Sec8Case := H.setting.2.2.2.2.2.2.2.2.2.2

theorem maximal : GSMaximalUnbalancingTriple h.a h.x h.J := H.setting.2.2.2.2.2.1

theorem x_mul_x : h.x * h.x = 1 := by
  obtain ⟨-, hx, -⟩ := gsUnbalancingTriple_iff.mp H.maximal.1
  rw [← pow_two, ← hx, pow_orderOf_eq_one]

theorem K_conj : conjugate h.K h.a = h.K := (Sec8Case.exists_params h H.sec8Case).1

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
  obtain ⟨b, hb2, hBb, -, -, hab, -, -, -, -, -⟩ :=
    h.sec8_P4_setup H.T_eq H.C_eq H.card_P H.x_mul_x
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
  obtain ⟨-, p, f, hp, hp2, hf, hK, -⟩ := Sec8Case.exists_params h H.sec8Case
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
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.sec8Case
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

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

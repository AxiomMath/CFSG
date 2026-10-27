module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2TB

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Cat8

structure S2Facts : Prop where
  jorder : CFSec8JOrder
  f2 : CFSp4F2
  l2inv : CFL2Inv
  layer : CFSp4Layer
  order : CFSec8Order

end Cat8

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

theorem false_of_five_le (H : L83Hyp h)
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hS2 : Cat8.S2Facts) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h5 : 5 ≤ p ^ f) (hK : IsSec8Socle (h.K ⧸ pPrimeCore 2 h.K) p f)
    (hJ : IsSec8JType (h.J ⧸ pPrimeCore 2 h.J) p f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d⟩ := H.nonempty_S2Data hCF1 hCF2 hS2.jorder hS2.f2
  obtain ⟨Lφ, -, hLφ1, hLφ2, hLφ3, hLφ4⟩ :=
    hS2.l2inv _ p f hp hp2 hf h5 hJ d.phi d.phi_mul_self (d.phi_ne_one hCF1 hCF2)
  have hpsiL : d.psiT ≤ Lφ := hLφ1 _ d.psiT_le_centralizer_phi d.psiT_perfect
  have hcard : Nat.card d.psiT ≤ Cat8.ordL2 (p ^ f) := (card_le_of_le hpsiL).trans hLφ2
  obtain ⟨hceq, y, hyInn, hya, hyE, hyord⟩ :=
    d.exists_y hCF1 hCF2 hS2.jorder hS2.layer hp hp2 hf h5 hK hJ hcard
  have hpsi : d.psiT = Lφ := eq_of_le_of_card_ge hpsiL (by rw [hceq]; exact hLφ2)
  have hLcard : Nat.card Lφ = Cat8.ordL2 (p ^ f) := by rw [← hpsi, hceq]
  obtain ⟨s, hs, hsa, hsw, hsy⟩ := d.exists_lift hCF1 hyInn hya
  have hsa' : s ∈ centralizer ({h.a} : Set X) := mem_centralizer_singleton_iff.mpr hsa
  have hcases := d.sigmaA_lift_cases hLφ3 (hLφ4 hLcard) hpsi hs hsa' hsw
    (by rw [hsy]; exact hyE)
  have hss : s * s ∈ h.O0 := d.sq_mem_O0_of_cases hCF1 hCF2 hsa' hcases
  have hsN2 : s * s ∈ normalizer (d.L : Set X) := mul_mem hs hs
  have hy2 : Eight.oddBarAction d.L ⟨s * s, hsN2⟩ = y * y := by
    rw [show (⟨s * s, hsN2⟩ : normalizer (d.L : Set X)) = ⟨s, hs⟩ * ⟨s, hs⟩ from Subtype.ext rfl,
      map_mul, hsy]
  have hodd2 : Odd (orderOf (y * y)) := by
    have h1 : orderOf (s * s) ∣ Nat.card h.O0 := by
      rw [← Subgroup.orderOf_mk (s * s) hss]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (y * y) ∣ orderOf (s * s) := by
      rw [← hy2, ← Subgroup.orderOf_mk (s * s) hsN2]
      exact orderOf_map_dvd _ _
    exact (odd_card_O0 h).of_dvd_nat (h2.trans h1)
  rcases hyord with h4 | ⟨hyodd, hy1⟩
  ·
    have h2 : orderOf (y * y) = 2 := by
      rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [h4]; norm_num), h4]
    rw [h2] at hodd2
    exact absurd hodd2 (by decide)
  ·
    have hd₀O : (s * s) ^ ((orderOf y + 1) / 2) ∈ h.O0 := pow_mem hss _
    have hd₀N : (s * s) ^ ((orderOf y + 1) / 2) ∈ normalizer (d.L : Set X) := pow_mem hsN2 _
    have hd₀y : Eight.oddBarAction d.L ⟨(s * s) ^ ((orderOf y + 1) / 2), hd₀N⟩ = y := by
      rw [show (⟨(s * s) ^ ((orderOf y + 1) / 2), hd₀N⟩ : normalizer (d.L : Set X)) =
          ⟨s * s, hsN2⟩ ^ ((orderOf y + 1) / 2) from
          Subtype.ext (SubgroupClass.coe_pow (⟨s * s, hsN2⟩ : normalizer (d.L : Set X))
            ((orderOf y + 1) / 2)).symm,
        map_pow, hy2, ← Eight.eq_sq_pow_of_odd hyodd]
    have hd₀D : (s * s) ^ ((orderOf y + 1) / 2) ∈
        (pPrimeCore 2 (centralizer ({h.a} : Set X))).map (centralizer ({h.a} : Set X)).subtype ⊓
          centralizer ({d.w} : Set X) := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem (mul_mem hsw hsw) _⟩
      exact Eight.le_oddCore_of_odd ((map_subtype_le _).trans inf_le_left)
        H.centralizer_a_le_normalizer_O0 (odd_card_O0 h) hd₀O
    have hd₀K : (s * s) ^ ((orderOf y + 1) / 2) ∉ coreActionKernel d.L := by
      intro hK'
      apply hy1
      rw [← hd₀y]
      have : (⟨(s * s) ^ ((orderOf y + 1) / 2), hd₀N⟩ : normalizer (d.L : Set X)) ∈
          (Eight.oddBarAction d.L).ker := Eight.mem_ker_oddBarAction.mpr hK'
      exact this
    obtain ⟨l, hl, hdl⟩ : ∃ l ∈ d.L, l⁻¹ * ((s * s) ^ ((orderOf y + 1) / 2))⁻¹ * l *
        (s * s) ^ ((orderOf y + 1) / 2) ∉ (pPrimeCore 2 d.L).map d.L.subtype := by
      by_contra hne
      push Not at hne
      exact hd₀K (mem_coreActionKernel.mpr ⟨hd₀N, hne⟩)
    have htriple := Eight.gsUnbalancingTriple_of_active d.orderOf_w h.orderOf_a d.w_comm_a
      d.L_le_centralizer_w d.isPComponent_L hd₀D hl hdl
    obtain ⟨hsimp, hnonab, hKP, hz, hU, -⟩ := H.setting
    rcases d.isSec8Socle_L hK with hL | ⟨hp3, hf1, -⟩
    · exact Sp4TB.false_of_unbalancingTriple_psp hTB hSA hnonab hKP hz hU htriple hp hp2 h5 hL
        (d.center_Lbar hCF1)
    · rw [hp3, hf1] at h5
      norm_num at h5

theorem isQ3 (H : L83Hyp h) (hTB : GSLit.ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (hS2 : Cat8.S2Facts) : h.IsQ3 := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.sec8Case
  by_cases h5 : 5 ≤ p ^ f
  · exact (H.false_of_five_le hTB hSA hCF1 hCF2 hS2 hp hp2 hf h5 hK hJ).elim
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hp3' : p = 3 := by
      rcases (by omega : p = 3 ∨ p = 4) with h3 | h3
      · exact h3
      · exact absurd (h3 ▸ hp) (by norm_num)
    subst hp3'
    have hf1 : f = 1 := by
      by_contra hf1
      have h2 : 9 ≤ 3 ^ f :=
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hf1
    exact ⟨hK, hJ⟩

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB

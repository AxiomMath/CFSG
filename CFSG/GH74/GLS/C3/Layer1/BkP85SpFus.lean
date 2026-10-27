module

public import CFSG.GH74.Generic.S45.LEvSporCfg
public import CFSG.GH74.Generic.S45.LEvSporEmbed
public import CFSG.GH74.Generic.S45.LEvSporFacts

public section

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.M12Cover
open CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor

namespace CFSG.GH74.GLS.Th2.P85.Sp

section Transport

variable {G G' : Type*} [Group G] [Group G'] {N : Subgroup G} {W : Subgroup G'}

theorem fusion_transport_dom (ψ : ↥N ≃* ↥W) {x y : G} (hx : x ∈ N) (hy : y ∈ N)
    (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdom : ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({y} : Set G) ⊓ N) →
      2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) :
    (∀ n' ∈ W, n' * ((ψ ⟨x, hx⟩ : ↥W) : G') * n'⁻¹ ≠ ((ψ ⟨y, hy⟩ : ↥W) : G')) ∧
      ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({((ψ ⟨y, hy⟩ : ↥W) : G')} : Set G') ⊓ W) →
        2 ^ k ∣ Nat.card ↥(centralizer ({((ψ ⟨x, hx⟩ : ↥W) : G')} : Set G') ⊓ W) := by
  refine ⟨?_, fun k hk => ?_⟩
  · intro n' hn' h
    obtain ⟨n, hn, rfl⟩ := Corr.exists_elt ψ hn'
    apply hynot n hn
    have h1 : ψ (⟨n, hn⟩ * ⟨x, hx⟩ * ⟨n, hn⟩⁻¹) = ψ ⟨y, hy⟩ := by
      rw [map_mul, map_mul, map_inv]
      exact Subtype.ext h
    exact congrArg Subtype.val (ψ.injective h1)
  · have hx' := (SCorr.singleton hx rfl (ψ := ψ)).centralizer.card_eq
    have hy' := (SCorr.singleton hy rfl (ψ := ψ)).centralizer.card_eq
    rw [← hy'] at hk
    rw [← hx']
    exact hdom k hk

end Transport

section Models

variable {G : Type*} [Group G] [Finite G]

theorem leaf3_m12_dom {N H K Q : Subgroup G} (hF : M12AutFacts N H) (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (hQC : Q ≤ centralizer (K : Set G) ⊓ N)
    (hQs : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N)) {x : G} (hxQ : x ∈ Q)
    (hx2 : orderOf x = 2) (hKx : ∀ k ∈ K, k * x = x * k) {y : G} (hyN : y ∈ N)
    (hy2 : orderOf y = 2) (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdom : ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({y} : Set G) ⊓ N) →
      2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) :
    Nat.card ↥(centralizer ({y} : Set G) ⊓ N) = 240 ∧
      Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 ∧ ∃ n ∈ N, n * y * n⁻¹ ∈ Q := by
  obtain ⟨tO, tB, tA, M, htO, htOH, htB, htA, hOo, hBo, hAo, hcover, hcO, hcB, hcA, hM, hder, hOA,
    hOM⟩ := hF.data
  have hxN : x ∈ N := (hQC hxQ).2
  have hKC : K ≤ centralizer ({x} : Set G) ⊓ N := fun k hk =>
    ⟨mem_centralizer_singleton_iff.2 (hKx k hk), hHN (hKH hk)⟩
  obtain ⟨c, hc, h | h | h⟩ := hcover x hxN hx2
  ·
    exfalso
    have hcx : Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 240 := by
      rw [h, card_cent_conj hc, hcO]
    obtain ⟨c', hc', h' | h' | h'⟩ := hcover y hyN hy2
    · refine hynot (c' * c⁻¹) (N.mul_mem hc' (N.inv_mem hc)) ?_
      rw [h, h']
      group
    · have := hdom 7 (by rw [h', card_cent_conj hc', hcB]; norm_num)
      rw [hcx] at this
      norm_num at this
    · have := hdom 5 (by rw [h', card_cent_conj hc', hcA]; norm_num)
      rw [hcx] at this
      norm_num at this
  ·
    exfalso
    have hd := Subgroup.card_dvd_of_le hKC
    rw [a5_card e, h, card_cent_conj hc, hcB] at hd
    norm_num at hd
  · have hcx : Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 := by
      rw [h, card_cent_conj hc, hcA]
    obtain ⟨c', hc', h' | h' | h'⟩ := hcover y hyN hy2
    ·
      have hcy : Nat.card ↥(centralizer ({y} : Set G) ⊓ N) = 240 := by
        rw [h', card_cent_conj hc', hcO]
      have hdvd : Nat.card ↥(centralizer ({y} : Set G) ⊓ N) ∣
          Nat.card ↥(centralizer ({x} : Set G) ⊓ N) := by
        rw [hcy, hcx]
        norm_num
      exact ⟨hcy, hcx, leaf3_of_m12Facts hF hHN hnorm hKH e hQC hQs hxQ hx2 hKx hyN hy2 hynot hdvd⟩
    ·
      exfalso
      have := hdom 7 (by rw [h', card_cent_conj hc', hcB]; norm_num)
      rw [hcx] at this
      norm_num at this
    ·
      exfalso
      refine hynot (c' * c⁻¹) (N.mul_mem hc' (N.inv_mem hc)) ?_
      rw [h, h']
      group

theorem leaf3_j2_dom {N H K Q E : Subgroup G} (hF : J2AutFacts N H) (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hcard : Nat.card ↥N = 2 * Nat.card ↥H)
    (hKH : K ≤ H) (e : ↥K ≃* alternatingGroup (Fin 5)) (hQC : Q ≤ centralizer (K : Set G) ⊓ N)
    {x : G} (hxQ : x ∈ Q) (hx2 : orderOf x = 2) (hKx : ∀ k ∈ K, k * x = x * k) (hEQ : E ≤ Q)
    (hEa : IsElementaryAbelian 2 ↥E) (hE4 : 4 ≤ Nat.card ↥E) {y : G} (hyN : y ∈ N)
    (hy2 : orderOf y = 2) (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdom : ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({y} : Set G) ⊓ N) →
      2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) :
    Nat.card ↥(centralizer ({y} : Set G) ⊓ N) = 672 ∧
      Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 ∧
      ∀ t ∈ H, orderOf t = 2 → ¬ 7 ∣ Nat.card ↥(centralizer ({t} : Set G) ⊓ N) := by
  obtain ⟨tO, tB, tA, vA, vB, htO, htOH, htB, htA, hvA, hvAH, hvB, hvBH, hOo, hBo, hAo, hvAo, hvBo,
    hvAc, hvBc, hcover, hcHO, hcHB, hcHA, hcent5, hcent5o⟩ := hF.data
  have hxN : x ∈ N := (hQC hxQ).2
  have hKC : K ≤ centralizer ({x} : Set G) ⊓ N := fun k hk =>
    ⟨mem_centralizer_singleton_iff.2 (hKx k hk), hHN (hKH hk)⟩
  have hcO : Nat.card ↥(centralizer ({tO} : Set G) ⊓ N) = 672 := by
    rw [card_cent_of_outer hHN hcard htO htOH rfl, hcHO]
  have hcB : Nat.card ↥(centralizer ({tB} : Set G) ⊓ N) = 480 := by
    rw [card_cent_of_outer hHN hcard hvB hvBH hvBc, hcHB]
  have hcA : Nat.card ↥(centralizer ({tA} : Set G) ⊓ N) = 3840 := by
    rw [card_cent_of_outer hHN hcard hvA hvAH hvAc, hcHA]
  have h7 : ∀ t ∈ H, orderOf t = 2 → ¬ 7 ∣ Nat.card ↥(centralizer ({t} : Set G) ⊓ N) := by
    intro t htH ht2
    have htN : t ∈ N := hHN htH
    obtain ⟨c, hc, h | h | h⟩ := hcover t htN ht2
    · exfalso
      apply htOH
      have : tO = c⁻¹ * t * c⁻¹⁻¹ := by rw [h]; group
      rw [this]
      exact hnorm c⁻¹ (N.inv_mem hc) t htH
    · rw [h, card_cent_conj hc, hcB]
      norm_num
    · rw [h, card_cent_conj hc, hcA]
      norm_num
  obtain ⟨c, hc, h | h | h⟩ := hcover x hxN hx2
  ·
    exfalso
    have hd := Subgroup.card_dvd_of_le hKC
    rw [a5_card e, h, card_cent_conj hc, hcO] at hd
    norm_num at hd
  ·
    have hcx : Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 := by
      rw [h, card_cent_conj hc, hcB]
    obtain ⟨c', hc', h' | h' | h'⟩ := hcover y hyN hy2
    · exact ⟨by rw [h', card_cent_conj hc', hcO], hcx, h7⟩
    · exfalso
      refine hynot (c' * c⁻¹) (N.mul_mem hc' (N.inv_mem hc)) ?_
      rw [h, h']
      group
    · exfalso
      have := hdom 8 (by rw [h', card_cent_conj hc', hcA]; norm_num)
      rw [hcx] at this
      norm_num at this
  ·
    exfalso
    have hcentN : ∀ z ∈ H, z ∈ centralizer ({tA} : Set G) → orderOf z = 5 →
        ∀ c' ∈ N, c' ∈ centralizer ({tA} : Set G) → c' * z = z * c' →
          ∃ j : ℕ, c' = z ^ j ∨ c' = tA * z ^ j := by
      intro z hz hzc hz5 c' hc'N hc'c hc'z
      by_cases hc'H : c' ∈ H
      · exact hcent5 z hz hzc hz5 c' hc'H hc'c hc'z
      · exfalso
        have h0H : vA * c' ∈ H :=
          (mul_mem_iff_of_card hHN hcard hvA hc'N).2 (iff_of_false hvAH hc'H)
        have h0c : vA * c' ∈ centralizer ({tA} : Set G) := by
          rw [mem_centralizer_singleton_iff] at hc'c ⊢
          calc vA * c' * tA = vA * (c' * tA) := mul_assoc _ _ _
            _ = vA * (tA * c') := by rw [hc'c]
            _ = (vA * tA) * c' := (mul_assoc _ _ _).symm
            _ = (tA * vA) * c' := by rw [hvAc]
            _ = tA * (vA * c') := mul_assoc _ _ _
        apply hcent5o z hz hzc hz5 (vA * c') h0H h0c
        have hvv : vA * vA = 1 := by
          have := pow_orderOf_eq_one vA
          rwa [hvAo, pow_two] at this
        have : vA * (vA * c') = c' := by rw [← mul_assoc, hvv, one_mul]
        rw [this]
        exact hc'z
    obtain ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩ := conj_setup_N hc hnorm hKH e h hKx
    have ht2 : tA * tA = 1 := by
      have := pow_orderOf_eq_one tA
      rwa [hAo, pow_two] at this
    have hC : ∀ w ∈ Q, w * x = x * w → w = 1 ∨ w = x := by
      intro w hwQ hwx
      have hwC := hQC hwQ
      have hwN : w ∈ N := hwC.2
      have hwK : ∀ k ∈ K, k * w = w * k := fun k hk => mem_centralizer_iff.1 hwC.1 k hk
      have hw₁N : c⁻¹ * w * c ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hc) hwN) hc
      have hw₁t : c⁻¹ * w * c ∈ centralizer ({tA} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        rw [h] at hwx
        calc c⁻¹ * w * c * tA = c⁻¹ * (w * (c * tA * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * tA * c⁻¹) * w) * c := by rw [hwx]
          _ = tA * (c⁻¹ * w * c) := by group
      have hw₁K : ∀ k ∈ K₁, k * (c⁻¹ * w * c) = (c⁻¹ * w * c) * k := by
        intro k hk
        have h1 := hwK _ ((hmem k).1 hk)
        calc k * (c⁻¹ * w * c) = c⁻¹ * ((c * k * c⁻¹) * w) * c := by group
          _ = c⁻¹ * (w * (c * k * c⁻¹)) * c := by rw [h1]
          _ = c⁻¹ * w * c * k := by group
      have hw : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      rcases eq_one_or_eq_of_cent5₂ ht2 hcentN hK₁H hK₁t e₁ hw₁N hw₁t hw₁K with h1 | h1
      · left
        rw [hw, h1]
        group
      · right
        rw [hw, h1, h]
    have hle := card_le_two_of_centralizer_le hxQ hx2 hC hEQ (IsElementaryAbelian.isPGroup 2 ↥E)
    omega

end Models

section Generic

variable {G : Type} [Group G] [Finite G]

theorem spor_fusion_dom
    {N H K Q : Subgroup G} {x y : G} (cfg : SporAutCfg N H K Q x)
    (hyN : y ∈ N) (hy2 : orderOf y = 2) (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdom : ∀ k : ℕ, 2 ^ k ∣ Nat.card ↥(centralizer ({y} : Set G) ⊓ N) →
      2 ^ k ∣ Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) :
    (NativeSporadic.IsSporadic ↥H .M12 ∧
        Nat.card ↥(centralizer ({y} : Set G) ⊓ N) = 240 ∧
        Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 ∧ ∃ n ∈ N, n * y * n⁻¹ ∈ Q) ∨
      (NativeSporadic.IsSporadic ↥H .J2 ∧
        Nat.card ↥(centralizer ({y} : Set G) ⊓ N) = 672 ∧
        Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 ∧
        ∀ t ∈ H, orderOf t = 2 → ¬ 7 ∣ Nat.card ↥(centralizer ({t} : Set G) ⊓ N)) := by
  obtain ⟨E, hcfg⟩ := cfg.cfgData
  rcases cfg.sporadic with hM | hJ
  ·
    left
    refine ⟨hM, ?_⟩
    obtain ⟨e⟩ := hM
    have eD : ↥H ≃* ↥blockGroup := e.trans m12EquivD
    have hcardNR : Nat.card ↥N = Nat.card ↥autModel := by
      rw [cfg.index_two, Nat.card_congr eD.toEquiv, card_autModel_eq]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv m12_smallAutModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eD
    obtain ⟨K', Q', E', x', hC', -, hQ', -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    subst hx'
    obtain ⟨e'⟩ := hC'.K5
    obtain ⟨hynot', hdom'⟩ := fusion_transport_dom ψ hxN hyN hynot hdom
    obtain ⟨hc240, hc480, n', hn'W, hn'Q⟩ := leaf3_m12_dom m12_autFacts hC'.hHN hC'.hnorm
      hC'.hKH e' hC'.hQC hC'.hQs hC'.hxQ hC'.hx2 hC'.hKx (ψ ⟨y, hyN⟩).2
      ((orderOf_corr ψ ⟨y, hyN⟩).trans hy2) hynot' hdom'
    refine ⟨?_, ?_, Corr.pull_conj ψ hQ' hyN hn'W hn'Q⟩
    · rw [(SCorr.singleton hyN rfl (ψ := ψ)).centralizer.card_eq]
      exact hc240
    · rw [(SCorr.singleton hxN rfl (ψ := ψ)).centralizer.card_eq]
      exact hc480
  ·
    right
    refine ⟨hJ, ?_⟩
    obtain ⟨e⟩ := hJ
    have eP : ↥H ≃* ↥j2P := e.trans j2PermEquiv
    have hcardNR : Nat.card ↥N = Nat.card ↥j2R := by
      obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := ctuc_j2_normalizing_involution_permutation_model
      rw [cfg.index_two, Nat.card_congr eP.toEquiv, card_j2P, hRcard]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv j2_autModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eP
    obtain ⟨K', Q', E', x', hC', -, -, -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    subst hx'
    obtain ⟨e'⟩ := hC'.K5
    obtain ⟨hynot', hdom'⟩ := fusion_transport_dom ψ hxN hyN hynot hdom
    obtain ⟨hc672, hc480, h7⟩ := leaf3_j2_dom j2_autFacts hC'.hHN hC'.hnorm hC'.hcard hC'.hKH e'
      hC'.hQC hC'.hxQ hC'.hx2 hC'.hKx hC'.hEQ hC'.hEa hC'.hE4 (ψ ⟨y, hyN⟩).2
      ((orderOf_corr ψ ⟨y, hyN⟩).trans hy2) hynot' hdom'
    refine ⟨?_, ?_, ?_⟩
    · rw [(SCorr.singleton hyN rfl (ψ := ψ)).centralizer.card_eq]
      exact hc672
    · rw [(SCorr.singleton hxN rfl (ψ := ψ)).centralizer.card_eq]
      exact hc480
    · intro t htH ht2 h7t
      have htN : t ∈ N := cfg.socle.le htH
      have ht' := (hψ.mem_iff ⟨t, htN⟩).1 htH
      refine h7 _ ht' ((orderOf_corr ψ ⟨t, htN⟩).trans ht2) ?_
      rw [← (SCorr.singleton htN rfl (ψ := ψ)).centralizer.card_eq]
      exact h7t

end Generic

end CFSG.GH74.GLS.Th2.P85.Sp

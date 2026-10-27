module

public import CFSG.GH74.Generic.S45.LEvSporAut
public import CFSG.GH74.Generic.S45.LEvSporLeaf1

public section

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45

section Facts

variable {G : Type*} [Group G]

theorem conj_mem_iff {N H : Subgroup G} (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) {c : G}
    (hc : c ∈ N) (y : G) : c * y * c⁻¹ ∈ H ↔ y ∈ H := by
  refine ⟨fun h => ?_, hnorm c hc y⟩
  have := hnorm c⁻¹ (N.inv_mem hc) _ h
  simpa [mul_assoc] using this

theorem card_cent_conj {N : Subgroup G} {c : G} (hc : c ∈ N) (t : G) :
    Nat.card ↥(centralizer ({c * t * c⁻¹} : Set G) ⊓ N) =
      Nat.card ↥(centralizer ({t} : Set G) ⊓ N) := by
  have h := inf_centralizer_conj (H := N) (t := t) hc
  rw [inf_comm, h, Subgroup.card_map_of_injective (MulAut.conj c).injective, inf_comm]

theorem orderOf_conj' (c t : G) : orderOf (c * t * c⁻¹) = orderOf t := by
  have := MulEquiv.orderOf_eq (MulAut.conj c) t
  simpa [MulAut.conj_apply] using this

structure J2AutFacts (N H : Subgroup G) : Prop where
  data : ∃ tO tB tA vA vB : G, tO ∈ N ∧ tO ∉ H ∧ tB ∈ H ∧ tA ∈ H ∧ vA ∈ N ∧ vA ∉ H ∧ vB ∈ N ∧
    vB ∉ H ∧ orderOf tO = 2 ∧ orderOf tB = 2 ∧ orderOf tA = 2 ∧ orderOf vA = 2 ∧ orderOf vB = 2 ∧
    vA * tA = tA * vA ∧ vB * tB = tB * vB ∧
    (∀ y ∈ N, orderOf y = 2 →
      ∃ c ∈ N, y = c * tO * c⁻¹ ∨ y = c * tB * c⁻¹ ∨ y = c * tA * c⁻¹) ∧
    Nat.card ↥(centralizer ({tO} : Set G) ⊓ H) = 336 ∧
    Nat.card ↥(centralizer ({tB} : Set G) ⊓ H) = 240 ∧
    Nat.card ↥(centralizer ({tA} : Set G) ⊓ H) = 1920 ∧
    (∀ z ∈ H, z ∈ centralizer ({tA} : Set G) → orderOf z = 5 →
      ∀ c ∈ H, c ∈ centralizer ({tA} : Set G) → c * z = z * c →
        ∃ j : ℕ, c = z ^ j ∨ c = tA * z ^ j) ∧
    (∀ z ∈ H, z ∈ centralizer ({tA} : Set G) → orderOf z = 5 →
      ∀ c ∈ H, c ∈ centralizer ({tA} : Set G) → vA * c * z ≠ z * (vA * c))

theorem leaf2_of_j2Facts {N H : Subgroup G} (hF : J2AutFacts N H)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) {x : G} (hxN : x ∈ N) (hx2 : orderOf x = 2) :
    ∃ u ∈ N, u ∉ H ∧ orderOf u = 2 ∧ u * x = x * u := by
  obtain ⟨tO, tB, tA, vA, vB, htO, htOH, htB, htA, hvA, hvAH, hvB, hvBH, hOo, hBo, hAo, hvAo, hvBo,
    hvAc, hvBc, hcover, -, -, -, -, -⟩ := hF.data
  by_cases hxH : x ∈ H
  swap
  · exact ⟨x, hxN, hxH, hx2, rfl⟩
  obtain ⟨c, hc, h | h | h⟩ := hcover x hxN hx2
  · exfalso
    apply htOH
    have : tO = c⁻¹ * x * c⁻¹⁻¹ := by rw [h]; group
    rw [this]
    exact hnorm c⁻¹ (N.inv_mem hc) x hxH
  · refine ⟨c * vB * c⁻¹, N.mul_mem (N.mul_mem hc hvB) (N.inv_mem hc), ?_, ?_, ?_⟩
    · rw [conj_mem_iff hnorm hc]
      exact hvBH
    · rw [orderOf_conj', hvBo]
    · rw [h]
      calc c * vB * c⁻¹ * (c * tB * c⁻¹) = c * (vB * tB) * c⁻¹ := by group
        _ = c * (tB * vB) * c⁻¹ := by rw [hvBc]
        _ = c * tB * c⁻¹ * (c * vB * c⁻¹) := by group
  · refine ⟨c * vA * c⁻¹, N.mul_mem (N.mul_mem hc hvA) (N.inv_mem hc), ?_, ?_, ?_⟩
    · rw [conj_mem_iff hnorm hc]
      exact hvAH
    · rw [orderOf_conj', hvAo]
    · rw [h]
      calc c * vA * c⁻¹ * (c * tA * c⁻¹) = c * (vA * tA) * c⁻¹ := by group
        _ = c * (tA * vA) * c⁻¹ := by rw [hvAc]
        _ = c * tA * c⁻¹ * (c * vA * c⁻¹) := by group

structure M12AutFacts (N H : Subgroup G) : Prop where
  data : ∃ (tO tB tA : G) (M : Subgroup G), tO ∈ N ∧ tO ∉ H ∧ tB ∈ H ∧ tA ∈ H ∧ orderOf tO = 2 ∧
    orderOf tB = 2 ∧ orderOf tA = 2 ∧
    (∀ y ∈ N, orderOf y = 2 →
      ∃ c ∈ N, y = c * tO * c⁻¹ ∨ y = c * tB * c⁻¹ ∨ y = c * tA * c⁻¹) ∧
    Nat.card ↥(centralizer ({tO} : Set G) ⊓ N) = 240 ∧
    Nat.card ↥(centralizer ({tB} : Set G) ⊓ N) = 384 ∧
    Nat.card ↥(centralizer ({tA} : Set G) ⊓ N) = 480 ∧ Nat.card ↥M = 60 ∧
    (∀ x ∈ H, x ∈ centralizer ({tA} : Set G) → ∀ y ∈ H, y ∈ centralizer ({tA} : Set G) →
      ⁅x, y⁆ ∈ M) ∧
    tO * tA = tA * tO ∧ ∀ m ∈ M, m * tO = tO * m

theorem leaf2_of_m12Facts [Finite G] {N H K : Subgroup G} (hF : M12AutFacts N H) (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) {x : G} (hxN : x ∈ N) (hx2 : orderOf x = 2)
    (hKx : ∀ k ∈ K, k * x = x * k) :
    ∃ u ∈ N, u ∉ H ∧ orderOf u = 2 ∧ u * x = x * u := by
  obtain ⟨tO, tB, tA, M, htO, htOH, htB, htA, hOo, hBo, hAo, hcover, hcO, hcB, hcA, hM, hder, hOA,
    hOM⟩ := hF.data
  by_cases hxH : x ∈ H
  swap
  · exact ⟨x, hxN, hxH, hx2, rfl⟩
  obtain ⟨c, hc, h | h | h⟩ := hcover x hxN hx2
  · exfalso
    apply htOH
    have : tO = c⁻¹ * x * c⁻¹⁻¹ := by rw [h]; group
    rw [this]
    exact hnorm c⁻¹ (N.inv_mem hc) x hxH
  · exfalso
    have hKC : K ≤ centralizer ({x} : Set G) ⊓ N := fun k hk =>
      ⟨mem_centralizer_singleton_iff.2 (hKx k hk), hHN (hKH hk)⟩
    have hdvd := Subgroup.card_dvd_of_le hKC
    rw [a5_card e, h, card_cent_conj hc, hcB] at hdvd
    norm_num at hdvd
  · refine ⟨c * tO * c⁻¹, N.mul_mem (N.mul_mem hc htO) (N.inv_mem hc), ?_, ?_, ?_⟩
    · rw [conj_mem_iff hnorm hc]
      exact htOH
    · rw [orderOf_conj', hOo]
    · rw [h]
      calc c * tO * c⁻¹ * (c * tA * c⁻¹) = c * (tO * tA) * c⁻¹ := by group
        _ = c * (tA * tO) * c⁻¹ := by rw [hOA]
        _ = c * tA * c⁻¹ * (c * tO * c⁻¹) := by group

theorem leaf3_of_m12Facts [Finite G] {N H K Q : Subgroup G} (hF : M12AutFacts N H) (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hKH : K ≤ H)
    (e : ↥K ≃* alternatingGroup (Fin 5)) (hQC : Q ≤ centralizer (K : Set G) ⊓ N)
    (hQs : IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N)) {x : G} (hxQ : x ∈ Q)
    (hx2 : orderOf x = 2) (hKx : ∀ k ∈ K, k * x = x * k) {y : G} (hyN : y ∈ N)
    (hy2 : orderOf y = 2) (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdvd : Nat.card ↥(centralizer ({y} : Set G) ⊓ N) ∣
      Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) :
    ∃ n ∈ N, n * y * n⁻¹ ∈ Q := by
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
    · rw [hcx, h', card_cent_conj hc', hcB] at hdvd
      norm_num at hdvd
    · rw [hcx, h', card_cent_conj hc', hcA] at hdvd
      norm_num at hdvd
  ·
    exfalso
    have hd := Subgroup.card_dvd_of_le hKC
    rw [a5_card e, h, card_cent_conj hc, hcB] at hd
    norm_num at hd
  · have hcx : Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 := by
      rw [h, card_cent_conj hc, hcA]
    obtain ⟨c', hc', h' | h' | h'⟩ := hcover y hyN hy2
    ·
      obtain ⟨K₁, hmem, ⟨e₁⟩, hK₁H, hK₁t⟩ := conj_setup_N hc hnorm hKH e h hKx
      have hK₁M : K₁ = M :=
        eq_of_perfect_le_derived (D := H ⊓ centralizer ({tA} : Set G)) (le_inf hK₁H hK₁t)
          (a5_perfect e₁) (fun a ha b hb => hder a ha.1 ha.2 b hb.1 hb.2)
          (by rw [hM, a5_card e₁])
      have hw₀N : c * tO * c⁻¹ ∈ N := N.mul_mem (N.mul_mem hc htO) (N.inv_mem hc)
      have hw₀K : ∀ k ∈ K, k * (c * tO * c⁻¹) = (c * tO * c⁻¹) * k := by
        intro k hk
        have hmK : c⁻¹ * k * c ∈ K₁ := by
          rw [hmem]
          simpa [mul_assoc] using hk
        have hmM : c⁻¹ * k * c ∈ M := hK₁M ▸ hmK
        have := hOM _ hmM
        calc k * (c * tO * c⁻¹) = c * ((c⁻¹ * k * c) * tO) * c⁻¹ := by group
          _ = c * (tO * (c⁻¹ * k * c)) * c⁻¹ := by rw [this]
          _ = c * tO * c⁻¹ * k := by group
      have hw₀C : c * tO * c⁻¹ ∈ centralizer (K : Set G) ⊓ N :=
        ⟨mem_centralizer_iff.2 hw₀K, hw₀N⟩
      obtain ⟨g, hg, hgw⟩ := exists_conj_mem_sylow hQs hw₀C (by rw [orderOf_conj', hOo])
      have hw₁N : g⁻¹ * (c * tO * c⁻¹) * g ∈ N :=
        N.mul_mem (N.mul_mem (N.inv_mem hg.2) hw₀N) hg.2
      have hw₁H : g⁻¹ * (c * tO * c⁻¹) * g ∉ H := by
        intro hH
        apply htOH
        have h1 : g⁻¹ * (c * tO * c⁻¹) * g⁻¹⁻¹ ∈ H := by simpa using hH
        rw [conj_mem_iff hnorm (N.inv_mem hg.2)] at h1
        rwa [conj_mem_iff hnorm hc] at h1
      have hw₁2 : orderOf (g⁻¹ * (c * tO * c⁻¹) * g) = 2 := by
        have := orderOf_conj' g⁻¹ (c * tO * c⁻¹)
        rw [inv_inv] at this
        rw [this, orderOf_conj', hOo]
      obtain ⟨c₁, hc₁, h₁ | h₁ | h₁⟩ := hcover _ hw₁N hw₁2
      · refine ⟨c₁ * c'⁻¹, N.mul_mem hc₁ (N.inv_mem hc'), ?_⟩
        have : (c₁ * c'⁻¹) * y * (c₁ * c'⁻¹)⁻¹ = g⁻¹ * (c * tO * c⁻¹) * g := by
          rw [h₁, h']
          group
        rw [this]
        exact hgw
      · exact absurd ((h₁ ▸ (conj_mem_iff hnorm hc₁ tB).2 htB : _)) hw₁H
      · exact absurd ((h₁ ▸ (conj_mem_iff hnorm hc₁ tA).2 htA : _)) hw₁H
    ·
      exfalso
      rw [hcx, h', card_cent_conj hc', hcB] at hdvd
      norm_num at hdvd
    ·
      exfalso
      refine hynot (c' * c⁻¹) (N.mul_mem hc' (N.inv_mem hc)) ?_
      rw [h, h']
      group


theorem leaf3_of_j2Facts [Finite G] {N H K Q E : Subgroup G} (hF : J2AutFacts N H) (hHN : H ≤ N)
    (hnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H) (hcard : Nat.card ↥N = 2 * Nat.card ↥H)
    (hKH : K ≤ H) (e : ↥K ≃* alternatingGroup (Fin 5)) (hQC : Q ≤ centralizer (K : Set G) ⊓ N)
    {x : G} (hxQ : x ∈ Q) (hx2 : orderOf x = 2) (hKx : ∀ k ∈ K, k * x = x * k) (hEQ : E ≤ Q)
    (hEa : IsElementaryAbelian 2 ↥E) (hE4 : 4 ≤ Nat.card ↥E) {y : G} (hyN : y ∈ N)
    (hy2 : orderOf y = 2) (hynot : ∀ n ∈ N, n * x * n⁻¹ ≠ y)
    (hdvd : Nat.card ↥(centralizer ({y} : Set G) ⊓ N) ∣
      Nat.card ↥(centralizer ({x} : Set G) ⊓ N)) : False := by
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
  obtain ⟨c, hc, h | h | h⟩ := hcover x hxN hx2
  ·
    have hd := Subgroup.card_dvd_of_le hKC
    rw [a5_card e, h, card_cent_conj hc, hcO] at hd
    norm_num at hd
  ·
    have hcx : Nat.card ↥(centralizer ({x} : Set G) ⊓ N) = 480 := by
      rw [h, card_cent_conj hc, hcB]
    obtain ⟨c', hc', h' | h' | h'⟩ := hcover y hyN hy2
    · rw [hcx, h', card_cent_conj hc', hcO] at hdvd
      norm_num at hdvd
    · refine hynot (c' * c⁻¹) (N.mul_mem hc' (N.inv_mem hc)) ?_
      rw [h, h']
      group
    · rw [hcx, h', card_cent_conj hc', hcA] at hdvd
      norm_num at hdvd
  ·
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

end Facts

end CFSG.GH74.Generic.S45

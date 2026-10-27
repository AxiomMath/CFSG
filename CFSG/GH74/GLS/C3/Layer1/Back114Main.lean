module

public import CFSG.GH74.GLS.C3.Layer1.Back114W
public import CFSG.GH74.GLS.C3.Layer1.BackAuxSA
public import CFSG.GH74.GLS.C3.Layer1.BackStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {x : G} {K L M T Q : Subgroup G}

theorem aconfigW_of_concl (hh : Hyp9A x K L M T Q) (p91 : Prop91Concl K M T Q)
    (l113 : Lemma113Concl x K L M T Q) :
    ∃ n ∈ ({5, 6, 7} : Finset ℕ), ∃ (S : Subgroup G) (a : G), IsAConfigW n x K T Q S a := by
  obtain ⟨⟨hQab, hQ4⟩, -, -, -⟩ := p91
  obtain ⟨hnot, hKL, hterm, n, hn, ⟨e0⟩, hψ, hfive⟩ := l113
  refine ⟨n, hn, ?_⟩
  obtain ⟨ψ₀, hker⟩ := hψ
  subst hKL
  obtain ⟨S, hSsyl, hTS, a, haS, haN, haT, ha2⟩ :=
    exists_sylow_gt_and_a hh.sylowT.isPGroup hnot
  have hCM := hh.centralizer_le
  have hQsubN : Q ≤ CxK x K := by rw [hh.hQ]; exact inf_le_right
  have hNle : CxK x K ≤ CMK M K := fun n hn => ⟨hCM hn.1, hn.2⟩
  refine ⟨S, a, ?_⟩
  exact
    { twoTerminal := hh.twoTerminal
      terminal := hterm
      kbar := ⟨e0⟩
      normalInC := fun c hc k hk => hh.L_normal.2 c (hCM hc) k hk
      sylowT := hh.sylowT
      hQ := hh.hQ
      sylowQ := hh.sylowQ.of_le hQsubN hNle
      card_Q := hQ4
      elemQ := hQab
      sylowS := hSsyl
      T_lt_S := hTS
      a_mem := ⟨haS, haN, haT, ha2⟩
      cond6 := fun hcen u hu hu1 => by
        have hu' : u ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Q) u hu
        exact hh.cent5 u hu (fun t ht => hcen u hu t ht) (orderOf_eq_prime hu' hu1)
      quotientType := ⟨ψ₀.comp (Subgroup.inclusion hCM), by
        ext c
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        have h1 : (ψ₀.comp (Subgroup.inclusion hCM)) c = 1 ↔
            (Subgroup.inclusion hCM c) ∈ ψ₀.ker := by
          rw [MonoidHom.mem_ker]; rfl
        rw [h1, hker, Subgroup.mem_subgroupOf]
        show (c : G) ∈ CMK M K ↔ (c : G) ∈ CxK x K
        constructor
        · intro hc; exact ⟨c.2, hc.2⟩
        · intro hc; exact ⟨hCM c.2, hc.2⟩⟩
      fiveCase := hfive }

end CFSG.GH74.GLS.C3.Layer1.Back

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

section Steps

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

namespace IsAConfigW

theorem conj_W_le_U (h : IsAConfigW n x K T Q S a) :
    (pPrimeCoreOf 2 (centralizer ({x} : Set G))).map (MulAut.conj a).toMonoidHom ≤
      pPrimeCoreOf 2 (centralizer ((Ysub x K T a : Subgroup G) : Set G)) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set W : Subgroup G := pPrimeCoreOf 2 C with hW
  set A : Subgroup G := W.map (MulAut.conj a).toMonoidHom with hA
  have hAmem : ∀ g ∈ A, ∃ w ∈ W, g = a * w * a⁻¹ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have hYA : Ysub x K T a ≤ centralizer (A : Set G) := by
    unfold Ysub
    refine sup_le ?_ ?_
    · rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨w, hw, rfl⟩ := hAmem g hg
      have hpw : p * w = w * p := h.W_centralizes_K hw hp.2
      show a * w * a⁻¹ * (a * p * a⁻¹) = a * p * a⁻¹ * (a * w * a⁻¹)
      calc a * w * a⁻¹ * (a * p * a⁻¹) = a * (w * p) * a⁻¹ := by group
        _ = a * (p * w) * a⁻¹ := by rw [hpw]
        _ = a * p * a⁻¹ * (a * w * a⁻¹) := by group
    · refine zpowers_le.2 ?_
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨w, hw, rfl⟩ := hAmem g hg
      have hxw : w * x = x * w := mem_centralizer_singleton_iff.1 (W_le_C hw)
      calc a * w * a⁻¹ * (a * x * a⁻¹) = a * (w * x) * a⁻¹ := by group
        _ = a * (x * w) * a⁻¹ := by rw [hxw]
        _ = a * x * a⁻¹ * (a * w * a⁻¹) := by group
  have hAY : A ≤ centralizer ((Ysub x K T a : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.1 (hYA hy) g hg).symm
  have hzY : a * x * a⁻¹ ∈ (Ysub x K T a : Subgroup G) := by
    unfold Ysub
    exact Subgroup.mem_sup_right (mem_zpowers _)
  refine le_pPrimeCoreOf_of_normal hAY ?_ ?_
  · intro g hg y hy
    obtain ⟨w, hw, rfl⟩ := hAmem y hy
    have hgz : (a * x * a⁻¹) * g = g * (a * x * a⁻¹) := (mem_centralizer_iff.1 hg) _ hzY
    have hcC : a⁻¹ * g * a ∈ C := by
      refine mem_centralizer_singleton_iff.2 ?_
      calc a⁻¹ * g * a * x = a⁻¹ * (g * (a * x * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * x * a⁻¹) * g) * a := by rw [hgz]
        _ = x * (a⁻¹ * g * a) := by group
    have hw' := W_normal hcC hw
    refine ⟨(a⁻¹ * g * a) * w * (a⁻¹ * g * a)⁻¹, hw', ?_⟩
    show a * ((a⁻¹ * g * a) * w * (a⁻¹ * g * a)⁻¹) * a⁻¹ = g * (a * w * a⁻¹) * g⁻¹
    group
  · rw [hA, card_map_conj]
    exact TwoThin.card_pPrimeCoreOf_odd C

theorem U_le_W (h : IsAConfigW n x K T Q S a)
    (hA2 : ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G),
      Odd (orderOf u) → u ∈ CxK x K) :
    pPrimeCoreOf 2 (centralizer ((Ysub x K T a : Subgroup G) : Set G)) ≤
      pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
  intro u hu
  have hodd := odd_orderOf_of_mem_pPrimeCoreOf hu
  have huY : u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G) := TwoThin.pPrimeCoreOf_le _ hu
  exact h.odd_mem_W (hA2 u huY hodd) hodd

theorem a_mem_normalizer_W (h : IsAConfigW n x K T Q S a)
    (hA2 : ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G),
      Odd (orderOf u) → u ∈ CxK x K) :
    a ∈ normalizer (pPrimeCoreOf 2 (centralizer ({x} : Set G)) : Set G) := by
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({x} : Set G)) with hW
  have hle : W.map (MulAut.conj a).toMonoidHom ≤ W := (h.conj_W_le_U).trans (h.U_le_W hA2)
  have hcard : Nat.card ↥W ≤ Nat.card ↥(W.map (MulAut.conj a).toMonoidHom) := by
    rw [card_map_conj]
  have heq : W.map (MulAut.conj a).toMonoidHom = W := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have : a * w * a⁻¹ ∈ W.map (MulAut.conj a).toMonoidHom := ⟨w, hw, rfl⟩
    rwa [heq] at this
  · intro hw
    rw [← heq] at hw
    obtain ⟨w', hw', hw'eq⟩ := hw
    have h2 : a * w' * a⁻¹ = a * w * a⁻¹ := hw'eq
    have h3 : w' = w := by
      calc w' = a⁻¹ * (a * w' * a⁻¹) * a := by group
        _ = a⁻¹ * (a * w * a⁻¹) * a := by rw [h2]
        _ = w := by group
    rwa [← h3]

end IsAConfigW

end Steps

end CFSG.GH74.GLS

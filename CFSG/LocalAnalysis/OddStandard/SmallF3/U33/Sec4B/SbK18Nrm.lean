module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_inf_centralizer_of_normalizer {P A : Subgroup G}
    (hP : IsSylowIn 2 P (normalizer (A : Set G))) :
    IsSylowIn 2 (P ⊓ centralizer (A : Set G)) (centralizer (A : Set G)) := by
  set N : Subgroup G := normalizer (A : Set G) with hN
  set C : Subgroup G := centralizer (A : Set G) with hC
  have hPNsylow : IsSylowIn 2 P N := by rw [hN]; exact hP
  have hCN : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have hna : n⁻¹ * a * n ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp (by rwa [hN] at hn) a).mp ha
    have hcomm := hc (n⁻¹ * a * n) hna
    calc a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * c * n⁻¹) * a := by group
  have hC2 : IsPGroup 2 ↥(P ⊓ C) := hP.2.1.to_inf_left
  have hPCC : P ⊓ C ≤ C := inf_le_right
  obtain ⟨T, hTsylow, hPT⟩ := exists_isSylowIn_of_le hPCC hC2
  have hTCN : C ≤ N := by
    rw [hC, hN]
    exact Subgroup.centralizer_le_normalizer (A : Set G)
  have hTN : T ≤ N := hTsylow.1.trans hTCN
  obtain ⟨T₂, hT₂sylow, hTT₂⟩ := exists_isSylowIn_of_le hTN hTsylow.2.1
  obtain ⟨n, hnN, hncj⟩ := exists_cj_of_isSylowIn hPNsylow hT₂sylow
  have hCn : cj n C = C := cj_eq_self_of_normalizes (hCN n hnN)
  have hle : T ≤ cj n (P ⊓ C) := by
    rw [cj_inf, hncj, hCn]
    exact le_inf hTT₂ hTsylow.1
  have hcardT : Nat.card T ≤ Nat.card ↥(P ⊓ C) := by
    have h1 : Nat.card T ≤ Nat.card (cj n (P ⊓ C)) := Subgroup.card_le_of_le hle
    rwa [card_cj] at h1
  have hEq : P ⊓ C = T := Subgroup.eq_of_le_of_card_ge hPT hcardT
  rw [hEq]
  exact hTsylow

theorem cj_cent_singleton {t u h : G} (hh : h * t * h⁻¹ = u) :
    cj h (centralizer ({t} : Set G)) = centralizer ({u} : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have hcon := congrArg (fun z => h * z * h⁻¹) hx
    have e1 : h * ((h⁻¹ * x * h) * t) * h⁻¹ = x * u := by
      rw [← hh]; group
    have e2 : h * (t * (h⁻¹ * x * h)) * h⁻¹ = u * x := by
      rw [← hh]; group
    rw [e1, e2] at hcon
    exact hcon
  · intro hx
    have hcon := congrArg (fun z => h⁻¹ * z * h) hx
    have e1 : h⁻¹ * (x * u) * h = (h⁻¹ * x * h) * t := by
      rw [← hh]; group
    have e2 : h⁻¹ * (u * x) * h = t * (h⁻¹ * x * h) := by
      rw [← hh]; group
    rw [e1, e2] at hcon
    exact hcon

theorem card_le_of_le_centralizer_conj {S P : Subgroup G} {t u h : G}
    (hS : IsSylowIn 2 S (centralizer ({t} : Set G))) (hScard : Nat.card S = 2 ^ 7)
    (hh : h * t * h⁻¹ = u) (hP2 : IsPGroup 2 P) (hP : P ≤ centralizer ({u} : Set G)) :
    Nat.card P ≤ 2 ^ 7 := by
  have hh' : h⁻¹ * u * (h⁻¹)⁻¹ = t := by rw [inv_inv, ← hh]; group
  have hcent : cj h⁻¹ (centralizer ({u} : Set G)) = centralizer ({t} : Set G) :=
    cj_cent_singleton (t := u) (u := t) (h := h⁻¹) hh'
  have hle : cj h⁻¹ P ≤ centralizer ({t} : Set G) := by
    rw [← hcent]
    exact cj_mono hP
  have hP'2 : IsPGroup 2 (cj h⁻¹ P) := isPGroup_cj hP2
  obtain ⟨T, hTsylow, hP'T⟩ :=
    exists_isSylowIn_of_le (K := centralizer ({t} : Set G)) hle hP'2
  obtain ⟨c, _hcC, hcj⟩ := exists_cj_of_isSylowIn hS hTsylow
  calc Nat.card P = Nat.card (cj h⁻¹ P) := (card_cj h⁻¹ P).symm
    _ ≤ Nat.card T := Subgroup.card_le_of_le hP'T
    _ = Nat.card (cj c S) := by rw [hcj]
    _ = Nat.card S := card_cj c S
    _ = 2 ^ 7 := hScard

theorem mem_normalizer_of_conj_le {A : Subgroup G} {g : G} (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    g ∈ normalizer (A : Set G) := by
  have hle : cj g A ≤ A := by
    intro x hx
    rw [mem_cj] at hx
    have hx' := h (g⁻¹ * x * g) hx
    convert hx' using 1
    group
  have heq : cj g A = A :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_cj g A).symm)
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    have hx' : x ∈ cj g A := by rw [heq]; exact hx
    rwa [mem_cj] at hx'
  · intro hx
    have hx' := h (g⁻¹ * x * g) hx
    convert hx' using 1
    group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

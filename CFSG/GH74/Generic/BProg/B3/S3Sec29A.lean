module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29A

variable {G : Type} [Group G] [Finite G]

theorem card_mul_le_card_inf_mul {A B C : Subgroup G} (hAB : A ≤ B) (hCB : C ≤ B) :
    Nat.card ↥A * Nat.card ↥C ≤ Nat.card ↥(C ⊓ A) * Nat.card ↥B := by
  have h1 := Subgroup.relIndex_mul_card (H := C) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := C) (K := B)
  have h3 : C ⊓ B = C := inf_eq_left.2 hCB
  rw [h3] at h2
  have hne : C.relIndex B ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := ↥B)).ne h2
  have h4 : C.relIndex A ≤ C.relIndex B := Subgroup.relIndex_le_of_le_right hAB hne
  calc Nat.card ↥A * Nat.card ↥C
      = (C.relIndex A * Nat.card ↥(C ⊓ A)) * Nat.card ↥C := by rw [h1]
    _ ≤ (C.relIndex B * Nat.card ↥(C ⊓ A)) * Nat.card ↥C := by gcongr
    _ = Nat.card ↥(C ⊓ A) * (C.relIndex B * Nat.card ↥C) := by ring
    _ = Nat.card ↥(C ⊓ A) * Nat.card ↥B := by rw [h2]

theorem comm_mem_cSec_of_mem_sup {B D J : Subgroup G} {b : G}
    (hDB : D ≤ B) (hb : b ∈ centralizer (B : Set G))
    (hcomp : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hDN : D ≤ normalizer (J : Set G))
    (hDsq : ∀ d ∈ D, d * d = 1) {d₀ : G} (hd₀ : d₀ ∈ D) (hd₀1 : d₀ ≠ 1) {c : G}
    (hc : c ∈ AG D ⊓ centralizer ({b} : Set G)) {d' c' : G} (hd' : d' ∈ D)
    (hc' : c' ∈ cSec J) : ⁅c, d' * c'⁆ ∈ cSec J := by
  have hDH : D ≤ centralizer ({b} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hb x (hDB hx))
  have hcN : c ∈ normalizer (J : Set G) :=
    Obs.inf_AG_le_normalizer hDH hDsq hcomp hDN hd₀ hd₀1 hc
  have hcO := TwoThin.mem_normalizer_pPrimeCoreOf hcN
  have hcc' : ⁅c, c'⁆ ∈ cSec J := by
    have h1 := Obs.conj_mem_centralizerSection hcN hcO hc'
    have h2 : ⁅c, c'⁆ = (c * c' * c⁻¹) * c'⁻¹ := by
      simp only [commutatorElement_def]
    rw [h2]
    exact (cSec J).mul_mem h1 ((cSec J).inv_mem hc')
  have hcd : c * d' = d' * c :=
    (mem_centralizer_iff.mp (Th2Sig6.AG_le_centralizer hc.1) d' hd').symm
  have hd'N : d' ∈ normalizer (J : Set G) := hDN hd'
  have hd'O := TwoThin.mem_normalizer_pPrimeCoreOf hd'N
  have h3 : ⁅c, d' * c'⁆ = d' * ⁅c, c'⁆ * d'⁻¹ := by
    calc ⁅c, d' * c'⁆ = (c * d') * c' * c⁻¹ * c'⁻¹ * d'⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (d' * c) * c' * c⁻¹ * c'⁻¹ * d'⁻¹ := by rw [hcd]
      _ = d' * ⁅c, c'⁆ * d'⁻¹ := by simp only [commutatorElement_def]; group
  rw [h3]
  exact Obs.conj_mem_centralizerSection hd'N hd'O hcc'

theorem obs52_quot {B : Subgroup G} {b : G} {D J : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB16 : Nat.card ↥B = 16) (h : Obs52 B b D J) :
    2 ^ 3 * Nat.card ↥(B ⊓ cSec J) ≤ Nat.card ↥B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hDB, hDel, hDrk⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hDcard := C3.Layer1.Back.card_eq_two_pow_pRank hDel
  have hDC : ∀ x ∈ D, x ∈ B ⊓ cSec J → x = 1 := fun x hx hxC => by
    by_contra hx1
    exact h.D_faith x hx hx1 (Subgroup.mem_inf.1 hxC).2
  have hle := Obs.card_mul_le_of_trivial_inter hDB (inf_le_left : B ⊓ cSec J ≤ B) hDC
  rcases h.unbal with ⟨hD3, -⟩ | ⟨hD2, c, hc, e, heB, hce⟩
  · rw [hDcard, hD3] at hle
    exact hle
  · rw [hDcard, hD2] at hle
    obtain ⟨d₀, hd₀, hd₀1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) (by omega)
      (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
    have hcomm : ∀ d ∈ D, ∀ k ∈ B ⊓ cSec J, d * k = k * d := fun d hd k hk =>
      hBc d (hDB hd) k (Subgroup.mem_inf.1 hk).1
    have hi : D ⊓ (B ⊓ cSec J) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      exact Subgroup.mem_bot.2 (hDC z (Subgroup.mem_inf.1 hz).1 (Subgroup.mem_inf.1 hz).2)
    have hMcard := S3Theta52.card_sup_of_commute hcomm hi
    have hMB : D ⊔ (B ⊓ cSec J) ≤ B := sup_le hDB inf_le_left
    have heM : e ∉ D ⊔ (B ⊓ cSec J) := by
      intro heM
      obtain ⟨d', hd', c', hc', rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm heM
      exact hce (comm_mem_cSec_of_mem_sup hDB h.b_cent h.comp h.D_norm hDsq hd₀ hd₀1 hc hd'
        (Subgroup.mem_inf.1 hc').2)
    have hlt : D ⊔ (B ⊓ cSec J) < B :=
      lt_of_le_of_ne hMB (fun hEq => heM (by rw [hEq]; exact heB))
    have h2 := Obs.two_mul_card_le_of_lt hlt
    have hD4 : Nat.card ↥D = 4 := by rw [hDcard, hD2]; norm_num
    rw [hMcard, hD4] at h2
    omega

theorem obs32_quot {A B D J : Subgroup G} {y : G} (hAB : A ≤ B) (hA : IsE 3 ⊤ A)
    (hA8 : Nat.card ↥A = 8) (hA3 : pRank 2 ↥A ≤ 3) (hyA : y ∈ A) (h : Obs32 A y D J) :
    2 ^ 2 * Nat.card ↥(B ⊓ cSec J) ≤ Nat.card ↥B := by
  have hcA := h.cA_eq hA hA3 hyA
  have hle := card_mul_le_card_inf_mul hAB (inf_le_left : B ⊓ cSec J ≤ B)
  have hsub : (B ⊓ cSec J) ⊓ A ≤ zpowers y := by
    intro z hz
    obtain ⟨hzC, hzA⟩ := Subgroup.mem_inf.1 hz
    rcases hcA z hzA (Subgroup.mem_inf.1 hzC).2 with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers y
  have hz2 : Nat.card ↥(zpowers y) = 2 := by rw [Nat.card_zpowers, h.y_ord]
  have h2 : Nat.card ↥((B ⊓ cSec J) ⊓ A) ≤ 2 := hz2 ▸ Subgroup.card_le_of_le hsub
  rw [hA8] at hle
  have : 8 * Nat.card ↥(B ⊓ cSec J) ≤ 2 * Nat.card ↥B :=
    hle.trans (Nat.mul_le_mul_right _ h2)
  omega

end S3Sec29A

end CFSG.GH74.Generic.BProg.B3

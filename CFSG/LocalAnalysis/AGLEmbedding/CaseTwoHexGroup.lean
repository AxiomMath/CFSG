module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open scoped Pointwise

variable {X : Type*} [Group X]

theorem d1_isElemAbelian_sup_of_le_centralizer {p : ℕ} {A B : Subgroup X}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hAB : A ≤ Subgroup.centralizer (B : Set X)) : IsElemAbelian p (A ⊔ B) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set X) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1
  have hBB : B ≤ Subgroup.centralizer (B : Set X) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hB.1
  have hBA : B ≤ Subgroup.centralizer (A : Set X) := Subgroup.le_centralizer_iff.mp hAB
  refine ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp (sup_le ?_ ?_), fun x hx => ?_⟩
  · exact Subgroup.le_centralizer_iff.mp (sup_le hAA hBA)
  · exact Subgroup.le_centralizer_iff.mp (sup_le hAB hBB)
  · have hx' : x ∈ ((A : Set X) * (B : Set X)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B
        (hAB.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hc : Commute a b := (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
    rw [hc.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem d1_isElemAbelian_of_le {p : ℕ} {E F : Subgroup X} (hE : IsElemAbelian p E)
    (hFE : F ≤ E) : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem card_sup_of_le_centralizer {A B : Subgroup X}
    (hAB : B ≤ Subgroup.centralizer (A : Set X)) (hAB' : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := card_sup_mul_card_inf_eq_of_le_normalizer
    (hAB.trans (Subgroup.centralizer_le_normalizer _))
  rwa [hAB', Subgroup.card_bot, mul_one] at h1

theorem d1_mem_centralizer_of_rep {A : Subgroup X} {r u : X} (hr : r ∈ A)
    (hru : r⁻¹ * u ∈ Subgroup.centralizer (A : Set X)) :
    r ∈ Subgroup.centralizer ({u} : Set X) := by
  have hc := Subgroup.mem_centralizer_iff.mp hru r hr
  rw [mul_inv_cancel_left] at hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc r * u = r * (r⁻¹ * u * r) := by rw [← hc]
    _ = u * r := by group

theorem d1_mem_centralizer_of_rep_center {A : Subgroup X} {r u ζ : X}
    (hr : r ∈ A) (hru : r⁻¹ * u ∈ Subgroup.centralizer (A : Set X)) (hζA : ζ ∈ A)
    (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) :
    ζ ∈ Subgroup.centralizer ({u} : Set X) := by
  have h1 := Subgroup.mem_centralizer_iff.mp hζC r hr
  have h2 := Subgroup.mem_centralizer_iff.mp hru ζ hζA
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hu : u = r * (r⁻¹ * u) := by group
  rw [hu, ← mul_assoc, ← h1, mul_assoc, h2, ← mul_assoc]

theorem exists_rep_of_mem_sup [Finite X] {A : Subgroup X} {u : X}
    (hin : u ∈ A ⊔ Subgroup.centralizer (A : Set X)) (hu3 : u ^ 3 = 1)
    (hnC : u ∉ Subgroup.centralizer (A : Set X)) :
    ∃ r ∈ A, (∃ k : ℕ, r ^ 3 ^ k = 1) ∧ r⁻¹ * u ∈ Subgroup.centralizer (A : Set X) ∧
      r ∉ Subgroup.centralizer (A : Set X) := by
  obtain ⟨r, hr, hr3, hrc⟩ := exists_pElt_of_mem_sup Nat.prime_three hin hu3
  refine ⟨r, hr, hr3, hrc, fun hrC => hnC ?_⟩
  have e : u = r * (r⁻¹ * u) := by group
  rw [e]
  exact Subgroup.mul_mem _ hrC hrc

theorem exists_center_of_card {A : Subgroup X} (hZ : Nat.card (Subgroup.center ↥A) = 3) :
    ∃ ζ ∈ A, ζ ∈ Subgroup.centralizer (A : Set X) ∧ ζ ≠ 1 ∧ ζ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (Subgroup.center A) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hc : 3 ∣ Nat.card (Subgroup.center A) := by rw [hZ]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hc
  refine ⟨((x : A) : X), (x : A).2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha'
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨a, ha'⟩)
  · intro h1
    have hx1 : x = 1 := Subtype.ext (Subtype.ext h1)
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg (fun y : Subgroup.center A => ((y : A) : X)) h3

theorem card_sup_zpowers_rep {A : Subgroup X} {r ζ : X} (hr : r ∈ A)
    (hrn : r ∉ Subgroup.centralizer (A : Set X)) (hr3 : r ^ 3 = 1)
    (hζC : ζ ∈ Subgroup.centralizer (A : Set X)) (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1) :
    Nat.card (Subgroup.zpowers r ⊔ Subgroup.zpowers ζ : Subgroup X) = 3 ^ 2 ∧
      IsElemAbelian 3 (Subgroup.zpowers r ⊔ Subgroup.zpowers ζ : Subgroup X) := by
  have hro : orderOf r = 3 := orderOf_eq_prime hr3 (fun h1 => hrn (h1 ▸ Subgroup.one_mem _))
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hrζ : r * ζ = ζ * r := Subgroup.mem_centralizer_iff.mp hζC r hr
  have hle : Subgroup.zpowers ζ ≤ Subgroup.centralizer (Subgroup.zpowers r : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute r ζ from hrζ) n).eq
  have hbot : Subgroup.zpowers r ⊓ Subgroup.zpowers ζ = ⊥ := by
    have h0 := zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hro hrn
    refine eq_bot_iff.mpr (le_trans (inf_le_inf_left _ ?_) h0.le)
    rw [Subgroup.zpowers_le]
    exact hζC
  refine ⟨?_, d1_isElemAbelian_sup_of_le_centralizer (isElemAbelian_zpowers_three hr3)
    (isElemAbelian_zpowers_three hζ3) (Subgroup.le_centralizer_iff.mp hle)⟩
  rw [card_sup_of_le_centralizer hle hbot, Nat.card_zpowers, Nat.card_zpowers, hro, hζo]
  norm_num

theorem card_three_reps_center {A₀ A₁ A₂ : Subgroup X}
    (h01 : A₁ ≤ Subgroup.centralizer (A₀ : Set X))
    (h02 : A₂ ≤ Subgroup.centralizer (A₀ : Set X))
    (h12 : A₂ ≤ Subgroup.centralizer (A₁ : Set X)) {r₀ r₁ r₂ ζ : X}
    (hr₀ : r₀ ∈ A₀) (hr₀n : r₀ ∉ Subgroup.centralizer (A₀ : Set X)) (hr₀3 : r₀ ^ 3 = 1)
    (hr₁ : r₁ ∈ A₁) (hr₁n : r₁ ∉ Subgroup.centralizer (A₁ : Set X)) (hr₁3 : r₁ ^ 3 = 1)
    (hr₂ : r₂ ∈ A₂) (hr₂n : r₂ ∉ Subgroup.centralizer (A₂ : Set X)) (hr₂3 : r₂ ^ 3 = 1)
    (hζA : ζ ∈ A₀) (hζC : ζ ∈ Subgroup.centralizer (A₀ : Set X)) (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) :
    Nat.card ((Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊔ Subgroup.zpowers r₁ ⊔
      Subgroup.zpowers r₂ : Subgroup X) = 3 ^ 4 ∧
    IsElemAbelian 3 ((Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ) ⊔ Subgroup.zpowers r₁ ⊔
      Subgroup.zpowers r₂ : Subgroup X) := by
  obtain ⟨hE₀c, hE₀e⟩ := card_sup_zpowers_rep hr₀ hr₀n hr₀3 hζC hζ1 hζ3
  set E₀ := Subgroup.zpowers r₀ ⊔ Subgroup.zpowers ζ with hE₀
  have hE₀A : E₀ ≤ A₀ := sup_le ((Subgroup.zpowers_le).mpr hr₀) ((Subgroup.zpowers_le).mpr hζA)
  have hr₁o : orderOf r₁ = 3 := orderOf_eq_prime hr₁3 (fun h1 => hr₁n (h1 ▸ Subgroup.one_mem _))
  have hr₂o : orderOf r₂ = 3 := orderOf_eq_prime hr₂3 (fun h1 => hr₂n (h1 ▸ Subgroup.one_mem _))
  have hE₀C₁ : E₀ ≤ Subgroup.centralizer (A₁ : Set X) :=
    hE₀A.trans (Subgroup.le_centralizer_iff.mp h01)
  have hc1 : Subgroup.zpowers r₁ ≤ Subgroup.centralizer (E₀ : Set X) :=
    ((Subgroup.zpowers_le).mpr hr₁).trans (h01.trans (Subgroup.centralizer_le hE₀A))
  have hd1 : E₀ ⊓ Subgroup.zpowers r₁ = ⊥ := by
    rw [inf_comm]
    exact eq_bot_iff.mpr (le_trans (inf_le_inf_left _ hE₀C₁)
      (zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hr₁o hr₁n).le)
  set E₁ := E₀ ⊔ Subgroup.zpowers r₁ with hE₁
  have hE₁c : Nat.card E₁ = 3 ^ 3 := by
    rw [hE₁, card_sup_of_le_centralizer hc1 hd1, hE₀c, Nat.card_zpowers, hr₁o]
    norm_num
  have hE₁e : IsElemAbelian 3 E₁ := d1_isElemAbelian_sup_of_le_centralizer hE₀e
    (isElemAbelian_zpowers_three hr₁3) (Subgroup.le_centralizer_iff.mp hc1)
  have hE₁C₂ : E₁ ≤ Subgroup.centralizer (A₂ : Set X) := by
    refine sup_le (hE₀A.trans (Subgroup.le_centralizer_iff.mp h02)) ?_
    exact ((Subgroup.zpowers_le).mpr hr₁).trans (Subgroup.le_centralizer_iff.mp h12)
  have hc2' : Subgroup.zpowers r₂ ≤ Subgroup.centralizer (E₁ : Set X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun e he =>
      (Subgroup.mem_centralizer_iff.mp (hE₁C₂ he) r₂ hr₂).symm
  have hd2 : E₁ ⊓ Subgroup.zpowers r₂ = ⊥ := by
    rw [inf_comm]
    exact eq_bot_iff.mpr (le_trans (inf_le_inf_left _ hE₁C₂)
      (zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hr₂o hr₂n).le)
  refine ⟨?_, d1_isElemAbelian_sup_of_le_centralizer hE₁e (isElemAbelian_zpowers_three hr₂3)
    (Subgroup.le_centralizer_iff.mp hc2')⟩
  rw [card_sup_of_le_centralizer hc2' hd2, hE₁c, Nat.card_zpowers, hr₂o]
  norm_num

theorem card_sup_zpowers_elem {F D : Subgroup X} {w : X} (hFD : F ≤ D) (hw3 : w ^ 3 = 1)
    (hwD : w ∉ D) (hFw : F ≤ Subgroup.centralizer ({w} : Set X)) (hF : IsElemAbelian 3 F) :
    Nat.card (F ⊔ Subgroup.zpowers w : Subgroup X) = Nat.card F * 3 ∧
      IsElemAbelian 3 (F ⊔ Subgroup.zpowers w : Subgroup X) := by
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 (fun h1 => hwD (h1 ▸ D.one_mem))
  have hFw' : F ≤ Subgroup.centralizer (Subgroup.zpowers w : Set X) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hFw hf)).symm n).eq)
  refine ⟨card_sup_zpowers Nat.prime_three hFD hwo hwD hFw', ?_⟩
  exact d1_isElemAbelian_sup_of_le_centralizer hF (isElemAbelian_zpowers_three hw3) hFw'

theorem d1_pow_three_of_mem_map_conj {A : Subgroup X}
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) {g r : X}
    (hr : r ∈ A.map (MulAut.conj g).toMonoidHom) (hrp : ∃ k : ℕ, r ^ 3 ^ k = 1) :
    r ^ 3 = 1 := by
  obtain ⟨s, hs, hsr⟩ := hr
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsr
  obtain ⟨k, hk⟩ := hrp
  have hsk : s ^ 3 ^ k = 1 := by
    rw [← hsr, conj_pow] at hk
    have := congrArg (fun y => g⁻¹ * y * g) hk
    simpa [mul_assoc] using this
  rw [← hsr, conj_pow, hb s hs ⟨k, hsk⟩, mul_one, mul_inv_cancel]

end CFSG.AGLEmbedding

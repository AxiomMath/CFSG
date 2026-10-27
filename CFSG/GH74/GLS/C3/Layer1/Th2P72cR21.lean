module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR3
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_lam_le {x t : G} {K J : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K) :
    ∃ Λ : Subgroup G, IsLam x t K Λ ∧ Λ ≤ J ∧ bar t Λ = bar t J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY : x ∈ centralizer ({t} : Set G) := TwoThin.mem_centralizer_symm hlt.2.2.1
  have hle : TwoThin.hatCard J ≤ TwoThin.hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, hJc, ⟨eΛ⟩, -, -, hcases⟩ := rigid_step hlt hxY hle
  have hvert : bar t Λ = bar t J := (hcases.resolve_right (fun h => h.1 hxJ)).2
  refine ⟨Λ, hΛ, ?_, hvert⟩
  have hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
  have hΛN : ∀ a ∈ Λ, a ∈ normalizer (J : Set G) := by
    intro a ha
    refine TwoThin.mem_normalizer_of_map_normalizes hJc.1 (TwoThin.isPCompIn_two_iff.mp hJc).2 (hΛY ha) ?_
    have h1 := map_conj_bar_of_normalizes (u := t) (X := Λ) (hΛY ha) (Subgroup.le_normalizer ha)
    rw [hvert] at h1
    exact h1
  have hΛperf : ⁅Λ, Λ⁆ = Λ := C3.Layer1.Bk.perfect_of_isPCompIn hΛ.pc
  set O' : Subgroup G := pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ normalizer (J : Set G)
    with hO'
  have hO'odd : Odd (Nat.card O') :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({t} : Set G)))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hlam : Λ ≤ J ⊔ O' := by
    intro a ha
    have hmem : TwoThin.barMk ↥(centralizer ({t} : Set G)) ⟨a, hΛY ha⟩ ∈ bar t J := by
      rw [← hvert]
      exact ⟨⟨a, hΛY ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    obtain ⟨j, hj, hjπ⟩ := hmem
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have h1 : TwoThin.barMk ↥(centralizer ({t} : Set G)) (j⁻¹ * ⟨a, hΛY ha⟩) = 1 := by
      rw [map_mul, map_inv, hjπ, inv_mul_cancel]
    have h2 : (j : G)⁻¹ * a ∈ pPrimeCoreOf 2 (centralizer ({t} : Set G)) :=
      (P85.barMk_eq_one_iff_mem_pPrimeCoreOf _).1 h1
    have h3 : (j : G)⁻¹ * a ∈ normalizer (J : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hjJ)) (hΛN a ha)
    have e1 : a = (j : G) * ((j : G)⁻¹ * a) := by group
    rw [e1]
    exact Subgroup.mul_mem_sup hjJ ⟨h2, h3⟩
  exact C3.Layer1.Bk.le_of_perfect_of_le_sup_odd hΛperf hO'odd inf_le_right hlam

theorem mem_pumpup_of_two_elt {x t p : G} {K J : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K) (hpK : p ∈ K) (hpt : p * t = t * p)
    (h2 : ∃ n : ℕ, p ^ (2 ^ n) = 1) : p ∈ J := by
  obtain ⟨Λ, hΛ, hΛJ, -⟩ := exists_lam_le hlt hxJ e
  exact hΛJ (hΛ.twoElt p ⟨hpK, mem_centralizer_singleton_iff.2 hpt⟩ h2)

theorem exists_inverted_element {A P₀ : Subgroup G} {z : G} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hA3 : pRank 2 ↥A = 3) (hodd : ¬ 2 ∣ Nat.card P₀) (hAN : A ≤ normalizer (P₀ : Set G))
    (hzA : z ∈ A) (hw : ∃ w ∈ P₀, z * w ≠ w * z) :
    ∃ (V : Subgroup G) (a : G), V ≤ A ∧ pRank 2 ↥V = 2 ∧ a ∈ P₀ ∧ (∀ v ∈ V, v * a = a * v) ∧
      z * a * z⁻¹ = a⁻¹ ∧ a ≠ 1 := by
  classical
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have hz2 : z * z = 1 := hAsq z hzA
  by_contra hno
  push Not at hno
  obtain ⟨w, hwP, hzw⟩ := hw
  have hgen : P₀ ≤ centralizer ({z} : Set G) := by
    refine Th2.L83.le_of_forall_inf_centralizer_rank 2 hAel (by omega) hodd hAN ?_
    intro F hFA hFr g hg
    obtain ⟨hgP, hgF⟩ := Subgroup.mem_inf.1 hg
    have hFel : CFSG.IsElementaryAbelian 2 ↥F := isElementaryAbelian_le hAel hFA
    have hFle : pRank 2 ↥F ≤ 3 := hA3 ▸ C3.Layer1.Back.pRank_mono' hFA
    by_cases hF3 : pRank 2 ↥F = 3
    ·
      have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hFel
      have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hAel
      have hFA' : F = A := Subgroup.eq_of_le_of_card_ge hFA (by rw [h1, h2, hF3, hA3])
      rw [mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.1 hgF z (hFA' ▸ hzA)
      exact this.symm
    · have hF2 : pRank 2 ↥F = 2 := by omega
      by_contra hgz
      have hgz' : z * g ≠ g * z := fun h => hgz (mem_centralizer_singleton_iff.2 h.symm)
      have hzP : z * g * z⁻¹ ∈ P₀ := (Subgroup.mem_normalizer_iff.1 (hAN hzA) g).1 hgP
      have haP : g⁻¹ * (z * g * z⁻¹) ∈ P₀ := P₀.mul_mem (P₀.inv_mem hgP) hzP
      have hcomm : ∀ v ∈ F, v * (g⁻¹ * (z * g * z⁻¹)) = (g⁻¹ * (z * g * z⁻¹)) * v := by
        intro v hv
        have hgv : v * g = g * v := Subgroup.mem_centralizer_iff.1 hgF v hv
        have hvz : v * z = z * v := hAc v (hFA hv) z hzA
        calc v * (g⁻¹ * (z * g * z⁻¹)) = (v * g⁻¹) * (z * g * z⁻¹) := by group
          _ = (g⁻¹ * v) * (z * g * z⁻¹) := by
            have : v * g⁻¹ = g⁻¹ * v := by
              calc v * g⁻¹ = g⁻¹ * (g * v) * g⁻¹ := by group
                _ = g⁻¹ * (v * g) * g⁻¹ := by rw [hgv]
                _ = g⁻¹ * v := by group
            rw [this]
          _ = g⁻¹ * ((v * z) * g * z⁻¹) := by group
          _ = g⁻¹ * ((z * v) * g * z⁻¹) := by rw [hvz]
          _ = g⁻¹ * (z * (v * g) * z⁻¹) := by group
          _ = g⁻¹ * (z * (g * v) * z⁻¹) := by rw [hgv]
          _ = g⁻¹ * (z * g * (v * z⁻¹)) := by group
          _ = g⁻¹ * (z * g * (z⁻¹ * v)) := by
            have : v * z⁻¹ = z⁻¹ * v := by
              calc v * z⁻¹ = z⁻¹ * (z * v) * z⁻¹ := by group
                _ = z⁻¹ * (v * z) * z⁻¹ := by rw [hvz]
                _ = z⁻¹ * v := by group
            rw [this]
          _ = (g⁻¹ * (z * g * z⁻¹)) * v := by group
      have hinv : z * (g⁻¹ * (z * g * z⁻¹)) * z⁻¹ = (g⁻¹ * (z * g * z⁻¹))⁻¹ := by
        have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        have e1 : z * (g⁻¹ * (z * g * z⁻¹)) * z⁻¹ = z * g⁻¹ * z * g * (z⁻¹ * z⁻¹) := by group
        have e0 : z⁻¹ * z⁻¹ = 1 := by rw [← mul_inv_rev, hz2, inv_one]
        have e3 : (g⁻¹ * (z * g * z⁻¹))⁻¹ = z * g⁻¹ * z⁻¹ * g := by group
        rw [e1, e0, mul_one, e3, hz1]
      have h1 := hno F (g⁻¹ * (z * g * z⁻¹)) hFA hF2 haP hcomm hinv
      apply hgz'
      have : z * g * z⁻¹ = g := by
        calc z * g * z⁻¹ = g * (g⁻¹ * (z * g * z⁻¹)) := by group
          _ = g := by rw [h1]; group
      calc z * g = z * g * z⁻¹ * z := by group
        _ = g * z := by rw [this]
  exact hzw (Subgroup.mem_centralizer_singleton_iff.1 (hgen hwP)).symm

end CFSG.GH74.GLS.Th2.Obs

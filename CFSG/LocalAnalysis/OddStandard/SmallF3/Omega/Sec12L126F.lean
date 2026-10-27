module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_fusion_N [Finite G] {t h c : G} {A B V E : Subgroup G} (ht2 : t * t = 1)
    (hB : Nat.card ↥B = 16) (hV : CFSG.Open.IsElemAbelian 2 V) (hcV : Nat.card ↥V = 2 ^ 8)
    (htA : t ∈ A) (hA1 : conjClassIn ⊤ t ∩ (A : Set G) = cosetSet t B)
    (hE : IsSylow2Of E (normalizer (A : Set G) ⊓ centralizer (B : Set G)))
    (hEV : V ⊔ zpowers t = E) (hEN : E ≤ normalizer (V : Set G))
    (hVC : V ⊓ centralizer ({t} : Set G) = B)
    (hsN : h⁻¹ * t * h ∈ normalizer (V : Set G))
    (hDeq : V ⊓ centralizer ({h⁻¹ * t * h} : Set G) =
      CFSG.conjugate (CFSG.conjugate B h) c)
    (hFA : V ⊓ centralizer ({h⁻¹ * t * h} : Set G) ⊔ zpowers (h⁻¹ * t * h) =
      CFSG.conjugate A (h * c))
    (hconj : (h * c)⁻¹ * t * (h * c) = h⁻¹ * t * h) :
    ∃ n ∈ normalizer (V : Set G), n⁻¹ * t * n = h⁻¹ * t * h := by
  generalize hs : h⁻¹ * t * h = s at *
  generalize hD : V ⊓ centralizer ({s} : Set G) = D at *
  have hs2 : s * s = 1 := by
    rw [← hs]
    calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [ht2]; group
  have hDV : D ≤ V := by
    rw [← hD]
    exact inf_le_left
  have hDB : D = CFSG.conjugate B (h * c) := by
    rw [hDeq, sec126_conjugate_conjugate]
  have hVN : V ≤ normalizer (CFSG.conjugate A (h * c) : Set G) := by
    have h0 := sec126_V_normalizes hV hs2 hsN
    rw [hD, hFA] at h0
    exact h0
  have hVC' : V ≤ centralizer (CFSG.conjugate B (h * c) : Set G) := by
    rw [← hDB]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hV.comm (hDV hd) hv
  obtain ⟨p, hpP, hp⟩ := sec126_exists_h2 hV hE hVN hVC'
  obtain ⟨h2, hh2⟩ : ∃ h2 : G, h2 = p * (h * c) := ⟨_, rfl⟩
  have hVE2 : V ≤ CFSG.conjugate E h2 := fun v hv => by
    rw [mem_conjugate_iff, hh2]
    exact hp v hv
  have hEc : CFSG.conjugate E h2 =
      CFSG.conjugate V h2 ⊔ zpowers (h2⁻¹ * t * h2) := by
    rw [← hEV, sec126_conjugate_sup, sec126_conjugate_zpowers]
  have htE : t ∈ E := by
    rw [← hEV]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hs'N : h2⁻¹ * t * h2 ∈ normalizer (CFSG.conjugate V h2 : Set G) := by
    rw [sec126_mem_normalizer_conjugate_iff]
    have : h2 * (h2⁻¹ * t * h2) * h2⁻¹ = t := by group
    rw [this]
    exact hEN htE
  have hs'2 : (h2⁻¹ * t * h2) * (h2⁻¹ * t * h2) = 1 := by
    calc (h2⁻¹ * t * h2) * (h2⁻¹ * t * h2) = h2⁻¹ * (t * t) * h2 := by group
      _ = 1 := by rw [ht2]; group
  have hCle : Nat.card ↥(CFSG.conjugate V h2 ⊓ centralizer ({h2⁻¹ * t * h2} : Set G)) ≤ 16 := by
    have hle : CFSG.conjugate V h2 ⊓ centralizer ({h2⁻¹ * t * h2} : Set G) ≤
        CFSG.conjugate B h2 := by
      intro x hx
      obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
      rw [mem_conjugate_iff] at hxV ⊢
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC
      rw [← hVC]
      refine Subgroup.mem_inf.mpr ⟨hxV, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : h2 * (x * (h2⁻¹ * t * h2)) * h2⁻¹ = h2 * ((h2⁻¹ * t * h2) * x) * h2⁻¹ := by
        rw [hxC]
      calc h2 * x * h2⁻¹ * t = h2 * (x * (h2⁻¹ * t * h2)) * h2⁻¹ := by group
        _ = h2 * ((h2⁻¹ * t * h2) * x) * h2⁻¹ := h3
        _ = t * (h2 * x * h2⁻¹) := by group
    calc _ ≤ Nat.card ↥(CFSG.conjugate B h2) := Subgroup.card_le_of_le hle
      _ = 16 := by rw [sec126_card_conjugate, hB]
  have hVeq : V = CFSG.conjugate V h2 :=
    sec126_eq_of_le_sup hV (sec4_isElemAbelian_conjugate hV h2) hcV
      (by rw [sec126_card_conjugate, hcV]) hs'N hs'2 (by rw [← hEc]; exact hVE2) hCle
  have hh2N : h2 ∈ normalizer (V : Set G) := sec126_mem_normalizer_of_conjugate_eq hVeq.symm
  have hpA : p ∈ normalizer (A : Set G) := (Subgroup.mem_inf.mp hpP).1
  have htp : p⁻¹ * t * p ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hpA) t).mp htA
    simpa using this
  have htpG : p⁻¹ * t * p ∈ conjClassIn ⊤ t := ⟨p⁻¹, Subgroup.mem_top _, by rw [inv_inv]⟩
  have htpB : p⁻¹ * t * p ∈ cosetSet t B := by
    rw [← hA1]
    exact ⟨htpG, htp⟩
  obtain ⟨b, hb, hbp⟩ := htpB
  have hdD : (h * c)⁻¹ * b * (h * c) ∈ D := by
    rw [hDB, mem_conjugate_iff]
    have : (h * c) * ((h * c)⁻¹ * b * (h * c)) * (h * c)⁻¹ = b := by group
    rw [this]
    exact hb
  have hs's : h2⁻¹ * t * h2 = s * ((h * c)⁻¹ * b * (h * c)) := by
    calc h2⁻¹ * t * h2 = (h * c)⁻¹ * (p⁻¹ * t * p) * (h * c) := by rw [hh2]; group
      _ = (h * c)⁻¹ * (t * b) * (h * c) := by rw [hbp]
      _ = ((h * c)⁻¹ * t * (h * c)) * ((h * c)⁻¹ * b * (h * c)) := by group
      _ = s * ((h * c)⁻¹ * b * (h * c)) := by rw [hconj]
  have hDc : Nat.card ↥(V ⊓ centralizer ({s} : Set G)) = 16 := by
    rw [hD, hDB, sec126_card_conjugate, hB]
  have hdD' : (h * c)⁻¹ * b * (h * c) ∈ V ⊓ centralizer ({s} : Set G) := by
    rw [hD]
    exact hdD
  obtain ⟨v, hv, hvs⟩ := sec126_exists_conj hV hs2 hsN (by rw [hDc, hcV]; norm_num) hdD'
  refine ⟨h2 * v⁻¹, (normalizer (V : Set G)).mul_mem hh2N
    ((normalizer (V : Set G)).inv_mem (Subgroup.le_normalizer hv)), ?_⟩
  calc (h2 * v⁻¹)⁻¹ * t * (h2 * v⁻¹) = v * (h2⁻¹ * t * h2) * v⁻¹ := by group
    _ = v * (s * ((h * c)⁻¹ * b * (h * c))) * v⁻¹ := by rw [hs's]
    _ = v * (v⁻¹ * s * v) * v⁻¹ := by rw [hvs]
    _ = s := by group

end CFSG.OddStandard.SmallF3.Omega

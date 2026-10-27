module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndL

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {c x : G} (hc : x * c = c * x) :
    x ∈ normalizer (zpowers c : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have hxc : x * c * x⁻¹ = c := by rw [hc]; group
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← conj_zpow, hxc]
    exact zpow_mem_zpowers c k
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
    have h1 : y = c ^ k := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * c ^ k * x := by rw [hk]
        _ = (x⁻¹ * c * x) ^ k := by rw [conj_inv_zpow]
        _ = c ^ k := by rw [show x⁻¹ * c * x = c by rw [mul_assoc, ← hc]; group]
    rw [h1]
    exact zpow_mem_zpowers c k

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem normalizer_W_facts (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {W : Subgroup G}
    (hWN : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ normalizer (W : Set G)) :
    L ≤ normalizer (W : Set G) ∧ s ∈ normalizer (W : Set G) ∧
      conjugate L s ≤ normalizer (W : Set G) ∧
      centralizer ({z} : Set G) ≤ normalizer (W : Set G) ∧
      centralizer ({t} : Set G) ≤ normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzRs := H.z_mem_Rs
  have hz1 : zpowers z ≠ ⊥ := fun h => H.z_ne_one (by
    have h1 := mem_zpowers z
    rw [h] at h1
    exact mem_bot.mp h1)
  have hzle : zpowers z ≤ conjugate (S ⊓ L) s := zpowers_le_of_mem hzRs
  have hR1 : S ⊓ L ≠ ⊥ := fun h => H.t_ne_one (by
    have h1 := H.sec5.tR
    rw [h] at h1
    exact mem_bot.mp h1)
  have hL : L ≤ normalizer (W : Set G) := by
    refine H.le_of_forall_inf_centralizer_le hK hcalc fun r hr hr2 x hx => ?_
    obtain ⟨hxL, hxr⟩ := mem_inf.mp hx
    have hr1 : zpowers r ≠ ⊥ := fun h => by
      have h1 := mem_zpowers r
      rw [h] at h1
      rw [mem_bot.mp h1, orderOf_one] at hr2
      omega
    refine hWN _ _ (zpowers_le_of_mem hr) hzle hr1 hz1 ?_
    exact mem_normalizer_sup
      (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hxr))
      (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp (H.sec5.zL.2.1 hxL)))
  have hRs1 : conjugate (S ⊓ L) s ≠ ⊥ := fun h => H.z_ne_one (by
    rw [h] at hzRs
    exact mem_bot.mp hzRs)
  have hs : s ∈ normalizer (W : Set G) := by
    refine hWN _ _ le_rfl le_rfl hR1 hRs1 (mem_normalizer_of_map_conj_le ?_)
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_sup_right (H.conj_s_mem_Rs hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_sup_left (mem_conjugate_iff.mp hx)
  have hLs : conjugate L s ≤ normalizer (W : Set G) := by
    intro x hx
    rw [show x = s⁻¹ * (s * x * s⁻¹) * s by group]
    exact mul_mem (mul_mem (inv_mem hs) (hL (mem_conjugate_iff.mp hx))) hs
  have hCz : centralizer ({z} : Set G) ≤ normalizer (W : Set G) := by
    intro x hx
    have hxN := H.sec5.centralizer_le_normalizer hx
    have hconjL : conjugate L x⁻¹ = L := by
      ext y
      rw [mem_conjugate_iff]
      exact ((mem_normalizer_iff.mp (inv_mem hxN)) y).symm
    have hR' : IsSylowOf 2 (conjugate (S ⊓ L) x⁻¹) L := by
      have h := isSylowOf_conjugate H.sec5.R_sylow x⁻¹
      rwa [hconjL] at h
    obtain ⟨k, hkL, hk⟩ := Foote5.exists_conj_eq_of_isSylowOf H.sec5.R_sylow hR'
    rw [conjugate_conjugate] at hk
    have hgN : x⁻¹ * k ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro r
      rw [← mem_conjugate_iff, hk]
    have hgz : (x⁻¹ * k) * z = z * (x⁻¹ * k) := by
      have h1 := mem_centralizer_singleton_iff.mp hx
      have h2 := mem_centralizer_singleton_iff.mp (H.sec5.zL.2.1 hkL)
      calc x⁻¹ * k * z = x⁻¹ * (z * k) := by rw [mul_assoc, h2]
        _ = z * (x⁻¹ * k) := by
          rw [← mul_assoc, show x⁻¹ * z = z * x⁻¹ by
            calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * z) * x⁻¹ := by rw [h1]
              _ = z * x⁻¹ := by group, mul_assoc]
    have hgW : x⁻¹ * k ∈ normalizer (W : Set G) :=
      hWN _ _ le_rfl hzle hR1 hz1 (mem_normalizer_sup hgN (mem_normalizer_zpowers_of_commute hgz))
    rw [show x = k * (x⁻¹ * k)⁻¹ by group]
    exact mul_mem (hL hkL) (inv_mem hgW)
  have hCt : centralizer ({t} : Set G) ≤ normalizer (W : Set G) := by
    intro x hx
    have h1 : s * x * s⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← H.conj_s_t]
      calc s * x * s⁻¹ * (s * t * s⁻¹) = s * (x * t) * s⁻¹ := by group
        _ = s * (t * x) * s⁻¹ := by rw [hx]
        _ = s * t * s⁻¹ * (s * x * s⁻¹) := by group
    rw [show x = s⁻¹ * (s * x * s⁻¹) * s by group]
    exact mul_mem (mul_mem (inv_mem hs) (hCz h1)) hs
  exact ⟨hL, hs, hLs, hCz, hCt⟩

theorem normalizer_W_ne_top {W : Subgroup G} (hW1 : W ≠ ⊥) (hWodd : Odd (Nat.card W)) :
    normalizer (W : Set G) ≠ ⊤ := by
  have hsimple : IsSimpleGroup G := H.sec5.sec4.simple
  intro h
  have hn : W.Normal := normalizer_eq_top_iff.mp h
  rcases hn.eq_bot_or_eq_top with h1 | h1
  · exact hW1 h1
  · rw [h1] at hWodd
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_of_involution (mem_top t) H.mul_self_t H.t_ne_one)

end Hyp

end CFSG.ComponentClassification.Sol78.F514

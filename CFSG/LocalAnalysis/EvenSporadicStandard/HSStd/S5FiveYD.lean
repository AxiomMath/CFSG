module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYDZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSection
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import Certificates.Certificate27263
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup Equiv

theorem card_centralizer_eq_cardCent (x : A5S5) : Nat.card ↥(centralizer ({x} : Set A5S5)) =
    cardCent x := by
  classical
  rw [cardCent, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by
    rw [mem_centralizer_singleton_iff])

theorem false_of_dConfig (hH2 : Harada39Two) {D : Type} [Group D]
    [Finite D] (hD : CFSG.SectionRank.IsKGroupCat D) (c : DConfig D) : False := by
  have hharada := hH2 (DBar D) (hD.quotient _) c.zstar_bar c.tb c.vb c.orderOf_tb c.vb_sq
    c.fhom.range
    ⟨(MonoidHom.ofInjective c.fhom_injective).symm⟩ c.V_inf_J c.V_comm_J c.cent_tb c.cent_vb
    c.cent_tvb
  rcases hharada with hnorm | ⟨⟨φ⟩⟩
  ·
    obtain ⟨g, hg⟩ := c.fus_u
    have h1 : (QuotientGroup.mk g : DBar D) * c.tb * (QuotientGroup.mk g)⁻¹ =
        c.tb * c.fhom c.σ₀ := by
      have := congrArg (QuotientGroup.mk : D → DBar D) hg
      simpa [DConfig.tb, DConfig.fhom_apply] using this
    have hmem : c.tb * c.fhom c.σ₀ ∈ zpowers c.tb ⊔ zpowers c.vb := by
      rw [← h1]
      exact hnorm.conj_mem _ (mem_sup_left (mem_zpowers _)) _
    have hu : c.fhom c.σ₀ ∈ zpowers c.tb ⊔ zpowers c.vb := by
      have h2 := (zpowers c.tb ⊔ zpowers c.vb).mul_mem
        ((zpowers c.tb ⊔ zpowers c.vb).inv_mem (mem_sup_left (mem_zpowers c.tb))) hmem
      rwa [inv_mul_cancel_left] at h2
    have hbot : c.fhom c.σ₀ ∈ (zpowers c.tb ⊔ zpowers c.vb) ⊓ c.fhom.range :=
      ⟨hu, ⟨c.σ₀, rfl⟩⟩
    rw [c.V_inf_J, mem_bot] at hbot
    exact c.σ₀_ne (c.fhom_injective (hbot.trans (map_one c.fhom).symm))
  ·
    have hstmt : a5s5Stmt := Certificates.certificate27263
    set t' : A5S5 := φ c.tb with ht'
    set u' : A5S5 := φ (c.fhom c.σ₀) with hu'
    have ht'2 : t' * t' = 1 := by rw [ht', ← map_mul, c.tb_sq, map_one]
    have ht'1 : t' ≠ 1 := fun h => c.tb_ne_one ((map_eq_one_iff φ φ.injective).1 h)
    have hcard : cardCent t' = 480 := by
      rw [← card_centralizer_eq_cardCent,
        ← Nat.card_congr (centralizerSingletonEquiv φ c.tb).toEquiv, c.card_cent_tb]
    have hz : ∃ z : A5S5, z ≠ 1 ∧ z ≠ t' ∧ z * t' = t' * z ∧
        ∀ g : A5S5, g * t' = t' * g → z * g = g * z := by
      refine ⟨φ c.vb, ?_, ?_, ?_, ?_⟩
      · exact fun h => c.vb_ne_one ((map_eq_one_iff φ φ.injective).1 h)
      · exact fun h => c.tb_ne_vb (φ.injective h).symm
      · rw [ht', ← map_mul, ← map_mul, c.tvb_comm]
      · intro g hg
        set g₀ := φ.symm g with hg₀
        have hg1 : g₀ * c.tb = c.tb * g₀ := by
          apply φ.injective
          rw [map_mul, map_mul, hg₀, MulEquiv.apply_symm_apply]
          exact hg
        have hg2 : g₀ ∈ centralizer ({c.vb} : Set (DBar D)) := by
          rw [c.cent_vb]
          exact mem_centralizer_singleton_iff.2 hg1
        have hg3 := mem_centralizer_singleton_iff.1 hg2
        have : φ (g₀ * c.vb) = φ (c.vb * g₀) := congrArg φ hg3
        rw [map_mul, map_mul, hg₀, MulEquiv.apply_symm_apply] at this
        exact this.symm
    have hu'2 : u' * u' = 1 := by rw [hu', ← map_mul, ← map_mul, c.σ₀_sq, map_one, map_one]
    have hu'c : u' * t' = t' * u' := by
      rw [hu', ht', ← map_mul, ← map_mul, c.fhom_comm_tb]
    have hτ : ∃ τ : Perm (Fin 5), τ * c.σ₀ ≠ c.σ₀ * τ := by
      by_contra h
      exact c.σ₀_ne (CFSG.perm_eq_one_of_forall_commute (by simp) fun τ =>
        by_contra fun hne => h ⟨τ, Ne.symm hne⟩)
    obtain ⟨τ, hτ⟩ := hτ
    have hw : ∃ w : A5S5, w * t' = t' * w ∧ u' * w ≠ w * u' := by
      refine ⟨φ (c.fhom τ), ?_, ?_⟩
      · rw [ht', ← map_mul, ← map_mul, c.fhom_comm_tb]
      · intro h
        have h0 : φ (c.fhom c.σ₀ * c.fhom τ) = φ (c.fhom τ * c.fhom c.σ₀) := by
          rw [map_mul, map_mul]
          exact h
        have h1 := φ.injective h0
        rw [← map_mul, ← map_mul] at h1
        exact hτ (c.fhom_injective h1).symm
    obtain ⟨g, hg⟩ := c.fus_u
    have hconj : ∃ c' : Equiv.Perm (Fin 5), c' * (t' * u').2 * c'⁻¹ = t'.2 := by
      refine ⟨((φ (QuotientGroup.mk g))⁻¹).2, ?_⟩
      have h1 : (QuotientGroup.mk g : DBar D) * c.tb * (QuotientGroup.mk g)⁻¹ =
          c.tb * c.fhom c.σ₀ := by
        have := congrArg (QuotientGroup.mk : D → DBar D) hg
        simpa [DConfig.tb, DConfig.fhom_apply] using this
      have h2 : φ (QuotientGroup.mk g) * t' * (φ (QuotientGroup.mk g))⁻¹ = t' * u' := by
        rw [ht', hu', ← map_inv, ← map_mul, ← map_mul, h1, map_mul]
      have h3 : (φ (QuotientGroup.mk g))⁻¹ * (t' * u') * ((φ (QuotientGroup.mk g))⁻¹)⁻¹ = t' := by
        rw [inv_inv, ← h2]
        group
      simpa using congrArg Prod.snd h3
    exact hstmt t' ht'2 ht'1 hcard hz u' hu'2 hu'c hw hconj

end CFSG.EvenSporadicStandard.HSStd.FiveY

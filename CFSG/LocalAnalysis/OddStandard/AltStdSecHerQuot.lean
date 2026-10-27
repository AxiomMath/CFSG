module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerCop
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Quot

variable {H : Type} [Group H] [Finite H]

theorem exactShape_quotient_oddCore {t : H} {B : Subgroup H} {m : ℕ} (ht : orderOf t = 2)
    (hm : 5 ≤ m) (e : B ≃* alternatingGroup (Fin m)) (hBt : B ≤ centralizer ({t} : Set H))
    (hnorm : centralizer ({t} : Set H) ≤ normalizer (B : Set H))
    (hcc : centralizer (B : Set H) ⊓ centralizer ({t} : Set H) ≤ zpowers t ⊔ CFSG.oddCore H) :
    ExactShape (QuotientGroup.mk t : H ⧸ CFSG.oddCore H)
      (B.map (QuotientGroup.mk' (CFSG.oddCore H))) m := by
  classical
  set P := CFSG.oddCore H with hPdef
  have hPodd : ∀ x ∈ P, Odd (orderOf x) := fun x hx => orderOf_odd_of_mem_oddCore hx
  have ht1 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hBP : B ⊓ P = ⊥ := inf_oddCore_eq_bot_of_alt hm e
  have hinj : Function.Injective ((QuotientGroup.mk' P).domRestrict B) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have hb1 : (QuotientGroup.mk' P) (b : H) = 1 := hb
    have : (b : H) ∈ B ⊓ P := ⟨b.2, (QuotientGroup.eq_one_iff _).1 hb1⟩
    rw [hBP] at this
    exact Subtype.ext this
  have hconj : ∀ c ∈ normalizer (B : Set H), ∀ y : H ⧸ P,
      y ∈ B.map (QuotientGroup.mk' P) ↔
        (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ ∈ B.map (QuotientGroup.mk' P) := by
    intro c hc y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    constructor
    · rintro ⟨b, hb, hby⟩
      refine ⟨c * b * c⁻¹, (mem_normalizer_iff.1 hc b).1 hb, ?_⟩
      rw [← hby]
      simp
    · rintro ⟨b, hb, hby⟩
      refine ⟨c⁻¹ * b * c, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hc) b).1 hb
        simpa using this
      · have h1 : (b : H ⧸ P) = (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ := hby
        have : ((c⁻¹ * b * c : H) : H ⧸ P) = (c : H ⧸ P)⁻¹ * b * (c : H ⧸ P) := by simp
        simp only [QuotientGroup.mk'_apply, this, h1]
        group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    apply orderOf_eq_prime
    · have h2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      rw [← QuotientGroup.mk_pow, h2]
      rfl
    · intro h1
      exact ClassicalInvolution.QuaternionStructure.not_mem_oddCore_of_orderOf_eq_two ht
        ((QuotientGroup.eq_one_iff t).1 h1)
  · exact ⟨(ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective
      (QuotientGroup.mk' P) B hinj).symm.trans e⟩
  ·
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hBt hb)
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
  ·
    intro x hx
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage hPodd ht1 hx
    rw [mem_normalizer_iff]
    exact hconj c (hnorm hc)
  ·
    apply le_antisymm
    · rintro x ⟨hxB, hxt⟩
      obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage hPodd ht1 hxt
      have hcN : c ∈ normalizer (B : Set H) := hnorm hc
      have hcB : c ∈ centralizer (B : Set H) := by
        rw [mem_centralizer_iff]
        intro b hb
        have hcomm : (b : H ⧸ P) * (c : H ⧸ P) = (c : H ⧸ P) * (b : H ⧸ P) :=
          mem_centralizer_iff.1 hxB (b : H ⧸ P) ⟨b, hb, rfl⟩
        have h1 : c * b * c⁻¹ * b⁻¹ ∈ B :=
          mul_mem ((mem_normalizer_iff.1 hcN b).1 hb) (inv_mem hb)
        have h2 : c * b * c⁻¹ * b⁻¹ ∈ P := by
          rw [← QuotientGroup.eq_one_iff]
          have : ((c * b * c⁻¹ * b⁻¹ : H) : H ⧸ P) =
              (c : H ⧸ P) * b * (c : H ⧸ P)⁻¹ * (b : H ⧸ P)⁻¹ := by simp
          rw [this, ← hcomm]
          group
        have h3 : c * b * c⁻¹ * b⁻¹ ∈ B ⊓ P := ⟨h1, h2⟩
        rw [hBP] at h3
        have h4 : c * b * c⁻¹ * b⁻¹ = 1 := h3
        calc b * c = (c * b * c⁻¹ * b⁻¹)⁻¹ * (c * b) := by group
          _ = c * b := by rw [h4]; group
      have hmem : c ∈ zpowers t ⊔ P := hcc ⟨hcB, hc⟩
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' P) hmem
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq]
        at this
    · refine le_inf ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        rintro _ ⟨b, hb, rfl⟩
        have := mem_centralizer_singleton_iff.1 (hBt hb)
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
      · rw [zpowers_le, mem_centralizer_singleton_iff]

end Quot

end CFSG.OddStandard.AltStdSec

module

public import CFSG.GH74.Generic.BProg.B3.KG531BPairAux

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

namespace KG9

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open scoped MatrixGroups

variable {L : Type} [Group L]

theorem pPrimeCore_le_center_of_sl2 (hq : IsQuasisimple L) {F : Type} [Field F] [Fintype F]
    (hodd : Odd (Fintype.card F)) (e : L ⧸ pPrimeCore 2 L ≃* SL(2, F)) :
    pPrimeCore 2 L ≤ center L := by
  classical
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
    (CFSG.pPrimeCore_normal : (pPrimeCore 2 L).Normal) with htop | hle
  · exfalso
    have hall : ∀ g : SL(2, F), g = 1 := by
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx : x ∈ pPrimeCore 2 L := by
        rw [htop]
        exact Subgroup.mem_top x
      rw [(QuotientGroup.eq_one_iff x).2 hx, map_one]
    have hc := CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)
    have hc1 : Nat.card ↥(center SL(2, F)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩, ⟨1⟩⟩
    rw [Fintype.card_eq_nat_card] at hodd
    obtain ⟨k, hk⟩ := hodd
    rw [hc1, show Nat.card F - 1 = 2 * k by omega, Nat.gcd_mul_right_right] at hc
    exact absurd hc (by norm_num)
  · exact hle

theorem nonempty_centerQuot_alt6 (hq : IsQuasisimple L) {F : Type} [Field F] [Fintype F]
    (h9 : Fintype.card F = 9) (e : L ⧸ pPrimeCore 2 L ≃* SL(2, F)) :
    Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) := by
  classical
  have hOZ := pPrimeCore_le_center_of_sl2 hq (by rw [h9]; exact ⟨4, rfl⟩) e
  set φ : L →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 L)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker ≤ center L := by
    intro y hy
    apply hOZ
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (QuotientGroup.mk y) = 1 := hy
    rwa [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff] at h1
  have hk := ker_comp_eq_center hq φ hφs hφk
  have hs : Function.Surjective ((QuotientGroup.mk' (center SL(2, F))).comp φ) :=
    (QuotientGroup.mk'_surjective _).comp hφs
  obtain ⟨eA⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism F h9
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hs)).trans eA⟩

variable [Finite L]

theorem pPrimeCore_eq_bot_of_map {B : Type} [Group B] (hOZ : pPrimeCore 2 L ≤ center L)
    (σ : L →* B) (hσ : Function.Surjective σ) (hZB : IsPGroup 2 ↥(center B))
    (hker : ∀ N : Subgroup L, N ≤ σ.ker → Odd (Nat.card N) → N = ⊥) :
    pPrimeCore 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hle : (pPrimeCore 2 L).map σ ≤ center B :=
    (Subgroup.map_mono hOZ).trans (Subgroup.map_center_le_center hσ)
  have h2 : IsPGroup 2 ↥((pPrimeCore 2 L).map σ) := hZB.to_le hle
  have hd : Nat.card ↥((pPrimeCore 2 L).map σ) ∣ Nat.card ↥(pPrimeCore 2 L) :=
    Subgroup.card_map_dvd _ σ
  have h1 : Nat.card ↥((pPrimeCore 2 L).map σ) = 1 := by
    rcases h2.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (even_iff_two_dvd.mpr (h.trans hd)) (Nat.not_even_iff_odd.mpr hodd)
  have hbot : (pPrimeCore 2 L).map σ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  exact hker _ ((Subgroup.map_eq_bot_iff _).mp hbot) hodd

end KG9

end KG531BP

end CFSG.GH74.Generic.BProg.B3

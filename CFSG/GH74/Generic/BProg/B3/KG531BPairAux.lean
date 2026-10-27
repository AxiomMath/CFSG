module

public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

open CFSG CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt Subgroup
open scoped MatrixGroups

variable {L : Type} [Group L]

theorem ker_comp_eq_center {F : Type} [Field F] (hq : IsQuasisimple L) (φ : L →* SL(2, F))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center L) :
    ((QuotientGroup.mk' (center SL(2, F))).comp φ).ker = center L := by
  have hZ := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq hφ hker
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    rw [hZ] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have h1 : z⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hzx, inv_mul_cancel]
    have : x = z * (z⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ hz (hker h1)
  · intro hx
    rw [hZ]
    exact ⟨x, hx, rfl⟩

variable [Finite L]

theorem card_center_dvd_two
    (hq : IsQuasisimple L) {F : Type} [Field F] [Fintype F]
    (hodd : Odd (Fintype.card F)) (h5 : 5 ≤ Fintype.card F) (h9 : Fintype.card F ≠ 9)
    (φ : L →* SL(2, F)) (hφ : Function.Surjective φ) (hker : φ.ker ≤ center L) :
    Nat.card ↥(center L) ∣ 2 := by
  classical
  set ψ : L →* PSL(2, F) := (QuotientGroup.mk' (center SL(2, F))).comp φ with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψk : ψ.ker = center L := ker_comp_eq_center hq φ hφ hker
  let e' : L ⧸ center L ≃* PSL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hdvd := B2.L2Cover.card_center_dvd_card_hopfMultiplier_qs hq e'
  obtain ⟨-, ⟨e⟩⟩ := SL2Closed.psl_two_hopfMultiplier (k := F) h5 h9
  have h1 := Nat.card_congr ((hopfMultiplierEquivGriess _).symm.trans e).toEquiv
  rw [h1, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
  have hg : Nat.gcd 2 (Fintype.card F - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  rwa [hg] at hdvd

theorem pPrimeCore_eq_bot_of_qs_sl2
    (hq : IsQuasisimple L) {F : Type} [Field F] [Fintype F]
    (hodd : Odd (Fintype.card F)) (h5 : 5 ≤ Fintype.card F) (h9 : Fintype.card F ≠ 9)
    (e : L ⧸ pPrimeCore 2 L ≃* SL(2, F)) : pPrimeCore 2 L = ⊥ := by
  classical
  set O := pPrimeCore 2 L with hO
  set φ : L →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' O) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker = O := by
    ext y
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hOZ : O ≤ center L := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (CFSG.pPrimeCore_normal : O.Normal) with htop | hle
    · exfalso
      have hall : ∀ g : SL(2, F), g = 1 := by
        intro g
        obtain ⟨y, rfl⟩ := hφs g
        have : y ∈ φ.ker := by rw [hφk, hO, htop]; exact Subgroup.mem_top y
        exact this
      have hc := CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)
      have hc1 : Nat.card ↥(center SL(2, F)) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩, ⟨1⟩⟩
      rw [Fintype.card_eq_nat_card] at hodd
      obtain ⟨k, hk⟩ := hodd
      rw [hc1, show Nat.card F - 1 = 2 * k by omega, Nat.gcd_mul_right_right] at hc
      exact absurd hc (by norm_num)
    · exact hle
  have h2 := card_center_dvd_two hq hodd h5 h9 φ hφs (hφk ▸ hOZ)
  have hOdvd : Nat.card ↥O ∣ 2 := (Subgroup.card_dvd_of_le hOZ).trans h2
  have hcop : Nat.Coprime 2 (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  have h1 : Nat.card ↥O = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hOdvd
  exact Subgroup.eq_bot_of_card_eq _ h1

end KG531BP

end CFSG.GH74.Generic.BProg.B3

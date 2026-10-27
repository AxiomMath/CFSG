module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem center_eq_bot_of_isSimpleGroup_nonabelian {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hnc : ∃ a b : Y, a * b ≠ b * a) : center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem mulAut_mul_conj_mul_inv {Y : Type} [Group Y] (g : MulAut Y) (y : Y) :
    g * MulAut.conj y * g⁻¹ = MulAut.conj (g y) := by
  ext z
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem autOddCoreTrivial_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree s) {Y : Type} [Group Y]
    [Finite Y] [IsSimpleGroup Y] (hna : ∃ a b : Y, a * b ≠ b * a)
    (θ : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier s) : AutOddCoreTrivial Y := by
  intro ν hν1 hνν P hP hPn hodd
  have hord : orderOf ν = 2 := orderOf_eq_prime (by rw [pow_two]; exact hνν) hν1
  have hbal := CFSG.ComponentClassification.Foote5.hbal_of_coreFree hna
    (CFSG.ComponentClassification.Foote5.coreFree_of_sporadicOddCoreFree hs θ) ν hord
  have hZ : center Y = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hna
  have hκ : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro a b hab
    have key : ∀ z : Y, b⁻¹ * a * z = z * (b⁻¹ * a) := by
      intro z
      have h1 := congrArg (fun f : MulAut Y => f z) hab
      simp only [MulAut.conj_apply] at h1
      calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
        _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h1]
        _ = z * (b⁻¹ * a) := by group
    have hc : b⁻¹ * a ∈ center Y := Subgroup.mem_center_iff.2 fun g => (key g).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  set D : Subgroup (MulAut Y) := centralizer ({ν} : Set (MulAut Y)) with hD
  set F : Subgroup Y := fixSubgroup ν with hF
  set F' : Subgroup (MulAut Y) := F.map (MulAut.conj : Y →* MulAut Y) with hF'
  have hFmem : ∀ y : Y, y ∈ F ↔ ν y = y := fun y => Iff.rfl
  have hF'D : F' ≤ D := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hD, mem_centralizer_singleton_iff]
    ext z
    have hνy : ν y = y := (hFmem y).1 hy
    simp [MulAut.conj_apply, MulAut.mul_apply, hνy]
  have hnormE : (F'.subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, hy, hyn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [Subgroup.mem_subgroupOf]
    have hgD : (g : MulAut Y) * ν = ν * (g : MulAut Y) := mem_centralizer_singleton_iff.1 g.2
    have hgy : (g : MulAut Y) y ∈ F := by
      rw [hFmem]
      have := congrArg (fun f : MulAut Y => f y) hgD
      simp only [MulAut.mul_apply] at this
      rw [← this, (hFmem y).1 hy]
    refine ⟨(g : MulAut Y) y, hgy, ?_⟩
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← hyn, ← mulAut_mul_conj_mul_inv]
  have hcoreE : pPrimeCore 2 ↥(F'.subgroupOf D) = ⊥ := by
    have : (F'.subgroupOf D).Normal := hnormE
    set R : Subgroup ↥D := (pPrimeCore 2 ↥(F'.subgroupOf D)).map (F'.subgroupOf D).subtype
    have hRcop : Nat.Coprime 2 (Nat.card R) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Subgroup.card_map_of_injective (F'.subgroupOf D).subtype_injective]
      exact pPrimeCore_coprime_card
    have hR := (pPrimeCore_eq_bot_iff.1 hbal) R inferInstance hRcop
    exact (Subgroup.map_eq_bot_iff_of_injective _ (F'.subgroupOf D).subtype_injective).1 hR
  let ψ : ↥F ≃* ↥(F'.subgroupOf D) :=
    (Subgroup.equivMapOfInjective F (MulAut.conj : Y →* MulAut Y) hκ).trans
      (Subgroup.subgroupOfEquivOfLe hF'D).symm
  have hcoreF : pPrimeCore 2 ↥F = ⊥ := by
    have h := pPrimeCore_map_iso 2 ψ
    rw [hcoreE] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h
  have hPcop : Nat.Coprime 2 (Nat.card (P.subgroupOf F)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hPbot := (pPrimeCore_eq_bot_iff.1 hcoreF) (P.subgroupOf F) hPn hPcop
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : (⟨x, hP hx⟩ : ↥F) ∈ P.subgroupOf F := hx
  rw [hPbot, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')

end CFSG.EvenSporadicStandard.Induction

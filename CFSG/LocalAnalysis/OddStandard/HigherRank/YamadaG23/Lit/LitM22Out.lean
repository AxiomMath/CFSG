module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitM22Abs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitM22Fix

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem gomiOuterM22_holds :
    GomiOuterM22 := by
  intro G _ _ M σ hMn hM22 hC hσ2 hσ1 h9
  haveI : M.Normal := hMn
  obtain ⟨e⟩ := hM22
  let e' : ↥M ≃* ↥NativeSporadic.M22 := e
  haveI : IsSimpleGroup ↥NativeSporadic.M22 := fam_m22_simplicity.2.2
  haveI hs : IsSimpleGroup ↥M := e'.isSimpleGroup
  have hcardM : Nat.card ↥M = Nat.card ↥NativeSporadic.M22 := Nat.card_congr e'.toEquiv
  have hcardA : Nat.card (MulAut ↥M) = Nat.card (MulAut ↥NativeSporadic.M22) :=
    Nat.card_congr (MulAut.congr e').toEquiv
  have hcard : Nat.card (MulAut ↥M) ≤ 2 * Nat.card ↥M := by
    rw [hcardA, hcardM]
    exact m22_mulAut_card
  obtain ⟨α, hα2, hα1, hP⟩ := lit_outer_reduce hs hC hcard σ hσ2 hσ1
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(litFixSub σ)) 3 (n := 2)
    (by simpa using h9)
  have hP9 : Nat.card (K.map (litFixSub σ).subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (litFixSub σ).subtype_injective, hK]
    norm_num
  obtain ⟨P', hP'9, hfix⟩ := hP _ hP9 (Subgroup.map_subtype_le K)
  have hα2' : MulAut.congr e' α * MulAut.congr e' α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hα1' : MulAut.congr e' α ≠ 1 := by
    intro h
    exact hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hle : P'.map e'.toMonoidHom ≤ fixSub (MulAut.congr e' α) := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_fixSub]
    show e' (α (e'.symm (e' x))) = e' x
    rw [MulEquiv.symm_apply_apply, hfix x hx]
  have hdvd : 9 ∣ Nat.card ↥(fixSub (MulAut.congr e' α)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective e'.injective, hP'9] at this
  exact lit_m22_fix_card _ hα2' hα1' hdvd

end CFSG.OddStandard.HigherRank.YamadaG23

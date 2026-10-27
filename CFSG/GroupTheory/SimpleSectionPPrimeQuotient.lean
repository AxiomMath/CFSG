module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open Subgroup

theorem card_dvd_of_isSimpleGroup_quotient_of_isPPrimeQuotient
    {H S : Type*} [Group H] [Finite H] [Group S] [Finite S] {L : Subgroup H} [L.Normal]
    {p : ℕ} (hL : ¬ p ∣ Nat.card (H ⧸ L)) {Y : Subgroup H} (f : ↥Y →* S)
    (hf : Function.Surjective f) (hS : IsSimpleGroup S) (hp : p ∣ Nat.card S) :
    Nat.card S ∣ Nat.card L := by
  classical
  let Y₀ : Subgroup ↥Y := L.subgroupOf Y
  haveI hY₀ : Y₀.Normal := inferInstance
  have hmapn : (Y₀.map f).Normal := hY₀.map f hf
  haveI := hmapn
  rcases hS.eq_bot_or_eq_top_of_normal (Y₀.map f) with hbot | htop
  ·
    have hY₀ker : Y₀ ≤ f.ker := by
      intro y hy
      have hy' : f y ∈ Y₀.map f := Subgroup.mem_map_of_mem f hy
      rw [hbot, Subgroup.mem_bot] at hy'
      exact hy'
    have hsurj : Function.Surjective (QuotientGroup.lift Y₀ f hY₀ker) := by
      intro s
      obtain ⟨y, rfl⟩ := hf s
      exact ⟨QuotientGroup.mk y, rfl⟩
    have hdvdS : Nat.card S ∣ Nat.card (↥Y ⧸ Y₀) :=
      Subgroup.card_dvd_of_surjective hsurj
    have hdvdY : Nat.card (↥Y ⧸ Y₀) ∣ Nat.card (H ⧸ L) := by
      let φ : ↥Y →* H ⧸ L := (QuotientGroup.mk' L).comp Y.subtype
      have hφker : φ.ker = Y₀ := by
        ext y
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact QuotientGroup.eq_one_iff (N := L) (x := (y : H))
      have he : (↥Y ⧸ Y₀) ≃* φ.range :=
        (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
          (QuotientGroup.quotientKerEquivRange φ)
      rw [Nat.card_congr he.toEquiv]
      exact (Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)).trans (by rw [Subgroup.card_top])
    exact absurd (hp.trans (hdvdS.trans hdvdY)) hL
  ·
    have hsurj : Function.Surjective (f.comp Y₀.subtype) := by
      intro s
      have hs : s ∈ Y₀.map f := by rw [htop]; exact Subgroup.mem_top s
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hs
      exact ⟨⟨y, hy⟩, rfl⟩
    have hdvdS : Nat.card S ∣ Nat.card Y₀ :=
      Subgroup.card_dvd_of_surjective hsurj
    have hY₀eq : Y₀ = (Y ⊓ L).subgroupOf Y := by
      ext y
      exact ⟨fun h => Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨y.2, h⟩),
        fun h => (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2⟩
    have hdvdY : Nat.card Y₀ ∣ Nat.card L := by
      rw [hY₀eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact hdvdS.trans hdvdY

end CFSG.GroupTheory

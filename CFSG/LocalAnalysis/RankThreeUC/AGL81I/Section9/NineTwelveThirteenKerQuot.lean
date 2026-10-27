module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHullThirteen
public import CFSG.Quasithin.Background.A1cSL2Facts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped MatrixGroups

variable {Y : Type} [Group Y]

theorem exists_hom_quotient_range_eq_map (F : Subgroup Y) [F.Normal] (X : Subgroup Y)
    (T : Subgroup ↥X) [T.Normal] (hTF : T.map X.subtype ≤ F) :
    ∃ ψ : ↥X ⧸ T →* Y ⧸ F, ψ.range = X.map (QuotientGroup.mk' F) := by
  let φ : ↥X →* Y ⧸ F := (QuotientGroup.mk' F).comp X.subtype
  have hT : T ≤ φ.ker := fun t ht =>
    MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (N := F) _).mpr (hTF ⟨t, ht, rfl⟩))
  refine ⟨QuotientGroup.lift T φ hT, le_antisymm ?_ ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T q
    exact ⟨x, x.2, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk' T ⟨x, hx⟩, rfl⟩

theorem map_le_oPPrimeHull_of_quotient [Finite Y] {d : ℕ} [Fact d.Prime] (F : Subgroup Y)
    [F.Normal] (X : Subgroup Y) (T : Subgroup ↥X) [T.Normal] (hTF : T.map X.subtype ≤ F)
    (hgen : oPPrimeHull d (⊤ : Subgroup (↥X ⧸ T)) = ⊤) :
    X.map (QuotientGroup.mk' F) ≤ oPPrimeHull d (X.map (QuotientGroup.mk' F)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_quotient_range_eq_map F X T hTF
  have h1 := oPPrimeHull_range_eq_of_top ψ hgen
  rw [hψ] at h1
  exact h1.symm.le

theorem map_le_map_of_le_sup (F : Subgroup Y) [F.Normal] {X L V : Subgroup Y} (hX : X ≤ L ⊔ V)
    (hL : L ≤ F) : X.map (QuotientGroup.mk' F) ≤ V.map (QuotientGroup.mk' F) := by
  have hL' : L.map (QuotientGroup.mk' F) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hL
  calc X.map (QuotientGroup.mk' F) ≤ (L ⊔ V).map (QuotientGroup.mk' F) := Subgroup.map_mono hX
    _ = V.map (QuotientGroup.mk' F) := by rw [Subgroup.map_sup, hL', bot_sup_eq]

theorem eq_bot_or_range_le_of_sl2_thirteen {Γ : Type} [Group Γ] (ψ : SL(2, ZMod 13) →* Γ)
    {X : Subgroup Γ} (hXn : X.Normal) (hXψ : X ≤ ψ.range) (hX : X ≤ oPPrimeHull 13 X) :
    X = ⊥ ∨ ψ.range ≤ X := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : (X.comap ψ).Normal := hXn.comap ψ
  rcases CFSG.Quasithin.A1c.normal_le_center_or_eq_top (p := 13) (by norm_num) (X.comap ψ) with
    hc | ht
  · left
    have hsq : ∀ x ∈ X, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨z, rfl⟩ := hXψ hx
      have hz : z ∈ Subgroup.center SL(2, ZMod 13) := hc hx
      rw [← map_pow, sq_eq_one_of_mem_center_sl2_thirteen hz, map_one]
    refine eq_bot_iff.mpr (hX.trans ((Subgroup.closure_le _).mpr ?_))
    rintro x ⟨hxX, k, hk⟩
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq x hxX)
    rw [hk] at h2
    have hk0 : k = 0 := by
      by_contra hk0
      have h13 : 13 ∣ 2 := (dvd_pow_self 13 hk0).trans h2
      norm_num at h13
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact Subgroup.mem_bot.mpr hk
  · right
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ X.comap ψ := by
      rw [ht]
      exact Subgroup.mem_top z
    exact hz

theorem map_le_oPPrimeHull_seven_of_sl2_thirteen [Finite Y] (F : Subgroup Y) [F.Normal]
    {X L V : Subgroup Y} (hXn : X.Normal) (hX13 : X ≤ oPPrimeHull 13 X) (hXLV : X ≤ L ⊔ V)
    (hLF : L ≤ F) (W : Subgroup ↥V) [W.Normal] (hWF : W.map V.subtype ≤ F)
    (e : ↥V ⧸ W ≃* SL(2, ZMod 13)) :
    X.map (QuotientGroup.mk' F) ≤ oPPrimeHull 7 (X.map (QuotientGroup.mk' F)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨ψ₀, hψ₀⟩ := exists_hom_quotient_range_eq_map F V W hWF
  have hψ : (ψ₀.comp e.symm.toMonoidHom).range = V.map (QuotientGroup.mk' F) := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective e.symm.toMonoidHom e.symm.surjective,
      ← MonoidHom.range_eq_map, hψ₀]
  have hXψ : X.map (QuotientGroup.mk' F) ≤ (ψ₀.comp e.symm.toMonoidHom).range := by
    rw [hψ]
    exact map_le_map_of_le_sup F hXLV hLF
  have hX13' : X.map (QuotientGroup.mk' F) ≤ oPPrimeHull 13 (X.map (QuotientGroup.mk' F)) :=
    (Subgroup.map_mono hX13).trans (S631.map_oPPrimeHull (p := 13) _ X).le
  rcases eq_bot_or_range_le_of_sl2_thirteen (ψ₀.comp e.symm.toMonoidHom)
      (hXn.map _ (QuotientGroup.mk'_surjective F)) hXψ hX13' with h | h
  · rw [h]
    exact bot_le
  · rw [le_antisymm hXψ h]
    exact (oPPrimeHull_range_eq_of_top _ oPPrimeHull_seven_sl2_thirteen).symm.le

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

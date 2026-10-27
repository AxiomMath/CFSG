module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGT0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STEnd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem aschOmega6Minus_of (h36 : Asc82Lemma36) (hZ : Asc82ZExists) (h83 : Asc82Lemma83)
    (hM : Asc82Tab6M) (h84 : Asc82Thm84) (hT0 : Asc82Sec9T0)
    (h9 : ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
      (B : Subgroup G) (t₀ : G), Sec9Ctx G t L S z g B t₀ → False) :
    AschOmega6Minus := by
  intro G _ _ t L hS hΩ
  obtain ⟨s, hs2, hsC, α, hα⟩ := h84 G t L hS hΩ
  obtain ⟨S, hSsyl, _⟩ :=
    sec68_exists_sylow_ge (G := G) (B := ⊥) (H := centralizer ({t} : Set G))
      IsPGroup.of_bot bot_le
  obtain ⟨z, hz⟩ := hZ G t L hS S hSsyl
  have hconj : IsConj t (t * z) := h83 G t L hS hΩ z hz.pocket.1 hz.pocket.mem
  obtain ⟨g, hg⟩ := isConj_iff_inv_mul.mp hconj
  have hLcent : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hS
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLcent hN hSsyl
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hΩ⟩
  obtain ⟨B, _B₂, _hBne, hBnorm, _hB₂norm, _huniq⟩ :=
    hM.sylow_E16 G L hLM (S ⊓ L) hP
  have hsetting : Sec8Setting G t L S z :=
    { toSec3SettingLB := hS, toAsc82Notation := hz, omega6m := hΩ }
  have hbase : Sec8Base G t L S z g B :=
    ⟨hsetting, hg, by rw [inf_comm]; exact hBnorm.1, hBnorm.2.1⟩
  obtain ⟨B', t₀, hctx9⟩ := hT0 G t L S z g B hbase ⟨s, hs2, hsC, α, hα⟩
  exact h9 G t L S z g B' t₀ hctx9

theorem aschOmega6Minus_of_tab6 (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h66 : Asc82Lemma66) (h68 : Asc82Lemma68) (h82 : Asc82Lemma82) (hZ : Asc82ZExists)
    (hM : Asc82Tab6M) (hN : Asc82NormA6) (hCos : Asc82Sec9Cos) (h84 : Asc82Thm84)
    (hT0 : Asc82Sec9T0) : AschOmega6Minus := by
  exact aschOmega6Minus_of h36 hZ h66 hM h84 hT0
    (asc82Sec9_false_of_tab6 hsh h36 h37 h66 h68 h82 (asc82Sec8B_of hM) hM hN hCos)

end CFSG.OddStandard.SmallF3.Omega

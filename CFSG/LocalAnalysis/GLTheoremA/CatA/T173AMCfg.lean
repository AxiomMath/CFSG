module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

structure MCfg (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω) :
    Prop where
  prime : p.Prime
  odd : p ≠ 2
  normal : S.Normal
  qs : CFSG.Open.IsQuasisimple ↥S
  elem : IsElemAbelian p B
  four : p ^ 4 ≤ Nat.card B
  mem : x ∈ B
  ne_one : x ≠ 1
  cent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x
  cyc : CycModSylow p S
  split : SplitInnerDiagMarking16 p B S
  std : GLAStdSubPre p B x S D K
  hc : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧
    closureIn K N ⊔ B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅closureIn K N, T⁆ : Subgroup Ω) ≠ ⊥

theorem mcfg_of_cfg173 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (h : Cfg173 p S B N D K x) : MCfg p S B N D K x :=
  ⟨h.prime, h.odd, h.normal, h.qs, h.elem, h.four, h.mem, h.ne_one, h.cent, h.cyc, h.split, h.std,
    h.hc⟩

theorem MCfg.K_le {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (h : MCfg p S B N D K x) : K ≤ S := by
  rw [h.std.2.2.2.2.1]
  exact (Y10F.glaLayer_le _).trans inf_le_left

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

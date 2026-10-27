module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6E64Ker
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E29Ker
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf4Thin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Basic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfClosureE29
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2FixE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfClosureE64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem labelInj {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AEQ m)} (hm : 5 ≤ m)
    (I : AEIdentOn (fam K (conjSub g (piGen π))) m 𝒜 H) :
    ∀ L ∈ fam K (conjSub g (piGen π)), ∀ L' ∈ fam K (conjSub g (piGen π)),
      (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map I.φ =
        (L'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map I.φ → L = L' := by
  intro L hL L' hL' he
  obtain ⟨α, -, h4, b, hlab⟩ := I.label L hL
  exact TL4.eq_of_map_le_memBar S.hs.hyp S.hs.two hm I.φ (I.toLabel.isPGroup_ker S.hOdd)
    (S.fam_mem hL) (S.fam_mem hL') (le_pSpan hL) (le_pSpan hL') hlab he.le

theorem fam_conj_mem {L : Subgroup G} (hL : L ∈ fam K (conjSub g (piGen π)))
    {x : G} (hx : x ∈ pSpan (fam K (conjSub g (piGen π)))) :
    conjSub x L ∈ fam K (conjSub g (piGen π)) :=
  fam_inv L hL x (by rwa [S.fam_gen] at hx)

end Setting

theorem thinKerOdd64_proved {IH : Prop} :
    ThinKerOdd IH 7 AE.e64Sets AE.e64Sub := by
  intro _ G _ _ K₀ K K' z π g S _ _ I zS hzS k hk
  obtain rfl : zS = ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ := Subtype.ext hzS
  exact AEIdentOn.ker_le_threeClosure_e64 I S.hOdd
    (fun L hL => S.card8 L (S.fam_mem hL)) (fun L hL x hx => S.fam_conj_mem hL hx)
    (S.labelInj (by norm_num) I) S.mem_fam_self S.hz k hk

theorem thinKerOdd29_proved {IH : Prop} :
    ThinKerOdd IH 8 AE.e29Sets AE.e29Sub := by
  intro _ G _ _ K₀ K K' z π g S _ _ I zS hzS k hk
  obtain rfl : zS = ⟨z, le_pSpan S.mem_fam_self S.hz.mem⟩ := Subtype.ext hzS
  exact AEIdentOn.ker_le_threeClosure_e29 I S.hOdd
    (fun L hL => S.card8 L (S.fam_mem hL)) (fun L hL x hx => S.fam_conj_mem hL hx)
    (S.labelInj (by norm_num) I) S.mem_fam_self S.hz k hk

theorem thinE64_proved {IH : Prop} : ThinE64 IH :=
  thinE64_of_targets TwinThinPf.fixTrivial_e64_proved TwinThinPf.oddClosure_e64
    thinKerOdd64_proved

theorem thinE29_proved {IH : Prop} : ThinE29 IH :=
  thinE29_of_pair_ker TwinThinPf.oddClosure_e29 thinKerOdd29_proved

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

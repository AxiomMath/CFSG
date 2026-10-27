module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8E
public import CFSG.ClassicalInvolution.Q3.Sec13PerpW
public import CFSG.ClassicalInvolution.Q3.TL4WylA
public import CFSG.ClassicalInvolution.Q3.Sec13RecogLabel

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem muIsoWylD4_all {W : Subgroup G} (hW : W ∈ WSet Ω) (hWyl : MuIsoWylD4 Ω W) :
    ∀ W' ∈ WSet Ω, MuIsoWylD4 Ω W' := by
  intro W' hW'
  obtain ⟨g, rfl⟩ := wSet_conj h hW hW'
  exact TL4.muIsoWylD4_conjSub h.thmD.hyp hWyl g

section FrameCert


theorem aeIdent_eight (h9 : Perp9 Ω)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) (h13 : ∀ K ∈ Ω, zGroup Ω ≠ eGroup Ω K) :
    Nonempty (AEIdent Ω 8) := by
  obtain ⟨φ, hinj, hrange, K, hK, α, hα, b, hKφ⟩ :=
    AE8End.exists_hom_aeModel_eight (End18.Hyp.mk h h9 hμ h13)
  exact nonempty_aeIdent_of_hom h.thmD.hyp.conjInvariant h.thmD.trans h.thmD.gen
    (by norm_num) φ hinj hrange hK hα hKφ

theorem false_of_wyl_ne (h9 : Perp9 Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hWyl : MuIsoWylD4 Ω W) (h13 : ∀ K ∈ Ω, zGroup Ω ≠ eGroup Ω K) :
    False :=
  (h.no_aeIdent (by norm_num : 5 ≤ 8)).false
    (h.aeIdent_eight h9 (h.muIsoWylD4_all hW hWyl) h13).some

end FrameCert

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13

module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.ClassicalInvolution.Asc77.T8 (XMem ne_of_mem_omegaNbr)
open CFSG.Blueprint

section Gen

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {r : ℕ}

theorem card_eq_of_sylow (hr : 2 ≤ r) (h : TypeRFam r Φ) {L P : Subgroup Q} (hL : L ∈ Φ)
    (hP : IsSylow2In P L) : Nat.card ↥P = 2 ^ r := by
  obtain ⟨e⟩ := h.quat L hL P hP
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  ring

end Gen

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem exists_std8 (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ∃ W : Subgroup Y, TightStd8R r n R S t J P R₀ T₀ W u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨W, hW, hWP, hWn⟩ := Q3CP.exists_W_of_hypOmegaGen hs.large.datum.hypOmegaGen P
  exact ⟨W, ⟨hs.large, hs.hJ, hs.hu, ⟨mem_RSet_of_isSylow2In hK hs.hR₀, hs.hR₀.1, hs.hR₀P⟩,
    ⟨mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀, hs.hT₀.1, hs.hT₀P⟩, ⟨hW, hWP, hWn⟩⟩⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big.C264

module

public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.Thompson (le_normalizer_biSup_of_acts)
open CFSG.ClassicalInvolution.Asc77.T8 (normalizer_le_sigmaNorm)
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem TightLargeHypR.partIHypG (hL : TightLargeHypR r n Y Rd Sd z) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore Rd)) :=
  hL.datum.partIHypG

theorem TightLargeHypR.exists_nbr (hL : TightLargeHypR r n Y Rd Sd z) :
    ∃ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∃ t : Y, IsUniqueInvolution J t := by
  have hΩ := hL.datum.hypOmegaGen
  have hedge := hL.edge
  unfold TightEdgeless DEdgeless at hedge
  push Not at hedge
  obtain ⟨K₀, hK₀, J₀, hJ₀, hadj⟩ := hedge
  have hnbr : J₀ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) K₀ := by
    rcases hadj with h | h
    · exact h
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ₀ hK₀ h
  obtain ⟨g, hg⟩ := hK₀
  have h1 := omegaNbr_conj hΩ.conjInvariant hnbr g⁻¹
  rw [← hg, conjSub_inv_conjSub] at h1
  exact ⟨_, h1, Sec6Gen.exists_uniqueInvolution hΩ h1.1⟩

theorem TightLargeHypR.exists_std8 (hL : TightLargeHypR r n Y Rd Sd z) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) {t : Y}
    (ht : IsUniqueInvolution J t) :
    ∃ (S : Sylow 2 Y) (R T W : Subgroup Y), TightStd8R r n Rd Sd z J S R T W t := by
  have hΩ := hL.datum.hypOmegaGen
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set Y) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hSN : (S : Subgroup Y) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup Y) : Set Y) :=
    le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { large := hL
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hK hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

namespace TightStd8R

variable {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem hyp (hs : TightStd8R r n Rd Sd z J S R T W t) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) :=
  hs.large.datum.hypOmegaGen

theorem partIHypG (hs : TightStd8R r n Rd Sd z J S R T W t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore Rd)) :=
  TightLargeHypR.partIHypG hs.large

theorem mem (_hs : TightStd8R r n Rd Sd z J S R T W t) :
    tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
  CoreAssembly.mem_conjClass_self _

theorem hz (hs : TightStd8R r n Rd Sd z J S R T W t) : IsUniqueInvolution (tightCore Rd) z :=
  hs.large.datum.isUniqueInvolution_core

theorem noTwins (hs : TightStd8R r n Rd Sd z J S R T W t) :
    ∀ K' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), K' = tightCore Rd := by
  rw [hs.large.datum.twinSet_eq]
  exact fun K' hK' => hK'

theorem trans (_hs : TightStd8R r n Rd Sd z J S R T W t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore Rd), ∃ g : Y, conjSub g (tightCore Rd) = L :=
  fun _ hL => hL

theorem centralizer_le_sigmaNorm (hs : TightStd8R r n Rd Sd z J S R T W t) :
    Subgroup.centralizer ({z} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
  hs.large.datum.le_normalizer_core.trans (normalizer_le_sigmaNorm hs.hyp.conjInvariant hs.mem)

theorem toStd8Core (hs : TightStd8R r n Rd Sd z J S R T W t) :
    Q3CL.T8R.Loc.Std8Core (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) J S R T W z t :=
  ⟨hs.large.datum.ascStandCore, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT, hs.hW⟩

end TightStd8R

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

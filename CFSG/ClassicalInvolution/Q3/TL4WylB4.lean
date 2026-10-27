module

public import CFSG.ClassicalInvolution.Q3.TL4WylB3
import CFSG.ClassicalInvolution.Q3.Q3CLWylB
public import CFSG.ClassicalInvolution.Q3.TL4WylA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8 stdRepK)

namespace Wyl

open CFSG.ClassicalInvolution.Disconnected
open CFSG.StronglyEmbedded.UniqueCoset

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem fixesUniqueCoset_zt (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset (z * t) (T8.H274 Ω K z) :=
  Q3CL.Wyl.fixesUniqueCoset_zt hs hμ hne

end Wyl

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

open CFSG.StronglyEmbedded.UniqueCoset CFSG.GH74.Uniqueness in
theorem TightStd8R.h274_eq_top_of_wylD4 (hB : TightBenderEndR)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : Y ⧸ T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
      z • c = c := Wyl.fixesUniqueCoset_z hs.toStd8Core hμ hne
  have h2' : ∀ g : Y, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : Y ⧸ T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
        (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases isConj_or_mem_omegaNbr_gen hs.hyp hs.mem (hs.large.datum.aEmpty _ hs.mem)
      hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ (tightCore Rd)) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨g', S', R', T', hstd⟩ :=
        TightLargeHypR.exists_std8_of_wset hs.large hnbr hb hs.hW.1
      exact Wyl.fixesUniqueCoset_zt hstd.toStd8Core (muIsoWylD4_conjSub hs.hyp hμ g') hne
  obtain ⟨hFs, hFnab, hFc⟩ := TightLargeHypR.isSimpleGroup_genFittingFStar hs.large
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hTnab : ∃ x ∈ genFittingFStar Y, ∃ y ∈ genFittingFStar Y, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hFnab
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  obtain ⟨hLF, hLB, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz2 hFs hTnab hFc
    (L := Subgroup.closure (conjugatesOf z)) rfl
    (S_ZD_unconditional Y (conjugatesOf z) _ (isInvariantInvolutionSet hz2)
      (isProductDisconnected hH hz2 h1 h2'))
  exact hB Y Rd Sd z hs.large.datum (hLF ▸ hLB) hFc

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main
public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Mu

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem not_comm_of_muIsoWylD4_gen (h : MuIsoWylD4 Ω W) :
    ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x := fun hc =>
  s26_not_comm_of_muIso (Or.inr (Or.inr h)) fun x y => Subtype.ext (hc _ x.2 _ y.2)

theorem not_muIsoE4_of_muIsoWylD4 (h : MuIsoWylD4 Ω W) : ¬ MuIsoE4 Ω W := by
  rintro ⟨e⟩
  refine not_comm_of_muIsoWylD4_gen h fun x hx y hy => ?_
  have h1 : e ⟨x, hx⟩ * e ⟨y, hy⟩ = e ⟨y, hy⟩ * e ⟨x, hx⟩ := mul_comm _ _
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (e.injective h1)

theorem muIsoWylD4_conjSub [Finite G] (hΩ : HypOmegaGen Ω) (h : MuIsoWylD4 Ω W) (g : G) :
    MuIsoWylD4 Ω (conjSub g W) := by
  obtain ⟨e⟩ := h
  exact ⟨(muGroupConjEquivGen hΩ g W).symm.trans e⟩

end Mu

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.centralizer_le_sigmaNorm_of_not_comm (hT4 : Thm4RBelow r n)
    (hYs : TightC27_YsmallR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hE4 : ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hab : ¬ ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
      ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) :
    Subgroup.centralizer ({z * t} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hK := hs.xMem_K
  have hY : layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    by_cases hconn : T3.DStarConnected
        (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
    · obtain ⟨u, v, hu, hv, hu1, hv1, huv, hne, hux, hvx, hgu, hgv, hguv⟩ :=
        exists_good_pair_of_nonabelian_gen hs.toStd8Core hcomp hab
      exact layerY_le_sigmaNorm_of_conn h hK hcomp hconn
        (oddCoreOf_layerY_le_of_good_pair hΩ.conjInvariant hu hv huv hu1 hv1 hne hux hvx hgu
          hgv hguv)
    · exact hYs Y Rd Sd z J S R T W t hs hdisc hE4 hab hconn
  exact centralizer_le_sigmaNorm_of_layerY_le h hT4 hs.natCard_secQuot_lt hK hcomp hY


open CFSG.StronglyEmbedded.UniqueCoset CFSG.GH74.Uniqueness in
theorem TightStd8R.h274_eq_top_of_dComp_eq (hmin : TightC27_4MR r n) (hB : TightBenderEndR)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : Y ⧸ H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
      z • c = c := fixesUniqueCoset_z hs.toStd8Core hcomp
  have h2' : ∀ g : Y, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : Y ⧸ H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z,
        (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne hcomm
    rcases isConj_or_mem_omegaNbr_gen hs.hyp hs.mem (hs.large.datum.aEmpty _ hs.mem)
      hs.noTwins hz hne hcomm with hconj | hnbr
    · exact existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ (tightCore Rd)) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := TightLargeHypR.exists_std8 hs.large hnbr hb
      exact fixesUniqueCoset_zt_of_min hstd.toStd8Core hcomp
        (hmin Y Rd Sd z _ S' R' T' W' _ hstd hdisc)
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

theorem TightStd8R.false_of_wylD4_of_dComp_eq (hmin : TightC27_4MR r n) (hB : TightBenderEndR)
    (hT4 : Thm4RBelow r n) (hYs : TightC27_YsmallR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) : False := by
  have h4 := hs.h274_eq_top_of_dComp_eq hmin hB hdisc hcomp
  have hle : H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    refine sup_le le_rfl (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => ?_)
    obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
    have hμ' := muIsoWylD4_conjSub hs.hyp hμ g
    exact hstd.centralizer_le_sigmaNorm_of_not_comm hT4 hYs hdisc hcomp
      (not_muIsoE4_of_muIsoWylD4 hμ') (not_comm_of_muIsoWylD4_gen hμ')
  rw [h4] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans (top_le_iff.mp hle))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

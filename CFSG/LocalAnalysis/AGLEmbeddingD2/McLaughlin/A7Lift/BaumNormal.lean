module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Theta
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumStar
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModG
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Lift

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.A7Six Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

private theorem gnC_le_nL (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) :
    gnC T ≤ nL T L := by
  intro x hx
  rw [nL, Subgroup.mem_comap]
  have hx1 : QuotientGroup.mk' (gnC T) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [hx1]
  exact Subgroup.one_mem _

private theorem thompsonJ_le_nL (hX : GNSetting X T) (hL : IsComponentOf L ⊤) :
    thompsonJ T ≤ nL T L := by
  intro x hx
  rw [nL, Subgroup.mem_comap]
  exact thompsonJ_le_normalizer_of_isComponentOf hX hL ⟨x, hx, rfl⟩

private theorem mem_nL_iff_map_conj_eq (b : X) :
    b ∈ nL T L ↔
      L.map (MulAut.conj (QuotientGroup.mk' (gnC T) b)).toMonoidHom = L := by
  rw [nL, Subgroup.mem_comap]
  exact Subgroup.mem_normalizer_iff_map_conj_eq

private theorem exists_central_involution (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    (hne : nV T L ≠ ⊥) :
    ∃ e ∈ nV T L, e ≠ 1 ∧ ∀ b ∈ baum T, b * e = e * b := by
  have hJle : thompsonJ T ≤ nL T L := thompsonJ_le_nL hX hL
  have hJN : thompsonJ T ≤ Subgroup.normalizer (nV T L : Set X) :=
    hJle.trans (SixCtx.nL_le_normalizer_nV (T := T) (L := L) (normal_gnV T))
  let ρ : ↥(thompsonJ T) →* MulAut ↥(nV T L) :=
    (Subgroup.normalizerMonoidHom (nV T L)).comp (Subgroup.inclusion hJN)
  haveI : Nontrivial ↥(nV T L) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hP : IsPGroup 2 ↥(thompsonJ T) := hX.sylow.2.1.to_le (CFSG.Quasithin.B6.thompsonJ_le T)
  have hN : IsPGroup 2 ↥(nV T L) :=
    (CFSG.Open.IsElemAbelian.isPGroup
      (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX)).to_le
      (Subgroup.commutator_le_left _ _)
  obtain ⟨k, hk1, hkfix⟩ :=
    CFSG.Quasithin.F53.Stellmacher.S43.exists_fixed_ne_one hP hN ρ
  refine ⟨(k : X), k.2, fun h => hk1 (Subtype.ext h), ?_⟩
  intro b hb
  have hcommJ : ∀ j ∈ thompsonJ T, j * (k : X) = (k : X) * j := by
    intro j hj
    have h := congrArg (fun z : ↥(nV T L) => (z : X)) (hkfix ⟨j, hj⟩)
    have h' : j * (k : X) * j⁻¹ = (k : X) := by
      simpa [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    calc j * (k : X) = j * (k : X) * j⁻¹ * j := by group
      _ = (k : X) * j := by rw [h']
  have hkΩ : (k : X) ∈ omegaOneCenterOf (thompsonJ T) :=
    CFSG.AGLEmbeddingD2.Tits.E23.mem_omegaOneCenterOf_thompsonJ
      (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX)
      (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.gnV_le T hX)
      (Subgroup.commutator_le_left _ _ k.2) hcommJ
  exact (Subgroup.mem_centralizer_iff.mp hb.2 (k : X) hkΩ).symm

private theorem conj_preimage_centralizes (hL : IsComponentOf L ⊤) {b e : X}
    (hbn : b ∉ nL T L)
    (hcent : ∀ g : X, (∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l =
      l * QuotientGroup.mk' (gnC T) g) → ∀ u ∈ nV T L, g * u * g⁻¹ = u)
    (heN : e ∈ nV T L) :
    ∀ u ∈ lT T L, (b * u * b⁻¹) * e * (b * u * b⁻¹)⁻¹ = e := by
  have hL₁ : IsComponentOf
      (L.map (MulAut.conj (QuotientGroup.mk' (gnC T) b)).toMonoidHom) ⊤ :=
    CFSG.Quasithin.F918V5G.isComponentOf_map_conj hL (Subgroup.mem_top _)
  have hcomm : ∀ l ∈ L,
      ∀ y ∈ L.map (MulAut.conj (QuotientGroup.mk' (gnC T) b)).toMonoidHom, l * y = y * l := by
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute hL hL₁ with h | h
    · exact absurd ((mem_nL_iff_map_conj_eq (L := L) b).mpr h.symm) hbn
    · exact h
  intro u hu
  have hmem : QuotientGroup.mk' (gnC T) (b * u * b⁻¹) ∈
      L.map (MulAut.conj (QuotientGroup.mk' (gnC T) b)).toMonoidHom := by
    refine ⟨QuotientGroup.mk' (gnC T) u, (Subgroup.mem_comap.mp hu), ?_⟩
    simp [MulAut.conj_apply, map_mul]
  exact hcent (b * u * b⁻¹) (fun l hl => (hcomm l hl _ hmem).symm) e heN

theorem baum_le_nL (hX : GNSetting X T) (hL : IsComponentOf L ⊤) (hne : nV T L ≠ ⊥)
    (hC : nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥)
    (hcent : ∀ g : X, (∀ l ∈ L, QuotientGroup.mk' (gnC T) g * l =
      l * QuotientGroup.mk' (gnC T) g) → ∀ u ∈ nV T L, g * u * g⁻¹ = u) :
    baum T ≤ nL T L := by
  obtain ⟨e, heN, he1, hcentral⟩ := exists_central_involution hX hL hne
  intro b hb
  by_contra hbn
  have hbe' : b⁻¹ * e * b = e := by
    have h := hcentral b hb
    calc b⁻¹ * e * b = b⁻¹ * (e * b) := by group
      _ = b⁻¹ * (b * e) := by rw [← h]
      _ = e := by group
  have hconj := conj_preimage_centralizes hL hbn hcent heN
  have heC : e ∈ Subgroup.centralizer (lT T L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := hconj u hu
    have h2 : u * e * u⁻¹ = e := by
      have h' := congrArg (fun z => b⁻¹ * z * b) h
      calc u * e * u⁻¹ = u * (b⁻¹ * e * b) * u⁻¹ := by rw [hbe']
        _ = b⁻¹ * ((b * u * b⁻¹) * e * (b * u * b⁻¹)⁻¹) * b := by group
        _ = b⁻¹ * e * b := by rw [h']
        _ = e := hbe'
    calc u * e = u * e * u⁻¹ * u := by group
      _ = e * u := by rw [h2]
  have hebot : e ∈ (⊥ : Subgroup X) := by
    rw [← hC]
    exact Subgroup.mem_inf.mpr ⟨heN, heC⟩
  exact he1 (Subgroup.mem_bot.mp hebot)

theorem nT_facts (hX : GNSetting X T) (hbL : baum T ≤ nL T L) :
    T ⊓ nL T L ≤ T ∧ T ⊓ gnC T ≤ T ⊓ nL T L ∧
      pCoreOf 2 (⊤ : Subgroup X) ≤ T ⊓ nL T L ∧
      baum (T ⊓ nL T L) = baum T ∧
      omegaOneCenterOf T ≤ omegaOneCenterOf (T ⊓ nL T L) ∧
      IsPGroup 2 ↥(T ⊓ nL T L) := by
  refine ⟨inf_le_left, inf_le_inf_left T (gnC_le_nL T L), ?_, ?_, ?_, ?_⟩
  · exact le_inf (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow)
      ((pCoreOf_le_gnC hX).trans (gnC_le_nL T L))
  · exact (CFSG.Quasithin.baum_eq_of_le (S := T) (R := T ⊓ nL T L)
      (le_inf inf_le_left hbL) inf_le_left).symm
  · intro x hx
    have hxT : x ∈ T := CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self T hx
    have hxQ : x ∈ pCoreOf 2 (⊤ : Subgroup X) := omegaOneCenterOf_le_pCoreOf hX hx
    have hxC : x ∈ gnC T := pCoreOf_le_gnC hX hxQ
    have hxR : x ∈ T ⊓ nL T L := ⟨hxT, gnC_le_nL T L hxC⟩
    have hx2 : x ^ 2 = 1 := CFSG.Quasithin.sq_eq_one_of_mem_omegaOneCenterOf hx
    refine CFSG.Quasithin.mem_omegaOneCenterOf hxR (fun y hy => ?_) hx2
    exact CFSG.Quasithin.mem_centralizer_of_mem_omegaOneCenterOf hx hy.1
  · exact hX.sylow.2.1.to_le inf_le_left

end CFSG.AGLEmbeddingD2.McLaughlin.A7Lift


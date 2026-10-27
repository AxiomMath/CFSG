module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3Socle
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3Class

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

theorem exists_shape_three {H : Type} [Group H] {z : H} (hz : orderOf z = 2)
    (hInv : IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H)))
      .G2 3 1) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂)
      (S : Shape ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) F₁ F₂),
      Nat.card F₁ = 3 ∧ Nat.card F₂ = 3 ∧ (S.z : H) = z := by
  obtain ⟨M, _, z', hM, hz', ⟨e⟩⟩ := hInv
  obtain ⟨F, hF, hFin, S₀, hFc, -⟩ :=
    GHInv.exists_shape_G2 Nat.prime_three (by norm_num) hM z' hz'
  have hFc3 : Nat.card F = 3 := by simpa using hFc
  have hFodd : Odd (Nat.card F) := by rw [hFc3]; exact ⟨1, rfl⟩
  have htop := S₀.oPrimeResidual_eq_top_of_odd hFodd hFodd
  have hOC : oPrimeResidualOf 2 (centralizer ({z'} : Set M)) = centralizer ({z'} : Set M) := by
    unfold oPrimeResidualOf
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  let φ : ↥(centralizer ({z'} : Set M)) ≃*
      ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) :=
    (e.trans (MulEquiv.subgroupCongr hOC)).symm
  refine ⟨F, F, hF, hF, hFin, hFin, S₀.mapEquiv φ, hFc3, hFc3, ?_⟩
  exact shape_z_eq _ hz

theorem ivk_9_4_g4_small_G2three_proved
    (hfilter : GH74FilterStmt) : IVK_9_4_g4_small_G2three := by
  intro H _ _ Gs _ z hgen hrk hyp
  obtain ⟨hKgrp, hcore, ht, hp', hp'2, p, f, P, U, hp, hp2, hGs, hSS, hZ, hzU, hUP, hU4, hInv,
    hconj⟩ := hyp
  obtain ⟨hzord, u, huU, huord, huz, -, -⟩ := unpack_four_subgroup hZ hzU hUP hU4
  have hzu : IsConj z u := hconj z (hzU (Subgroup.mem_zpowers z)) u huU hzord huord
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hzS⟩ := exists_shape_three hzord hInv
  obtain ⟨hzK, hs, hnab, h3, h32, h128, hY⟩ :=
    exists_socle_data rfl hcore hrk hzord huord (Ne.symm huz) hzu P hZ (hUP huU) S hzS hc₁ hc₂
  have hcat : Catalog ↥(layer H) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKgrp (layer H)
      (MonoidHom.id ↥(layer H)) Function.surjective_id
  have hgen4 : Gen4 ↥(layer H) := Gen4.subgroup (layer H) hgen
  have hle3 : CFSG.pRank 2 ↥(layer H) ≤ 3 := by
    refine le_trans ?_ hrk
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(layer H),
      CFSG.SectionRank.pRank_eq_open_pRank_top 2 H]
    exact CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_two.one_lt (layer H).subtype
      (layer H).subtype_injective
  have htwo : Open.twoRank ↥(layer H) = 3 := by
    have h1 : Open.twoRank ↥(layer H) = CFSG.pRank 2 ↥(layer H) :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(layer H)).symm
    omega
  have hz' : orderOf (⟨z, hzK⟩ : ↥(layer H)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hzord
  exact classify_g2_three hnab hcat hgen4 htwo hfilter hz' h32 h128 hY

theorem ivk_9_4_g4_G2three_all
    (hfilter : GH74FilterStmt) : IVK_9_4_g4_G2three :=
  ivk_9_4_g4_G2three_proved hfilter (ivk_9_4_g4_small_G2three_proved hfilter)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94

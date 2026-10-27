module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.LocalData
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.ThreeFour
public import CFSG.GF2Type.Smith1980Orth.W4Rel
public import CFSG.LargeExtraspecial.S4CEMain
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.IndexEight
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LieType.Universal.Spin CFSG.RankThree.OrthogonalInvolutions

namespace S2Data

variable {G : Type} [Group G] [Finite G] {S : Setting G} {M1 : Subgroup S.O}

theorem ncard_singV_eq_nine (D : S2Data S M1) (hw : S.width = 4)
    (hplus : CFSG.GF2Type.Smith1979.PlusTypeAt S D.g D.good.ht) :
    D.singV.ncard = 9 := by
  have hdim : finrank (ZMod 2) (Vt S D.g D.t) = 4 := by rw [D.finrank_Vt, hw]
  obtain ⟨P, hP2, hP⟩ := hplus
  have hsing : ∀ v ∈ P, D.QV v = 0 := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · exact (D.QV_eq_zero_iff hv0).mpr (hP v hv hv0)
  have hp : CFSG.GroupTheory.WeirSylow.IsPlusType D.QV := ⟨P, by rw [hP2, hdim], hsing⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus D.QV_nondegenerate
    (n := 2) (by rw [hdim]) hp
  have hset : D.singV = (Vt S D.g D.t).subtype '' {v : Vt S D.g D.t | v ≠ 0 ∧ D.QV v = 0} := by
    ext w
    rw [D.mem_singV_iff]
    exact ⟨fun ⟨s, hs0, hsQ, hsw⟩ => ⟨s, ⟨hs0, hsQ⟩, hsw⟩,
      fun ⟨s, ⟨hs0, hsQ⟩, hsw⟩ => ⟨s, hs0, hsQ, hsw⟩⟩
  rw [hset, Set.ncard_image_of_injective _ (Submodule.injective_subtype _)]
  have hcard : {v : Vt S D.g D.t | D.QV v = 0}.ncard = 10 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {v : Vt S D.g D.t // D.QV v = 0} = 10
    have h := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) 1).1
    have h2 : Nat.card {v : Vt S D.g D.t // D.QV v = 0} =
        Nat.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // quadPlus 2 (ZMod 2) v = 0} :=
      CFSG.Timmesfeld.ClassicalOrders.card_singular_congr e
    rw [h2]
    have h10 : (Nat.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // quadPlus 2 (ZMod 2) v = 0} : ℤ) = 10 := by
      simpa using h
    omega
  have hsplit : {v : Vt S D.g D.t | v ≠ 0 ∧ D.QV v = 0}.ncard + 1 = 10 := by
    have h1 : {v : Vt S D.g D.t | v ≠ 0 ∧ D.QV v = 0} = {v | D.QV v = 0} \ {0} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨fun ⟨hv0, hvQ⟩ => ⟨hvQ, hv0⟩, fun ⟨hvQ, hv0⟩ => ⟨hv0, hvQ⟩⟩
    rw [h1, Set.ncard_diff_singleton_add_one (show (0 : Vt S D.g D.t) ∈ {v | D.QV v = 0}
      from map_zero D.QV), hcard]
  omega

theorem orbitMbar_eq_mulActionOrbit (D : S2Data S M1) :
    D.orbitMbar = (MulAction.orbit S.Mbar (S.cl (D.g * S.z * D.g⁻¹)) : Set S.Qt) := by
  ext v
  rw [S2Data.orbitMbar, MulAction.mem_orbit_iff]
  exact ⟨fun ⟨x, hx, hxv⟩ => ⟨⟨x, hx⟩, hxv.symm⟩, fun ⟨x, hxv⟩ => ⟨x, x.2, hxv.symm⟩⟩

theorem ncard_orbitMbar_eq_twentyseven (D : S2Data S M1) (hw : S.width = 4)
    (hplus : CFSG.GF2Type.Smith1979.PlusTypeAt S D.g D.good.ht) :
    Nat.card (MulAction.orbit S.Mbar (S.cl (D.g * S.z * D.g⁻¹))) = 27 := by
  rw [← D.orbitMbar_eq_mulActionOrbit, Nat.card_coe_set_eq, D.ncard_orbitMbar,
    D.ncard_singV_eq_nine hw hplus]

theorem three_le_finrank_commSpace_of_width_eq_four (D : S2Data S M1) (hw : S.width = 4) :
    ∀ y : G, IsConj S.z y → (hyM : y ∈ S.M) → y ∉ S.QG →
      3 ≤ finrank (ZMod 2)
        (commSpace ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  intro y hy hyM hyQ
  rcases D.oTypes_of_width_eq_four hw y hy hyM hyQ with h | h
  · rcases h with h | h | h
    · rw [h, D.commSpace_eq, D.finrank_Vt, hw]
      norm_num
    · rw [h, D.commSpace_kt_eq, D.finrank_Wkt, hw]
      norm_num
    · rw [h, D.commSpace_kkt_eq, D.finrank_Wk, hw]
      norm_num
  · obtain ⟨hs, hA⟩ := h
    have hdim := D.finrank_commSpace_Cbar ⟨S.ρ ⟨y, hyM⟩, hs⟩
    rw [hA.2.2.2.1] at hdim
    have h4 : 4 ≤ finrank (ZMod 2) (commSpace ((S.ρ ⟨y, hyM⟩ : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt)) := by simpa using hdim.ge
    omega

end S2Data

end CFSG.GF2Type.Smith1980Orth

namespace CFSG.GF2Type.Smith1979.TriConf

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G]

theorem plusTypeAt_congr {S : Setting G} {g : G} {t : S.O} {ht ht' : t ∈ S.Lbar g}
    (h : CFSG.GF2Type.Smith1979.PlusTypeAt S g ht) :
    CFSG.GF2Type.Smith1979.PlusTypeAt S g ht' := by
  obtain ⟨P, hP2, hP⟩ := h
  refine ⟨P, hP2, fun v hv hv0 => ?_⟩
  have h' := hP v hv hv0
  rwa [show aV ht = aV ht' from Subtype.ext rfl] at h'

theorem false_of_triLocal_of_plusTypeAt
    [IsSimpleGroup G] {S : Setting G} (hw : S.width = 4) (hnoAll : S11.NoA2All S)
    (hirr : ¬ S.IsReducible) {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4) {k : S.O}
    {M1 : Subgroup S.O} (T : TriLocal S g t k M1)
    (hplus : CFSG.GF2Type.Smith1979.PlusTypeAt S g ht)
    (hM : Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296) : False := by
  obtain ⟨D, hg, htD, hk⟩ := exists_s2Data_of_triLocal S4.centralExtInput hw H C ht ht1 hVQ
    hΩ h4 hirr hnoAll T
  obtain ⟨⟨g', t', k', good', four_le', finrank', kmem', kne', kcube', kconj', tinv', fpf',
    mulCbar', rel'⟩, hΩ'⟩ := D
  subst hg
  subst htD
  subst hk
  let D' : Smith1980Orth.S2Data S M1 :=
    ⟨⟨g', t', k', good', four_le', finrank', kmem', kne', kcube', kconj', tinv', fpf',
      mulCbar', rel'⟩, hΩ'⟩
  have hplusD : CFSG.GF2Type.Smith1979.PlusTypeAt S g' good'.ht := plusTypeAt_congr hplus
  have hdim := D'.three_le_finrank_commSpace_of_width_eq_four hw
  have h27 := D'.ncard_orbitMbar_eq_twentyseven hw hplusD
  obtain ⟨D₀⟩ := nonempty_s2Data_of_triLocal S4.centralExtInput hw H C ht ht1 hVQ hΩ h4 hirr
    hnoAll T
  obtain ⟨hloc, hpath⟩ := D₀.oLocal_oPath_of_width_eq_four hw
  exact false_of_oLocal_oPath hw H hirr hloc hpath hM
    (fun _ => index_mod_eight_eq_seven H hnoAll hw h27 hdim)

end CFSG.GF2Type.Smith1979.TriConf

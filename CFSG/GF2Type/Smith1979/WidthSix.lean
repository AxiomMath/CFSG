module

public import CFSG.GF2Type.Smith1979.Exits
public import CFSG.GF2Type.Smith1980Orthogonal
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fi24Inputs
public import CFSG.Quasithin.Vol2.Ch8InputsB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.Yardstones.M3aba7dc4b8a8
  CFSG.EvenSporadicStandard

@[expose] def WidthSixCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ S : Setting G, S.width = 6 →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) → ¬ S.IsReducible →
        (∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
          (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
            Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q))) ∨
        (TwoFi22.ParrottShape S.M ∧ ¬ IsCharTwoType G) ∨
        (Quasithin.H13.J4.IsTypeJ4Core S.M (Quasithin.H13.J4.selfC S.z) ∧
          Quasithin.H13.J4.IsAutTripleM22 (S.M ⧸ CFSG.pCore 2 S.M))

variable {G : Type} [Group G] [Finite G] {z : G}

theorem coreReducible_of_isReducible (S : Setting G) (hz : S.z = z) (hQ : S.QG = coreQ z)
    (h : S.IsReducible) : CoreReducible z := by
  obtain ⟨W, hW0, hWt, hWinv⟩ := h
  subst hz
  refine ⟨S.clPre W, ?_, ?_, ?_⟩
  · rw [← hQ]
    refine lt_of_le_of_ne (fun x hx => ?_) fun heq => ?_
    · rcases (DW.W4Rank.mem_center_map_QG_iff S).mp hx with rfl | rfl
      · exact one_mem _
      · exact S.z_mem_clPre W
    · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
      have hx : x ∈ S.clPre W := ⟨hxQ, hvW⟩
      rw [← heq] at hx
      rcases (DW.W4Rank.mem_center_map_QG_iff S).mp hx with rfl | rfl
      · exact hv0 S.cl_one
      · exact hv0 S.cl_z
  · rw [← hQ]
    refine lt_of_le_of_ne (S.clPre_le_QG W) fun heq => hWt ?_
    rw [← S.clSub_clPre W, heq, ← S.clPre_top, S.clSub_clPre]
  · intro m hm
    have key : ∀ {m' : G} (hm' : m' ∈ S.M) {x : G}, x ∈ S.clPre W →
        m' * x * m'⁻¹ ∈ S.clPre W := fun {m'} hm' {x} hx =>
      ⟨S.conj_mem_QG hm' hx.1, by rw [← S.ρ_cl ⟨m', hm'⟩ hx.1]; exact hWinv _ _ hx.2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key hm, fun hx => ?_⟩
    have h := key (S.M.inv_mem hm) hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at h

theorem widthSixAlternativeFourCase_of_core (h77 : AschbacherFSmith1977Statement)
    (hDW : DW.DW37Statement) (h80 : Smith1980OrthogonalStatement)
    (hAS : Quasithin.H13.InputAS91) (hcore : WidthSixCore) :
    WidthSixAlternativeFourCase := by
  intro G _ _ _ z hset hext hcard Mbar _ hMbar _
  have hz : orderOf z = 2 := hset.2.2.2.2.1
  have hcard' : Nat.card (coreQ z) = 2 ^ (1 + 2 * 6) := by rw [hcard]
  by_cases hwc : ZWeaklyClosedInCore z
  · exact Or.inr (Or.inl (psu_of_weaklyClosed h77 hset hext hcard' (by norm_num) hwc))
  by_cases hred : CoreReducible z
  · exact Or.inl (psl_of_reducible hDW hz hext hcard' (by norm_num) hwc hred)
  have hS6 : (setting hz hext hcard').width = 6 := setting_width hz hext hcard'
  have hQ := setting_QG hz hext hcard'
  have hex := DW.W4Rank.exists_conj_of_not_weaklyClosed (setting hz hext hcard')
    (setting_z hz hext hcard') hQ hwc
  have hirr : ¬ (setting hz hext hcard').IsReducible := fun h =>
    hred (coreReducible_of_isReducible _ (setting_z hz hext hcard') hQ h)
  rcases hcore G hset.2.1 (setting hz hext hcard') hS6 hex hirr with
    ⟨q, hq, hiso⟩ | ⟨-, hnc⟩ | ⟨hJ1, hJ2⟩
  ·
    have hMbar' : timmesfeldQuotientIso
        (timmesfeldFStar (Subgroup.centralizer ({(setting hz hext hcard').z} : Set G))) Mbar := by
      rw [← Bridge.generalizedFitting_eq_timmesfeldFStar]
      exact hMbar
    obtain ⟨e⟩ := Bridge.nonempty_mulEquiv_Mbar_ofFStar hz (timmesfeld_hypotheses hext hcard').1
      hMbar'
    have hiso' : Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q) := by
      rcases hiso with hA | hB
      · obtain ⟨f⟩ := hA
        exact Or.inl ⟨e.symm.trans f⟩
      · obtain ⟨f⟩ := hB
        exact Or.inr ⟨e.symm.trans f⟩
    have h := h80 G hset.1 z hz hext 6 hcard' (by norm_num) (by decide) Mbar hMbar q hq hiso'
    by_cases hplus : timmesfeldPlusType q
    · exact Or.inr (Or.inr (Or.inl (h.1 hplus)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h.2 hplus))))
  ·
    exact absurd hset.2.2.1 hnc
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hAS G inferInstance hset.1 z hz hJ1 hJ2 ?_)))))
    obtain ⟨g, hgQ, hgz⟩ := hex
    have hO2 : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) = coreQ z := by
      change (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype =
        (generalizedFitting (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype
      have h1 := hJ1.1
      change CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G)) =
        generalizedFitting (Subgroup.centralizer ({z} : Set G)) at h1
      rw [h1]
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hO2, ← hQ, inv_inv]
      exact hgQ
    · rw [inv_inv]
      exact hgz

end CFSG.GF2Type.Smith1979

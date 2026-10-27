module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Step2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [← sq] at hu2; exact hu2) hu1
  have hpg : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hle : Subgroup.zpowers u ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) := by
    refine le_pCoreOf_of_le_normalizer ?_ ?_ hpg
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [normalizer_zpowers_eq_centralizer hu2]
  intro h
  rw [h, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hu1 hle

theorem step2 (hI32 : LemmaI32) (h3 : Prop121Three) (h5 : Prop121Five)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) (hq : QTKECore G)
    {u v : G} (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1)
    (huv : u * v = v * u) {X : Subgroup G}
    (hX : IsComponentIn X (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)))
    (hXe : 2 ∣ Nat.card X) (hX4 : ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ Nat.card E = 4) :
    X ≤ (⨆ g ∈ oddLayer (Subgroup.centralizer ({u} : Set G)), CFSG.conjugate X g) ∧
      ((∃ J : Subgroup G, IsComponentIn J (Subgroup.centralizer ({u} : Set G)) ∧
          (⨆ g ∈ oddLayer (Subgroup.centralizer ({u} : Set G)), CFSG.conjugate X g) = J ∧
          v ∈ Subgroup.normalizer (J : Set G)) ∨
        ∃ J : Subgroup G, IsComponentIn J (Subgroup.centralizer ({u} : Set G)) ∧
          J ≠ CFSG.conjugate J v ∧
          (⨆ g ∈ oddLayer (Subgroup.centralizer ({u} : Set G)), CFSG.conjugate X g) =
            J ⊔ CFSG.conjugate J v ∧ ⁅J, CFSG.conjugate J v⁆ = ⊥ ∧
          Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* (↥X ⧸ Subgroup.center ↥X))) := by
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  have hu2' : u * u = 1 := by rwa [sq] at hu2
  have hv2' : v * v = 1 := by rwa [sq] at hv2
  have hpc : pCoreOf 2 H ≠ ⊥ := pCoreOf_centralizer_ne_bot hu1 hu2'
  have hK : CFSG.SectionRank.IsKGroupCat ↥H := (hq.1 H hpc).2
  have hvH : v ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr huv.symm
  have hX2 : IsTwoComponentIn X (H ⊓ Subgroup.centralizer ({v} : Set G)) :=
    isTwoComponentIn_of_isComponentIn hX hXe
  have hXY : X ≤ ⨆ g ∈ oddLayer H, CFSG.conjugate X g := by
    refine le_trans (le_of_eq (BenderBranch.conjugate_one X).symm) ?_
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) le_rfl
  refine ⟨hXY, ?_⟩
  rcases hI32 G H hK v hvH hv1 hv2 X hX2 with ⟨hY, hvY⟩ | ⟨J, hJ, hJne, hYJ, hiso⟩
  ·
    left
    set Y := ⨆ g ∈ oddLayer H, CFSG.conjugate X g with hYdef
    have hYX : X ≤ Y := hXY
    have hqY : CFSG.IsQuasisimple ↥Y := by
      have hperf : ⁅Y, Y⁆ = Y := perfect_of_mem_cComp hY.1
      refine h5 G hsimple hnonab hq H hpc Y hY.1 ?_ ?_
      · have hcen := pCore_le_center_of_oddCore_quotient hY.2
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hy' : y ∈ CFSG.pCore 2 ↥Y := by
          exact hy
        refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
        have hc := Subgroup.mem_center_iff.mp (hcen hy') ⟨w, hw⟩
        exact congrArg Subtype.val hc
      · obtain ⟨E, hEX, hE, hE4⟩ := hX4
        exact ⟨E, hEX.trans hYX, hE, hE4⟩
    exact ⟨Y, isComponentIn_of_mem_cComp hY.1 hqY, rfl, hvY⟩
  ·
    right
    have hJc : J ∈ cComp H := hJ.1
    have hnot : ¬ H ≤ Subgroup.normalizer (J : Set G) := fun hle =>
      hJne ((BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hle hvH)).symm)
    rcases h3 G hsimple hnonab hq H hpc J hJc with hnorm | ⟨-, hlist⟩
    · exact absurd hnorm hnot
    · obtain ⟨hs, hnc, hevJ, -⟩ := hlist
      have hqJ : CFSG.IsQuasisimple ↥J :=
        isQuasisimple_of_simple_O2_quotient (perfect_of_mem_cComp hJc) hJ.2 hs hnc
      have hJcomp : IsComponentIn J H := isComponentIn_of_mem_cComp hJc hqJ
      have hJev : 2 ∣ Nat.card J :=
        hevJ.trans ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)⟩
      have hXq : CFSG.IsQuasisimple ↥X := BenderBranch.isQuasisimple_of_isComponentIn hX
      have hJv : IsComponentIn (CFSG.conjugate J v) H := Unc25G2.isComponentIn_conjugate hJcomp hvH
      refine ⟨J, hJcomp, hJne, hYJ, ?_, oddTwoIso_iff_center hqJ hJev hXq hXe hiso⟩
      exact (BenderBranch.eq_or_commute_of_isComponentIn hJcomp hJv).resolve_left
        fun h => hJne h

end Step2

end CFSG.QuasithinUnique.Id2519

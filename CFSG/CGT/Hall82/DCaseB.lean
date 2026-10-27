module

public import CFSG.CGT.Hall82.DCaseA
public import CFSG.CGT.Hall82.DCaseBQ
public import CFSG.CGT.Hall82.DReducible
public import CFSG.CGT.Hall82.DSplit
public import CFSG.GF2Type.Smith1979W3.KProper
public import CFSG.GF2Type.Smith1979W3.CaseIINonsplit
public import CFSG.Quasithin.Vol2.Asc94.He42Holds
public import CFSG.Quasithin.Vol2.Asc94.HeOrderHolds
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.LargeExtraspecial.DWW4Rank

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

private theorem exists_mem_ne_ne_of_two_lt {A : Subgroup G} (hA : 2 < Nat.card A) (a b : G) :
    ∃ x ∈ A, x ≠ a ∧ x ≠ b := by
  by_contra h
  push_neg at h
  have hsub : (A : Set G) ⊆ {a, b} := fun x hx => by
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (h x hx hxa)
  have h2 : Nat.card (A : Set G) ≤ 2 :=
    (Nat.card_mono (Set.toFinite _) hsub).trans
      ((Set.ncard_insert_le a {b}).trans (by rw [Set.ncard_singleton]))
  exact absurd hA (not_lt.mpr h2)

theorem inCatalog_of_psl52_or_m24_or_he
    {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSL 5 2 1 ∨ Blueprint.NativeSporadic.IsSporadic X .M24 ∨
      Blueprint.NativeSporadic.IsSporadic X .He) : Assembly.InCatalog X := by
  rcases h with h | h | h
  · exact ClassicalModels.statedClassicalModel_PSL_inCatalog_all X 5 2 1
      (Blueprint.LieModel.statedClassicalModel h (by decide))
  · exact RankThree.GF2n.sporadicBridge_M24 X h
  · exact RankThree.GF2n.sporadicBridge_He X h

theorem inCatalog_of_not_centralizer_le
    (S : Setting G M L) (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (hcM : ¬ Subgroup.centralizer ({rep 5} : Set G) ≤ M) :
    Assembly.InCatalog G := by
  classical
  haveI := S.simple
  set H : Subgroup G := fiveCent rep with hH
  set Q : Subgroup G := fiveQ rep with hQ
  have h51 : rep 5 ≠ 1 := fun h => absurd ((rep_eq_one_iff hc).mp h) (by decide)
  have hz : orderOf (rep 5) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact rep_mul_self hc 5) h51
  have h5J : rep 5 ∈ CFSG.Open.pCoreOf 2 M := by
    rw [S.pCoreOf_eq_blockU hF hc hC1]
    exact hc.mem 5
  have hFit : generalizedFitting ↥H = CFSG.pCore 2 ↥H := S.cent (rep 5) h5J h51
  have h5Q : rep 5 ∈ Q := S.rep_mem_pCoreOf hF hD hc hC1 (by decide)
  have hcard : Nat.card Q = 128 := S.card_pCoreOf_five hF hD hc hC1 hcM
  have hZ : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) ↔ x = 1 ∨ x = rep 5 :=
    fun x hx => S.commute_pCoreOf_iff hF hD hc hC1 hcM hx
  have hcomm := S.comm_mem_pCoreOf hF hD hc hC1 hcM
  have hsq := S.mul_self_mem_pCoreOf hF hD hc hC1 hcM
  have hnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
    obtain ⟨x, hxQ, hx1, hx5⟩ := exists_mem_ne_ne_of_two_lt (A := Q) (by omega) 1 (rep 5)
    have hxc : ¬ ∀ y ∈ Q, x * y = y * x := fun h => by
      rcases (hZ x hxQ).mp h with h | h
      · exact hx1 h
      · exact hx5 h
    push_neg at hxc
    exact ⟨x, hxQ, hxc⟩
  have hext : IsExtraspecialPGroup 2 ↥Q :=
    LargeExtraspecial.isExtraspecialPGroup_two_of_center
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) h5Q h51 hZ hcomm
      (fun x hx => by rw [pow_two]; exact hsq x hx) hnc
  have hFS : Open.timmesfeldFStar ↥H = CFSG.pCore 2 ↥H := by
    rw [← LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar, hFit]
  have hext' : Open.timmesfeldIsExtraspecial (Open.timmesfeldFStar ↥H) := by
    rw [hFS, LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff]
    exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ H.subtype_injective).symm hext
  let T := LargeExtraspecial.Setting.ofFStar (rep 5) hz hext'
  have hTQG : T.QG = Q := by
    change (Open.timmesfeldFStar ↥H).map H.subtype = (CFSG.pCore 2 ↥H).map H.subtype
    rw [hFS]
  have hTw : T.width = 3 := by
    refine T.width_eq ?_
    change Nat.card ↥(Open.timmesfeldFStar ↥H) = 2 ^ (1 + 2 * 3)
    rw [hFS, Nat.card_congr (Subgroup.equivMapOfInjective _ _ H.subtype_injective).toEquiv]
    exact hcard
  have hNWC : GF2Type.Smith1979W3.NotWeaklyClosed T := by
    obtain ⟨g, hg, hne⟩ := S.exists_conj_five_mem hF hD hc hC1
    refine ⟨g, ?_, hne⟩
    rw [hTQG]
    exact hg
  obtain ⟨Φ, hΦinj, hΦ, hΦrep⟩ := S.exists_split hF hD hc hC1
  have hQn : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) q).mp hq
  obtain ⟨A, hAQ, h5A, hA16, hAn⟩ := S.exists_normal_of_split hF hD hc hC1 Φ hΦinj hΦ hΦrep
    (S.pCoreOf_centralizer_five_le hF hc hC1) (LieType.BorelTits.pCoreOf_le 2 _) hQn
    (S.rep_mem_pCoreOf_iff hF hD hc hC1 hcM) (S.psiSub_pCoreOf_eq hF hD hc hC1 hcM)
    (S.psiSub_M_eq_hexaM hF hD hc hC1 hcM) hcomm hsq
    (fun g h h' hh hh' hg => S.mem_of_conj_oval hF hD hc hC1 hh hh' hg)
  have hred : T.IsReducible := by
    refine LargeExtraspecial.DW.W4Rank.isReducible_of_lt T (A := A) ?_ ?_ ?_
    · rw [SetLike.lt_iff_le_and_exists]
      refine ⟨fun x hx => ?_, ?_⟩
      · rcases (LargeExtraspecial.DW.W4Rank.mem_center_map_QG_iff T).mp hx with h | h
        · rw [h]
          exact A.one_mem
        · rw [h]
          exact h5A
      · obtain ⟨x, hxA, hx1, hx5⟩ := exists_mem_ne_ne_of_two_lt (A := A) (by omega) 1 (rep 5)
        refine ⟨x, hxA, fun hx => ?_⟩
        rcases (LargeExtraspecial.DW.W4Rank.mem_center_map_QG_iff T).mp hx with h | h
        · exact hx1 h
        · exact hx5 h
    · rw [hTQG]
      refine lt_of_le_of_ne hAQ fun h => ?_
      rw [h, hcard] at hA16
      omega
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro a
      refine ⟨fun ha => hAn g hg a ha, fun ha => ?_⟩
      have h := hAn g⁻¹ (H.inv_mem hg) _ ha
      simpa [mul_assoc] using h
  have hK : Assembly.KProper Blueprint.Catalog G :=
    Assembly.KProper.of_catalogImp RankThree.PartOne.TCB.tauCetiCatalogBridge S.kProper
  exact inCatalog_of_psl52_or_m24_or_he
    (GF2Type.Smith1979W3.reducibleK_of_split GF2Type.Smith1979W3.dwSplitWidthThree
        (Quasithin.A94.asc94K_of_he_order Quasithin.A94.he_order_holds) G hK T hTw hNWC hred)

end CFSG.CGT.Hall82.Setting

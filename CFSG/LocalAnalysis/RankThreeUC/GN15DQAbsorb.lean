module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Base
public import CFSG.LocalAnalysis.RankThreeUC.GN15Steps
import CFSG.LocalAnalysis.RankThreeUC.GN15DQNormal
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.Open
open scoped Pointwise

section Decomposition

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

private theorem biSup_le_centralizer_biSup {Gp : Type*} [Group Gp] [Finite Gp]
    {F F' : Set (Subgroup Gp)} (hF : ∀ L ∈ F, IsComponentOf L ⊤)
    (hF' : ∀ L ∈ F', IsComponentOf L ⊤) (hd : ∀ L ∈ F, ∀ L' ∈ F', L ≠ L') :
    (⨆ L ∈ F, L) ≤ Subgroup.centralizer ((⨆ L ∈ F', L : Subgroup Gp) : Set Gp) := by
  refine iSup₂_le fun L hL => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun L' hL' => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  rcases CFSG.LocalCores.distinct_components_commute
    ((CFSG.isComponent_iff_open L').2 (hF' L' hL')) ((CFSG.isComponent_iff_open L).2 (hF L hL))
    with h | h
  · exact absurd h.symm (hd L hL L' hL')
  · exact h

private theorem mem_sup_sup_of_le_centralizer {Gp : Type*} [Group Gp] {A B C : Subgroup Gp}
    (hAB : A ≤ Subgroup.centralizer (B : Set Gp)) (hAC : A ≤ Subgroup.centralizer (C : Set Gp))
    (hBC : B ≤ Subgroup.centralizer (C : Set Gp)) {x : Gp} (hx : x ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, x = a * b * c := by
  have h1 : (↑(A ⊔ B) : Set Gp) = (A : Set Gp) * (B : Set Gp) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B
      (hAB.trans (Subgroup.centralizer_le_normalizer _))
  have h2 : A ⊔ B ≤ Subgroup.centralizer (C : Set Gp) := sup_le hAC hBC
  have h3 : (↑(A ⊔ B ⊔ C) : Set Gp) = ((A ⊔ B : Subgroup Gp) : Set Gp) * (C : Set Gp) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (A ⊔ B) C
      (h2.trans (Subgroup.centralizer_le_normalizer _))
  have hx' : x ∈ (↑(A ⊔ B ⊔ C) : Set Gp) := hx
  rw [h3] at hx'
  obtain ⟨y, hy, c, hc, rfl⟩ := hx'
  have hy' : y ∈ (↑(A ⊔ B) : Set Gp) := hy
  rw [h1] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

private def famY (T T₁ T₂ : Subgroup X) : Set (Subgroup (X ⧸ gnC T)) :=
  {L | (IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥) ∧ GNYComponent T T₁ T₂ L}

private def famC (T T₁ T₂ : Subgroup X) : Set (Subgroup (X ⧸ gnC T)) :=
  {L | (IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥) ∧ ¬ GNYComponent T T₁ T₂ L ∧
    L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))}

private def famN (T T₁ T₂ : Subgroup X) : Set (Subgroup (X ⧸ gnC T)) :=
  {L | (IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥) ∧ ¬ GNYComponent T T₁ T₂ L ∧
    ¬ L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))}

omit [Finite X] in
private theorem gnDStar_le_sup_fam :
    gnDStar T ≤ (⨆ L ∈ famC T T₁ T₂, L) ⊔ (⨆ L ∈ famY T T₁ T₂, L) ⊔ (⨆ L ∈ famN T T₁ T₂, L) := by
  refine iSup₂_le fun L hL => ?_
  by_cases hY : GNYComponent T T₁ T₂ L
  · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup₂_of_le L ⟨hL, hY⟩ le_rfl))
  · by_cases hC : L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_iSup₂_of_le L ⟨hL, hY, hC⟩ le_rfl))
    · exact le_sup_of_le_right (le_iSup₂_of_le L ⟨hL, hY, hC⟩ le_rfl)

omit [Finite X] in
private theorem famC_le : (⨆ L ∈ famC T T₁ T₂, L) ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) :=
  iSup₂_le fun _ hL => hL.2.2

omit [Finite X] in
private theorem famY_le : (⨆ L ∈ famY T T₁ T₂, L) ≤ Ystar T T₁ T₂ :=
  iSup₂_le fun L hL => le_iSup₂_of_le L hL.2 le_rfl

omit [Finite X] in
private theorem famN_le : (⨆ L ∈ famN T T₁ T₂, L) ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) :=
  iSup₂_le fun _ hL =>
    (le_or_le_of_not_gnYComponent hL.1.1 hL.2.1).resolve_left hL.2.2

private theorem famC_le_centralizer_famY :
    (⨆ L ∈ famC T T₁ T₂, L) ≤ Subgroup.centralizer ((⨆ L ∈ famY T T₁ T₂, L : Subgroup _) : Set _) :=
  biSup_le_centralizer_biSup (fun _ hL => hL.1.1) (fun _ hL => hL.1.1)
    (fun _ hL _ hL' h => hL.2.1 (h ▸ hL'.2))

private theorem famC_le_centralizer_famN :
    (⨆ L ∈ famC T T₁ T₂, L) ≤ Subgroup.centralizer ((⨆ L ∈ famN T T₁ T₂, L : Subgroup _) : Set _) :=
  biSup_le_centralizer_biSup (fun _ hL => hL.1.1) (fun _ hL => hL.1.1)
    (fun _ hL _ hL' h => hL'.2.2 (h ▸ hL.2.2))

private theorem famY_le_centralizer_famN :
    (⨆ L ∈ famY T T₁ T₂, L) ≤ Subgroup.centralizer ((⨆ L ∈ famN T T₁ T₂, L : Subgroup _) : Set _) :=
  biSup_le_centralizer_biSup (fun _ hL => hL.1.1) (fun _ hL => hL.1.1)
    (fun _ hL _ hL' h => hL'.2.1 (h ▸ hL.2))

private theorem famN_le_centralizer_Ystar :
    (⨆ L ∈ famN T T₁ T₂, L) ≤ Subgroup.centralizer (Ystar T T₁ T₂ : Set (X ⧸ gnC T)) :=
  biSup_le_centralizer_biSup (F' := {L | GNYComponent T T₁ T₂ L}) (fun _ hL => hL.1.1)
    (fun _ hL => hL.1) (fun _ hL _ hL' h => hL.2.1 (h ▸ hL'))

private theorem exists_decomposition {e : X} (he : e ∈ gnDPre T) :
    ∃ c ∈ Subgroup.centralizer (T₁ : Set X), ∃ p ∈ Y0 T T₁ T₂,
      ∃ r ∈ Subgroup.normalizer (T₂ : Set X),
        (∀ y ∈ Y0 T T₁ T₂, r * y * r⁻¹ ∈ Y0 T T₁ T₂) ∧ ∃ z ∈ gnC T, e = c * p * r * z := by
  have he' : toStar T e ∈ gnDStar T := he
  obtain ⟨pc, hpc, py, hpy, pn, hpn, hdec⟩ := mem_sup_sup_of_le_centralizer
    famC_le_centralizer_famY famC_le_centralizer_famN famY_le_centralizer_famN
    (gnDStar_le_sup_fam he')
  obtain ⟨c, hc, hcpc⟩ := (famC_le hpc : pc ∈ gnImg T (Subgroup.centralizer (T₁ : Set X)))
  obtain ⟨r, hr, hrpn⟩ := (famN_le hpn : pn ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)))
  obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective py
  have hcpc' : (c : X ⧸ gnC T) = pc := hcpc
  have hrpn' : (r : X ⧸ gnC T) = pn := hrpn
  have hpY : p ∈ Y0 T T₁ T₂ := by
    show toStar T p ∈ Ystar T T₁ T₂
    rw [show toStar T p = py from hp]
    exact famY_le hpy
  have hcpr : ((c * p * r : X) : X ⧸ gnC T) = (e : X ⧸ gnC T) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hcpc', hp, hrpn']
    exact hdec.symm
  refine ⟨c, hc, p, hpY, r, hr, fun y hy => ?_, (c * p * r)⁻¹ * e, QuotientGroup.eq.1 hcpr,
    by group⟩
  show toStar T (r * y * r⁻¹) ∈ Ystar T T₁ T₂
  have hy' : toStar T y ∈ Ystar T T₁ T₂ := hy
  have hcomm := Subgroup.mem_centralizer_iff.1 (famN_le_centralizer_Ystar hpn) _ hy'
  rw [map_mul, map_mul, map_inv]
  have hrr : toStar T r = pn := hrpn'
  rw [hrr]
  have : pn * toStar T y * pn⁻¹ = toStar T y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  rw [this]
  exact hy'

theorem gnAbsorbs_gnDPre (hX : GNSetting X T) : GNAbsorbs T T₁ T₂ (gnDPre T) := by
  intro d hd m hm
  obtain ⟨a, ha, y, hy, n, hn, rfl⟩ := mem_gnM_iff.mp hm
  have hd' : a⁻¹ * d * a ∈ gnDPre T := by
    simpa using (gnDPre_normal hX).conj_mem d hd a⁻¹
  obtain ⟨c, hc, p, hp, r, hr, hrY, z, hz, hdec⟩ :=
    exists_decomposition (T₁ := T₁) (T₂ := T₂) hd'
  have hz₁ : r * z * r⁻¹ ∈ Y0 T T₁ T₂ := by
    have : r * z * r⁻¹ ∈ gnC T := (gnC_normal T).conj_mem z hz r
    show toStar T (r * z * r⁻¹) ∈ Ystar T T₁ T₂
    have h1 : toStar T (r * z * r⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 this
    rw [h1]
    exact one_mem _
  refine mem_gnM_iff.mpr ⟨a * c, mul_mem ha hc, p * (r * z * r⁻¹) * (r * y * r⁻¹),
    mul_mem (mul_mem hp hz₁) (hrY y hy), r * n, mul_mem hr hn, ?_⟩
  have hd'' : d = a * (c * p * r * z) * a⁻¹ := by
    rw [← hdec]; group
  rw [hd'']
  group

end Decomposition

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

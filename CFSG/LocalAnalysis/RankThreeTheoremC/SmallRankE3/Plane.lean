module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

theorem le_of_isPGroup_of_plane_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {Q : Subgroup G} (hQ : IsPGroup 3 Q)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q) : Q ≤ M := by
  have hsit := h.situation
  have hpl := SmallRankPlane.of_situation h.setting hsit h.point h.central
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal h.setting hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  by_contra hQM
  have hYQ : Q ⊓ M < Q :=
    lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
  have hBY : zpowers x ⊔ zpowers z ≤ Q ⊓ M := le_inf hBQ (hBP.trans hPM)
  have hY2 : 2 ≤ CFSG.Open.pRank 3 (Q ⊓ M) :=
    le_pRank_of_isElemAbelian Nat.prime_three hBY hpl.isElemAbelian hpl.card_eq
  have hNY : normalizer ((Q ⊓ M : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank h.setting h.u0 hsit.mem_sigmaA hsit.isCoreMaxLocal
      (hQ.to_le inf_le_left) inf_le_right hY2
  obtain ⟨y, hyQ, hyN, hyY⟩ := exists_mem_normalizer_not_mem_of_lt hQ hYQ
  exact hyY ⟨hyQ, hNY hyN⟩

theorem pRank_centralizer_le_two_of_mem_plane {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {y : G} (hy : y ∈ zpowers x ⊔ zpowers z) (hyz : y ∉ zpowers z) :
    CFSG.Open.pRank 3 (centralizer ({y} : Set G)) ≤ 2 := by
  have hsit := h.situation
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal h.setting hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra hc
    exact hsit.largeObstruction_empty x ⟨hPM h.point.mem, h.point.ne_one, h.point.pow_eq_one,
      by omega, h.point.not_centralizer_le⟩
  obtain ⟨g, -, hconj⟩ :=
    exists_mem_normalizer_conj_zpowers h.setting hsit h.point h.central hy hyz
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({y} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    calc centralizer ({y} : Set G)
        = centralizer ((zpowers y : Subgroup G) : Set G) := hcz _
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hconj]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  rw [hC, pRank_map_automorphism 3 Nat.prime_three.one_lt]
  exact hCx

theorem mem_zpowers_of_conj_mem_plane {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  by_contra hgz
  have h2 := pRank_centralizer_le_two_of_mem_plane h hg hgz
  have hP3 := (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA
    h.situation.isCoreMaxLocal).2
  have hPz : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp h.central.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h3 := pRank_mono 3 Nat.prime_three.one_lt hPz
  rw [pRank_map_automorphism 3 Nat.prime_three.one_lt, hP3] at h3
  omega

set_option linter.unusedVariables false in
theorem centralizer_le_of_isElemAbelian_le_centralizer {P : Sylow 3 G} {M : Subgroup G}
    {x z : G} (h : Setup65A G P M x z) {y : G} (hyM : y ∈ M) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27)
    (hEy : E ≤ centralizer ({y} : Set G)) : centralizer ({y} : Set G) ≤ M := by
  by_contra hCM
  have h3 : 3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set G)) :=
    le_pRank_of_isElemAbelian Nat.prime_three hEy hE (by rw [hEc]; norm_num)
  exact h.situation.largeObstruction_empty y ⟨hyM, hy1, hy3, h3, hCM⟩

theorem normalizer_zpowers_le_of_isElemAbelian_le_centralizer {P : Sylow 3 G} {M : Subgroup G}
    {x z : G} (h : Setup65A G P M x z) {y : G} (hyM : y ∈ M) (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27)
    (hEy : E ≤ centralizer ({y} : Set G)) : normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
  have hsit := h.situation
  have hCM : centralizer ({y} : Set G) ≤ M :=
    centralizer_le_of_isElemAbelian_le_centralizer h hyM hy1 hy3 hEM hE hEc hEy
  obtain ⟨S, hES, hSC, hS3, hSidx⟩ :=
    exists_sylow_le_of_isPGroup Nat.prime_three hEy (elementary_isPGroup 3 E hE)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 S (centralizer ({y} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hSC, hS3, hSidx⟩
  have hS3' : 3 ≤ CFSG.Open.pRank 3 S :=
    le_pRank_of_isElemAbelian Nat.prime_three hES hE (by rw [hEc]; norm_num)
  have hSM : normalizer (S : Set G) ≤ M :=
    normalizer_le_of_le_of_two_le_pRank h.setting h.u0 hsit.mem_sigmaA hsit.isCoreMaxLocal hS3
      (hSC.trans hCM) (by omega)
  exact (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer y)
    hSsyl).trans (sup_le hCM hSM)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

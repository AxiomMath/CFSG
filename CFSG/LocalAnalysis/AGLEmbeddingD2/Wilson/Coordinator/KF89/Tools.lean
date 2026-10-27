module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.Passage

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_normalizes_perfect {e g : G} {L P : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 e) (hg : g ∈ centralizer ({e} : Set G)) (hP : P ≠ ⊥)
    (hPperf : Group.IsPerfect P) (hPL : P ≤ L) (hPg : ∀ y ∈ P, g⁻¹ * y * g ∈ P) :
    g ∈ normalizer (L : Set G) := by
  set H := centralizer ({e} : Set G) with hH
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  set σ : MulAut H := MulAut.conj ⟨g, hg⟩ with hσ
  have hL₀' := map_mulEquiv_mem_thetaComponents Nat.prime_three σ hL₀
  have hPH : P ≤ H := hPL.trans (map_subtype_le L₀)
  set P₀ := P.subgroupOf H with hP₀
  have hP₀map : P₀.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h0
    apply hP
    rw [← hP₀map, h0, Subgroup.map_bot]
  have hP₀perf : Group.IsPerfect P₀ :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hP₀L : P₀ ≤ L₀ := by
    intro y hy
    have hy' : (y : G) ∈ L₀.map H.subtype := hPL (mem_subgroupOf.mp hy)
    obtain ⟨w, hw, hwy⟩ := hy'
    have : w = y := Subtype.ext hwy
    rwa [← this]
  have hP₀L' : P₀ ≤ L₀.map σ.toMonoidHom := by
    intro y hy
    have hyP : (y : G) ∈ P := mem_subgroupOf.mp hy
    have hgH : g⁻¹ * (y : G) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) y.2) hg
    refine ⟨⟨g⁻¹ * (y : G) * g, hgH⟩, hP₀L (mem_subgroupOf.mpr (hPg _ hyP)), ?_⟩
    apply Subtype.ext
    change g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
    group
  have heq := theta_component_eq_of_perfect_le Nat.prime_three hL₀ hL₀' hP₀ne hP₀perf hP₀L hP₀L'
  rw [mem_normalizer_iff_map_conj_eq]
  change (L₀.map H.subtype).map (MulAut.conj g).toMonoidHom = L₀.map H.subtype
  have hconj : (L₀.map H.subtype).map (MulAut.conj g).toMonoidHom =
      (L₀.map σ.toMonoidHom).map H.subtype := by
    rw [map_map, map_map]
    rfl
  rw [hconj, ← heq]

theorem theta_map_le_of_mem_thetaComponentsAt {e : G} {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 e) :
    (aschbacherSolvableCore 3 Y).map Y.subtype ≤
      (aschbacherSolvableCore 3 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype := by
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  have hθ := (aschbacherSolvableCore_map_mulEquiv Nat.prime_three
    (Y₀.equivMapOfInjective _ (centralizer ({e} : Set G)).subtype_injective)).symm
  have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hY₀.2.1
  rintro _ ⟨u, hu, rfl⟩
  have hu' : u ∈ aschbacherSolvableCore 3 (Y₀.map (centralizer ({e} : Set G)).subtype) := hu
  rw [hθ] at hu'
  obtain ⟨v, hv, hvu⟩ := hu'
  have hv' : (v : centralizer ({e} : Set G)) ∈ inSubgroup (aschbacherSolvableCore 3) Y₀ :=
    ⟨v, hv, rfl⟩
  rw [hint] at hv'
  refine ⟨(v : centralizer ({e} : Set G)), hv'.2, ?_⟩
  rw [← hvu]
  rfl

omit [Finite G] in
theorem conj_mem_inSubgroup_perfectResidual {M : Subgroup G} {g : G} (hg : g ∈ M) {j : G}
    (hj : j ∈ inSubgroup perfectResidual M) : g * j * g⁻¹ ∈ inSubgroup perfectResidual M := by
  obtain ⟨j', hj', rfl⟩ := hj
  have hn : (perfectResidual M).Normal := inferInstance
  exact ⟨⟨g, hg⟩ * j' * ⟨g, hg⟩⁻¹, hn.conj_mem _ hj' _, rfl⟩

@[expose] noncomputable def actHat (Y : Subgroup G) :
    normalizer (Y : Set G) →*
      MulAut ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y)) :=
  (K423Cover.zQuot (Y ⧸ aschbacherSolvableCore 3 Y)).comp
    ((thetaQuotMulAut Y).comp (compAction Y))

theorem actHat_mk (Y : Subgroup G) (g : normalizer (Y : Set G)) (y : Y) :
    actHat Y g (((y : Y ⧸ aschbacherSolvableCore 3 Y)) :
      (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y)) =
      (((Y.normalizerMonoidHom g y : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :
        (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y)) :=
  rfl

omit [Finite G] in
theorem exists_conj_eq_of_pow_three {Q : Type*} [Group Q] [Finite Q]
    (hOut : Nat.card (Outer Q) ≤ 2) (hZ : center Q = ⊥) {σ : MulAut Q} (hσ : σ ^ 3 = 1) :
    ∃ y : Q, MulAut.conj y = σ ∧ y ^ 3 = 1 := by
  have hin : σ ∈ (MulAut.conj : Q →* MulAut Q).range := by
    set q : Outer Q := QuotientGroup.mk σ with hq
    have hpos : 0 < Nat.card (Outer Q) := Nat.card_pos
    have hdvd : orderOf q ∣ 2 := by
      have h1 := orderOf_dvd_natCard q
      rcases (show Nat.card (Outer Q) = 1 ∨ Nat.card (Outer Q) = 2 by omega) with h | h
      · rw [h] at h1
        exact h1.trans (one_dvd 2)
      · rwa [h] at h1
    have h2 : q ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    have h3 : q ^ 3 = 1 := by rw [hq, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one]
    have h1 : q = 1 := by
      calc q = q ^ 3 * (q ^ 2)⁻¹ := by group
        _ = 1 := by rw [h2, h3, inv_one, mul_one]
    rw [hq] at h1
    have h4 : σ ∈ inner Q := (QuotientGroup.eq_one_iff (N := inner Q) _).mp h1
    exact h4
  obtain ⟨y, rfl⟩ := hin
  refine ⟨y, rfl, ?_⟩
  have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow, hσ]
  have h2 : y ^ 3 ∈ center Q := by
    rw [mem_center_iff]
    intro z
    have := congrArg (fun τ : MulAut Q => τ z) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * y ^ 3 = y ^ 3 * z * (y ^ 3)⁻¹ * y ^ 3 := by rw [this]
      _ = y ^ 3 * z := by group
  rw [hZ, mem_bot] at h2
  exact h2

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

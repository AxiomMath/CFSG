module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLinTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinLang

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.HardMathSupport.Foote.ModuleExclusions
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinTw (scalar_eq_smul_one units_eq_one_of_sq)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld
  (pslEquivLarge pslEquivLarge_mk nonempty_psl_equiv_statedProj isSimpleGroup_statedProj_of_three_le
    isPerfect_statedProj_of_three_le component_eq_of_fixed nonempty_quotCenter_equiv)
open scoped commutatorElement

theorem lang_fixed_nz {d : ℕ} [NeZero d] {K : Type} [Field K] [Finite K] (A : GL (Fin d) K) (σ : K ≃+* K)
    (c : K)
    (hg : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K),
      β (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) :
    ∃ Y : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      Y ≤ fixSubgroup β ∧ (Y.subgroupOf (fixSubgroup β)).Normal ∧
        ⁅fixSubgroup β, fixSubgroup β⁆ ≤ Y ∧
        Nonempty (↥Y ≃* StatedProj (StatedSL d ↥(fixField σ))) := by
  obtain ⟨Y₀, hY₀F, hY₀n, hFY₀, ⟨e₀⟩⟩ := exists_psl_fix_equiv σ A c hg
  obtain ⟨eP⟩ := nonempty_psl_equiv_statedProj d ↥(fixField σ)
  have hcomp : ∀ y : PSL (Fin d) K,
      β (pslEquivLarge d y) = pslEquivLarge d (slTwistBar σ A y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [slTwistBar_mk, pslEquivLarge_mk, pslEquivLarge_mk]
    exact hβ g
  have hC : fixSubgroup β = (fixHom (slTwistBar σ A)).map (pslEquivLarge d).toMonoidHom := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨(pslEquivLarge d).symm x, ?_, (pslEquivLarge d).apply_symm_apply x⟩
      rw [mem_fixHom]
      have h1 : pslEquivLarge d (slTwistBar σ A ((pslEquivLarge d).symm x)) =
          pslEquivLarge d ((pslEquivLarge d).symm x) := by
        rw [← hcomp, MulEquiv.apply_symm_apply]
        exact hx
      exact (pslEquivLarge d).injective h1
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      show β (pslEquivLarge d y) = pslEquivLarge d y
      rw [hcomp, mem_fixHom.1 hy]
  have hYC : Y₀.map (pslEquivLarge d).toMonoidHom ≤ fixSubgroup β := by
    rw [hC]
    exact Subgroup.map_mono hY₀F
  have hYn : ((Y₀.map (pslEquivLarge d).toMonoidHom).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYC]
    intro h k hh hk
    rw [hC] at hk
    obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨f₀ * h₀ * f₀⁻¹, ?_, by simp⟩
    exact (Subgroup.normal_subgroupOf_iff hY₀F).1 hY₀n h₀ f₀ hh₀ hf₀
  have hCY : ⁅fixSubgroup β, fixSubgroup β⁆ ≤ Y₀.map (pslEquivLarge d).toMonoidHom := by
    rw [hC, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hFY₀
  refine ⟨Y₀.map (pslEquivLarge d).toMonoidHom, hYC, hYn, hCY, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective Y₀ (pslEquivLarge d).toMonoidHom (pslEquivLarge d).injective).symm.trans
    (e₀.trans eP)



theorem isPerfect_statedSL_two_of_four_le {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (StatedSL 2 F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
  exact Group.IsPerfect.ofSurjective
    (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toMonoidHom)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective

theorem isSimpleGroup_statedProj_two_of_four_le {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup (StatedProj (StatedSL 2 F)) :=
  CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL F (by norm_num) (Or.inr (by omega))
    (Or.inr (by omega))

theorem not_perfect_of_prime_card {J : Type} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card J = p) [Group.IsPerfect J] : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic J := isCyclic_of_prime_card hc
  have h1 : commutator J = ⊥ := commutator_eq_bot J
  have h2 : (⊤ : Subgroup J) = ⊥ := by
    rw [← Group.IsPerfect.commutator_eq_top, h1]
  have hx : ∀ x : J, x = 1 := fun x => by
    have hm : x ∈ (⊤ : Subgroup J) := Subgroup.mem_top x
    rw [h2, Subgroup.mem_bot] at hm
    exact hm
  have h1card : Nat.card J = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun x y => by rw [hx x, hx y]⟩, ⟨1⟩⟩
  rw [h1card] at hc
  exact hp.one_lt.ne hc

theorem card_eq_one_of_perfect_of_dvd_six (J : Type) [Group J] [Finite J] [Group.IsPerfect J]
    (hJ : Nat.card J ∣ 6) : Nat.card J = 1 := by
  have hle : Nat.card J ≤ 6 := Nat.le_of_dvd (by norm_num) hJ
  obtain ⟨n, hn⟩ : ∃ n, Nat.card J = n := ⟨_, rfl⟩
  rw [hn] at hJ hle ⊢
  interval_cases n
  · norm_num at hJ
  · rfl
  · exact (not_perfect_of_prime_card Nat.prime_two hn).elim
  · exact (not_perfect_of_prime_card Nat.prime_three hn).elim
  · norm_num at hJ
  · norm_num at hJ
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : Fintype J := Fintype.ofFinite J
    have h3 : 3 ∣ Fintype.card J := by
      rw [← Nat.card_eq_fintype_card, hn]
      norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 h3
    have hHcard : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
    have hidx : (Subgroup.zpowers g).index = 2 := by
      have hm := (Subgroup.zpowers g).index_mul_card
      rw [hHcard, hn] at hm
      omega
    haveI : (Subgroup.zpowers g).Normal := Subgroup.normal_of_index_eq_two hidx
    haveI : Group.IsPerfect (J ⧸ Subgroup.zpowers g) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.zpowers g))
        (QuotientGroup.mk'_surjective _)
    have hq : Nat.card (J ⧸ Subgroup.zpowers g) = 2 := hidx
    exact (not_perfect_of_prime_card Nat.prime_two hq).elim

theorem card_statedProj_two_eq_six {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0) (hF : Nat.card F = 2) :
    Nat.card (StatedProj (StatedSL 2 F)) = 6 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hS : slGL (Fin 2) F = StatedSL 2 F := (CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 F).symm
  have hN : (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hx
    have hx1 : (x : GL (Fin 2) F) ∈ slGL (Fin 2) F := by
      rw [hS]
      exact x.2
    have hd1 := mem_slGL.1 hx1
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one] at hd1
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd1
    have hc1 : c = 1 := units_eq_one_of_sq h2 c hd1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hc, hc1, map_one]
  have hSL : Nat.card (StatedSL 2 F) = 6 := by
    rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
      Matrix.card_SL_field, hq]
    norm_num [Fin.prod_univ_two]
  have key := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
  have h1 : Nat.card ↥((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) = 1 := by
    rw [hN]
    exact Subgroup.card_bot
  rw [h1, mul_one, hSL] at key
  exact key.symm

theorem fixed_component_iso {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0)
    (A : GL (Fin d) K) (σ : K ≃+* K) (p : ℕ) (hord : orderOf σ = p)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x))
    (hsc : ∃ c : K, Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) (hJ : GLAPComponent p (fixSubgroup u) J)
    (h4 : 3 ≤ d ∨ 4 ≤ Nat.card (fixField σ)) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL d ↥(fixField σ))) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨c, hc⟩ := hsc
  obtain ⟨Y, hYC, hYn, hCY, ⟨eY⟩⟩ := lang_fixed_nz A σ c hc u hβ
  rcases (show 3 ≤ d ∨ d = 2 by omega) with h3 | h2d
  · haveI := isSimpleGroup_statedProj_of_three_le h3 ↥(fixField σ)
    haveI := isPerfect_statedProj_of_three_le h3 ↥(fixField σ)
    haveI : IsSimpleGroup ↥Y := eY.isSimpleGroup
    haveI : Group.IsPerfect ↥Y :=
      Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
    rw [component_eq_of_fixed hJ hYC hYn hCY]
    exact nonempty_quotCenter_equiv eY
  · have h4' : 4 ≤ Nat.card (fixField σ) := h4.resolve_left (by omega)
    subst h2d
    haveI := isSimpleGroup_statedProj_two_of_four_le h4'
    haveI := isPerfect_statedSL_two_of_four_le h4'
    haveI : Group.IsPerfect (StatedProj (StatedSL 2 ↥(fixField σ))) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI : IsSimpleGroup ↥Y := eY.isSimpleGroup
    haveI : Group.IsPerfect ↥Y :=
      Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
    rw [component_eq_of_fixed hJ hYC hYn hCY]
    exact nonempty_quotCenter_equiv eY

theorem no_pComponent_two_two {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0)
    (A : GL (Fin 2) K) (σ : K ≃+* K) (p : ℕ) (hord : orderOf σ = p)
    (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)))
    (hβ : ∀ x : ↥(slGL (Fin 2) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) (slTwist σ A x))
    (hsc : ∃ c : K, Ai σ (A : Matrix (Fin 2) (Fin 2) K) (orderOf σ) = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hcard : Nat.card (fixField σ) = 2)
    (J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) (hJ : GLAPComponent p (fixSubgroup u) J) :
    False := by
  obtain ⟨c, hc⟩ := hsc
  obtain ⟨Y, hYC, hYn, hCY, ⟨eY⟩⟩ := lang_fixed_nz A σ c hc u hβ
  have h2F : (2 : ↥(fixField σ)) = 0 := Subtype.ext h2
  have hYcard : Nat.card ↥Y = 6 := by
    rw [Nat.card_congr eY.toEquiv]
    exact card_statedProj_two_eq_six h2F hcard
  have hperf : ⁅J, J⁆ = J := Lemma53Ns.glaPComponent_perfect hJ
  have hJY : J ≤ Y :=
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup u, fixSubgroup u⁆ := Subgroup.commutator_mono hJ.1 hJ.1
      _ ≤ Y := hCY
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
  have hdvd : Nat.card ↥J ∣ 6 := by
    have h1 : Nat.card ↥(J.subgroupOf Y) = Nat.card ↥J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv
    have h3 : Nat.card ↥(J.subgroupOf Y) ∣ Nat.card ↥Y := Subgroup.card_subgroup_dvd_card _
    rw [h1, hYcard] at h3
    exact h3
  exact glaPComponent_ne_bot hJ (Subgroup.card_eq_one.1 (card_eq_one_of_perfect_of_dvd_six ↥J hdvd))

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinLang

end

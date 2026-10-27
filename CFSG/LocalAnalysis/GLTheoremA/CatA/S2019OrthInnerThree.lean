module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthThreeFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthWittOne
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Cubic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympInnerThree
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreLift
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LieType.SeitzGeneration.OrthSingular

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Helpers

private theorem mem_commutator_of_coe_mem {G : Type*} [Group G] {Γ : Subgroup G} {y : Γ}
    (hy : (y : G) ∈ ⁅Γ, Γ⁆) : y ∈ commutator Γ := by
  rw [← Subgroup.map_subtype_commutator] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show y = z from Subtype.ext hzy.symm]

private theorem not_isQuasisimple_of_comm'' {G : Type*} [Group G]
    (h : ∀ a b : G, a * b = b * a) : ¬ CFSG.IsQuasisimple G := by
  rintro ⟨-, -, a, b, hab⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem exists_sq_eq_one_of_mem_scalarKernel''
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {z : ↥(orthDerived Q)}
    (hz : z ∈ (scalars K V).subgroupOf (orthDerived Q)) :
    ∃ c : K, c ^ 2 = 1 ∧ ∀ v, (z : V ≃ₗ[K] V) v = c • v := by
  have ha : ∃ a : V, Q a ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    apply hu
    apply eq_zero_of_polar_eq_zero hQ
    intro v
    rw [QuadraticMap.polar, h, h, h, sub_zero, sub_zero]
  obtain ⟨a, ha⟩ := ha
  exact CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars (Subgroup.mem_subgroupOf.1 hz)
    (orthDerived_le_orthogonalGroup z.2) ha

private theorem ker_mk'_le_center :
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker ≤
      Subgroup.center ↥(orthDerived Q) := by
  rw [QuotientGroup.ker_mk']
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.1 hz) g).symm

end Helpers

section Core

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem commutator_eq_bot_of_orthBlockThree [CharP K 3] {A : Subgroup (V ≃ₗ[K] V)}
    (hAΩ : A ≤ orthDerived Q) (hAp : ⁅A, A⁆ = A) (hA : OrthBlockThree A)
    {J T₀ : Subgroup (ProjOrthDerived Q)}
    (hJ : J = (A.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJT : J ≤ Subgroup.normalizer (T₀ : Set (ProjOrthDerived Q))) (hT : IsPGroup 2 T₀) :
    ⁅T₀, J⁆ = ⊥ := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨P, hPA, hP3, hP9, hPZ, hPq⟩ := hA
  have hPΩ : P ≤ orthDerived Q := hPA.trans hAΩ
  let ρ : ↥(orthDerived Q) →* LinearMap.GeneralLinearGroup K V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom.comp
      (orthDerived Q).subtype
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.injective.comp
      (orthDerived Q).subtype_injective
  have hJ₀ : ⁅A.subgroupOf (orthDerived Q), A.subgroupOf (orthDerived Q)⁆ =
      A.subgroupOf (orthDerived Q) := by
    apply Subgroup.map_injective (orthDerived Q).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAΩ, hAp]
  refine commutator_eq_bot_of_quadratic_lift_three hJq hJT hT
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
    (QuotientGroup.mk'_surjective _) ker_mk'_le_center ρ hρ
    (P := P.subgroupOf (orthDerived Q)) hJ₀ hJ.symm
    (fun u hu => Subgroup.mem_subgroupOf.2 (hPA (Subgroup.mem_subgroupOf.1 hu)))
    (hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPΩ).symm) ?_ ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΩ).toEquiv]
    exact hP9
  · intro u hu hc
    apply Subtype.ext
    exact hPZ _ (Subgroup.mem_subgroupOf.1 hu) fun j hj =>
      congrArg Subtype.val (hc ⟨j, hAΩ hj⟩ (Subgroup.mem_subgroupOf.2 hj))
  · intro u hu hc hu3
    exact hPq _ (Subgroup.mem_subgroupOf.1 hu)
      (fun w hw => congrArg Subtype.val (hc ⟨w, hPΩ hw⟩ (Subgroup.mem_subgroupOf.2 hw)))
      (by rw [← map_pow, hu3, map_one])

end Core

section WittOne

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem coe_eq_eichler_of_fixedBlockEquiv (hx : OddOrderIsometry Q p x)
    {u w : fixedSpace x} (hu : (Q.comp (fixedSpace x).subtype) u = 0)
    (huw : polar (Q.comp (fixedSpace x).subtype) u w = 0) (g : ↥(supportedBlock Q x (X - 1)))
    (hg : ((fixedBlockEquiv hx g :
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[K] fixedSpace x) = eichler (Q.comp (fixedSpace x).subtype) u w) :
    (g : V ≃ₗ[K] V) = eichler Q (u : V) (w : V) := by
  obtain ⟨hc, horth⟩ := hx.fixed_others
  have hu' : Q (u : V) = 0 := hu
  have huw' : polar Q (u : V) (w : V) = 0 := huw
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨a, ha, r, hr, rfl⟩ := CFSG.RankThree.PartOne.KCOrthogonal.exists_add_of_isCompl hc v
  rw [map_add, map_add]
  congr 1
  · have h1 : ((eichler (Q.comp (fixedSpace x).subtype) u w ⟨a, ha⟩ : fixedSpace x) : V) =
        (g : V ≃ₗ[K] V) a := by
      have := coe_fixedBlockEquiv hx g ⟨a, ha⟩
      rw [hg] at this
      exact this
    rw [← h1, eichler_apply hu huw, eichler_apply hu' huw']
    rfl
  · have hgr : (g : V ≃ₗ[K] V) r = r := (mem_supportedBlock.mp g.2).2 r hr
    rw [hgr, eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact horth _ u.2 r hr)
      (by rw [polar_comm]; exact horth _ w.2 r hr)]

theorem commutator_eq_bot_of_fixedFactor_wittOne [CharP K 3]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x)
    (hS2 : ¬ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    {J T₀ : Subgroup (ProjOrthDerived Q)}
    (hJ : J = (F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJT : J ≤ Subgroup.normalizer (T₀ : Set (ProjOrthDerived Q))) (hT : IsPGroup 2 T₀) :
    ⁅T₀, J⁆ = ⊥ := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := fun h0 => one_ne_zero (by linear_combination h3K - h0 : (1 : K) = 0)
  have h21 : (2 : K) ≠ 1 := fun h => one_ne_zero (by linear_combination h : (1 : K) = 0)
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hFB : F ≤ supportedBlock Q x (X - 1) :=
    hFle.trans supportedFixedDerived_le_supportedBlock
  have hCB : ∀ g : ↥(supportedBlock Q x (X - 1)), (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      g ∈ commutator ↥(supportedBlock Q x (X - 1)) := by
    intro g hg
    rw [← hSFD] at hg
    obtain ⟨g', hg', hgg⟩ := hg
    rwa [show g = g' from Subtype.ext hgg.symm]
  have hmapC : (commutator ↥(supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := (fixedBlockEquiv hx).toMonoidHom)).2
        (fixedBlockEquiv hx).surjective]
  obtain ⟨L, hL⟩ : ∃ L : Subgroup
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)),
      L = (F.subgroupOf (supportedBlock Q x (X - 1))).map (fixedBlockEquiv hx).toMonoidHom :=
    ⟨_, rfl⟩
  have hLle : L ≤
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rw [hL]
    rintro _ ⟨g, hg, rfl⟩
    rw [← hmapC]
    exact ⟨g, hCB g (hFle hg), rfl⟩
  have hLn : (L.subgroupOf (commutator
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLle, hL]
    rintro _ k ⟨g, hg, rfl⟩ hk
    rw [← hmapC] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    refine ⟨c * g * c⁻¹, ?_, by simp⟩
    have hcS : (c : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := hSFD ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hFle).1 hFn _ _ hg hcS
  have hLq : CFSG.IsQuasisimple ↥L := by
    rw [hL]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hFB).symm.trans
      ((F.subgroupOf (supportedBlock Q x (X - 1))).equivMapOfInjective
        (fixedBlockEquiv hx).toMonoidHom (fixedBlockEquiv hx).injective)) hFq
  have hs : ¬ (finrank K (fixedSpace x) = 4 ∧ ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0) := fun h => hS2 h.2
  have hC := orthogonal_regular_space_derived_quasisimple _ hQW hlist.1 hlist.2 hs
  have hLC : L =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC hLn with h | h
    · exact le_antisymm hLle (Subgroup.subgroupOf_eq_top.1 h)
    · exfalso
      refine not_isQuasisimple_of_comm'' (fun a b => ?_) hLq
      have ha : (⟨a.1, hLle a.2⟩ : ↥(commutator
          ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))) ∈
          L.subgroupOf (commutator
            ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :=
        Subgroup.mem_subgroupOf.2 a.2
      have hc := Subgroup.mem_center_iff.1 (h ha) ⟨b.1, hLle b.2⟩
      exact Subtype.ext (congrArg Subtype.val hc).symm
  have hEF : ∀ (P' : HypPair (Q.comp (fixedSpace x).subtype)) (w : fixedSpace x), w ∈ P'.perp →
      eichler Q (P'.e : V) (w : V) ∈ F := by
    intro P' w hw
    have hmem := CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup h2 h21 P' hw
    have hz : (⟨eichler _ P'.e w, eichler_mem_orthogonalGroup _ _ _⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) ∈
          commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
      mem_commutator_of_coe_mem hmem
    rw [← hLC, hL] at hz
    obtain ⟨g, hg, hgz⟩ := hz
    have hgF : (g : V ≃ₗ[K] V) ∈ F := Subgroup.mem_subgroupOf.1 hg
    rwa [coe_eq_eichler_of_fixedBlockEquiv hx P'.Q_e (HypPair.mem_perp.1 hw).1 g
      (congrArg Subtype.val hgz)] at hgF
  obtain ⟨e, -, he0, he⟩ := CFSG.LieType.SeitzGeneration.exists_singular_of_three_le_odd
    (Q := Q.comp (fixedSpace x).subtype) h2 (S := ⊤) (by rw [finrank_top]; exact hlist.1)
  obtain ⟨P, -⟩ := exists_hypPair hQW he he0
  have haniso : ∀ u ∈ P.perp, u ≠ 0 → (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro u hu hu0 hQu
    apply hS2
    obtain ⟨heu, hfu⟩ := HypPair.mem_perp.1 hu
    have hli : LinearIndependent K ![P.e, u] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (fun z => polar (Q.comp (fixedSpace x).subtype) z P.f) hst
      simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, polar_zero_left] at h1
      rw [polar_comm _ u, hfu, mul_zero, add_zero, mul_one] at h1
      subst h1
      rw [zero_smul, zero_add] at hst
      exact ⟨rfl, (smul_eq_zero.1 hst).resolve_right hu0⟩
    refine ⟨Submodule.span K (Set.range ![P.e, u]), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro y hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        QuadraticMap.map_add, QuadraticMap.map_smul, P.Q_e, hQu, polar_smul_left_eq,
        polar_smul_right_eq, heu, smul_zero, mul_zero, add_zero]
  obtain ⟨v₁, hv₁, hQv₁⟩ := CFSG.RankThree.Classical.exists_mem_perp_map_ne_zero hQW hlist.1 P
  have hv₁0 : v₁ ≠ 0 := fun h => hQv₁ (by rw [h, QuadraticMap.map_zero])
  have hφinj : Function.Injective (ZMod.castHom (dvd_refl 3) K) := ZMod.castHom_injective K
  have hφ0 : ∀ c : ZMod 3, c ≠ 0 → ZMod.castHom (dvd_refl 3) K c ≠ 0 := fun c hc h =>
    hc (hφinj (by rw [h, map_zero]))
  obtain ⟨v₂, hv₂, hgood⟩ : ∃ v₂ ∈ P.perp, ∀ c₁ c₂ : ZMod 3, (c₁, c₂) ≠ 0 →
      ZMod.castHom (dvd_refl 3) K c₁ • v₁ + ZMod.castHom (dvd_refl 3) K c₂ • v₂ ≠ 0 := by
    by_cases hK3 : Nat.card K = 3
    ·
      have h4 : 4 ≤ finrank K (fixedSpace x) := by
        have := hlist.1
        by_contra hlt
        exact hlist.2 (Or.inl ⟨by omega, hK3⟩)
      obtain ⟨v₂, hv₂, hnot⟩ : ∃ v₂ ∈ P.perp, v₂ ∉ K ∙ v₁ := by
        by_contra hcon
        push Not at hcon
        have h1 : finrank K P.perp ≤ 1 := (Submodule.finrank_mono hcon).trans
          (finrank_span_singleton hv₁0).le
        have hsup : (⊤ : Submodule K (fixedSpace x)) ≤
            Submodule.span K (Set.range ![P.e, P.f]) ⊔ P.perp := by
          intro z _
          rw [P.eq_add_proj z]
          exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))))
            (Submodule.mem_sup_right (P.proj_mem_perp z))
        have h2' := Submodule.finrank_mono hsup
        rw [finrank_top] at h2'
        have h3' := Submodule.finrank_add_le_finrank_add_finrank
          (Submodule.span K (Set.range ![P.e, P.f])) P.perp
        have h4' := finrank_range_le_card (R := K) ![P.e, P.f]
        rw [Fintype.card_fin, Set.finrank] at h4'
        omega
      refine ⟨v₂, hv₂, fun c₁ c₂ hc h0 => ?_⟩
      by_cases hc2 : c₂ = 0
      · subst hc2
        have hc1 : c₁ ≠ 0 := fun h => hc (by rw [h]; rfl)
        rw [map_zero, zero_smul, add_zero] at h0
        exact (smul_eq_zero.1 h0).elim (hφ0 c₁ hc1) hv₁0
      · apply hnot
        rw [Submodule.mem_span_singleton]
        refine ⟨-(ZMod.castHom (dvd_refl 3) K c₂)⁻¹ * ZMod.castHom (dvd_refl 3) K c₁, ?_⟩
        have h1 : ZMod.castHom (dvd_refl 3) K c₂ • v₂ =
            -(ZMod.castHom (dvd_refl 3) K c₁ • v₁) := eq_neg_of_add_eq_zero_right h0
        rw [mul_smul, neg_smul, ← smul_neg, ← h1, smul_smul, inv_mul_cancel₀ (hφ0 c₂ hc2),
          one_smul]
    ·
      obtain ⟨s, hs⟩ : ∃ s : K, ∀ c : ZMod 3, ZMod.castHom (dvd_refl 3) K c ≠ s := by
        by_contra hcon
        push Not at hcon
        have h1 := Nat.card_le_card_of_surjective _ hcon
        rw [Nat.card_zmod] at h1
        haveI := Fintype.ofFinite K
        obtain ⟨n, -, hn⟩ := FiniteField.card K 3
        rw [Nat.card_eq_fintype_card, hn] at h1 hK3
        have hn1 : (n : ℕ) = 1 := by
          have := n.pos
          rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
          · omega
          · have : 3 ^ 2 ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h
            omega
        exact hK3 (by rw [hn1, pow_one])
      refine ⟨s • v₁, P.perp.smul_mem s hv₁, fun c₁ c₂ hc h0 => ?_⟩
      rw [smul_smul, ← add_smul] at h0
      rcases smul_eq_zero.1 h0 with h | h
      · by_cases hc2 : c₂ = 0
        · subst hc2
          rw [map_zero, zero_mul, add_zero] at h
          exact hc (by rw [hφinj (h.trans (map_zero _).symm)]; rfl)
        · apply hs (-c₁ / c₂)
          rw [map_div₀, div_eq_iff (hφ0 c₂ hc2), show ZMod.castHom (dvd_refl 3) K (-c₁) =
            -ZMod.castHom (dvd_refl 3) K c₁ from map_neg _ _]
          linear_combination -h
      · exact hv₁0 h
  obtain ⟨Tt, hTt2, hTtT, hJ₀Tt⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_two_subgroup_map_eq_of_cover
      (QuotientGroup.mk'_surjective ((scalars K V).subgroupOf (orthDerived Q))) ker_mk'_le_center
      hT (S := F.subgroupOf (orthDerived Q)) (fun g hg u hu => by
        have hgJ : QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) g ∈ J := by
          rw [hJ]
          exact ⟨g, hg, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hJT hgJ) u).1 hu)
  have hRn : ∀ g ∈ F, g ∈ Subgroup.normalizer
      ((Tt.map (orthDerived Q).subtype : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) := by
    intro g hg
    have hN := hJ₀Tt (Subgroup.mem_subgroupOf.2 hg : (⟨g, hFΩ hg⟩ : ↥(orthDerived Q)) ∈
      F.subgroupOf (orthDerived Q))
    exact Subgroup.le_normalizer_map (orthDerived Q).subtype ⟨⟨g, hFΩ hg⟩, hN, rfl⟩
  have hcomm := eichler_commute_of_isPGroup_two (Q := Q) (e₀ := (P.e : V)) (w₁ := (v₁ : V))
    (w₂ := (v₂ : V)) P.Q_e ⟨(P.f : V), by
      change polar (Q.comp (fixedSpace x).subtype) P.f P.e ≠ 0
      rw [P.polar_fe]
      exact one_ne_zero⟩ (HypPair.mem_perp.1 hv₁).1 (HypPair.mem_perp.1 hv₂).1
    (fun c₁ c₂ hc => haniso _ (P.perp.add_mem (P.perp.smul_mem _ hv₁) (P.perp.smul_mem _ hv₂))
      (hgood c₁ c₂ hc))
    (hTt2.map _) (fun c₁ c₂ => hRn _ (hEF P _ (P.perp.add_mem (P.perp.smul_mem _ hv₁)
      (P.perp.smul_mem _ hv₂))))
  have hyF : eichler Q (P.e : V) (v₁ : V) ∈ F := hEF P v₁ hv₁
  let P' : HypPair (Q.comp (fixedSpace x).subtype) := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  have hv₁' : v₁ ∈ P'.perp :=
    HypPair.mem_perp.2 ⟨(HypPair.mem_perp.1 hv₁).2, (HypPair.mem_perp.1 hv₁).1⟩
  have hy'F : eichler Q (P.f : V) (v₁ : V) ∈ F := hEF P' v₁ hv₁'
  set π := QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hπ
  set Y : ↥(orthDerived Q) := ⟨eichler Q (P.e : V) (v₁ : V), hFΩ hyF⟩ with hY
  set Y' : ↥(orthDerived Q) := ⟨eichler Q (P.f : V) (v₁ : V), hFΩ hy'F⟩ with hY'
  have hYJ : π Y ∈ J := by
    rw [hJ]
    exact ⟨Y, Subgroup.mem_subgroupOf.2 hyF, rfl⟩
  have hY'J : π Y' ∈ J := by
    rw [hJ]
    exact ⟨Y', Subgroup.mem_subgroupOf.2 hy'F, rfl⟩
  have hYC : π Y ∈ Subgroup.centralizer (T₀ : Set (ProjOrthDerived Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [← hTtT] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm _ ⟨t', ht', rfl⟩).symm
  let PV : HypPair Q := ⟨(P.e : V), (P.f : V), P.Q_e, P.Q_f, P.polar_ef⟩
  have hwV : (v₁ : V) ∈ PV.perp :=
    HypPair.mem_perp.2 ⟨(HypPair.mem_perp.1 hv₁).1, (HypPair.mem_perp.1 hv₁).2⟩
  obtain ⟨hne1, hne2⟩ := eichler_mul_apply_ne h2 PV hwV hQv₁
  have he0V : (P.e : V) ≠ 0 := fun h => by
    have := P.polar_ef
    rw [show P.e = 0 from Subtype.ext h, polar_zero_left] at this
    exact zero_ne_one this
  haveI : Nontrivial V := ⟨⟨_, _, he0V⟩⟩
  have hnc : π Y' * π Y ≠ π Y * π Y' := by
    intro h
    obtain ⟨z, hzdef⟩ : ∃ z : ↥(orthDerived Q), z = (Y * Y')⁻¹ * (Y' * Y) := ⟨_, rfl⟩
    have hz : z ∈ (scalars K V).subgroupOf (orthDerived Q) := by
      have h3 : π z = 1 := by
        rw [hzdef, map_mul, map_inv, map_mul, map_mul, h, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff z).1 h3
    obtain ⟨c, hc2, hc⟩ := exists_sq_eq_one_of_mem_scalarKernel'' hQ hz
    have hprod : Y' * Y = (Y * Y') * z := by
      rw [hzdef]
      group
    have h1 : ((Y' : V ≃ₗ[K] V) * Y) (P.e : V) =
        c • (((Y : V ≃ₗ[K] V) * Y') (P.e : V)) := by
      have h3 := congrArg (fun g : ↥(orthDerived Q) => (g : V ≃ₗ[K] V) (P.e : V)) hprod
      simp only [Subgroup.coe_mul] at h3
      rw [h3, show ((Y : V ≃ₗ[K] V) * Y' * z) (P.e : V) =
        ((Y : V ≃ₗ[K] V) * Y') ((z : V ≃ₗ[K] V) (P.e : V)) from rfl, hc, map_smul]
    rcases sq_eq_one_iff.1 hc2 with hc1 | hc1
    · rw [hc1, one_smul] at h1
      exact hne1 h1.symm
    · rw [hc1, neg_one_smul] at h1
      exact hne2 (by rw [h1, neg_neg])
  exact commutator_eq_bot_of_noncentral_mem_centralizer hJq hJT hYJ ⟨π Y', hY'J, hnc⟩ hYC

end WittOne

section Main

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem not_isQuasisimple_bot'' {G : Type*} [Group G] :
    ¬ CFSG.IsQuasisimple ↥(⊥ : Subgroup G) := by
  rintro ⟨-, -, a, b, hab⟩
  apply hab
  haveI : Subsingleton (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) :=
    Quotient.instSubsingletonQuotient _
  exact Subsingleton.elim _ _

theorem s2019FixCentralizes_conj_projOrth_three {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (hring : ringChar K = 3) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (b : ProjOrthDerived Q) (hb : b ^ p = 1) :
    S2019FixCentralizes p (MulAut.conj b) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 3 := hring ▸ ringChar.charP K
  have hpℓ : p ≠ ringChar K := by rw [hring]; exact hp3
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  intro L hL T₀ hT₀ hLT
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hle := perfectInLayer_conj_of_equiv hQ hT hp hp2 hpℓ (MulEquiv.refl _) b hb L hL.1 hperf
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hL hle
  have hcomp' := hcomp
  rw [fixSubgroup_conj_eq_centralizer] at hcomp'
  obtain ⟨x, hx, hcases⟩ := exists_lift_component_cases hp hp2 hQ hT hpℓ b hb L hcomp'
  rcases hcases with ⟨h, hh, hne1, hqs, hLh⟩ | ⟨hlist, F, hFq, hFle, hFn, hLF⟩
  ·
    have hΩ : specialBlock Q x h ≤ orthDerived Q :=
      specialBlock_le_orthDerived_of_perfect hqs.1
        ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
      by_contra hlt
      have hpos := hx.primaryMultiplicity_pos hh
      have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
      rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh h1] at hqs
      exact not_isQuasisimple_bot'' hqs
    have hB : OrthBlockThree (specialBlock Q x h) := by
      by_cases hself : h = reciprocalPolynomial h
      · exact orthBlockThree_selfDual hx hp hp2 hh hne1 hself hf hK hm
      · exact orthBlockThree_paired hx hp hp2 hh hne1 hself hm
    exact commutator_eq_bot_of_orthBlockThree hΩ (Subgroup.isPerfect_iff.mp hqs.1) hB hLh
      hcomp.2.2 hLT hT₀
  ·
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    by_cases hS2 : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
        ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0
    · exact commutator_eq_bot_of_orthBlockThree hFΩ (Subgroup.isPerfect_iff.mp hFq.1)
        (orthBlockThree_of_fixedFactor hx hlist hS2 hFq hFle hFn) hLF hcomp.2.2 hLT hT₀
    · exact commutator_eq_bot_of_fixedFactor_wittOne hQ hx hlist hS2 hFq hFle hFn hLF hcomp.2.2
        hLT hT₀

theorem s2019OrthInner_three : S2019OrthInner (· = 3) := by
  intro p q hp hp2 hq hq2 hqp hq3 t ht G _ n f hG a ha
  change q = 3 at hq3
  subst hq3
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hcard, hring, ⟨e⟩⟩ := exists_projOrth_model_card ht hG
  haveI : Finite G := by
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
    exact Finite.of_equiv _ e.toEquiv.symm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hcard, h0, pow_zero] at h1
      omega
    · exact h0
  refine s2019FixCentralizes_of_congr hp e (MulAut.conj a) ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  exact s2019FixCentralizes_conj_projOrth_three hf hcard hring hQ hT hp hp2 hqp.symm (e a)
    (by rw [← map_pow, ha, map_one])

theorem s2019FactClassicalOn_orthogonal_of_D4Outer (hD4 : S2019OrthD4Outer) :
    S2019FactClassicalOn .orthogonal :=
  s2019FactClassicalOn_orthogonal_of_three s2019OrthInner_three hD4 s2019SympInner_three

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019

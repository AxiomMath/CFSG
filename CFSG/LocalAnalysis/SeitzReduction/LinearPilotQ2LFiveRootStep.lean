module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootNorm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRootEmb
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallestAut
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFldData
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore HasBLift)

theorem specialLinear_map_transvection {m : ℕ} {K F : Type*} [Field K] [Field F] (ι : K →+* F)
    {i j : Fin m} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (ι c) := by
  refine Subtype.ext ?_
  change (1 + Matrix.single i j c).map ι = 1 + Matrix.single i j (ι c)
  rw [Matrix.map_add ι (map_add ι), Matrix.map_one ι (map_zero ι) (map_one ι), Matrix.map_single]

theorem fixingAutDichotomy_of_mulEquiv {Y : Type*} [Group Y] {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ} (hm : 3 ≤ m) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (ψ : Y ≃* LinearFlag.projectiveSL m F) {D : Subgroup Y}
    (hD : ∀ (i j : Fin m) (hij : i ≠ j) (c : F), σ c = c →
      ψ.symm (LinearFlag.proj m F (SpecialLinearGroup.transvection hij c)) ∈ D)
    {τ : MulAut Y} (hτ : ∀ y, ψ (τ y) = LinearFlag.fieldAut m F σ (ψ y)) :
    FixingAutDichotomy D τ := by
  intro α hα
  set β : MulAut (LinearFlag.projectiveSL m F) := (ψ.symm.trans α).trans ψ with hβ
  have hβfix : ∀ (i j : Fin m) (hij : i ≠ j), ∀ c, σ c = c →
      β (LinearFlag.proj m F (SpecialLinearGroup.transvection hij c)) =
        LinearFlag.proj m F (SpecialLinearGroup.transvection hij c) := by
    intro i j hij c hc
    rw [hβ, MulEquiv.trans_apply, MulEquiv.trans_apply, hα _ (hD i j hij c hc),
      MulEquiv.apply_symm_apply]
  rcases E6Pilot.eq_one_or_eq_fieldAut_of_forall_apply_transvection hm hσ hβfix with h | h
  · left
    ext y
    have h1 : β (ψ y) = ψ y := by rw [h]; rfl
    rw [hβ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact ψ.injective h1
  · right
    ext y
    have h1 : β (ψ y) = LinearFlag.fieldAut m F σ (ψ y) := by rw [h]
    rw [hβ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, ← hτ] at h1
    exact ψ.injective h1

section Root

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem rootSL2_le_centralizer_of_field_five
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 5 K)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 5} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 5 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1) (htX : t ∈ centralizer (modelToG e X₀ : Set G))
    (hfk : LinearTwoFieldKindAtRoot e t a b X₀ htX) :
    modelToG e (rootSL2 (K := K) a b) ≤
      centralizer (centralizerPerfectCore (modelToG e X₀) : Set G) := by
  obtain ⟨hZ, Kc, hKcomp, hDK, hsN, hτ, hmodel⟩ := hfk
  obtain ⟨hcore, hB, q, hqs, -, -, hqdvd, -, -⟩ := neighbourCore_field_linear_two
    (X := modelToG e X₀) (D := modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5)))) hset hK
    e le_rfl htC ht hab hX₀ hX₀c rfl htX rfl hKcomp hDK hsN hτ hmodel
  obtain ⟨F, _, _, _, hF4, ι, σ, hσ1, hσσ, hfix, eN, ψ, hψD, hψτ⟩ :=
    exists_mulEquiv_fieldKind_two hset hK e le_rfl htC ht hab hX₀ hX₀c htX hZ hDK hsN hτ hmodel
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hNab : Disjoint ({a, b}ᶜ : Finset (Fin 5)) ({a, b} : Finset (Fin 5)) :=
    disjoint_compl_left
  have hDC : modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5))) ≤
      centralizer (modelToG e X₀ : Set G) :=
    modelToG_le_centralizer e ((blockSL_le_centralizer_blockSL_of_disjoint hNab).trans
      (centralizer_le hX₀))
  have hdich : FixingAutDichotomy
      ((((modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5)))).subgroupOf
        (centralizer (modelToG e X₀ : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))))).subgroupOf
            (perfectCore (⊤ : Subgroup (centralizer (modelToG e X₀ : Set G) ⧸
              oddCore (centralizer (modelToG e X₀ : Set G))))))
      (neighbourCoreConj (modelToG e X₀)
        (Subgroup.centralizer_le_normalizer (modelToG e X₀ : Set G) htX)) := by
    refine fixingAutDichotomy_of_mulEquiv (by norm_num) hσ2
      ((MulEquiv.subgroupCongr hcore).trans ψ) ?_ ?_
    ·
      intro i j hij c hc
      obtain ⟨k, rfl⟩ := (hfix c).1 hc
      have hxD : ((e.symm (LinearFlag.proj 5 K (blockSLEquiv ({a, b}ᶜ : Finset (Fin 5)) eN
          (SpecialLinearGroup.transvection hij k))) : L) : G) ∈
          modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5))) :=
        symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv ({a, b}ᶜ : Finset (Fin 5)) eN
          (SpecialLinearGroup.transvection hij k)).2)
      have hx := hDC hxD
      have hk : QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨_, hx⟩ ∈ Kc :=
        hDK (Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hxD))
      have h1 : ψ ⟨_, hk⟩ =
          LinearFlag.proj (5 - 2) F (SpecialLinearGroup.transvection hij (ι k)) :=
        (hψD _ hx hk).trans (by rw [specialLinear_map_transvection])
      have h2 : ψ.symm (LinearFlag.proj (5 - 2) F (SpecialLinearGroup.transvection hij (ι k))) =
          ⟨_, hk⟩ := by
        rw [MulEquiv.symm_apply_eq]
        exact h1.symm
      rw [mem_subgroupOf, MulEquiv.symm_trans_apply, h2]
      exact Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hxD)
    ·
      intro y
      have hy : (neighbourCoreConj (modelToG e X₀)
          (Subgroup.centralizer_le_normalizer (modelToG e X₀ : Set G) htX) y :
            centralizer (modelToG e X₀ : Set G) ⧸ oddCore (centralizer (modelToG e X₀ : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩ *
            (y : centralizer (modelToG e X₀ : Set G) ⧸
              oddCore (centralizer (modelToG e X₀ : Set G))) *
            (QuotientGroup.mk' (oddCore (centralizer (modelToG e X₀ : Set G))) ⟨t, htX⟩)⁻¹ := by
        obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective
          (y : centralizer (modelToG e X₀ : Set G) ⧸ oddCore (centralizer (modelToG e X₀ : Set G)))
        rw [coe_neighbourCoreConj_apply, ← hz, neighbourQuotConj_mk]
        have e1 : neighbourCentralizerConj (modelToG e X₀)
            (Subgroup.centralizer_le_normalizer (modelToG e X₀ : Set G) htX) z =
              ⟨t, htX⟩ * z * ⟨t, htX⟩⁻¹ := by
          apply Subtype.ext
          rw [coe_neighbourCentralizerConj_apply]
          rfl
        rw [e1]
        rfl
      have hy' : (⟨_, hcore.le (neighbourCoreConj (modelToG e X₀)
          (Subgroup.centralizer_le_normalizer (modelToG e X₀ : Set G) htX) y).2⟩ : Kc) =
          Kc.normalizerMonoidHom ⟨_, hsN⟩ ⟨_, hcore.le y.2⟩ := by
        apply Subtype.ext
        rw [F4Pilot.coe_normalizerMonoidHom_mk_apply]
        exact hy
      change ψ ⟨_, hcore.le (neighbourCoreConj (modelToG e X₀)
          (Subgroup.centralizer_le_normalizer (modelToG e X₀ : Set G) htX) y).2⟩ =
        LinearFlag.fieldAut (5 - 2) F σ (ψ ⟨_, hcore.le y.2⟩)
      rw [hy', hψτ]
  rcases rootSL2_le_centralizer_or_card_dvd_of_fixingAutDichotomy (X := modelToG e X₀)
      (D := modelToG e (blockSL (K := K) ({a, b}ᶜ : Finset (Fin 5)))) hset hK e le_rfl htC ht hab
      hX₀ hX₀c rfl htX rfl (forall_mem_oddCore_commute_of_perfectCore_eq hcore hB) hdich with
    ⟨g, hgL, hdvd⟩ | h
  · exfalso
    have hKc : Nat.card Kc = 20160 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hF4
    have hcardP : Nat.card (centralizerPerfectCore (modelToG e X₀)) =
        Nat.card q.ker * Nat.card Kc := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hqs).toEquiv, mul_comm]
    rw [card_eq_of_mulEquiv_projectiveSL_five hK e, hcardP, hKc] at hdvd
    have h3 : Nat.card q.ker ∣ 3 := by simpa using hqdvd
    have hk1 : Nat.card q.ker = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
      · exact h
      · rw [h] at hdvd
        norm_num at hdvd
    have hqinj : Function.Injective q := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact Subgroup.eq_bot_of_card_eq _ hk1
    let pe : centralizerPerfectCore (modelToG e X₀) ≃* LinearFlag.projectiveSL (5 - 2) F :=
      MulEquiv.ofBijective (ψ.toMonoidHom.comp q) ⟨ψ.injective.comp hqinj, ψ.surjective.comp hqs⟩
    let c : centralizerPerfectCore (modelToG e X₀) →* L :=
      ((MulAut.conj g).toMonoidHom.comp
        (centralizerPerfectCore (modelToG e X₀)).subtype).codRestrict L
        fun y => hgL (Subgroup.mem_map_of_mem _ y.2)
    have hcinj : Function.Injective c := by
      intro y y' hyy
      have h1 := congrArg Subtype.val hyy
      simp only [c, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Subgroup.coe_subtype] at h1
      exact Subtype.ext ((MulAut.conj g).injective h1)
    exact not_injective_projectiveSL_three_four_five_two hF4 hK
      (ρ := e.toMonoidHom.comp (c.comp pe.symm.toMonoidHom))
      (e.injective.comp (hcinj.comp pe.symm.injective))
  · exact h

theorem lFiveFieldRootStepInput_holds :
    LFiveFieldRootStepInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt a b hab X₀ hX₀ hX₀c htX hfk c hca hcb W₁ _ hW₁2 hW₁t
    htW₁ hLW
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hW₀E := wZero_le_centralizerPerfectCore_of_wOne hset hK e ht hKt hab hca hcb hX₀ hX₀c
    hW₁2 hW₁t htW₁ hLW
  have hJ := rootSL2_le_centralizer_of_field_five hset hK e htC ht hab hX₀ hX₀c htX hfk
  exact centralizer_le hW₀E (hJ (symm_mem_modelToG e (xab_mem_rootSL2 hab 1)))

end Root

end CFSG.SeitzReduction.LinearPilot

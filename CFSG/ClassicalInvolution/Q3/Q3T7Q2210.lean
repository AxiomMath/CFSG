module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25V01
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2209
public import CFSG.ClassicalInvolution.Asc77.AscC22P1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T7V
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7V
set_option linter.unusedSectionVars false
section Family
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}
open Classical in

theorem exists_sylow_family
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) (hz : IsUniqueInvolution K z)
    (s : Finset (Subgroup G)) (hs : ∀ M ∈ s, M ∈ twinSet Ω K) :
    ∃ R : Subgroup G → Subgroup G, (∀ M ∈ s, IsSylow2In (R M) M) ∧
      (∀ M ∈ s, ∀ M' ∈ s, M ≠ M' → Commutes (R M) (R M')) ∧
      IsPGroup 2 ↥(⨆ M ∈ s, R M) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ⊥, by simp, by simp, ?_⟩
    exact (isPGroup_two_bot (G := G)).to_le
      (iSup₂_le fun M hM => absurd hM (Finset.notMem_empty M))
  | insert M₀ s hM₀ ih =>
    obtain ⟨R, hRs, hRc, hRP⟩ := ih (fun M hM => hs M (Finset.mem_insert_of_mem hM))
    have hM₀K : M₀ ∈ twinSet Ω K := hs M₀ (Finset.mem_insert_self _ _)
    have hz₀ : IsUniqueInvolution M₀ z := isUniqueInvolution_of_mem_twinSet hz hM₀K
    have hPN : (⨆ M ∈ s, R M) ≤ Subgroup.normalizer (M₀ : Set G) := by
      refine iSup₂_le fun M hM => ?_
      have hMK : M ∈ twinSet Ω K := hs M (Finset.mem_insert_of_mem hM)
      have hne : M ≠ M₀ := fun e => hM₀ (by rw [← e]; exact hM)
      exact (hRs M hM).1.trans (hΩ.le_normalizer_of_twin hMK.1 hM₀K.1 hne
        (isUniqueInvolution_of_mem_twinSet hz hMK) hz₀)
    obtain ⟨R₀, hR₀, hP₀⟩ := exists_isPGroup_sup_sylow hRP hPN
    have hupd : ∀ M ∈ s, Function.update R M₀ R₀ M = R M := fun M hM =>
      Function.update_of_ne (fun e => hM₀ (by rw [← e]; exact hM)) _ _
    have hle : ∀ M ∈ s, R M ≤ (⨆ M ∈ s, R M) ⊔ R₀ := fun M hM =>
      le_sup_of_le_left (le_iSup₂ (f := fun M (_ : M ∈ s) => R M) M hM)
    refine ⟨Function.update R M₀ R₀, ?_, ?_, ?_⟩
    · intro M hM
      rcases Finset.mem_insert.mp hM with rfl | hMs
      · simpa using hR₀
      · rw [hupd M hMs]
        exact hRs M hMs
    ·
      have hcomm₀ : ∀ M ∈ s, Commutes (R M) R₀ := by
        intro M hM
        have hMK : M ∈ twinSet Ω K := hs M (Finset.mem_insert_of_mem hM)
        have hne : M ≠ M₀ := fun e => hM₀ (by rw [← e]; exact hM)
        exact hΩ.commutes_of_twin_of_isPGroup hMK.1 hM₀K.1 hne
          (isUniqueInvolution_of_mem_twinSet hz hMK) hz₀ (hRs M hM).1 hR₀.1
          (hP₀.to_le (sup_le (hle M hM) le_sup_right))
      intro M hM M' hM' hne
      rcases Finset.mem_insert.mp hM with rfl | hMs <;>
        rcases Finset.mem_insert.mp hM' with rfl | hMs'
      · exact absurd rfl hne
      · rw [Function.update_self, hupd M' hMs']
        exact (hcomm₀ M' hMs').symm
      · rw [Function.update_self, hupd M hMs]
        exact hcomm₀ M hMs
      · rw [hupd M hMs, hupd M' hMs']
        exact hRc M hMs M' hMs' hne
    · refine hP₀.to_le (iSup₂_le fun M hM => ?_)
      rcases Finset.mem_insert.mp hM with rfl | hMs
      · rw [Function.update_self]
        exact le_sup_right
      · rw [hupd M hMs]
        exact hle M hMs
end Family
section Wyl
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

@[expose] def Hyp22SettingWyl
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W

theorem exists_reps_of_family
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (S : Finset (Subgroup G)) (hKS : K ∈ S) (hS : ∀ M ∈ S, M ∈ twinSet Ω K) :
    ∃ W ∈ WSet Ω, ∃ ρ : Subgroup G → Rep Ω W, ∀ M ∈ S, (ρ M).K = M := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  obtain ⟨R, hRs, -, hRP⟩ := Q3T8.Asc77.T7V.exists_sylow_family hΩ h.hz S hS
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup (Q3T7.modU_toGen3 hΩ) hRP
  have hex : ∀ M ∈ S, ∃ ρ : Rep Ω W, ρ.K = M := fun M hM => by
    obtain ⟨ρ, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW (hS M hM).1
        (hRs M hM)
      (hWD (R M) (mem_RSet_of_isSylow2In (hS M hM).1 (hRs M hM))
        (le_iSup₂_of_le M hM le_rfl))
    exact ⟨ρ, hρK⟩
  have : Nonempty (Rep Ω W) := ⟨(hex K hKS).choose⟩
  choose! ρ hρ using hex
  exact ⟨W, hW, ρ, hρ⟩

theorem twins_card_le_four
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W)
    (S : Finset (Subgroup G)) (hKS : K ∈ S) (hS : ∀ M ∈ S, M ∈ twinSet Ω K) : S.card ≤ 4 := by
  classical
  obtain ⟨W, hW, ρ, hρ⟩ := Q3T8.Asc77.T7V.exists_reps_of_family h S hKS hS
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ K hKS⟩
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand h.stand hW
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨c.hΩ, h.stand.cls, c.hA⟩
  let g : Subgroup G → ↥(muGroup Ω W) := fun M => T7D.imgQ (ρ M)
  have hinj : Set.InjOn g (↑S : Set (Subgroup G)) := by
    intro M hM M' hM' e
    have := c.K_eq_of_img_eq (ρ M) (ρ M') (congrArg Subtype.val e)
    rwa [hρ M hM, hρ M' hM'] at this
  have hsub : (↑(S.image g) : Set ↥(muGroup Ω W)) ⊆
      Star3T.cent (muDelta Ω W) (g K) := by
    intro y hy
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    by_cases hMK : M = K
    · rw [hMK]
      exact Star3T.self_mem_cent (T7D.imgQ_mem _)
    · refine ⟨T7D.imgQ_mem _, (Subtype.ext (c.comm_of_omega (ρ K) (ρ M) ?_)).symm⟩
      rw [hρ K hKS, hρ M hM]
      exact Q3T8.Asc77.T7V.adj_of_twins h (hS K hKS) (hS M hM) hMK
  have hcard : S.card ≤ (Star3T.cent (muDelta Ω W) (g K)).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at this
  rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc' (g K) (T7D.imgQ_mem _) with h1 | h1 | ⟨h1, -⟩
      <;> omega

theorem exists_fourth_twin
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W) :
    ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ := by
  classical
  have hK : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem h.hz
  obtain ⟨W, hW, ρ, hρ⟩ := Q3T8.Asc77.T7V.exists_reps_of_family h ({K, K', K₃} : Finset (Subgroup
      G))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl
      · exact hK
      · exact h.hK'
      · exact h.hK₃)
  have hρ₁ : (ρ K).K = K := hρ K (by simp)
  have hρ₂ : (ρ K').K = K' := hρ K' (by simp)
  have hρ₃ : (ρ K₃).K = K₃ := hρ K₃ (by simp)
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ₁⟩
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand h.stand hW
  have hz' : IsUniqueInvolution K' z := h.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := h.hzK₃
  obtain ⟨ρ₄, h41, h42, h43, h4a, -, -, -⟩ := c.exists_fourth h.stand.cls hnc' (ρ K) (ρ K') (ρ K₃)
    (by rw [hρ₁, hρ₂]; exact Q3T8.Asc77.T7V.adj_of_twins h hK h.hK' h.hne)
    (by rw [hρ₁, hρ₃]; exact Q3T8.Asc77.T7V.adj_of_twins h hK h.hK₃ h.hK₃K)
    (by rw [hρ₂, hρ₃]; exact Q3T8.Asc77.T7V.adj_of_twins h h.hK' h.hK₃ h.hK₃K')
    (by rw [hρ₁]; exact h.hz) (by rw [hρ₂]; exact hz') (by rw [hρ₃]; exact hz₃)
  rw [hρ₁] at h41 h4a
  rw [hρ₂] at h42
  rw [hρ₃] at h43
  have hmem : ρ₄.K ∈ twinSet Ω K := by
    rw [← h.perp]
    exact Or.inr h4a
  exact ⟨ρ₄.K, hmem, h41, h42, h43⟩

theorem hyp22FourTwins_of_wyl
    (hR : Q3T8.Asc77.T7V.Hyp22SettingWyl) : Q3T8.Asc77.Hyp22FourTwins :=
    by
  classical
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs
  have hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W :=
    fun W hW ⟨ρ₀, hρ₀⟩ =>
      Q3T8.Asc77.T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀ (hR G Ω K K' K₃ z u₁ u₂ u₃ hs W hW)
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := Q3T8.Asc77.T7V.exists_fourth_twin hs hnc
  refine ⟨K₄, hK₄, h41, h42, h43, fun M hM => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hMK, hMK', hMK₃, hMK₄⟩ := hcon
  have hK : K ∈ twinSet Ω K := mem_twinSet_self hs.stand.mem hs.hz
  have hle := Q3T8.Asc77.T7V.twins_card_le_four hs hnc ({K, K', K₃, K₄, M} : Finset (Subgroup G))
      (by simp)
    (by
      intro N hN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl
      · exact hK
      · exact hs.hK'
      · exact hs.hK₃
      · exact hK₄
      · exact hM)
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have h5 : ({K, K', K₃, K₄, M} : Finset (Subgroup G)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hKK', hKK₃, hKK₄, hMK.symm]),
      Finset.card_insert_of_notMem (by simp [hK'K₃, hK'K₄, hMK'.symm]),
      Finset.card_insert_of_notMem (by simp [hK₃K₄, hMK₃.symm]),
      Finset.card_insert_of_notMem (by simp [hMK₄.symm]), Finset.card_singleton]
  omega
end Wyl
end T7V
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_conj_of_mem_dstarComp
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ J ∈ dstarComp Ω K, ∃ w : G, IsUniqueInvolution J w ∧
      ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have key : ∀ J : Subgroup G, Relation.ReflTransGen (dstarAdj Ω) K J →
      ∃ w : G, IsUniqueInvolution J w ∧
        ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨z, hz, 1, (genGroup Ω K (u₁ * u₂)).one_mem, by group⟩
    | @tail b c hpre hstep ih =>
      obtain ⟨wb, hwb, y, hy, hyz⟩ := ih
      have hbΩ : b ∈ Ω := (T3.mem_dstarComp_symm hK hpre).1
      obtain ⟨hcΩ, hor⟩ := hstep
      have hcb : c ∈ omegaStarNbr Ω b := by
        rcases hor with h | h
        · exact h
        · exact Q3T8.Asc77.T3.omegaStarNbr_symm (Q3T8.Asc77.l6_2) hΩ hcΩ hbΩ h
      have hM : conjSub y⁻¹ b ∈ twinSet Ω K :=
        conjSub_mem_twinSet hΩ.conjInvariant hz hbΩ hwb hyz
      have hMΩ : conjSub y⁻¹ b ∈ Ω := hM.1
      have hzM : IsUniqueInvolution (conjSub y⁻¹ b) z := isUniqueInvolution_of_mem_twinSet hz hM
      have hJ'' : conjSub y⁻¹ c ∈ omegaStarNbr Ω (conjSub y⁻¹ b) :=
        omegaStarNbr_conj hΩ.conjInvariant hcb y⁻¹
      have hJ''Ω : conjSub y⁻¹ c ∈ Ω := hΩ.conjInvariant y⁻¹ c hcΩ
      obtain ⟨w', hw'⟩ := hΩ.exists_uniqueInvolution hcΩ
      have hw'' : IsUniqueInvolution (conjSub y⁻¹ c) (y⁻¹ * w' * y⁻¹⁻¹) := hw'.conj y⁻¹
      refine ⟨w', hw', ?_⟩
      by_cases hJt : conjSub y⁻¹ c ∈ twinSet Ω K
      · have h1 := isUniqueInvolution_of_mem_twinSet hz hJt
        have h2 : z = y⁻¹ * w' * y⁻¹⁻¹ := h1.eq hw''
        exact ⟨y, hy, by rw [h2]; group⟩
      · obtain ⟨W₁, hW₁, R, hRD, T, hTD, hRM, hTJ⟩ :=
          Q3T8.Asc77.Thompson.exists_W_of_mem_omegaStarNbr (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hMΩ hJ''
        have hzW : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hMΩ hRD hRM hzM).2
        have hwW : y⁻¹ * w' * y⁻¹⁻¹ ∈ W₁ :=
          (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hJ''Ω hTD hTJ hw'').2
        obtain ⟨y'', hy'', hy''z⟩ := Q3T8.Asc77.C22G.exists_conj_of_far hs hW₁ hzW hJ''Ω hJt hw''
            hwW
        refine ⟨y * y'', (genGroup Ω K (u₁ * u₂)).mul_mem hy hy'', ?_⟩
        calc y * y'' * z * (y * y'')⁻¹ = y * (y'' * z * y''⁻¹) * y⁻¹ := by group
          _ = y * (y⁻¹ * w' * y⁻¹⁻¹) * y⁻¹ := by rw [hy''z]
          _ = w' := by group
  intro J hJ
  exact key J hJ

theorem le_genGroup_of_mem_dstarComp
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {J :
    Subgroup G}
    (hJ : J ∈ dstarComp Ω K) : J ≤ genGroup Ω K (u₁ * u₂) := by
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := (T3.mem_dstarComp_symm hK hJ).1
  obtain ⟨w, hw, y, hy, hyw⟩ := Q3T8.Asc77.C22G.exists_conj_of_mem_dstarComp hs J hJ
  exact le_genGroup_of_conj hs.stand.modU.conjInvariant hs.hz hJΩ hw hy hyw

theorem genGroup_eq_top_of_dstarConnected
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hconn : T3.DStarConnected Ω) : genGroup Ω K (u₁ * u₂) = ⊤ := by
  have hK : K ∈ Ω := hs.stand.mem
  rw [eq_top_iff]
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := hs.stand.gen
  rw [← hgen]
  exact iSup₂_le fun J hJ => Q3T8.Asc77.C22G.le_genGroup_of_mem_dstarComp hs (hconn K hK J hJ)
end Setting
section Statement

@[expose] def C22_dstarConn
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      T3.DStarConnected Ω

theorem c22_8Gen_of_dstarConn
    (h : Q3T8.Asc77.C22G.C22_dstarConn) : Q3T8.Asc77.C22_8Gen := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp
  exact Q3T8.Asc77.C22G.genGroup_eq_top_of_dstarConnected hyp.setting (h G Ω K K' K₃ z u₁ u₂ u₃ hyp)
end Statement
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layer_dstarConnected (hΩ : Q3T7M.HM Ω)
    (hAΩ : ∀ M ∈ Ω, AEmpty Ω M) {u : G} (hu2 : u * u = 1)
    (hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G)
    (hL : Q3T8.Asc77.LayerOrthType Ω u 6 (piSign 3 1)) :
    T3.DStarConnected (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) := by
  have hGS := (Q3T8.Asc77.S22.layer_section hΩ hAΩ hu2 hnc).1
  obtain ⟨t, n, hI, D, hcard, i, ht, hk⟩ := hL
  let hDo := LieSystemData.toOmegaLie D hGS.gen
  have hsurj := hDo.hom_surjective_of_gen hcard hGS.gen i
  let M : Q3T8.Asc77.Ih8Model (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω u)) (D.tag i)
      (D.rank i) (D.exp i) :=
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := hsurj
      cls := hDo.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => hDo.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => hDo.cls_conj hGS.hyp.conjInvariant i hR g }
  cases hπ : piSign 3 1
  · rw [hπ] at hI
    obtain ⟨rfl, rfl⟩ := (MuTab.isOrth_six_false t n).mp hI
    exact Q3T8.Asc77.C22G.ih8_dstarConnected_psu4 hGS.hyp (MuTab.pow_mod_four_of_piSign_false (by
        norm_num) hπ) M ht hk
  · rw [hπ] at hI
    obtain ⟨rfl, rfl⟩ := (MuTab.isOrth_six_true t n).mp hI
    exact Q3T8.Asc77.C22G.ih8_dstarConnected_psl4 hGS.hyp (MuTab.piSign_true_iff.mp hπ) M ht hk
end Layer
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem fourTwins_S
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ ∧
      ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄ := by
  classical
  have hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W :=
    fun W hW ⟨ρ₀, hρ₀⟩ => Q3T8.Asc77.T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀ (hμ W hW)
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := Q3T8.Asc77.T7V.exists_fourth_twin hs hnc
  refine ⟨K₄, hK₄, h41, h42, h43, fun M hM => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hMK, hMK', hMK₃, hMK₄⟩ := hcon
  have hK : K ∈ twinSet Ω K := mem_twinSet_self hs.stand.mem hs.hz
  have hle := Q3T8.Asc77.T7V.twins_card_le_four hs hnc ({K, K', K₃, K₄, M} : Finset (Subgroup G))
      (by simp)
    (by
      intro N hN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl
      · exact hK
      · exact hs.hK'
      · exact hs.hK₃
      · exact hK₄
      · exact hM)
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have h5 : ({K, K', K₃, K₄, M} : Finset (Subgroup G)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hKK', hKK₃, hKK₄, hMK.symm]),
      Finset.card_insert_of_notMem (by simp [hK'K₃, hK'K₄, hMK'.symm]),
      Finset.card_insert_of_notMem (by simp [hK₃K₄, hMK₃.symm]),
      Finset.card_insert_of_notMem (by simp [hMK₄.symm]), Finset.card_singleton]
  omega

theorem exists_sylow_quad_S
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet
    Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) :
    ∃ R₁ R₂ R₃ R₄ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧
      IsSylow2In R₄ K₄ ∧ u₁ ∈ R₁ ∧ u₂ ∈ R₂ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ ∧
      Commutes R₁ R₄ ∧ Commutes R₂ R₄ ∧ Commutes R₃ R₄ := by
  obtain ⟨R₁, R₂, R₃, h1, h2, h3, hu₁, hu₂, -, c12, c13, c23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃ : K₃ ∈ Ω := h.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz := h.hz
  have hz' := h.hzK'
  have hz₃ := h.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have nK : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have nK₃ : K₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK₃ hK₄Ω h43.symm hz₃ hz₄
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPN : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    sup_le (sup_le (h1.1.trans nK) (h2.1.trans nK')) (h3.1.trans nK₃)
  obtain ⟨R₄, h4, hQ⟩ := exists_isPGroup_sup_sylow hP hPN
  have hR₁Q : R₁ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hR₂Q : R₂ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans le_sup_left
  have hR₄Q : R₄ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right
  refine ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, ?_, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hK hK₄Ω h41.symm hz hz₄ h1.1 h4.1
      (hQ.to_le (sup_le hR₁Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK' hK₄Ω h42.symm hz' hz₄ h2.1 h4.1
      (hQ.to_le (sup_le hR₂Q hR₄Q))
  · exact hΩ.commutes_of_twin_of_isPGroup hK₃ hK₄Ω h43.symm hz₃ hz₄ h3.1 h4.1
      (hQ.to_le (sup_le hR₃Q hR₄Q))
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Twins
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_commuting_sylow_exactCore
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {c : G}
    {J J' : Subgroup G} {z : G} (hJ : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hJ' : J' ∈
        Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hne : J ≠ J') (hz : IsUniqueInvolution J z) (hz' : IsUniqueInvolution J' z) :
    ∃ V V' : Subgroup G, IsSylow2In V (Q3T8.Asc77.ExactLayer.exactCore c J) ∧ IsSylow2In V'
        (Q3T8.Asc77.ExactLayer.exactCore c J') ∧
      Commutes V V' := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G))
    (bot_le : ⊥ ≤ Q3T8.Asc77.ExactLayer.exactCore c J)
  have hVJ : V ≤ J := hV.1.trans (Q3T8.Asc77.ExactLayer.exactCore_le_left c J)
  have hVc : V ≤ Subgroup.centralizer ({c} : Set G) := hV.1.trans
      (Q3T8.Asc77.ExactLayer.exactCore_le_centralizer c J)
  have hJN : J ≤ Subgroup.normalizer (J' : Set G) :=
    hΩ.le_normalizer_of_twin hJ.1 hJ'.1 hne hz hz'
  have hVN : V ≤ Subgroup.normalizer (Q3T8.Asc77.ExactLayer.exactCore c J' : Set G) := by
    intro v hv
    rw [mem_normalizer_iff_conjSub_eq]
    have hvJ' : conjSub v J' = J' := mem_normalizer_iff_conjSub_eq.mp (hJN (hVJ hv))
    have hvc : v * c * v⁻¹ = c := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hVc hv)
      calc v * c * v⁻¹ = (c * v) * v⁻¹ := by rw [this]
        _ = c := by group
    have h2 := Q3T8.Asc77.ExactLayer.exactCore_conjSub v c J'
    rw [hvc, hvJ'] at h2
    exact h2.symm
  obtain ⟨V', hV', hfix⟩ := exists_sylow_normalized hV.2.1 hVN
  have hVV' : V ≤ Subgroup.normalizer (V' : Set G) := fun v hv =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix v hv)
  have hP2 : IsPGroup 2 ↥(V ⊔ V') := hV.2.1.to_sup_of_normal_right' hV'.2.1 hVV'
  exact ⟨V, V', hV, hV', hΩ.commutes_of_twin_of_isPGroup hJ.1 hJ'.1 hne hz hz' hVJ
    (hV'.1.trans (Q3T8.Asc77.ExactLayer.exactCore_le_left c J')) hP2⟩
end Twins
section Data
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem mem_tqMembers_of_twin
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ twinSet Ω K) (hJK : J ≠ K) (hJK' : J ≠ K') : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω
        (u₁ * u₂) := by
  have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet h.hz hJ
  have h1 : u₁ ∈ trivialOnQuot J :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot h.stand.modU h.stand.mem hJ.1 hJK.symm h.hz hzJ h.hu₁.1
  have h2 : u₂ ∈ trivialOnQuot J :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot h.stand.modU h.hK'.1 hJ.1 hJK'.symm h.hzK' hzJ h.hu₂.1
  exact ⟨hJ.1, (trivialOnQuot J).mul_mem h1 h2⟩
end Data
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T7V
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7V
set_option linter.unusedSectionVars false
section Wyl

theorem c22_4_of_wyl
    (hR : Q3T8.Asc77.T7V.Hyp22SettingWyl) : Q3T8.Asc77.C22_4 :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW => hR G Ω K K' K₃ z u₁ u₂ u₃ h.setting W hW

theorem hyp22Fuse_of_wyl
    (hR : Q3T8.Asc77.T7V.Hyp22SettingWyl) : Q3T8.Asc77.Hyp22Fuse :=
  Q3T8.Asc77.T7V.hyp22Fuse_of_c22_4 (Q3T8.Asc77.T7V.c22_4_of_wyl hR)

@[expose] def Hyp22SigmaNe
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      dComp Ω K ≠ dstarComp Ω K

theorem hyp22SettingWyl_of_sigmaNe
    (hσ : Q3T8.Asc77.T7V.Hyp22SigmaNe) :
    Q3T8.Asc77.T7V.Hyp22SettingWyl := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h W hW
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨h.stand.modU, h.stand.cls, h.stand.aEmpty⟩
  have hnc : ¬ DbarConnected Ω W :=
    Q3T8.Asc77.thompsonGraphAll G Ω hP h.stand.mem (hσ G Ω K K' K₃ z u₁ u₂ u₃ h) hW
  obtain ⟨h3, h4⟩ := h.not_mu_S3_S4 hW
  rcases Q3T8.Asc77.l7_10_proved G Ω hP W hW hnc with h1 | h1 | h1
  · exact absurd h1 h3
  · exact absurd h1 h4
  · exact h1

@[expose] def Hyp22SigmaNeX4
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ K₄ ∈ twinSet Ω K, K₄ ≠ K → K₄ ≠ K' → K₄ ≠ K₃ → dComp Ω K ≠ dstarComp Ω K

theorem hyp22SigmaNe_of_split
    (h3 : Q3T8.Asc77.Hyp22FourthTwin) (h4 :
    Q3T8.Asc77.T7V.Hyp22SigmaNeX4) :
    Q3T8.Asc77.T7V.Hyp22SigmaNe := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  obtain ⟨K₄, hK₄, h41, h42, h43⟩ := h3 G Ω K K' K₃ z u₁ u₂ u₃ h
  exact h4 G Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h41 h42 h43
end Wyl
end T7V
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Setting
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hyp22_of_setting
    {L L' M : Subgroup G} {x y w z' : G}
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) (hs : Q3T8.Asc77.Hyp22Setting Ω L L' M z' x y w) :
    Q3T8.Asc77.Hyp22 Ω L L' M z' x y w where
  std := ⟨hs.stand, h.std.disconnected, hs.hz, hs.hK', hs.hne, h.std.cex⟩
  perp := hs.perp
  hK₃ := hs.hK₃
  hK₃K := hs.hK₃K
  hK₃K' := hs.hK₃K'
  hu₁ := hs.hu₁
  hu₂ := hs.hu₂
  hu₃ := hs.hu₃
  hB := hs.hB

theorem exists_third_twin
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (L L' : Subgroup G) :
    ∃ M ∈ twinSet Ω K, M ≠ L ∧ M ≠ L' := by
  by_contra hcon
  have hmem : ∀ M ∈ twinSet Ω K, M = L ∨ M = L' := by
    intro M hM
    by_cases h : M = L
    · exact Or.inl h
    · by_cases h' : M = L'
      · exact Or.inr h'
      · exact absurd ⟨M, hM, h, h'⟩ hcon
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hs.stand.mem hs.hz
  have hKK' : K' ≠ K := hs.hne
  have hKK₃ : K₃ ≠ K := hs.hK₃K
  have hK'K₃ : K₃ ≠ K' := hs.hK₃K'
  rcases hmem K hKtw with h1 | h1 <;> rcases hmem K' hs.hK' with h2 | h2 <;>
    rcases hmem K₃ hs.hK₃ with h3 | h3 <;>
    first
    | exact hKK' (h2.trans h1.symm)
    | exact hKK₃ (h3.trans h1.symm)
    | exact hK'K₃ (h3.trans h2.symm)

theorem exists_sylow_third
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {L L' M : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hM : M ∈ twinSet Ω K) (hML : M ≠ L)
    (hML' : M ≠ L') {R₁ R₂ : Subgroup G} (h₁ : IsSylow2In R₁ L) (h₂ : IsSylow2In R₂ L')
    (c₁₂ : Commutes R₁ R₂) :
    ∃ R₃ : Subgroup G, IsSylow2In R₃ M ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hzL := isUniqueInvolution_of_mem_twinSet hz hL
  have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
  have hzM := isUniqueInvolution_of_mem_twinSet hz hM
  have nL : L ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hL.1 hM.1 (Ne.symm hML) hzL hzM
  have nL' : L' ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hL'.1 hM.1 (Ne.symm hML') hzL' hzM
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h₁.2.1.to_sup_of_normal_right' h₂.2.1 (T7A.le_normalizer_of_commutes c₁₂.symm)
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (M : Set G) :=
    sup_le (h₁.1.trans nL) (h₂.1.trans nL')
  obtain ⟨R₃, h₃, hQ⟩ := exists_isPGroup_sup_sylow hP12 hPN
  refine ⟨R₃, h₃, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hL.1 hM.1 (Ne.symm hML) hzL hzM h₁.1 h₃.1
      (hQ.to_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  · exact hΩ.commutes_of_twin_of_isPGroup hL'.1 hM.1 (Ne.symm hML') hzL' hzM h₂.1 h₃.1
      (hQ.to_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
end Setting
section Statement

@[expose] def C22_layerStar
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂), J ∈ dstarComp Ω K

theorem c22_dstarConn_of_layerStar
    (hE : Q3T7E.ThmEWithSylow3) (hLay :
    Q3T8.Asc77.C22G.C22_layerStar) :
    Q3T8.Asc77.C22G.C22_dstarConn := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp
  have hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ := hyp.setting
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hLt : conjSub c K ∈ twinSet Ω K := ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hLt)
  have hnon : ∀ L ∈ twinSet Ω K, ∀ J ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution J z' →
      z' ≠ z → Subgroup.centralizer ({z'} : Set G) ≤ sigmaStarNorm Ω K ∧
        Subgroup.centralizer ({z * z'} : Set G) ≤ sigmaStarNorm Ω K := by
    intro L hL J hJ z' hz' hzz
    exfalso
    have h1 : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hL, twinSet_eq_of_mem_twinSet hz hL] at h1
    obtain ⟨-, z₀, hz₀K, hz₀J⟩ := h1
    exact hzz ((hz₀J.eq hz').symm.trans (hz.eq hz₀K).symm)
  have htw : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          Subgroup.centralizer ({x * y} : Set G) ≤ sigmaStarNorm Ω K := by
    intro L hL L' hL' hne R₁ R₂ h₁ h₂ c₁₂ x hx y hy ox oy c hc
    obtain ⟨M, hM, hML, hML'⟩ := Q3T8.Asc77.C22G.exists_third_twin hs L L'
    obtain ⟨R₃, h₃, c₁₃, c₂₃⟩ := Q3T8.Asc77.C22G.exists_sylow_third hs hL hL' hM hML hML' h₁ h₂ c₁₂
    obtain ⟨u₃', hu₃', ou₃⟩ :=
      hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hM.1 h₃)
    have hzL := isUniqueInvolution_of_mem_twinSet hz hL
    have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
    have hzM := isUniqueInvolution_of_mem_twinSet hz hM
    have hL'L : L' ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet hz hL]; exact hL'
    have hML₀ : M ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet hz hL]; exact hM
    have hs' : Q3T8.Asc77.Hyp22Setting Ω L L' M z x y u₃' :=
      Q3T8.Asc77.S22.hyp22Setting_of_sylows (hst.of_mem hL.1) hzL hL'L hne
          (Q3T8.Asc77.T7S22.perp_of_twin hs hL) hML₀ hML
        hML' h₁ h₂ h₃ c₁₂ c₁₃ c₂₃ hx hy hu₃' ox oy ou₃
    have hxM : x ∈ trivialOnQuot M :=
      Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hL.1 hM.1 (Ne.symm hML) hzL hzM (h₁.1 hx)
    have hyM : y ∈ trivialOnQuot M :=
      Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hL'.1 hM.1 (Ne.symm hML') hzL' hzM (h₂.1 hy)
    have hMt : M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (x * y) := ⟨hM.1, Subgroup.mul_mem _ hxM hyM⟩
    have hJt : conjSub c M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (x * y) :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc hMt
    have hJL : conjSub c M ∈ dstarComp Ω L :=
      hLay G Ω L L' M z x y u₃' (Q3T8.Asc77.C22G.hyp22_of_setting hyp hs') _ hJt
    have hLK : dstarComp Ω L = dstarComp Ω K :=
      T7A.dstarComp_eq_of_mem hK (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hL)
    rw [hLK] at hJL
    have hKtw : conjSub c K ∈ twinSet Ω (conjSub c M) :=
      ⟨hΩ.conjInvariant c K hK, c * z * c⁻¹, hzM.conj c, hz.conj c⟩
    have hKJ : conjSub c K ∈ dstarComp Ω (conjSub c M) :=
      Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hJt.1 hKtw
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hJL.trans hKJ)
  have hstd : StdCent Ω K (sigmaStarNorm Ω K) z := ⟨hz_le, hnon, htw⟩
  have htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ sigmaStarNorm Ω K, conjSub h K = J := by
    intro J hJ
    obtain ⟨g, hg⟩ := hst.trans J (T3.mem_dstarComp_symm hK hJ).1
    exact ⟨g, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hg ▸ hJ), hg⟩
  have htop : sigmaStarNorm Ω K = ⊤ := Q3T8.Asc77.thmE_apply hE hst hz hs.hK' hs.hne hstd htrans
  refine T3.dstarConnected_of_pivot hK fun B hB => ?_
  obtain ⟨g, hg⟩ := hst.trans B hB
  have hgH : g ∈ sigmaStarNorm Ω K := htop ▸ Subgroup.mem_top g
  have h1 := (mem_sigmaStarNorm_iff.mp hgH K).mp Relation.ReflTransGen.refl
  rwa [hg] at h1
end Statement
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Basic
variable {G : Type} [Group G] [Finite G]

structure FrameData (Ω : Set (Subgroup G)) (K₃ K₄ : Subgroup G) (z c : G) (R R' : Subgroup G)
    (b b' y : G) : Prop where
  hR : IsSylow2In R K₃
  hR' : IsSylow2In R' K₄
  hRR' : Commutes R R'
  hRc : R ≤ Subgroup.centralizer ({c} : Set G)
  hR'c : R' ≤ Subgroup.centralizer ({c} : Set G)
  hbR : b ∈ R
  hb'R' : b' ∈ R'
  hb4 : orderOf b = 4
  hb'4 : orderOf b' = 4
  hbz : b * b = z
  hb'z : b' * b' = z
  hy : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c
  hyz : y * z * y⁻¹ = b * b' * c
  htz : b * b' * c ≠ z
  hzt : z * (b * b' * c) = (b * b' * c) * z
end Basic
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hAall_of_dstarComp
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hA : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K) :
    ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M, ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  intro M hM J hJ
  obtain ⟨g, hg⟩ := h.stand.trans M hM
  have e1 : conjSub g⁻¹ J ∈ omegaStarNbr Ω K := by
    have := omegaStarNbr_conj hΩ.conjInvariant hJ g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have e2 : conjSub g⁻¹ J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨e1.1, Or.inl e1⟩
  have e3 : conjSub g⁻¹ J ∈ twinSet Ω K := hA _ e2
  have e4 := twinSet_conj hΩ.conjInvariant e3 g
  rw [conjSub_conjSub_inv, hg] at e4
  obtain ⟨-, w, hw1, hw2⟩ := e4
  exact ⟨w, hw1, hw2⟩

theorem layer_zStar (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h1 : K₄ ≠ K) (h2 : K₄ ≠ K') (h3 : K₄ ≠ K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
  classical
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.stand.below
  have hK : K ∈ Ω := h.stand.mem
  have hu1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins h.stand.modU h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
      h.hu₂.1 h.hu₂.2).1
  have hu₂C' : (u₁ * u₂) * u₂ = u₂ * (u₁ * u₂) := by
    calc (u₁ * u₂) * u₂ = (u₂ * u₁) * u₂ := by rw [h.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := h.sq_12
  set u : G := u₁ * u₂ with hudef
  have hcpg : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    obtain ⟨x, -, y, -, hxy⟩ :=
      (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
    have hucen : u ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  obtain ⟨hS, hlt⟩ := Q3T8.Asc77.S22.layer_section hΩ h.stand.aEmpty hu2 hnc
  have hK₃Ω : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u := Q3T8.Asc77.S22.mem_tqMembers_of_twin h
      h.hK₃ h.hK₃K h.hK₃K'
  have hK₄Ω : K₄ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u := Q3T8.Asc77.S22.mem_tqMembers_of_twin h
      hK₄ h1 h2
  have hzK₃ : IsUniqueInvolution K₃ z := h.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet h.hz hK₄
  have hzc₃ : z ∈ Q3T8.Asc77.ExactLayer.exactCore u K₃ :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hK₃Ω hzK₃).mem
  have hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u :=
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₃Ω hzc₃
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  
  have hA3 : Q3T8.Asc77.T7H.exactImg Ω u K₃ ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω
      u) := Q3T8.Asc77.T7H.exactImg_mem hK₃Ω
  have hA4 : Q3T8.Asc77.T7H.exactImg Ω u K₄ ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω
      u) := Q3T8.Asc77.T7H.exactImg_mem hK₄Ω
  have hzA3 : IsUniqueInvolution (Q3T8.Asc77.T7H.exactImg Ω u K₃) (Q3T8.Asc77.T7H.toBar Ω u z hzY)
      :=
    Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₃Ω hzK₃ hzY
  have hzA4 : IsUniqueInvolution (Q3T8.Asc77.T7H.exactImg Ω u K₄) (Q3T8.Asc77.T7H.toBar Ω u z hzY)
      :=
    Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₄Ω hzK₄ hzY
  have hne : Q3T8.Asc77.T7H.exactImg Ω u K₃ ≠ Q3T8.Asc77.T7H.exactImg Ω u K₄ := by
    obtain ⟨V, V', hV, hV', hcomm⟩ :=
      Q3T8.Asc77.S22.exists_commuting_sylow_exactCore hΩ hK₃Ω hK₄Ω (Ne.symm h3) hzK₃ hzK₄
    refine Q3T8.Asc77.map_ne_of_commutes_sylow (N := N₀) hS.hyp hN₀odd
      (M₁ := (Q3T8.Asc77.ExactLayer.exactCore u K₃).subgroupOf Y) (M₂ :=
          (Q3T8.Asc77.ExactLayer.exactCore u K₄).subgroupOf Y)
      (V₁ := V.subgroupOf Y) (V₂ := V'.subgroupOf Y)
      ⟨_, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hK₃Ω,
          Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₃Ω, rfl⟩
      (hV.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₃Ω))
      (hV'.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₄Ω)) ?_
    intro x hx y hy
    exact Subtype.ext (hcomm x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hstar := Q3T8.Asc77.S22.hstar_layer hΩ hcpg hAall
  
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  have hYconj : ∀ g ∈ C, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    have := conj_mem_conjSub (n := g) hy
    rwa [Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hg] at this
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant
          hg))
  have hu₂C : u₂ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hu₂C'.symm
  let N₁ : Subgroup ↥C := (oddCoreOf Y).subgroupOf C
  have hN₁ : N₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hOnorm g g.2) n).mp hn
  have hle : N₀ ≤ N₁.comap (Subgroup.inclusion hYC) := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨n, hn, rfl⟩
  let ι : (↥Y ⧸ N₀) →* (↥C ⧸ N₁) := QuotientGroup.map N₀ N₁ (Subgroup.inclusion hYC) hle
  have hιmk : ∀ y : ↥Y, ι (QuotientGroup.mk' N₀ y) =
      QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) := fun y => rfl
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy1 : QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
      obtain ⟨hyY, hyo⟩ := mem_oddCoreOf_iff.mp hy1
      exact (QuotientGroup.eq_one_iff y).mpr hyo
  have hιmk' : ∀ y : ↥Y, ι (y : ↥Y ⧸ N₀) = ((Subgroup.inclusion hYC y : ↥C) : ↥C ⧸ N₁) :=
    fun y => rfl
  have hconjι : ∀ (g : ↥C) (y : ↥Y), (g : ↥C ⧸ N₁) * ι (y : ↥Y ⧸ N₀) * (g : ↥C ⧸ N₁)⁻¹ =
      ι ((⟨(g : G) * y * (g : G)⁻¹, hYconj g g.2 y y.2⟩ : ↥Y) : ↥Y ⧸ N₀) := by
    intro g y
    rw [hιmk', hιmk', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  let g₂ : ↥C := ⟨u₂, hu₂C⟩
  have ha : ∀ x : ↥Y ⧸ N₀, (g₂ : ↥C ⧸ N₁) * ι x * (g₂ : ↥C ⧸ N₁)⁻¹ ∈ ι.range ∧
      (g₂ : ↥C ⧸ N₁)⁻¹ * ι x * (g₂ : ↥C ⧸ N₁) ∈ ι.range := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      refine ⟨⟨_, (hconjι g₂ y).symm⟩, ?_⟩
      have h' := hconjι g₂⁻¹ y
      rw [QuotientGroup.mk_inv, inv_inv] at h'
      exact ⟨_, h'.symm⟩
  have hactJ : ∀ {J : Subgroup G}, J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u → u₂ ∈ trivialOnQuot J →
      ∀ x ∈ Q3T8.Asc77.T7H.exactImg Ω u J, ∃ n ∈ oddCoreOf (Q3T8.Asc77.T7H.exactImg Ω u J),
        (g₂ : ↥C ⧸ N₁) * ι x * (g₂ : ↥C ⧸ N₁)⁻¹ = ι (n * x) := by
    intro J hJ hvJ x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hk : (y : G) ∈ Q3T8.Asc77.ExactLayer.exactCore u J := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨n, hn, hnk⟩ := Q3T8.Asc77.S22.exists_odd_mul hΩ hcpg hJ hu₂C hvJ hk y.2 (hYconj u₂ hu₂C
        y y.2)
    refine ⟨n, hn, ?_⟩
    have e := hconjι g₂ y
    exact e.trans (congrArg ι hnk)
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ h.hK'.1 h.hK₃.1 h.hK₃K'.symm h.hzK' hzK₃ h.hu₂.1
  have hu₂K₄ : u₂ ∈ trivialOnQuot K₄ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ h.hK'.1 hK₄.1 h2.symm h.hzK' hzK₄ h.hu₂.1
  have ha2 : (g₂ : ↥C ⧸ N₁) * (g₂ : ↥C ⧸ N₁) = ι (Q3T8.Asc77.T7H.toBar Ω u z hzY) := by
    rw [← QuotientGroup.mk_mul]
    show ((g₂ * g₂ : ↥C) : ↥C ⧸ N₁) = ((Subgroup.inclusion hYC ⟨z, hzY⟩ : ↥C) : ↥C ⧸ N₁)
    congr 1
    exact Subtype.ext h.sq₂
  have hall := Q3T8.Asc77.S22.twin_section_dichotomy hBelow hlt hS hA3 hA4 hne hzA3 hzA4 hstar ι hι
    (g₂ : ↥C ⧸ N₁) ha (hactJ hK₃Ω hu₂K₃) (hactJ hK₄Ω hu₂K₄) ha2
  
  have hOY : oddCoreOf Y ≤ oddCoreOf C :=
    le_oddCoreIn_of_normalizes ((oddCoreOf_le_self Y).trans hYC) (fun g hg => hOnorm g hg)
      (oddCoreOf_odd_natCard _)
  have hzC : z ∈ C := hYC hzY
  have hcomm : ∀ g ∈ C, ⁅g, z⁆ ∈ oddCoreOf Y := by
    intro g hg
    have hgK₃ : conjSub g K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
        Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hg hK₃Ω
    have hzg : IsUniqueInvolution (conjSub g K₃) (g * z * g⁻¹) := hzK₃.conj g
    have hzgc : g * z * g⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K₃) :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hgK₃ hzg).mem
    have hzgY : g * z * g⁻¹ ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hgK₃ hzgc
    have hB := hall _ (Q3T8.Asc77.T7H.exactImg_mem hgK₃)
    have hB' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hgK₃ hzg hzgY
    have heq : Q3T8.Asc77.T7H.toBar Ω u z hzY = Q3T8.Asc77.T7H.toBar Ω u (g * z * g⁻¹) hzgY :=
        hB.eq hB'
    have hmem : (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨g * z * g⁻¹, hzgY⟩ ∈ N₀ := QuotientGroup.eq.mp heq
    have hmemG : z⁻¹ * (g * z * g⁻¹) ∈ oddCoreOf Y := ⟨_, hmem, rfl⟩
    have hconj := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hzY) hmemG
    have e : z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = ⁅g, z⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at hconj
  refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hc : ⁅(g : G), z⁆ ∈ oddCoreOf C := hOY (hcomm g g.2)
    obtain ⟨hcC, hco⟩ := mem_oddCoreOf_iff.mp hc
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
        (g * ⟨z, hzC⟩ * g⁻¹ * ⟨z, hzC⟩⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hco
    have h1' : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥C) g,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨z, hzC⟩⁆ = 1 := by
      rw [commutatorElement_def]
      simpa only [map_mul, map_inv] using h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1'
end Main
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G

theorem c22_dstarConn_of_layerStar_proved [Fact Q3T7E.ThmEWithSylow3] (h :
    Q3T8.Asc77.C22G.C22_layerStar) : Q3T8.Asc77.C22G.C22_dstarConn :=
  Q3T8.Asc77.C22G.c22_dstarConn_of_layerStar (Q3T8.Asc77.thmEWithSylow_of_nonToral
      G2D4Models.g2NonToralGenerate_all) h

theorem c22_8Gen_of_layerStar [Fact Q3T7E.ThmEWithSylow3] (h : Q3T8.Asc77.C22G.C22_layerStar) :
    Q3T8.Asc77.C22_8Gen :=
  Q3T8.Asc77.C22G.c22_8Gen_of_dstarConn (Q3T8.Asc77.C22G.c22_dstarConn_of_layerStar_proved h)
end C22G
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

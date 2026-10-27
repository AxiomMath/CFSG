module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelWeight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterStepHyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V : Subgroup G} {k : ℕ}

theorem coords (H : U3C1OuterStepHyp G L f t T R₂ D d V k) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (v : G → K) (μ : K),
      Fintype.card K = 2 ^ f ∧ U3A₁Coords (szA₁ (szT₁ L T)) d v μ ∧
        ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w := by
  obtain ⟨-, hA₁card, -, -, -, hA₁2, -⟩ := H.start.facts_of_card_sylow H.card_sylow
  have hdA : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    normalizer_le_normalizer_inf_centralizer _ (H.cartan.le_normalizer H.cartan.mem)
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a₀ ∈ szA₁ (szT₁ L T), a₀ ≠ 1 := by
    rcases (szA₁ (szT₁ L T)).bot_or_exists_ne_one with hbot | hex
    · exfalso
      rw [hbot, Subgroup.card_bot] at hA₁card
      have h4 : 4 ≤ 2 ^ f :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) H.start.two_le
      omega
    · exact hex
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := outerLevel_exists_coords (A := szA₁ (szT₁ L T))
    (fun a ha b hb => mem_centralizer_iff.mp (mem_szA₁.mp hb).2 a (mem_szA₁.mp ha).1) hA₁2 ha₀
    ha₀1 (fun b hb => (mem_normalizer_iff''.mp hdA b).mp hb) H.cartan.trans
  exact ⟨K, inferInstance, inferInstance, inferInstance, v, μ, by rw [hK, hA₁card], hc, hμ⟩

theorem outerStage (H : U3C1OuterStepHyp G L f t T R₂ D d V k)
    {U U₁ : Subgroup G} (hL : U3C1OuterLevelData G L f t T D V U U₁ k) :
    U3C1OuterStage G L f t T d V U U₁ k where
  start := H.start
  card_sylow := H.card_sylow
  one_le := H.conf.one_le
  coords := H.coords
  d_norm := ⟨⟨H.conf.D_le H.cartan.mem, H.cartan.le_normalizer H.cartan.mem⟩,
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp H.start.mem d (H.cartan.le H.cartan.mem))⟩
  le_centralizer := H.conf.le_centralizer
  comm := H.conf.comm
  card := H.conf.card
  omega := H.conf.omega
  pow := H.conf.pow
  le := H.conf.le
  inv := H.conf.inv
  U_le := hL.U_le
  card_U := hL.card_U
  conj_t_not_mem := hL.conj_t_not_mem
  conj_szA₁ := hL.conj_szA₁
  conj_T₁ := hL.conj_T₁
  conj_V₁ := hL.conj_V₁
  inf_centralizer := hL.inf_centralizer
  U₁_le := hL.U₁_le
  U₁_normal := hL.U₁_normal
  sup_eq := hL.sup_eq
  t_not_mem := hL.t_not_mem
  inf_eq := hL.inf_eq
  d_mem_U₁ := hL.D_le H.cartan.mem

end U3C1OuterStepHyp

theorem u3C1OuterMuHighInput_holds : U3C1OuterMuHighInput := by
  intro G _ _ L f t T R₂ D d V U U₁ k H hL hk
  have h := H.outerStage hL
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  obtain ⟨μ', -, hμ0, hμ'⟩ := h.mu_eq_zero_or_one hK hc hμ
  intro x hx
  refine mem_centralizer_iff.mpr fun r hr => ?_
  obtain ⟨y, hy, rfl⟩ := h.exists_comm_t_eq hK hc hμ hr
  have e := hμ' x hx y hy
  rw [hμ0 hk, zero_mul] at e
  have e1 := hc.eq_one_of_v_eq_zero (h.conj_V₁ x hx _ (h.comm_t_mem (h.U₁_le hy))) e
  calc (y * t * y⁻¹ * t⁻¹) * x =
        (y * t * y⁻¹ * t⁻¹) * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * x := by
        rw [e1, mul_one]
    _ = x * (y * t * y⁻¹ * t⁻¹) := by group

theorem u3C1OuterStructureInput_holds :
    U3C1OuterStructureInput := by
  intro G _ _ L f t T R₂ D d V U U₁ k H hL hμV hlam
  have h := H.outerStage hL
  exact
    { comm := h.V₁_comm hμV hlam
      card := h.card_V₁ hlam
      sq_mem := fun x hx => h.sq_mem_V (mem_outerV₁.mp hx).1
      omega := fun x hx hx2 => h.omega_V₁ hμV hx hx2 }

end CFSG.SeitzReduction.RankOne

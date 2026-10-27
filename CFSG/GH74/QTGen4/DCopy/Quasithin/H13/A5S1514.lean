module

public import CFSG.Quasithin.H13.A5S1514
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem conjClosure_V3_le_T_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz) :
    conjClosure S.V3 H ≤ T :=
  (S.hypF91_F4 h1323 hH).F92_1.1.trans
    (pCoreOf_two_le_of_isSylowTwoOf (S.hypF91_F4 h1323 hH).sylow_H)

theorem almostSpecialA5Hyp_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : AlmostSpecialA5Hyp S.V3 S.V1 L T H where
  base := (S.hypF91_F4 h1323 hH).almostSpecialHyp
  natural := S.isA5ModuleFor
  card_V₁ := S.card_V1
  V_eq := by rw [S.conjClosure_V1_L, lOne_eq_L₁Of]; exact S.commutator_V_L1.symm
  U_ne := S.not_le_pCoreOf_of_not_elemAbelian hna

theorem lemma_13_5_14_one_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hU : ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 = conjClosure S.V3 H) :
    ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H ∧ conjClosure S.V3 H ≤ S.L1 := by
  have hV1 : S.V1 ≤ ⁅conjClosure S.V3 H, S.L1⁆ :=
    S.V1_le_V3.trans (S.commutator_V3_L1.ge.trans
      (Subgroup.commutator_mono (le_conjClosure _ _) le_rfl))
  have h1 : ⁅conjClosure S.V3 H, S.L1⁆ = conjClosure S.V3 H :=
    calc ⁅conjClosure S.V3 H, S.L1⁆ = ⁅conjClosure S.V3 H, S.L1⁆ ⊔ S.V1 :=
          (sup_eq_left.mpr hV1).symm
      _ = conjClosure S.V3 H := hU
  refine ⟨h1, ?_⟩
  rw [← h1, Subgroup.commutator_le]
  intro u hu l hl
  have huN : u ∈ Subgroup.normalizer (S.L1 : Set G) :=
    S.T_le_normalizer_L1 (S.conjClosure_V3_le_T_F4 h1323 hH hu)
  have : u * l * u⁻¹ ∈ S.L1 := (Subgroup.mem_normalizer_iff.mp huN l).mp hl
  rw [commutatorElement_def]
  exact S.L1.mul_mem this (S.L1.inv_mem hl)

theorem rho_U_InD_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz) {u : G}
    (hu : u ∈ conjClosure S.V3 H) :
    InD (S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T_F4 h1323 hH hu)⟩) :=
  S.frame.T_D _ (S.conjClosure_V3_le_T_F4 h1323 hH hu)

theorem lemma_13_5_14_two_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) :
    (∀ u (hu : u ∈ conjClosure S.V3 H),
        InK4 (S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T_F4 h1323 hH hu)⟩)) ∧
      ∀ σ, InK4 σ → ∃ u, ∃ hu : u ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨u, S.frame.T_le (S.conjClosure_V3_le_T_F4 h1323 hH hu)⟩ = σ := by
  have hUN : ∀ u ∈ conjClosure S.V3 H, u ∈ Subgroup.normalizer (V : Set G) := fun u hu =>
    S.frame.T_le (S.conjClosure_V3_le_T_F4 h1323 hH hu)
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1

  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 →
      ∀ u (hu : u ∈ conjClosure S.V3 H), ∃ hu' : (g : G) * u * (g : G)⁻¹ ∈ conjClosure S.V3 H,
        S.frame.ρ ⟨_, hUN _ hu'⟩ = S.frame.ρ g * S.frame.ρ ⟨u, hUN u hu⟩ * (S.frame.ρ g)⁻¹ := by
    intro g hg u hu
    have hu' := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure S.V3 H (hL1H hg)) u).mp hu
    refine ⟨hu', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  obtain ⟨g, hgL1, hg⟩ := S.exists_L1_of_three c3p_props.1 c3p_props.2.1 c3p_props.2.2
  obtain ⟨g', hg'L1, hg'⟩ := S.exists_L1_of_three c3q_props.1 c3q_props.2.1 c3q_props.2.2
  have hgi : ((g⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.L1 := S.L1.inv_mem hgL1
  have hK4 : ∀ u (hu : u ∈ conjClosure S.V3 H), InK4 (S.frame.ρ ⟨u, hUN u hu⟩) := by
    intro u hu
    obtain ⟨h1, e1⟩ := hconj g hgL1 u hu
    obtain ⟨h2, e2⟩ := hconj g⁻¹ hgi u hu
    obtain ⟨h3, e3⟩ := hconj g' hg'L1 u hu
    have d1 := S.rho_U_InD_F4 h1323 hH h1
    have d2 := S.rho_U_InD_F4 h1323 hH h2
    have d3 := S.rho_U_InD_F4 h1323 hH h3
    rw [e1, hg] at d1
    rw [e2, map_inv, hg, inv_inv] at d2
    rw [e3, hg'] at d3
    exact InK4_of_conj_D _ (S.rho_U_InD_F4 h1323 hH hu) d1 d2 d3
  refine ⟨hK4, fun σ hσ => ?_⟩

  obtain ⟨u, hu, huC⟩ : ∃ u ∈ conjClosure S.V3 H, u ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    refine S.not_le_pCoreOf_of_not_elemAbelian hna fun x hx => ?_
    rw [← S.cLT]
    exact ⟨le_sup_right (a := L) (S.conjClosure_V3_le_T_F4 h1323 hH hx), hall x hx⟩
  have hu1 : S.frame.ρ ⟨u, hUN u hu⟩ ≠ 1 := fun h => huC (S.frame.mem_centralizer_of_rho _ h)
  rcases hσ with rfl | hσ
  · exact ⟨1, Subgroup.one_mem _, map_one _⟩
  have hσl : σ ∈ [pa, pb, pc] := by
    rcases hσ with rfl | rfl | rfl <;> simp
  have hul : S.frame.ρ ⟨u, hUN u hu⟩ ∈ [pa, pb, pc] := by
    rcases hK4 u hu with h | h | h | h
    · exact absurd h hu1
    all_goals simp [h]
  rcases K4_orbit _ hul σ hσl with h | h | h
  · exact ⟨u, hu, h.symm⟩
  · obtain ⟨h1, e1⟩ := hconj g hgL1 u hu
    exact ⟨_, h1, by rw [e1, hg, h]⟩
  · obtain ⟨h2, e2⟩ := hconj g⁻¹ hgi u hu
    exact ⟨_, h2, by rw [e2, map_inv, hg, inv_inv, h]⟩

theorem lemma_13_5_14_three_F4 (h1323 : Input1323Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (S.V1 : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l = L ⊔ conjClosure S.V3 H ∧
      S.L1 ≤ conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) l := by
  have h2 := (S.almostSpecialA5Hyp_F4 h1323 hH hna).G24_two hl hlN
  exact ⟨h2, h2 ▸ S.L1_le_L.trans le_sup_left⟩

end Setting

end CFSG.Quasithin.H13.A5

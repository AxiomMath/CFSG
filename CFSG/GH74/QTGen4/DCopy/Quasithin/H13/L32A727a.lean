module

public import CFSG.Quasithin.H13.L32A727a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem l1T_le_M_F4 (hyp : Hyp147 G T L V) (h1332 : Stmt13_3_2_F4) :
    l1 T L V ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer))
    (h1332 G T L hyp.hyp.h13 L hyp.hyp.h13.faithful).2.1.1

theorem setting_of_le_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {X : Subgroup G} (hLX : l1 T L V ⊔ T ≤ X) (hXH : X ≤ H)
    (hXM : ¬ X ≤ Subgroup.normalizer (L : Set G)) : Setting147 G T L V X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1 := Hyp147.isTSub_V1_F4 S.hyp (stmtL32NModule_of_inputs_F4 h1332 h1334)
  have hXG : X ≤ A6.g1 T V := hXH.trans S.hz.2.1
  have hV1T : fsuV1 T V ≤ T := by
    have hZ : quasithinOmegaOneCenter T ≤ T :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
    exact inf_le_right.trans hZ
  have hV1O : fsuV1 T V ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (hV1T.trans (le_sup_right.trans hLX)) hXG
      (IsPGroup.of_card hV1.2.1)
  have hO2 : pCoreOf 2 X ≠ ⊥ := by
    intro h
    have : Nat.card ↥(fsuV1 T V) = 1 := by
      rw [h, le_bot_iff] at hV1O
      rw [hV1O, Subgroup.card_bot]
    rw [hV1.2.1] at this
    norm_num at this
  exact ⟨S.hyp, ⟨⟨hLX, hO2⟩, hXG, hXM⟩⟩

theorem le_M_of_concl_F4 {H₀ : Subgroup G} (S₀ : Setting147 G T L V H₀) (h1332 : Stmt13_3_2_F4)
    (hC : Concl T L V H₀) {N R : Subgroup G} (hNH : N ≤ H₀)
    (hHN : H₀ ≤ Subgroup.normalizer (N : Set G)) (hRH : R ≤ H₀)
    (hRn : H₀ ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 ↥R)
    (h3 : ∀ n ∈ N, ∃ k : ℕ, n ^ 3 ^ k ∈ R) : N ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRO : R ≤ pCoreOf 2 H₀ := le_pCoreOf_of_le_normalizer 2 hRH hRn hR2
  have hOT : pCoreOf 2 H₀ ≤ T := pCoreOf_le_of_le S₀.hyp (le_sup_right.trans S₀.hz.1.1)
  have hLM := l1T_le_M_F4 S₀.hyp h1332

  have hNn : (modO2Image H₀ N).Normal := by
    have hn : (N.subgroupOf H₀).Normal := by
      refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHN g.2) n).mp (Subgroup.mem_subgroupOf.mp hn)
      simpa using h1
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hN3 : IsPGroup 3 ↥(modO2Image H₀ N) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := mem_modO2Image'.mp hy
    obtain ⟨k, hk⟩ := h3 n hn
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : n ^ 3 ^ k ∈ CFSG.pCore 2 ↥H₀ := by
      rw [← mem_pCoreOf_iff]
      simpa using hRO hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have hNP : modO2Image H₀ N ≤ CFSG.pCore 3 (↥H₀ ⧸ CFSG.pCore 2 ↥H₀) := le_sSup ⟨hNn, hN3⟩
  intro n hn
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨n, hNH hn⟩ ∈
      CFSG.pCore 3 (↥H₀ ⧸ CFSG.pCore 2 ↥H₀) :=
    hNP ⟨⟨n, hNH hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  rcases hC with h | h
  · rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← mem_pCoreOf_iff] at hmem
    exact le_sup_right.trans hLM (hOT hmem)
  · rw [h] at hmem
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmem
    have h1 : a⁻¹ * ⟨n, hNH hn⟩ ∈ CFSG.pCore 2 ↥H₀ := by
      rw [← QuotientGroup.eq]
      exact hae
    rw [← mem_pCoreOf_iff] at h1
    have e : n = (a : G) * ((a⁻¹ * ⟨n, hNH hn⟩ : ↥H₀) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (le_sup_left.trans hLM ha) (le_sup_right.trans hLM (hOT h1))

end CFSG.Quasithin.H13.L32A.R727

module

public import CFSG.Quasithin.H13.L32AC52c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC52b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem setting_g1_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) :
    Setting147 G T L V (A6.g1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hV1c : Nat.card (fsuV1 T V) = 2 := (hMod G T L V S.hyp.hyp S.hyp.fsu).2.2.2.1
  have hV1p : IsPGroup 2 (fsuV1 T V) := IsPGroup.of_card (n := 1) (by rw [hV1c, pow_one])
  have hO2 : pCoreOf 2 (A6.g1 T V) ≠ ⊥ := by
    intro hbot
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer (H := fsuV1 T V)) le_rfl hV1p
    rw [hbot] at h1
    have := Subgroup.card_le_of_le h1
    rw [Subgroup.card_bot, hV1c] at this
    omega
  exact ⟨S.hyp, ⟨⟨S.hz.1.1.trans S.hz.2.1, hO2⟩, le_rfl, fun h => S.hz.2.2 (S.hz.2.1.trans h)⟩⟩

theorem eq_g1_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) (h49 : Lemma14_7_49_F4)
    (h50 : Lemma14_7_50_F4) (h51 : Lemma14_7_51_F4) (S : Setting147 G T L V H) :
    H = A6.g1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hcK, -, -⟩ := h48 _ T L V H S
  have hK : K ∈ cComp H := by rw [hcK]; exact Set.mem_singleton K
  have S₁ := setting_g1_F4 h1332 h1334 S
  have hHG : H ≤ A6.g1 T V := S.hz.2.1
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTG : T ≤ A6.g1 T V := hTH.trans hHG
  have hKH := le_of_mem_cComp hK

  obtain ⟨K₁, hK₁, hKK₁⟩ := CFSG.Quasithin.lemma_1_2_4_exists S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h37 h39 S₁.hz.1.2
    (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTG) (hKH.trans hHG)
    (cComp_subset_lFamily hTH hK)

  obtain ⟨hdvd, heq⟩ := card_dvd_of_le hKK₁
  have hc : ∀ {X : Type} [Group X], IsAlt 5 X ∨ IsPSU 3 3 1 X → Nat.card X = 60 ∨
      Nat.card X = 6048 := fun h => h.imp card_of_isAlt_five SBc11.card_of_isPSU_three_three
  have hK₁le : K₁ ≤ K ⊔ pCoreOf 2 K₁ := by
    refine heq ?_
    rcases hc (kstar_cases_F4 h47 h49 h50 h51 S hK) with h | h <;>
      rcases hc (kstar_cases_F4 h47 h49 h50 h51 S₁ hK₁) with h' | h' <;>
      rw [h, h'] at hdvd ⊢ <;> first | rfl | (exfalso; norm_num at hdvd)

  have hNT : pCoreOf 2 K₁ ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₁)).trans
      (L32A.pCoreOf_le_of_le S.hyp hTG)
  have hK₁H : K₁ ≤ H := hK₁le.trans (sup_le hKH (hNT.trans hTH))
  obtain ⟨K₁', hcK₁', hG₁, -⟩ := h48 _ T L V _ S₁
  have hK₁K₁' : K₁ = K₁' := by
    have := hK₁
    rw [hcK₁'] at this
    exact this
  subst hK₁K₁'
  refine le_antisymm hHG ?_
  rw [hG₁]
  exact sup_le hK₁H hTH

theorem thm14_7_52_of_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) (h49 : Lemma14_7_49_F4)
    (h50 : Lemma14_7_50_F4) (h51 : Lemma14_7_51_F4) : Thm14_7_52_F4 := by
  intro G _ _ T L V H S K hK
  obtain ⟨K', hcK', hHKT, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hHg := eq_g1_F4 h1332 h1334 h37 h39 h47 h48 h49 h50 h51 S
  refine ⟨hHKT, hHg, fun H' S' => (eq_g1_F4 h1332 h1334 h37 h39 h47 h48 h49 h50 h51 S').trans
    hHg.symm, ?_, kstar_cases_F4 h47 h49 h50 h51 S hK⟩
  rw [hHg]

end CFSG.Quasithin.H13.L32A.C

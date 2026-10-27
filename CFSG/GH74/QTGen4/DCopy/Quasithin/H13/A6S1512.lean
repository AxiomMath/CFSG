module

public import CFSG.Quasithin.H13.A6S1512
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1516d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem a6CentralQuotient_of_isA6On_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4) [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (hH : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hA6V : IsA6On L V) : A6CentralQuotient L := by
  obtain ⟨hfive, -, -, -⟩ := h1332 G T L hH L hH.faithful
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  obtain ⟨e⟩ := hA6V
  obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLN
  obtain ⟨φ₁, hφ₁⟩ := exists_surjective_quot_of_alt6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
  have hle := Nat.card_le_card_of_surjective φ₁ hφ₁
  rw [card_alt6] at hle
  rcases hfive with hf | h32 | hf | hhat | hu
  · obtain ⟨f⟩ := hf
    rw [Nat.card_congr f.toEquiv, card_alt5] at hle
    omega
  · rw [card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h32)] at hle
    omega
  · obtain ⟨f⟩ := hf
    have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have h1 : f z ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) :=
        map_center_le_center f.toMonoidHom f.surjective ⟨z, hz, rfl⟩
      rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact f.injective (h1.trans (map_one f).symm)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans f)⟩
  · exact hhat.2.2
  · exact (h13316 G T L hH hu).elim

@[expose] def Input13518Six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ IsHatA6 L → ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) →
    ∃ H ∈ S.Hz, ¬ IsElemAbelian 2 (conjClosure S.V3 H) ∧ H ≤ Subgroup.normalizer (S.L1 : Set G)

@[expose] def Input13521Four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsHatA6 L

theorem stmt13_5_12_six_of_inputs_F4
    (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4)
    (h1341 : Stmt13_4_1_F4) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) (hU43 : StmtU43Type)
    (h13521 : Input13521Four_F4) (h13518 : Input13518Six_F4) : Stmt13_5_12_six_F4 := by
  intro G _ _ T L V hH hV hA6V hNS hna

  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact hNS (h1341 G T L V hH hV h)
  obtain ⟨S⟩ := exists_setting4_F4 h1332 h13316 hH
    (a6CentralQuotient_of_isA6On_F4 h1332 h13316 hH hV hA6V) hV hZV

  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  rw [S.v3_eq, hg1] at hna
  have hna' : ¬ IsElemAbelian 2 (conjClosure S.V3 S.G1) := fun h => hna h.1

  have hhat := h13521 G T L V S hNS hna'
  obtain ⟨H, hH', hnaH, hn⟩ := h13518 G T L V S hNS hhat hna'

  exact S.psu43_F4 hNS h13315 h1356two hH' hhat hn hnaH hobl hctk hU43

end CFSG.Quasithin.H13.A6

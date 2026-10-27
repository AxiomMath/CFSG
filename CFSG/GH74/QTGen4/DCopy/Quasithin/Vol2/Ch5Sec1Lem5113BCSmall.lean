module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCSmall
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem stmt5_1_13_bc_small_of_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
      Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
      Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
      quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
      ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
      Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
      Nat.card T ≤ 2 ^ 7 →
        pCoreOf 2 (conjClosure Kh₁ T) = ⁅conjClosure (quasithinOmegaOneCenter T)
            (conjClosure Kh₁ T ⊔ T), conjClosure Kh₁ T⁆ ∧
          Nat.card ↥(pCoreOf 2 (conjClosure Kh₁ T)) = 2 ^ 4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 _ hX hnZ hA7 _ _ hT
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hX hnZ hA7
  have hT2 : IsPGroup 2 T := m.hyp.toHyp5_0_1.sylow.1
  have hTK := pk.card_inf_eq_eight_mul
  have hUO := pk.commutator_le_pCoreOf hT2
  have hU16 : 16 ≤ Nat.card ↥⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T),
      conjClosure Kh₁ T⁆ := by
    rcases pk.card with h | h <;> rw [h] <;> norm_num
  have hcU := Subgroup.card_le_of_le hUO
  have hcT := Subgroup.card_le_of_le (inf_le_left : T ⊓ conjClosure Kh₁ T ≤ T)
  have hT' : Nat.card T ≤ 128 := by simpa using hT
  have hO16 : Nat.card ↥(pCoreOf 2 (conjClosure Kh₁ T)) = 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    omega
  exact ⟨(Subgroup.eq_of_le_of_card_ge hUO (by omega)).symm, hO16⟩

end CFSG.Quasithin.H13

module

public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal
public import CFSG.GH74.Generic.S1.Exo.NbCenterBasic
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.Generic.ComponentBranches
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
open CFSG.GH74.GLS.Stage1.Thm6.Glue

private theorem nb_hasL2Model_gt_three {K : Type} [Group K] (h : HasL2Model K Odd) :
    HasL2Model K (fun q => Odd q ∧ 3 < q) := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  refine ⟨p, f, hp, hf, ⟨hq, ?_⟩, hL⟩
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hq
    omega
  all_goals exact absurd h0 (by norm_num)

theorem nb_center_classes
    (hG : GenericKnownFacts) (hF : E2.E2ComponentFacts) {K : Type} [Group K] [Finite K]
    (hq : IsQuasisimple K) (hZ : IsPGroup 2 ↥(center K)) (hgen : Gen4 K)
    (hgh : GHList (K ⧸ center K)) (hne : center K ≠ ⊥) :
    HasSL2Model K Odd ∨ (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt K n) ∨
      (IsL34Quotient K ∧ Monoid.exponent ↥(center K) = 4) ∨ E2.Shape2M12 K ∨ E2.Shape2Sz8 K ∨
      IsSL4Model K ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
        Nonempty (K ≃* ↥(StatedSp 2 F))) := by
  classical
  have h2c : 2 ∣ Nat.card ↥(center K) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [pow_zero] at hn
      exact Subgroup.card_eq_one.1 hn
    exact hn ▸ dvd_pow_self 2 hn0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwc, hw2⟩ : ∃ w : K, w ∈ center K ∧ orderOf w = 2 := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center K)) 2 h2c
    exact ⟨z, z.2, by rw [← hz]; exact Subgroup.orderOf_coe z⟩
  by_cases hT : InT2 K
  · obtain ⟨-, hT⟩ := hT
    rcases hT with hL2 | hS | hA7 | ⟨n, h7, h11, hn⟩ | ⟨hl, hexp⟩
    · exfalso
      obtain ⟨p, f, hp, hf, ⟨hqodd, -⟩, hL⟩ := hL2
      exact hne (center_eq_bot_of_isL2Model (isL2Model_of_hasL2Model
        (nb_hasL2Model_gt_three ⟨p, f, hp, hf, hqodd, hL⟩)))
    · exact Or.inl hS
    · exact absurd (center_eq_bot_of_isA7Model hA7) hne
    · exact Or.inr (Or.inl ⟨n, h7, h11, hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hl, hexp⟩))
  by_cases hC : InC2 K
  · rcases TwoThin.c2ShapeG_of_inC2 hG hF hC hgen with h | h | h
    · exact absurd h hne
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hO : pPrimeCore 2 K = ⊥ := nb_pPrimeCore_eq_bot_of_center hq hZ hne
  have hcpc : center K = pCore 2 K := nb_center_eq_pCore hq hZ
  obtain ⟨e₀⟩ := nb_nonempty_mulEquiv_centralizerBar hwc hO
  let e : K ≃* ↥(⊤ : Subgroup (CentralizerBar w)) := e₀.trans Subgroup.topEquiv.symm
  have hq' : IsQuasisimple ↥(⊤ : Subgroup (CentralizerBar w)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hcen' : center ↥(⊤ : Subgroup (CentralizerBar w)) =
      pCore 2 ↥(⊤ : Subgroup (CentralizerBar w)) := by
    have h1 := Subgroup.map_center_eq e
    have h2 : (CFSG.pCore 2 K).map e.toMonoidHom = CFSG.pCore 2 ↥(⊤ : Subgroup (CentralizerBar w)) :=
      CFSG.pCore_map_iso 2 e
    rw [← h1, ← h2, hcpc]
    rfl
  have hC' : ¬ InC2 ↥(⊤ : Subgroup (CentralizerBar w)) :=
    fun h => hC (E2.inC2_of_mulEquiv e.symm h)
  have hT' : ¬ InT2 ↥(⊤ : Subgroup (CentralizerBar w)) :=
    fun h => hT (TwoThin.inT2_of_mulEquiv e.symm h)
  have hset : Setup w (⊤ : Subgroup (CentralizerBar w)) := ⟨hq', hcen', hC', hT'⟩
  have hgh' : GHList (↥(⊤ : Subgroup (CentralizerBar w)) ⧸
      center ↥(⊤ : Subgroup (CentralizerBar w))) :=
    GHList.of_mulEquiv (E2.centerQuotientEquiv e) hgh
  have hshape : GenericShape w (⊤ : Subgroup (CentralizerBar w)) := by
    rcases hgh' with ⟨n, hn7, hn11, ⟨e1⟩⟩ | hsp | ⟨p, f, hp, hf, hL⟩
    · exact shape_of_alt hG hgen hw2 hset hn7 hn11 e1
    · rcases hsp with h | h | h | h | h | h | h | h | h
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_M11 hset.isSimple h)
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_M12 hset.isSimple h)
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_M22 hset.isSimple h)
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_M23 hset.isSimple h)
      · exact shape_of_J1 hG hw2 hset h
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_J2 hset.isSimple h)
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_J3 hset.isSimple h)
      · exact shape_of_McL hG hgen hw2 hset h
      · exact shape_of_Ly hG hgen hw2 hset h
    · rcases hL with ⟨hp2, h | h | h | h | h | h⟩ | ⟨hp2, -, h⟩ | ⟨hp2, -, h⟩ | ⟨hq4, h⟩ |
          ⟨hq4, h⟩ | h | ⟨-, h | h | h | h | h⟩
      · exact shape_of_psl2 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psl3 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psu3 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psp4 hG hgen hw2 hset hp hp2 h
      · exact shape_of_g2 hG hgen hw2 hset hp hp2 h hf
      · exact shape_of_3D4 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psl4 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psu4 hG hgen hw2 hset hp hp2 h
      · exact shape_of_psl5 hG hgen hw2 hset hp hq4 h
      · exact shape_of_psu5 hG hgen hw2 hset hp hq4 h
      · exact shape_of_ree hG hw2 hset h
      · exact shape_of_simpleInC2 hgen hw2 hset (simpleInC2_of_even hset.isSimple (Or.inl h))
      · exact shape_of_simpleInC2 hgen hw2 hset
          (simpleInC2_of_even hset.isSimple (Or.inr (Or.inl h)))
      · exact shape_of_simpleInC2 hgen hw2 hset
          (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inl h))))
      · exact shape_of_simpleInC2 hgen hw2 hset
          (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact shape_of_simpleInC2 hgen hw2 hset
          (simpleInC2_of_even hset.isSimple (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  rcases hshape with h1 | h2 | h3 | h4 | h5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsSL4Model.of_mulEquiv h1.1 e.symm))))))
  · obtain ⟨⟨F, hF1, hF2, hodd, ⟨e2⟩⟩, -⟩ := h2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨F, hF1, hF2, hodd, ⟨e.trans e2⟩⟩)))))
  · exact absurd (Subgroup.mem_top _) h3.2
  · exact absurd (Subgroup.mem_top _) h4.2
  · exact absurd (Subgroup.mem_top _) h5.2

end CFSG.GH74.Generic.S1.Exo

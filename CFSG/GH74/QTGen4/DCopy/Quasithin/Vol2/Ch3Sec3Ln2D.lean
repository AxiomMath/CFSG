module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2D

public section
namespace CFSG.Quasithin.H13.Ln2

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem module_cases_F4
    (h18 : Stmt3_3_18_F4) (h51 : AsB51) (hI16 : AsI16Cover) (h : Hyp331 G T M L D)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      B51Hyp (ffJ (autOn (L ⊔ T) (vPlus L T))) (autOn L (vPlus L T)) ∧
      ((∃ Z : Subgroup ↥(vPlus L T),
          Z ≤ fixV (autOn L (vPlus L T)) ⊓ commV (autOn L (vPlus L T)) ∧ Nat.card ↥Z ≤ 2 ∧
          (n = 5 → Z = ⊥) ∧
          SLExteriorTwo (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) Z n) ∨
        SumNatDual (autOn L (vPlus L T)) (commV (autOn L (vPlus L T))) n) := by
  obtain ⟨hVc, hB⟩ := b51Hyp_of h h38 h39 hTL
  refine ⟨hVc, hB, ?_⟩
  set K := autOn L (vPlus L T) with hKdef
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hn3 : 3 ≤ n := by omega
  have hK : IsPSL n 2 1 ↥K :=
    LRed4.isPSL_two_of_statedSL' hn3 (e.trans (statedSLEquivZModTwo (n := n) h2).symm)
  have hcard : Nat.card ↥K = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hV2 : ∀ v : ↥(vPlus L T), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hred.2.1.2 v v.2)
  have hA := alt15127_of_b51 h51 hI16 asI16CoverA8_of hV2 hB
    (by rcases hn with rfl | rfl; exacts [Or.inl hK, Or.inr hK])
  rcases hA with ⟨Z, hZ, hZ2, hext⟩ | hext | ⟨n', hsnd⟩ | ⟨n', hn', k, hk1, -, hDS⟩
  ·
    obtain ⟨π, hπ⟩ := hext
    by_cases h4 : n = 4
    · subst h4
      exact Or.inl ⟨Z, hZ, hZ2, fun h5 => absurd h5 (by norm_num), π, hπ⟩
    · exact (false_of_surjective (Or.inl rfl) hn (Ne.symm h4) hcard π hπ.1).elim
  ·
    obtain ⟨π, hπ⟩ := hext
    by_cases h5 : n = 5
    · subst h5
      exact Or.inl ⟨⊥, bot_le, by rw [Subgroup.card_bot]; norm_num, fun _ => rfl, π, hπ⟩
    · exact (false_of_surjective (Or.inr rfl) hn (Ne.symm h5) hcard π hπ.1).elim
  ·
    by_cases hnn : n' = n
    · subst hnn
      exact Or.inr hsnd
    · obtain ⟨hn'', π, U₁, U₂, -, hR, -⟩ := hsnd
      exact (false_of_surjective hn'' hn hnn hcard π hR.1).elim
  ·
    by_cases hnn : n' = n
    · subst hnn
      exfalso
      obtain ⟨_, h18'⟩ := h18 G T M L D h n' hn ⟨e⟩
      apply h18'
      refine ⟨k, hk1, ?_⟩
      rw [← commV_autOn_eq h]
      exact hDS
    · obtain ⟨I, π, -, -, -, hR⟩ := hDS
      exact (false_of_surjective hn' hn hnn hcard π (hR ⟨0, hk1⟩).1).elim

end CFSG.Quasithin.H13.Ln2

module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113TypeF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Type
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113TypeS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem false_of_a314One_F4 (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hM23 : FactM23L34) (h312 : A312ForSQTK) (h510 : Stmt5_1_10_F4) (hlie : Stmt5_1_13_lieC_F4)
    (hK4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (heq : K₁ = oTwoUpper H)
    (hR2 : IsRank2LieChar2 (O2Q (conjClosure Kh₁ T))) : False := by
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  have hlie' := fun htype =>
    (hlie G T M L V H B D K₁ X Kh₁ n k m.hyp m.nota hk m.module m.comp m.closure m.inH m.hat m.lt
      htype).resolve_right fun h => h.not_lieModel_two hK4
  have hk2 : 2 ≤ k := e.field.1.1
  have hshape := e.shape heq
  rw [← heq] at hshape
  rcases hshape with (hL2 | hSz | ⟨hq, hU⟩) | ⟨hS, hD⟩
  · exact m.not_le (hlie' (Or.inr ⟨heq ▸ hL2, hR2⟩))
  · have h2 := e.twoF4_of_suzuki hM h312 heq hSz
    rw [← hcl] at h2
    exact m.not_le (hlie' (Or.inl ⟨heq ▸ hSz, h2⟩))
  · exact e.false_of_unitary hM h312 heq hk2 hq hU
  · rcases hS with hSL | hSp
    · rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · obtain rfl : k = 2 := by omega
        exact e.false_of_l34 hM hM23 h312 heq hSL hD
      · rcases hSL with hL3 | ⟨F, _, _, hF, ⟨eF⟩⟩
        · exact e.false_of_psl3 hM h312 heq hk3 hL3
        · exact e.false_of_sl3 hM h312 heq hk3 hF eF
    · exact e.false_of_psp4 hM h312 heq hk2 hSp

end Main513

theorem stmt5_1_13_type_of_F4
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h36' : A36ForSQTK)
    (h38' : A38ForSQTK) (hF318 : A318Facts) (h510 : Stmt5_1_10_F4) (hlie : Stmt5_1_13_lieC_F4)
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34) (h312 : A312ForSQTK)
    (hnq : Stmt5_1_13_type_nq_F4) (hj1 : Stmt5_1_13_type_j1_F4) (hhat : Stmt5_1_13_type_hat7_F4)
    (hTc : FactType513Aut) (hTe : FactType513Three) : Stmt5_1_13_type_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  obtain ⟨hst, hnot⟩ := m.star513_F4 h37 h38 h510 heq hcl hL24
  have hj := hj1 G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hh7 := hhat G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hnq' := hnq G T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have h314 := hc5.2.2.2
  rw [hcl] at h314
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1

  have hthree : (IsAlt 7 ↥(modO2Image X Kh₁) ∨
      IsHat ↥(modO2Image X Kh₁) (alternatingGroup (Fin 7)) ∨ IsSporadic .M22 ↥(modO2Image X Kh₁) ∨
      IsHat ↥(modO2Image X Kh₁) (NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥(modO2Image X Kh₁) ∨ IsSporadic .J1 ↥(modO2Image X Kh₁) ∨
      IsSporadic .J2 ↥(modO2Image X Kh₁) ∨ IsSporadic .J4 ↥(modO2Image X Kh₁) ∨
      IsSporadic .HS ↥(modO2Image X Kh₁) ∨ IsSporadic .Ru ↥(modO2Image X Kh₁)) →
      Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) := by
    intro hlist
    obtain ⟨hty, hexp, htb⟩ := hTe (O2Q X) _ _ _ _ _ hst hlist hj hnot
    have hty' : IsAlt 7 ↥(modO2Image X Kh₁) ∨ IsSporadic .J2 ↥(modO2Image X Kh₁) ∨
        IsSporadic .M23 ↥(modO2Image X Kh₁) := by
      rcases hty with h7 | h7h | hJ | hM'
      · exact Or.inl h7
      · exact absurd (IsHat.of_mulEquiv eH.symm h7h) (hh7 hexp)
      · exact Or.inr (Or.inl hJ)
      · exact Or.inr (Or.inr hM')
    exact m.type513_of_data hF318 h36' h38' hcl hnot hst.R_le hty' hexp htb

  have haut : ((∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      (IsPSL 2 p 1 ↥(modO2Image X Kh₁) ∨ IsSL2 p ↥(modO2Image X Kh₁))) ∨
      IsPSL 2 5 2 ↥(modO2Image X Kh₁) ∨
      ∃ s : Bool, IsPSLEps3 s 5 1 ↥(modO2Image X Kh₁) ∨ IsSLEps3 s 5 ↥(modO2Image X Kh₁)) →
      False :=
    fun hlist => hnot (hTc (O2Q X) _ _ _ _ _ hst hlist)
  unfold A314Statement at h314
  rcases h314 with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, h4, -⟩ | ⟨-, h5, -⟩ |
      ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ | ⟨-, h11, -⟩ |
      ⟨-, -, h12, -⟩ | h13 | h14
  · refine (m.false_of_a314One_F4 hM hM23 h312 h510 hlie hL24 heq ?_).elim
    rw [hcl]
    exact IsRank2LieChar2.of_mulEquiv eH.symm (isRank2LieChar2_of_a314One h1)
  · rcases h2 with h | h
    · exact hthree (Or.inl h)
    · exact hthree (Or.inr (Or.inl h))
  · rcases h3 with h | ⟨p, hp, hp5, hp8, h⟩
    · exact (haut (Or.inr (Or.inl h))).elim
    · exact (haut (Or.inl ⟨p, hp, hp5, hp8, Or.inl h⟩)).elim
  · exact (haut (Or.inr (Or.inr h4))).elim
  · rcases h5 with h | h
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inl h⟩))).elim
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inr h⟩))).elim
  · rcases h6 with h | h
    · exact hthree (Or.inr (Or.inr (Or.inl h)))
    · exact hthree (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h11)))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h12)))))))))
  · exact (hnq' (Or.inl h13)).elim
  · exact (hnq' (Or.inr h14)).elim

end CFSG.Quasithin.H13

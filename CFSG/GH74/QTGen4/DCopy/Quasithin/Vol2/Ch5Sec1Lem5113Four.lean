module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_four_star_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
      conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem atMaximal_F4 (m : Main513 G T M L V H B D K₁ X Kh₁ n) (h37 : Vol2Native.A37ForSQTKCat)
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (hlie : Stmt5_1_13_lieC_F4) (hc5 : Case5_512 T H X Kh₁)
    (ty : Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H)) {Kt : Subgroup G}
    (hKt : quasithinIsMaximalLocal T Kt) (hKhKt : Kh₁ ≤ Kt) :
    T ≤ Subgroup.normalizer (Kt : Set G) ∧
      Main513 G T M L V H B D K₁ (Kt ⊔ T) Kt n ∧ Case5_512 T H (Kt ⊔ T) Kt := by
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hc5.1)
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  have hTKh : T ≤ Subgroup.normalizer (Kh₁ : Set G) := e.T_le_normalizer_hat_of_eq heq
  set X' := Kt ⊔ T with hX'def
  have hKtc : Kt ∈ cComp X' := hKt.1.2.1
  have hX'O : pCoreOf 2 X' ≠ ⊥ := hKt.1.2.2.2
  have hTX' : T ≤ X' := le_sup_right
  have hTX's : IsSylowTwoOf T X' := h.isSylowTwoOf hTX'
  have hKhL : Kh₁ ∈ lFamily T := cComp_subset_lFamily e.T_le_X e.hat_cComp

  have hTKt : T ≤ Subgroup.normalizer (Kt : Set G) := by
    intro t ht
    have hKts : Kt.map (MulAut.conj t).toMonoidHom ∈ cComp X' := map_conj_mem_cComp hKtc (hTX' ht)
    have hKh : Kh₁ ≤ Kt.map (MulAut.conj t).toMonoidHom :=
      calc Kh₁ = Kh₁.map (MulAut.conj t).toMonoidHom := (A38.map_conj_eq_iff.mpr (hTKh ht)).symm
        _ ≤ Kt.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hKhKt
    exact A38.map_conj_eq_iff.mp
      (Vol2Native.lemma_1_2_4_unique hloc h37 hX'O hKhL hKts hKtc hKh hKhKt)
  have hclt : conjClosure Kt T = Kt := Emb512.conjClosure_hat_eq hTKt

  have hKX' : oTwoUpper H ≤ X' := (heq ▸ e.K₁_le_hat).trans (hKhKt.trans le_sup_left)
  have hHX' : H ≤ X' := by
    have hTK : T ⊔ oTwoUpper H = H := by
      rw [← F6.twoResidual_eq_oTwoUpper]
      exact sup_twoResidual_eq e.sylowH
    rw [← hTK]
    exact sup_le hTX' hKX'
  have hK₁L : K₁ ∈ lFamily T := e.K₁_lFamily
  have hhat : IsHatComp X' K₁ Kt := by
    refine ⟨hKtc, e.K₁_le_hat.trans hKhKt, fun Y hY hK₁Y => ?_⟩
    exact Vol2Native.lemma_1_2_4_unique hloc h37 hX'O hK₁L hY hKtc hK₁Y
      (e.K₁_le_hat.trans hKhKt)
  have hlt : oTwoUpper H < conjClosure Kt T := by
    rw [hclt]
    have := m.lt
    rw [hcl] at this
    exact lt_of_lt_of_le this hKhKt
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -⟩ := ty
  have hnot : ¬ D ⊓ X' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
    hD₃K ((le_inf (hD₃.trans inf_le_left)
      ((hD₃.trans inf_le_right).trans (hcl.le.trans (hKhKt.trans le_sup_left)))).trans hle)
  have m' : Main513 G T M L V H B D K₁ X' Kt n :=
    ⟨m.hyp, m.nota, m.module, m.comp, m.closure, ⟨hHX', hX'O⟩, hhat, hlt, hnot⟩
  refine ⟨hTKt, m', ?_⟩

  obtain ⟨Kt', hhat', -, hcases⟩ :=
    h5112 G T M L H B D K₁ n k m.hyp m.nota hk m.comp m.closure X' ⟨hHX', hX'O⟩
  have hKt' : Kt = Kt' := hhat'.2.2 Kt hKtc (e.K₁_le_hat.trans hKhKt)
  subst hKt'
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact absurd h1 hlt.ne
  · exact absurd heq h2.1.ne
  · exact absurd ((hlie G T M L V H B D K₁ X' Kt n k m.hyp m.nota hk m.module m.comp m.closure
      ⟨hHX', hX'O⟩ hhat hlt (Or.inl h3)).resolve_right fun h => h.not_lieModel_two hc5.1) hnot
  · exact absurd ((hlie G T M L V H B D K₁ X' Kt n k m.hyp m.nota hk m.module m.comp m.closure
      ⟨hHX', hX'O⟩ hhat hlt (Or.inr h4)).resolve_right fun h => h.not_lieModel_two hc5.1) hnot
  · exact h5

end Main513

theorem stmt5_1_13_four_of_F4 (h37 : Vol2Native.A37ForSQTKCat) (h510 : Stmt5_1_10_F4)
    (h5112 : Stmt5_1_12_F4) (hlie : Stmt5_1_13_lieC_F4) (htype : Stmt5_1_13_type_F4)
    (hstar : Stmt5_1_13_four_star_F4) : Stmt5_1_13_four_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hc5.1)
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  obtain ⟨Kt, hKhKt, hKt⟩ := exists_maximalLocal_ge e.isLocalHat
  obtain ⟨hTKt, m', hc5'⟩ := m.atMaximal_F4 h37 h510 h5112 hlie hc5 ty hKt hKhKt
  have hclt : conjClosure Kt T = Kt := Emb512.conjClosure_hat_eq hTKt
  have ty' := htype G T M L V H B D K₁ _ Kt n m' hc5'
  have hstar' := hstar G T M L V H B D K₁ _ Kt n m' hc5' ty' (by rw [hclt]; exact hKt)
  rw [hclt] at hstar'
  rw [hcl]
  exact hKhKt.trans hstar'

end CFSG.Quasithin.H13

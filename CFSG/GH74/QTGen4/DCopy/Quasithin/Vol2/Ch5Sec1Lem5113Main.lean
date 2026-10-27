module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113StepsS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem Main513.atCZ_F4 (m : Main513 G T M L V H B D K₁ X Kh₁ n) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4)
    (hlie : Stmt5_1_13_lieC_F4) (hc2 : Stmt5_1_13_c2_F4)
    (hK4 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2)
    (ty : Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (h4 : conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {Kz₁ : Subgroup G}
    (hz : IsHatComp (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) K₁ Kz₁) :
    Main513 G T M L V H B D K₁ (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) Kz₁ n ∧
      Case5_512 T H (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) Kz₁ ∧
      Kh₁ ≤ Kz₁ := by
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  set X' := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hX'def
  obtain ⟨hX', hSX'⟩ := m.inH_centralizer h4

  have hKhX' : Kh₁ ≤ X' := (le_conjClosure Kh₁ T).trans h4
  have hKhL : Kh₁ ∈ lFamily T := cComp_subset_lFamily e.T_le_X e.hat_cComp
  obtain ⟨L', ⟨hL', hKhL'⟩, -⟩ :=
    Vol2Native.lemma_1_2_4_existsUnique hloc h37 h39 hX'.2 hSX' hKhX' hKhL
  have hL'z : L' = Kz₁ := hz.2.2 L' hL' (e.K₁_le_hat.trans hKhL')
  subst hL'z

  have hlt' : oTwoUpper H < conjClosure L' T :=
    lt_of_lt_of_le m.lt (conjClosure_mono hKhL' le_rfl)
  obtain ⟨-, -, D₃, hD₃, -, hD₃K, -⟩ := ty
  have hnot' : ¬ D ⊓ X' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
    hD₃K ((le_inf (hD₃.trans inf_le_left) (hD₃.trans (inf_le_right.trans h4))).trans hle)
  have m' : Main513 G T M L V H B D K₁ X' L' n :=
    ⟨m.hyp, m.nota, m.module, m.comp, m.closure, hX', hz, hlt', hnot'⟩
  refine ⟨m', ?_, hKhL'⟩

  obtain ⟨Kh₁', hhat', -, hcases⟩ :=
    h5112 G T M L H B D K₁ n k m.hyp m.nota hk m.comp m.closure X' hX'
  have hKh : L' = Kh₁' := hhat'.2.2 L' hz.1 hz.2.1
  subst hKh
  rcases hcases with h1 | h2 | h3 | h4' | h5
  · exact absurd h1 hlt'.ne
  · exact (hc2 G T M L V H B D K₁ X' L' n m' h2.1 h2.2.1 h2.2.2).elim
  · exact absurd ((hlie G T M L V H B D K₁ X' L' n k m.hyp m.nota hk m.module m.comp m.closure
      hX' hz hlt' (Or.inl h3)).resolve_right fun h => h.not_lieModel_two hK4) hnot'
  · exact absurd ((hlie G T M L V H B D K₁ X' L' n k m.hyp m.nota hk m.module m.comp m.closure
      hX' hz hlt' (Or.inr h4')).resolve_right fun h => h.not_lieModel_two hK4) hnot'
  · exact h5

theorem Main513.six_F4
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (h37 : Vol2Native.A37ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h312 : A312ForSQTK) (h510 : Stmt5_1_10_F4)
    (h5112 : Stmt5_1_12_F4) (hlie : Stmt5_1_13_lieC_F4) (hc2 : Stmt5_1_13_c2_F4)
    (htype : Stmt5_1_13_type_F4) (hc5 : Case5_512 T H X Kh₁)
    (ty : Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H))
    (h4 : conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {Kz₁ : Subgroup G}
    (hz : IsHatComp (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) K₁ Kz₁) :
    conjClosure Kz₁ T =
        oThreePrimeResidual (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
      (conjClosure Kh₁ T = conjClosure Kz₁ T ∨
        (Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (O2Q (conjClosure Kz₁ T) ≃* NativeSporadic.M23))) := by
  have h := m.hyp.toHyp5_0_1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk

  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hc5.1)
  have hcl : conjClosure Kh₁ T = Kh₁ := e.conjClosure_hat_eq_of_eq heq
  obtain ⟨m', hc5', hKhKz⟩ := m.atCZ_F4 h37 h39 h510 h5112 hlie hc2 hc5.1 ty h4 hz
  obtain ⟨hX', hSX'⟩ := m.inH_centralizer h4
  have ty' := htype G T M L V H B D K₁ _ Kz₁ n m' hc5'
  refine ⟨ty'.2.1, ?_⟩

  have e' := m'.toEmb512 hk
  have hcl' : conjClosure Kz₁ T = Kz₁ := e'.conjClosure_hat_eq_of_eq heq
  have hty1 : IsA7J2M23 (O2Q Kh₁) := by
    have := ty.1
    rw [hcl] at this
    exact this
  have hty2 : IsA7J2M23 (O2Q Kz₁) := by
    have := ty'.1
    rw [hcl'] at this
    exact this
  rw [hcl, hcl']
  exact eq_or_alt_m23 h.qtke h.simple h.nonabelian h312 hX'.2 hSX'
    ((le_conjClosure Kh₁ T).trans h4) (cComp_subset_lFamily e.T_le_X e.hat_cComp) hz.1 hKhKz
    (e.T_le_normalizer_hat_of_eq heq) hty1 hty2

theorem stmt5_1_13_main_of_F4
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h312 : A312ForSQTK)
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (hlie : Stmt5_1_13_lieC_F4) (hc2 : Stmt5_1_13_c2_F4)
    (htype : Stmt5_1_13_type_F4) (hfour : Stmt5_1_13_four_F4) (hmod : Stmt5_1_13_mod_F4) :
    Stmt5_1_13_main_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n hyp hN hV hK₁ hKeq hX hhat hlt hnot hcase
  have m : Main513 G T M L V H B D K₁ X Kh₁ n := ⟨hyp, hN, hV, hK₁, hKeq, hX, hhat, hlt, hnot⟩
  rcases hcase with ⟨hlt₁, hL4, htyp⟩ | hc5
  · exact (hc2 G T M L V H B D K₁ X Kh₁ n m hlt₁ hL4 htyp).elim
  · have ty := htype G T M L V H B D K₁ X Kh₁ n m hc5
    have h4 := hfour G T M L V H B D K₁ X Kh₁ n m hc5 ty

    obtain ⟨Kz₀, hz₀⟩ := m.exists_hat_centralizer h37 h39 h4
    obtain ⟨m', hc5', -⟩ := m.atCZ_F4 h37 h39 h510 h5112 hlie hc2 hc5.1 ty h4 hz₀
    obtain ⟨hn2, hA5⟩ := hmod G T M L V H B D K₁ _ Kz₀ n m' hc5'
      (htype G T M L V H B D K₁ _ Kz₀ n m' hc5') rfl
    exact ⟨hc5.1, hn2, hA5, h4, ty.1, fun Kz₁ hz =>
      m.six_F4 h37 h39 h312 h510 h5112 hlie hc2 htype hc5 ty h4 hz⟩

end CFSG.Quasithin.H13

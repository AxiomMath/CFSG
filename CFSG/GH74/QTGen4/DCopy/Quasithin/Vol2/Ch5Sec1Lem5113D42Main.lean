module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113D42Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D42Four
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113D42Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_13_lie_D42C_of_F4
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (hF : FactF5113) (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51) (h5112 : Stmt5_1_12_F4)
    (h513 : Stmt5_1_3_F4) (h432 : Stmt4_3_2_F4) : Stmt5_1_13_lie_D42C_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n k hyp hN hk hV hK₁ hKeq hX hhat hlt htype hres
  by_cases hDK : D ⊓ X ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  · exact Or.inl hDK
  right
  have m : Main513 G T M L V H B D K₁ X Kh₁ n := ⟨hyp, hN, hV, hK₁, hKeq, hX, hhat, hlt, hDK⟩

  obtain ⟨hL8, ty⟩ := m.type3D4 hF318 h36 (a38ForSQTK_of_cat h38) h37 h38 hk htype hres
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL8)

  have h4 := m.hat_le_centralizer_d42_F4 h5171 h51 h37 h38 hF h5112 hk heq hL8 ty

  obtain ⟨Kz₁, hz⟩ := m.exists_hat_centralizer h37 h39 h4
  obtain ⟨m', -⟩ := m.atCZ_d42 h37 h39 ty h4 hz
  obtain ⟨htype', hres'⟩ := m'.residual_at_F4 h37 h38 hF h5112 hk heq hL8
  obtain ⟨-, ty'⟩ := m'.type3D4 hF318 h36 (a38ForSQTK_of_cat h38) h37 h38 hk htype' hres'

  obtain ⟨hn2, hA5⟩ := m'.mod_d42_F4 h513 h432 ty' rfl

  obtain ⟨hD4', hres3, -⟩ := ty'
  refine ⟨hL8, hn2, hA5, ?_, ?_⟩
  · rw [← hres3]
    exact m'.lt.le
  · have htr : ∀ A B : Subgroup G, A = B → Is3D4 2 1 (O2Q A) → Is3D4 2 1 (O2Q B) := by
      rintro A B rfl hA
      exact hA
    exact htr _ _ hres3 hD4'

end CFSG.Quasithin.H13

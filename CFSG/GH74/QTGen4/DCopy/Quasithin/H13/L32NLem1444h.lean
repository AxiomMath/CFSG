module

public import CFSG.Quasithin.H13.L32NLem1444h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem143
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_setup4_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest_F4) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hG2 : ¬ LieModel G .G2 0 3 1) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) :
    ∃ (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G), Setup4 G T L V V₂ g D Q₁ Q₂ := by
  obtain ⟨D, Q₁, Q₂, S⟩ :=
    exists_setup3_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hG2 hV₂ hgP hgH
  have hVO := lemma1444Four_of_inputs_F4 h1332 h1334 h1222 h12213 G T L V h hext h32 hG2
  obtain ⟨_, S'⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hTS := h.isSylowTwoOf_l32nH_F4 hV
  have hcardL : Nat.card L = 1344 := by
    rw [S'.card_L_F4, ← hVO, S.card8]
  have hcent : L ⊓ Subgroup.centralizer (V : Set G) = V := by rw [S'.cent_eq_F4, ← hVO]

  obtain ⟨z, a, b, hz, hz1, haV₂, haV₁, hb, hbV₂⟩ := S'.exists_basis_F4
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hzV₂ : z ∈ V₂ := S'.hV2.1 hz
  have ha : a ∈ V := S'.hV2.2.1 haV₂
  obtain ⟨y, hyL, hy3, hyz, hya, -⟩ := S'.exists_rot_F4 hzV ha hb
    (fun h => haV₁ (h ▸ one_mem _)) (fun h => hbV₂ (h ▸ one_mem _))
    (fun h => haV₁ (h ▸ hz)) (fun h => hbV₂ (h ▸ hzV₂)) (fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (h ▸ mul_mem hzV₂ haV₂))
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hbV₂
    rw [← hya]
    simpa using haV₂
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    ((lemma1433Five_of_inputs_F4 h1332 h1334 G T L V h.hyp h.fsu).le hx).1
  exact ⟨D, Q₁, Q₂, S, hVO, hcardL, hcent, S'.TL_F4, pCoreOf_two_le_of_isSylowTwoOf hTS,
    ⟨y, hyL, S'.mem_g1_F4 hz hz1 hyz, hy3, hy1⟩, hNL, hTS.1⟩

end L1444

end CFSG.Quasithin.H13

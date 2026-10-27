module

public import CFSG.Quasithin.H13.L32NLem1444d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_setup2_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest_F4) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) :
    ∃ D : HatModelU (fsuU T V), Setup2 G T L V V₂ g D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨hVe, hV8, hVN, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU_F4 h1222 h12213
  have hZ := zU_eq_F4 h1332 h1334 h1222 h12213 h hext
  have hC := cHat_eq_F4 h1332 h1334 h1222 h12213 h37 h38 h39 h hext
  have hd : Module.finrank (ZMod 2) D.V = 4 := by
    have hcard := D.card_U
    rw [hZ, hV1, h32] at hcard
    have h16 : Nat.card D.V = 2 ^ 4 := by omega
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)
    rw [h16, Nat.card_zmod] at hpow
    exact (Nat.pow_right_injective (le_refl 2) hpow).symm
  obtain ⟨hE, -, ⟨hzUg, -⟩, -⟩ := hRest G T L V h V₂ g hV₂ hgP hgH D hd
  exact ⟨D, h, hext, h32, hV₂, hgP, hgH, hd, hZ, hC, hVe, hV8, hVN, hV1, hE, hzUg⟩

end L1444

end CFSG.Quasithin.H13

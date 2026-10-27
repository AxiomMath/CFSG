module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.H13.A7InvolutionSeed
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.U3Local1332

public section
namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {G : Type} [Group G]

theorem centralizer_le_normalizer_of_uniqueMax_F4 (h331 : Stmt3_3_1_F4) [CFSG.GH74.QTGen4.Finite4 G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQTKE : QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G) {K : Subgroup G}
    (hKmax : quasithinIsMaximalLocal (T : Subgroup G) K)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) {e : G} (he : orderOf e = 2)
    (hKe : K ⊔ T ≤ centralizer ({e} : Set G)) :
    centralizer ({e} : Set G) ≤ normalizer (K : Set G) := by
  have hTsyl : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  obtain ⟨-, h331B⟩ := h331 G T hs hnab hQTKE hTsyl
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h331B K hKmax hKq
  have hcl : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun _ ht l hl => (mem_normalizer_iff.1 (hTK ht) l).1 hl)
      (le_conjClosure K T)
  rw [hcl] at huniq
  obtain ⟨P, hP1, hP2, hPe⟩ := isPLocal_two_centralizer_of_orderOf_eq_two he
  obtain ⟨M', hM', hle⟩ := U3.exists_maxTwoLocal_le (H := centralizer ({e} : Set G))
    ⟨P, hP1, hP2, hPe⟩
  rw [← huniq M' hM' (hKe.trans hle)]
  exact hle

end CFSG.Quasithin.H13.A7

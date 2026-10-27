module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem527
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsBS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stmt5_2_7_U4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n m : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → n = 2 * m → IsU4ExtTwo m (sec52Alpha M L H B D L₂) →
      2 < n ∧ sec52S M H ⊓ L = sec52S M H ⊓ oTwoUpper H ∧
      IsAmalgamOfGroup (sec52AlphaPrime M L H B D) (IsLieOverTwo .PSU 4 m)

theorem stmt5_2_7_of_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0})
    (hF11 : StmtF11_5_2_F4) (h510 : Stmt5_1_10_F4) (h524 : Stmt5_2_4_F4) (h526 : Stmt5_2_6_F4)
    (hbor : Stmt5_2_6_borel_F4) (hU4 : Stmt5_2_7_U4_F4) : Stmt5_2_7_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  obtain ⟨-, hL₂K, -, hO1, hO2, hcases, -, hab⟩ := h526 G T M L V H B D L₂ n hyp
  obtain ⟨hint, -, -, -⟩ := prop_F19_of_listed hF (hF11 G T M L V H B D L₂ n hyp)
  obtain ⟨hG1, hG2, hBig⟩ := hyp.parabolics_eq_F4 h331 hR (hbor G T M L V H B D L₂ n hyp)
  obtain ⟨-, -, ⟨hBS, hDSL₂, -⟩, -⟩ := h524 G T M L V H B D L₂ n hyp
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hN
  subst hL₂K
  set S := sec52S M H with hSdef
  set K := oTwoUpper H with hKdef

  have hTH : T ≤ H := hyp.hStar.1.1
  have hTM : T ≤ M := h.T_le
  have hML : M ≤ Subgroup.normalizer (L : Set G) := h.normal
  have hDL : D ≤ L := hN.2.1.1.trans inf_le_left
  have hBMH : B ≤ M ⊓ H := hN.1.1
  have hBM : B ≤ M := hBMH.trans inf_le_left
  have hBH : B ≤ H := hBMH.trans inf_le_right
  have hBKle : B ≤ K := hBK.1.trans inf_le_right
  have hBK' : B ⊓ K = B := inf_eq_left.mpr hBKle
  have hST : S ≤ T := h.pCoreOf_inf_le hTH
  have hSM : S ≤ M := (pCoreOf_le 2 _).trans inf_le_left
  have hSK : S ⊓ K = T ⊓ K := hyp.toHyp5_1_8.inf_oTwoUpper_eq hBorel
  have hSL : S ⊓ L = T ⊓ L := h.inf_L_eq_F4 h331 hR hyp.hStar

  have hSLK : S ⊓ L = S ⊓ K := by
    rcases hab with ⟨hSL', hSK', -, -⟩ | ⟨m, hn, -, hext, -⟩
    · rw [inf_eq_left.mpr hSL', inf_eq_left.mpr hSK']
    · exact (hU4 G T M L V H B D K n m hyp hn hext).2.1
  have hSLKle : S ⊓ L ≤ K := hSLK ▸ inf_le_right

  have hDSLn : D ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [hSLK]
    exact hDSL₂
  have hBSLn : B ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf hBS (hBM.trans hML)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hSSLn : S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hSM.trans hML)).trans
      Subgroup.inf_normalizer_le_normalizer_inf

  have h2a : L ⊔ (S ⊓ L) ⊔ (B ⊓ K) = L ⊔ B ⊔ D := by
    rw [hBK']
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left)
        (inf_le_right.trans (le_sup_left.trans le_sup_left))) (le_sup_right.trans le_sup_left)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (hDL.trans (le_sup_left.trans le_sup_left))
  have h2b : D ⊔ (S ⊓ L) ⊔ K = K ⊔ B ⊔ D := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_right (hSLKle.trans (le_sup_left.trans le_sup_left)))
        (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (hBKle.trans le_sup_right))
        (le_sup_left.trans le_sup_left)

  have hYB : (L ⊔ B ⊔ D) ⊓ (K ⊔ B ⊔ D) ≤ bigB L K S := by
    refine (inf_le_inf ?_ ?_).trans hint.le
    · rw [← hG1]
      show L ⊔ B ⊔ D ≤ L ⊔ S ⊔ (B ⊓ K)
      rw [hBK']
      exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (hDL.trans (le_sup_left.trans le_sup_left))
    · rw [← hG2]
      show K ⊔ B ⊔ D ≤ D ⊔ S ⊔ K
      exact sup_le (sup_le le_sup_right (hBKle.trans le_sup_right))
        (le_sup_left.trans le_sup_left)

  have hbigN : bigB L K S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [hBig]
    exact sup_le (sup_le hDSLn hSSLn) (inf_le_left.trans hBSLn)
  have hbigL : bigB L K S ⊓ L ≤ D ⊔ (S ⊓ L) := by
    have h1 : bigB L K S ⊓ L ≤ borelOf L S := fun x hx =>
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hbigN (Subgroup.mem_inf.mp hx).1⟩
    have hborL : borelOf L S = borelL T L := by
      unfold borelOf
      rw [hSL]
    rw [hSL, h.borelL_eq_sup hN.2.1]
    exact h1.trans hborL.le
  have h2c : (L ⊔ B ⊔ D) ⊓ (K ⊔ B ⊔ D) = (S ⊓ L) ⊔ B ⊔ D := by
    apply le_antisymm
    · intro y hy
      have hyLB : y ∈ L ⊔ B :=
        (sup_le le_rfl (hDL.trans le_sup_left) : L ⊔ B ⊔ D ≤ L ⊔ B) (Subgroup.mem_inf.mp hy).1
      obtain ⟨l, hl, b, hb, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes (hBM.trans hML)).mp hyLB
      have hbY : b ∈ (L ⊔ B ⊔ D) ⊓ (K ⊔ B ⊔ D) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right hb),
          Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)⟩
      have hlY : l ∈ (L ⊔ B ⊔ D) ⊓ (K ⊔ B ⊔ D) := by
        have := Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hbY)
        simpa using this
      have hlD : l ∈ D ⊔ (S ⊓ L) := hbigL (Subgroup.mem_inf.mpr ⟨hYB hlY, hl⟩)
      have hle : D ⊔ (S ⊓ L) ≤ (S ⊓ L) ⊔ B ⊔ D :=
        sup_le le_sup_right (le_sup_left.trans le_sup_left)
      exact Subgroup.mul_mem _ (hle hlD) (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
    · refine le_inf ?_ ?_
      · exact sup_le (sup_le (inf_le_right.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left)) le_sup_right
      · exact sup_le (sup_le (hSLKle.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left)) le_sup_right

  have hSLp : IsPGroup 2 ↥(S ⊓ L) := (pCoreOf_isPGroup 2 (M ⊓ H)).to_le inf_le_left
  have h2f : S ⊓ L = pCoreOf 2 ((L ⊔ B ⊔ D) ⊓ (K ⊔ B ⊔ D)) := by
    rw [h2c, sup_assoc, sup_comm B D]
    exact (pCoreOf_sup_eq_of_odd hSLp (sup_le hDSLn hBSLn)
      (odd_card_sup hN.2.2 hN.2.1.2.1 hN.1.2.1)).symm

  have hMH : B ⊔ T = M ⊓ H :=
    sup_eq_of_isHall_of_isSylowTwoOf hN.1 (h.isSylowTwoOf (le_inf hTM hTH))
  have hO₂le : ∀ X : Subgroup G, B ⊔ T ≤ X → pCoreOf 2 X ≤ S := by
    intro X hX
    have h1 : pCoreOf 2 X ≤ T :=
      F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf (le_sup_right.trans hX))
    have h3 : M ⊓ H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := by
      rw [← hMH]
      exact hX.trans (le_normalizer_pCoreOf 2 X)
    exact le_pCoreOf_of_le_normalizer 2 (h1.trans (le_inf hTM hTH)) h3 (pCoreOf_isPGroup 2 X)
  have h3a : pCoreOf 2 L = pCoreOf 2 (L ⊔ B ⊔ D ⊔ T) := by
    have hXM : L ⊔ B ⊔ D ⊔ T ≤ M := sup_le (sup_le (sup_le h.L_le hBM) (hDL.trans h.L_le)) hTM
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2
        ((pCoreOf_le 2 L).trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
        (hXM.trans (hML.trans (normalizer_le_normalizer_pCoreOf 2 L))) (pCoreOf_isPGroup 2 L)
    · have hBTX : B ⊔ T ≤ L ⊔ B ⊔ D ⊔ T :=
        sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left)) le_sup_right
      have hG1X : sec52G1 M L H B K ≤ L ⊔ B ⊔ D ⊔ T := by
        show L ⊔ S ⊔ (B ⊓ K) ≤ L ⊔ B ⊔ D ⊔ T
        exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
          (hST.trans le_sup_right))
          (inf_le_left.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      have hSG1 : S ≤ sec52G1 M L H B K := le_sup_right.trans le_sup_left
      rw [← hO1]
      exact le_pCoreOf_of_le_normalizer 2 ((hO₂le _ hBTX).trans hSG1)
        (hG1X.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have h3b : pCoreOf 2 K = pCoreOf 2 (K ⊔ B ⊔ D ⊔ T) := by
    have hXN : K ⊔ B ⊔ D ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
      sup_le (sup_le (sup_le Subgroup.le_normalizer (hBH.trans (le_normalizer_oTwoUpper H)))
        hyp.D_le) (hTH.trans (le_normalizer_oTwoUpper H))
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2
        ((pCoreOf_le 2 K).trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
        (hXN.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
    · have hBTX : B ⊔ T ≤ K ⊔ B ⊔ D ⊔ T :=
        sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left)) le_sup_right
      have hG2X : sec52G2 M H D K ≤ K ⊔ B ⊔ D ⊔ T := by
        show D ⊔ S ⊔ K ≤ K ⊔ B ⊔ D ⊔ T
        exact sup_le (sup_le (le_sup_right.trans le_sup_left) (hST.trans le_sup_right))
          (le_sup_left.trans (le_sup_left.trans le_sup_left))
      have hSG2 : S ≤ sec52G2 M H D K := le_sup_right.trans le_sup_left
      rw [← hO2]
      exact le_pCoreOf_of_le_normalizer 2 ((hO₂le _ hBTX).trans hSG2)
        (hG2X.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  refine ⟨?_, ⟨h2a, h2b, h2c, hSL, hSLK.trans hSK, h2f⟩, h3a, h3b⟩

  by_cases hext : ∃ m : ℕ, n = 2 * m ∧ IsU4ExtTwo m (sec52Alpha M L H B D K)
  · obtain ⟨m, hn, hx⟩ := hext
    obtain ⟨h2n, -, hamal⟩ := hU4 G T M L V H B D K n m hyp hn hx
    exact Or.inr (Or.inl ⟨m, hn, h2n, hamal⟩)
  · have hSLe : S ≤ L := by
      rcases hab with ⟨h1, -, -, -⟩ | ⟨m, hn, -, hx, -⟩
      · exact h1
      · exact absurd ⟨m, hn, hx⟩ hext
    have hα : sec52AlphaPrime M L H B D = sec52Alpha M L H B D K := by
      show RankTwoAmalgam.ofSubgroups (L ⊔ (S ⊓ L) ⊔ (B ⊓ K)) (D ⊔ (S ⊓ L) ⊔ K) =
        RankTwoAmalgam.ofSubgroups (L ⊔ S ⊔ (B ⊓ K)) (D ⊔ S ⊔ K)
      rw [inf_eq_left.mpr hSLe]
    rw [hα]
    rcases hcases with ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩ |
        ⟨m, hn, h2n, h6, -⟩ | ⟨hn, h7, -⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h2))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h4))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h5))))
    · rcases h6 with h6 | h6
      · exact Or.inr (Or.inl ⟨m, hn, h2n, h6⟩)
      · exact absurd ⟨m, hn, h6⟩ hext
    · exact Or.inr (Or.inr ⟨hn, h7⟩)

end CFSG.Quasithin.H13

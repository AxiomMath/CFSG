module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113M4F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113FourCZ
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Pos

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem not_thompsonJ_le_centralizer_of_F4 (h5171 : A5.Stmt5_1_7_one_F4)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n) (hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)))
    {Q : Subgroup G} (hQe : IsElemAbelian 2 Q) (hQT : Q ≤ T)
    (hYQ : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer (Q : Set G))
    (hKQ : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (Q : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (Q : Set G) := by
  intro hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hKhperf : ⁅conjClosure Kh₁ T, conjClosure Kh₁ T⁆ = conjClosure Kh₁ T :=
    A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1)
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hOT : pCoreOf 2 (conjClosure Kh₁ T ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le hTY

  have hQZ := le_omegaOneCenterOf_thompsonJ hQe hQT hJ
  have hBC : baum T ≤ (conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer (Q : Set G) :=
    le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hQZ hx))

  have hC2 := isPGroup_sup_inf_centralizer hKhperf hs h.sylow.1 hTKh hYQ hKQ
  have hCY : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer
      (((conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) :=
    fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYQ hy⟩
  have hCO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCY hC2

  have hbeq := baum_eq_of_baum_le (hBC.trans hCO) hOT
  have hYB : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer (baum T : Set G) := by
    rw [← hbeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (normalizer_le_normalizer_baum _)

  have hNM := h5171 G T L M h.simple h.nonabelian h.qtke h.sylow h.maximal h.faithful
    ⟨n, h.two_le, h.lie⟩ h.maxTwoLocal h.T_le h.L_le h.normal
  have hKM : oTwoUpper H ≤ M := (m.lt.le.trans (le_sup_left.trans hYB)).trans hNM
  apply m.hyp.hStar.2.1
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (h.isSylowTwoOf m.hyp.hStar.1.1)]
  exact sup_le hKM h.T_le

end Main513

theorem stmt5_1_13_four_m4_of_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51) (h510 : Stmt5_1_10_F4) :
    Stmt5_1_13_four_m4_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA _ V' hV' _ hnat h64
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := by
    obtain ⟨e'⟩ := hA
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e'.isSimpleGroup
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hmax hZ hA
  obtain ⟨-, -, D₃, hD₃, h3, hD₃K, hDK, -⟩ := ty
  obtain ⟨hpos, hmove⟩ := m.d3_stab_zero_five_six_F4 h510 hc5 pk.r0 pk.p0 hD₃ h3 hD₃K hDK
  have hJU := m.not_thompsonJ_le_centralizer_of_F4 h5171 hs pk.elemAbelian (pk.U_le.trans pk.le_T)
    (sup_le pk.le_normalizer pk.T_le_normalizer) pk.not_le_centralizer
  exact not_le_normalizer_thompsonJ_of_six pk h64 hJU h3 hpos hmove
    ((hD₃.trans inf_le_left).trans (m.le_normalizer_thompsonJ_of_nat hV' hnat))

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourA7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem commutator_thompsonJ_ne_bot_F4 (h5171 : A5.Stmt5_1_7_one_F4)
    (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hmax : quasithinIsMaximalLocal T (conjClosure Kh₁ T))
    (hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)))
    (hZ : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    IsTwoReducedIn (conjClosure Kh₁ T ⊔ T)
        (conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T)) ∧
      ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer
        ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
          Set G) ∧
      ⁅conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T), thompsonJ T⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hKhperf : ⁅conjClosure Kh₁ T, conjClosure Kh₁ T⁆ = conjClosure Kh₁ T :=
    A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1)
  have hTKh : T ≤ Subgroup.normalizer (conjClosure Kh₁ T : Set G) :=
    le_normalizer_conjClosure Kh₁ T
  have hTY : IsSylowTwoOf T (conjClosure Kh₁ T ⊔ T) := h.isSylowTwoOf le_sup_right
  have hchar : CharTwo (conjClosure Kh₁ T ⊔ T) :=
    charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, hmax.1.2.2.2⟩
  obtain ⟨hWO, hWel, hWred⟩ := conjClosure_isTwoReducedIn_of_charTwo hTY hchar le_rfl
  have hOT : pCoreOf 2 (conjClosure Kh₁ T ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le hTY
  have hWT : conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) ≤ T :=
    (hWO.trans inf_le_left).trans hOT
  have hYW := hWred.2.1
  have hKhW : ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := fun hle =>
    hZ (hle.trans (Subgroup.centralizer_le fun x hx => le_conjClosure _ _ hx))
  refine ⟨hWred, hKhW, fun hJ => ?_⟩
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hJ

  have hWZ := le_omegaOneCenterOf_thompsonJ hWel hWT hJ
  have hBC : baum T ≤ (conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) :=
    le_inf (inf_le_left.trans le_sup_right)
      (inf_le_right.trans (Subgroup.centralizer_le fun x hx => hWZ hx))

  have hC2 := isPGroup_sup_inf_centralizer hKhperf hs h.sylow.1 hTKh hYW hKhW
  have hCY : conjClosure Kh₁ T ⊔ T ≤ Subgroup.normalizer
      (((conjClosure Kh₁ T ⊔ T) ⊓ Subgroup.centralizer
        ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
          Set G) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hYW hy⟩
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

theorem stmt5_1_13_four_A7_of_F4
    (h5171 : A5.Stmt5_1_7_one_F4) (hFF : FactFFJ2M23) : Stmt5_1_13_four_A7_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := IsA7J2M23.isSimpleGroup ty.1
  rcases ty.1 with hA7 | hJM | hJM
  · exact hA7
  all_goals
    exfalso
    obtain ⟨hW, hKhW, hJ⟩ := m.commutator_thompsonJ_ne_bot_F4 h5171 hmax hs hZ
    apply hJ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hFF G (conjClosure Kh₁ T) T _ (A3.conjClosure_perfect (perfect_of_mem_cComp m.hat.1))
      (by first | exact Or.inl hJM | exact Or.inr hJM) (h.isSylowTwoOf le_sup_right)
      (le_normalizer_conjClosure Kh₁ T) (InternalSec.sqtkGroup_of_localSQTK hloc hmax.1.2.2.2) hW
      hKhW

end CFSG.Quasithin.H13

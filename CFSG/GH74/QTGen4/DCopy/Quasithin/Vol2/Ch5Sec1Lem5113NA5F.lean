module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113FourNA5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Pos
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NA5K
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NA5L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_13_four_nA5_four_of_F4 (h5171 : A5.Stmt5_1_7_one_F4)
    (h51 : AsB51) (h510 : Stmt5_1_10_F4) : Stmt5_1_13_four_nA5_four_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 ty hmax hZ hA hLJ V' hV' hZV' hJV hn2 hsplit hS5
    hmodS5 h16
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hs : IsSimpleGroup (O2Q (conjClosure Kh₁ T)) := by
    obtain ⟨e'⟩ := hA
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e'.isSimpleGroup
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hmax hZ hA
  obtain ⟨-, -, D₃, hD₃, h3, hD₃K, hDK, -⟩ := ty
  obtain ⟨hpos, -⟩ := m.d3_stab_zero_five_six_F4 h510 hc5 pk.r0 pk.p0 hD₃ h3 hD₃K hDK

  obtain ⟨-, -, hJWc⟩ := m.commutator_thompsonJ_ne_bot_F4 h5171 hmax hs hZ
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (conjClosure Kh₁ T ⊔ T) : Subgroup G) :
        Set G) := fun hle => hJWc (by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle)
  have hDJ := le_normalizer_thompsonJ_of_four h51 pk
    (InternalSec.sqtkGroup_of_localSQTK hloc hmax.1.2.2.2) hJW h16 (fun d hd => (hD₃ hd).2) hpos

  have hD := m.nota.2.1
  have hD3 : Nat.card D = 3 := by
    have h1 := (h.isCyclic_card_of_isHall l2TorusFact hD).2
    rw [hn2] at h1
    exact h1
  have hDeq : D₃ = D :=
    Subgroup.eq_of_le_of_card_ge (hD₃.trans inf_le_left) (by rw [hD3, h3])

  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTLT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hsyl : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTLT le_sup_left (sup_le Subgroup.le_normalizer hTL)
  have hred := hV'.isTwoReducedIn
  have hV'T : V' ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans (F7.isSylowTwoOf_pCoreOf_le hTLT)
  have hVL : ⁅V', L⁆ ≤ V' :=
    A7ZK.commutator_le_left_of_le_normalizer (le_sup_left.trans hred.2.1)
  have hWe : IsElemAbelian 2 ⁅V', L⁆ := A7ZK.isElemAbelian_of_le hVL hred.2.2.1
  have hJW' : ¬ thompsonJ T ≤ Subgroup.centralizer ((⁅V', L⁆ : Subgroup G) : Set G) := by
    intro hle
    apply hJV
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hsplit.2]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp (hle hj) x hx).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_iff.mp hx.2 j (Subgroup.mem_sup_right (B6.thompsonJ_le T hj))
  exact not_le_normalizer_thompsonJ_of_s5 h.maximal.1.2.1.2.1
    (isSimpleGroup_of_lieModel_PSL2 h.lie) h.sylow.1 hTL hsyl hWe (hVL.trans hV'T) hmodS5 hJW'
    (hD.1.trans inf_le_left) (hD.1.trans inf_le_right) hD3 (hDeq ▸ hDJ)

end CFSG.Quasithin.H13

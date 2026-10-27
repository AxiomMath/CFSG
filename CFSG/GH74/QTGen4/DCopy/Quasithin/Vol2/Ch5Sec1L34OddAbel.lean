module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34InputsOddAb
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem516

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.SL2Model
open scoped MatrixGroups commutatorElement

theorem stmt5_1_17_abelian_of_F4 (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first_F4) (h126 : A126TwoFact) (hnb : Stmt5_1_17_noBlock_F4) :
    Stmt5_1_17_abelian_F4 := by
  intro G _ _ T M L V H B D n s _ H₁ hH₁ hH₁N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hA := s.almostSpecialHyp hI hF hH₁ hH₁N
  have hTH₁ : T ≤ H₁ := s.hyp.hyp.hStar.1.1.trans (le_sup_left.trans hH₁)
  by_contra hU

  have hUO : ¬ conjClosure V H₁ ≤ pCoreOf 2 (L ⊔ T) := fun hle => hU
    (isElemAbelian_conjClosure_of_le_centralizer s.elemAbelian
      (hle.trans ((hh.sup_inf_centralizer_eq s.hyp.module).ge.trans inf_le_right)))
  have hyp2 : AlmostSpecialL2Hyp n V (quasithinOmegaOneCenter T ⊓ V) L T H₁ :=
    ⟨hA, by have := s.one_le_n; omega, s.V_eq_conjClosure, s.isNaturalSL2Module hI, hUO⟩

  obtain ⟨g, hgL, hgN⟩ : ∃ g ∈ L,
      g ∉ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) := by
    by_contra hcon
    have hall : ∀ l ∈ L,
        l ∈ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) :=
      fun l hl => by_contra fun hn => hcon ⟨l, hl, hn⟩
    have hle : V ≤ quasithinOmegaOneCenter T ⊓ V :=
      calc V = conjClosure (quasithinOmegaOneCenter T ⊓ V) L := s.V_eq_conjClosure
        _ ≤ quasithinOmegaOneCenter T ⊓ V := conjClosure_le fun l hl z hz =>
          (Subgroup.mem_normalizer_iff.mp (hall l hl) z).mp hz
    exact hA.irred.1.not_ge hle

  set U := conjClosure V H₁ with hUdef
  set I := U ⊔ rconj U g with hIdef
  set S := pCoreOf 2 I with hSdef
  set S₂ := U ⊓ rconj U g with hS₂def
  have h2 : I = L ⊔ U := hyp2.G23_two hgL hgN
  have h4 := hyp2.G23_four hgL hgN
  have hVS₂ : V ≤ S₂ := h4.1
  have hIS : I ≤ Subgroup.normalizer (S : Set G) := h4.2.2.2.2.2
  have h5 : ⁅S₂, I⁆ ≤ V := (hyp2.G23_five hgL hgN).1
  obtain ⟨⟨r, β, φ, -, hβk, -, hφk, hφe⟩, -, -, hWS⟩ :=
    hyp2.G23_six (U := U) (I := I) (S := S) (W := U ⊓ S) rfl hgL hgN rfl rfl rfl
      G1.theorem_G_1_3_two
  obtain ⟨D₀⟩ := hyp2.natural.nonempty_data
  have hSO : S ≤ pCoreOf 2 (L ⊔ T) :=
    (⟨hyp2, D₀⟩ : L2Setting n V (quasithinOmegaOneCenter T ⊓ V) L T H₁).pCoreOf_I_le_O hgL hgN

  have hN1M : Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G) ≤
      Subgroup.normalizer (oTwoUpper H : Set G) := by
    have hloc : IsTwoLocal
        (Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G)) :=
      ⟨_, s.Z₁_ne_bot, hA.isPGroup_V₁, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hHM' : H ≤ M' := ((le_sup_left.trans hH₁).trans hH₁N).trans hle
    rw [← (s.hyp.isUniqueM_F4 h5114).2 M' ⟨hM', hHM'⟩]
    exact hle

  have hLI : L ≤ I := by rw [h2]; exact le_sup_left
  have hDI : D ≤ I := (s.hyp.notation59.2.1.1.trans inf_le_left).trans hLI
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := hDI.trans hIS
  have hDodd : Odd (Nat.card D) := s.hyp.notation59.2.1.2.1
  have hcardD : Nat.card D = 2 ^ n - 1 := (hh.isCyclic_card_of_isHall hF s.hyp.notation59.2.1).2
  have hodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd => Odd.of_dvd_nat hDodd (by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _)
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 I
  have hcop : Nat.Coprime (Nat.card D) (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hDodd)
  have hSsolv : Group.IsSolvable ↥S := by
    have := hS2.isNilpotent
    infer_instance

  have hfac := coprime_le_commutator_sup_inf_centralizer hDS hSsolv hcop
  have hidem := coprime_commutator_commutator_eq hDS hcop

  have hCS : S ⊓ Subgroup.centralizer (D : Set G) ≤ S₂ := by
    rintro c ⟨hcS, hcC⟩
    obtain ⟨d, hdD, hd1'⟩ : ∃ d ∈ D, d ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one D with h0 | h0
      · exfalso
        have h1 : Nat.card D = 1 := by rw [h0, Subgroup.card_bot]
        have h4' : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hh.two_le
        omega
      · exact h0
    have hβ : β ⟨d, hDI hdD⟩ ≠ 1 := fun h1 =>
      hd1' (eq_one_of_odd_orderOf_of_mem hS2 ((hβk ⟨d, hDI hdD⟩).mp h1) (hodd d hdD))
    have hβodd : Odd (orderOf (β ⟨d, hDI hdD⟩)) := Odd.of_dvd_nat (hodd d hdD) (by
      have := orderOf_map_dvd β ⟨d, hDI hdD⟩
      rwa [Subgroup.orderOf_mk] at this)
    have hfix := hφe ⟨d, hDI hdD⟩ ⟨c, hcS⟩ ⟨c, hcS⟩ (by
      show c = d * c * d⁻¹
      rw [Subgroup.mem_centralizer_iff.mp hcC d hdD, mul_inv_cancel_right])
    have hw : ∀ j, Multiplicative.toAdd (φ ⟨c, hcS⟩) j = 0 := by
      intro j
      by_contra hj
      have hj' := congrFun (congrArg Multiplicative.toAdd hfix) j
      simp only [toAdd_ofAdd] at hj'
      have hAA := sl2_mul_self_eq_one_of_smul_eq hj hj'.symm
      apply hβ
      have h1 : orderOf (β ⟨d, hDI hdD⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hAA)
      exact orderOf_eq_one_iff.mp
        (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.mpr hβodd) h1)
    have h1 : φ ⟨c, hcS⟩ = 1 := by
      rw [← ofAdd_toAdd (φ ⟨c, hcS⟩), show Multiplicative.toAdd (φ ⟨c, hcS⟩) = 0 from funext hw,
        ofAdd_zero]
    exact (hφk ⟨c, hcS⟩).mp h1

  have hST : S ≤ T := hSO.trans (pCoreOf_two_le_of_isSylowTwoOf hA.sylow_LT)
  have hDC : D ≤ centralizerModO2 (oTwoUpper H) := s.D_le_centralizer
  have hMC := normalizer_le_normalizer_centralizerModO2 (oTwoUpper H)
  have hSDS : ⁅S, D⁆ ≤ S := (Subgroup.le_normalizer_iff_commutator_le_left).mp hDS
  have hSDC : ⁅S, D⁆ ≤ centralizerModO2 (oTwoUpper H) :=
    Subgroup.commutator_le.mpr fun x hx d hd => by
      have h1 : x * d * x⁻¹ ∈ centralizerModO2 (oTwoUpper H) :=
        (Subgroup.mem_normalizer_iff.mp (hMC (s.hyp.T_le_Mp (hST hx))) d).mp (hDC hd)
      rw [commutatorElement_def]
      exact (centralizerModO2 (oTwoUpper H)).mul_mem h1
        ((centralizerModO2 (oTwoUpper H)).inv_mem (hDC hd))

  have hD3 : ¬ 3 ∣ Nat.card D := by
    rw [hcardD]
    exact s.not_three_dvd
  have hcop6 : Nat.Coprime (Nat.card D) 6 := by
    have h3 : Nat.Coprime (Nat.card D) 3 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3)
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hDodd) h3
  have hA126 : ⁅S, D⁆ ≤ pCoreOf 2 (centralizerModO2 (oTwoUpper H)) := by
    refine h126 G (centralizerModO2 (oTwoUpper H)) D ⁅S, D⁆ hDC ?_ hSDC (hS2.to_le hSDS) hidem
      s.solvable ?_ ?_
    · exact le_antisymm (oTwoUpper_le D) fun d hd => mem_oTwoUpper_of_odd hd (hodd d hd)
    · intro p hp hp2
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
        (centralizerModO2_le_normalizer (oTwoUpper H))).trans
          (s.hyp.pRank_Mp_le_two_F4 h5114 hp hp2)
    · refine le_antisymm ((Subgroup.closure_le D).mpr fun x hx => hx.1) fun d hd => ?_
      refine Subgroup.subset_closure ⟨hd, Nat.Coprime.coprime_dvd_left ?_ hcop6⟩
      rw [← Subgroup.orderOf_mk d hd]
      exact orderOf_dvd_natCard _

  have hH₁M : H₁ ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hH₁N.trans hN1M
  have hMP : Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (centralizerModO2 (oTwoUpper H)) : Set G) :=
    hMC.trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hPT : pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≤ T :=
    (le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 _).trans (centralizerModO2_le_normalizer (oTwoUpper H))) hMP
      (pCoreOf_isPGroup 2 _)).trans
      (pCoreOf_two_le_of_isSylowTwoOf (hh.isSylowTwoOf s.hyp.T_le_Mp))
  have hPQ : pCoreOf 2 (centralizerModO2 (oTwoUpper H)) ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 (hPT.trans hTH₁) (hH₁M.trans hMP) (pCoreOf_isPGroup 2 _)
  have hUQ : U ≤ pCoreOf 2 H₁ :=
    le_pCoreOf_of_le_normalizer 2 (hA.G22_three.1.trans hTH₁) (le_normalizer_conjClosure V H₁)
      (hA.isPGroup_T.to_le hA.G22_three.1)
  have hSQ : S ≤ pCoreOf 2 H₁ :=
    hfac.trans (sup_le (hA126.trans hPQ) (hCS.trans (inf_le_left.trans hUQ)))

  have hSU : S ≤ U := fun x hx => ((hWS x hx).mpr fun u hu =>
    hVS₂ (almostSpecial_commutator_mem_of_mem_pCoreOf hA hu (hSQ hx)).2).1
  have hSS₂ : S ≤ S₂ := fun x hx =>
    ⟨hSU hx, mem_rconj.mpr (hSU ((Subgroup.mem_normalizer_iff.mp (hIS (hLI hgL)) x).mp hx))⟩

  have hOL : pCoreOf 2 L ≤ S := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLI) ?_ (pCoreOf_isPGroup 2 L)
    rw [h2]
    exact sup_le (le_normalizer_pCoreOf 2 L)
      ((hA.G22_three.1.trans hA.T_le_normL).trans (normalizer_le_normalizer_pCoreOf 2 L))
  exact hnb G T M L V H B D n s ((Subgroup.commutator_mono (hOL.trans hSS₂) hLI).trans h5)

end CFSG.Quasithin.H13

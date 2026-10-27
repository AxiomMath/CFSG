module

public import CFSG.CGT.PushingUpLit.BHS6.BlockFacts
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.PushingUpLit.BHS6.SixThree

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

omit [Finite Γ] in
theorem pCoreOf_le_self (G : Subgroup Γ) : pCoreOf 2 G ≤ G := CFSG.openPCoreOf_le 2 G

omit [Finite Γ] in
theorem le_normalizer_pCoreOf_self' (G : Subgroup Γ) :
    G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Γ) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 G

theorem pCoreOf_le_normalizer_of_isBTBlock (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    pCoreOf 2 G ≤ Subgroup.normalizer (E : Set Γ) := by
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  refine six_three hT hE (pCoreOf_le_self G)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G) ?_
  exact sup_le (((inf_le_left : baum T ≤ T).trans hT'.1).trans (le_normalizer_pCoreOf_self' G))
    (hE.le.trans (le_normalizer_pCoreOf_self' G))

theorem charTwo_of_isBTBlock (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    CharTwo E :=
  two_two_normalizes hG hE.le (pCoreOf_le_normalizer_of_isBTBlock hT hE)

theorem commutator_pCoreOf_le (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    ⁅E, pCoreOf 2 G⁆ ≤ pCoreOf 2 E := by
  have hQN := pCoreOf_le_normalizer_of_isBTBlock hT hE
  have hEQ : E ≤ Subgroup.normalizer (pCoreOf 2 G : Set Γ) :=
    hE.le.trans (le_normalizer_pCoreOf_self' G)
  have h1 : ⁅E, pCoreOf 2 G⁆ ≤ E := Subgroup.le_normalizer_iff_commutator_le_left.mp hQN
  have h2 : ⁅E, pCoreOf 2 G⁆ ≤ pCoreOf 2 G := Subgroup.le_normalizer_iff_commutator_le_right.mp hEQ
  have hnorm : ((E ⊓ pCoreOf 2 G).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hEQ hg⟩
  have hp : IsPGroup 2 ↥(E ⊓ pCoreOf 2 G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G).to_le inf_le_right
  exact (le_inf h1 h2).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (E ⊓ pCoreOf 2 G) E
      inf_le_left hnorm hp)

theorem commutator_pCoreOf_eq_bot (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    ⁅pCoreOf 2 E, pCoreOf 2 G⁆ = ⊥ := by
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  set Q : Subgroup Γ := pCoreOf 2 G with hQ
  set W : Subgroup Γ := pCoreOf 2 E with hW
  set C : Subgroup Γ := W ⊓ Subgroup.centralizer (E : Set Γ) with hC
  have hQ2 : IsPGroup 2 ↥Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G
  have hW2 : IsPGroup 2 ↥W := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E
  have hQN : Q ≤ Subgroup.normalizer (E : Set Γ) := pCoreOf_le_normalizer_of_isBTBlock hT hE
  have hEQ : E ≤ Subgroup.normalizer (Q : Set Γ) := hE.le.trans (le_normalizer_pCoreOf_self' G)
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hQW : Q ≤ Subgroup.normalizer (W : Set Γ) :=
    hQN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hE.elemAbelian.1
  have hWne : W ≠ ⊥ := pCoreOf_ne_bot hE hchar
  have hNW : ⁅W, Q⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hQW
  have hNE : ∀ g ∈ E, ∀ n ∈ (⁅W, Q⁆ : Subgroup Γ), g * n * g⁻¹ ∈ (⁅W, Q⁆ : Subgroup Γ) :=
    fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_commutator (hEW hg) (hEQ hg)) n).mp hn
  have hCW : C ≤ W := inf_le_left
  have hCz : C ≤ Subgroup.centralizer (E : Set Γ) := inf_le_right
  have hNC_inv : ∀ g ∈ E, ∀ x ∈ (⁅W, Q⁆ ⊔ C : Subgroup Γ),
      g * x * g⁻¹ ∈ (⁅W, Q⁆ ⊔ C : Subgroup Γ) := by
    intro g hg x hx
    obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup'
      (fun n hn c hc => hWab n (hNW hn) c (hCW hc)) hx
    have hgc : g * c = c * g := Subgroup.mem_centralizer_iff.mp (hCz hc) g hg
    have : g * (n * c) * g⁻¹ = (g * n * g⁻¹) * c := by
      calc g * (n * c) * g⁻¹ = (g * n * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * n * g⁻¹) * c := by rw [hgc]; group
    rw [this]
    exact mul_mem ((le_sup_left : ⁅W, Q⁆ ≤ ⁅W, Q⁆ ⊔ C) (hNE g hg n hn))
      ((le_sup_right : C ≤ ⁅W, Q⁆ ⊔ C) hc)
  have hirr := pCoreOf_irred hE hchar (⁅W, Q⁆ ⊔ C) le_sup_right (sup_le hNW hCW) hNC_inv
  rcases hirr with h1 | h1
  ·
    have hNC : ⁅W, Q⁆ ≤ C := le_sup_left.trans h1.le
    have hWE : ⁅W, E⁆ = W := hE.perfect
    have hEQW : ⁅E, Q⁆ ≤ W := commutator_pCoreOf_le hT hE
    have ha : ⁅⁅E, Q⁆, W⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_mono hEQW le_rfl).trans ?_)
      exact (commutator_self_eq_bot hWab).le
    have hb : ⁅⁅Q, W⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Q W, eq_bot_iff, Subgroup.commutator_le]
      intro x hx e he
      have hxc : x ∈ Subgroup.centralizer (E : Set Γ) := hCz (hNC hx)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hxc e he).symm
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := W) (H₂ := E) (H₃ := Q) ha hb
    rwa [hWE] at h3
  ·
    exfalso
    have hWN : W ≤ ⁅W, Q⁆ := by
      have hcomm : ⁅W, E⁆ ≤ ⁅W, Q⁆ := by
        rw [Subgroup.commutator_le]
        intro x hx e he
        have hx' : x ∈ (⁅W, Q⁆ ⊔ C : Subgroup Γ) := by rw [h1]; exact hx
        obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup'
          (fun n hn c hc => hWab n (hNW hn) c (hCW hc)) hx'
        have hec : e * c = c * e := Subgroup.mem_centralizer_iff.mp (hCz hc) e he
        have h3 : c * e * c⁻¹ = e := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hec.symm
        have h4 : ⁅n * c, e⁆ = n * (e * n⁻¹ * e⁻¹) := by
          calc ⁅n * c, e⁆ = n * (c * e * c⁻¹) * n⁻¹ * e⁻¹ := by
                simp only [commutatorElement_def]; group
            _ = n * e * n⁻¹ * e⁻¹ := by rw [h3]
            _ = n * (e * n⁻¹ * e⁻¹) := by group
        rw [h4]
        exact mul_mem hn (hNE e he n⁻¹ (inv_mem hn))
      have hWE : ⁅W, E⁆ = W := hE.perfect
      rwa [hWE] at hcomm
    exact lt_irrefl _ (lt_of_lt_of_le (commutator_lt_of_isPGroup hW2 hQ2 hQW hWne) hWN)

theorem six_four_a (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    opResidual 2 (E ⊔ pCoreOf 2 G) = E ∧ blockW E ≤ omegaOneCenterOf (pCoreOf 2 G) := by
  refine ⟨opResidual_sup_eq (opResidual_eq_of_isBTBlock hE)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 G)
    (pCoreOf_le_normalizer_of_isBTBlock hT hE), ?_⟩
  rw [blockW_eq_pCoreOf hE]
  have hc := commutator_pCoreOf_eq_bot hG hT hE
  have hWG : pCoreOf 2 E ≤ G := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E).trans hE.le
  intro w hw
  have hwc : w ∈ Subgroup.centralizer (pCoreOf 2 G : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : ⁅w, q⁆ ∈ (⁅pCoreOf 2 E, pCoreOf 2 G⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator hw hq
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hwQ : w ∈ pCoreOf 2 G := hG ⟨hWG hw, hwc⟩
  refine Subgroup.subset_closure ⟨⟨hwQ, hwc⟩, hE.elemAbelian.2 w hw⟩

theorem six_four_d (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    ⁅blockW E, thompsonJ T⁆ ≠ ⊥ := by
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hchar : CharTwo E := charTwo_of_isBTBlock hG hT hE
  rw [blockW_eq_pCoreOf hE]
  set W : Subgroup Γ := pCoreOf 2 E with hW
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := hE.elemAbelian.1
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hWab hE.elemAbelian.2
  have hWne : W ≠ ⊥ := pCoreOf_ne_bot hE hchar
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hWE : ⁅W, E⁆ = W := hE.perfect
  have hWT : W ≤ T := by
    have h1 := (six_four_a hG hT hE).2
    rw [blockW_eq_pCoreOf hE] at h1
    exact (h1.trans (C1GN.omegaOneCenterOf_le_self _)).trans hT'.pCoreOf_le
  intro hJ
  have hWJ : W ≤ Subgroup.centralizer (thompsonJ T : Set Γ) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 : ⁅w, j⁆ ∈ (⁅W, thompsonJ T⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hw hj
    rw [hJ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hWA : ∀ A, IsMaxElemAbelian T A → W ≤ A := by
    intro A hA
    have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
    have hAC : A ≤ Subgroup.centralizer (W : Set Γ) := fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp (hWJ hw) a (hAJ ha)).symm
    have hel : IsElemAbelian 2 (A ⊔ W) := isElemAbelian_sup' hA.2.1 hWe fun a ha w hw =>
      (Subgroup.mem_centralizer_iff.mp (hAC ha) w hw).symm
    have hle : Nat.card ↥(A ⊔ W) ≤ Nat.card ↥A := hA.2.2 _ (sup_le hA.1 hWT) hel
    have heq : A ⊔ W = A := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
    exact heq ▸ le_sup_right
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  have hWJ' : W ≤ thompsonJ T := (hWA A₀ hA₀).trans (B6.le_thompsonJ hA₀)
  have hWZ : W ≤ omegaOneCenterOf (thompsonJ T) := by
    intro w hw
    refine Subgroup.subset_closure ⟨⟨hWJ' hw, ?_⟩, hE.elemAbelian.2 w hw⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hWJ hw) y hy
  have hBW : ⁅baum T, W⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb w hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hb.2 w (hWZ hw)).symm
  have h1 : ⁅⁅E, W⁆, baum T⁆ = ⊥ := by
    rw [Subgroup.commutator_comm E W, hWE, Subgroup.commutator_comm]
    exact hBW
  have h2 : ⁅⁅W, baum T⁆, E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm W (baum T), hBW]
    exact (Subgroup.commutator_bot_left E)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := baum T) (H₂ := E)
    (H₃ := W) h1 h2
  rw [Subgroup.commutator_comm (baum T) E, hE.commutator] at h3
  apply hWne
  rw [← hWE, Subgroup.commutator_comm]
  exact h3

end CFSG.CGT.PushingUpLit.BHS6

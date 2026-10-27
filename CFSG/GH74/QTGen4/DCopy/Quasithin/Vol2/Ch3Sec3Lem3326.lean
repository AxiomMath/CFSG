module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3326

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_26_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h25 : Stmt3_3_25_F4) : Stmt3_3_26_F4 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hshort : IsShort2 L := by
    rcases (h25 G T M L D h).1 with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQN : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hUV := h.blockU_le_vPlus h38 h39 hshort hTL
  have hQU := Hyp331.commutator_qL_le_blockU hshort hTL
  have hVd : ∀ d ∈ D, d ∈ M → CFSG.conjugate (vPlus L T) d = vPlus L T := by
    intro d hdD hdM
    have hZ : d ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
      Hyp331.normalizer_le_normalizer_of_characteristic (L246C127.omegaOneCenter_le_self T)
        (L246C127.characteristic_omegaOneCenter T) (h.DN hdD)
    have hMp : d ∈ Subgroup.normalizer (mPlus L T : Set G) := by
      rw [← h.toSetup331.eq_normalizer h38 h39]
      exact hdM
    exact A38.map_conj_eq_iff.mpr (inv_mem (mem_normalizer_conjClosure hZ hMp))
  by_contra hcon
  have hall : ∀ d ∈ D, CFSG.conjugate (vPlus L T) d ≤ qL L T := by
    intro d hd
    by_cases hdM : d ∈ M
    · rw [hVd d hd hdM]
      exact hVQ
    · by_contra hle
      exact hcon ⟨d, hd, hdM, hle⟩
  set W := conjClosure (vPlus L T) (T ⊔ D) with hWdef
  have hWQ : W ≤ qL L T := by
    refine conjClosure_le fun x hx v hv => ?_
    obtain ⟨s, hs, d, hd, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer h.DN).mp hx
    have hdv : d * v * d⁻¹ ∈ qL L T := by
      refine hall d⁻¹ (D.inv_mem hd) ⟨v, hv, ?_⟩
      simp [MulAut.conj_apply]
    have := (Subgroup.mem_normalizer_iff.mp (hQN (Subgroup.mem_sup_right hs)) _).mp hdv
    simpa [mul_assoc] using this
  have hVne : vPlus L T ≠ ⊥ := by
    intro hb
    apply h.not_L_le_centralizer h38 h39
    rw [hb]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  have hWne : W ≠ ⊥ := fun hb => hVne (le_bot_iff.mp (hb ▸ le_conjClosure _ _))
  have hWN : T ⊔ D ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure _ _
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_le fun l hl w hw => ?_
    have hc : ⁅l, w⁆ ∈ W := by
      have h1 : ⁅l, w⁆ ∈ ⁅qL L T, L⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hl (hWQ hw)
      exact le_conjClosure _ _ (hUV (hQU h1))
    have e : l * w * l⁻¹ = ⁅l, w⁆ * w := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hc hw
  exact h.not_le_normalizer h38 h39 hWne (hWQ.trans hQLT)
    (sup_le hLW (le_sup_left.trans hWN)) (le_sup_right.trans hWN)

end CFSG.Quasithin.H13

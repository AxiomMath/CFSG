module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5E49
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace L1295B

section Act

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T V L V₁ Vp H : Subgroup G}

end Act

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ} {V₁ K₁ : Subgroup G}

theorem false_of_e49_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1)
    (hU : IsMulCommutative ↥(u128 V V₁)) (hLK : lOne L V₁ ≤ K₁)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hHz : IsHzOne T L V₁ (K₁ ⊔ T)) (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hF := L1286.hypF98_of_abelian_F4 h1222 h37 h38 h39 hcx.hyp hV₁ hU hHz
  have hF1 := hF.toHypF91
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) :=
    hV₁.2.2.trans (normalizer_le_of_lOne_le_F4 h1222 h37 h38 hcx.hyp hn hV₁ hLK hK)
  have hT2 : IsPGroup 2 T := hcx.hyp.hyp.sylow.1
  have hKH : K₁ ≤ K₁ ⊔ T := le_sup_left
  have hHK : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  have hUT := hF1.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))) := commGroupOfElemAbelian hUT
  have hsq : ∀ w : ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))), w ^ 2 = 1 :=
    fun w => Subtype.ext (by simpa using hUT.2 w w.2)
  set φ := actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) with hφ
  have hXeq : autOn (tildeOf V₁ (K₁ ⊔ T)) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) =
      ((K₁ ⊔ T).subgroupOf (K₁ ⊔ T)).map φ :=
    autOn_tilde_eq_map_actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) le_rfl
  have hKeq : autOn (tildeOf V₁ K₁) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) =
      (K₁.subgroupOf (K₁ ⊔ T)).map φ :=
    autOn_tilde_eq_map_actH hF1.H_normalizes_V₁ (le_normalizer_conjClosure V (K₁ ⊔ T)) hKH
  set X := autOn (tildeOf V₁ (K₁ ⊔ T)) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) with hX
  set Kp := autOn (tildeOf V₁ K₁) (tildeOf V₁ (conjClosure V (K₁ ⊔ T))) with hKp

  have hKpX : Kp ≤ X := by
    rw [hKeq, hXeq, Subgroup.subgroupOf_self]
    exact Subgroup.map_mono le_top
  have hXK :
      X ≤ Subgroup.normalizer (Kp : Set (MulAut ↥(tildeOf V₁ (conjClosure V (K₁ ⊔ T))))) := by
    have hn : (K₁.subgroupOf (K₁ ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
    rw [hKeq, hXeq, Subgroup.subgroupOf_self, ← Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.le_normalizer_map φ
  have hpow : ∀ x ∈ X, ∃ j : ℕ, x ^ 2 ^ j ∈ Kp := by
    intro x hx
    rw [hXeq] at hx
    obtain ⟨h, -, rfl⟩ := hx
    obtain ⟨j, hj⟩ := L1286.exists_two_pow_mem_of_mem_sup hT2 hTK h.2
    refine ⟨j, ?_⟩
    rw [hKeq, ← map_pow]
    exact ⟨h ^ 2 ^ j, Subgroup.mem_subgroupOf.2 (by simpa using hj), rfl⟩
  have hEKp : IsSL27OverE49 ↥Kp := by
    obtain ⟨e⟩ := nonempty_mulEquiv_autOn hF1 hKH hHK
    exact IsSL27OverE49.of_mulEquiv e hE
  have hO2 : pCoreOf 2 X = ⊥ :=
    pCoreOf_autOn_eq_bot_of_isTwoReducedIn (lemma12_8_4_one_F4 h1222 hcx.hyp hV₁ hHz).G22_four

  obtain ⟨-, B, -, hBQ⟩ := hF.F916_3
  obtain ⟨⟨hB2, hBr⟩, hBc⟩ := hBQ
  have hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    kq_le_iff.2 ⟨_, hB2, commSeries_eq_bot_of_le (by norm_num) hBc, hBr⟩
  have hne : qhatOf X ≠ ⊤ := fun h => by
    rw [h] at hq
    exact absurd hq (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have hr2 : r ≤ 2 := by
    rw [← hr] at hq
    exact_mod_cast hq

  obtain ⟨A, hA⟩ := QhatStar_nonempty hr.symm hr2
  obtain ⟨-, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hD := commutator_pCoreOf_seven_ne_bot hKpX hXK hpow hEKp hO2 hA2.le hA2.ne_bot
    hA2.isElemAbelian2.2
  have h7 := (D2_13 hsq hr.symm hA (p := 7) (by norm_num) rfl hD).1
  omega

end L1295B

end CFSG.Quasithin.H13

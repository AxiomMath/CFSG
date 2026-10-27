module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Set
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Inv
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248
open scoped IsMulCommutative commutatorElement

namespace S1248

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V U : Subgroup G} {z : G}

theorem exists_facts_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hpre : Pre1242_F4) (hS : Setting G T L V U) :
    ∃ z, Facts G T L V U z := by
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hS.cx hS.quot
  exact ⟨z, hS, hf, hypE61_of_cx_F4 h331 h1222 h323 h3228 hS.cx hf.isElemAbelian
    hS.cx.hyp.irrPlus.2.1 hf.le_T hf.T_le hf.normalizes⟩

namespace Facts

variable (hF : Facts G T L V U z)
include hF

theorem inf_centralizer_eq_F4 (hinv : InvolFact1248_F4) {W : Subgroup G}
    (hW : W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) :
    Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) := by
  have hWU : W ≤ U := by
    rcases hW with rfl | ⟨h, -⟩
    · exact le_rfl
    · exact h
  have hWV : W ≤ V := hWU.trans hF.setting.le
  refine le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hWV))
  rintro m ⟨hmM, hmW⟩
  refine ⟨hmM, ?_⟩
  set C := V ⊓ Subgroup.centralizer ({m} : Set G) with hCdef
  have hWC : W ≤ C := fun w hw => ⟨hWV hw, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hmW w hw)⟩
  have hzC : z ∈ C := by
    refine ⟨hF.z_mem, ?_⟩
    show z ∈ Subgroup.centralizer ({m} : Set G)
    have hmz : m ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [hF.centralizer_z_eq]
      exact hmM
    rw [Subgroup.mem_centralizer_singleton_iff] at hmz ⊢
    exact hmz.symm
  have hzW : z ∉ W := fun h => hF.z_not_mem (hWU h)
  have hWltC : W < C := lt_of_le_of_ne hWC fun h => hzW (h ▸ hzC)
  have hCV : C ≤ V := inf_le_left

  have hWidx : W.relIndex V = 2 ∨ W.relIndex V = 4 := by
    rcases hW with rfl | ⟨h, h2⟩
    · exact Or.inl hF.setting.hyper
    · right
      rw [← Subgroup.relIndex_mul_relIndex W U V h hF.setting.le, h2, hF.setting.hyper]
  have hmul := Subgroup.relIndex_mul_relIndex W C V hWC hCV
  have hWC2 : 2 ≤ W.relIndex C := by
    have h0 : W.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : W.relIndex C ≠ 1 := fun h => (not_le_of_gt hWltC) (Subgroup.relIndex_eq_one.1 h)
    omega
  have hCidx : C.relIndex V = 1 ∨ C.relIndex V = 2 := by
    have h0 : C.relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases hWidx with h | h <;> rw [h] at hmul
    · left
      nlinarith
    · rcases (Nat.lt_or_ge (C.relIndex V) 3) with h3 | h3
      · omega
      · nlinarith
  have hVC : V ≤ C → m ∈ Subgroup.centralizer (V : Set G) := by
    intro h
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (h hv).2
  rcases hCidx with h1 | h2
  · exact hVC (Subgroup.relIndex_eq_one.1 h1)
  · by_contra hmV

    have hmVn : m ∈ Subgroup.normalizer (V : Set G) := by
      rw [hF.normalizer_V_eq]
      exact hmM
    have hA : (C.subgroupOf V).index = 2 := h2
    have hCinv : ∀ c ∈ C, m * c * m⁻¹ = c := by
      intro c hc
      have := Subgroup.mem_centralizer_singleton_iff.1 hc.2
      rw [← this]
      group
    have hm2 : m ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hmv : m * v * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hmVn v).1 hv
      by_cases hvC : v ∈ C
      · rw [pow_two]
        have h1 := hCinv v hvC
        calc v * (m * m) = m * (m * v * m⁻¹) * m⁻¹ * (m * m) := by rw [h1, h1]
          _ = m * m * v := by group
      · have hmvC : m * v * m⁻¹ ∉ C := by
          intro h'
          apply hvC
          have := hCinv _ h'
          have e : v = m⁻¹ * (m * v * m⁻¹) * m := by group
          rw [e]
          have e2 : m⁻¹ * (m * v * m⁻¹) * m = m * v * m⁻¹ := by
            calc m⁻¹ * (m * v * m⁻¹) * m = m⁻¹ * (m * (m * v * m⁻¹) * m⁻¹) * m := by rw [this]
              _ = m * v * m⁻¹ := by group
          rw [e2]
          exact h'

        have hcC : m * v * m⁻¹ * v⁻¹ ∈ C := by
          have hmem := (Subgroup.mul_mem_iff_of_index_two hA
            (a := (⟨m * v * m⁻¹, hmv⟩ : ↥V)) (b := (⟨v, hv⟩ : ↥V)⁻¹)).2
          have h3 : (⟨m * v * m⁻¹, hmv⟩ : ↥V) * (⟨v, hv⟩ : ↥V)⁻¹ ∈ C.subgroupOf V := by
            apply hmem
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            simp only [Subgroup.coe_inv]
            rw [Subgroup.inv_mem_iff]
            exact iff_of_false hmvC hvC
          exact h3
        set c := m * v * m⁻¹ * v⁻¹ with hc
        have hc2 : c ^ 2 = 1 := hF.cx.sq _ hcC.1
        have hcm : m * c * m⁻¹ = c := hCinv _ hcC

        rw [pow_two]
        have key : m * m * v * (m * m)⁻¹ = v := by
          have e1 : m * m * v * (m * m)⁻¹ = (m * c * m⁻¹) * (c * v) := by
            rw [hc]
            group
          rw [e1, hcm, ← mul_assoc, ← sq, hc2, one_mul]
        calc v * (m * m) = m * m * v * (m * m)⁻¹ * (m * m) := by rw [key]
          _ = m * m * v := by group
    exact hinv G T L V hF.setting.cx hF.setting.quot m hmM hmV hm2 h2

theorem mem_gamma_F4 (hinv : InvolFact1248_F4) {W : Subgroup G}
    (hW : W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) :
    W ∈ E6.gammaE64 V (Subgroup.normalizer (L : Set G)) := by
  have hWU : W ≤ U := by
    rcases hW with rfl | ⟨h, -⟩
    · exact le_rfl
    · exact h
  have hWV : W ≤ V := hWU.trans hF.setting.le
  refine ⟨hWV, ?_, ?_, ?_⟩
  ·
    intro hbot
    have h4 := hF.four_lt_card_V
    have hWidx : W.relIndex V ≤ 4 := by
      rcases hW with rfl | ⟨h, h2⟩
      · rw [hF.setting.hyper]
        norm_num
      · rw [← Subgroup.relIndex_mul_relIndex W U V h hF.setting.le, h2, hF.setting.hyper]
    rw [hbot, Subgroup.relIndex_bot_left] at hWidx
    omega
  · intro hle
    apply hF.setting.escape
    rw [hF.normalizer_V_eq]
    exact (Subgroup.centralizer_le hWU).trans hle
  · rw [hF.inf_centralizer_eq_F4 hinv hW]
    exact twoPrimeResidual_le_self _

theorem lemma115Hyp_F4 (hinv : InvolFact1248_F4) {W : Subgroup G}
    (hW : W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) :
    QuasithinUnique.Lemma115Hyp (Subgroup.centralizer (W : Set G))
      (T ⊓ Subgroup.centralizer (V : Set G)) (Subgroup.normalizer (L : Set G)) z := by
  have hΓ := hF.mem_gamma_F4 hinv hW
  have hWV : W ≤ V := hΓ.1
  have hyp := hF.setting.cx.hyp
  have hSyl := E6.e6_5_one hF.e61 hΓ
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hWC : W ≤ Subgroup.centralizer (W : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 (hF.V_le_centralizer (hWV hw)) v (hWV hv)
  exact QuasithinUnique.lemma116 hyp.qtke.2.1 (B := W) (T := T)
    (hT2.to_le (hWV.trans hF.cx.le_T)) hΓ.2.1 (sup_le hWC le_rfl)
    (Subgroup.centralizer_le_normalizer _) ⟨hSyl.1, hSyl.2.1, hSyl.2.2⟩
    ⟨le_top, hT2, by
      change ¬ 2 ∣ T.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hyp.sylow.2⟩
    inf_le_left (hF.cx.le_T hF.z_mem) hF.z_mem_centralizer_T hF.z_ne_one hF.z_sq hF.e61.inM.1
    (by rw [hF.centralizer_z_eq])

end Facts

end S1248

theorem oddInv1248_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h3228 : Stmt3_2_2_eight) (hpre : Pre1242_F4) (hinv : InvolFact1248_F4) : OddInv1248_F4 := by
  intro G _ _ T L V U hS z' hz' hz'1 W hW x hx
  obtain ⟨z, hF⟩ := S1248.exists_facts_F4 h331 h1222 h323 h3228 hpre hS
  rw [hF.eq_of_mem_inf hz' hz'1]
  have h := (hF.lemma115Hyp_F4 hinv hW).inverts_oddCoreIn x hx
  have hzinv : z⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hF.z_sq]
  rw [hzinv] at h ⊢
  exact h

end CFSG.Quasithin.H13

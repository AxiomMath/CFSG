module

public import CFSG.Quasithin.H13.A5S136l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136f

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma115Hyp_Gv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) :
    Lemma115Hyp (Subgroup.centralizer ({S.v12} : Set G)) S.Tv S.G1 S.z := by
  have hTG1 : T ≤ S.G1 := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have := S.conj_z_of_mem_T ht
      calc t * S.z = t * S.z * t⁻¹ * t := by group
        _ = S.z * t := by rw [this])
  have hzGv : S.z ∈ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.z, S.z_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  have hG1 : InH T S.G1 := ⟨hTG1, fun h => S.z_ne_one (by
    have := S.V1_le_pCoreOf_G1 (Subgroup.mem_zpowers S.z)
    rw [h] at this
    exact Subgroup.mem_bot.mp this)⟩
  have hvGv : S.v12 ∈ Subgroup.centralizer ({S.v12} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine
    { pCore_ne_bot := fun h => S.v12_ne_one (by
        have := S.v12_mem_pCoreOf le_rfl hvGv
        rw [h] at this
        exact Subgroup.mem_bot.mp this)
      sylow := S.isSylowTwoOf_centralizer_F4 h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1
      charTwo := S.charTwo_of_inH hG1
      pCore_M_ne_bot := hG1.2
      le := inf_le_left.trans hTG1
      centralizer_le := fun x hx => ?_
      centralizer_z_le := le_rfl
      z_ne_one := S.z_ne_one
      z_mem := ⟨S.V_le_T S.z_mem_V, hzGv⟩
      z_central := ?_
      z_sq := S.z_sq }
  ·
    have hv : S.v12 ∈ pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G) ⊓ S.G1) :=
      S.v12_mem_pCoreOf inf_le_left ⟨hvGv, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val
          (S.elemAbelian_V.1.is_comm.comm ⟨S.v12, S.v12_mem_V⟩ ⟨S.z, S.z_mem_V⟩))⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 S.v12 hv).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]

theorem oddCoreIn_Gv_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) :
    oddCoreIn (Subgroup.centralizer ({S.v12} : Set G)) = ⊥ := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hHyp := S.lemma115Hyp_Gv_F4 h1222 h517

  have hVGv : V ≤ Gv := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨u, hu⟩ ⟨S.v12, S.v12_mem_V⟩))
  have hLvGv : S.Lv ≤ Gv := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact (oTwoUpper_le _).trans inf_le_right
  obtain ⟨hcomm, hcomm2⟩ := S.commutator_V_Lv
  have hWV : S.pre W23 ≤ V := S.pre_le_V _
  have hWel : IsElemAbelian 2 (S.pre W23) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => S.elemAbelian_V.2 x (hWV hx)⟩
    have hc : (a : G) * b = b * a :=
      congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨a, hWV a.2⟩ ⟨b, hWV b.2⟩)
    exact Subtype.ext hc
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (pCoreOf p Gv) ≤ 2 := by
    intro p hp hp2
    have hO2 : pCoreOf 2 Gv ≠ ⊥ := hHyp.pCore_ne_bot
    have hsqt : CFSG.IsStronglyQuasithin ↥Gv := (hloc Gv hO2).1
    have h1 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp hsqt) p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    rw [pRank_top_subtype] at h1
    exact (CFSG.SectionRank.pRank_mono hp.one_lt (CFSG.LieType.BorelTits.pCoreOf_le p Gv)).trans
      h1
  have hWC : S.pre W23 ≤ Subgroup.centralizer (fusionOddCoreOf Gv : Set G) :=
    a126_one hLvGv S.opResidual_two_Lv (hWV.trans hVGv) (S.isPGroup_V.to_le hWV) hcomm2 hrank
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hWel)

  have hzv : S.z * S.v12⁻¹ ∈ S.pre W23 := by
    refine S.mem_pre.2 ⟨V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V), ?_⟩
    have e : (⟨S.z * S.v12⁻¹, V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V)⟩ : ↥V) =
        ⟨S.z, S.z_mem_V⟩ * (⟨S.v12, S.v12_mem_V⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_z, S.psi_v12]
    exact W4_E12_mem
  refine eq_bot_iff.mpr fun y hy => ?_
  have hyGv : y ∈ Gv := oddCoreIn_le Gv hy
  have hc1 : (S.z * S.v12⁻¹) * y = y * (S.z * S.v12⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp (hWC hzv) y hy).symm
  have hc2 : S.v12 * y = y * S.v12 := (Subgroup.mem_centralizer_singleton_iff.mp hyGv).symm
  have hzy : S.z * y = y * S.z := by
    have e1 : S.z = (S.z * S.v12⁻¹) * S.v12 := by group
    rw [e1, mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]

  have hinv := hHyp.inverts_oddCoreIn y hy
  have hyy : y = y⁻¹ := by
    rw [← hinv]
    calc y = S.z⁻¹ * (S.z * y) := by group
      _ = S.z⁻¹ * (y * S.z) := by rw [hzy]
      _ = S.z⁻¹ * y * S.z := by group
  have hy2 : y ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hyy]
    exact mul_inv_cancel y

  have hodd : Odd (orderOf y) := by
    have h1 := Subgroup.orderOf_dvd_natCard (oddCoreIn Gv) hy
    exact Odd.of_dvd_nat (odd_card_oddCoreIn Gv) h1
  have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have h2 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h2)

theorem exists_component_Gv_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : ¬ CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    ∃ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) := by
  by_contra hE
  push Not at hE
  exact hF (DoubleA3.charTwo_of_no_component hE (S.oddCoreIn_Gv_F4 h1222 h517))

end Setting

@[expose] def Elim1366AB_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseA K S.z ∨ Lemma115CaseB K S.z) → False

@[expose] def Elim1366CD_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseC K S.z ∨ Lemma115CaseD K S.z) → False

@[expose] def Elim1366EF_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V),
    IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ K : Subgroup G, IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)) →
      (Lemma115CaseE K S.z ∨ Lemma115CaseF K S.z) → False

theorem lemma1366_of_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hlist : Lemma115_3_List) (hAB : Elim1366AB_F4) (hCD : Elim1366CD_F4) (hEF : Elim1366EF_F4) :
    Lemma1366_F4 := by
  intro G _ _ T L V S hab
  by_contra hF
  have : IsSimpleGroup G := S.h13.simple
  obtain ⟨K, hK⟩ := S.exists_component_Gv_F4 h1222 h517 hF
  have hcases := hlist G S.h13.simple S.h13.nonabelian (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke)
    _ _ _ _ (S.lemma115Hyp_Gv_F4 h1222 h517) K hK
  rcases hcases with h | h | h | h | h | h
  · exact hAB G T L V S hab K hK (Or.inl h)
  · exact hAB G T L V S hab K hK (Or.inr h)
  · exact hCD G T L V S hab K hK (Or.inl h)
  · exact hCD G T L V S hab K hK (Or.inr h)
  · exact hEF G T L V S hab K hK (Or.inl h)
  · exact hEF G T L V S hab K hK (Or.inr h)

end CFSG.Quasithin.H13.A5

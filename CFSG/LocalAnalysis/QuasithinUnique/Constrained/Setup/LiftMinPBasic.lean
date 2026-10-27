module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Helpers

variable {G : Type} [Group G]

theorem le_normalizer_of_char_char {R S C : Subgroup G} (hSR : S ≤ R)
    (hS : (S.subgroupOf R).Characteristic) (hCS : C ≤ S) (hCchar : (C.subgroupOf S).Characteristic) :
    R ≤ Subgroup.normalizer (C : Set G) := by
  have hCR : C ≤ R := hCS.trans hSR
  have hchR : (C.subgroupOf R).Characteristic :=
    C1GN.characteristic_subgroupOf_trans hSR hCS hS hCchar
  have key : ∀ r ∈ R, ∀ x ∈ C, r * x * r⁻¹ ∈ C := by
    intro r hr x hx
    have h1 := Subgroup.characteristic_iff_map_eq.mp hchR (MulAut.conj (⟨r, hr⟩ : R))
    have h2 : (MulAut.conj (⟨r, hr⟩ : R)) ⟨x, hCR hx⟩ ∈ C.subgroupOf R := by
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h2
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key r hr x, fun hx => by simpa [mul_assoc] using key r⁻¹ (R.inv_mem hr) _ hx⟩

variable [Finite G]

theorem minPBasic_of_data {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F)
    (hno : ∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Rc : Set G))
    (hbase : BaseData R V) {T P : Subgroup G} (hSyl : IsSylowTwoOf (baum R) T)
    (hT : T ≤ oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) (hmin : IsMinimalOver (baum R) T M P) :
    MinPBasic R M P := by
  have hSR : baum R ≤ R := inf_le_left
  have hRM : R ≤ M := hS.max.1
  have hSM : baum R ≤ M := hSR.trans hRM
  have hPT : P ≤ T := hmin.le
  have hSP : baum R ≤ P := hmin.S_le
  have hPnotM : ¬ P ≤ M := hmin.not_le
  have hPLS : P ≤ oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R := hPT.trans hT
  have hV0 : V ≠ ⊥ := by
    intro h
    apply hS.thompson_ne
    rw [h]
    exact Subgroup.commutator_bot_right _
  have hVS : V ≤ baum R := hbase.V_le_Q.trans hbase.Q_le_S
  have hS0 : baum R ≠ ⊥ := fun h => hV0 (eq_bot_iff.2 (hVS.trans h.le))
  have hSchar : ((baum R).subgroupOf R).Characteristic := C1GN.characteristic_baum R
  have hRS : R ≤ Subgroup.normalizer (baum R : Set G) := by
    have hnormal : ((baum R).subgroupOf R).Normal := inferInstance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).1 hnormal
  have hSS : ((baum R).subgroupOf (baum R)).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hNS : ¬ (⊤ : Subgroup G) ≤ Subgroup.normalizer (baum R : Set G) :=
    hno (baum R) hS0 le_rfl hSS
  have hNM : Subgroup.normalizer (baum R : Set G) ≤ M :=
    hS.max.2.2 _ hRS (lt_top_iff_ne_top.2 fun h => hNS h.ge)
  have hgen : P ⊔ R = ⊤ := by
    by_contra hne
    exact hPnotM (le_sup_left.trans
      (hS.max.2.2 (P ⊔ R) le_sup_right (lt_top_iff_ne_top.2 hne)))
  refine ⟨?_, B6.isSylowTwoOf_mono hSyl hSP hPT, ?_, ?_, hgen, ?_, ?_⟩
  · exact lt_of_le_of_ne hSP fun h => hPnotM (h.symm.le.trans hSM)
  · intro hn
    exact hPnotM (((Subgroup.normal_subgroupOf_iff_le_normalizer hSP).1 hn).trans hNM)
  · intro Y hSY hYP
    by_contra hYM
    exact hYP.ne (hmin.minimal Y hSY hYP.le hYM)
  · intro C hCS hC0 hCchar hPC
    refine hno C hC0 hCS hCchar ?_
    exact hgen.symm.le.trans (sup_le hPC (le_normalizer_of_char_char hSR hSchar hCS hCchar))
  ·
    have hQP : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ P :=
      hbase.Q_le_S.trans hSP
    have hQn : ((pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R)).subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2
        (hPLS.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    have hQO : pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ≤ pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 hQP hQn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    intro x hx
    have hxC : x ∈ (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) ⊓
        Subgroup.centralizer (pCoreOf 2 (oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) : Set G) :=
      ⟨hPLS hx.1, Subgroup.mem_centralizer_iff.2 fun q hq =>
        Subgroup.mem_centralizer_iff.1 hx.2 q (hQO hq)⟩
    exact hQO (hbase.charTwo hxC)

end Helpers

section Props

theorem natMinPBasicProp
    : NatMinPBasicProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hbase hY hmin
  have hbaum := even_SL2_natural_baumann ctx.setting ctx.comps ctx.natural
  have hT : oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R ≤
      oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R := sup_le_sup_right hY.le_L _
  have hSyl := B6.isSylowTwoOf_mono hbaum.sylow
    (le_sup_right : baum R ≤ oddOrderSubgroup (rhoPreimage V ⊤ ctx.hX (Lc i)) ⊔ baum R) hT
  exact minPBasic_of_data ctx.setting ctx.noChar hbase hSyl hT hmin

theorem delMinPBasicProp : DelMinPBasicProp := by
  intro G _ _ R M V n F _ r Lc ctx i Fs P _ hbase _ hH0 hmin
  exact minPBasic_of_data ctx.setting ctx.noChar hbase.base hH0.sylow
    (inf_le_left : delH0 R V ctx.hX Fs ≤ oddOrderSubgroup (⊤ : Subgroup G) ⊔ baum R) hmin

end Props

end CFSG.QuasithinUnique.Setup.Lift

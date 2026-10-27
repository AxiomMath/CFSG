module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTData
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCov
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrPerf
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure IPart (H P T U I : Subgroup G) : Prop where
  good : L52Two.GoodI1 H U I
  le_L : I ≤ pLayerOf 2 (centralizer (U : Set G))
  norm_P : I ≤ normalizer (P : Set G)
  T_norm : T ≤ normalizer (I : Set G)
  perf : ⁅I, I⁆ = I
  surj : (I.subgroupOf (pLayerOf 2 (centralizer (U : Set G)))).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(pLayerOf 2 (centralizer (U : Set G))))) = ⊤

variable {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G} {g : G}
  {X Y : Subgroup G}

omit [Finite G] in
theorem conj_mem_inf3 {A B C : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) (hC : x ∈ normalizer (C : Set G)) {b : G}
    (hb : b ∈ A ⊓ B ⊓ C) : x * b * x⁻¹ ∈ A ⊓ B ⊓ C :=
  ⟨⟨(mem_normalizer_iff.mp hA b).mp hb.1.1, (mem_normalizer_iff.mp hB b).mp hb.1.2⟩,
    (mem_normalizer_iff.mp hC b).mp hb.2⟩

theorem exists_iPart {t : G} {q : ℕ} (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hU : UPart z k S T Tstar t q) : ∃ I : Subgroup G, IPart H P T (L52Two.U4 z t) I := by
  set U : Subgroup G := L52Two.U4 z t with hUdef
  set C : Subgroup G := centralizer (U : Set G) with hC
  set L : Subgroup G := pLayerOf 2 C with hL
  set X : Subgroup G := H ⊓ C with hX
  set B : Subgroup G := H ⊓ L with hB
  set BP : Subgroup G := H ⊓ normalizer (P : Set G) ⊓ L with hBP
  have hU2 : IsPGroup 2 ↥U := hU.udata.isPGroup_U4
  have hUH : U ≤ H := U_le_H h hU
  have hLC : L ≤ C := sSup_le fun K hK => hK.1
  have hCL : C ≤ normalizer (L : Set G) := L52Two.le_normalizer_pLayerOf C
  have hTC : T ≤ C := T_le_centralizer hU
  have hXO : ∀ x ∈ X, ∀ o ∈ pPrimeCoreOf 2 L, x * o * x⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro x hx o ho
    have hx' : x ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) :=
      LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥L)
        (hCL hx.2)
    exact (Subgroup.mem_normalizer_iff.1 hx' o).1 ho
  have hXB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun x hx b hb =>
    ⟨H.mul_mem (H.mul_mem hx.1 hb.1) (H.inv_mem hx.1),
      (Subgroup.mem_normalizer_iff.1 (hCL hx.2) b).1 hb.2⟩
  have hTBP : ∀ x ∈ T, ∀ b ∈ BP, x * b * x⁻¹ ∈ BP := fun x hx b hb =>
    conj_mem_inf3 (Subgroup.le_normalizer (T_le h hx)) (Subgroup.le_normalizer (T_norm h hx))
      (hCL (hTC hx)) hb
  have hBL : B ≤ L := inf_le_right
  have hBPL : BP ≤ L := inf_le_right
  have hBPB : BP ≤ B := inf_le_inf_right L inf_le_left
  have hsimple : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) :=
    L52Two.I1.isSimpleGroup_of_isL2 hU.q_gt hU.L2
  have hqs : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    L52Two.I1.isQuasisimple_of_isL2 hU.q_gt hU.L2
  have heven : Even (Nat.card (↥L ⧸ pPrimeCore 2 ↥L)) :=
    ComponentClassification.Burgoyne.even_card_of_isQuasisimple hqs
  have hZ : Subgroup.center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ :=
    GH74.GLS.Stage2.Local.P27.S45.center_eq_bot_of_isL2 hU.L2
  have hcovP : L ≤ BP ⊔ pPrimeCoreOf 2 L :=
    L52Two.covering_of_normalizes hU.Tstar_eq (T_isPGroup hU)
      (hTC.trans (L52Two.le_normalizer_pLayerOf C)) (cover h)
  set I₁ : Subgroup G := perfCore B with hI₁
  set I : Subgroup G := perfCore BP with hI
  obtain ⟨I', hI'BP, hI'perf, -, hI'surj⟩ :=
    L52Two.I1.exists_perfect_core (X := T) hBPL hTBP hqs.1 hcovP
  have hI'I : I' ≤ I := le_perfCore hI'BP hI'perf
  have hII₁ : I ≤ I₁ := le_perfCore ((perfCore_le BP).trans hBPB) (commutator_perfCore BP)
  have hIL : I ≤ L := (perfCore_le BP).trans hBPL
  have hI₁L : I₁ ≤ L := (perfCore_le B).trans hBL
  have hIH : I ≤ H := (perfCore_le BP).trans (inf_le_left.trans inf_le_left)
  have hI₁H : I₁ ≤ H := (perfCore_le B).trans inf_le_left
  have hIsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤ := by
    rw [eq_top_iff, ← hI'surj]
    exact Subgroup.map_mono (Subgroup.comap_mono hI'I)
  have hI₁surj : (I₁.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤ := by
    rw [eq_top_iff, ← hIsurj]
    exact Subgroup.map_mono (Subgroup.comap_mono hII₁)
  have hI₁X' : I₁ ≤ X := le_inf hI₁H (hI₁L.trans hLC)
  have hI₁X : ∀ x ∈ X, ∀ i ∈ I₁, x * i * x⁻¹ ∈ I₁ := by
    intro x hx i hi
    have hxB : x ∈ normalizer (B : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro b
      refine ⟨fun hb => hXB x hx b hb, fun hb => ?_⟩
      have h1 := hXB x⁻¹ (X.inv_mem hx) _ hb
      have e : x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b := by group
      rwa [e] at h1
    exact conj_mem_perfCore hxB hi
  have hTI : T ≤ normalizer (I : Set G) := by
    intro x hx
    apply mem_normalizer_perfCore
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => hTBP x hx b hb, fun hb => ?_⟩
    have h1 := hTBP x⁻¹ (T.inv_mem hx) _ hb
    have e : x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b := by group
    rwa [e] at h1
  refine ⟨I, ⟨hIH, fun i hi u hu => ?_, ?_, ?_, ?_⟩, hIL,
    fun x hx => ((perfCore_le BP) hx).1.2, hTI, commutator_perfCore BP, hIsurj⟩
  · exact Subgroup.mem_centralizer_iff.1 (hLC (hIL hi)) u hu
  · have hqI := L52Two.I1.isQuasisimple_image hI₁L hI₁X' hXO hI₁X hsimple heven hqs hI₁surj
    have hlayer : I₁ ≤ pLayerOf 2 X :=
      L52Two.I1.le_pLayerOf_of_perfect_normal hI₁X' hI₁X (commutator_perfCore B) hqI
    exact (L52Two.barIn_mono hII₁).trans (L52Two.I1.barIn_le_layer_of_le_pLayerOf
      (hlayer.trans (L52Two.I1.pLayerOf_inf_centralizer_le hUH hU2)))
  · exact L52Two.I1.exists_isFourSubgroup_of_cover hU.q_odd hIL hU.L2 hIsurj
  · intro i hi hcomm
    exact L52Two.I1.odd_orderOf_of_comm_mem hIL hIH hsimple heven hZ hIsurj hi hcomm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

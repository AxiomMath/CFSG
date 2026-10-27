module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBUQ1

theorem le_normalizer_inf {G : Type} [Group G] {X A C : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hC : X ≤ Subgroup.normalizer (C : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hA hg) x) (Subgroup.mem_normalizer_iff.mp (hC hg) x)

theorem commutator_le_of_le {G : Type} [Group G] {X E T : Subgroup G} (hX : X ≤ E)
    (hT : T ≤ Subgroup.normalizer (E : Set G)) : ⁅X, T⁆ ≤ E := by
  rw [Subgroup.commutator_le]
  intro x hx t ht
  have h1 : t * x⁻¹ * t⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hT ht) x⁻¹).mp (E.inv_mem (hX hx))
  have e : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  rw [e]
  exact E.mul_mem (hX hx) h1

theorem dsFrattini_le_of_relIndex_two {G : Type} [Group G] {Q R : Subgroup G}
    (hR : R.relIndex Q = 2) : dsFrattini Q ≤ R := by
  have hcoat : IsCoatom (R.subgroupOf Q) := by
    apply Subgroup.isCoatom_of_index_prime
    have h2 : (R.subgroupOf Q).index = 2 := hR
    rw [h2]
    exact Nat.prime_two
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_subgroupOf.mp (frattini_le_coatom hcoat hy)

theorem le_of_sup_dsFrattini_eq {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (hM : M ≤ Q) (h : M ⊔ dsFrattini Q = Q) : Q ≤ M := by
  have hA : M.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hAtop : M.subgroupOf Q = ⊤ := frattini_nongenerating hA
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Q) ∈ M.subgroupOf Q := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem dsOmega1_centerOf_le {G : Type} [Group G] (Q : Subgroup G) :
    dsOmega1 (centerOf Q) ≤ Q :=
  (Subgroup.closure_le _).2 fun _ hx => (inf_le_left : centerOf Q ≤ Q) hx.1

end DSBUQ1

theorem leafDSBUQ1 [DSLeaf LeafDSBUQQ] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafZiStructure] [DSLeaf LeafZiChief] [DSLeaf LeafM3] [DSLeaf LeafFrattiniChief] [DSLeaf LeafSylowS] : LeafDSBUQ1 := by
  intro G _ _ L1 L2 S h cU
  have hZS : ZSetting L1 L2 S := ⟨h.hyp, DSBHyp.bnorm h⟩
  have hA : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := (sylow_s h.hyp).2.2
  obtain ⟨hS1, -, hQL1⟩ := dsba5_vertex h
  have hSL1 : S ⊓ L1 = S := by
    have h2 : dsQ L1 L2 S ≤ S ⊓ L1 := le_inf hQS hQL1
    have h1 := hS1
    rw [sup_eq_left.mpr h2] at h1
    exact h1.symm
  have hSL : S ≤ L1 := by
    calc S = S ⊓ L1 := hSL1.symm
      _ ≤ L1 := inf_le_right
  have hchief := frattini_chief hA
  obtain ⟨hZA, hZeq, hZc, -⟩ := zi_chief hZS hA.quot cU
  have hZQ : dsZi L1 S ≤ dsQ L1 L2 S :=
    (zi_structure hZS).2.2.1.trans (DSBUQ1.dsOmega1_centerOf_le _)
  have hEA : IsElemAbelian 2 (dsZi L1 S) := by
    rw [hZeq]
    exact (zi_structure hZS).2.2.2.1
  obtain ⟨-, hR2, hZnot⟩ := dsbuqq h cU
  have hΦR : dsFrattini (dsQ L1 L2 S) ≤ dsQ L1 L2 S ⊓ dsQ L2 L1 S :=
    DSBUQ1.dsFrattini_le_of_relIndex_two hR2
  have hQQ : dsQ L1 L2 S = dsZi L1 S := by
    have hXQ : dsZi L1 S ⊔ dsFrattini (dsQ L1 L2 S) ≤ dsQ L1 L2 S :=
      sup_le hZQ (Subgroup.map_subtype_le (frattini ↥(dsQ L1 L2 S)))
    have hPX : L1 ⊔ bigB L1 L2 S ≤
        Subgroup.normalizer ((dsZi L1 S ⊔ dsFrattini (dsQ L1 L2 S) : Subgroup G) : Set G) :=
      F1.le_normalizer_sup hZA.norm_E hchief.norm_K
    rcases hchief.irred (dsZi L1 S ⊔ dsFrattini (dsQ L1 L2 S)) le_sup_right hXQ hPX with hK | hE
    · exfalso
      exact hZnot ((le_sup_left.trans hK.le).trans (hΦR.trans inf_le_right))
    · exact le_antisymm (DSBUQ1.le_of_sup_dsFrattini_eq hZQ hE) hZQ
  have hZcard : Nat.card (dsZi L1 S) = 16 := by
    have h16 := hZA.card
    rwa [Subgroup.relIndex_bot_left] at h16
  have hQcard : Nat.card (dsQ L1 L2 S) = 16 := by
    rw [hQQ]
    exact hZcard
  have hRcard : Nat.card ↥(dsQ L1 L2 S ⊓ dsQ L2 L1 S) = 8 := by
    have h : (dsQ L1 L2 S ⊓ dsQ L2 L1 S).relIndex (dsQ L1 L2 S) *
        Nat.card ↥((dsQ L1 L2 S ⊓ dsQ L2 L1 S) ⊓ dsQ L1 L2 S) = Nat.card ↥(dsQ L1 L2 S) :=
      Subgroup.relIndex_mul_card _ _
    have hinf : (dsQ L1 L2 S ⊓ dsQ L2 L1 S) ⊓ dsQ L1 L2 S = dsQ L1 L2 S ⊓ dsQ L2 L1 S :=
      inf_eq_left.mpr inf_le_left
    rw [hinf, hR2, hQcard] at h
    omega
  have hT : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  have hM3 := m3 hZA hT
  have hNN : ¬ NatSec L1 ⊥ (dsZi L1 S) := by
    intro hN
    have hRE : dsQ L1 L2 S ⊓ dsQ L2 L1 S ≤ dsZi L1 S := by
      rw [← hQQ]
      exact inf_le_left
    have hborel : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
    have hBR : bigB L1 L2 S ≤
        Subgroup.normalizer ((dsQ L1 L2 S ⊓ dsQ L2 L1 S : Subgroup G) : Set G) := by
      apply DSBUQ1.le_normalizer_inf
      · exact le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      · have hBP2 : bigB L1 L2 S ≤ L2 ⊔ bigB L2 L1 S := by
          rw [bigB_comm L1 L2 S]
          exact le_sup_right
        exact hBP2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L2 ⊔ bigB L2 L1 S))
    have hLN : L1 ⊓ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((dsQ L1 L2 S ⊓ dsQ L2 L1 S : Subgroup G) : Set G) :=
      hborel.trans hBR
    obtain ⟨hfirst, hrel4, -, -, -⟩ := hM3.1 hN
    rcases hfirst (dsQ L1 L2 S ⊓ dsQ L2 L1 S) bot_le hRE hLN with h0 | h4 | hE
    · rw [h0, Subgroup.card_bot] at hRcard
      omega
    · rw [h4] at hRcard
      rw [Subgroup.relIndex_bot_left] at hrel4
      omega
    · rw [hE, hZcard] at hRcard
      omega
  obtain ⟨-, hrel2, -, hcomm1, hcomm2, -⟩ := hM3.2 hNN
  rw [hSL1] at hrel2 hcomm1 hcomm2
  have hSN : S ≤ Subgroup.normalizer (dsZi L1 S : Set G) :=
    hSL.trans (le_sup_left.trans hZA.norm_E)
  have hWE : ⁅⁅dsZi L1 S, S⁆, S⁆ ≤ dsZi L1 S :=
    DSBUQ1.commutator_le_of_le (DSBUQ1.commutator_le_of_le le_rfl hSN) hSN
  have hZW : dsZ S = ⁅⁅dsZi L1 S, S⁆, S⁆ ⊔ ⊥ := by
    ext x
    rw [hZc, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxE, hxC⟩
      exact hcomm2 x hxE fun t ht =>
        Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hxC t ht).symm)
    · intro hx
      have hxW : x ∈ ⁅⁅dsZi L1 S, S⁆, S⁆ := by
        rwa [sup_bot_eq] at hx
      refine ⟨hWE hxW, fun t ht => ?_⟩
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hcomm1 t ht x hx))).symm
  have hZ2 : Nat.card (dsZ S) = 2 := by
    rw [hZW]
    have h := hrel2
    rw [Subgroup.relIndex_bot_left] at h
    exact h
  have hpcQ : pCoreOf 2 L1 = dsQ L1 L2 S := by
    have h1 := F1.inf_pCoreOf_parabolic_eq h.hyp
    rw [← h1]
    exact inf_eq_left.mpr hQL1
  have hCT : CharTwo L1 := by
    have hP := F1.parabolic_charTwo h.hyp
    intro x hx
    rw [hpcQ] at hx ⊢
    exact hP ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hdsQ2 := (dsbs3_vertex h).2.2.2
  refine ⟨hpcQ, hQQ, hCT, ?_, ?_, ?_, ?_, hZ2⟩
  · rw [hpcQ, hQQ]
    exact hEA
  · rw [hpcQ]
    exact hQcard
  · rw [hpcQ, hQQ]
    exact hNN
  · omega

end CFSG.GH74.QTGen4.DSGen4

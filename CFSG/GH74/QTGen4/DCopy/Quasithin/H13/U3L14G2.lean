module

public import CFSG.Quasithin.H13.U3L14G2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14B56

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem stepG_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) {K : Subgroup G}
    (hD : KData14 T L V V₂ Lp K) : ¬ Lp ≤ K := by
  intro hLpK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := reducedAggregate (K ⊔ T) with hWdef
  have hred : IsTwoReducedIn (K ⊔ T) W := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hKW : K ≤ normalizer (W : Set G) := le_sup_left.trans hred.2.1

  have hW3 := S.isTwoReducedIn_W3 hQ hD hLpK
  have hV3W : V₃ ≤ W :=
    (le_conjClosure V₃ K).trans (A7.le_reducedAggregate_of_isTwoReducedIn hW3)
  have hV3WK : V₃ ≤ ⁅W, K⁆ := by
    rw [← S.V3_comm_Lp]
    exact commutator_mono hV3W hLpK
  have hKV1 : K ≤ centralizer (fsuV1 T V : Set G) := fun k hk =>
    S.mem_centralizer_V1 ((le_of_mem_cComp hD.mem) hk)
  have hV1C : fsuV1 T V ≤ ⁅W, K⁆ ⊓ centralizer (K : Set G) := by
    refine le_inf (S.le13.trans hV3WK) fun v hv => ?_
    rw [mem_centralizer_iff]
    intro k hk
    exact ((mem_centralizer_iff.mp (hKV1 hk)) v hv).symm

  have hO : pCoreOf 2 K ≤ centralizer (W : Set G) := by
    have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
      (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K _ le_sup_left
        hKn
    refine h1.trans (hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 _)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => ?_)
    obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  obtain ⟨h5, -, ⟨⟨I, hI⟩, hall⟩, h4⟩ := h1332 G T L S.h13 K hD.faithful
  obtain ⟨hWc, -, hcase⟩ := S.b51Part1_KT_F4 h1332 hC58 h317 h56 hD
  have hcard : Nat.card (autOn K W) ≤ 6048 :=
    (card_autOn_le_card_quot hKW hO).trans (card_le_of_qt13Five h5)
  obtain ⟨hn3, hn4⟩ := not_case1iii_iv (J := ffJ (autOn (K ⊔ T) W)) hcard
  have hmap := map_commV_autOn hKW
  rcases hcase with h1i | h1ii | h1iii | h1iv
  ·
    have hWK : ⁅W, K⁆ = I := eq_of_irrPlus hKW h1i.1 hI.1 hI.2.2.1 hI.2.2.2.1 hI.2.1
    rw [hWK] at hV1C hV3WK
    have hZ : I ⊓ centralizer (K : Set G) ≠ ⊥ := fun h =>
      S.V1_ne (le_bot_iff.1 (h ▸ hV1C))

    obtain ⟨-, -, -, hIc, hmod⟩ := hall I hI
    have hreal : FFModel.Realizes (V := ↥I) (altCoreModel 6) (autOn K I) ⊤ ⊥ := by
      rcases hmod with ⟨-, h0⟩ | ⟨-, h0⟩ | ⟨-, -, hr⟩ | ⟨-, -, h0⟩ | ⟨-, -, h0⟩
      · exact absurd h0 hZ
      · exact absurd h0 hZ
      · exact hr
      · exact absurd h0 hZ
      · exact absurd h0 hZ
    have hO' : pCoreOf 2 K ≤ centralizer (I : Set G) := hO.trans (centralizer_le hI.1)
    have hK13 : QTH13 G T K := by
      refine h4 (Or.inl fun ⟨φ, hφs, hφk⟩ => ?_)
      obtain ⟨e6⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altCoreModel_faithful (by norm_num))
        hreal
      have h1 : Nat.card (autOn K I) = 360 := by
        rw [Nat.card_congr e6.toEquiv]
        show Nat.card ↥(alternatingGroup (Fin 6)) = 360
        rw [nat_card_alternatingGroup, Nat.card_fin]
        rfl
      have h2 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
        rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq
          ((A3.pCore_eq_openCore 2 ↥K).trans hφk.symm)).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).toEquiv,
          nat_card_alternatingGroup, Nat.card_fin]
        rfl
      have := card_autOn_le_card_quot hI.2.2.1 hO'
      omega
    obtain ⟨S'⟩ := A6.exists_setting134_F4 h1332 hK13 hI hZ

    obtain ⟨v, hv, e, he, hve⟩ : ∃ v ∈ V₃, ∃ e ∈ pCoreOf 2 Lp, ⁅v, e⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply S.V1_ne
      rw [← S.comm3, eq_bot_iff, commutator_le]
      intro v hv e he
      exact mem_bot.2 (hcon v hv e he)
    have hc1 : ⁅v, e⁆ ∈ fsuV1 T V := S.comm3 ▸ commutator_mem_commutator hv he
    have hcz : ⁅v, e⁆ = S'.zV := (S'.mem_ZV_iff.1 (hV1C hc1)).resolve_left hve
    have hvI : v ∈ I := hV3WK hv
    have heK : e ∈ K := hLpK ((LieType.BorelTits.pCoreOf_le 2 Lp) he)
    have heN : e ∈ normalizer (I : Set G) := S'.frame.L_le heK
    have hv'I : e * v⁻¹ * e⁻¹ ∈ I := (mem_normalizer_iff.mp heN v⁻¹).mp (inv_mem hvI)
    have hcI : ⁅v, e⁆ ∈ I := by
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc e]
      exact mul_mem hvI hv'I

    set σ := S'.frame.ρ ⟨e, heN⟩ with hσ
    have hψ1 : S'.frame.ψ ⟨⁅v, e⁆, hcI⟩ =
        S'.frame.ψ ⟨v, hvI⟩ * S'.frame.ψ ⟨e * v⁻¹ * e⁻¹, hv'I⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show ⁅v, e⁆ = v * (e * v⁻¹ * e⁻¹)
      rw [commutatorElement_def]
      group
    have hψ2 : S'.frame.ψ ⟨e * v⁻¹ * e⁻¹, hv'I⟩ = (G6.coreAct 6 σ (S'.frame.ψ ⟨v, hvI⟩))⁻¹ := by
      have := S'.psi_conj ⟨e, heN⟩ ⟨v⁻¹, inv_mem hvI⟩
      rw [show (⟨v⁻¹, inv_mem hvI⟩ : ↥I) = (⟨v, hvI⟩ : ↥I)⁻¹ from rfl, map_inv, map_inv] at this
      exact this
    have hψz : S'.frame.ψ ⟨⁅v, e⁆, hcI⟩ = ⟨G6.allOnes 6, A6.allOnes_mem_core⟩ := by
      rw [← S'.psi_zV]
      congr 1
      exact Subtype.ext hcz
    rw [hψ1, hψ2] at hψz
    have h3 := congrArg Subtype.val hψz
    simp only [coe_mul, coe_inv, G6.coreAct_coe] at h3
    exact mul_inv_permAct_ne_allOnes σ _ (G6.mem_coreMod.1 (S'.frame.ψ ⟨v, hvI⟩).2) h3
  ·
    have h0 := fixV_inf_commV_eq_bot_of_case1ii h1ii
    apply S.V1_ne
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvWK, hvK⟩ := mem_inf.mp (hV1C hv)
    have hvW : v ∈ W := (Subgroup.le_normalizer_iff_commutator_le_left.mp hKW) hvWK
    have hmem : (⟨v, hvW⟩ : ↥W) ∈ fixV (autOn K W) ⊓ commV (autOn K W) := by
      refine mem_inf.mpr ⟨mem_fixV.2 fun σ hσ => ?_, ?_⟩
      · obtain ⟨⟨g, hgN⟩, hgK, rfl⟩ := Setup.mem_autOn_iff.1 hσ
        apply Subtype.ext
        rw [coe_conjAct_apply]
        have := (mem_centralizer_iff.mp hvK) g hgK
        calc g * v * g⁻¹ = v * g * g⁻¹ := by rw [this]
          _ = v := by group
      · have h1 : v ∈ (commV (autOn K W)).map W.subtype := hmap ▸ hvWK
        obtain ⟨y, hy, hyv⟩ := h1
        have : y = ⟨v, hvW⟩ := Subtype.ext hyv
        exact this ▸ hy
    rw [h0, mem_bot] at hmem
    exact mem_bot.2 (congrArg Subtype.val hmem)
  · exact (hn3 h1iii).elim
  · exact (hn4 h1iv).elim

end Set14

end CFSG.Quasithin.H13.U3

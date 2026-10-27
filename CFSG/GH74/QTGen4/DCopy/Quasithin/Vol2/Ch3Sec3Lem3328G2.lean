module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328G2

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

variable {G : Type} [Group G]

@[expose] def Step3_3_28G2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → T ≤ Subgroup.normalizer (L : Set G) → tC L T ≠ ⊥ →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T →
      frattini ↥(qL L T) = ⊥ ∧
      (∀ B : Subgroup G, B ≤ rCZ L T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(qL L T)) ∧
      (∀ B : Subgroup G, IsMaxElemAbelian (rCZ L T) B → ¬ B ≤ qL L T →
        ∃ b ∈ B, qL L T ⊓ Subgroup.centralizer (B : Set G) =
          qL L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
      ∀ B B' : Subgroup G, IsMaxElemAbelian (rCZ L T) B → IsMaxElemAbelian (rCZ L T) B' →
        ¬ B ≤ qL L T → ¬ B' ≤ qL L T → B ⊔ qL L T = B' ⊔ qL L T

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_28G2TC_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4) (h25 : Stmt3_3_25_F4)
    (h26 : Stmt3_3_26_F4) (h29 : Stmt3_3_29_F4) (hS : Step3_3_28G2_F4) : Stmt3_3_28G2TC_F4 := by
  intro G _ _ T M L D h hG2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hTC
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  obtain ⟨d, hdD, hdM, hdV⟩ := h26 G T M L D h
  obtain ⟨-, hDR, -⟩ := (h25 G T M L D h).2.1 hTC (h29 G T M L D h)
  obtain ⟨hF, ha, hb, hc⟩ := hS G T M L D h hG2 hTL hTC d hdD hdM hdV
  set X := oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) with hXdef
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hXL : X ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    (sup_le_sup_right hXL T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hQR : qL L T ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) hXTN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hRT : R ≤ T := by
    have hTs : IsSylowTwoOf T (X ⊔ T) := ⟨le_sup_right, h.sylow.1,
      Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
    exact pCoreOf_le_of_isSylowTwoOf hTs
  have hRN : R ≤ Subgroup.normalizer (qL L T : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hXTN
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hRC : R ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQR fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
    rw [← hCQ]
    exact ⟨hRT hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) hx.2⟩
  have hQmax : IsMaxElemAbelian R (qL L T) := ⟨hQR, hQe, ha⟩
  have huniq : ∀ A A' : Subgroup G, IsMaxElemAbelian R A → IsMaxElemAbelian R A' →
      A ≠ qL L T → A' ≠ qL L T → A = A' := by
    intro A A' hA hA' hAQ hA'Q
    have hout : ∀ B : Subgroup G, IsMaxElemAbelian R B → B ≠ qL L T → ¬ B ≤ qL L T :=
      fun B hB hne hle => hne (Subgroup.eq_of_le_of_card_ge hle (hB.2.2 _ hQR hQe))
    obtain ⟨b, hbA, hbC⟩ := hb A hA (hout A hA hAQ)
    have hsup := hc A A' hA hA' (hout A hA hAQ) (hout A' hA' hA'Q)
    have hauto : autI hQe A = autI hQe A' := by
      rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hQab (hA.1.trans hRN), hsup,
        autOn_sup_eq_of_comm hQab (hA'.1.trans hRN)]
    exact (B2_21 hQe hQR hRN hRC hA hbA hbC hA' hauto).symm
  have hDQ : D ≤ Subgroup.normalizer (qL L T : Set G) := by
    intro g hg
    have hodd : Odd (orderOf g) := by
      have h1 : orderOf (⟨g, hg⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat h.Dodd h1
    exact Lem3331.mem_normalizer_of_odd_of_unique hQmax huniq (hDR hg) hodd
  exact h.not_le_normalizer h38 h39 h.toSetup331.pCoreOf_ne_bot
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    hDQ

end CFSG.Quasithin.H13

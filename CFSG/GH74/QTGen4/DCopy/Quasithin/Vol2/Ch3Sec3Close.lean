module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Close

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_close_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h30 : Stmt3_3_30_F4) (h31 : Stmt3_3_31_F4) (h32 : Stmt3_3_32_F4) (hI : InspClose) :
    Stmt3_3_Close_F4 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hA6 := h30 G T M L D h
  have hTC := h31 G T M L D h
  obtain ⟨hc1, -, φ, hφT, hDT₀⟩ := h32 G T M L D h
  obtain ⟨ha, hb, hc⟩ := hI G T M L D h hTL hA6 hTC hc1 φ hφT
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hFQ := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
  rw [hTC] at hFQ
  have hF : frattini ↥(qL L T) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (qL L T).subtype_injective).mp (le_bot_iff.mp hFQ)
  have hQe : IsElemAbelian 2 (qL L T) :=
    isElemAbelian_of_frattini_eq_bot (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hF
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hQT₀ : qL L T ≤ preimageA2 T L φ := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨hQT hq, ⟨⟨q, hTV (hQT hq)⟩, ?_, rfl⟩⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [InternalSec.conjAct_eq_one_of_mem_centralizer _ (hQC hq)]
    exact Subgroup.one_mem _
  have hT₀T : preimageA2 T L φ ≤ T := inf_le_left
  have hT₀N : preimageA2 T L φ ≤ Subgroup.normalizer (qL L T : Set G) :=
    hT₀T.trans (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have hT₀C : preimageA2 T L φ ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQT₀ fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
    rw [← hCQ]
    exact ⟨hT₀T (Subgroup.mem_inf.mp hx).1,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) (Subgroup.mem_inf.mp hx).2⟩
  have hQmax : IsMaxElemAbelian (preimageA2 T L φ) (qL L T) := ⟨hQT₀, hQe, ha⟩
  have hperm : ∀ g ∈ D, ∀ B, IsMaxElemAbelian (preimageA2 T L φ) B →
      IsMaxElemAbelian (preimageA2 T L φ) (B.map (MulAut.conj g).toMonoidHom) := by
    intro g hg B hB
    have hT₀g : (preimageA2 T L φ).map (MulAut.conj g).toMonoidHom = preimageA2 T L φ :=
      A38.map_conj_eq_iff.mpr (hDT₀ hg)
    have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hB
    rwa [hT₀g] at this
  have hQne : qL L T ≠ ⊥ := h.toSetup331.pCoreOf_ne_bot
  have hDQ : ¬ D ≤ Subgroup.normalizer (qL L T : Set G) :=
    h.not_le_normalizer h38 h39 hQne (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  obtain ⟨d, hdD, hdQ⟩ := IsConcreteLE.not_le_iff_exists.mp hDQ
  have hdQ' : d⁻¹ ∉ Subgroup.normalizer (qL L T : Set G) := fun h' => hdQ (by
    simpa using inv_mem h')
  have hnot : ∀ g : G, g ∉ Subgroup.normalizer (qL L T : Set G) →
      ¬ (qL L T).map (MulAut.conj g).toMonoidHom ≤ qL L T := by
    intro g hg hle
    apply hg
    refine A38.map_conj_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hQ₁ := hperm d hdD _ hQmax
  have hQ₂ := hperm d⁻¹ (inv_mem hdD) _ hQmax
  have hcard : Nat.card ↥((qL L T).map (MulAut.conj d).toMonoidHom ⊔ qL L T) =
      Nat.card ↥((qL L T).map (MulAut.conj d⁻¹).toMonoidHom ⊔ qL L T) := by
    have e : ((qL L T).map (MulAut.conj d).toMonoidHom ⊔ qL L T).map
        (MulAut.conj d⁻¹).toMonoidHom = (qL L T).map (MulAut.conj d⁻¹).toMonoidHom ⊔ qL L T := by
      rw [Subgroup.map_sup, map_conj_map_conj, inv_mul_cancel, map_conj_one, sup_comm]
    rw [← e, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective]
  have hsup := hc _ _ hQ₁ hQ₂ (hnot d hdQ) (hnot d⁻¹ hdQ') hcard
  obtain ⟨b, hbQ₁, hbC⟩ := hb _ hQ₁ (hnot d hdQ)
  have hauto : autI hQe ((qL L T).map (MulAut.conj d).toMonoidHom) =
      autI hQe ((qL L T).map (MulAut.conj d⁻¹).toMonoidHom) := by
    rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hQab (hQ₁.1.trans hT₀N), hsup,
      autOn_sup_eq_of_comm hQab (hQ₂.1.trans hT₀N)]
  have heq := B2_21 hQe hQT₀ hT₀N hT₀C hQ₁ hbQ₁ hbC hQ₂ hauto
  have hd2 : d ^ 2 ∈ Subgroup.normalizer (qL L T : Set G) := by
    refine A38.map_conj_eq_iff.mp ?_
    have h1 := congrArg (fun X : Subgroup G => X.map (MulAut.conj d).toMonoidHom) heq
    simp only [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h1
    rw [pow_two, ← h1]
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat h.Dodd h1
  exact hdQ ((Subgroup.zpowers_le.mpr hd2) (mem_zpowers_sq_of_odd hodd))

theorem stmt3_3_1A_of_inputs_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h30 : Stmt3_3_30_F4) (h31 : Stmt3_3_31_F4) (h32 : Stmt3_3_32_F4) (hI : InspClose) : Stmt3_3_1A_F4 :=
  stmt3_3_1A_of_close_F4 (stmt3_3_close_of_F4 h38 h39 h14 h30 h31 h32 hI)

end CFSG.Quasithin.H13

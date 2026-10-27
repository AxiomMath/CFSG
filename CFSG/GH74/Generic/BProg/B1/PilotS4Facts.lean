module

public import CFSG.GH74.Generic.BProg.B1.PilotS4Split
public import CFSG.Walter.Ree.Model.Fusion
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS4

open CFSG CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Walter CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Walter.Ree.Model CFSG.GH74.Generic.BProg.B1.PilotS5 Subgroup
open scoped MatrixGroups

theorem isSplit_jtHyp {G : Type} [Group G] [Finite G] (J : JT.JTHyp G) (hp2 : J.p ≠ 2) :
    IsSplit (Nat.card PSL(2, GaloisField J.p J.f)) J.t J.F (centralizer ({J.t} : Set G)) := by
  have hf : J.f ≠ 0 := by
    intro h0
    have := J.five_lt
    rw [h0, pow_zero] at this
    omega
  have : NeZero J.f := ⟨hf⟩
  have hK : Nat.card (GaloisField J.p J.f) = J.p ^ J.f := GaloisField.card J.p J.f hf
  have h2 : Nat.card (GaloisField J.p J.f) ≠ 2 := by have := J.five_lt; omega
  have h3 : Nat.card (GaloisField J.p J.f) ≠ 3 := by have := J.five_lt; omega
  have hsimple : IsSimpleGroup PSL(2, GaloisField J.p J.f) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 _
      le_rfl (Or.inr h2) (Or.inr h3)
  obtain ⟨x, y, hxy⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
      (GaloisField J.p J.f) h2 h3
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField J.p J.f)) :=
    ⟨J.p, J.f, Fact.out, (Fact.out : J.p.Prime).odd_of_ne_two hp2, Nat.one_le_iff_ne_zero.2 hf, hK⟩
  have heven := CFSG.Walter.Suzuki.two_dvd_card_psl2 (GaloisField J.p J.f) hodd
  refine ⟨J.orderOf_t, J.le_centralizer, J.t_not_mem, J.centralizer_eq, J.iso.isSimpleGroup, ?_, ?_,
    heven⟩
  · exact ⟨J.iso.symm x, J.iso.symm y, fun hc => hxy (by simpa using congrArg J.iso hc)⟩
  · exact Nat.card_congr J.iso.toEquiv

theorem reeTitsModel_of_lieModel {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .twistedG2 n p f) : ReeTitsModel X .twistedG2 p f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

section Ree


theorem splitGrp_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    SplitGrp (Nat.card PSL(2, GaloisField 3 (2 * a + 1))) ↥(ReeTag.G2.reeGamma K a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set J : JT.JTHyp ↥(ReeTag.G2.reeGamma K a) := smallReeJTHyp ha hK with hJ
  refine ⟨fun z hz => ?_, ⟨J.t, J.orderOf_t⟩, fun u hu => ?_⟩
  · have hzc : z ∈ Subgroup.center ↥(ReeTag.G2.reeGamma K a) := Subgroup.mem_center_iff.2 hz
    rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hzc
    exact hzc
  · have hu' : orderOf (u : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    obtain ⟨g, hgΓ, hgu⟩ := exists_conj_eq_smallReeH_of_orderOf hK hw₀ u.2 hu'
    set g₀ : ↥(ReeTag.G2.reeGamma K a) := ⟨g, hgΓ⟩ with hg₀
    have hconj : g₀ * u * g₀⁻¹ = J.t := Subtype.ext hgu
    have ht' : (J.conj g₀⁻¹).t = u := by
      rw [JT.JTHyp.conj_t, ← hconj]
      group
    have hp2 : (J.conj g₀⁻¹).p ≠ 2 := by
      show (3 : ℕ) ≠ 2
      norm_num
    have := isSplit_jtHyp (J.conj g₀⁻¹) hp2
    rw [ht'] at this
    exact ⟨_, this⟩

theorem ree_model_data' {T : Type} [Group T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.G2.prime),
      1 ≤ a ∧ Nat.card K = 3 ^ (2 * a + 1) ∧ Nonempty (T ≃* ↥(ReeTag.G2.reeGamma K a)) := by
  obtain ⟨-, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  exact ⟨a', K, inferInstance, inferInstance, this, ha, by rw [hK, hfa], ⟨E⟩⟩

theorem splitGrp_of_qShape4 {Kt : Type} [Group Kt] (h : QShape4 Kt) : ∃ n, SplitGrp n Kt := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data' (reeTitsModel_of_lieModel hf)
  exact ⟨_, (splitGrp_reeGamma ha hK).map_equiv e.symm⟩

theorem center_of_qShape4 {Kt : Type} [Group Kt] (h : QShape4 Kt) :
    ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1 := by
  obtain ⟨n, hn⟩ := splitGrp_of_qShape4 h
  exact hn.center

theorem exists_four_of_qShape4 {Kt : Type} [Group Kt] [Finite Kt] (h : QShape4 Kt) :
    ∃ V : Subgroup Kt, CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨n, hn⟩ := splitGrp_of_qShape4 h
  exact hn.exists_four

end Ree

end CFSG.GH74.Generic.BProg.B1.PilotS4

module

public import CFSG.Quasithin.Background.HPair
public import CFSG.LinearAlgebra.ScalarGraphAction
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Basic
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools
public import CFSG.Quasithin.EmptyFaithful.S152N2Lin

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem mem_four_of_pRank_le_two {Q : Subgroup G} (hQ : CFSG.Open.pRank 2 Q ≤ 2) {w z u : G}
    (hwQ : w ∈ Q) (hzQ : z ∈ Q) (huQ : u ∈ Q) (hw2 : w * w = 1) (hz2 : z * z = 1)
    (hu2 : u * u = 1) (hw1 : w ≠ 1) (hz1 : z ≠ 1) (hwz : w ≠ z) (hcwz : w * z = z * w)
    (hcuw : u * w = w * u) (hcuz : u * z = z * u) : u = 1 ∨ u = w ∨ u = z ∨ u = w * z := by
  by_contra hne
  push Not at hne
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions w z hw2 hz2 hcwz with hV
  have hVmem : ∀ x, x ∈ V ↔ x = w * z ∨ x = w ∨ x = z ∨ x = 1 := fun x => by
    change x ∈ ({w * z, w, z, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hV4 : IsKleinFour V :=
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions w z hw2 hz2 hw1 hz1 hwz hcwz
  have hVQ : V ≤ Q := by
    intro x hx
    rcases (hVmem x).mp hx with rfl | rfl | rfl | rfl
    · exact mul_mem hwQ hzQ
    · exact hwQ
    · exact hzQ
    · exact one_mem _
  have hVe : CFSG.Open.IsElemAbelian 2 V := by
    refine ⟨IsKleinFour.isMulCommutative (G := V), fun x hx => ?_⟩
    have h1 := IsKleinFour.mul_self (G := V) ⟨x, hx⟩
    rw [sq]
    exact congrArg Subtype.val h1
  have hVc : Nat.card V = 2 ^ 2 := by rw [IsKleinFour.card_four]; norm_num
  have huV : u ∉ V := fun hu => by
    rcases (hVmem u).mp hu with h1 | h1 | h1 | h1
    · exact hne.2.2.2 h1
    · exact hne.2.1 h1
    · exact hne.2.2.1 h1
    · exact hne.1 h1
  have hcomm : ∀ e ∈ V, Commute e u := by
    intro e he
    rcases (hVmem e).mp he with rfl | rfl | rfl | rfl
    · show w * z * u = u * (w * z)
      rw [mul_assoc, ← hcuz, ← mul_assoc, ← hcuw, mul_assoc]
    · exact hcuw.symm
    · exact hcuz.symm
    · exact Commute.one_left u
  have h3 := succ_le_open_pRank_of_commute Nat.prime_two hVe hVc hcomm (by rw [sq]; exact hu2)
    huV hVQ huQ
  omega

theorem exists_conj_eq_of_isSylowOf {P P' K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hP' : IsSylowOf 2 P' K) : ∃ k ∈ K, conjugate P' k = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hk⟩ := exists_conj_le_of_isSylowOf hP hP'.le hP'.isPGroup
  refine ⟨k, hkK, eq_of_le_of_card_ge (conjugate_le_of_forall hk) ?_⟩
  rw [card_conjugate_eq_card, hP.card_eq, hP'.card_eq]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem R_le_footeFixed {b : G} (hbQ : b ∈ Q) : S ⊓ L ≤ footeFixed L b := by
  intro r hr
  rw [footeFixed]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_S) ⟨r, (mem_inf.mp hr).1⟩
  refine subset_closure ⟨mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp hr).2, ?_⟩), k, ?_⟩
  · exact mem_centralizer_singleton_iff.mpr (h.commute_Q_R hbQ hr).symm
  · rwa [Subgroup.orderOf_mk] at hk

theorem footeF_data {b : G} (hbQ : b ∈ Q) (hb2 : orderOf b = 2) :
    footeFixed L b = footeF L₀ b ∧ IsTwoComponentAt b (footeF L₀ b) ∧
      footeF L₀ b ∈ footeFamilyOf L₀ ∧
      IsSimpleGroup (footeF L₀ b ⧸ pPrimeCore 2 (footeF L₀ b)) ∧
      (∃ x y : footeF L₀ b ⧸ pPrimeCore 2 (footeF L₀ b), x * y ≠ y * x) ∧
      GorensteinWalter.HasDihedralSylowTwo (footeF L₀ b ⧸ pPrimeCore 2 (footeF L₀ b)) := by
  have h4 := h.sec4
  obtain ⟨hfix, hLb, hLbF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hb2 (h.Q_le hbQ)
  obtain ⟨hs, ⟨e⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.hrank2 hLb hLbF
  exact ⟨hfix, hLb, hLbF, hs,
    exists_mul_ne_mul_of_isQuasisimple (isQuasisimple_quotient_of_isPComponent hLb.2.1 hLb.2.2),
    OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv e
      (hasDihedralSylowTwo_of_footeFamilyType h4.footeFamilyType)⟩

theorem exists_conj_t_footeF {b : G} (hbQ : b ∈ Q) (hb2 : orderOf b = 2) {W : Subgroup G}
    (hW : IsPGroup 2 W) (hWQ : W ≤ Q) (hWb : W ≤ centralizer ({b} : Set G)) {r : G}
    (hr : r ∈ S ⊓ L) (hr2 : orderOf r = 2) :
    ∃ k ∈ footeF L₀ b, k ∈ centralizer (W : Set G) ∧ k⁻¹ * r * k = t := by
  obtain ⟨hfix, hLb, -, hs, hna, hdih⟩ := h.footeF_data hbQ hb2
  have hLb' : IsTwoComponentAt b (footeFixed L b) := hfix ▸ hLb
  have hWC : W ≤ coreActionKernel (footeF L₀ b) := by
    intro q hq
    rw [← hfix]
    exact mem_coreActionKernel_footeFixed (mem_centralizer_singleton_iff.mp (hWb hq)).symm
      (h.Q_le (hWQ hq)) hLb'
  have hRF : S ⊓ L ≤ footeF L₀ b := hfix ▸ h.R_le_footeFixed hbQ
  have hcent : ∀ x ∈ S ⊓ L, x ∈ centralizer (W : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun q hq => h.commute_Q_R (hWQ hq) hx
  exact exists_conj_of_involutions hna hdih hW hWC (hRF hr) (hRF h.tR) hr2 h.t2
    (hcent r hr) (hcent t h.tR)

end Sec5

section TorusFamily
open scoped Pointwise
open CFSG.Quasithin.S152N2
variable {W : Type*} [CommGroup W] [Finite W]

@[simp]
private theorem torus_projection_coe
    {R P : Subgroup W} (hinf : P ⊓ R = ⊥) (hsup : P ⊔ R = ⊤) (w : W) :
    ((((CFSG.Quasithin.H.Pair.proj hinf hsup).codRestrict P
      (CFSG.Quasithin.H.Pair.proj_mem hinf hsup)) w : P) : W) =
      CFSG.Quasithin.H.Pair.proj hinf hsup w := rfl

open CFSG.ScalarGraphAction

end TorusFamily

open scoped Pointwise

end CFSG.ComponentClassification.Foote5

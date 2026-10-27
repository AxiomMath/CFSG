module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Helpers
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Solv
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section VFacts

variable {G : Type} [Group G] {V : Subgroup G}

theorem V_sq_eq_one (hV : IVK.IsFourSubgroup V) {v : G} (hv : v ∈ V) : v ^ 2 = 1 := by
  have := hV.1
  exact elemPow_eq_one_of_isElementaryAbelian v hv

theorem V_orderOf_two (hV : IVK.IsFourSubgroup V) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) : orderOf v = 2 :=
  orderOf_eq_prime (V_sq_eq_one hV hv) hv1

theorem V_comm (hV : IVK.IsFourSubgroup V) {v w : G} (hv : v ∈ V) (hw : w ∈ V) : v * w = w * v := by
  have := hV.1.toIsMulCommutative
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨v, hv⟩ : ↥V) ⟨w, hw⟩)

theorem V_exists_ne_one (hV : IVK.IsFourSubgroup V) : ∃ v ∈ V, v ≠ 1 := by
  by_contra hno
  push Not at hno
  have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hno
  have h4 := hV.2
  rw [this, Subgroup.card_bot] at h4
  omega

end VFacts



section V7Facts

variable {G : Type} [Group G] [Finite G] {z : G} {S V : Subgroup G}

theorem V7.z_not_mem (hz : orderOf z = 2) (hV : V7 z S V) : z ∉ V := by
  intro hzV
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; omega
  have hex : ∃ w ∈ V, w ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ Subgroup.zpowers z := fun w hw => hcon w hw
    have h1 : Nat.card ↥V ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz] at h1
    have := hV.four.2
    omega
  obtain ⟨w, hwV, hwz⟩ := hex
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ one_mem _)
  obtain ⟨c, hc, hcw⟩ := hV.conj z hzV hz1 w hwV hw1
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  apply hwz
  have : w = z := by rw [← hcw, hcz]; group
  rw [this]
  exact Subgroup.mem_zpowers z

end V7Facts

section L74

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_pPrimeCoreOf (M : Subgroup G) :
    M ≤ normalizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) :=
  haveI : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
  le_normalizer_map_subtype M (pPrimeCore 2 ↥M)

theorem odd_card_pPrimeCoreOf (M : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := by
  have h1 : Nat.card ↥(pPrimeCoreOf 2 M) = Nat.card ↥(pPrimeCore 2 ↥M) :=
    Subgroup.card_map_of_injective M.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))

theorem not_mem_pPrimeCoreOf_of_orderOf_two {M : Subgroup G} {w : G} (hw : orderOf w = 2)
    (hwO : w ∈ pPrimeCoreOf 2 M) : False := by
  have hodd := odd_card_pPrimeCoreOf M
  have hdvd : orderOf w ∣ Nat.card ↥(pPrimeCoreOf 2 M) := by
    have := orderOf_dvd_natCard (⟨w, hwO⟩ : ↥(pPrimeCoreOf 2 M))
    rwa [Subgroup.orderOf_mk] at this
  rw [hw] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem not_cover_of_conj {z v g : G} {M : Subgroup G} (hz : orderOf z = 2) (hCM : Cen z ≤ M)
    (hvC : v ∈ Cen z) (hv2 : orderOf v = 2) (hvz : v ≠ z) (hg : g * z * g⁻¹ = v) (hgM : g ∈ M)
    (hcov : ∀ h ∈ M, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 M, h = c * o) : False := by
  obtain ⟨c, hc, o, ho, hgco⟩ := hcov g hgM
  have hzM : z ∈ M := hCM (mem_Cen_self z)
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcz' : z * c⁻¹ = c⁻¹ * z := (Commute.inv_right (show Commute z c from hcz.symm)).eq
  have hzc : z⁻¹ * c⁻¹ * z = c⁻¹ := by rw [mul_assoc, ← hcz', inv_mul_cancel_left]
  have hnorm := le_normalizer_pPrimeCoreOf M
  have hu : o * z * o⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 M := by
    have h1 : z * o⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 M :=
      (mem_normalizer_iff.mp (hnorm hzM) o⁻¹).mp ((pPrimeCoreOf 2 M).inv_mem ho)
    have : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
    rw [this]
    exact (pPrimeCoreOf 2 M).mul_mem ho h1
  have hu' : c * (o * z * o⁻¹ * z⁻¹) * c⁻¹ ∈ pPrimeCoreOf 2 M :=
    (mem_normalizer_iff.mp (hnorm (hCM hc)) _).mp hu
  have hv : v = (c * (o * z * o⁻¹ * z⁻¹) * c⁻¹) * z := by
    rw [← hg, hgco, mul_inv_rev]
    calc c * o * z * (o⁻¹ * c⁻¹) = c * (o * z * o⁻¹) * c⁻¹ := by group
      _ = c * (o * z * o⁻¹) * (z⁻¹ * c⁻¹ * z) := by rw [hzc]
      _ = _ := by group
  set u : G := c * (o * z * o⁻¹ * z⁻¹) * c⁻¹ with hu_def
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hv2' : v ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one v
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
  have hvzc : Commute v z := Subgroup.mem_centralizer_singleton_iff.mp hvC
  have hu_eq : u = v * z := by
    have := eq_mul_inv_of_mul_eq hv.symm
    rwa [hzinv] at this
  have hu_ne : u ≠ 1 := by
    intro h1
    rw [h1] at hu_eq
    have : v = z⁻¹ := eq_inv_of_mul_eq_one_left hu_eq.symm
    exact hvz (this.trans hzinv)
  have hu_sq : u ^ 2 = 1 := by
    rw [hu_eq, hvzc.mul_pow, hv2', hz2, one_mul]
  exact not_mem_pPrimeCoreOf_of_orderOf_two (orderOf_eq_prime hu_sq hu_ne) hu'

theorem lemma7_4_of (h72 : Lemma7_2) (h73 : Lemma7_3) (h34 : Leaf_Prop34) : Lemma7_4 := by
  intro G _ _ z k S M p hC Q V hQ hV v hv hv2 hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hCv : ∀ w ∈ V, w ≠ 1 → centralizer ({w} : Set G) ≤ M := h72 G z k S M p hC Q V hQ hV
  have hVle : V ≤ conjugate M g⁻¹ := by
    intro w hw
    rw [mem_conjugate_iff]
    have hwv : w * v = v * w := V_comm hV.four hw hv
    have hz' : z = g⁻¹ * v * g := by rw [← hg]; group
    refine hC.cen_le ?_
    rw [Subgroup.mem_centralizer_singleton_iff, hz']
    have e1 : g⁻¹ * w * g⁻¹⁻¹ * (g⁻¹ * v * g) = g⁻¹ * (w * v) * g := by group
    have e2 : g⁻¹ * v * g * (g⁻¹ * w * g⁻¹⁻¹) = g⁻¹ * (v * w) * g := by group
    rw [e1, e2, hwv]
  have hgM : g⁻¹ ∈ M := h73 G z k S M p hC V hV.four hCv g⁻¹ hVle
  have hvC : v ∈ Cen z := LC_le_Cen z (hV.le_L hv)
  have hvz : v ≠ z := fun h => V7.z_not_mem hC.orderOf_z hV (h ▸ hv)
  have h3 := h34 G z k S hC.ctx M hC.cen_le hC.coatom.1
  rcases h3 with hcov | hd | ⟨ε, q, L₁, L₂, hk, hL4, hq4, -⟩
  · exact not_cover_of_conj hC.orderOf_z hC.cen_le hvC hv2 hvz hg ((Subgroup.inv_mem_iff M).mp hgM) hcov
  · exact CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S hC.ctx hd
  · have hcase : CaseC z S := by
      rcases hL4.fusion with ⟨hq1, -⟩ | ⟨-, x, hx, -⟩
      · exfalso
        cases ε <;> simp at hq1 hq4 <;> omega
      · exact ⟨q, L₁, L₂, x, hL4.pair, hx⟩
    exact (hV.caseC hcase).1 v hv hv2 hconj

theorem lemma7_4_classes (h74 : Lemma7_4) {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hC : Ctx6 G z k S M p) {Q V : Subgroup G} (hQ : QP z p (Op p M) Q) (hV : V7 z S V) :
    ¬ ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  intro hall
  obtain ⟨v, hv, hv1⟩ := V_exists_ne_one hV.four
  have hv2 := V_orderOf_two hV.four hv hv1
  exact h74 G z k S M p hC Q V hQ hV v hv hv2 (hall z v hC.orderOf_z hv2)

end L74

section P71

theorem prop7_1_of (hV : V7_exists) (h72 : Lemma7_2) (h74 : Lemma7_4) (h75 : Lemma7_5) (h34 : Leaf_Prop34) :
    Prop7_1 := by
  intro G _ _ z k S M p hC Q hQ
  exfalso
  obtain ⟨V, hV7⟩ := hV G z k S hC.ctx
  have hk : k = Kind.m12 := h75 G z k S M p hC Q V hQ hV7
  subst hk
  have hCs : Group.IsSolvable ↥(Cen z) := cen_solvable_of_m12 hC.ctx
  obtain ⟨v, hv, hv1⟩ := V_exists_ne_one hV7.four
  have hv2 := V_orderOf_two hV7.four hv hv1
  have hnc : ¬ IsConj z v := h74 G z Kind.m12 S M p hC Q V hQ hV7 v hv hv2
  have hns := not_solvable_centralizer_of_nonCentral (hC.ctx.detail.m12 rfl v hv2 hnc)
  have hle : centralizer ({v} : Set G) ≤ M := h72 G z Kind.m12 S M p hC Q V hQ hV7 v hv hv1
  have hMns : ¬ Group.IsSolvable ↥M := fun hM =>
    hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  have h3 := h34 G z Kind.m12 S hC.ctx M hC.cen_le hC.coatom.1
  rcases h3 with hcov | hd | ⟨ε, q, L₁, L₂, hk, -⟩
  · exact hMns (solvable_of_cover hC.cen_le hCs hcov)
  · exact CFSG.GH74.GLS.Stage2.Final.Thm4.not_isDihedral_S hC.ctx hd
  · exact absurd hk (by simp)

end P71

end CFSG.GH74.GLS.Stage2.Bender.Thm1

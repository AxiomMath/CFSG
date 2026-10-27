module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYSzSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXCriterion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

section Inner

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal]

theorem exists_mul_mem_centralizer_of_quotientConj_eq (hperf : commutator L = ⊤) {x : X}
    {y : L ⧸ Subgroup.center L} (hxy : quotientConj L x = MulAut.conj y) :
    ∃ l : L, (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  set w := (l : X)⁻¹ * x with hwdef
  have hw : ∀ k : L, ((MulAut.conjNormal w k : L) : L ⧸ Subgroup.center L) =
      ((1 * k * 1⁻¹ : L) : L ⧸ Subgroup.center L) := by
    intro k
    rw [one_mul, inv_one, mul_one, ← quotientConj_mk, hwdef, map_mul, MulAut.mul_apply, hxy,
      MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      quotientConj_mk]
    congr 1
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  refine ⟨l, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h := congrArg Subtype.val
    (eq_conj_of_perfect hperf (MulAut.conjNormal w).toMonoidHom 1 hw ⟨k, hk⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, one_mul, inv_one, mul_one] at h
  calc k * w = w * k * w⁻¹ * w := by rw [h]
    _ = w * k := by group

theorem exists_mul_mem_centralizer_of_odd_outer (hperf : commutator L = ⊤)
    (hodd : Odd (Nat.card (Outer (L ⧸ Subgroup.center L)))) {x : X} (hx : orderOf x = 2) :
    ∃ l : L, (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
  obtain ⟨y, hy⟩ := quotientConj_mem_inner hodd (Subgroup.zpowers x)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
    ⟨x, Subgroup.mem_zpowers x⟩
  exact exists_mul_mem_centralizer_of_quotientConj_eq hperf hy.symm

end Inner

variable {X : Type} [Group X] [Finite X]

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem mul_self_ne_of_szModel
    (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eS : L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) {x : X} (hx : x ∈ L) :
    x * x ≠ e := by
  intro hxx
  have h1 := mul_self_eq_one_of_szModel hZ eS (k := ⟨x, hx⟩) (by
    rw [show (⟨x, hx⟩ * ⟨x, hx⟩ : L) = ⟨e, hL.mem⟩ from Subtype.ext hxx]
    exact hL.mem_center hc)
  have h2 := hc.order
  rw [← hxx, show x * x = 1 from congrArg Subtype.val h1, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem mem_of_szModel
    (hL : OneComponent Y e v L) (hZ : Nat.card (Subgroup.center L) = 2)
    (eS : L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) {t : X}
    (ht : orderOf t = 2) : t ∈ L := by
  have := hL.normal
  have hodd : Odd (Nat.card (Outer (L ⧸ Subgroup.center L))) :=
    odd_card_outer_of_mulEquiv_suzukiMatrixGroup le_rfl
      (eS.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup 1)))
  obtain ⟨l, hk⟩ := exists_mul_mem_centralizer_of_odd_outer hL.perfect hodd ht
  set k := (l : X)⁻¹ * t with hkdef
  have hlk : (l : X) * k = k * l := Subgroup.mem_centralizer_iff.mp hk l l.2
  have ht' : t = l * k := by rw [hkdef, mul_inv_cancel_left]
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hll : (l : X) * l * (k * k) = 1 := by
    rw [← htt, ht']
    calc (l : X) * l * (k * k) = l * (l * k) * k := by group
      _ = l * (k * l) * k := by rw [hlk]
      _ = l * k * (l * k) := by group
  have hllZ : l * l ∈ Subgroup.center L := mem_center_of_mem_centralizer (by
    rw [Subgroup.coe_mul, eq_inv_of_mul_eq_one_left hll]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hk hk))
  have hl1 : (l : X) * l = 1 := congrArg Subtype.val (mul_self_eq_one_of_szModel hZ eS hllZ)
  have hkk : k * k = 1 := by rwa [hl1, one_mul] at hll
  have hkL : k ∈ L := by
    by_cases hk1 : k = 1
    · rw [hk1]
      exact L.one_mem
    · rw [hL.eq_of_mem_centralizer k hk (orderOf_eq_prime (by rw [pow_two]; exact hkk) hk1)]
      exact hL.mem
  rw [ht']
  exact L.mul_mem l.2 hkL

end OneComponent

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem BadLift.false_of_szModel
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eS : L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) : False := by
  have hc := hu.baseConfig h hz hrank
  exact hu.not_embedded (hu.toEscapingLift.fusionStronglyEmbedded_of_quasiQuotient h hz (H := L)
    (fun t ht => hL.mem_of_szModel hZ eS (quasi_orderOf_mk u ht))
    (fun x hx => hL.mul_self_ne_of_szModel hc hZ eS hx))

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

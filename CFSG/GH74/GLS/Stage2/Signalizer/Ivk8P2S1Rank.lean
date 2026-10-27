module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.GH74.Uniqueness.SU.SU1Graph

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage12
open CFSG.GH74.Uniqueness.SU.SU1

section Gen

variable {G : Type} [Group G] {p : ℕ}

theorem three_le_pRank_of_elem [Finite G] (hp : p.Prime) {K A : Subgroup G} (hAK : A ≤ K)
    (hA : Open.IsElemAbelian p A) (hc : p ^ 3 ≤ Nat.card ↥A) : 3 ≤ CFSG.pRank p ↥K := by
  obtain ⟨j, hj⟩ := IsElemAbelian.exists_card hp hA
  have h1 : j ≤ Open.pRank p K := le_pRank hp.one_lt hAK hA hj
  have h2 : 3 ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hj ▸ hc)
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp]
  omega

theorem not_isCyclic_of_card (hp : p.Prime) {V : Subgroup G} (hV : IsElementaryAbelian p ↥V)
    (hc : p ^ 2 ≤ Nat.card ↥V) : ¬ IsCyclic ↥V := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = Nat.card ↥V := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : orderOf g ∣ p := (Monoid.order_dvd_exponent g).trans hV.exponent_dvd_p
  have h3 : orderOf g ≤ p := Nat.le_of_dvd hp.pos h2
  have h4 : p < p ^ 2 := by
    have := hp.one_lt
    nlinarith
  omega

theorem rank_centralizer_of_elem [Finite G] (hp : p.Prime) {P V : Subgroup G} (hVP : V ≤ P)
    (hV : Open.IsElemAbelian p V) (hc : p ^ 3 ≤ Nat.card ↥V) :
    ∀ v ∈ V, 3 ≤ CFSG.pRank p ↥(P ⊓ centralizer ({v} : Set G)) := by
  intro v hv
  refine three_le_pRank_of_elem hp (A := V) (fun a ha => Subgroup.mem_inf.2 ⟨hVP ha, ?_⟩) hV hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (isElemAbelian_iff.1 hV).1 a ha v hv

theorem Op_commute [Finite G] {K : Subgroup G} {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrq : r ≠ q) {x y : G} (hx : x ∈ Op r K) (hy : y ∈ Op q K) : x * y = y * x := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  have hdisj : Disjoint (pCore r ↥K) (pCore q ↥K) := by
    rw [Subgroup.disjoint_def]
    intro a ha1 ha2
    obtain ⟨i, hi⟩ := (pCore_isPGroup (p := r) (G := ↥K)) ⟨a, ha1⟩
    obtain ⟨j, hj⟩ := (pCore_isPGroup (p := q) (G := ↥K)) ⟨a, ha2⟩
    have hi' : a ^ (r ^ i) = 1 := congrArg Subtype.val hi
    have hj' : a ^ (q ^ j) = 1 := congrArg Subtype.val hj
    have hcop : Nat.Coprime (r ^ i) (q ^ j) := ((Nat.coprime_primes hr hq).2 hrq).pow _ _
    have h1 : orderOf a ∣ Nat.gcd (r ^ i) (q ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hi') (orderOf_dvd_of_pow_eq_one hj')
    rw [hcop] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have h := Subgroup.commute_of_normal_of_disjoint (pCore r ↥K) (pCore q ↥K) pCore_normal
    pCore_normal hdisj x' y' hx' hy'
  exact congrArg Subtype.val h

end Gen

section FM

variable {G : Type} [Group G] [Finite G]

theorem Op_le_Op_Fm {p : ℕ} (hp : p.Prime) (M : Subgroup G) : Op p M ≤ Op p (Fm M) :=
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20.le_Op_of_normalized p
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.Op_le_Fm p hp M)
    (fun _ hb _ hw => L193.Op_norm p M (CFSG.GH74.GLS.Stage2.Bender.Thm1.Fm_le M hb) hw)
    (CFSG.GH74.GLS.Stage2.Final.Thm6.L20.isPGroup_Op p M)

theorem Op_Fm_le_Op (r : ℕ) (M : Subgroup G) : Op r (Fm M) ≤ Op r M :=
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20.le_Op_of_normalized r
    (le_trans (Subgroup.map_subtype_le _) (CFSG.GH74.GLS.Stage2.Bender.Thm1.Fm_le M))
    (fun _ hb _ hw => CFSG.GH74.GLS.Stage2.Final.Thm6.L20.Op_conj_mem r
      (fun _ hc _ hb' => CFSG.GH74.GLS.Stage2.Final.Thm6.L20.Fm_conj_mem M hc hb') hb hw)
    (CFSG.GH74.GLS.Stage2.Final.Thm6.L20.isPGroup_Op r (Fm M))

theorem le_Op_Fm_of_pow {r : ℕ} (hr : r.Prime) {X : Subgroup G} {M : Subgroup G}
    (hXF : X ≤ Fm M) (hX : ∀ x ∈ X, x ^ r = 1) : X ≤ Op r (Fm M) := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · have : Fact r.Prime := ⟨hr⟩
    exact CFSG.GH74.GLS.Stage2.Final.Thm6.L20.mem_Op_of_orderOf_prime
      (CFSG.GH74.GLS.Stage2.Final.Thm6.L20.Fm_isNilpotent M) (hXF hx)
      (orderOf_eq_prime (hX x hx) hx1)

theorem Fof_le_Fm {p : ℕ} (hp : p.Prime) (M U : Subgroup G) : Fof p M U ≤ Fm M := by
  refine sup_le (inf_le_left.trans (CFSG.GH74.GLS.Stage2.Bender.Thm1.Op_le_Fm p hp M)) ?_
  exact iSup₂_le fun q _ => Subgroup.map_subtype_le _

end FM

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}

theorem rank_Q (h : CtxP G z k S M p) {U : Subgroup G} (hUP : U ≤ Op p M)
    (hUn : (U.subgroupOf (Op p M)).Normal) (hUe : IsElementaryAbelian p ↥U)
    (hUc : Nat.card ↥U = p ^ 2) : 3 ≤ Open.pRank p (Qof p M U) := by
  have hPp : IsPGroup p ↥(Op p M) := CFSG.GH74.GLS.Stage2.Final.Thm6.L20.isPGroup_Op p M
  have hNE : IsNormalEp2 p (Op p M) U := by
    refine ⟨hUP, fun g' hg' => ?_,
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hUe, hUc⟩
    have hn : ∀ g ∈ Op p M, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun g hg u hu =>
      hUn.conj_mem ⟨u, hUP hu⟩ (mem_subgroupOf.2 hu) ⟨g, hg⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hn g' hg' u hu, fun hu => ?_⟩
    have := hn g'⁻¹ ((Op p M).inv_mem hg') _ hu
    have e : g'⁻¹ * (g' * u * g'⁻¹) * g'⁻¹⁻¹ = u := by group
    rwa [e] at this
  obtain ⟨-, -, hrk⟩ := ig10_20_ii h.prime hPp hNE
  have h3 : 3 ≤ Open.pRank p (Op p M) := by
    have := h.rank
    rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank h.prime] at this
  unfold Qof
  rw [inf_comm, hrk]
  exact h3

theorem exists_V_b (h : CtxP G z k S M p) {U : Subgroup G} (hUP : U ≤ Op p M)
    (hUn : (U.subgroupOf (Op p M)).Normal) (hUe : IsElementaryAbelian p ↥U)
    (hUc : Nat.card ↥U = p ^ 2) {V : Subgroup G} (hVQ : V ≤ Qof p M U)
    (hVe : IsElementaryAbelian p ↥V) :
    ∀ v ∈ V, 3 ≤ CFSG.pRank p ↥(Op p M ⊓ centralizer ({v} : Set G)) := by
  intro v hv
  have hU' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hUe
  have hV' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p V).mp hVe
  have hcomm : ∀ u ∈ U, ∀ w ∈ V, u * w = w * u := fun u hu w hw =>
    mem_centralizer_iff.1 (hVQ hw).2 u hu
  have hA := IsElemAbelian.sup hU' hV' hcomm
  have hAP : U ⊔ V ≤ Op p M := sup_le hUP (hVQ.trans inf_le_left)
  obtain ⟨j, hj⟩ := IsElemAbelian.exists_card h.prime hA
  have hUA : U ≤ U ⊔ V := le_sup_left
  have h2j : 2 ≤ j := by
    have := Subgroup.card_le_of_le hUA
    rw [hUc, hj] at this
    exact (Nat.pow_le_pow_iff_right h.prime.one_lt).mp this
  by_cases hj3 : 3 ≤ j
  · exact rank_centralizer_of_elem h.prime hAP hA
      (by rw [hj]; exact Nat.pow_le_pow_right h.prime.pos hj3) v (mem_sup_right hv)
  · have hj2 : j = 2 := by omega
    have hUeqA : U ⊔ V = U := (Subgroup.eq_of_le_of_card_ge hUA
      (by rw [hUc, hj, hj2])).symm
    have hvU : v ∈ U := hUeqA ▸ mem_sup_right hv
    have hQc : Qof p M U ≤ Op p M ⊓ centralizer ({v} : Set G) := fun q hq =>
      Subgroup.mem_inf.2 ⟨hq.1, Subgroup.mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 hq.2 v hvU).symm⟩
    have h3 := rank_Q h hUP hUn hUe hUc
    have h4 := CFSG.SectionRank.pRank_mono h.prime.one_lt hQc
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank h.prime]
    omega

theorem exists_V_a (h : CtxP G z k S M p) (hMC : M = Cen z) {U : Subgroup G} (hUP : U ≤ Op p M)
    (hUn : (U.subgroupOf (Op p M)).Normal) (hUe : IsElementaryAbelian p ↥U)
    (hUc : Nat.card ↥U = p ^ 2) {H X : Subgroup G} (hXF : X ≤ Fof p M U) {r : ℕ}
    (hr : r.Prime) (hXe : IsElementaryAbelian r ↥X) (hXH : normalizer (X : Set G) ≤ H) :
    z ∈ H ∧ ∃ V : Subgroup G, V ≤ Op p M ∧ IsElementaryAbelian p ↥V ∧ p ^ 3 ≤ Nat.card ↥V ∧
      V ≤ H := by
  have hp := h.prime
  have hU' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hUe
  have hFM : Fof p M U ≤ Fm M := Fof_le_Fm hp M U
  have hXFm : X ≤ Fm M := hXF.trans hFM
  have hXM : X ≤ M := hXFm.trans (CFSG.GH74.GLS.Stage2.Bender.Thm1.Fm_le M)
  have hz : z ∈ H := by
    refine hXH (Subgroup.centralizer_le_normalizer (X : Set G) ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hXM hx
    rw [hMC, Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  refine ⟨hz, ?_⟩
  have hXE := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r X).mp hXe
  have hXpow : ∀ x ∈ X, x ^ r = 1 := (isElemAbelian_iff.1 hXE).2
  have hXOp : X ≤ Op r (Fm M) := le_Op_Fm_of_pow hr hXFm hXpow
  obtain ⟨E₃, hE₃Q, hE₃e, hE₃c⟩ :=
    exists_isElemAbelian_of_le_pRank hp (rank_Q h hUP hUn hUe hUc)
  have hE₃P : E₃ ≤ Op p M := hE₃Q.trans inf_le_left
  have hE₃elem : IsElementaryAbelian p ↥E₃ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₃).mpr hE₃e
  have hE₃c' : p ^ 3 ≤ Nat.card ↥E₃ := hE₃c.ge
  by_cases hrp : r = p
  · subst hrp
    have hXP : X ≤ Op r M := hXOp.trans (Op_Fm_le_Op r M)
    have hFC : Fof r M U ≤ centralizer (U : Set G) := by
      refine sup_le inf_le_right (iSup₂_le fun q hq y hy => ?_)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact Op_commute hp hq.1 (Ne.symm hq.2.2) (Op_le_Op_Fm hp M (hUP hu)) hy
    have hXQ : X ≤ Qof r M U := fun x hx => Subgroup.mem_inf.2 ⟨hXP hx, hFC (hXF hx)⟩
    by_cases hXU : X ≤ U
    · refine ⟨E₃, hE₃P, hE₃elem, hE₃c', fun a ha => hXH ?_⟩
      refine Subgroup.centralizer_le_normalizer (X : Set G) ?_
      exact Subgroup.centralizer_le (show (X : Set G) ⊆ (U : Set G) from hXU) (hE₃Q ha).2
    · have hcomm : ∀ u ∈ U, ∀ x ∈ X, u * x = x * u := fun u hu x hx =>
        mem_centralizer_iff.1 (hXQ hx).2 u hu
      have hA := IsElemAbelian.sup hU' hXE hcomm
      refine ⟨U ⊔ X, sup_le hUP (hXQ.trans inf_le_left),
        (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).mpr hA, ?_, ?_⟩
      · obtain ⟨j, hj⟩ := IsElemAbelian.exists_card hp hA
        have hlt : U < U ⊔ X := lt_of_le_of_ne le_sup_left (fun heq => hXU (heq ▸ le_sup_right))
        have h1 := Subgroup.card_lt_of_lt hlt
        rw [hUc, hj] at h1
        have h2 : 3 ≤ j := by
          have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
          omega
        rw [hj]
        exact Nat.pow_le_pow_right hp.pos h2
      · intro a ha
        refine hXH (Subgroup.centralizer_le_normalizer (X : Set G) ?_)
        have hle : U ⊔ X ≤ centralizer (X : Set G) := by
          refine sup_le (fun u hu => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact (hcomm u hu y hy).symm
          · rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact (isElemAbelian_iff.1 hXE).1 y hy x hx
        exact hle ha
  · have hQX : Qof p M U ≤ centralizer (X : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Op_commute hr hp hrp (hXOp hx) (Op_le_Op_Fm hp M hq.1)
    exact ⟨E₃, hE₃P, hE₃elem, hE₃c', fun a ha =>
      hXH (Subgroup.centralizer_le_normalizer (X : Set G) (hQX (hE₃Q ha)))⟩

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S1

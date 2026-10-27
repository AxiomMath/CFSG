module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.PLengthOneNormalSeries
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.NormalModularSubgroupIrreducibleTrivial
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.PrimeChiefFactorsCoprimeQuotient
import CFSG.FeitThompson.Local.OddRankTwoAutomorphismDerivedPrimePower
import CFSG.FeitThompson.Local.RankTwoTrivialPprimeCoreAbelianQuotient

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

theorem commutator_le_of_le_ker_quotientFactorConj (X Y : Subgroup G) [X.Normal] [Y.Normal]
    {L : Subgroup G} (h : L ≤ (quotientFactorConj X Y).ker) : ⁅L, X⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro l hl x hx
  have h1 : ((quotientFactorConj X Y l ⟨(x : G ⧸ Y), mk_mem_quotientFactor X Y hx⟩ :
      ↥(quotientFactor X Y)) : G ⧸ Y) = (x : G ⧸ Y) := by rw [h hl]; rfl
  rw [coe_quotientFactorConj_apply] at h1
  have h2 : ((l : G ⧸ Y)) * (x : G ⧸ Y) * ((l : G ⧸ Y))⁻¹ = (x : G ⧸ Y) := h1
  rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
  have h3 : ((l * x * l⁻¹ * x⁻¹ : G) : G ⧸ Y)
      = ((l : G ⧸ Y) * (x : G ⧸ Y) * ((l : G ⧸ Y))⁻¹) * ((x : G ⧸ Y))⁻¹ := rfl
  rw [h3, h2, mul_inv_cancel]

theorem eq_of_mulEquiv_of_isPGroup [Finite G] {X Y : Subgroup G} [Y.Normal] {p r d : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hd : 1 ≤ d) (hpX : IsPGroup p (↥X ⧸ Y.subgroupOf X))
    (e : ↥(quotientFactor X Y) ≃* Multiplicative (Fin d → ZMod r)) : r = p := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpX
  have hcard : Nat.card ↥(quotientFactor X Y) = r ^ d := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcard2 : Nat.card ↥(quotientFactor X Y) = p ^ k := by
    rw [← Nat.card_congr (quotientFactorMulEquiv X Y).toEquiv, hk]
  exact (Nat.prime_dvd_prime_iff_eq hr hp).1
    (hr.dvd_of_dvd_pow (show r ∣ p ^ k by rw [← hcard2, hcard]; exact dvd_pow_self r (by omega)))

theorem odd_of_relIndex_eq_pow_of_odd [Finite G] {p k : ℕ} (hp : p.Prime) (hodd : Odd (Nat.card G))
    {X Y : Subgroup G} (hYX : Y < X) (hk : Y.relIndex X = p ^ k) : Odd p := by
  refine hp.odd_of_ne_two fun hp2 => ?_
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exfalso
      rw [pow_zero, Subgroup.relIndex, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hk
      exact absurd (le_antisymm hYX.le hk) hYX.ne
    · exact hk1
  have hdvd : p ∣ Nat.card G := by
    refine dvd_trans ?_ ((Subgroup.relIndex_dvd_index_of_le hYX.le).trans Y.index_dvd_card)
    rw [hk]; exact dvd_pow_self p (by omega)
  rw [hp2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem le_sup_of_not_dvd_relIndex [Finite G] {p : ℕ} (hp : p.Prime) {N X Y R : Subgroup G}
    [Y.Normal] [R.Normal] (hYX : Y ≤ X) (hXN : X ≤ N) (hRN : R ≤ N)
    (hpX : IsPGroup p (↥X ⧸ Y.subgroupOf X)) (hR : ¬ p ∣ R.relIndex N) : X ≤ Y ⊔ R := by
  have := Fact.mk hp
  set A : Subgroup G := Y ⊔ R with hA
  have hAN : A ≤ N := sup_le (hYX.trans hXN) hRN
  set m := A.relIndex X with hm
  have h1 : m ∣ Y.relIndex X :=
    Subgroup.index_dvd_of_le (Subgroup.comap_mono (le_sup_left : Y ≤ A))
  have h2 : Y.relIndex X = Nat.card (↥X ⧸ Y.subgroupOf X) := (Subgroup.index_eq_card _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpX
  have h3 : m = Nat.card (Subgroup.map (mk' A) X) := by
    rw [hm, ← Subgroup.relIndex_ker X (mk' A), QuotientGroup.ker_mk']
  have h4 : A.relIndex N = Nat.card (Subgroup.map (mk' A) N) := by
    rw [← Subgroup.relIndex_ker N (mk' A), QuotientGroup.ker_mk']
  have h5 : m ∣ A.relIndex N := by
    rw [h3, h4]; exact Subgroup.card_dvd_of_le (Subgroup.map_mono hXN)
  have h6 : A.relIndex N ∣ R.relIndex N :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex R A N le_sup_right hAN)
  have hpm : ¬ p ∣ m := fun hd => hR (hd.trans (h5.trans h6))
  have hm1 : m = 1 := by
    have hdvd : m ∣ p ^ k := by rw [← hk, ← h2]; exact h1
    obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hje
    · exact absurd (hje ▸ dvd_pow_self p (by omega)) hpm
  exact Subgroup.relIndex_eq_one.1 hm1

theorem isPGroup_map_of_ker_le {p : ℕ} [Fact p.Prime] {K₁ K₂ : Type*} [Group K₁] [Group K₂]
    [Finite K₁] [Finite K₂] (f : G →* K₁) (t : G →* K₂) (hker : f.ker ≤ t.ker) (S : Subgroup G)
    (hS : IsPGroup p (Subgroup.map f S)) : IsPGroup p (Subgroup.map t S) := by
  have h1 : Nat.card (Subgroup.map t S) ∣ Nat.card (Subgroup.map f S) := by
    rw [← Subgroup.relIndex_ker S f, ← Subgroup.relIndex_ker S t]
    exact Subgroup.index_dvd_of_le (Subgroup.comap_mono hker)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  exact IsPGroup.of_card_dvd_pow (hn ▸ h1)

theorem map_equivMapOfInjective_subgroupOf (N : Subgroup G) (S T : Subgroup ↥N) :
    Subgroup.map (Subgroup.equivMapOfInjective T N.subtype N.subtype_injective : ↥T →* _)
        (S.subgroupOf T) = (S.map N.subtype).subgroupOf (T.map N.subtype) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t : ↥N), ht, rfl⟩
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨t', ht', ht'x⟩ := x.2
    have hst : s = t' := N.subtype_injective (hsx.trans ht'x.symm)
    exact ⟨⟨s, hst ▸ ht'⟩, hs, Subtype.ext hsx⟩

noncomputable def factorMulEquivMapSubtype (N : Subgroup G) (S T : Subgroup ↥N) [S.Normal]
    [((S.map N.subtype).subgroupOf (T.map N.subtype)).Normal] :
    ↥T ⧸ S.subgroupOf T ≃*
      ↥(T.map N.subtype) ⧸ (S.map N.subtype).subgroupOf (T.map N.subtype) :=
  QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective T N.subtype N.subtype_injective)
    (map_equivMapOfInjective_subgroupOf N S T)

instance pComplPCore_characteristic (p : ℕ) (X : Type*) [Group X] [Finite X] :
    (pComplPCore p X).Characteristic := by
  rw [pComplPCore_eq_comap]
  exact Subgroup.Characteristic.comap_quotient_mk inferInstance

theorem elementaryAbelianPRank_quotient_pComplCore_pComplPCore_le {p : ℕ} (hp : p.Prime)
    (X : Type*) [Group X] [Finite X] :
    elementaryAbelianPRank p (↥(pComplPCore p X) ⧸ (pComplCore p X).subgroupOf (pComplPCore p X))
      ≤ elementaryAbelianPRank p X := by
  rw [elementaryAbelianPRank_eq_of_mulEquiv (p := p) hp.one_lt
    (quotientFactorMulEquiv (pComplPCore p X) (pComplCore p X))]
  refine (elementaryAbelianPRank_subgroup_le hp.one_lt _).trans ?_
  exact le_of_eq (elementaryAbelianPRank_quotient_eq hp
    ((hp.coprime_iff_not_dvd).2 (not_dvd_natCard_pComplCore hp X)))

theorem not_dvd_index_pComplPCore {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (X : Type*) [Group X]
    [Finite X] [Group.IsSolvable X] (hodd : Odd (Nat.card X))
    (hrank : elementaryAbelianPRank p X ≤ 2) : ¬ p ∣ (pComplPCore p X).index := by
  rw [index_pComplPCore]
  have hcop := (hp.coprime_iff_not_dvd).2 (not_dvd_natCard_pComplCore hp X)
  refine not_dvd_index_pCore_of_pComplCore_eq_bot hp hpodd
    (hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card (pComplCore p X)))
    (pComplCore_quotient_pComplCore p X) ?_
  rw [elementaryAbelianPRank_quotient_eq hp hcop]
  exact hrank

theorem commutator_le_of_isChiefFactor_of_controlled [Finite G] [Group.IsSolvable G] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hodd : Odd (Nat.card G)) {X Y D T : Subgroup G} [X.Normal]
    [Y.Normal] [D.Normal] [T.Normal] (h : IsChiefFactor X Y)
    (hpXY : IsPGroup p (↥X ⧸ Y.subgroupOf X)) (hVp : IsPGroup p (↥T ⧸ D.subgroupOf T))
    (hVrank : elementaryAbelianPRank p (↥T ⧸ D.subgroupOf T) ≤ 2) (hXYT : X ≤ Y ⊔ T)
    (hXDY : X ⊓ D ≤ Y) : ⁅_root_.commutator G, X⁆ ≤ Y := by
  have := Fact.mk hp
  set σ : G →* MulAut (↥T ⧸ D.subgroupOf T) := factorConj T D with hσ
  have hkerle : σ.ker ≤ (quotientFactorConj X Y).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [coe_quotientFactorConj_apply]
    obtain ⟨x, hx, hxa⟩ := (mem_quotientFactor X Y).1 a.2
    change (g : G ⧸ Y) * (a : G ⧸ Y) * ((g : G ⧸ Y))⁻¹ = (a : G ⧸ Y)
    rw [← hxa]
    obtain ⟨y, hy, t, ht, hyt⟩ := Subgroup.mem_sup_of_normal_right.1 (hXYT hx)
    have htX : t ∈ X := by
      have hmul : y⁻¹ * (y * t) ∈ X := X.mul_mem (X.inv_mem (h.le hy)) (hyt ▸ hx)
      simpa using hmul
    have h1 : (QuotientGroup.mk (MulAut.conjNormal g ⟨t, ht⟩) : ↥T ⧸ D.subgroupOf T)
        = QuotientGroup.mk ⟨t, ht⟩ := by
      rw [← factorConj_apply_mk T D g ⟨t, ht⟩, ← hσ, hg]; rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have hu : (g * t * g⁻¹)⁻¹ * t ∈ D := by
      simpa [MulAut.conjNormal_apply] using h1
    have hc : g * t * g⁻¹ * t⁻¹ ∈ D := by
      have hcj := ‹D.Normal›.conj_mem _ (D.inv_mem hu) t
      have heq : t * ((g * t * g⁻¹)⁻¹ * t)⁻¹ * t⁻¹ = g * t * g⁻¹ * t⁻¹ := by group
      rwa [heq] at hcj
    have hcY : g * t * g⁻¹ * t⁻¹ ∈ Y :=
      hXDY ⟨X.mul_mem (‹X.Normal›.conj_mem _ htX g) (X.inv_mem htX), hc⟩
    have hmem : g * x * g⁻¹ * x⁻¹ ∈ Y := by
      subst hyt
      have heq : g * (y * t) * g⁻¹ * (y * t)⁻¹
          = (g * y * g⁻¹) * (g * t * g⁻¹ * t⁻¹) * y⁻¹ := by group
      rw [heq]
      exact Y.mul_mem (Y.mul_mem (‹Y.Normal›.conj_mem _ hy g) hcY) (Y.inv_mem hy)
    have hone : ((g * x * g⁻¹ * x⁻¹ : G) : G ⧸ Y) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
    have hcast : ((g * x * g⁻¹ * x⁻¹ : G) : G ⧸ Y)
        = (g : G ⧸ Y) * (x : G ⧸ Y) * ((g : G ⧸ Y))⁻¹ * ((x : G ⧸ Y))⁻¹ := rfl
    rw [hcast] at hone
    exact mul_inv_eq_one.1 hone
  have hσp : IsPGroup p (Subgroup.map σ (_root_.commutator G)) := by
    rw [map_commutator_eq]
    exact isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hpodd hVp
      hVrank (hodd.of_dvd_nat (Subgroup.card_range_dvd σ))
  have hτp : IsPGroup p (Subgroup.map (quotientFactorConj X Y) (_root_.commutator G)) :=
    isPGroup_map_of_ker_le σ (quotientFactorConj X Y) hkerle _ hσp
  obtain ⟨r, d, hr, hd, e, -⟩ := exists_prime_mulEquiv_isIrreducible_of_isChiefFactor X Y h
  have hrp : r = p := eq_of_mulEquiv_of_isPGroup hp hr hd hpXY e
  subst hrp
  set M : Subgroup (MulAut ↥(quotientFactor X Y)) := (quotientFactorConj X Y).range with hM
  have hntQF : Nontrivial ↥(quotientFactor X Y) := nontrivial_quotientFactor X Y h.lt
  have hirr : (representationOfMulAut r M.subtype e).IsIrreducible := by
    refine isIrreducible_representationOfMulAut r _ e fun S hS => ?_
    refine eq_bot_or_eq_top_of_quotientFactorConj_invariant X Y h S fun g q hq => ?_
    exact hS ⟨quotientFactorConj X Y g, ⟨g, rfl⟩⟩ q hq
  have hUp : IsPGroup r (_root_.commutator ↥M) := by
    have h1 : Subgroup.map M.subtype (_root_.commutator ↥M)
        = Subgroup.map (quotientFactorConj X Y) (_root_.commutator G) := by
      rw [Subgroup.map_subtype_commutator, map_commutator_eq]
    have h2 : IsPGroup r ↥(Subgroup.map M.subtype (_root_.commutator ↥M)) := by rw [h1]; exact hτp
    exact IsPGroup.of_equiv h2
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hUp
  have hker := le_ker_of_isIrreducible (U := _root_.commutator ↥M) (a := a) ha hirr
  refine commutator_le_of_le_ker_quotientFactorConj X Y (L := _root_.commutator G) fun g hg => ?_
  have hmem : quotientFactorConj X Y g ∈ Subgroup.map M.subtype (_root_.commutator ↥M) := by
    rw [Subgroup.map_subtype_commutator, ← map_commutator_eq]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨u, hu, hug⟩ := hmem
  have h4 : ∀ q : ↥(quotientFactor X Y), (M.subtype u) q = q := by
    intro q
    have h5 := representationOfMulAut_apply_toAdd (r := r) M.subtype e u q
    rw [MonoidHom.mem_ker.1 (hker hu)] at h5
    simp only [Module.End.one_apply] at h5
    exact (e.injective (Multiplicative.toAdd.injective h5)).symm
  have hone : M.subtype u = (1 : MulAut ↥(quotientFactor X Y)) :=
    MulEquiv.ext fun q => (h4 q).trans rfl
  rw [MonoidHom.mem_ker, ← hug, hone]

theorem commutator_le_of_isChiefFactor_of_elementaryAbelianPRank_le_two [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    [N.Normal] (hrank : elementaryAbelianPRank p ↥N ≤ 2) {X Y : Subgroup G}
    (h : IsChiefFactor X Y) (hpXY : ∃ k : ℕ, Y.relIndex X = p ^ k) (hXN : X ≤ N) :
    ⁅_root_.commutator G, X⁆ ≤ Y := by
  have := Fact.mk hp
  have hX := h.normal_num
  have hY := h.normal_den
  have hsolvN : Group.IsSolvable ↥N := isSolvable_of_le (le_top : N ≤ ⊤)
  have hoddN : Odd (Nat.card ↥N) := hodd.of_dvd_nat N.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := hpXY
  have hpXY : IsPGroup p (↥X ⧸ Y.subgroupOf X) :=
    IsPGroup.of_card (n := k) (((Subgroup.index_eq_card (Y.subgroupOf X)).symm).trans hk)
  have hpodd : Odd p := odd_of_relIndex_eq_pow_of_odd hp hodd h.lt hk
  set D : Subgroup G := Subgroup.map N.subtype (pComplCore p ↥N) with hD
  set T : Subgroup G := Subgroup.map N.subtype (pComplPCore p ↥N) with hT
  have hDnormal : D.Normal := ConjAct.normal_of_characteristic_of_normal
  have hTnormal : T.Normal := ConjAct.normal_of_characteristic_of_normal
  have hDTnormal : (D.subgroupOf T).Normal := hDnormal.subgroupOf _
  have hTsub : T.subgroupOf N = pComplPCore p ↥N :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hequiv : ↥(pComplPCore p ↥N) ⧸ (pComplCore p ↥N).subgroupOf (pComplPCore p ↥N)
      ≃* ↥T ⧸ D.subgroupOf T := factorMulEquivMapSubtype N _ _
  have hVp : IsPGroup p (↥T ⧸ D.subgroupOf T) :=
    IsPGroup.of_equiv isPGroup_quotient_pComplCore_subgroupOf hequiv
  have hVrank : elementaryAbelianPRank p (↥T ⧸ D.subgroupOf T) ≤ 2 :=
    (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt hequiv).symm.trans_le
      ((elementaryAbelianPRank_quotient_pComplCore_pComplPCore_le hp ↥N).trans hrank)
  have hXDY : X ⊓ D ≤ Y := by
    refine inf_le_of_coprime_of_isPGroup (N := D) ?_ hpXY
    rw [hD, Subgroup.card_map_of_injective N.subtype_injective]
    exact ((hp.coprime_iff_not_dvd).2 (not_dvd_natCard_pComplCore hp ↥N)).symm
  have hXYT : X ≤ Y ⊔ T := by
    refine le_sup_of_not_dvd_relIndex hp h.le hXN (Subgroup.map_subtype_le _) hpXY ?_
    rw [show T.relIndex N = (pComplPCore p ↥N).index by rw [Subgroup.relIndex, hTsub]]
    exact not_dvd_index_pComplPCore hp hpodd ↥N hoddN hrank
  exact commutator_le_of_isChiefFactor_of_controlled hp hpodd hodd h hpXY hVp hVrank hXYT hXDY

theorem commutator_le_of_isChiefFactor_of_elementaryAbelianPRank_le_two' [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    [N.Normal] (hrank : elementaryAbelianPRank p ↥N ≤ 2) {X Y : Subgroup G}
    (h : IsChiefFactor X Y) (hpXY : ∃ k : ℕ, Y.relIndex X = p ^ k) (hXN : X ≤ N) :
    ⁅Subgroup.closure {g : G | ∃ a ∈ (⊤ : Subgroup G), ∃ b ∈ (⊤ : Subgroup G),
      a⁻¹ * b⁻¹ * a * b = g}, X⁆ ≤ Y := by
  rw [closure_setOf_inv_mul_inv_mul_mul, ← _root_.commutator_def]
  exact commutator_le_of_isChiefFactor_of_elementaryAbelianPRank_le_two hodd hp hrank h hpXY hXN

end

end CFSG.FeitThompson

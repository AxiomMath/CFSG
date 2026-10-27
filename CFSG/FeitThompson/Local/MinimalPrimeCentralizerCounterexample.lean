module

public import CFSG.FeitThompson.Definitions.AdmissibleCoprimeActionQuadruple
public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Local.CoprimeDisplacementFixedInDerived
public import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition
import CFSG.FeitThompson.Local.PLengthOneQuotientLift
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.PSubgroupCentralizersLiftQuotient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup
open scoped commutatorElement

universe u

variable {G : Type*} [Group G] {p : ℕ}

attribute [local instance] conjMulDistribMulAction

theorem isZGroup_of_le {S W : Subgroup G} [IsZGroup ↥W] (h : S ≤ W) : IsZGroup ↥S :=
  IsZGroup.of_injective (f := S.subtype.codRestrict W fun x => h x.2)
    fun _ _ hab => Subtype.ext (by simpa using hab)

theorem isZGroup_of_map_subtype_le {K : Subgroup G} (T : Subgroup ↥K) {W : Subgroup G}
    [IsZGroup ↥W] (h : T.map K.subtype ≤ W) : IsZGroup ↥T :=
  IsZGroup.of_injective (f := (K.subtype.comp T.subtype).codRestrict W fun x => h ⟨x, x.2, rfl⟩)
    fun _ _ hab => Subtype.ext (Subtype.ext (by simpa using hab))

theorem isZGroup_map {G' : Type*} [Group G'] {W : Subgroup G} [Finite ↥W] [IsZGroup ↥W]
    (f : G →* G') : IsZGroup ↥(W.map f) := by
  refine IsZGroup.of_surjective (f := (f.comp W.subtype).codRestrict (W.map f)
    fun x => ⟨x, x.2, rfl⟩) ?_
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem normal_commutator_of_sup_eq_top {H R : Subgroup G} (hsup : H ⊔ R = ⊤) :
    (⁅H, R⁆ : Subgroup G).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup, sup_le_iff]
  exact ⟨Subgroup.normalizer_commutator_ge_left H R, Subgroup.normalizer_commutator_ge_right H R⟩

theorem subgroupOf_inf {K J A : Subgroup G} :
    (J ⊓ A).subgroupOf K = J.subgroupOf K ⊓ A.subgroupOf K := Subgroup.comap_inf _ _ _

theorem commutator_subgroupOf {K J A : Subgroup G} (hJ : J ≤ K) (hA : A ≤ K) :
    ⁅J.subgroupOf K, A.subgroupOf K⁆ = ⁅J, A⁆.subgroupOf K := by
  refine Subgroup.map_injective K.subtype_injective ?_
  rw [Subgroup.map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_eq_left.2 hJ, inf_eq_left.2 hA,
      inf_eq_left.2 (Subgroup.commutator_le.2 fun a ha b hb =>
        mul_mem (mul_mem (mul_mem (hJ ha) (hA hb)) (K.inv_mem (hJ ha))) (K.inv_mem (hA hb)))]

theorem natCard_map_mk'_of_inf_eq_bot {D S : Subgroup G} [D.Normal] (h : D ⊓ S = ⊥) :
    Nat.card ↥(S.map (mk' D)) = Nat.card ↥S := by
  have hker : ((mk' D).comp S.subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hmem : (x : G) ∈ D ⊓ S :=
      ⟨by simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hx, x.2⟩
    rw [h] at hmem
    exact Subtype.ext (by simpa using hmem)
  rw [show S.map (mk' D) = ((mk' D).comp S.subtype).range by
    rw [MonoidHom.range_comp, Subgroup.subtype_range]]
  exact (Nat.card_congr (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).1 hker)).toEquiv).symm

noncomputable def quotientSubgroupOfEquivMapMk' (H D : Subgroup G) [D.Normal] :
    (↥H ⧸ D.subgroupOf H) ≃* ↥(H.map (mk' D)) :=
  (QuotientGroup.quotientMulEquivOfEq (M := ((mk' D).comp H.subtype).ker)
    (N := D.subgroupOf H) (by
      ext x
      simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf])).symm.trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.subtype_range])))

theorem index_lt_natCard [Finite G] {D : Subgroup G} (hD : D ≠ ⊥) : D.index < Nat.card G := by
  have h := Subgroup.card_mul_index D
  have h1 : 1 < Nat.card ↥D := (Subgroup.one_lt_card_iff_ne_bot D).2 hD
  have hidx : 0 < D.index := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at h; exact Nat.card_pos.ne h
  calc D.index = 1 * D.index := (one_mul _).symm
    _ < Nat.card ↥D * D.index := Nat.mul_lt_mul_of_lt_of_le h1 le_rfl hidx
    _ = Nat.card G := h

instance pComplCore_map_subtype_normal (H : Subgroup G) [H.Normal] [Finite G] :
    ((pComplCore p ↥H).map H.subtype).Normal := ConjAct.normal_of_characteristic_of_normal

theorem isAdmissible_subgroupOf {H R R0 : Subgroup G}
    (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0) {B : Subgroup G} (hBH : B ≤ H)
    (hBnormal : B.Normal) :
    IsAdmissibleCoprimeActionQuadruple ↥(B ⊔ R) (B.subgroupOf (B ⊔ R))
      (R.subgroupOf (B ⊔ R)) (R0.subgroupOf (B ⊔ R)) := by
  have hsolv : Group.IsSolvable G := hadm.isSolvable
  have hZ := hadm.isZGroup_centralizer
  set K : Subgroup G := B ⊔ R with hKdef
  have hBK : B ≤ K := le_sup_left
  have hRK : R ≤ K := le_sup_right
  have hR0K : R0 ≤ K := hadm.le.trans hRK
  refine ⟨inferInstance, hadm.odd_card_subgroup K, hBnormal.subgroupOf K, ?_, ?_, ?_,
    Subgroup.comap_mono hadm.le, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hBK hRK, ← hKdef, subgroupOf_self]
  · rw [← subgroupOf_inf, show B ⊓ R = ⊥ from
      le_bot_iff.1 (le_trans (inf_le_inf_right R hBH) (le_of_eq hadm.inf_eq_bot)),
      Subgroup.bot_subgroupOf]
  · rw [natCard_subgroupOf_of_le hBK, natCard_subgroupOf_of_le hRK]
    exact hadm.coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hBH)
  · rw [natCard_subgroupOf_of_le hR0K]; exact hadm.prime_card
  · refine isZGroup_of_map_subtype_le (W := centralizer (R0 : Set G) ⊓ H) _ ?_
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val ((mem_centralizer_iff.1 hy1) (⟨g, hR0K hg⟩ : ↥K)
        (by simpa [Subgroup.mem_subgroupOf] using hg)),
      hBH (Subgroup.mem_subgroupOf.1 hy2)⟩

theorem isAdmissible_map_mk' {H R R0 : Subgroup G} [Finite G]
    (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
    {D : Subgroup G} [D.Normal] (hDH : D ≤ H) :
    IsAdmissibleCoprimeActionQuadruple (G ⧸ D) (H.map (mk' D)) (R.map (mk' D))
      (R0.map (mk' D)) := by
  have hHn := hadm.normal
  have hsolv : Group.IsSolvable G := hadm.isSolvable
  have hZ := hadm.isZGroup_centralizer
  have _hfact : Fact (Nat.card ↥R0).Prime := ⟨hadm.prime_card⟩
  have hDR : D ⊓ R = ⊥ :=
    le_bot_iff.1 (le_trans (inf_le_inf_right R hDH) (le_of_eq hadm.inf_eq_bot))
  have hDR0 : D ⊓ R0 = ⊥ := le_bot_iff.1 ((inf_le_inf_left D hadm.le).trans hDR.le)
  refine ⟨inferInstance, hadm.odd_card.of_dvd_nat (Subgroup.card_quotient_dvd_card D),
    hHn.map _ (mk'_surjective D), ?_, ?_, ?_, Subgroup.map_mono hadm.le, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hadm.sup_eq_top, Subgroup.map_top_of_surjective _ (mk'_surjective D)]
  · refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨h, hh, rfl⟩ := hx1
    obtain ⟨r, hr', hr2⟩ := hx2
    have hinvD : h⁻¹ * r ∈ D := QuotientGroup.eq.1 (by simpa using hr2.symm)
    have hrH : r ∈ H := by simpa using H.mul_mem hh (hDH hinvD)
    have hrbot : r ∈ (⊥ : Subgroup G) := hadm.inf_eq_bot ▸ Subgroup.mem_inf.2 ⟨hrH, hr'⟩
    rw [Subgroup.mem_bot, ← hr2, Subgroup.mem_bot.1 hrbot, map_one]
  · rw [natCard_map_mk'_of_inf_eq_bot hDR]
    exact hadm.coprime.coprime_dvd_left (Subgroup.card_map_dvd H _)
  · rw [natCard_map_mk'_of_inf_eq_bot hDR0]; exact hadm.prime_card
  · have hDcop : (Nat.card ↥D).Coprime (Nat.card ↥R0) :=
      (hadm.coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hDH)).coprime_dvd_right
        (Subgroup.card_dvd_of_le hadm.le)
    have hcent := centralizer_map_mk'_eq (p := Nat.card ↥R0) (N := D) (R := R0) hDcop
      (IsPGroup.of_card (n := 1) (by rw [pow_one]))
    have _hZmap : IsZGroup ↥((centralizer (R0 : Set G) ⊓ H).map (mk' D)) := isZGroup_map _
    refine isZGroup_of_le (W := (centralizer (R0 : Set G) ⊓ H).map (mk' D)) ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [hcent] at hx1
    obtain ⟨c, hc, rfl⟩ := hx1
    obtain ⟨h, hh, hh2⟩ := hx2
    have hcd : c⁻¹ * h ∈ D := QuotientGroup.eq.1 (by simpa using hh2.symm)
    have hcH : c ∈ H := by simpa [mul_assoc] using H.mul_mem hh (H.inv_mem (hDH hcd))
    exact ⟨c, Subgroup.mem_inf.2 ⟨hc, hcH⟩, rfl⟩

theorem map_subtype_smulDisplacementSubgroup_eq_commutator (H R : Subgroup G) [H.Normal] :
    (smulDisplacementSubgroup ↥R ↥H).map H.subtype = ⁅H, R⁆ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine smulDisplacementSubgroup_le fun a v => ?_
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      conjMulDistribMulAction_smul_coe,
      show ((v : G))⁻¹ * ((a : G) * (v : G) * (a : G)⁻¹) = ⁅((v : G))⁻¹, (a : G)⁆ by
        rw [commutatorElement_def]; group]
    exact commutator_mem_commutator (H.inv_mem v.2) a.2
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have key : ⁅g₁, g₂⁆ = (((⟨g₁⁻¹, H.inv_mem hg₁⟩ : ↥H)⁻¹ *
        (⟨g₂, hg₂⟩ : ↥R) • (⟨g₁⁻¹, H.inv_mem hg₁⟩ : ↥H) : ↥H) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjMulDistribMulAction_smul_coe,
        commutatorElement_def]
      simp only
      group
    rw [key]
    exact ⟨_, inv_mul_smul_mem_smulDisplacementSubgroup _ _, rfl⟩

theorem mem_centralizer_of_mem_fixedPoints (H R : Subgroup G) [H.Normal] {c : ↥H}
    (hc : c ∈ FixedPoints.subgroup ↥R ↥H) : (c : G) ∈ centralizer (R : Set G) := by
  rw [mem_centralizer_iff]
  intro g hg
  have h2 : (g : G) * (c : G) * (g : G)⁻¹ = (c : G) := by
    rw [← conjMulDistribMulAction_smul_coe R H ⟨g, hg⟩ c,
      (FixedPoints.mem_subgroup ↥R ↥H c).1 hc ⟨g, hg⟩]
  calc (g : G) * (c : G) = (g * c * g⁻¹) * g := by group
    _ = c * g := by rw [h2]

theorem exists_mem_commutator_mul_mem_inf_centralizer (H R : Subgroup G) [H.Normal]
    [Finite G] [Group.IsSolvable G] (hcop : (Nat.card ↥R).Coprime (Nat.card ↥H))
    {x : G} (hx : x ∈ H) :
    ∃ w ∈ ⁅H, R⁆, ∃ c ∈ H ⊓ centralizer (R : Set G), x = w * c := by
  obtain ⟨w, hw, c, hc, hwc⟩ :=
    exists_mem_smulDisplacementSubgroup_mul_mem_fixedPoints ↥R ↥H hcop ⟨x, hx⟩
  exact ⟨(w : G), by
      rw [← map_subtype_smulDisplacementSubgroup_eq_commutator H R]; exact ⟨w, hw, rfl⟩,
    (c : G), Subgroup.mem_inf.2 ⟨c.2, mem_centralizer_of_mem_fixedPoints H R hc⟩,
    congrArg Subtype.val hwc⟩

theorem commutator_commutator_eq_commutator (H R : Subgroup G) [H.Normal]
    [Finite G] [Group.IsSolvable G] (hcop : (Nat.card ↥R).Coprime (Nat.card ↥H)) :
    ⁅⁅H, R⁆, R⁆ = ⁅H, R⁆ := by
  refine le_antisymm (commutator_mono (commutator_le_left H R) le_rfl) ?_
  rw [Subgroup.commutator_le]
  intro x hx r hr
  obtain ⟨w, hw, c, hc, rfl⟩ := exists_mem_commutator_mul_mem_inf_centralizer H R hcop hx
  have hcr : c * r = r * c := ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) r hr).symm
  have key : ⁅w * c, r⁆ = ⁅w, r⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc w * c * r * (w * c)⁻¹ * r⁻¹ = w * (c * r) * (c⁻¹ * w⁻¹) * r⁻¹ := by group
      _ = w * (r * c) * (c⁻¹ * w⁻¹) * r⁻¹ := by rw [hcr]
      _ = w * r * w⁻¹ * r⁻¹ := by group
  rw [key]
  exact commutator_mem_commutator hw hr

section Main

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G] {H R R0 : Subgroup G}
  (hadm : IsAdmissibleCoprimeActionQuadruple G H R R0)
  (hnot : ¬ HasPLengthLeOne p ↥⁅H, R⁆)
  (hmin : ∀ (Y : Type u) [Group Y] [Finite Y] (J A A0 : Subgroup Y),
    IsAdmissibleCoprimeActionQuadruple Y J A A0 → Nat.card Y < Nat.card G →
    HasPLengthLeOne p ↥⁅J, A⁆)

include hadm hnot hmin

theorem eq_commutator_of_minimal : H = ⁅H, R⁆ := by
  have hHn := hadm.normal
  have hsolv : Group.IsSolvable G := hadm.isSolvable
  set B : Subgroup G := ⁅H, R⁆ with hBdef
  have hBH : B ≤ H := Subgroup.commutator_le_left H R
  have hBnormal : B.Normal := normal_commutator_of_sup_eq_top hadm.sup_eq_top
  by_contra hne
  have hlt : B < H := hBH.lt_of_ne fun h => hne h.symm
  set K : Subgroup G := B ⊔ R with hKdef
  have hBK : B ≤ K := le_sup_left
  have hRK : R ≤ K := le_sup_right
  have hadm' := isAdmissible_subgroupOf hadm hBH hBnormal
  have hcard : Nat.card ↥K < Nat.card G := by
    have h1 := hadm'.card_mul_card
    rw [natCard_subgroupOf_of_le hBK, natCard_subgroupOf_of_le hRK] at h1
    rw [← h1, ← hadm.card_mul_card]
    exact (Nat.mul_lt_mul_right Nat.card_pos).2
      (Nat.lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hBH))
        fun he => hlt.ne (Subgroup.eq_of_le_of_card_ge hBH he.ge))
  have hplen := hmin ↥K _ _ _ hadm' hcard
  rw [commutator_subgroupOf hBK hRK,
    show ⁅B, R⁆ = B from commutator_commutator_eq_commutator H R hadm.coprime.symm] at hplen
  exact hnot (hplen.of_surjective
    (f := ((Subgroup.subgroupOfEquivOfLe hBK) : ↥(B.subgroupOf K) →* ↥B))
    (Subgroup.subgroupOfEquivOfLe hBK).surjective)

theorem not_hasPLengthLeOne_of_minimal : ¬ HasPLengthLeOne p ↥H := by
  rw [eq_commutator_of_minimal hadm hnot hmin]; exact hnot

theorem dvd_natCard_of_minimal : p ∣ Nat.card ↥H := by
  by_contra hcon
  exact not_hasPLengthLeOne_of_minimal hadm hnot hmin (hasPLengthLeOne_of_not_dvd_card hcon)

theorem ne_bot_of_minimal : H ≠ ⊥ := by
  intro h0
  have hdvd := dvd_natCard_of_minimal hadm hnot hmin
  rw [h0] at hdvd
  simp only [Subgroup.card_bot, Nat.dvd_one] at hdvd
  exact (Fact.out : p.Prime).one_lt.ne' hdvd

theorem ne_natCard_of_minimal : p ≠ Nat.card ↥R0 := by
  intro h
  have hpR : p ∣ Nat.card ↥R := h ▸ Subgroup.card_dvd_of_le hadm.le
  exact (Fact.out : p.Prime).one_lt.ne'
    (Nat.eq_one_of_dvd_one (hadm.coprime ▸
      Nat.dvd_gcd (dvd_natCard_of_minimal hadm hnot hmin) hpR))

theorem hasPLengthLeOne_quotient_of_minimal {D : Subgroup G} [D.Normal]
    (hD : D ≠ ⊥) (hDH : D ≤ H) : HasPLengthLeOne p (↥H ⧸ D.subgroupOf H) := by
  have hplen := hmin (G ⧸ D) _ _ _ (isAdmissible_map_mk' hadm hDH)
    (by rw [← Subgroup.index_eq_card]; exact index_lt_natCard hD)
  rw [← Subgroup.map_commutator, ← eq_commutator_of_minimal hadm hnot hmin] at hplen
  exact hplen.of_surjective (f := ((quotientSubgroupOfEquivMapMk' H D).symm :
    ↥(H.map (mk' D)) →* ↥H ⧸ D.subgroupOf H)) (quotientSubgroupOfEquivMapMk' H D).symm.surjective

theorem pComplCore_eq_bot_of_minimal : pComplCore p ↥H = ⊥ := by
  have hHn := hadm.normal
  by_contra hne
  set D : Subgroup G := (pComplCore p ↥H).map H.subtype with hDdef
  have hDne : D ≠ ⊥ := by
    rwa [hDdef, Ne, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective]
  have heq : D.subgroupOf H = pComplCore p ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have _i1 := pComplCore_normal p ↥H
  have _i2 := (pComplCore_map_subtype_normal (p := p) H).subgroupOf H
  have hq := hasPLengthLeOne_quotient_of_minimal hadm hnot hmin hDne (Subgroup.map_subtype_le _)
  have hq' : HasPLengthLeOne p (↥H ⧸ pComplCore p ↥H) :=
    hq.of_surjective (f := ((QuotientGroup.quotientMulEquivOfEq heq) :
        (↥H ⧸ D.subgroupOf H) →* ↥H ⧸ pComplCore p ↥H))
      (QuotientGroup.quotientMulEquivOfEq heq).surjective
  exact not_hasPLengthLeOne_of_minimal hadm hnot hmin
    (hasPLengthLeOne_of_quotient (not_dvd_natCard_pComplCore Fact.out ↥H) hq')

theorem minimalPrimeCentralizerCounterexample :
    H = ⁅H, R⁆ ∧ H ≠ ⊥ ∧ p ∣ Nat.card ↥H ∧ p ≠ Nat.card ↥R0 ∧ pComplCore p ↥H = ⊥ ∧
      ∀ (D : Subgroup G) (_ : D.Normal), D ≠ ⊥ → D ≤ H →
        HasPLengthLeOne p (↥H ⧸ D.subgroupOf H) :=
  ⟨eq_commutator_of_minimal hadm hnot hmin, ne_bot_of_minimal hadm hnot hmin,
    dvd_natCard_of_minimal hadm hnot hmin, ne_natCard_of_minimal hadm hnot hmin,
    pComplCore_eq_bot_of_minimal hadm hnot hmin,
    fun _ _ hD hDH => hasPLengthLeOne_quotient_of_minimal hadm hnot hmin hD hDH⟩

end Main

end CFSG.FeitThompson


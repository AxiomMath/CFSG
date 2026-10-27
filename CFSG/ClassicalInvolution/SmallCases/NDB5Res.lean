module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.ClassicalInvolution.AschTight.S1911FusB
public import CFSG.ClassicalInvolution.AschTight.S1911Facts

public section

namespace CFSG.ClassicalInvolution.NDB.SRes

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidual_map_eq)
open CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  (nonempty_quotEquiv_of_surjective_of_odd)
open scoped MatrixGroups

theorem perfectResidualOf_map {M N : Type*} [Group M] [Group N] [Finite M] [Finite N]
    (f : M →* N) (H : Subgroup M) :
    perfectResidualOf (H.map f) = (perfectResidualOf H).map f := by
  have h := finite_perfectResidual_map_eq (f.subgroupMap H) (f.subgroupMap_surjective H)
  have e : (H.map f).subtype.comp (f.subgroupMap H) = f.comp H.subtype := by
    ext x
    rfl
  calc perfectResidualOf (H.map f) =
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(H.map f)).map
          (H.map f).subtype := rfl
    _ = ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥H).map
          (f.subgroupMap H)).map (H.map f).subtype := by rw [h]
    _ = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥H).map (f.comp H.subtype) := by
          rw [Subgroup.map_map, e]
    _ = (perfectResidualOf H).map f := by rw [← Subgroup.map_map]; rfl

variable {G : Type} [Group G] [Finite G] {a : G}

@[expose] noncomputable def toQuot {W : Subgroup G}
    (hW : W ≤ Subgroup.centralizer ({a} : Set G)) : ↥W →* OddQuot a :=
  (oddQuotMk a).comp (Subgroup.inclusion hW)

omit [Finite G] in
theorem range_toQuot {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({a} : Set G)) :
    (toQuot hW).range = modOdd a W := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨Subgroup.inclusion hW w, w.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem modOdd_perfectResidualOf {W : Subgroup G} (hW : W ≤ Subgroup.centralizer ({a} : Set G)) :
    modOdd a (perfectResidualOf W) = perfectResidualOf (modOdd a W) := by
  have h := finite_perfectResidual_map_eq (toQuot hW).rangeRestrict
    (toQuot hW).rangeRestrict_surjective
  have e1 : modOdd a (perfectResidualOf W) =
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥W).map (toQuot hW) := by
    ext x
    constructor
    · rintro ⟨k, ⟨w, hw, hwk⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      show oddQuotMk a (Subgroup.inclusion hW w) = oddQuotMk a k
      congr 1
      exact Subtype.ext hwk
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Subgroup.inclusion hW w, ⟨w, hw, rfl⟩, rfl⟩
  rw [e1, ← range_toQuot hW]
  show _ = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(toQuot hW).range).map
    (toQuot hW).range.subtype
  rw [← h, Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]

theorem modOdd_comap_inf_centralizer (S : Subgroup (OddQuot a)) {s : G}
    (hs : s ∈ Subgroup.centralizer ({a} : Set G)) (hs2 : s * s = 1) :
    modOdd a ((S.comap (oddQuotMk a)).map (Subgroup.centralizer ({a} : Set G)).subtype ⊓
      Subgroup.centralizer ({s} : Set G)) =
      S ⊓ Subgroup.centralizer ({oddQuotMk a ⟨s, hs⟩} : Set (OddQuot a)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have e1 : ((S.comap (oddQuotMk a)).map C.subtype ⊓
      Subgroup.centralizer ({s} : Set G)).subgroupOf C =
      S.comap (oddQuotMk a) ⊓ Subgroup.centralizer ({⟨s, hs⟩} : Set ↥C) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hxs⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact ⟨hy, Subtype.ext hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨⟨x, hx, rfl⟩, congrArg Subtype.val hxs⟩
  have hNW : componentClassificationOddCore ↥C ≤ S.comap (oddQuotMk a) := fun x hx => by
    rw [Subgroup.mem_comap, oddQuotMk_eq_one_iff.mpr hx]
    exact S.one_mem
  have hcop : Nat.Coprime 2 (Nat.card (componentClassificationOddCore ↥C)) :=
    Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥C)
  have hs2' : (⟨s, hs⟩ : ↥C) ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hs2
  have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq Nat.prime_two hNW hcop hs2'
  have hsurj : (S.comap (oddQuotMk a)).map (oddQuotMk a) = S :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) S
  unfold modOdd
  rw [e1]
  have h' : ((S.comap (oddQuotMk a)) ⊓ Subgroup.centralizer ({⟨s, hs⟩} : Set ↥C)).map
      (oddQuotMk a) = (S.comap (oddQuotMk a)).map (oddQuotMk a) ⊓
        Subgroup.centralizer ({oddQuotMk a ⟨s, hs⟩} : Set (OddQuot a)) := h
  rw [h', hsurj]

theorem mem_of_oddQuotMk_eq {L : Subgroup G} (ha2 : a * a = 1)
    {k : ↥(Subgroup.centralizer ({a} : Set G))} (hk : (k : G) ∈ L)
    (h : oddQuotMk a k = oddQuotMk a ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :
    a ∈ L := by
  set a' : ↥(Subgroup.centralizer ({a} : Set G)) :=
    ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with ha'
  set o := a'⁻¹ * k with ho
  have hoO : o ∈ componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) :=
    QuotientGroup.eq.mp h.symm
  have hodd : Odd (orderOf o) :=
    (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hoO)
  have hcomm : Commute a' o :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp o.2).symm
  have hk' : k = a' * o := by rw [ho, mul_inv_cancel_left]
  have ha'2 : a' ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext ha2
  obtain ⟨m, hm⟩ := hodd
  have hpow : k ^ orderOf o = a' := by
    rw [hk', hcomm.mul_pow, pow_orderOf_eq_one, mul_one, hm, pow_succ, pow_mul, ha'2, one_pow,
      one_mul]
  have h1 := L.pow_mem hk (orderOf o)
  rw [← Subgroup.coe_pow, hpow] at h1
  exact h1

theorem oddCore_sl2_eq_bot {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
    (hK : IsClassicalMember p f K z) :
    classicalInvolutionOddCore SL(2, GaloisField p f) = ⊥ := by
  obtain ⟨e⟩ := hK.nonempty_equiv
  have h1 : classicalInvolutionOddCore (↥K ⧸ classicalInvolutionOddCore ↥K) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥K
  have h2 : (classicalInvolutionOddCore (↥K ⧸ classicalInvolutionOddCore ↥K)).map
      e.toMonoidHom = classicalInvolutionOddCore SL(2, GaloisField p f) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [← h2, h1, Subgroup.map_bot]

theorem nonempty_equiv_of_modOdd_eq {F : Type*} [Field F] {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({a} : Set G)) (κ : SL(2, F) →* OddQuot a)
    (hκ : Function.Injective κ) (himg : modOdd a L = κ.range)
    (hO : classicalInvolutionOddCore SL(2, F) = ⊥) :
    Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)) := by
  let e : SL(2, F) ≃* κ.range := MonoidHom.ofInjective hκ
  have hr : ∀ l, toQuot hL l ∈ κ.range := fun l => by
    rw [← himg, ← range_toQuot hL]
    exact ⟨l, rfl⟩
  let π : ↥L →* SL(2, F) := e.symm.toMonoidHom.comp ((toQuot hL).codRestrict κ.range hr)
  have hsurj : Function.Surjective π := by
    intro B
    obtain ⟨l, hl⟩ : κ B ∈ (toQuot hL).range := by
      rw [range_toQuot hL, himg]
      exact ⟨B, rfl⟩
    refine ⟨l, ?_⟩
    show e.symm ⟨toQuot hL l, hr l⟩ = B
    rw [e.symm_apply_eq]
    exact Subtype.ext hl
  have hker : Odd (Nat.card π.ker) := by
    have hle : π.ker.map (Subgroup.inclusion hL) ≤
        componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) := by
      rintro _ ⟨l, hl, rfl⟩
      have h1 : π l = 1 := hl
      have h2 : (toQuot hL).codRestrict κ.range hr l = 1 :=
        (MulEquiv.map_eq_one_iff e.symm).mp h1
      have h3 : toQuot hL l = 1 := congrArg Subtype.val h2
      exact oddQuotMk_eq_one_iff.mp h3
    have hcard : Nat.card (π.ker.map (Subgroup.inclusion hL)) = Nat.card π.ker :=
      (Nat.card_congr (π.ker.equivMapOfInjective _
        (Subgroup.inclusion_injective hL)).toEquiv).symm
    rw [← hcard]
    exact (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  exact nonempty_quotEquiv_of_surjective_of_odd π hsurj hker hO

end CFSG.ClassicalInvolution.NDB.SRes

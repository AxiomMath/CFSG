module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem IsKType.congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : IsKType Q) :
    IsKType Q' := by
  obtain ⟨hq, h2⟩ := h
  refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, ?_⟩
  have hc : (center Q).map e.toMonoidHom = center Q' := Subgroup.map_center_eq e
  let f : Q ⧸ center Q ≃* Q' ⧸ center Q' := QuotientGroup.congr _ _ e hc
  rcases h2 with ⟨n, hn, hd⟩ | ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
  · exact Or.inl ⟨n, hn, GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr e hd⟩
  · exact Or.inr (Or.inl ⟨f.symm.trans g⟩)
  · exact Or.inr (Or.inr ⟨f.symm.trans g⟩)

theorem IsKComp.map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {L : Subgroup X}
    (h : IsKComp L) : IsKComp (L.map e.toMonoidHom) := by
  refine ⟨LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e h.1, ?_⟩
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
  exact IsKType.congr f h.2

theorem KProd.normal (X : Type) [Group X] : (KProd X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  let φ : X ≃* X := MulAut.conj g
  have hle : KProd X ≤ (KProd X).comap φ.toMonoidHom := by
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (IsKComp.map_equiv φ hL)
  exact hle hn

instance (X : Type) [Group X] : (KProd X).Normal := KProd.normal X

theorem isPComponent_map_subtype_of_subnormal {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.IsSubnormal) {K : Subgroup ↥N} (hK : IsPComponent 2 K) :
    IsPComponent 2 (K.map N.subtype) := by
  rw [isPComponent_two_iff] at hK ⊢
  exact ⟨hK.1.trans' hN,
    (isTwoGenQuasi_congr_iff (K.equivMapOfInjective N.subtype N.subtype_injective)).1 hK.2⟩

theorem KProdIn_le_KProd_of_subnormal {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.IsSubnormal) : KProdIn N ≤ KProd X := by
  unfold KProdIn KProd
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨isPComponent_map_subtype_of_subnormal hN hK.1, ?_⟩
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (K.equivMapOfInjective N.subtype N.subtype_injective)
  exact IsKType.congr f hK.2

theorem KProd_le_map_of_odd {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : KProd (X ⧸ N) ≤ (KProd X).map (QuotientGroup.mk' N) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπdef
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    intro h
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  obtain ⟨-, hinv, hiso⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection π hsurj hker
  refine sSup_le fun Kb hKb => ?_
  obtain ⟨hKc, hKmap⟩ := hinv Kb hKb.1
  set K : Subgroup X := Subgroup.closure
    {x : X | x ∈ Kb.comap π ∧ ∃ k : ℕ, orderOf x = 2 ^ k} with hKdef
  have hKcomp : IsKComp K := by
    refine ⟨hKc, ?_⟩
    obtain ⟨q, -⟩ := hiso K hKc
    obtain ⟨q'⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr hKmap)
    exact IsKType.congr (q.trans q').symm hKb.2
  calc Kb = K.map π := hKmap.symm
    _ ≤ (KProd X).map π := Subgroup.map_mono (le_sSup hKcomp)

theorem le_KProd_of_map_le_of_odd {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) {L : Subgroup X} (hL : primeResidual 2 ↥L = ⊤)
    (h : L.map (QuotientGroup.mk' N) ≤ KProd (X ⧸ N)) : L ≤ KProd X := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπdef
  have hmap : L.map π ≤ (KProd X).map π := h.trans (KProd_le_map_of_odd hN)
  have hpow : ∀ x ∈ L, (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ KProd X := by
    intro x hx ⟨j, hj⟩
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 (hmap (Subgroup.mem_map_of_mem π hx))
    have hm : k⁻¹ * x ∈ N := by
      rw [← QuotientGroup.eq]
      exact hkx
    let ρ : X →* X ⧸ KProd X := QuotientGroup.mk' (KProd X)
    have hρk : ρ k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    have hx1 : ρ x = ρ (k⁻¹ * x) := by
      rw [map_mul, map_inv, hρk, inv_one, one_mul]
    have h1 : orderOf (ρ x) ∣ 2 ^ j := hj ▸ orderOf_map_dvd ρ x
    have h2 : orderOf (ρ x) ∣ Nat.card N := by
      rw [hx1]
      exact (orderOf_map_dvd ρ _).trans (Subgroup.orderOf_dvd_natCard N hm)
    have hcop : Nat.Coprime (2 ^ j) (Nat.card N) :=
      (Nat.coprime_two_left.2 hN).pow_left j
    have h3 : orderOf (ρ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)
  have hcl : primeResidual 2 ↥L ≤ (KProd X).comap L.subtype := by
    rw [primeResidual_eq_closure, Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    exact hpow x x.2 ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ primeResidual 2 ↥L := by rw [hL]; exact Subgroup.mem_top _
  exact hcl hy'

end CFSG.OddStandard.Solomon75

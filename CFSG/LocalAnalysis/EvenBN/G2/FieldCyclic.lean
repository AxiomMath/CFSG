module

public import CFSG.LocalAnalysis.EvenBN.G2.SeriesCenters
public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups

namespace FieldCyclicAux

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_conj)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (barMap_eq_iff mem_barSub_iff)

noncomputable def slCongr {k k' : Type*} [Field k] [Field k'] (e : k ≃+* k') :
    SL(2, k) ≃* SL(2, k') :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

theorem exists_type_model (k : Type*) [Field k] [Finite k] [CharP k 2] :
    ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' 2), Nonempty (k ≃+* k') := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k 2
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance,
    ⟨FiniteField.ringEquivOfCardEq ?_⟩⟩
  rw [hcard, ← Nat.card_eq_fintype_card, GaloisField.card 2 n n.ne_zero]

theorem exists_hom_outer {Γ : Type*} [Group Γ] {k : Type} [Field k]
    {N R B P : Subgroup Γ} (ψ : N ≃* SL(2, k)) (hRodd : Odd (Nat.card R)) (hNR : N ⊓ R = ⊥)
    (hC : centralizer (N : Set Γ) ≤ R) (hBN : B ≤ normalizer (N : Set Γ)) (hB2 : IsPGroup 2 B)
    (hBP : B ⊓ N = P) :
    ∃ Θ : B →* Outer SL(2, k), Θ.ker = P.subgroupOf B := by
  classical
  subst hBP
  let A : B →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let Θ : B →* Outer SL(2, k) :=
    (QuotientGroup.mk' (inner SL(2, k))).comp ((MulAut.congr ψ).toMonoidHom.comp A)
  refine ⟨Θ, ?_⟩
  ext b
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro hb
    have hin : MulAut.congr ψ (A b) ∈ inner SL(2, k) := (QuotientGroup.eq_one_iff _).mp hb
    obtain ⟨s, hs⟩ := hin
    set n : N := ψ.symm s with hn
    have hAn : A b = MulAut.conj n := by
      apply (MulAut.congr ψ).injective
      rw [← hs, congr_conj, hn, MulEquiv.apply_symm_apply]
    have hconj : ∀ x : N, (b : Γ) * x * (b : Γ)⁻¹ = (n : Γ) * x * (n : Γ)⁻¹ := fun x =>
      congrArg (fun a : MulAut N => ((a x : N) : Γ)) hAn
    set c : Γ := (n : Γ)⁻¹ * b with hc
    have hcC : c ∈ centralizer (N : Set Γ) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := hconj ⟨x, hx⟩
      calc x * c = (n : Γ)⁻¹ * ((n : Γ) * x * (n : Γ)⁻¹) * b := by rw [hc]; group
        _ = (n : Γ)⁻¹ * ((b : Γ) * x * (b : Γ)⁻¹) * b := by rw [← h1]
        _ = c * x := by rw [hc]; group
    have hcR : c ∈ R := hC hcC
    have hnc : Commute (n : Γ) c := mem_centralizer_iff.mp hcC n n.2
    have hbnc : (b : Γ) = n * c := by rw [hc]; group
    obtain ⟨m, hm⟩ := hB2 b
    have hbm : (b : Γ) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hcm : c ^ 2 ^ m ∈ N ⊓ R := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem hcR _⟩
      have h1 : (n : Γ) ^ 2 ^ m * c ^ 2 ^ m = 1 := by
        rw [← hnc.mul_pow, ← hbnc]
        exact hbm
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (pow_mem n.2 _)
    have hc1pow : c ^ 2 ^ m = 1 := by
      rw [hNR] at hcm
      exact mem_bot.mp hcm
    have hc1 : c = 1 := by
      have hd1 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hc1pow
      have hd2 : orderOf c ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hcR
      have hcop : Nat.Coprime (2 ^ m) (Nat.card R) := (Nat.coprime_two_left.2 hRodd).pow_left m
      have : orderOf c = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hd1 hd2)
      exact orderOf_eq_one_iff.mp this
    refine ⟨b.2, ?_⟩
    rw [hbnc, hc1, mul_one]
    exact n.2
  · intro hb
    have hbN : (b : Γ) ∈ N := hb.2
    have hAb : A b = MulAut.conj (⟨b, hbN⟩ : N) := by
      ext x
      rfl
    refine (QuotientGroup.eq_one_iff _).mpr ⟨ψ ⟨b, hbN⟩, ?_⟩
    show MulAut.conj (ψ ⟨b, hbN⟩) = MulAut.congr ψ (A b)
    rw [hAb, congr_conj]

theorem exists_hom_cyclic {Γ : Type*} [Group Γ] {k : Type*} [Field k] [Finite k] [CharP k 2]
    {N R B P : Subgroup Γ} (ψ : N ≃* SL(2, k)) (hRodd : Odd (Nat.card R)) (hNR : N ⊓ R = ⊥)
    (hC : centralizer (N : Set Γ) ≤ R) (hBN : B ≤ normalizer (N : Set Γ)) (hB2 : IsPGroup 2 B)
    (hBP : B ⊓ N = P) :
    ∃ (Q : Type) (_ : Group Q) (_ : IsCyclic Q) (Θ : B →* Q), Θ.ker = P.subgroupOf B := by
  obtain ⟨k', _, _, _, ⟨e⟩⟩ := exists_type_model k
  obtain ⟨Θ, hΘ⟩ := exists_hom_outer (ψ.trans (slCongr e)) hRodd hNR hC hBN hB2 hBP
  haveI : IsCyclic (Outer SL(2, k')) :=
    CFSG.RankThree.PartOne.KCRootAxis.out_sl2_isCyclic (K := k')
  exact ⟨Outer SL(2, k'), inferInstance, inferInstance, Θ, hΘ⟩

theorem isCyclic_quotient_of_ker {Γ : Type*} [Group Γ] {B P : Subgroup Γ} {Q : Type*} [Group Q]
    [IsCyclic Q] (Θ : B →* Q) (hΘ : Θ.ker = P.subgroupOf B) [(P.subgroupOf B).Normal] :
    IsCyclic (B ⧸ P.subgroupOf B) := by
  refine isCyclic_of_injective (QuotientGroup.lift (P.subgroupOf B) Θ hΘ.ge) ?_
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.lift_mk] at hq
  rw [QuotientGroup.eq_one_iff, ← hΘ]
  exact hq

theorem isCyclic_quotient_of_bar {G : Type*} [Group G] {X N P B : Subgroup G}
    {Nb R : Subgroup (BarM X)} {k : Type*} [Field k] [Finite k] [CharP k 2]
    (hXP : X ≤ P) (hPB : P ≤ B) (hBX : B ≤ normalizer (X : Set G))
    (hNn : (N.subgroupOf (normalizer (X : Set G))).Normal) (hNb : barSub X N = Nb)
    (ψ : Nb ≃* SL(2, k)) (hRodd : Odd (Nat.card R)) (hNR : Nb ⊓ R = ⊥)
    (hC : centralizer (Nb : Set (BarM X)) ≤ R) (hB2 : IsPGroup 2 B) (hBN : B ⊓ N = P)
    [(P.subgroupOf B).Normal] : IsCyclic (B ⧸ P.subgroupOf B) := by
  classical
  have hNbn : Nb.Normal := by
    rw [← hNb]
    exact hNn.map (barMap X) (QuotientGroup.mk'_surjective _)
  have hBb : barSub X B ≤ normalizer (Nb : Set (BarM X)) := fun x _ => by
    rw [Subgroup.normalizer_eq_top (H := Nb)]
    exact Subgroup.mem_top x
  have hB2b : IsPGroup 2 (barSub X B) :=
    (hB2.comap_subtype (K := normalizer (X : Set G))).map (barMap X)
  have hBNb : barSub X B ⊓ Nb = barSub X P := by
    rw [← hNb]
    apply le_antisymm
    · rintro _ ⟨hx1, hx2⟩
      obtain ⟨b, hb, rfl⟩ := hx1
      obtain ⟨n, hn, hnb⟩ := hx2
      have hxn : (n : G)⁻¹ * b ∈ X := barMap_eq_iff.mp hnb
      have hnB : (n : G) ∈ B := by
        have e : (n : G) = b * ((n : G)⁻¹ * b)⁻¹ := by group
        rw [e]
        exact mul_mem (mem_subgroupOf.mp hb) (inv_mem (hPB (hXP hxn)))
      have hnP : (n : G) ∈ P := by
        rw [← hBN]
        exact ⟨hnB, mem_subgroupOf.mp hn⟩
      have hbP : (b : G) ∈ P := by
        have e : (b : G) = n * ((n : G)⁻¹ * b) := by group
        rw [e]
        exact mul_mem hnP (hXP hxn)
      exact ⟨b, mem_subgroupOf.mpr hbP, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      have hp' : (p : G) ∈ B ⊓ N := by
        rw [hBN]
        exact mem_subgroupOf.mp hp
      exact ⟨⟨p, mem_subgroupOf.mpr hp'.1, rfl⟩, ⟨p, mem_subgroupOf.mpr hp'.2, rfl⟩⟩
  obtain ⟨Q, _, hQ, Θ, hΘ⟩ := exists_hom_cyclic ψ hRodd hNR hC hBb hB2b hBNb
  let ρ : B →* barSub X B :=
    ((barMap X).comp (Subgroup.inclusion hBX)).codRestrict (barSub X B)
      (fun b => ⟨Subgroup.inclusion hBX b, mem_subgroupOf.mpr b.2, rfl⟩)
  refine isCyclic_quotient_of_ker (Θ.comp ρ) ?_
  ext b
  rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hΘ,
    mem_subgroupOf]
  exact mem_barSub_iff hXP (Subgroup.inclusion hBX b)

end FieldCyclicAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem isCyclic_quotient_yamadaP_of_field (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hF : FieldAlternative (yamadaBarK₂ d t) (yamadaT₂ d t) f) {B : Subgroup G}
    (hB : IsSylowOf 2 B (normalizer (yamadaP d t : Set G))) (hPB : yamadaP d t ≤ B)
    [((yamadaP d t).subgroupOf B).Normal] : IsCyclic (B ⧸ (yamadaP d t).subgroupOf B) := by
  classical
  have hKN : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  obtain ⟨hMY, hNP⟩ := h.yamadaP_inf_centralizer_yamadaY₂ hW d hK hQ hex
  have hMP : yamadaM₆ d t ≤ yamadaP d t := hMY ▸ inf_le_left
  have hBM : B ≤ normalizer (yamadaM₆ d t : Set G) := hB.le.trans hNP
  have hBN : B ⊓ yamadaN₂ d t = yamadaP d t :=
    hsyl.eq_of_le (le_inf hPB hsyl.le) inf_le_right hB.isPGroup.to_inf_left
  obtain ⟨k₂, _, _, hk₂, ψ, -⟩ := hF
  haveI : Finite k₂ := Finite.of_fintype k₂
  have hk₂' : Nat.card k₂ = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
  haveI : CharP k₂ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by have := h.two_le; omega) hk₂'
  obtain ⟨hNR, hCR, -⟩ := hex
  exact FieldCyclicAux.isCyclic_quotient_of_bar hMP hPB hBM
    (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hKN)
    (barSub_yamadaN₂ d t hKN) ψ (GMSK.odd_card_standardComponentOddCore _) hNR hCR.le
    hB.isPGroup hBN

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2

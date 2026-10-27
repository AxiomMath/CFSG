module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem eq_of_card_psl2GF_dvd {p n m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n) (hm : m ≠ 0)
    (hdvd : Nat.card (PSL2GF p n) ∣ Nat.card (PSL2GF p m)) (hpm : p ^ m ∣ p ^ n * n) :
    m = n := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) (n := 2 * n) hp3
      (by omega)
  have hℓp : ¬ ℓ ∣ p := by
    intro h'
    have h1 : ℓ ∣ p ^ (2 * n) := h'.trans (dvd_pow_self p (by omega))
    have h2 := Nat.dvd_sub h1 hℓdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  have hℓm : ℓ ∣ p ^ (2 * m) - 1 := by
    have h1 := (prime_dvd_card_psl2GF hp2 (by omega) hℓ hℓdvd hprim).trans hdvd
    rw [CFSG.SectionRank.OddCover.card_psl_two hp hp2 (GaloisField.card p m hm)] at h1
    have h2 : ℓ ∣ ((p ^ m) ^ 2 - 1) / 2 :=
      ((Nat.Prime.dvd_mul hℓ).mp h1).resolve_left fun h' => hℓp (hℓ.dvd_of_dvd_pow h')
    have hev : 2 ∣ (p ^ m) ^ 2 - 1 :=
      (Nat.Odd.sub_odd (hp.odd_of_ne_two hp2).pow.pow odd_one).two_dvd
    have hsq : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
    exact hsq ▸ h2.trans (Nat.div_dvd_of_dvd hev)
  have hnm : n ∣ m := by
    have hg : ℓ ∣ p ^ Nat.gcd (2 * n) (2 * m) - 1 := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one]
      exact Nat.dvd_gcd hℓdvd hℓm
    have hpos : 0 < Nat.gcd (2 * n) (2 * m) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hle : Nat.gcd (2 * n) (2 * m) ≤ 2 * n := Nat.gcd_le_left _ (by omega)
    have heq : Nat.gcd (2 * n) (2 * m) = 2 * n := by
      by_contra hne
      exact hprim _ hpos (lt_of_le_of_ne hle hne) hg
    exact Nat.dvd_of_mul_dvd_mul_left two_pos (heq ▸ Nat.gcd_dvd_right _ _)
  have hm2 : m < 2 * n := by
    have h1 := Nat.le_of_dvd (Nat.mul_pos (pow_pos hp.pos n) (by omega)) hpm
    have h2 : p ^ n * n < p ^ n * p ^ n :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_pow_self hp.one_lt) (pow_pos hp.pos n)
    rw [← pow_add, show n + n = 2 * n by ring] at h2
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt h1 h2)
  obtain ⟨k, rfl⟩ := hnm
  have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left (a := n) (by linarith)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hm (mul_zero n)
  rw [show k = 1 by omega, mul_one]

open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo in
theorem le_of_centralizer_eq_bot_of_mulEquiv_psl2 {Y : Type*} [Group Y] {K J : Subgroup Y}
    [K.Normal] (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hJ : Group.IsPerfect J)
    {F : Type*} [Field F] [Finite F] (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    J ≤ K := by
  intro j hj
  let f : Y →* Outer K := (QuotientGroup.mk' (inner K)).comp MulAut.conjNormal
  have h1 : f j = 1 := by
    have hmem : (⟨j, hj⟩ : J) ∈ derivedSeries J 2 := by
      rw [Group.IsPerfect.derivedSeries_eq_top]
      exact Subgroup.mem_top _
    have h2 := map_derivedSeries_le_derivedSeries (f.comp J.subtype) 2 ⟨_, hmem, rfl⟩
    rwa [outer_secondDerived_eq_bot_of_equiv F e, Subgroup.mem_bot] at h2
  have h1' : (MulAut.conjNormal j : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := h1'
  have hc : (k : Y)⁻¹ * j ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h3 : (k : Y) * x * (k : Y)⁻¹ = j * x * j⁻¹ := by
      have := congrArg (fun α : MulAut K => ((α ⟨x, hx⟩ : K) : Y)) hk
      simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
    calc x * ((k : Y)⁻¹ * j) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * j := by group
      _ = (k : Y)⁻¹ * (j * x * j⁻¹) * j := by rw [h3]
      _ = (k : Y)⁻¹ * j * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc ▸ k.2

namespace JStarHyp

variable {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}

theorem eq_component_of_psl2GF (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    {m : ℕ} (hm : m ≠ 0) (h9 : p ^ m ≠ 9) (e : K ⧸ Subgroup.center K ≃* PSL2GF p m) :
    Jt = K ∧ m = n ∧ JStarConcl p n Jt := by
  have hp : p.Prime := Fact.out
  have hp2 := h.ne_two
  have hn := h.three_le
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set Y), orderOf c = p → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp : IsPGroup p (Subgroup.centralizer (K : Set Y)) :=
    isPGroup_centralizer_of_forall_mem hp hp2 h.red.core_eq_bot hKn hmem
  have hZle : (Subgroup.center K).map K.subtype ≤ Subgroup.centralizer (K : Set Y) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨x, hx⟩)
  have hZp : IsPGroup p (Subgroup.center K) :=
    (hCp.to_le hZle).of_equiv
      (Subgroup.equivMapOfInjective (Subgroup.center K) K.subtype K.subtype_injective).symm
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_center_quotient_psl2 hp2 hm h9 hK.2.2 hZp e
  have hC : Subgroup.centralizer (K : Set Y) = ⊥ :=
    centralizer_eq_bot_of_forall_mem hp hp2 h.red.core_eq_bot hKn hmem hZ
  have eK : K ≃* PSL2GF p m :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  have hJK : Jt ≤ K := le_of_centralizer_eq_bot_of_mulEquiv_psl2 hC h.isPerfect eK
  have hpm : p ^ m ∣ p ^ n * n := by
    obtain ⟨T⟩ : Nonempty (Sylow p (PSL2GF p m)) := inferInstance
    have hS : Nat.card (((T : Subgroup (PSL2GF p m)).map eK.symm.toMonoidHom).map K.subtype) =
        p ^ m := by
      rw [Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective eK.symm.injective, (psl2GF_sylow p m (by omega) T).2]
    rw [← hS]
    exact h.card_dvd _ (IsPGroup.of_card hS)
  have hdvd : Nat.card (PSL2GF p n) ∣ Nat.card (PSL2GF p m) := by
    rw [← Nat.card_congr eK.toEquiv]
    exact (Subgroup.card_dvd_of_surjective (f := φ) h.surj).trans (Subgroup.card_dvd_of_le hJK)
  obtain rfl : m = n := eq_of_card_psl2GF_dvd hp2 hn hm hdvd hpm
  obtain rfl : Jt = K := by
    refine Subgroup.eq_of_le_of_card_ge hJK ?_
    rw [Nat.card_congr eK.toEquiv]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_surjective (f := φ) h.surj)
  exact ⟨rfl, rfl, hKn, ⟨eK⟩, hC⟩

theorem eq_component_of_isLinTwoIndex (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    {m : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p m d)
    (he : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Jt = K ∧ m = n ∧ JStarConcl p n Jt := by
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hm : m ≠ 0 := by
    obtain ⟨q, -, -, rfl⟩ := hd
    exact q.exponent_pos.ne'
  exact h.eq_component_of_psl2GF hK huniq hcent hm (card_ne_nine_of_isLinTwoIndex hd) (e.trans e')

theorem jStarConcl_of_isLinTwoIndex (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    {m : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p m d)
    (he : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    JStarConcl p n Jt :=
  (h.eq_component_of_isLinTwoIndex hK huniq hcent hd he).2.2

end JStarHyp

end CFSG.AGLEmbedding

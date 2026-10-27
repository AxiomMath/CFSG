module

public import CFSG.ClassicalInvolution.TwoGroupCase.Q8
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Act

variable {G : Type*} [Group G]

theorem tl3_oddCore_char [Finite G] (R : Subgroup G) : (oddCore R).Characteristic := by
  rw [QuaternionStructure.oddCore_eq_pPrimeCore_two]
  infer_instance

theorem tl3_map_oddCore [Finite G] (R : Subgroup G) (φ : MulAut R) :
    Subgroup.map (↑φ : R →* R) (oddCore R) = oddCore R :=
  Subgroup.characteristic_iff_map_eq.mp (tl3_oddCore_char R) φ

noncomputable def tl3Act [Finite G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) →* MulAut (R ⧸ oddCore R) where
  toFun g := QuotientGroup.congr (oddCore R) (oddCore R) (R.normalizerMonoidHom g)
    (tl3_map_oddCore R _)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H r => simp [QuotientGroup.congr_mk]
  map_mul' g h := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H r =>
      rw [MulAut.mul_apply]
      erw [QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      simp

theorem tl3Act_mk [Finite G] (R : Subgroup G) (g : Subgroup.normalizer (R : Set G)) (r : R) :
    tl3Act R g (r : R ⧸ oddCore R) = ((R.normalizerMonoidHom g r : R) : R ⧸ oddCore R) :=
  QuotientGroup.congr_mk _ _ _ (tl3_map_oddCore R _) r

theorem mem_oddCore_iff_coe_mem_oddCoreImg (R : Subgroup G) (u : R) :
    u ∈ oddCore R ↔ (u : G) ∈ oddCoreImg R := by
  constructor
  · intro h
    exact ⟨u, h, rfl⟩
  · rintro ⟨u', hu', hu⟩
    have : u' = u := Subtype.ext hu
    rwa [← this]

theorem tl3_normalizerMonoidHom_coe (R : Subgroup G) (g : Subgroup.normalizer (R : Set G))
    (r : R) :
    ((R.normalizerMonoidHom g r : R) : G) = (g : G) * (r : G) * (g : G)⁻¹ := rfl

theorem tl3Act_eq_one_iff [Finite G] (R : Subgroup G) (g : Subgroup.normalizer (R : Set G)) :
    tl3Act R g = 1 ↔ ∀ r ∈ R, ⁅(g : G), r⁆ ∈ oddCoreImg R := by
  constructor
  · intro h r hr
    have h1 := DFunLike.congr_fun h ((⟨r, hr⟩ : R) : R ⧸ oddCore R)
    rw [tl3Act_mk, MulAut.one_apply, QuotientGroup.eq] at h1
    have h2 := (mem_oddCore_iff_coe_mem_oddCoreImg R _).mp h1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, tl3_normalizerMonoidHom_coe] at h2
    have h3 := conj_mem_oddCoreImg (Subgroup.le_normalizer hr) ((oddCoreImg R).inv_mem h2)
    have key : ∀ a : G, r * ((a * r * a⁻¹)⁻¹ * r)⁻¹ * r⁻¹ = ⁅a, r⁆ := by
      intro a
      rw [commutatorElement_def]; group
    have := key (g : G)
    simp only at h3
    rw [this] at h3
    exact h3
  · intro h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H r =>
      rw [tl3Act_mk, MulAut.one_apply, QuotientGroup.eq, mem_oddCore_iff_coe_mem_oddCoreImg,
        Subgroup.coe_mul, Subgroup.coe_inv, tl3_normalizerMonoidHom_coe]
      have h2 := conj_mem_oddCoreImg (Subgroup.le_normalizer (R.inv_mem r.2))
        ((oddCoreImg R).inv_mem (h (r : G) r.2))
      have key : ∀ a b : G, b⁻¹ * (⁅a, b⁆)⁻¹ * (b⁻¹)⁻¹ = (a * b * a⁻¹)⁻¹ * b := by
        intro a b
        rw [commutatorElement_def]; group
      rwa [key] at h2

theorem tl3Act_of_mem [Finite G] (R : Subgroup G) (r : R) :
    tl3Act R ⟨(r : G), Subgroup.le_normalizer r.2⟩ = MulAut.conj (r : R ⧸ oddCore R) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H s =>
    rw [tl3Act_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

end Act


theorem tl3_q8_card_central :
    Fintype.card {z : QuaternionGroup 2 // ∀ g : QuaternionGroup 2, z * g * z⁻¹ = g} = 2 := by
  decide +kernel

section AutQ8

variable {M : Type*} [Group M]

theorem tl3_natCard_mulAut_le (e : M ≃* QuaternionGroup 2) : Nat.card (MulAut M) ≤ 24 := by
  have f : MulAut M ≃ (QuaternionGroup 2 ≃* QuaternionGroup 2) :=
    { toFun := fun φ => e.symm.trans (φ.trans e)
      invFun := fun ψ => e.trans (ψ.trans e.symm)
      left_inv := fun φ => by ext m; simp
      right_inv := fun ψ => by ext q; simp }
  rw [Nat.card_congr f]
  exact q8_natCard_mulEquiv_le

theorem tl3_natCard_inn (e : M ≃* QuaternionGroup 2) :
    Nat.card (MulAut.conj : M →* MulAut M).range = 4 := by
  set K := (MulAut.conj : M →* MulAut M).ker with hKdef
  have hK : Nat.card K = 2 := by
    have e1 : K ≃ {z : M // ∀ g : M, z * g * z⁻¹ = g} :=
      Equiv.subtypeEquivRight fun z => by
        rw [hKdef, MonoidHom.mem_ker, MulEquiv.ext_iff]
        simp [MulAut.conj_apply]
    have e2 : {z : M // ∀ g : M, z * g * z⁻¹ = g} ≃
        {z : QuaternionGroup 2 // ∀ g : QuaternionGroup 2, z * g * z⁻¹ = g} :=
      Equiv.subtypeEquiv e.toEquiv fun z => by
        constructor
        · intro h g
          have := congrArg e (h (e.symm g))
          simpa using this
        · intro h g
          have := h (e g)
          apply e.injective
          simpa using this
    rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_eq_fintype_card, tl3_q8_card_central]
  have hM : Nat.card M = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [hM, hK] at h1
  have h2 : Nat.card (M ⧸ K) = 4 := by omega
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (MulAut.conj : M →* MulAut M)).toEquiv]
  exact h2

theorem tl3_inn_normal : ((MulAut.conj : M →* MulAut M).range).Normal := by
  refine ⟨fun n hn φ => ?_⟩
  obtain ⟨m, rfl⟩ := hn
  refine ⟨φ m, ?_⟩
  refine MulEquiv.ext fun g => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]


theorem tl3_inn_sup_zpowers_normal [Finite M] (e : M ≃* QuaternionGroup 2) {P : MulAut M} {k : ℕ}
    (hPk : P ^ 3 ^ k = 1) (hP1 : P ≠ 1) :
    ((MulAut.conj : M →* MulAut M).range ⊔ Subgroup.zpowers P).Normal := by
  set Inn := (MulAut.conj : M →* MulAut M).range with hInn
  have hA := tl3_natCard_mulAut_le e
  have hI := tl3_natCard_inn e
  have : Finite (MulAut M) :=
    Finite.of_injective (fun f : MulAut M => (f : M → M)) DFunLike.coe_injective
  have hApos : 0 < Nat.card (MulAut M) := Nat.card_pos
  have h4A : 4 ∣ Nat.card (MulAut M) := by
    have := Subgroup.card_subgroup_dvd_card Inn
    rwa [hI] at this
  have hord : orderOf P = 3 := by
    have hd : orderOf P ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hPk
    obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hdA : orderOf P ∣ Nat.card (MulAut M) := orderOf_dvd_natCard P
    rcases m with _ | _ | m
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hmo)) hP1
    · simpa using hmo
    · exfalso
      have h9 : 9 ∣ orderOf P := by
        rw [hmo]
        exact (pow_dvd_pow 3 (by omega : 2 ≤ m + 1 + 1))
      have h9A : 9 ∣ Nat.card (MulAut M) := h9.trans hdA
      have : 36 ∣ Nat.card (MulAut M) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4A h9A
      have := Nat.le_of_dvd hApos this
      omega
  set B := Inn ⊔ Subgroup.zpowers P with hB
  have h4 : 4 ∣ Nat.card B := by
    rw [← hI]; exact Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card B := by
    rw [← hord, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le le_sup_right
  have h12 : 12 ∣ Nat.card B := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have h12le : 12 ≤ Nat.card B := Nat.le_of_dvd hBpos h12
  have hidx := Subgroup.card_mul_index B
  have hidx2 : B.index ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hidx0 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  interval_cases hi : B.index
  · exact absurd rfl hidx0
  · rw [Subgroup.index_eq_one.mp hi]; exact Subgroup.normal_top
  · exact Subgroup.normal_of_index_eq_two hi

end AutQ8


end CFSG.ClassicalInvolution.Q3

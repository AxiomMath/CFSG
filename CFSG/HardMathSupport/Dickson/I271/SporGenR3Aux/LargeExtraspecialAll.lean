module

public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponentsApply
public import CFSG.CharacterTheory.Burnside

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll

open CFSG.Open CFSG.HardMathSupport.MathTwE6

variable {G : Type*} [Group G]

section Normalizer

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem mem_normalizer_sup [Finite G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

end Normalizer

section Orbit

theorem index_normalizer_le [Finite G] {X Γ J : Subgroup G}
    (hΓ : Γ ≤ Subgroup.normalizer (X : Set G)) (hJ : IsComponentOf J X) {d k : ℕ}
    (hd : d ∣ (Subgroup.center J).index) (hdk : ¬ d ^ (k + 1) ∣ Nat.card G) :
    ((Subgroup.normalizer (J : Set G)).subgroupOf Γ).index ≤ k := by
  classical
  by_contra hlt
  replace hlt := not_le.1 hlt
  set H : Subgroup Γ := (Subgroup.normalizer (J : Set G)).subgroupOf Γ with hH
  letI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  have hidx : H.index = Fintype.card (Γ ⧸ H) := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  obtain ⟨e⟩ : Nonempty (Fin (k + 1) ↪ Γ ⧸ H) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; omega)
  let rep : Γ ⧸ H → Γ := Quotient.out
  have hrep : ∀ q, ((rep q : Γ) : Γ ⧸ H) = q := fun q => QuotientGroup.out_eq' q
  let f : Fin (k + 1) → Subgroup G := fun i =>
    J.map (MulAut.conj ((rep (e i) : Γ) : G)).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f] at hij
    have h1 : J.map (MulAut.conj (((rep (e i) : Γ) : G)⁻¹ * ((rep (e j) : Γ) : G))).toMonoidHom
        = J := by
      rw [← map_conj_map_conj J ((rep (e j) : Γ) : G) ((rep (e i) : Γ) : G)⁻¹, ← hij,
        map_conj_map_conj, inv_mul_cancel, map_conj_one]
    have h2 := (map_conj_eq_iff_mem_normalizer J _).1 h1
    have h3 : (rep (e i))⁻¹ * rep (e j) ∈ H :=
      Subgroup.mem_subgroupOf.2 (by simpa using h2)
    have h4 : e i = e j := by
      rw [← hrep (e i), ← hrep (e j)]
      exact QuotientGroup.eq.2 h3
    exact e.injective h4
  have hcomp : ∀ i, IsComponentOf (f i) X := fun i =>
    isComponentOf_map_conj_of_mem_normalizer hJ (hΓ (rep (e i)).2)
  let S : Finset (Subgroup G) := Finset.univ.image f
  have hS : S.card = k + 1 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  apply hdk
  have hpow := pow_card_dvd_of_commute S d ?_ ?_
  · rwa [hS] at hpow
  · intro A hA B hB hne a ha b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB
    exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne (hcomp i) (hcomp j) hne ha hb
  · intro A hA
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    simp only [f]
    rw [index_center_map_conj]
    exact hd

theorem pow_factorial_mem_normalizer [Finite G] {X J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hJ : IsComponentOf J X) {d k : ℕ}
    (hd : d ∣ (Subgroup.center J).index) (hdk : ¬ d ^ (k + 1) ∣ Nat.card G) :
    g ^ k.factorial ∈ Subgroup.normalizer (J : Set G) := by
  have hΓ : Subgroup.zpowers g ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hg
  have hc := index_normalizer_le hΓ hJ hd hdk
  set H : Subgroup (Subgroup.zpowers g) :=
    (Subgroup.normalizer (J : Set G)).subgroupOf (Subgroup.zpowers g) with hH
  have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) ^ H.index ∈ H :=
    Subgroup.pow_index_mem H _
  have hg' : g ^ H.index ∈ Subgroup.normalizer (J : Set G) := by
    have := (Subgroup.mem_subgroupOf).1 hmem
    simpa using this
  obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hc
  rw [ht, pow_mul]
  exact (Subgroup.normalizer (J : Set G)).pow_mem hg' t

end Orbit

section Quasisimple

variable {J : Subgroup G}

theorem not_comm_quotient_center (hJ : CFSG.Open.IsQuasisimple J) :
    ¬ ∀ a b : J ⧸ Subgroup.center J, a * b = b * a := by
  intro hcomm
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2
  have h1 : commutator J ≤ Subgroup.center J := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    have h := map_commutatorElement (QuotientGroup.mk' (Subgroup.center J)) g₁ g₂
    simp only [QuotientGroup.mk'_apply] at h
    rw [h]
    exact commutatorElement_eq_one_iff_commute.2 (hcomm _ _)
  have htop : (⊤ : Subgroup J) ≤ Subgroup.center J := hJ.1 ▸ h1
  have hab : ∀ a b : J, a * b = b * a := fun a b =>
    (Subgroup.mem_center_iff.1 (htop (Subgroup.mem_top b))) a
  have h2 : commutator J ≤ ⊥ := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_commute.2 (hab _ _)
  have hone : ∀ x : J, x = 1 := fun x =>
    Subgroup.mem_bot.1 (h2 (hJ.1 ▸ Subgroup.mem_top x))
  obtain ⟨x, hx⟩ := exists_ne (1 : J ⧸ Subgroup.center J)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx (by rw [hone y]; rfl)

theorem eq_two_pow_mul_three_pow {n : ℕ} (hn : n ≠ 0)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = 3) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have hsub : n.factorization.support ⊆ {2, 3} := by
    intro r hr
    rw [Nat.support_factorization] at hr
    have := h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
    simpa using this
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsub _ (by simp), Finset.prod_pair (by norm_num)]

theorem exists_prime_ge_five_dvd_index_center [Finite G] (hJ : CFSG.Open.IsQuasisimple J) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ (Subgroup.center J).index := by
  by_contra hno
  have hno' : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ (Subgroup.center J).index := fun r hr h5 hd =>
    hno ⟨r, hr, h5, hd⟩
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2
  have hne : (Subgroup.center J).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpr : ∀ r : ℕ, r.Prime → r ∣ (Subgroup.center J).index → r = 2 ∨ r = 3 := by
    intro r hr hrd
    by_contra hh
    have h2 := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      norm_num at hr
    have h5 : 5 ≤ r := by omega
    exact hno' r hr h5 hrd
  have hform := eq_two_pow_mul_three_pow hne hpr
  letI : Fintype (J ⧸ Subgroup.center J) := Fintype.ofFinite _
  have hsolv : Group.IsSolvable (J ⧸ Subgroup.center J) := by
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num)
      (a := (Subgroup.center J).index.factorization 2)
      (b := (Subgroup.center J).index.factorization 3) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hform
  exact not_comm_quotient_center hJ (IsSimpleGroup.comm_iff_isSolvable.2 hsolv)

end Quasisimple

section CentralSylow

theorem exists_pComplement_of_central_order_prime {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {z : H} (hz : orderOf z = p) (hzc : ∀ h : H, h * z = z * h)
    (h2 : ¬ p ^ 2 ∣ Nat.card H) :
    ∃ K : Subgroup H, K.Normal ∧ commutator H ≤ K ∧ Nat.card K * p = Nat.card H ∧
      ¬ p ∣ Nat.card K ∧ ∀ h : H, h ∈ K ↔ ¬ p ∣ orderOf h := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ Nat.card H := by
    rw [← hz]
    exact orderOf_dvd_natCard z
  have hf : (Nat.card H).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card H).factorization p :=
      (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using hpd)
    have h2' : ¬ 2 ≤ (Nat.card H).factorization p := fun h =>
      h2 ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h)
    omega
  have hcardP : Nat.card (Subgroup.zpowers z) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_zpowers, hz, hf, pow_one]
  let P : Sylow p H := Sylow.ofCard (Subgroup.zpowers z) hcardP
  have hPz : (P : Subgroup H) = Subgroup.zpowers z := rfl
  have hPc : ∀ x ∈ (P : Subgroup H), ∀ y : H, y * x = x * y := by
    intro x hx y
    rw [hPz] at hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_right (show Commute y z from hzc y) n)).eq
  have hnorm : Subgroup.normalizer (P : Subgroup H) ≤ Subgroup.centralizer (P : Set H) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hPc x hx n).symm
  have hPcard : Nat.card (P : Subgroup H) = p := by
    rw [hPz, Nat.card_zpowers, hz]
  let φ : H →* P := MonoidHom.transferSylow P hnorm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hcard : Nat.card φ.ker * p = Nat.card H := by
    have := hcompl.card_mul
    rwa [hPcard] at this
  have hcomm_ker : commutator H ≤ φ.ker := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_commute.2 ?_
    exact Subtype.ext (hPc _ (φ g₂).2 _)
  have hKp : ¬ p ∣ Nat.card φ.ker := by
    intro hdv
    apply h2
    rw [← hcard, sq]
    exact Nat.mul_dvd_mul hdv dvd_rfl
  refine ⟨φ.ker, MonoidHom.normal_ker φ, hcomm_ker, hcard, hKp, fun h => ?_⟩
  constructor
  · intro hh hpo
    apply hKp
    have h1 : orderOf (⟨h, hh⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at h1
    exact hpo.trans h1
  · intro hnd
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (φ h) ∣ orderOf h := orderOf_map_dvd φ h
    have h3 : orderOf (φ h) ∣ p := by
      have := orderOf_dvd_natCard (φ h)
      rwa [hPcard] at this
    have hcop : Nat.Coprime (orderOf h) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h3)

theorem false_of_perfect_central_order_prime {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {z : H} (hz : orderOf z = p) (hzc : ∀ h : H, h * z = z * h)
    (h2 : ¬ p ^ 2 ∣ Nat.card H) (hperf : commutator H = ⊤) : False := by
  obtain ⟨K, -, hKc, hcard, -, -⟩ := exists_pComplement_of_central_order_prime hp hz hzc h2
  have hK : K = ⊤ := top_le_iff.1 (hperf ▸ hKc)
  have hKH : Nat.card K = Nat.card H := by rw [hK, Subgroup.card_top]
  rw [hKH] at hcard
  have hpos : 0 < Nat.card H := Nat.card_pos
  have := hp.two_le
  nlinarith

theorem not_sq_dvd_card_of_le_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {Q C : Subgroup G}
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup p P →
      Nat.card P ≤ p)
    (hC : C ≤ Subgroup.centralizer (Q : Set G)) : ¬ p ^ 2 ∣ Nat.card C := by
  intro h2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p C))
  have hcard : Nat.card ((P : Subgroup C).map C.subtype) = p ^ (Nat.card C).factorization p := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
  have hf : 2 ≤ (Nat.card C).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h2
  have hle := hCQ ((P : Subgroup C).map C.subtype) ((Subgroup.map_subtype_le _).trans hC)
    (P.isPGroup'.map C.subtype)
  rw [hcard] at hle
  have h3 : p ^ 2 ≤ p ^ (Nat.card C).factorization p := Nat.pow_le_pow_right hp.pos hf
  have h4 : p ^ 2 ≤ p := h3.trans hle
  have := hp.two_le
  nlinarith

theorem not_dvd_card_of_perfect_le_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {w : G}
    (hw : orderOf w = p) {Q J : Subgroup G} (hwQ : w ∈ Subgroup.centralizer (Q : Set G))
    (hwJ : ∀ j ∈ J, j * w = w * j) (hJQ : J ≤ Subgroup.centralizer (Q : Set G))
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup p P →
      Nat.card P ≤ p)
    (hperf : commutator J = ⊤) : ¬ p ∣ Nat.card J := by
  classical
  intro hpJ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hwJ' : w ∈ J := by
    set A : Subgroup G := Subgroup.zpowers (x : G) with hA
    set B : Subgroup G := Subgroup.zpowers w with hB
    have hwx : w ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact ((Commute.zpow_left (show Commute (x : G) w from hwJ x x.2) n)).eq
    have hBA : B ≤ Subgroup.normalizer (A : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      rw [hB, Subgroup.zpowers_le]
      exact hwx
    have hprod := card_sup_mul_card_inf_of_le_normalizer hBA
    have hAc : Nat.card A = p := by rw [hA, Nat.card_zpowers, hxo]
    have hBc : Nat.card B = p := by rw [hB, Nat.card_zpowers, hw]
    have hdvd : Nat.card ↥(A ⊔ B) ∣ p ^ 2 :=
      Dvd.intro _ (hprod.trans (by rw [hAc, hBc, sq]))
    obtain ⟨i, -, hiA⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hpg : IsPGroup p ↥(A ⊔ B) := IsPGroup.of_card hiA
    have hle : A ⊔ B ≤ Subgroup.centralizer (Q : Set G) := by
      refine sup_le ?_ ?_
      · rw [hA, Subgroup.zpowers_le]
        exact hJQ x.2
      · rw [hB, Subgroup.zpowers_le]
        exact hwQ
    have hcard := hCQ _ hle hpg
    have hAeq : A = A ⊔ B :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAc]; exact hcard)
    have hBA' : B ≤ A := le_sup_right.trans hAeq.ge
    have hwA : w ∈ A := hBA' (by rw [hB]; exact Subgroup.mem_zpowers w)
    have hAJ : A ≤ J := by
      rw [hA, Subgroup.zpowers_le]
      exact x.2
    exact hAJ hwA
  have h2 := not_sq_dvd_card_of_le_centralizer hp hCQ hJQ
  refine false_of_perfect_central_order_prime hp (z := (⟨w, hwJ'⟩ : J)) ?_ ?_ h2 hperf
  · rw [← Subgroup.orderOf_coe]
    exact hw
  · intro h
    exact Subtype.ext (hwJ h h.2)

theorem eq_zpowers_of_central_sylow [Finite G] {p : ℕ} (hp : p.Prime) {w : G}
    (hw : orderOf w = p) {X C : Subgroup G} (hCX : C ≤ X)
    (hXC : X ≤ Subgroup.normalizer (C : Set G)) (hwC : w ∈ C)
    (hwX : ∀ x ∈ X, x * w = w * x) (hC2 : ¬ p ^ 2 ∣ Nat.card C)
    (hO : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      Nat.Coprime p (Nat.card N) → N = ⊥) : C = Subgroup.zpowers w := by
  classical
  have hzc : ∀ h : C, h * (⟨w, hwC⟩ : C) = (⟨w, hwC⟩ : C) * h := fun h =>
    Subtype.ext (hwX h (hCX h.2))
  have hzo : orderOf (⟨w, hwC⟩ : C) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hw
  obtain ⟨K, -, -, hcard, hKp, hK⟩ :=
    exists_pComplement_of_central_order_prime hp hzo hzc hC2
  set K' : Subgroup G := K.map C.subtype with hK'
  have hmem : ∀ c : G, c ∈ K' ↔ c ∈ C ∧ ¬ p ∣ orderOf c := by
    intro c
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, ?_⟩
      have := (hK h).1 hh
      rwa [← Subgroup.orderOf_coe] at this
    · rintro ⟨hc, hnd⟩
      refine ⟨⟨c, hc⟩, (hK _).2 ?_, rfl⟩
      rwa [← Subgroup.orderOf_coe]
  have hK'X : K' ≤ X := fun c hc => hCX ((hmem c).1 hc).1
  have hXK' : X ≤ Subgroup.normalizer (K' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hxC := (Subgroup.mem_normalizer_iff.1 (hXC hx)) c
    have hord : orderOf (x * c * x⁻¹) = orderOf c := by
      have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective c
      simpa [MulAut.conj_apply] using this
    rw [hmem, hmem, hord, ← hxC]
  have hKc : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective C.subtype_injective
  have hcop : Nat.Coprime p (Nat.card K') := by
    rw [hKc]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hKp
  have hbot := hO K' hK'X hXK' hcop
  have hK1 : Nat.card K = 1 := by
    rw [← hKc, hbot, Subgroup.card_bot]
  rw [hK1, one_mul] at hcard
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hwC) ?_
  rw [Nat.card_zpowers, hw, hcard]

theorem pow_dvd_card_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {w : G} (hw : orderOf w = p)
    {L : Subgroup G} (hL : L ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G))
    {n : ℕ} (hn : p ^ n ∣ Nat.card L) :
    p ^ n ∣ Nat.card (Subgroup.centralizer ({w} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let ψ : L →* MulAut (Subgroup.zpowers w) :=
    (normalizerToMulAut (Subgroup.zpowers w)).comp (Subgroup.inclusion hL)
  have hker : ((ψ.ker).map L.subtype) ≤ Subgroup.centralizer ({w} : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : (Subgroup.inclusion hL g) ∈ (normalizerToMulAut (Subgroup.zpowers w)).ker := hg
    rw [mem_ker_normalizerToMulAut] at h1
    refine Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers w)) ?_
    exact h1
  have hcardmul := Subgroup.card_mul_index ψ.ker
  have hind : ψ.ker.index ∣ p - 1 := by
    rw [Subgroup.index_ker]
    haveI : Finite (MulAut (Subgroup.zpowers w)) :=
      Finite.of_injective (fun φ : MulAut (Subgroup.zpowers w) => (φ : _ → _))
        DFunLike.coe_injective
    have h1 : Nat.card ψ.range ∣ Nat.card (MulAut (Subgroup.zpowers w)) :=
      Subgroup.card_subgroup_dvd_card _
    rwa [IsCyclic.card_mulAut, Nat.card_zpowers, hw, Nat.totient_prime hp] at h1
  have hcop : Nat.Coprime (p ^ n) ψ.ker.index := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_)
    have := Nat.le_of_dvd (by have := hp.two_le; omega) (hdv.trans hind)
    have := hp.two_le
    omega
  have hdvd : p ^ n ∣ Nat.card ψ.ker := by
    refine Nat.Coprime.dvd_of_dvd_mul_right hcop ?_
    rw [hcardmul]
    exact hn
  have hkc : Nat.card ((ψ.ker).map L.subtype) = Nat.card ψ.ker :=
    Subgroup.card_map_of_injective L.subtype_injective
  exact (hkc ▸ hdvd).trans (Subgroup.card_dvd_of_le hker)

end CentralSylow

end CFSG.HardMathSupport.Dickson.I271.LargeExtraspecialAll

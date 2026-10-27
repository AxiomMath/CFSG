module

public import CFSG.ClassicalInvolution.Q3.Q3T6LinFin
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

theorem map_commutator_of_surjective {H S : Type*} [Group H] [Group S] (φ : H →* S)
    (hφ : Function.Surjective φ) : (commutator H).map φ = commutator S := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective φ hφ]

theorem exists_pow_two_pow_eq_one_of_isPGroup_zpowers {H : Type*} [Group H] {g : H}
    (hg : IsPGroup 2 (Subgroup.zpowers g)) : ∃ n : ℕ, g ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := hg ⟨g, Subgroup.mem_zpowers g⟩
  exact ⟨n, congrArg Subtype.val hn⟩

theorem mem_of_map_of_oddKernel {H Q : Type*} [Group H] [Group Q] (φ : H →* Q)
    (N : Subgroup H) [N.Normal] (hker : Odd (Nat.card φ.ker)) {g : H}
    (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) (hgN : φ g ∈ N.map φ) : g ∈ N := by
  obtain ⟨n, hn, hφn⟩ := hgN
  have hk : n⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφn, inv_mul_cancel]
  have hko : Odd (orderOf (n⁻¹ * g)) :=
    hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard φ.ker hk)
  have hmk : (QuotientGroup.mk g : H ⧸ N) = QuotientGroup.mk (n⁻¹ * g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).mpr hn, inv_one,
      one_mul]
  obtain ⟨m, hm⟩ := hg
  have h1 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hm, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ orderOf (n⁻¹ * g) := by
    rw [hmk]
    exact orderOf_map_dvd (QuotientGroup.mk' N) _
  have hcop : Nat.Coprime (2 ^ m) (orderOf (n⁻¹ * g)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hko)
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_commutator_of_two_element_of_oddKernel {H : Type*} [Group H]
    (φ : H →* SL(2, ZMod 3)) (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {g : H}
    (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) : g ∈ commutator H := by
  refine mem_of_map_of_oddKernel φ (commutator H) hker hg ?_
  rw [map_commutator_of_surjective φ hφ]
  obtain ⟨n, hn⟩ := hg
  exact sl2Three_mem_commutator_of_two_element ⟨n, by rw [← map_pow, hn, map_one]⟩

theorem mem_commutator_of_isPGroup_two_of_oddKernel {H : Type*} [Group H]
    (φ : H →* SL(2, ZMod 3)) (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) {g : H}
    (hg : IsPGroup 2 (Subgroup.zpowers g)) : g ∈ commutator H :=
  mem_commutator_of_two_element_of_oddKernel φ hφ hker
    (exists_pow_two_pow_eq_one_of_isPGroup_zpowers hg)

section Equiv

variable {P : Type*} [Group P]

theorem normal_cases_of_equiv_sl2Three (e : P ≃* SL(2, ZMod 3)) (N : Subgroup P) (hN : N.Normal) :
    N = ⊥ ∨ N = Subgroup.center P ∨ N = commutator P ∨ N = ⊤ := by
  have hN' : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  have hback : (N.map e.toMonoidHom).comap e.toMonoidHom = N :=
    Subgroup.comap_map_eq_self_of_injective e.injective N
  rcases sl2Three_normal_cases _ hN' with h | h | h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp h
  · right; left
    rw [← hback, h]
    ext x
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    exact (mem_center_iff_of_equiv_sl2 e x).symm
  · right; right; left
    rw [← hback, h, ← map_commutator_of_surjective e.toMonoidHom e.surjective,
      Subgroup.comap_map_eq_self_of_injective e.injective]
  · right; right; right
    rw [← hback, h, Subgroup.comap_top]

theorem natCard_commutator_of_equiv_sl2Three (e : P ≃* SL(2, ZMod 3)) :
    Nat.card (commutator P) = 8 := by
  rw [← sl2Three_card_commutator, ← map_commutator_of_surjective e.toMonoidHom e.surjective,
    Subgroup.card_map_of_injective e.injective]

theorem derived₂_eq_center_of_equiv_sl2Three (e : P ≃* SL(2, ZMod 3)) :
    ⁅commutator P, commutator P⁆ = Subgroup.center P := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_commutator, map_commutator_of_surjective e.toMonoidHom e.surjective,
    sl2Three_derived₂_eq_center]
  exact (Subgroup.map_center_eq e).symm

theorem commutator_ne_top_of_equiv_sl2Three (e : P ≃* SL(2, ZMod 3)) : commutator P ≠ ⊤ := by
  intro h
  have := natCard_commutator_of_equiv_sl2Three e
  rw [h, Subgroup.card_top, Nat.card_congr e.toEquiv, natCard_sl2Three] at this
  omega

theorem isSolvable_of_equiv_sl2Three (e : P ≃* SL(2, ZMod 3)) : Group.IsSolvable P := by
  have := sl2Three_isSolvable
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Equiv

section Exact

variable {K G : Type*} [Group K] [Group G] [Finite G]

theorem classicalInvolutionOddCore_map_eq_bot_of_sl2Three (ψ : K →* G) {R : Subgroup K}
    (e : R ≃* SL(2, ZMod 3)) (hinv : ∃ y ∈ R.map ψ, orderOf y = 2) :
    classicalInvolutionOddCore ↥(R.map ψ) = ⊥ := by
  obtain ⟨y, hy, hy2⟩ := hinv
  set K' := R.map ψ with hK'
  let φ : ↥R →* ↥K' := ψ.subgroupMap R
  have hφ : Function.Surjective φ := ψ.subgroupMap_surjective R
  set N := classicalInvolutionOddCore ↥K' with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥K'
  have hnorm : (N.comap φ).Normal := inferInstance
  have hback : (N.comap φ).map φ = N := Subgroup.map_comap_eq_self_of_surjective hφ N
  have hone : ∀ k : ℕ, Nat.card N ∣ 2 ^ k → N = ⊥ := fun k hdvd =>
    Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hNodd)) hdvd)
  rcases normal_cases_of_equiv_sl2Three e _ hnorm with h | h | h | h
  · rw [← hback, h, Subgroup.map_bot]
  · have hNM : N = (Subgroup.center ↥R).map φ := by rw [← hback, h]
    refine hone 1 ?_
    have := Subgroup.card_map_dvd (Subgroup.center ↥R) φ
    rw [← hNM, natCard_center_of_equiv_sl2 (by rw [Nat.card_zmod]; decide) e] at this
    simpa using this
  · have hNM : N = (commutator ↥R).map φ := by rw [← hback, h]
    refine hone 3 ?_
    have := Subgroup.card_map_dvd (commutator ↥R) φ
    rw [← hNM, natCard_commutator_of_equiv_sl2Three e] at this
    simpa using this
  · exfalso
    have hNtop : N = ⊤ := by
      rw [← hback, h, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ]
    rw [hNtop, Subgroup.card_top] at hNodd
    have hy' : orderOf (⟨y, hy⟩ : ↥K') = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hy2
    have h2 : 2 ∣ Nat.card ↥K' := hy' ▸ orderOf_dvd_natCard _
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)

end Exact

section Sylow

variable {K : Type*} [Group K] [Finite K]

private theorem two_pow_eq_eight {a m i : ℕ} (hm : Odd m) (hi : Odd i) (h : 2 ^ a * i = 8 * m) :
    2 ^ a = 8 := by
  have h1 : 2 ^ a ∣ 8 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm))
      (Dvd.intro i h)
  have h2 : 8 ∣ 2 ^ a :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hi) : Nat.Coprime 8 i)
      (Dvd.intro m h.symm)
  exact Nat.dvd_antisymm h1 h2

theorem exists_quaternion_of_quotEquiv_sl2Three
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3)) (T : Sylow 2 K) :
    Nonempty ((T : Subgroup K) ≃* QuaternionGroup 2) := by
  set O := classicalInvolutionOddCore K with hOdef
  have hO : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card K
  let ρ : K →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' O)
  have hρker : ∀ x, ρ x = 1 → x ∈ O := fun x hx => by
    have : e (QuotientGroup.mk' O x) = 1 := hx
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  have hT2 : ∀ x : (T : Subgroup K), ∃ n : ℕ, (x : K) ^ 2 ^ n = 1 := fun x => by
    obtain ⟨n, hn⟩ := T.isPGroup' x
    exact ⟨n, congrArg Subtype.val hn⟩
  have hinj : Function.Injective (ρ.comp (T : Subgroup K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : K) ∈ O := hρker x hx
    obtain ⟨n, hn⟩ := hT2 x
    have hd1 : orderOf (x : K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    have hd2 : orderOf (x : K) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    have hcop : Nat.Coprime (orderOf (x : K)) (Nat.card O) :=
      Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hO))
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd2))
  have hcardK : Nat.card K = 24 * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, Nat.card_congr e.toEquiv,
      natCard_sl2Three]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hidx : Odd (T : Subgroup K).index := Nat.odd_iff.mpr (by have := T.not_dvd_index; omega)
  have h8 : Nat.card T = 8 := by
    have h3m : Odd (3 * Nat.card O) := (by decide : Odd 3).mul hO
    have hmul : Nat.card T * (T : Subgroup K).index = Nat.card K := Subgroup.card_mul_index _
    have : 2 ^ a * (T : Subgroup K).index = 8 * (3 * Nat.card O) := by
      rw [← ha, hmul, hcardK]; ring
    rw [ha]
    exact two_pow_eq_eight h3m hidx this
  have hle : (ρ.comp (T : Subgroup K).subtype).range ≤ sl2ThreeQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := hT2 x
    refine mem_sl2ThreeQ_iff.mpr (sl2Three_pow_four_of_two_element ⟨n, ?_⟩)
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_pow, hn, map_one]
  have hrange : (ρ.comp (T : Subgroup K).subtype).range = sl2ThreeQ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [natCard_sl2ThreeQ, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, h8]
  obtain ⟨q⟩ := nonempty_mulEquiv_sl2ThreeQ
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans q.symm⟩

theorem exists_quaternion_of_sl2_three {F : Type} [Field F] (hF : Nat.card F = 3)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (T : Sylow 2 K) :
    Nonempty ((T : Subgroup K) ≃* QuaternionGroup 2) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  exact exists_quaternion_of_quotEquiv_sl2Three (e.trans eF) T

theorem exists_quaternion_of_sl2_three' {F : Type} [Field F] (hF : Nat.card F = 3)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (T : Sylow 2 K) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) :=
  ⟨3, le_rfl, exists_quaternion_of_sl2_three hF e T⟩

end Sylow

section Field

variable {F : Type*} [Field F]

theorem normal_cases_of_equiv_sl2_of_card_three (hF : Nat.card F = 3) {P : Type*} [Group P]
    (e : P ≃* SL(2, F)) (N : Subgroup P) (hN : N.Normal) :
    N = ⊥ ∨ N = Subgroup.center P ∨ N = commutator P ∨ N = ⊤ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  exact normal_cases_of_equiv_sl2Three (e.trans eF) N hN

theorem isClassicalSL2_normal_cases_of_card_three (hF : Nat.card F = 3) {G : Type*} [Group G]
    {J : Subgroup G} {d : G} (h : IsClassicalSL2 F J d) (N : Subgroup J) (hN : N.Normal) :
    N = ⊥ ∨ N = Subgroup.center J ∨ N = commutator J ∨ N = ⊤ := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact normal_cases_of_equiv_sl2_of_card_three hF e N hN

theorem natCard_commutator_of_equiv_sl2_of_card_three (hF : Nat.card F = 3) {P : Type*}
    [Group P] (e : P ≃* SL(2, F)) : Nat.card (commutator P) = 8 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  exact natCard_commutator_of_equiv_sl2Three (e.trans eF)

theorem commutator_ne_top_of_equiv_sl2_of_card_three (hF : Nat.card F = 3) {P : Type*}
    [Group P] (e : P ≃* SL(2, F)) : commutator P ≠ ⊤ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  exact commutator_ne_top_of_equiv_sl2Three (e.trans eF)

theorem mem_commutator_of_two_element_of_oddKernel_of_card_three (hF : Nat.card F = 3)
    {H : Type*} [Group H] (φ : H →* SL(2, F)) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) {g : H} (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) :
    g ∈ commutator H := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  have hk : (eF.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  refine mem_commutator_of_two_element_of_oddKernel (eF.toMonoidHom.comp φ)
    (eF.surjective.comp hφ) ?_ hg
  rwa [hk]

theorem mem_commutator_of_isPGroup_two_of_oddKernel_of_card_three (hF : Nat.card F = 3)
    {H : Type*} [Group H] (φ : H →* SL(2, F)) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) {g : H} (hg : IsPGroup 2 (Subgroup.zpowers g)) :
    g ∈ commutator H :=
  mem_commutator_of_two_element_of_oddKernel_of_card_three hF φ hφ hker
    (exists_pow_two_pow_eq_one_of_isPGroup_zpowers hg)

theorem classicalInvolutionOddCore_map_eq_bot_of_card_three (hF : Nat.card F = 3)
    {K G : Type*} [Group K] [Group G] [Finite G] (ψ : K →* G) {R : Subgroup K}
    (e : R ≃* SL(2, F)) (hinv : ∃ y ∈ R.map ψ, orderOf y = 2) :
    classicalInvolutionOddCore ↥(R.map ψ) = ⊥ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨eF⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF
  exact classicalInvolutionOddCore_map_eq_bot_of_sl2Three ψ (e.trans eF) hinv

end Field

end CFSG.ClassicalInvolution.Q3.Q3T6

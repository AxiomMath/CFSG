module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.ClassicalInvolution.TwoGroupCase.Q8
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.ClassicalInvolution

open CFSG QuaternionGroup
open scoped MatrixGroups

universe u

theorem eq_one_or_eq_of_commute_q8 {Y : Type*} [Group Y] {T : Subgroup Y} {k : ℕ}
    (eT : T ≃* QuaternionGroup (2 ^ k)) {Q : Subgroup Y} (eQ : QuaternionGroup 2 ≃* Q)
    (hQT : Q ≤ T) {c : Y} (hcT : c ∈ T) (hc : ∀ q ∈ Q, c * q = q * c) :
    c = 1 ∨ c = (eQ (a 2) : Y) := by
  obtain ⟨u, hu2, huniq, -⟩ := exists_unique_involution_of_mulEquiv_quaternionGroup eT
  have hT2 : IsPGroup 2 T := isPGroup_two_of_mulEquiv_quaternionGroup eT
  let ι : QuaternionGroup 2 →* T := (Subgroup.inclusion hQT).comp eQ.toMonoidHom
  have hι : Function.Injective ι := fun x y h => by
    have h' : ((ι x : T) : Y) = ((ι y : T) : Y) := congrArg Subtype.val h
    exact eQ.injective (Subtype.ext h')
  have hι2 : orderOf (ι (a 2)) = 2 := by
    rw [orderOf_injective ι hι]
    exact orderOf_eq_prime (by decide) (by decide)
  have hzu : ι (a 2) = u := huniq _ hι2
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hcz⟩ := hcon
  let cT : T := ⟨c, hcT⟩
  have hcT1 : cT ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hcTu : cT ≠ u := fun h => hcz (congrArg Subtype.val (h.trans hzu.symm))
  have hcomm : ∀ q, cT * ι q = ι q * cT := fun q => Subtype.ext (hc _ (eQ q).2)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hT2) cT
  rcases j with _ | _ | j
  · exact hcT1 (orderOf_eq_one_iff.mp (by simpa using hj))
  · exact hcTu (huniq cT (by simpa using hj))
  · set d : T := cT ^ (2 ^ j) with hd
    have hdo : orderOf d = 4 := by
      rw [hd, orderOf_pow_of_dvd (pow_ne_zero j two_ne_zero)
        (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj,
        Nat.pow_div (by omega) (by norm_num)]
      have : j + 1 + 1 - j = 2 := by omega
      rw [this]
    have hd2 : d ^ 2 = u := huniq _ (by
      rw [orderOf_pow_of_dvd two_ne_zero (by rw [hdo]; norm_num), hdo])
    have hxd : Commute (ι (a 1)) d := (Commute.pow_right (hcomm (a 1)).symm _)
    have hx2 : ι (a 1) ^ 2 = u := by
      rw [← hzu, ← map_pow]
      congr 1
    have hu1 : u * u = 1 := by
      rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hu2])
    have hw2 : (ι (a 1) * d) ^ 2 = 1 := by
      rw [hxd.mul_pow, hx2, hd2, hu1]
    have hw : ι (a 1) * d = 1 ∨ ι (a 1) * d = u := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hw2) with h | h
      · exact Or.inl (orderOf_eq_one_iff.mp h)
      · exact Or.inr (huniq _ h)
    have hdy : d * ι (xa 0) = ι (xa 0) * d :=
      (Commute.pow_left (hcomm (xa 0)) _)
    have hdq : ∃ q0 : QuaternionGroup 2, (q0 = 1 ∨ q0 = a 2) ∧ d = ι ((a 1)⁻¹ * q0) := by
      rcases hw with h | h
      · exact ⟨1, Or.inl rfl, by
          rw [map_mul, map_one, mul_one, map_inv]; exact eq_inv_of_mul_eq_one_right h⟩
      · refine ⟨a 2, Or.inr rfl, ?_⟩
        rw [map_mul, map_inv, hzu]
        exact eq_inv_mul_of_mul_eq h
    obtain ⟨q0, hq0, hdeq⟩ := hdq
    rw [hdeq, ← map_mul, ← map_mul] at hdy
    have := hι hdy
    rcases hq0 with rfl | rfl <;> exact absurd this (by decide)

theorem natCard_le_forty_eight_of_normal_q8 {Y : Type*} [Group Y] [Finite Y] (hO : oddCore Y = ⊥)
    {k : ℕ} (hT : ∀ T : Sylow 2 Y, Nonempty ((T : Subgroup Y) ≃* QuaternionGroup (2 ^ k)))
    (Q : Subgroup Y) [Q.Normal] (eQ : QuaternionGroup 2 ≃* Q) : Nat.card Y ≤ 48 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Y := Subgroup.centralizer (Q : Set Y) with hC
  have hQ2 : IsPGroup 2 Q := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr eQ.toEquiv.symm, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hC2 : Nat.card C ≤ 2 := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
    let P' : Subgroup Y := (P : Subgroup C).map C.subtype
    have hP' : IsPGroup 2 P' := P.isPGroup'.map C.subtype
    obtain ⟨T, hPT⟩ := hP'.exists_le_sylow
    obtain ⟨eT⟩ := hT T
    have hQT : Q ≤ (T : Subgroup Y) := hQ2.le_sylow_of_normal T
    have hP'sub : (P' : Set Y) ⊆ {1, (eQ (a 2) : Y)} := by
      intro c hc
      obtain ⟨c', hc'P, rfl⟩ := hc
      have hcC : (c' : Y) ∈ C := c'.2
      rcases eq_one_or_eq_of_commute_q8 eT eQ hQT (hPT ⟨c', hc'P, rfl⟩)
        (fun q hq => (Subgroup.mem_centralizer_iff.mp hcC q hq).symm) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hP2 : Nat.card P ≤ 2 := by
      rw [Nat.card_congr (Subgroup.equivMapOfInjective (P : Subgroup C) C.subtype
        C.subtype_injective).toEquiv]
      change Nat.card (P' : Set Y) ≤ 2
      calc Nat.card (P' : Set Y) = (P' : Set Y).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, (eQ (a 2) : Y)} : Set Y).ncard :=
          Set.ncard_le_ncard hP'sub (Set.toFinite _)
        _ ≤ ({(eQ (a 2) : Y)} : Set Y).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    have hcyc : IsCyclic P := by
      have hpos : 0 < Nat.card P := Nat.card_pos
      rcases Nat.lt_or_ge (Nat.card P) 2 with h | h
      · have h1 : Nat.card P = 1 := by omega
        have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp h1).1
        infer_instance
      · have h2 : Nat.card P = 2 := by omega
        have : Fact (Nat.Prime (Nat.card P)) := ⟨by rw [h2]; exact Nat.prime_two⟩
        exact isCyclic_of_prime_card (p := Nat.card P) rfl
    obtain ⟨hcard, -, -, ⟨-, hKodd, -, -⟩, hKchar⟩ := cyclic_sylow_normal_odd_complement P hcyc
    have : (pPrimeCore 2 C).Characteristic := hKchar
    have hKY : ((pPrimeCore 2 C).map C.subtype).Normal := inferInstance
    have hKodd' : Odd (Nat.card ((pPrimeCore 2 C).map C.subtype)) := by
      rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hKodd
    have hKbot : pPrimeCore 2 C = ⊥ := by
      have h1 : (pPrimeCore 2 C).map C.subtype ≤ oddCore Y := le_sSup ⟨hKY, hKodd'⟩
      rw [hO, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h1
    rw [hKbot, Subgroup.card_bot] at hcard
    have hdvd : Nat.card P ∣ Nat.card C := Subgroup.card_subgroup_dvd_card _
    have : Nat.card C = Nat.card P := by
      obtain ⟨m, hm⟩ := hdvd
      rw [hm, Nat.mul_div_cancel_left _ Nat.card_pos] at hcard
      rw [hm, ← hcard, mul_one]
    omega
  let θ : Y →* MulAut Q := MulAut.conjNormal
  have hker : θ.ker = C := by
    ext y
    simp only [MonoidHom.mem_ker, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro h q hq
      have := congrArg (fun m : MulAut Q => ((m ⟨q, hq⟩ : Q) : Y)) h
      change y * q * y⁻¹ = q at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · intro h
      refine MulEquiv.ext fun q => Subtype.ext ?_
      change y * (q : Y) * y⁻¹ = q
      rw [mul_inv_eq_iff_eq_mul]
      exact (h q q.2).symm
  have hAut : Nat.card (MulAut Q) ≤ 24 := by
    rw [← Nat.card_congr (MulAut.congr eQ).toEquiv]
    exact q8_natCard_mulEquiv_le
  have hrange : Nat.card θ.range ≤ 24 :=
    (Nat.card_le_card_of_injective _ θ.range.subtype_injective).trans hAut
  have := Subgroup.card_ker_mul_card_range θ
  rw [hker] at this
  nlinarith [Nat.card_pos (α := Y)]

private theorem natCard_sylow_eq {Y : Type*} [Group Y] [Finite Y] {r : ℕ} (hr : 3 ≤ r)
    (T : Sylow 2 Y) (hT : Nonempty ((T : Subgroup Y) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Nat.card (T : Subgroup Y) = 2 ^ r := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have : r = (r - 2) + 2 := by omega
  rw [this, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem solvable_quaternion_of_normal_sl2 {Y : Type u} [Group Y] [Finite Y] (hO : oddCore Y = ⊥)
    {r : ℕ} (hr : 3 ≤ r)
    (hT : ∀ T : Sylow 2 Y, Nonempty ((T : Subgroup Y) ≃* QuaternionGroup (2 ^ (r - 2))))
    (M : Subgroup Y) [M.Normal] (eM : M ≃* SL(2, ZMod 3)) :
    (r = 3 ∧ Nonempty (Y ≃* SL(2, ZMod 3))) ∨
      (r = 4 ∧ Nat.card Y = 48 ∧
        ∃ J : Subgroup Y, J.Normal ∧ J.index = 2 ∧ Nonempty (J ≃* SL(2, ZMod 3))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := nonempty_mulEquiv_sl2ThreeQ
  let QM : Subgroup M := sl2ThreeQ.map eM.symm.toMonoidHom
  have hQMn : QM.Normal :=
    Subgroup.Normal.map sl2ThreeQ_normal eM.symm.toMonoidHom eM.symm.surjective
  have hcardQM : Nat.card QM = 8 := by
    have h : Nat.card QM = Nat.card sl2ThreeQ :=
      (Nat.card_congr (MulEquiv.subgroupMap eM.symm sl2ThreeQ).toEquiv).symm
    rw [h, natCard_sl2ThreeQ]
  have hcardM : Nat.card M = 24 := by rw [Nat.card_congr eM.toEquiv, natCard_sl2Three]
  have hQM2 : IsPGroup 2 QM := IsPGroup.of_card (n := 3) (by rw [hcardQM]; norm_num)
  have hindexQM : QM.index = 3 := by
    have h := Subgroup.card_mul_index QM
    rw [hcardQM, hcardM] at h
    omega
  let P : Sylow 2 M := hQM2.toSylow (by rw [hindexQM]; norm_num)
  have hPchar : (P : Subgroup M).Characteristic := P.characteristic_of_normal hQMn
  let Q : Subgroup Y := (P : Subgroup M).map M.subtype
  have hQn : Q.Normal := inferInstance
  let eQ : QuaternionGroup 2 ≃* Q :=
    (e1.trans (MulEquiv.subgroupMap eM.symm sl2ThreeQ)).trans
      (Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective)
  have hle : Nat.card Y ≤ 48 := natCard_le_forty_eight_of_normal_q8 hO hT Q eQ
  have hidx := Subgroup.card_mul_index M
  rw [hcardM] at hidx
  have hpos : 0 < M.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨T⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hTcard := natCard_sylow_eq hr T (hT T)
  have hTidx := Subgroup.card_mul_index (T : Subgroup Y)
  have hTodd : ¬ 2 ∣ (T : Subgroup Y).index := T.not_dvd_index
  have hr5 : r < 5 := by
    by_contra h
    push Not at h
    have h1 : 2 ^ 5 ∣ Nat.card Y :=
      (pow_dvd_pow 2 h).trans ⟨(T : Subgroup Y).index, by rw [← hTcard, hTidx]⟩
    have h2 : 32 ∣ Nat.card Y := by simpa using h1
    omega
  have hM12 : M.index = 1 ∨ M.index = 2 := by omega
  rcases hM12 with h1 | h2
  ·
    have hMtop : M = ⊤ := Subgroup.index_eq_one.mp h1
    have hY24 : Nat.card Y = 24 := by omega
    have hr3 : r = 3 := by
      interval_cases r
      · rfl
      · exfalso
        rw [hTcard] at hTidx
        have : 2 ∣ (T : Subgroup Y).index := ⟨(T : Subgroup Y).index / 2, by omega⟩
        exact hTodd this
    refine Or.inl ⟨hr3, ⟨?_⟩⟩
    subst hMtop
    exact Subgroup.topEquiv.symm.trans eM
  ·
    have hY48 : Nat.card Y = 48 := by omega
    have hr4 : r = 4 := by
      interval_cases r
      · exfalso
        rw [hTcard] at hTidx
        omega
      · rfl
    exact Or.inr ⟨hr4, hY48, M, inferInstance, h2, ⟨eM⟩⟩

theorem solvable_quaternion_oddCore_quotient {X : Type u} [Group X] [Finite X]
    [Group.IsSolvable X] (S : Sylow 2 X) {r : ℕ} (hr : 3 ≤ r)
    (hS : Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Nonempty ((X ⧸ oddCore X) ≃* QuaternionGroup (2 ^ (r - 2))) ∨
      (r = 3 ∧ Nonempty ((X ⧸ oddCore X) ≃* SL(2, ZMod 3))) ∨
      (r = 4 ∧ Nat.card (X ⧸ oddCore X) = 48 ∧
        ∃ J : Subgroup (X ⧸ oddCore X), J.Normal ∧ J.index = 2 ∧
          Nonempty (J ≃* SL(2, ZMod 3))) := by
  obtain ⟨e⟩ := hS
  have hYs : Group.IsSolvable (X ⧸ oddCore X) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (oddCore X))
  have hYO : oddCore (X ⧸ oddCore X) = ⊥ := QuaternionStructure.oddCore_quotient_oddCore_eq_bot X
  have hT : ∀ T : Sylow 2 (X ⧸ oddCore X),
      Nonempty ((T : Subgroup (X ⧸ oddCore X)) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    fun T => QuaternionStructure.sylow_oddCore_quotient_quaternion S e T
  obtain ⟨z, -, -, -, hcases⟩ := quaternion_sylow_structure S ⟨r, hr, ⟨e⟩⟩
  rcases hcases with h2 | ⟨F, _, _, hF, L, hLn, -, ⟨eL⟩⟩ |
      ⟨F, _, _, hF, L, hLn, -, -, -, M, hMn, -, ⟨eM⟩⟩ | ⟨hqs, -, -⟩
  ·
    refine Or.inl ?_
    obtain ⟨f⟩ := QuaternionStructure.nonempty_mulEquiv_sylow_of_isPGroup_oddCore_quotient h2 S
    exact ⟨f.trans e⟩
  ·
    have hodd : Odd (Nat.card F) := QuaternionStructure.odd_natCard_of_ringChar_ne_two F hF
    have hLs : Group.IsSolvable SL(2, F) :=
      Group.isSolvable_of_isSolvable_injective (f := eL.symm.toMonoidHom) eL.symm.injective
    obtain ⟨f⟩ := nonempty_mulEquiv_sl2Three_of_isSolvable hodd hLs
    exact Or.inr (solvable_quaternion_of_normal_sl2 hYO hr hT L (eL.trans f))
  · have hodd : Odd (Nat.card F) := QuaternionStructure.odd_natCard_of_ringChar_ne_two F hF
    have hMs : Group.IsSolvable SL(2, F) :=
      Group.isSolvable_of_isSolvable_injective (f := eM.symm.toMonoidHom) eM.symm.injective
    obtain ⟨f⟩ := nonempty_mulEquiv_sl2Three_of_isSolvable hodd hMs
    exact Or.inr (solvable_quaternion_of_normal_sl2 hYO hr hT M (eM.trans f))
  ·
    exfalso
    obtain ⟨hperf, hsimple⟩ := hqs
    have hnt : Nontrivial (X ⧸ oddCore X) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (X ⧸ oddCore X))).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (X ⧸ oddCore X)).ne hperf

theorem solvable_quaternion_classification {X : Type u} [Group X] [Finite X]
    [Group.IsSolvable X] (hO : oddCore X = ⊥) (S : Sylow 2 X) {r : ℕ} (hr : 3 ≤ r)
    (hS : Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    Nonempty (X ≃* QuaternionGroup (2 ^ (r - 2))) ∨
      (r = 3 ∧ Nonempty (X ≃* SL(2, ZMod 3))) ∨
      (r = 4 ∧ Nat.card X = 48 ∧
        ∃ J : Subgroup X, J.Normal ∧ J.index = 2 ∧ Nonempty (J ≃* SL(2, ZMod 3))) := by
  have hinj : Function.Injective (QuotientGroup.mk' (oddCore X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  let π : X ≃* X ⧸ oddCore X :=
    MulEquiv.ofBijective (QuotientGroup.mk' (oddCore X)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  rcases solvable_quaternion_oddCore_quotient S hr hS with
    h | ⟨h3, h⟩ | ⟨h4, hcard, J, hJn, hJi, ⟨eJ⟩⟩
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨π.trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨h3, ⟨π.trans e⟩⟩)
  · refine Or.inr (Or.inr ⟨h4, ?_, J.map π.symm.toMonoidHom, ?_, ?_, ?_⟩)
    · rw [Nat.card_congr π.toEquiv]; exact hcard
    · exact Subgroup.Normal.map hJn _ π.symm.surjective
    · exact (Subgroup.index_map_equiv J π.symm).trans hJi
    · exact ⟨(MulEquiv.subgroupMap π.symm J).symm.trans eJ⟩

end CFSG.ClassicalInvolution

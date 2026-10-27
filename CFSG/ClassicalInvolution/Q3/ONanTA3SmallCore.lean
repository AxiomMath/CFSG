module

public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def NoOddNormalAt (t : Y) : Prop :=
  ∀ o ∈ Subgroup.centralizer ({t} : Set Y), o ≠ 1 → Odd (orderOf o) →
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), Even (orderOf (o * (c * o * c⁻¹)))

theorem odd_orderOf_of_mem_oddCoreImg {H : Subgroup Y} {o : Y} (ho : o ∈ oddCoreImg H) :
    Odd (orderOf o) := by
  have h1 : orderOf (⟨o, ho⟩ : oddCoreImg H) ∣ Nat.card (oddCoreImg H) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact (odd_natCard_oddCoreImg H).of_dvd_nat h1

theorem oddCoreImg_eq_bot {t : Y} (hno : NoOddNormalAt t) {H : Subgroup Y}
    (hH : H ≤ Subgroup.centralizer ({t} : Set Y))
    (hnorm : Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (H : Set Y)) :
    oddCoreImg H = ⊥ := by
  rw [eq_bot_iff]
  intro o ho
  by_contra hne
  have hne' : o ≠ 1 := by simpa using hne
  obtain ⟨c, hc, hev⟩ := hno o (hH (oddCoreImg_le H ho)) hne' (odd_orderOf_of_mem_oddCoreImg ho)
  have hco : c * o * c⁻¹ ∈ oddCoreImg H := conj_mem_oddCoreImg (hnorm hc) ho
  have hprod : o * (c * o * c⁻¹) ∈ oddCoreImg H := Subgroup.mul_mem _ ho hco
  exact (Nat.not_even_iff_odd.mpr (odd_orderOf_of_mem_oddCoreImg hprod)) hev

@[expose] def q8List (t a b : Y) : List Y := [1, a, t, t * a, b, b * a, b * t, b * (t * a)]

theorem q8_eq_of_sq_eq_one {w : QuaternionGroup 2} (h1 : w * w = 1) (h2 : w ≠ 1) :
    w = QuaternionGroup.a 2 := by
  revert w
  decide +kernel

theorem q8_cases (w : QuaternionGroup 2) :
    w = QuaternionGroup.a 0 ∨ w = QuaternionGroup.a 1 ∨ w = QuaternionGroup.a 2 ∨
      w = QuaternionGroup.a 3 ∨ w = QuaternionGroup.xa 0 ∨ w = QuaternionGroup.xa 1 ∨
      w = QuaternionGroup.xa 2 ∨ w = QuaternionGroup.xa 3 := by
  revert w
  decide +kernel

omit [Finite Y] in
theorem datum_shape_of_odd {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hOb : oddCoreImg R = ⊥) :
    oddCoreImg R = ⊥ ∧ IsPGroup 2 R ∧ ∃ a b : Y, a ∈ R ∧ b ∈ R ∧ a * a = t ∧ b * b = t ∧
      b * a = t * a * b ∧ ∀ r ∈ R, r ∈ q8List t a b := by
  obtain ⟨e⟩ := hq
  refine ⟨hOb, ?_⟩
  have hcore : classicalInvolutionOddCore R = ⊥ := by
    have h : (oddCore R).map R.subtype = ⊥ := hOb
    exact (Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp h
  have hP : IsPGroup 2 R := by
    have e' : R ⧸ classicalInvolutionOddCore R ≃* R :=
      (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
    exact hd.twoGroup.of_equiv e'
  refine ⟨hP, ?_⟩
  have hS : (⊤ : Subgroup R) = (S : Subgroup R) :=
    S.is_maximal' (hP.of_equiv Subgroup.topEquiv.symm) le_top
  let ι : (S : Subgroup R) →* Y := R.subtype.comp (S : Subgroup R).subtype
  have hιinj : Function.Injective ι :=
    R.subtype_injective.comp (S : Subgroup R).subtype_injective
  have hι : ∀ s : (S : Subgroup R), ι s = ((s : R) : Y) := fun s => rfl
  obtain ⟨i, hi⟩ : ∃ i : (S : Subgroup R), i = e.symm (QuaternionGroup.a 1) := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : (S : Subgroup R), j = e.symm (QuaternionGroup.xa 0) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : (S : Subgroup R), z = e.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  have hii : i * i = z := by
    rw [hi, hz, ← map_mul]
    congr 1
  have hjj : j * j = z := by
    rw [hj, hz, ← map_mul]
    congr 1
  have hji : j * i = z * i * j := by
    rw [hj, hi, hz, ← map_mul, ← map_mul, ← map_mul]
    congr 1
  have hzt : t = ι z := by
    obtain ⟨s, hs, hst⟩ := hd.mem
    have ht2 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [hd.order, pow_two] at this
    have ht1 : t ≠ 1 := fun h => by
      have := hd.order
      rw [h, orderOf_one] at this
      omega
    set s' : (S : Subgroup R) := ⟨s, hs⟩ with hs'
    have hts : ι s' = t := hst
    have hs2 : s' * s' = 1 := by
      apply hιinj
      rw [map_mul, hts, ht2, map_one]
    have hs1 : s' ≠ 1 := fun h => ht1 (by rw [← hts, h, map_one])
    have hw := q8_eq_of_sq_eq_one (w := e s') (by rw [← map_mul, hs2, map_one])
      (fun h => hs1 (e.injective (by rw [h, map_one])))
    have : s' = z := by
      rw [hz, ← hw, MulEquiv.symm_apply_apply]
    rw [← hts, this]
  refine ⟨ι i, ι j, (i : R).2, (j : R).2, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hii, ← hzt]
  · rw [← map_mul, hjj, ← hzt]
  · rw [hzt]
    simp only [← map_mul]
    exact congrArg ι hji
  · intro r hr
    have hrS : (⟨r, hr⟩ : R) ∈ (S : Subgroup R) := hS ▸ Subgroup.mem_top _
    set s : (S : Subgroup R) := ⟨⟨r, hr⟩, hrS⟩ with hs
    have hrs : r = ι s := rfl
    have hsw : s = e.symm (e s) := (MulEquiv.symm_apply_apply e s).symm
    rcases q8_cases (e s) with h | h | h | h | h | h | h | h
    · have : s = 1 := by rw [hsw, h, ← QuaternionGroup.one_def, map_one]
      rw [hrs, this, map_one]
      simp [q8List]
    · have : s = i := by rw [hsw, h, hi]
      rw [hrs, this]
      simp [q8List]
    · have : s = z := by rw [hsw, h, hz]
      rw [hrs, this, ← hzt]
      simp [q8List]
    · have : s = z * i := by
        rw [hsw, h, hz, hi, ← map_mul]
        congr 1
      rw [hrs, this, map_mul, ← hzt]
      simp [q8List]
    · have : s = j := by rw [hsw, h, hj]
      rw [hrs, this]
      simp [q8List]
    · have : s = j * i := by
        rw [hsw, h, hj, hi, ← map_mul]
        congr 1
      rw [hrs, this, map_mul]
      simp [q8List]
    · have : s = j * z := by
        rw [hsw, h, hj, hz, ← map_mul]
        congr 1
      rw [hrs, this, map_mul, ← hzt]
      simp [q8List]
    · have : s = j * (z * i) := by
        rw [hsw, h, hj, hz, hi, ← map_mul, ← map_mul]
        congr 1
      rw [hrs, this, map_mul, map_mul, ← hzt]
      simp [q8List]

theorem datum_shape {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hno : NoOddNormalAt t) :
    oddCoreImg R = ⊥ ∧ IsPGroup 2 R ∧ ∃ a b : Y, a ∈ R ∧ b ∈ R ∧ a * a = t ∧ b * b = t ∧
      b * a = t * a * b ∧ ∀ r ∈ R, r ∈ q8List t a b :=
  datum_shape_of_odd hd hq (oddCoreImg_eq_bot hno hd.cent hd.le_normalizer)

omit [Finite Y] in
theorem good_of_witness {R : Subgroup Y} {t a b : Y} (hOR : oddCoreImg R = ⊥)
    (hOC : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥) (ha : a ∈ R) (hb : b ∈ R)
    {x : Y} (hx : x ∈ Subgroup.centralizer ({t} : Set Y)) (hx3 : x ^ 3 = 1)
    (hmove : ¬ (x * a = a * x ∧ x * b = b * x))
    (hcomm : ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y →
      x * y = y * x) : GoodThreeElement R t := by
  have hcom : ∀ y r, r ∈ R → ⁅y, r⁆ ∈ oddCoreImg R → y * r = r * y := fun y r _ h => by
    rw [hOR, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  refine ⟨x, 1, hx, by simpa using hx3, ?_, ?_⟩
  · by_cases hxa : x * a = a * x
    · have hxb : ¬ x * b = b * x := fun h => hmove ⟨hxa, h⟩
      refine ⟨b, hb, fun h => hxb (hcom x b hb h)⟩
    · exact ⟨a, ha, fun h => hxa (hcom x a ha h)⟩
  · intro y hy hyR
    rw [hOC, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm y hy (hcom y a ha (hyR a ha)) (hcom y b hb (hyR b hb))

@[expose] def GoodPred (t : Y) : Prop :=
  NoOddNormalAt t ∧
    ∀ a b : Y, a * a = t → b * b = t → b * a = t * a * b →
      (∀ c ∈ Subgroup.centralizer ({t} : Set Y),
        c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b) →
      ∃ x ∈ Subgroup.centralizer ({t} : Set Y), x ^ 3 = 1 ∧ ¬ (x * a = a * x ∧ x * b = b * x) ∧
        ∀ y ∈ Subgroup.centralizer ({t} : Set Y), y * a = a * y → y * b = b * y →
          x * y = y * x

theorem good_of_goodPred {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hP : GoodPred t) :
    GoodThreeElement R t := by
  obtain ⟨hOR, -, a, b, ha, hb, haa, hbb, hba, hlist⟩ := datum_shape hd hq hP.1
  have hOC : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    oddCoreImg_eq_bot hP.1 le_rfl fun g hg => Subgroup.le_normalizer hg
  have hnorm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      c * a * c⁻¹ ∈ q8List t a b ∧ c * b * c⁻¹ ∈ q8List t a b := fun c hc =>
    ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) a).mp ha),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hc) b).mp hb)⟩
  obtain ⟨x, hx, hx3, hmove, hcomm⟩ := hP.2 a b haa hbb hba hnorm
  exact good_of_witness hOR hOC ha hb hx hx3 hmove hcomm

end CFSG.ClassicalInvolution.Q3.TA3

module

public import Certificates.Data.Kernel.LocalQT.Sec
public import CFSG.Certificates.Kernel.LocalQT.Steps
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.LocalQTSecLemmas
import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.KC.LQT

open CFSG.Blueprint CFSG.Open CFSG.KS.Ord CFSG.SectionRank
open scoped commutatorElement

theorem elem_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P O W : ℕ → ℕ} {N r : ℕ}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (he : elemOK c V N O W r = true) :
    ∃ E : Subgroup (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ,
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  have hv := SecS.vals_sound c hc hA hB h1 hs
  unfold elemOK at he
  obtain ⟨hO, he⟩ := SecS.andT he
  obtain ⟨hcube, he⟩ := SecS.andT he
  obtain ⟨hcomm, hker⟩ := SecS.andT he
  have hO' := SecS.allLt_spec hO
  have hX : ∀ i < r, CFSG.KS.Ord.Canon c.p c.d c.w (V (O i)) ∧
      CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O i)) ∈
        NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB) :=
    fun i hi => hv _ (Nat.blt_eq.mp (hO' i hi))
  have key : ∀ i j : Fin r, (j : ℕ) < i →
      CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O i)) * CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O j)) =
        CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O j)) *
          CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O i)) := by
    intro i j hji
    have h := Nat.eq_of_beq_eq_true (SecS.allLt_spec (SecS.allLt_spec hcomm i i.isLt) j hji)
    have hXi := (hX i i.isLt).1
    have hXj := (hX j j.isLt).1
    have h2 := congrArg (CFSG.KS.Ord.ordMat c.p c.d c.w c.S) h
    rwa [(SecS.mul_sound c hc hXi hXj).2, (SecS.mul_sound c hc hXj hXi).2] at h2
  refine CFSG.SectionRank.exists_elemAbelian_units _
    (fun i : Fin r => CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O i)))
    (fun i => (hX i i.isLt).2) (fun i => ?_) (fun i j => ?_) (fun a ha => ?_)
  · have hXi := (hX i i.isLt).1
    have h3 := Nat.eq_of_beq_eq_true (SecS.allLt_spec hcube i i.isLt)
    obtain ⟨cXX, eXX⟩ := SecS.mul_sound c hc hXi hXi
    obtain ⟨-, eXXX⟩ := SecS.mul_sound c hc cXX hXi
    have h4 := congrArg (CFSG.KS.Ord.ordMat c.p c.d c.w c.S) h3
    rw [eXXX, eXX, (CFSG.KS.Ord.one_sound hc).2] at h4
    change CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O i)) ^ 3 = 1
    rw [pow_three']
    exact h4
  · rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
    · exact (key j i hij).symm
    · rw [Fin.ext hij]
    · exact key i j hij
  · intro hone
    have hone' : (List.ofFn fun q : Fin r =>
        CFSG.KS.Ord.ordMat c.p c.d c.w c.S (V (O q)) ^ (a q : ℕ)).prod = 1 := hone
    have hlt := CFSG.SectionRank.enc_lt r a
    have hpos : CFSG.SectionRank.enc r a ≠ 0 :=
      fun h0 => ha (CFSG.SectionRank.eq_zero_of_enc_eq_zero r a h0)
    have hk := SecS.allLt_spec hker (CFSG.SectionRank.enc r a - 1) (by
      change _ < 3 ^ r - 1
      omega)
    simp only [SecS.strictB_eq] at hk
    have e : Nat.succ (CFSG.SectionRank.enc r a - 1) = CFSG.SectionRank.enc r a := by omega
    rw [e] at hk
    obtain ⟨ht, hne⟩ := SecS.andT hk
    have hu := SecS.unit_canon c hc (Nat.blt_eq.mp ht)
    obtain ⟨hD, hDv⟩ := SecS.digApp_spec c hc (fun i => V (O i)) r 0
      (fun q hq => (hX (0 + q) (by omega)).1) a hu
    simp only [Nat.zero_add] at hDv
    rw [hone', Matrix.vecMul_one] at hDv
    exact SecS.ne_of_notB hne (SecS.vec_inj (SecS.lay_w_pos c hc) hD hu hDv)

theorem sq_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P : ℕ → ℕ}
    {N ix iy ih r oh a b cc dd t : ℕ} {σ : List ℕ}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hq : sqOK c V N ix iy ih r oh a b cc dd t σ = true) :
    ∃ x y g : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ,
      x ^ r = 1 ∧ y ^ r = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set _)) = r ^ 2 ∧
      g * x * g⁻¹ = x ^ a * y ^ cc ∧ g * y * g⁻¹ = x ^ b * y ^ dd := by
  set S := NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB)
  have hv := SecS.vals_sound c hc hA hB h1 hs
  unfold sqOK at hq
  obtain ⟨hix, hq⟩ := SecS.andT hq
  obtain ⟨hiy, hq⟩ := SecS.andT hq
  obtain ⟨hih, hq⟩ := SecS.andT hq
  obtain ⟨hr, hq⟩ := SecS.andT hq
  obtain ⟨hoh, hq⟩ := SecS.andT hq
  obtain ⟨hXr, hq⟩ := SecS.andT hq
  obtain ⟨hYr, hq⟩ := SecS.andT hq
  obtain ⟨hHo, hq⟩ := SecS.andT hq
  obtain ⟨hXY, hq⟩ := SecS.andT hq
  obtain ⟨hHX, hq⟩ := SecS.andT hq
  obtain ⟨hHY, hnf⟩ := SecS.andT hq
  obtain ⟨cX, mX⟩ := hv _ (Nat.blt_eq.mp hix)
  obtain ⟨cY, mY⟩ := hv _ (Nat.blt_eq.mp hiy)
  obtain ⟨cH, mH⟩ := hv _ (Nat.blt_eq.mp hih)
  have hr' : 0 < r := Nat.blt_eq.mp hr
  have hoh' : 0 < oh := Nat.blt_eq.mp hoh
  have eX := SecS.pow_one_of c hc cX hXr
  have eY := SecS.pow_one_of c hc cY hYr
  have eH := SecS.pow_one_of c hc cH hHo
  let x := LocalWitness.unitOf S mX hr'.ne' eX
  let y := LocalWitness.unitOf S mY hr'.ne' eY
  let g := LocalWitness.unitOf S mH hoh'.ne' eH
  have fx : LocalWitness.valHom S x = ordMat c.p c.d c.w c.S (V ix) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fy : LocalWitness.valHom S y = ordMat c.p c.d c.w c.S (V iy) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fg : LocalWitness.valHom S g = ordMat c.p c.d c.w c.S (V ih) :=
    LocalWitness.valHom_unitOf S _ _ _
  have hx : x ^ r = 1 := LocalWitness.unitOf_pow S mX _ eX
  have hy : y ^ r = 1 := LocalWitness.unitOf_pow S mY _ eY
  have hxy : x * y = y * x := LocalWitness.valHom_injective S (by
    rw [map_mul, map_mul, fx, fy]
    exact SecS.mul_eq_of c hc cX cY cY cX hXY)
  have word : ∀ i j : ℕ, Canon c.p c.d c.w (c.mul (c.pow (V ix) i) (c.pow (V iy) j)) ∧
      LocalWitness.valHom S (x ^ i * y ^ j) =
        ordMat c.p c.d c.w c.S (c.mul (c.pow (V ix) i) (c.pow (V iy) j)) := by
    intro i j
    obtain ⟨d1, g1⟩ := SecS.pow_sound c hc cX i
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc cY j
    obtain ⟨d3, g3⟩ := SecS.mul_sound c hc d1 d2
    exact ⟨d3, by rw [map_mul, map_pow, map_pow, fx, fy, g3, g1, g2]⟩
  have conj : ∀ {w u : Sˣ} {W U : ℕ}, Canon c.p c.d c.w W →
      LocalWitness.valHom S w = ordMat c.p c.d c.w c.S W → Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U → conjOK c (V ih) U W = true →
      g * u * g⁻¹ = w := by
    intro w u W U cW fw cU fu hcj
    rw [mul_inv_eq_iff_eq_mul]
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fg, fu, fw]
    exact SecS.conj_mat c hc cH cU cW hcj
  refine ⟨x, y, g, hx, hy, hxy, ?_, conj (word a cc).1 (word a cc).2 cX fx hHX,
    conj (word b dd).1 (word b dd).2 cY fy hHY⟩
  refine LocalWitness.card_closure_eq_sq hr' hx hy hxy ?_
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij
  have hm := congrArg (LocalWitness.valHom S) hij
  simp only [map_mul, map_pow, fx, fy] at hm
  obtain ⟨e1, e2⟩ := SecS.normal2_inj c hc cX cY hr' hnf i.isLt j.isLt i'.isLt j'.isLt hm
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

theorem cub_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P : ℕ → ℕ}
    {N ix iy ih r oh a b cc dd k l μ t : ℕ} {σ : List ℕ}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N)
    (hq : cubOK c V N ix iy ih r oh a b cc dd k l μ t σ = true) :
    ∃ x y g : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ,
      x ^ r = 1 ∧ y ^ r = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set _)) = r ^ 3 ∧
      g * x * g⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k ∧
      g * y * g⁻¹ = x ^ cc * y ^ dd * ⁅x, y⁆ ^ l ∧ g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ μ := by
  set S := NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB)
  have hv := SecS.vals_sound c hc hA hB h1 hs
  unfold cubOK at hq
  obtain ⟨hix, hq⟩ := SecS.andT hq
  obtain ⟨hiy, hq⟩ := SecS.andT hq
  obtain ⟨hih, hq⟩ := SecS.andT hq
  obtain ⟨hr, hq⟩ := SecS.andT hq
  obtain ⟨hoh, hq⟩ := SecS.andT hq
  obtain ⟨hXr, hq⟩ := SecS.andT hq
  obtain ⟨hYr, hq⟩ := SecS.andT hq
  obtain ⟨hHo, hq⟩ := SecS.andT hq
  rw [SecS.strictB_eq] at hq
  obtain ⟨hZt, hq⟩ := SecS.andT hq
  obtain ⟨hZX, hq⟩ := SecS.andT hq
  obtain ⟨hZY, hq⟩ := SecS.andT hq
  obtain ⟨hHX, hq⟩ := SecS.andT hq
  obtain ⟨hHY, hq⟩ := SecS.andT hq
  obtain ⟨hHZ, hnf⟩ := SecS.andT hq
  have ht : t < c.d := Nat.blt_eq.mp (SecS.andT hnf).1
  obtain ⟨cX, mX⟩ := hv _ (Nat.blt_eq.mp hix)
  obtain ⟨cY, mY⟩ := hv _ (Nat.blt_eq.mp hiy)
  obtain ⟨cH, mH⟩ := hv _ (Nat.blt_eq.mp hih)
  have hr' : 0 < r := Nat.blt_eq.mp hr
  have hoh' : 0 < oh := Nat.blt_eq.mp hoh
  have eX := SecS.pow_one_of c hc cX hXr
  have eY := SecS.pow_one_of c hc cY hYr
  have eH := SecS.pow_one_of c hc cH hHo
  let x := LocalWitness.unitOf S mX hr'.ne' eX
  let y := LocalWitness.unitOf S mY hr'.ne' eY
  let g := LocalWitness.unitOf S mH hoh'.ne' eH
  have fx : LocalWitness.valHom S x = ordMat c.p c.d c.w c.S (V ix) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fy : LocalWitness.valHom S y = ordMat c.p c.d c.w c.S (V iy) :=
    LocalWitness.valHom_unitOf S _ _ _
  have fg : LocalWitness.valHom S g = ordMat c.p c.d c.w c.S (V ih) :=
    LocalWitness.valHom_unitOf S _ _ _
  have hx : x ^ r = 1 := LocalWitness.unitOf_pow S mX _ eX
  have hy : y ^ r = 1 := LocalWitness.unitOf_pow S mY _ eY
  have hZ : Canon c.p c.d c.w (commM c r (V ix) (V iy)) ∧
      LocalWitness.valHom S ⁅x, y⁆ = ordMat c.p c.d c.w c.S (commM c r (V ix) (V iy)) := by
    obtain ⟨d1, g1⟩ := SecS.mul_sound c hc cX cY
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc cX (r - 1)
    obtain ⟨d3, g3⟩ := SecS.pow_sound c hc cY (r - 1)
    obtain ⟨d4, g4⟩ := SecS.mul_sound c hc d1 d2
    obtain ⟨d5, g5⟩ := SecS.mul_sound c hc d4 d3
    refine ⟨d5, ?_⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul,
      LocalWitness.valHom_inv_of_pow S hr'.ne' hx, LocalWitness.valHom_inv_of_pow S hr'.ne' hy,
      fx, fy]
    change _ = ordMat c.p c.d c.w c.S
      (c.mul (c.mul (c.mul (V ix) (V iy)) (c.pow (V ix) (r - 1))) (c.pow (V iy) (r - 1)))
    rw [g5, g4, g1, g2, g3]
  obtain ⟨cZ, fz⟩ := hZ
  have comm : ∀ {u : Sˣ} {U : ℕ}, Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U →
      Nat.beq (c.mul (commM c r (V ix) (V iy)) U) (c.mul U (commM c r (V ix) (V iy))) = true →
      Commute ⁅x, y⁆ u := by
    intro u U cU fu hcm
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fz, fu]
    exact SecS.mul_eq_of c hc cZ cU cU cZ hcm
  have conj : ∀ {w u : Sˣ} {W U : ℕ}, Canon c.p c.d c.w W →
      LocalWitness.valHom S w = ordMat c.p c.d c.w c.S W → Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U → conjOK c (V ih) U W = true →
      g * u * g⁻¹ = w := by
    intro w u W U cW fw cU fu hcj
    rw [mul_inv_eq_iff_eq_mul]
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fg, fu, fw]
    exact SecS.conj_mat c hc cH cU cW hcj
  have word : ∀ i j k : ℕ, Canon c.p c.d c.w (c.mul (c.mul (c.pow (V ix) i) (c.pow (V iy) j))
      (c.pow (commM c r (V ix) (V iy)) k)) ∧
      LocalWitness.valHom S (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = ordMat c.p c.d c.w c.S
        (c.mul (c.mul (c.pow (V ix) i) (c.pow (V iy) j)) (c.pow (commM c r (V ix) (V iy)) k)) := by
    intro i j k
    obtain ⟨d1, g1⟩ := SecS.pow_sound c hc cX i
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc cY j
    obtain ⟨d3, g3⟩ := SecS.pow_sound c hc cZ k
    obtain ⟨d4, g4⟩ := SecS.mul_sound c hc d1 d2
    obtain ⟨d5, g5⟩ := SecS.mul_sound c hc d4 d3
    exact ⟨d5, by rw [map_mul, map_mul, map_pow, map_pow, map_pow, fx, fy, fz, g5, g4, g1, g2, g3]⟩
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro he
    apply SecS.mat_ne_one c hc ht cZ hZt
    rw [← fz, he, map_one]
  have hzx : Commute ⁅x, y⁆ x := comm cX fx hZX
  have hzy : Commute ⁅x, y⁆ y := comm cY fy hZY
  obtain ⟨cP, fP⟩ := SecS.pow_sound c hc cZ μ
  refine ⟨x, y, g, hx, hy, hz1, hzx, hzy, ?_, conj (word a b k).1 (word a b k).2 cX fx hHX,
    conj (word cc dd l).1 (word cc dd l).2 cY fy hHY,
    conj cP (by rw [map_pow, fz, fP]) cZ fz hHZ⟩
  refine LocalWitness.card_closure_eq_cube hr' hx hy hzx hzy ?_
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hijk
  have hm := congrArg (LocalWitness.valHom S) hijk
  simp only [map_mul, map_pow, fx, fy, fz] at hm
  obtain ⟨e1, e2, e3⟩ := SecS.normal3_inj c hc cX cY cZ hr' hnf i.isLt j.isLt k.isLt i'.isLt
    j'.isLt k'.isLt hm
  exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))

theorem loc_sound (c : Lay) (hc : c.ok = true) {LA LB : List Char} {V P I E PL CL : ℕ → ℕ}
    {N n t ok1 ok2 oh a b cc dd : ℕ} {σq σe : List ℕ}
    (hA : decOK c (V 0) LA = true) (hB : decOK c (V 1) LB = true) (h1 : V 2 = c.ONE)
    (hs : StepsTo (stepOK c V P) N) (hfac : n.factorization 3 = 2)
    (hq : locOK c V I E PL CL N n t ok1 ok2 oh a b cc dd σq σe = true) :
    ∃ (K : Subgroup (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ)
      (_ : Group.IsPerfect K) (Q : Sylow 3 K) (x y : K)
      (h k : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ),
      Nat.card K = n ∧ IsElemAbelian 3 (Q : Subgroup K) ∧
      Nat.card (Q : Subgroup K) = 3 ^ 2 ∧
      h ∈ Subgroup.normalizer
        (K : Set (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ) ∧
      Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ = (x : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA)
          (String.ofList LB))ˣ) ^ a *
        (y : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ) ^ cc ∧
      h * y * h⁻¹ = (x : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA)
          (String.ofList LB))ˣ) ^ b *
        (y : (NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB))ˣ) ^ dd ∧
      (∀ g ∈ K, Commute k g) ∧ orderOf k = 3 ∧ Subgroup.zpowers k ⊓ K = ⊥ := by
  classical
  set S := NativeSporadic.seedMonoid c.p c.d 1 (String.ofList LA) (String.ofList LB)
  have hv := SecS.vals_sound c hc hA hB h1 hs
  unfold locOK at hq
  obtain ⟨hI, hq⟩ := SecS.andT hq
  obtain ⟨hen, hq⟩ := SecS.andT hq
  obtain ⟨hse, hq⟩ := SecS.andT hq
  obtain ⟨hI2, hq⟩ := SecS.andT hq
  obtain ⟨q2, hq⟩ := SecS.andT hq
  obtain ⟨q3, hq⟩ := SecS.andT hq
  obtain ⟨q6, hq⟩ := SecS.andT hq
  obtain ⟨q7, hq⟩ := SecS.andT hq
  obtain ⟨q8, hq⟩ := SecS.andT hq
  obtain ⟨q9, hq⟩ := SecS.andT hq
  obtain ⟨ho1, hq⟩ := SecS.andT hq
  obtain ⟨ho2, hq⟩ := SecS.andT hq
  obtain ⟨hK1, hq⟩ := SecS.andT hq
  obtain ⟨hK2, hq⟩ := SecS.andT hq
  obtain ⟨hX3, hq⟩ := SecS.andT hq
  obtain ⟨hY3, hq⟩ := SecS.andT hq
  obtain ⟨hXY, hq⟩ := SecS.andT hq
  obtain ⟨hnf, hq⟩ := SecS.andT hq
  obtain ⟨hoh, hq⟩ := SecS.andT hq
  obtain ⟨hH, hq⟩ := SecS.andT hq
  obtain ⟨hHK1, hq⟩ := SecS.andT hq
  obtain ⟨hHK2, hq⟩ := SecS.andT hq
  obtain ⟨hHX, hq⟩ := SecS.andT hq
  obtain ⟨hHY, hq⟩ := SecS.andT hq
  obtain ⟨hC3, hq⟩ := SecS.andT hq
  obtain ⟨hCt, hq⟩ := SecS.andT hq
  obtain ⟨hCK1, hq⟩ := SecS.andT hq
  obtain ⟨hCK2, hq⟩ := SecS.andT hq
  obtain ⟨hCn, hq⟩ := SecS.andT hq
  obtain ⟨hC2n, hq⟩ := SecS.andT hq
  obtain ⟨hp1, hp2⟩ := SecS.andT hq
  have ht : t < c.d := Nat.blt_eq.mp (SecS.andT hnf).1
  have hIv : ∀ k < 10, Canon c.p c.d c.w (V (I k)) ∧ ordMat c.p c.d c.w c.S (V (I k)) ∈ S :=
    fun k hk => hv _ (Nat.blt_eq.mp (SecS.allLt_spec hI k hk))
  have hIn : ∀ k < 8, I (k + 10) < n := fun k hk => Nat.blt_eq.mp (SecS.allLt_spec hI2 k hk)
  have i10 : I 10 < n := hIn 0 (by norm_num)
  have i11 : I 11 < n := hIn 1 (by norm_num)
  have i12 : I 12 < n := hIn 2 (by norm_num)
  have i13 : I 13 < n := hIn 3 (by norm_num)
  have i14 : I 14 < n := hIn 4 (by norm_num)
  have i15 : I 15 < n := hIn 5 (by norm_num)
  have i16 : I 16 < n := hIn 6 (by norm_num)
  have i17 : I 17 < n := hIn 7 (by norm_num)
  obtain ⟨c0, m0⟩ := hIv 0 (by norm_num)
  obtain ⟨c1, m1⟩ := hIv 1 (by norm_num)
  obtain ⟨c2, -⟩ := hIv 2 (by norm_num)
  obtain ⟨c3, -⟩ := hIv 3 (by norm_num)
  obtain ⟨c4, m4⟩ := hIv 4 (by norm_num)
  obtain ⟨c5, m5⟩ := hIv 5 (by norm_num)
  have ho1' : 0 < ok1 := Nat.blt_eq.mp ho1
  have ho2' : 0 < ok2 := Nat.blt_eq.mp ho2
  have eK1 := SecS.pow_one_of c hc c0 hK1
  have eK2 := SecS.pow_one_of c hc c1 hK2
  let k1 := LocalWitness.unitOf S m0 ho1'.ne' eK1
  let k2 := LocalWitness.unitOf S m1 ho2'.ne' eK2
  have f1 : LocalWitness.valHom S k1 = ordMat c.p c.d c.w c.S (V (I 0)) :=
    LocalWitness.valHom_unitOf S _ _ _
  have f2 : LocalWitness.valHom S k2 = ordMat c.p c.d c.w c.S (V (I 1)) :=
    LocalWitness.valHom_unitOf S _ _ _
  set K := Subgroup.closure ({k1, k2} : Set Sˣ) with hKdef
  unfold enumOK at hen
  obtain ⟨hn0, hen⟩ := SecS.andT hen
  obtain ⟨hE0, hen⟩ := SecS.andT hen
  obtain ⟨htree, htab⟩ := SecS.andT hen
  have hn : 0 < n := Nat.blt_eq.mp hn0
  have hE : ∀ i < n, Canon c.p c.d c.w (V (E i)) ∧
      ∃ u ∈ K, LocalWitness.valHom S u = ordMat c.p c.d c.w c.S (V (E i)) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [Nat.eq_of_beq_eq_true hE0]
        obtain ⟨o1, o2⟩ := CFSG.KS.Ord.one_sound hc
        exact ⟨o1, 1, K.one_mem, by rw [map_one, o2]⟩
      · obtain ⟨i0, rfl⟩ : ∃ i0, i = Nat.succ i0 := ⟨i - 1, by omega⟩
        have htr := SecS.allLt_spec htree i0 (by change i0 < n - 1; omega)
        simp only [SecS.strictB_eq] at htr
        generalize Nat.land (PL (Nat.succ i0)) 1048575 = p at htr
        generalize Nat.shiftRight (PL (Nat.succ i0)) 20 = l at htr
        obtain ⟨hp, htr⟩ := SecS.andT htr
        obtain ⟨-, htr⟩ := SecS.andT htr
        have hp' := Nat.blt_eq.mp hp
        obtain ⟨cp, u, hu, fu⟩ := ih p hp' (by omega)
        have hgen : ∀ b : Bool, ∃ s ∈ K,
            Canon c.p c.d c.w (Bool.rec (motive := fun _ => ℕ) (V (I 1)) (V (I 0)) b) ∧
            LocalWitness.valHom S s =
              ordMat c.p c.d c.w c.S (Bool.rec (motive := fun _ => ℕ) (V (I 1)) (V (I 0)) b) := by
          intro b
          cases b
          · exact ⟨k2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), c1, f2⟩
          · exact ⟨k1, Subgroup.subset_closure (Set.mem_insert _ _), c0, f1⟩
        obtain ⟨s, hsK, cG, fs⟩ := hgen (Nat.beq l 0)
        obtain ⟨cm, em⟩ := SecS.mul_sound c hc cp cG
        rw [Nat.eq_of_beq_eq_true htr]
        exact ⟨cm, u * s, K.mul_mem hu hsK, by rw [map_mul, fu, fs, em]⟩
  have hEc : ∀ i < n, Canon c.p c.d c.w (V (E i)) := fun i hi => (hE i hi).1
  have hrt : ∀ i < n,
      (∃ j < n, ordMat c.p c.d c.w c.S (V (E i)) * ordMat c.p c.d c.w c.S (V (I 0)) =
        ordMat c.p c.d c.w c.S (V (E j))) ∧
      (∃ j < n, ordMat c.p c.d c.w c.S (V (E i)) * ordMat c.p c.d c.w c.S (V (I 1)) =
        ordMat c.p c.d c.w c.S (V (E j))) := by
    intro i hi
    obtain ⟨ha, hb⟩ := SecS.andT (SecS.allLt_spec htab i hi)
    rw [SecS.strictB_eq] at ha hb
    obtain ⟨ja, ha⟩ := SecS.andT ha
    obtain ⟨jb, hb⟩ := SecS.andT hb
    refine ⟨⟨_, Nat.blt_eq.mp ja, ?_⟩, ⟨_, Nat.blt_eq.mp jb, ?_⟩⟩
    · rw [← (SecS.mul_sound c hc (hEc i hi) c0).2]
      exact SecS.mat_of_beq c ha
    · rw [← (SecS.mul_sound c hc (hEc i hi) c1).2]
      exact SecS.mat_of_beq c hb
  have hpow : ∀ (s : Sˣ) (G : ℕ), LocalWitness.valHom S s = ordMat c.p c.d c.w c.S G →
      (∀ i < n, ∃ j < n, ordMat c.p c.d c.w c.S (V (E i)) * ordMat c.p c.d c.w c.S G =
        ordMat c.p c.d c.w c.S (V (E j))) →
      ∀ (m : ℕ) (u : Sˣ), (∃ i < n, LocalWitness.valHom S u = ordMat c.p c.d c.w c.S (V (E i))) →
        ∃ i < n, LocalWitness.valHom S (u * s ^ m) = ordMat c.p c.d c.w c.S (V (E i)) := by
    intro s G fs hsG m
    induction m with
    | zero =>
      intro u hu
      rw [pow_zero, mul_one]
      exact hu
    | succ m ih =>
      intro u hu
      obtain ⟨i, hi, fi⟩ := ih u hu
      obtain ⟨j, hj, fj⟩ := hsG i hi
      exact ⟨j, hj, by rw [pow_succ, ← mul_assoc, map_mul, fi, fs, fj]⟩
  have hall : ∀ u ∈ K, ∃ i < n, LocalWitness.valHom S u = ordMat c.p c.d c.w c.S (V (E i)) := by
    have hinv : ∀ {s : Sˣ} {o : ℕ}, 0 < o → s ^ o = 1 → s⁻¹ = s ^ (o - 1) := fun ho hso => by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel ho, hso]
    intro u hu
    induction hu using Subgroup.closure_induction_right with
    | one => exact ⟨0, hn, by rw [map_one, Nat.eq_of_beq_eq_true hE0, (CFSG.KS.Ord.one_sound hc).2]⟩
    | mul_right u _ s hs ih =>
      rcases hs with rfl | rfl
      · obtain ⟨i, hi, fi⟩ := hpow _ _ f1 (fun i hi => (hrt i hi).1) 1 u ih
        exact ⟨i, hi, by rw [← fi, pow_one]⟩
      · obtain ⟨i, hi, fi⟩ := hpow _ _ f2 (fun i hi => (hrt i hi).2) 1 u ih
        exact ⟨i, hi, by rw [← fi, pow_one]⟩
    | mul_inv_cancel u _ s hs ih =>
      rcases hs with rfl | rfl
      · rw [hinv (s := k1) ho1' (LocalWitness.unitOf_pow S m0 ho1'.ne' eK1)]
        exact hpow _ _ f1 (fun i hi => (hrt i hi).1) _ u ih
      · rw [hinv (s := k2) ho2' (LocalWitness.unitOf_pow S m1 ho2'.ne' eK2)]
        exact hpow _ _ f2 (fun i hi => (hrt i hi).2) _ u ih
  have hdist : ∀ i < n, ∀ j < n, ordMat c.p c.d c.w c.S (V (E i)) =
      ordMat c.p c.d c.w c.S (V (E j)) → i = j := fun i hi j hj he =>
    SecS.sortRun_inj hse hi hj (SecS.vec_unit_eq c hc ht (hEc i hi) (hEc j hj) he)
  choose! e emem emat using fun i (hi : i < n) => (hE i hi).2
  have hcardK : Nat.card K = n := by
    let F : Fin n → K := fun i => ⟨e i, emem i i.isLt⟩
    have hF : Function.Bijective F := by
      refine ⟨fun i j hij => Fin.ext (hdist i i.isLt j j.isLt ?_), fun u => ?_⟩
      · rw [← emat i i.isLt, ← emat j j.isLt]
        exact congrArg (fun w : K => LocalWitness.valHom S (w : Sˣ)) hij
      · obtain ⟨i, hi, hu⟩ := hall u u.2
        have he : (u : Sˣ) = e i := LocalWitness.valHom_injective S (hu.trans (emat i hi).symm)
        exact ⟨⟨i, hi⟩, Subtype.ext he.symm⟩
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]
  have hlist : ∀ {k j : ℕ}, j < n → Nat.beq (V (I k)) (V (E j)) = true →
      LocalWitness.valHom S (e j) = ordMat c.p c.d c.w c.S (V (I k)) := fun hj hb => by
    rw [emat _ hj, Nat.eq_of_beq_eq_true hb]
  let x : K := ⟨e (I 10), emem _ i10⟩
  let y : K := ⟨e (I 11), emem _ i11⟩
  have fx : LocalWitness.valHom S (x : Sˣ) = ordMat c.p c.d c.w c.S (V (I 2)) := hlist i10 q2
  have fy : LocalWitness.valHom S (y : Sˣ) = ordMat c.p c.d c.w c.S (V (I 3)) := hlist i11 q3
  have hx3 : x ^ 3 = 1 := Subtype.ext (LocalWitness.valHom_injective S (by
    rw [Subgroup.coe_pow, map_pow, fx, SecS.pow_one_of c hc c2 hX3]; rfl))
  have hy3 : y ^ 3 = 1 := Subtype.ext (LocalWitness.valHom_injective S (by
    rw [Subgroup.coe_pow, map_pow, fy, SecS.pow_one_of c hc c3 hY3]; rfl))
  have hxy : x * y = y * x := Subtype.ext (LocalWitness.valHom_injective S (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, fx, fy]
    exact SecS.mul_eq_of c hc c2 c3 c3 c2 hXY))
  have hinj : Function.Injective fun t : Fin 3 × Fin 3 => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hm := congrArg (fun w : K => LocalWitness.valHom S (w : Sˣ)) hij
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow] at hm
    rw [fx, fy] at hm
    obtain ⟨e1, e2⟩ := SecS.normal2_inj c hc c2 c3 (by norm_num) hnf i.isLt j.isLt i'.isLt
      j'.isLt hm
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  have hQcard : Nat.card (Subgroup.closure ({x, y} : Set K)) = 3 ^ 2 :=
    LocalWitness.card_closure_eq_sq (by norm_num) hx3 hy3 hxy hinj
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; omega)
  let Q : Sylow 3 K := Sylow.ofCard (Subgroup.closure ({x, y} : Set K)) (by
    rw [hQcard, hcardK, hfac])
  have hQ : (Q : Subgroup K) = Subgroup.closure ({x, y} : Set K) := rfl
  have hQab : IsElemAbelian 3 (Q : Subgroup K) := by
    rw [hQ]
    refine ⟨Subgroup.isMulCommutative_closure ?_, fun q hq => ?_⟩
    · rintro a (rfl | rfl) b (rfl | rfl) _
      · exact Commute.refl _
      · exact hxy
      · exact hxy.symm
      · exact Commute.refl _
    · have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
      obtain ⟨i, j, k, -, -, -, rfl⟩ := LocalWitness.mem_closure_normalForm (by norm_num) hx3 hy3
        (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) hq
      rw [hz, one_pow, mul_one, (Commute.pow_pow hxy i j).mul_pow, ← pow_mul, ← pow_mul,
        mul_comm i, mul_comm j, pow_mul, pow_mul, hx3, hy3, one_pow, one_pow, one_mul]
  have hperf : Group.IsPerfect K := by
    have comm : ∀ {kk : Sˣ} {ik i1 i2 j1 j2 : ℕ}, ik < 10 → i1 < 10 → i2 < 10 → j1 < n →
        j2 < n → LocalWitness.valHom S kk = ordMat c.p c.d c.w c.S (V (I ik)) →
        Nat.beq (V (I i1)) (V (E j1)) = true → Nat.beq (V (I i2)) (V (E j2)) = true →
        Nat.beq (c.mul (V (I i1)) (V (I i2))) (c.mul (c.mul (V (I ik)) (V (I i2))) (V (I i1))) =
          true → kk ∈ ⁅K, K⁆ := by
      intro kk ik i1 i2 j1 j2 hik hi1 hi2 hj1 hj2 hkk hb1 hb2 hrel
      have fu := hlist hj1 hb1
      have fw := hlist hj2 hb2
      obtain ⟨ck, -⟩ := hIv ik hik
      obtain ⟨cu, -⟩ := hIv i1 hi1
      obtain ⟨cw, -⟩ := hIv i2 hi2
      obtain ⟨ckw, ekw⟩ := SecS.mul_sound c hc ck cw
      have hrel' : e j1 * e j2 = kk * e j2 * e j1 := LocalWitness.valHom_injective S (by
        rw [map_mul, map_mul, map_mul, fu, fw, hkk, ← ekw]
        exact SecS.mul_eq_of c hc cu cw ckw cu hrel)
      have hk : kk = ⁅e j1, e j2⁆ := by
        rw [commutatorElement_def, hrel']
        group
      rw [hk]
      exact Subgroup.commutator_mem_commutator (emem j1 hj1) (emem j2 hj2)
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact comm (ik := 0) (by norm_num) (by norm_num) (by norm_num) i12 i13 f1 q6 q7 hp1
      · exact comm (ik := 1) (by norm_num) (by norm_num) (by norm_num) i14 i15 f2 q8 q9 hp2
  have hoh' : 0 < oh := Nat.blt_eq.mp hoh
  have eH := SecS.pow_one_of c hc c4 hH
  let hh := LocalWitness.unitOf S m4 hoh'.ne' eH
  have fh : LocalWitness.valHom S hh = ordMat c.p c.d c.w c.S (V (I 4)) :=
    LocalWitness.valHom_unitOf S _ _ _
  have conjK : ∀ {kk : Sˣ} {ik j : ℕ}, ik < 10 → j < n →
      LocalWitness.valHom S kk = ordMat c.p c.d c.w c.S (V (I ik)) →
      conjOK c (V (I 4)) (V (I ik)) (V (E j)) = true → hh * kk * hh⁻¹ ∈ K := by
    intro kk ik j hik hj hkk hcj
    obtain ⟨ck, -⟩ := hIv ik hik
    have he : hh * kk * hh⁻¹ = e j := by
      rw [mul_inv_eq_iff_eq_mul]
      apply LocalWitness.valHom_injective S
      rw [map_mul, map_mul, fh, hkk, emat j hj]
      exact SecS.conj_mat c hc c4 ck (hEc j hj) hcj
    rw [he]
    exact emem j hj
  have hnorm : hh ∈ Subgroup.normalizer (K : Set Sˣ) := by
    have hle : K.map (MulAut.conj hh).toMonoidHom ≤ K := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact conjK (by norm_num) i16 f1 hHK1
      · exact conjK (by norm_num) i17 f2 hHK2
    have heq : K.map (MulAut.conj hh).toMonoidHom = K :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Subgroup.card_map_of_injective (MulAut.conj hh).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [← heq]
      exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← heq] at hg
      obtain ⟨g', hg', hgg⟩ := hg
      have : g' = g := by
        simpa [MulAut.conj_apply] using hgg
      rw [← this]
      exact hg'
  have conj : ∀ {w u : Sˣ} {W U : ℕ}, Canon c.p c.d c.w W →
      LocalWitness.valHom S w = ordMat c.p c.d c.w c.S W → Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U → conjOK c (V (I 4)) U W = true →
      hh * u * hh⁻¹ = w := by
    intro w u W U cW fw cU fu hcj
    rw [mul_inv_eq_iff_eq_mul]
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fh, fu, fw]
    exact SecS.conj_mat c hc c4 cU cW hcj
  have word : ∀ i j : ℕ, Canon c.p c.d c.w (c.mul (c.pow (V (I 2)) i) (c.pow (V (I 3)) j)) ∧
      LocalWitness.valHom S ((x : Sˣ) ^ i * (y : Sˣ) ^ j) =
        ordMat c.p c.d c.w c.S (c.mul (c.pow (V (I 2)) i) (c.pow (V (I 3)) j)) := by
    intro i j
    obtain ⟨d1, g1⟩ := SecS.pow_sound c hc c2 i
    obtain ⟨d2, g2⟩ := SecS.pow_sound c hc c3 j
    obtain ⟨d3, g3⟩ := SecS.mul_sound c hc d1 d2
    exact ⟨d3, by rw [map_mul, map_pow, map_pow, fx, fy, g3, g1, g2]⟩
  have eC := SecS.pow_one_of c hc c5 hC3
  let z := LocalWitness.unitOf S m5 (by norm_num : (3 : ℕ) ≠ 0) eC
  have fz : LocalWitness.valHom S z = ordMat c.p c.d c.w c.S (V (I 5)) :=
    LocalWitness.valHom_unitOf S _ _ _
  have hz3 : z ^ 3 = 1 := LocalWitness.unitOf_pow S _ _ eC
  have hz1 : z ≠ 1 := by
    intro he
    apply SecS.mat_ne_one c hc ht c5 hCt
    rw [← fz, he, map_one]
  have zcomm : ∀ {kk : Sˣ} {ik : ℕ}, ik < 10 →
      LocalWitness.valHom S kk = ordMat c.p c.d c.w c.S (V (I ik)) →
      Nat.beq (c.mul (V (I 5)) (V (I ik))) (c.mul (V (I ik)) (V (I 5))) = true → Commute z kk := by
    intro kk ik hik hkk hce
    obtain ⟨ck, -⟩ := hIv ik hik
    apply LocalWitness.valHom_injective S
    rw [map_mul, map_mul, fz, hkk]
    exact SecS.mul_eq_of c hc c5 ck ck c5 hce
  have hzK : ∀ g ∈ K, Commute z g := by
    have hle : K ≤ Subgroup.centralizer {z} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (zcomm (by norm_num) f1 hCK1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (zcomm (by norm_num) f2 hCK2).symm
    intro g hg
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hnot : ∀ {u : Sˣ} {U : ℕ}, Canon c.p c.d c.w U →
      LocalWitness.valHom S u = ordMat c.p c.d c.w c.S U → notMemOK c V E n t U = true →
      u ∉ K := by
    intro u U cU hu hnm huK
    obtain ⟨j, hj, hj'⟩ := hall u huK
    exact SecS.notMem_spec c hnm j hj (SecS.vec_unit_eq c hc ht cU (hEc j hj) (by rw [← hu, hj']))
  obtain ⟨c55, e55⟩ := SecS.mul_sound c hc c5 c5
  have hzK1 : Subgroup.zpowers z ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgz, hgK⟩
    rw [Subgroup.mem_bot]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgz
    have hm : z ^ m = z ^ (m % 3).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact (zpow_eq_zpow_emod' m hz3).trans rfl
    rw [hm] at hgK ⊢
    have hlt : (m % 3).toNat < 3 := by omega
    interval_cases hk : (m % 3).toNat
    · rfl
    · rw [pow_one] at hgK
      exact absurd hgK (hnot c5 fz hCn)
    · exact absurd hgK (hnot c55 (by rw [map_pow, fz, pow_two, e55]) hC2n)
  refine ⟨K, hperf, Q, x, y, hh, z, hcardK, hQab, by rw [hQ]; exact hQcard, hnorm, hQ.symm,
    conj (word a cc).1 (word a cc).2 c2 fx hHX, conj (word b dd).1 (word b dd).2 c3 fy hHY, hzK,
    orderOf_eq_prime hz3 hz1, hzK1⟩

end CFSG.KC.LQT

end

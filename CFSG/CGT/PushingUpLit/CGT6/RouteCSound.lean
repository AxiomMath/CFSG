module

public import CFSG.CGT.PushingUpLit.CGT6.RouteCPack
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteC

variable {n : ℕ}

@[expose] def genMat (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ → Matrix (Fin n) (Fin n) (ZMod 2)
  | 0 => y
  | 1 => d
  | 2 => t
  | 3 => y * y
  | _ => d * d

@[expose] def evalMat (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) (w : List ℕ) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  w.foldl (fun acc l => acc * genMat y d t l) 1

structure ChartRel (y d t : Matrix (Fin n) (Fin n) (ZMod 2))
    (E : Matrix (Fin n) (Fin 6) (ZMod 2)) (φ ψ : ℕ) : Prop where
  surj : ∀ v : Fin n → ZMod 2, ∃ x, E.mulVec x = v
  hy : y * E = E * toMat 6 6 (chartY φ)
  hd : d * E = E * toMat 6 6 (chartD ψ)
  ht : t * E = E * toMat 6 6 chartT

variable {y d t : Matrix (Fin n) (Fin n) (ZMod 2)} {E : Matrix (Fin n) (Fin 6) (ZMod 2)}
  {φ ψ : ℕ}

theorem ChartRel.genMat_mul (R : ChartRel y d t E φ ψ) :
    ∀ l, genMat y d t l * E = E * toMat 6 6 (gen φ ψ l)
  | 0 => R.hy
  | 1 => R.hd
  | 2 => R.ht
  | 3 => by
    show y * y * E = E * toMat 6 6 (mul (chartY φ) (chartY φ))
    rw [toMat_mul 6 6 6 _ _ (by simp), Matrix.mul_assoc, R.hy, ← Matrix.mul_assoc, R.hy,
      Matrix.mul_assoc]
  | _ + 4 => by
    show d * d * E = E * toMat 6 6 (mul (chartD ψ) (chartD ψ))
    rw [toMat_mul 6 6 6 _ _ (by simp), Matrix.mul_assoc, R.hd, ← Matrix.mul_assoc, R.hd,
      Matrix.mul_assoc]

theorem ChartRel.evalMat_mul (R : ChartRel y d t E φ ψ) (w : List ℕ) :
    evalMat y d t w * E = E * toMat 6 6 (evalW φ ψ w) := by
  unfold evalMat evalW
  refine foldl_mul_intertwine E (genMat y d t) φ ψ R.genMat_mul w one 1 length_one ?_
  rw [Matrix.one_mul, toMat_one, Matrix.mul_one]

theorem vec_add_self {m : ℕ} (v : Fin m → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

theorem ChartRel.kernel_aux (R : ChartRel y d t E φ ψ) {Kb : List ℕ} (hK : KRel E (spanList Kb))
    (Kp : Mat) (hKp : Kp.length = 6) (bKp : Bnd Kp) (Ks : Matrix (Fin n) (Fin n) (ZMod 2))
    (hKs : Ks * E = E * toMat 6 6 Kp) (Wb : List ℕ)
    (h1 : ∀ b ∈ Wb, ∀ g ∈ [chartY φ, chartD ψ, chartT], mulVec g b ∈ spanList Wb)
    (h2 : ∀ x ∈ add Kp one, x ∈ spanList Wb)
    (h3 : ∀ b ∈ Wb, mulVec (add Kp one) b ∈ spanList Kb)
    (h4 : ∃ x ∈ add Kp one, x ∉ spanList Kb) :
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ w ∈ W, y.mulVec w ∈ W) ∧ (∀ w ∈ W, d.mulVec w ∈ W) ∧ (∀ w ∈ W, t.mulVec w ∈ W) ∧
      (∀ v, Ks.mulVec v + v ∈ W) ∧
      (∀ w ∈ W, Ks.mulVec w = w) ∧ ∃ v, Ks.mulVec v ≠ v := by
  have hkm1len : (add Kp one).length = 6 := by simp [add, hKp]
  have hkm1b : Bnd (add Kp one) := bnd_add _ _ bKp bnd_one
  have hT1 : toMat 6 6 (add Kp one) = toMat 6 6 Kp + 1 := by
    rw [toMat_add 6 6 _ _ (by simp [hKp]), toMat_one]
  set Kt := toMat 6 6 Kp with hKt
  set M := toMat 6 6 (add Kp one) with hM
  set W : Submodule (ZMod 2) (Fin n → ZMod 2) := (spanBits 6 Wb).map (Matrix.mulVecLin E) with hW
  have hmem : ∀ w ∈ W, ∃ z ∈ spanBits 6 Wb, E.mulVec z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
    exact ⟨z, hz, rfl⟩
  have inv : ∀ (X : Matrix (Fin n) (Fin n) (ZMod 2)) (A : Mat), A.length = 6 →
      X * E = E * toMat 6 6 A → (∀ b ∈ Wb, mulVec A b ∈ spanList Wb) →
      ∀ w ∈ W, X.mulVec w ∈ W := by
    intro X A hA hX hb w hw
    obtain ⟨z, hz, rfl⟩ := hmem w hw
    rw [Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec]
    exact Submodule.mem_map_of_mem (f := Matrix.mulVecLin E)
      (toMat_mulVec_mem_spanBits A hA Wb hb z hz)
  have hcol : ∀ j : Fin 6, bitVec 6 ((add Kp one).getD j 0) ∈ spanBits 6 Wb := fun j =>
    mem_spanBits_of_mem_spanList (h2 _ (getD_mem _ j (by rw [hkm1len]; exact j.2)))
  have hker : ∀ z ∈ spanBits 6 Wb, E.mulVec (M.mulVec z) = 0 := by
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨b, hb, rfl⟩
      have := mulVec_spec 6 (add Kp one) b
      rw [hkm1len] at this
      rw [hM, ← this]
      exact (hK.1 _ (h3 b hb))
    · simp
    · intro x y' _ _ hx hy
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hx, hy, add_zero]
    · intro c x _ hx
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hx, smul_zero]
  have key : ∀ z, Ks.mulVec (E.mulVec z) + E.mulVec z = E.mulVec (M.mulVec z) := by
    intro z
    rw [Matrix.mulVec_mulVec, hKs, ← Matrix.mulVec_mulVec, hT1, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_add]
  refine ⟨W, inv y _ (by simp) R.hy (fun b hb => h1 b hb _ (by simp)),
    inv d _ (by simp) R.hd (fun b hb => h1 b hb _ (by simp)),
    inv t _ (by simp) R.ht (fun b hb => h1 b hb _ (by simp)), ?_, ?_, ?_⟩
  · intro v
    obtain ⟨x, rfl⟩ := R.surj v
    rw [key]
    exact Submodule.mem_map_of_mem (f := Matrix.mulVecLin E)
      (toMat_mulVec_mem_of_cols _ _ hcol x)
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := hmem w hw
    have h5 := key z
    rw [hker z hz] at h5
    exact vec_eq_of_add_eq_zero h5
  · obtain ⟨x, hx, hxK⟩ := h4
    obtain ⟨j, hj, rfl⟩ := (List.mem_iff_getElem.mp hx)
    have hj6 : j < 6 := by rw [← hkm1len]; exact hj
    have hxlt : (add Kp one)[j] < 64 := hkm1b _ (List.getElem_mem hj)
    have hne : E.mulVec (bitVec 6 ((add Kp one)[j])) ≠ 0 := fun h0 => hxK (hK.2 _ hxlt h0)
    refine ⟨E.mulVec (Pi.single ⟨j, hj6⟩ 1), fun heq => hne ?_⟩
    have h5 := key (Pi.single ⟨j, hj6⟩ 1)
    rw [heq, vec_add_self] at h5
    have hc : M.mulVec (Pi.single ⟨j, hj6⟩ 1) = bitVec 6 ((add Kp one)[j]) := by
      funext i
      rw [Matrix.mulVec_single_one]
      simp [hM, toMat, List.getElem?_eq_getElem hj]
    rw [hc] at h5
    exact h5.symm

theorem ChartRel.cancel (R : ChartRel y d t E φ ψ) {X Y : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : X * E = Y * E) : X = Y := by
  ext i j
  obtain ⟨x, hx⟩ := R.surj (Pi.single j 1)
  have := congrFun (congrArg (fun M => M.mulVec x) h) i
  simp only [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_single_one] at this
  simpa using this

theorem intertwine_mul {X X' : Matrix (Fin n) (Fin n) (ZMod 2)} {A A' : Mat} (hA : A.length = 6)
    (h : X * E = E * toMat 6 6 A) (h' : X' * E = E * toMat 6 6 A') :
    (X * X') * E = E * toMat 6 6 (mul A A') := by
  rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, toMat_mul 6 6 6 A A' hA]

theorem intertwine_pow {X : Matrix (Fin n) (Fin n) (ZMod 2)} {A : Mat} (hA : A.length = 6)
    (h : X * E = E * toMat 6 6 A) : ∀ k, (X ^ k) * E = E * toMat 6 6 (pow A k)
  | 0 => by rw [pow_zero, Matrix.one_mul, pow, toMat_one, Matrix.mul_one]
  | k + 1 => by
    rw [pow_succ']
    exact intertwine_mul hA h (intertwine_pow hA h k)

theorem ChartRel.cent_aux (R : ChartRel y d t E φ ψ) {Kb : List ℕ} (hK : KRel E (spanList Kb))
    {a m : ℕ} {cw : List ℕ} (h : checkC φ ψ (spanList Kb) a m cw = true) :
    t * evalMat y d t cw = evalMat y d t cw * t ∧
    evalMat y d t cw * evalMat y d t (invW cw) = 1 ∧ m % 3 ≠ 0 ∧
    (y * (evalMat y d t cw * (y * evalMat y d t (invW cw)))) ^ a ≠ 1 ∧
    ((y * (evalMat y d t cw * (y * evalMat y d t (invW cw)))) ^ a) ^ m = 1 := by
  simp only [checkC, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hcE : evalMat y d t cw * E = E * toMat 6 6 (evalW φ ψ cw) := R.evalMat_mul cw
  have hciE : evalMat y d t (invW cw) * E = E * toMat 6 6 (evalW φ ψ (invW cw)) :=
    R.evalMat_mul (invW cw)
  have l6 : (chartY φ).length = 6 := length_chartY φ
  have lT : chartT.length = 6 := length_chartT
  have lc : (evalW φ ψ cw).length = 6 := length_evalW φ ψ cw
  have lci : (evalW φ ψ (invW cw)).length = 6 := length_evalW φ ψ (invW cw)
  have bc : Bnd (evalW φ ψ cw) := bnd_evalW φ ψ cw
  have bci : Bnd (evalW φ ψ (invW cw)) := bnd_evalW φ ψ (invW cw)
  have e1 := intertwine_mul (E := E) lT R.ht hcE
  have e1' := intertwine_mul (E := E) lc hcE R.ht
  have hy1 := intertwine_mul (E := E) l6 R.hy hciE
  have hy2 := intertwine_mul (E := E) lc hcE hy1
  have hx := intertwine_mul (E := E) l6 R.hy hy2
  have lx : (mul (chartY φ) (mul (evalW φ ψ cw) (mul (chartY φ) (evalW φ ψ (invW cw))))).length
      = 6 := by simp [length_mul, lci]
  have bx : Bnd (mul (chartY φ) (mul (evalW φ ψ cw) (mul (chartY φ) (evalW φ ψ (invW cw))))) :=
    bnd_mul _ _ (bnd_chartY φ)
  have hxa := intertwine_pow lx hx a
  have hxam := intertwine_pow (by simp [length_pow _ lx a]) hxa m
  refine ⟨R.cancel ?_, R.cancel ?_, by omega, ?_, ?_⟩
  · rw [e1, e1']
    exact (hK.eqMod_iff (mul chartT (evalW φ ψ cw)) (mul (evalW φ ψ cw) chartT)
      (by rw [length_mul]; exact lc) (by rw [length_mul]; exact lT) (bnd_mul _ _ bnd_chartT)
      (bnd_mul _ _ bc)).mp h1
  · rw [intertwine_mul lc hcE hciE, Matrix.one_mul]
    have := (hK.eqMod_iff (mul (evalW φ ψ cw) (evalW φ ψ (invW cw))) one
      (by rw [length_mul]; exact lci) length_one (bnd_mul _ _ bc) bnd_one).mp h2
    rw [toMat_one, Matrix.mul_one] at this
    exact this
  · intro hx1
    rw [hx1, Matrix.one_mul] at hxa
    have := (hK.eqMod_iff (pow (mul (chartY φ) (mul (evalW φ ψ cw) (mul (chartY φ)
      (evalW φ ψ (invW cw))))) a) one (length_pow _ lx a) length_one (bnd_pow _ bx a)
      bnd_one).mpr (by rw [toMat_one, Matrix.mul_one]; exact hxa.symm)
    rw [h4] at this
    exact Bool.false_ne_true this
  · have hxm1 := (hK.eqMod_iff (pow (pow (mul (chartY φ) (mul (evalW φ ψ cw) (mul (chartY φ)
      (evalW φ ψ (invW cw))))) a) m) one (length_pow _ (length_pow _ lx a) m) length_one
      (bnd_pow _ (bnd_pow _ bx a) m) bnd_one).mp h5
    rw [toMat_one, Matrix.mul_one] at hxm1
    apply R.cancel
    rw [hxam, hxm1, Matrix.one_mul]

theorem mat_ext_of_mulVec {m p : ℕ} {A B : Matrix (Fin m) (Fin p) (ZMod 2)}
    (h : ∀ x, A.mulVec x = B.mulVec x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext h)

theorem exists_right_inv {m p : ℕ} (M : Matrix (Fin m) (Fin p) (ZMod 2))
    (h : ∀ v : Fin m → ZMod 2, ∃ x, M.mulVec x = v) : ∃ R : Matrix (Fin p) (Fin m) (ZMod 2),
    M * R = 1 := by
  choose f hf using fun j : Fin m => h (Pi.single j 1)
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  ext i j
  have := congrFun (hf j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

@[expose] def SurvShape (n : ℕ) (s : Mat × Mat × Mat) : Prop :=
  s.1.length = n ∧ s.2.1.length = n ∧ s.2.2.length = n

instance (n : ℕ) (s : Mat × Mat × Mat) : Decidable (SurvShape n s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem ChartRel.survivor_aux (R : ChartRel y d t E φ ψ) {Kb : List ℕ}
    (hK : KRel E (spanList Kb)) {s : Mat × Mat × Mat} (hs : SurvShape n s) {θ : Mat}
    (h : checkS n φ ψ (spanList Kb) s θ = true) :
    ∃ g : Matrix (Fin n) (Fin n) (ZMod 2), IsUnit g ∧ g * y = toMat n n s.1 * g ∧
      g * d = toMat n n s.2.1 * g ∧ g * t = toMat n n s.2.2 * g := by
  unfold checkS at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.contains_iff_mem, Bool.beq_eq_decide_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hb⟩, hY⟩, hD⟩, hT⟩, hker⟩, hsurj⟩ := h
  set Θ := toMat n 6 θ with hΘdef
  have hΘ : ∀ (X Sx : Mat), X.length = 6 → Sx.length = n →
      X.map (mulVec θ) = θ.map (mulVec Sx) → Θ * toMat 6 6 X = toMat n n Sx * Θ := by
    intro X Sx hX hS hEq
    have e1 : toMat n 6 (mul θ X) = Θ * toMat 6 6 X := toMat_mul n 6 6 θ X hl
    have e2 : toMat n 6 (mul Sx θ) = toMat n n Sx * Θ := toMat_mul n n 6 Sx θ hS
    rw [← e1, ← e2]
    exact congrArg (toMat n 6) hEq
  have hΘker : ∀ z : Fin 6 → ZMod 2, E.mulVec z = 0 → Θ.mulVec z = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := bitVec_surj z
    have hx64 : x < 64 := by simpa using hx
    have hxK : x ∈ spanList Kb := hK.2 x hx64 hz
    have h0 : mulVec θ x = 0 := by
      have h1 := hker x hx64
      have h2 : (spanList Kb).contains x = true := List.contains_iff_mem.mpr hxK
      rw [← h1] at h2
      exact of_decide_eq_true h2
    have := mulVec_spec n θ x
    rw [hl] at this
    rw [← this, h0, bitVec_zero]
  obtain ⟨RE, hRE⟩ := exists_right_inv E R.surj
  have hgE : (Θ * RE) * E = Θ := by
    apply mat_ext_of_mulVec
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : E.mulVec (RE.mulVec (E.mulVec x) + x) = 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hRE, Matrix.one_mulVec, vec_add_self]
    have h2 := hΘker _ h1
    rw [Matrix.mulVec_add] at h2
    exact vec_eq_of_add_eq_zero h2
  have hΘs : ∀ v : Fin n → ZMod 2, ∃ z, Θ.mulVec z = v := by
    intro v
    obtain ⟨x, hx, rfl⟩ := bitVec_surj v
    have hmem := mem_spanBits_of_mem_spanList (m := n) (hsurj x hx)
    have hle : spanBits n θ ≤ LinearMap.range (Matrix.mulVecLin Θ) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
      have hj6 : j < 6 := hl ▸ hj
      refine ⟨Pi.single ⟨j, hj6⟩ 1, ?_⟩
      funext i
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      simp [hΘdef, toMat, List.getElem?_eq_getElem hj]
    obtain ⟨z, hz⟩ := hle hmem
    exact ⟨z, hz⟩
  have hgs : ∀ v : Fin n → ZMod 2, ∃ x, (Θ * RE).mulVec x = v := by
    intro v
    obtain ⟨z, hz⟩ := hΘs v
    refine ⟨E.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec, hgE, hz]
  obtain ⟨Rg, hRg⟩ := exists_right_inv (Θ * RE) hgs
  have hunit : IsUnit (Θ * RE) := ⟨⟨_, Rg, hRg, mul_eq_one_comm.mp hRg⟩, rfl⟩
  have l6 : (chartY φ).length = 6 := length_chartY φ
  refine ⟨Θ * RE, hunit, R.cancel ?_, R.cancel ?_, R.cancel ?_⟩
  · rw [Matrix.mul_assoc, R.hy, ← Matrix.mul_assoc, hgE, Matrix.mul_assoc, hgE]
    exact hΘ (chartY φ) s.1 l6 hs.1 hY
  · rw [Matrix.mul_assoc, R.hd, ← Matrix.mul_assoc, hgE, Matrix.mul_assoc, hgE]
    exact hΘ (chartD ψ) s.2.1 (length_chartD ψ) hs.2.1 hD
  · rw [Matrix.mul_assoc, R.ht, ← Matrix.mul_assoc, hgE, Matrix.mul_assoc, hgE]
    exact hΘ chartT s.2.2 length_chartT hs.2.2 hT

theorem ChartRel.kernel_word (R : ChartRel y d t E φ ψ) {Kb : List ℕ}
    (hK : KRel E (spanList Kb)) {m : ℕ} {g : List ℕ} (h : checkB φ ψ Kb m g = true) :
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ w ∈ W, y.mulVec w ∈ W) ∧ (∀ w ∈ W, d.mulVec w ∈ W) ∧ (∀ w ∈ W, t.mulVec w ∈ W) ∧
      (∀ v, (evalMat y d t g ^ m).mulVec v + v ∈ W) ∧
      (∀ w ∈ W, (evalMat y d t g ^ m).mulVec w = w) ∧ ∃ v, (evalMat y d t g ^ m).mulVec v ≠ v := by
  have hlen := length_evalW φ ψ g
  have hKs : (evalMat y d t g ^ m) * E = E * toMat 6 6 (pow (evalW φ ψ g) m) :=
    intertwine_pow hlen (R.evalMat_mul g) m
  unfold checkB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, x, hx, hxK⟩ := h
  refine R.kernel_aux hK _ (length_pow _ hlen m) (bnd_pow _ (bnd_evalW φ ψ g) m) _ hKs
    (closeBasis [chartY φ, chartD ψ, chartT] (Kb ++ add (pow (evalW φ ψ g) m) one))
    ?_ ?_ ?_ ⟨x, hx, ?_⟩
  · intro b hb g' hg'
    exact h1 b hb g' hg'
  · exact h2
  · exact h3
  · intro hm
    have h0 := List.contains_iff_mem.mpr hm
    rw [hxK] at h0
    exact Bool.false_ne_true h0


theorem invariantUnder_of_rel {Kb : List ℕ} {X : Matrix (Fin n) (Fin n) (ZMod 2)} {A : Mat}
    (hK : KRel E (spanList Kb)) (hA : A.length = 6) (bA : Bnd A)
    (hX : X * E = E * toMat 6 6 A) : invariantUnder Kb (spanList Kb) A = true := by
  simp only [invariantUnder, List.all_eq_true, List.contains_iff_mem]
  intro b hb
  have hbK : E.mulVec (bitVec 6 b) = 0 := hK.1 b (mem_spanList_of_mem hb)
  refine hK.2 _ (bnd_mulVec A bA b) ?_
  have := mulVec_spec 6 A b
  rw [hA] at this
  rw [this, Matrix.mulVec_mulVec, ← hX, ← Matrix.mulVec_mulVec, hbK, Matrix.mulVec_zero]

theorem ChartRel.condY_true (R : ChartRel y d t E φ ψ) {Kb : List ℕ} (hK : KRel E (spanList Kb)) :
    condY Kb (spanList Kb) φ = true :=
  invariantUnder_of_rel hK (length_chartY φ) (bnd_chartY φ) R.hy

theorem ChartRel.condD_true (R : ChartRel y d t E φ ψ) {Kb : List ℕ} (hK : KRel E (spanList Kb)) :
    condD Kb (spanList Kb) ψ = true :=
  invariantUnder_of_rel hK (length_chartD ψ) (bnd_chartD ψ) R.hd

theorem ChartRel.condT_true (R : ChartRel y d t E φ ψ) {Kb : List ℕ}
    (hK : KRel E (spanList Kb))
    (hkOk : ∀ x ∈ [1, 2, 3, 4, 8, 12], E.mulVec (bitVec 6 x) ≠ 0) (ht1 : t ≠ 1) :
    condT Kb (spanList Kb) = true := by
  unfold condT
  simp only [Bool.and_eq_true]
  refine ⟨⟨invariantUnder_of_rel hK length_chartT bnd_chartT R.ht, ?_⟩, ?_⟩
  · simp only [kOk, List.all_eq_true, Bool.not_eq_true']
    intro x hx
    cases hc : (spanList Kb).contains x
    · rfl
    · exact absurd (hK.1 x (List.contains_iff_mem.mp hc)) (hkOk x hx)
  · by_contra hcon
    simp only [List.any_eq_true, Bool.not_eq_true', not_exists, not_and, Bool.not_eq_false] at hcon
    have hall : ∀ x ∈ add chartT one, E.mulVec (bitVec 6 x) = 0 := fun x hx =>
      hK.1 x (List.contains_iff_mem.mp (hcon x hx))
    have hEM : E * toMat 6 6 (add chartT one) = 0 := by
      ext i j
      rw [mul_toMat_apply]
      have hj : (add chartT one).getD j 0 ∈ add chartT one :=
        getD_mem _ j (by simp [add])
      rw [hall _ hj]
      rfl
    have hsum : toMat 6 6 (add chartT one) = toMat 6 6 chartT + 1 := by
      rw [toMat_add 6 6 _ _ (by simp), toMat_one]
    have h1 : (t + 1) * E = (0 : Matrix (Fin n) (Fin n) (ZMod 2)) * E := by
      rw [Matrix.add_mul, Matrix.one_mul, R.ht, Matrix.zero_mul, ← hEM, hsum, Matrix.mul_add,
        Matrix.mul_one]
    have h2 : t + 1 = 0 := R.cancel h1
    exact ht1 ((eq_neg_of_add_eq_zero_left h2).trans (ZModModule.neg_eq_self _))

theorem mem_members {m : ℕ} {Kb : List ℕ} {φ ψ : ℕ} (hK : Kb ∈ kList (6 - m))
    (hT : condT Kb (spanList Kb) = true) (hφ : φ < 16) (hY : condY Kb (spanList Kb) φ = true)
    (hψ : ψ < 256) (hD : condD Kb (spanList Kb) ψ = true) : (Kb, φ, ψ) ∈ members m := by
  unfold members
  rw [List.mem_flatMap]
  refine ⟨Kb, hK, ?_⟩
  simp only [hT, ↓reduceIte, List.mem_flatMap]
  refine ⟨φ, List.mem_filter.mpr ⟨List.mem_range.mpr hφ, hY⟩, ?_⟩
  exact List.mem_map.mpr ⟨ψ, List.mem_filter.mpr ⟨List.mem_range.mpr hψ, hD⟩, rfl⟩

theorem zipWith_all_spec {α β : Type} (f : α → β → Bool) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (List.zipWith f l₁ l₂).all id = true → ∀ a ∈ l₁, ∃ b ∈ l₂, f a b = true
  | [], _, _, _, a, ha => by simp at ha
  | _ :: _, [], h, _, _, _ => by simp at h
  | a₀ :: l₁, b₀ :: l₂, h, hall, a, ha => by
    simp only [List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true, id] at hall
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨b₀, List.mem_cons_self .., hall.1⟩
    · obtain ⟨b, hb, hfb⟩ := zipWith_all_spec f l₁ l₂ (by simpa using h) hall.2 a ha'
      exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩

theorem check_spec {surv : List (Mat × Mat × Mat)} {m : ℕ} {data : List ℕ}
    (h : check surv m data = true) :
    ∀ x ∈ members m, ∃ w ∈ data, memberOk surv m x.1 x.2.1 x.2.2 (unpack 64 w) = true := by
  unfold check at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact zipWith_all_spec _ _ _ h.1 h.2


@[expose] def OutB (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∃ (m : ℕ) (g : List ℕ) (W : Submodule (ZMod 2) (Fin n → ZMod 2)),
    (∀ w ∈ W, y.mulVec w ∈ W) ∧ (∀ w ∈ W, d.mulVec w ∈ W) ∧ (∀ w ∈ W, t.mulVec w ∈ W) ∧
    (∀ v, (evalMat y d t g ^ m).mulVec v + v ∈ W) ∧
    (∀ w ∈ W, (evalMat y d t g ^ m).mulVec w = w) ∧ ∃ v, (evalMat y d t g ^ m).mulVec v ≠ v

@[expose] def OutC (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∃ (a m : ℕ) (cw : List ℕ), t * evalMat y d t cw = evalMat y d t cw * t ∧
    evalMat y d t cw * evalMat y d t (invW cw) = 1 ∧ m % 3 ≠ 0 ∧
    (y * (evalMat y d t cw * (y * evalMat y d t (invW cw)))) ^ a ≠ 1 ∧
    ((y * (evalMat y d t cw * (y * evalMat y d t (invW cw)))) ^ a) ^ m = 1

@[expose] def OutS (surv : List (Mat × Mat × Mat)) (y d t : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Prop :=
  ∃ s ∈ surv, ∃ g : Matrix (Fin n) (Fin n) (ZMod 2), IsUnit g ∧ g * y = toMat n n s.1 * g ∧
    g * d = toMat n n s.2.1 * g ∧ g * t = toMat n n s.2.2 * g

theorem ChartRel.member_cases (R : ChartRel y d t E φ ψ) {Kb : List ℕ}
    (hK : KRel E (spanList Kb)) {surv : List (Mat × Mat × Mat)}
    (hsurv : ∀ s ∈ surv, SurvShape n s) {w : List ℕ}
    (h : memberOk surv n Kb φ ψ w = true) : OutB y d t ∨ OutC y d t ∨ OutS surv y d t := by
  rcases w with _ | ⟨k, w⟩
  · simp [memberOk] at h
  rcases k with _ | _ | _ | _ | k
  · rcases w with _ | ⟨m, g⟩
    · simp [memberOk] at h
    · exact Or.inl ⟨m, g, R.kernel_word hK h⟩
  · rcases w with _ | ⟨a, w⟩
    · simp [memberOk] at h
    rcases w with _ | ⟨m, cw⟩
    · simp [memberOk] at h
    · exact Or.inr (Or.inl ⟨a, m, cw, R.cent_aux hK h⟩)
  · simp [memberOk] at h
  · rcases w with _ | ⟨i, θ⟩
    · simp [memberOk] at h
    · simp only [memberOk] at h
      cases hs : surv[i]? with
      | none => simp [hs] at h
      | some s =>
        rw [hs] at h
        have hsmem : s ∈ surv := List.mem_of_getElem? hs
        exact Or.inr (Or.inr ⟨s, hsmem, R.survivor_aux hK (hsurv s hsmem) h⟩)
  · simp [memberOk] at h


end CFSG.CGT.PushingUpLit.CGT6.RouteC

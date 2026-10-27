module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AA6FrameKFA6Pack

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AltSixK

open Equiv Finset CFSG.Permutation.FinPack CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack

@[expose] def c1 : Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c2 : Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def jj : Perm (Fin 6) :=
  Equiv.swap 0 4 * Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 2 5

@[expose] def e9 : Finset (Perm (Fin 6)) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image
    (fun p => c1 ^ (p.1 : ℕ) * c2 ^ (p.2 : ℕ))

abbrev PA (g : Perm (Fin 6)) : Prop :=
  (∀ x : Fin 6, x.val < 3 ↔ (g x).val < 3) ∨ (∀ x : Fin 6, x.val < 3 ↔ ¬ (g x).val < 3)

@[expose] def L9 : List (Perm (Fin 6)) :=
  [1, c2, c2 ^ 2, c1, c1 * c2, c1 * c2 ^ 2, c1 ^ 2, c1 ^ 2 * c2, c1 ^ 2 * c2 ^ 2]

theorem e9_eq : e9 = L9.toFinset := by decide +kernel

theorem mem_e9 {x : Perm (Fin 6)} : x ∈ e9 ↔ x ∈ L9 := by rw [e9_eq, List.mem_toFinset]

@[expose] def E9K : List ℕ :=
  [5517840, 3490320, 4411920, 5517345, 3489825, 4411425, 5517570, 3490050, 4411650]

theorem pin9 : L9.map enc = E9K := by decide +kernel

theorem mem_E9K {x : Perm (Fin 6)} : x ∈ e9 ↔ enc x ∈ E9K := by
  rw [mem_e9, ← pin9]
  exact mem_iff_enc (by norm_num) L9 x

theorem c1_mem : c1 ∈ e9 := mem_e9.2 (by decide +kernel)

theorem c2_mem : c2 ∈ e9 := mem_e9.2 (by decide +kernel)

theorem of9 {f : ℕ → Bool} (h : allK f E9K = true) {x : Perm (Fin 6)} (hx : x ∈ e9) :
    f (enc x) = true :=
  allK_iff.1 h _ (mem_E9K.1 hx)

theorem ne_one_beq {r : Perm (Fin 6)} (hr1 : r ≠ 1) :
    Nat.beq (enc r) (enc (1 : Perm (Fin 6))) = false :=
  Bool.eq_false_iff.2 fun h => hr1 (enc_inj (by norm_num) (Nat.eq_of_beq_eq_true h))

@[expose] def JK : ℕ := 2102595

@[expose] def JIK : ℕ := 2164020

theorem enc_jj : enc jj = JK := by decide +kernel

theorem enc_jjinv : enc jj⁻¹ = JIK := by decide +kernel

theorem e9_mul : ∀ x ∈ e9, ∀ y ∈ e9, x * y ∈ e9 := by
  have h : allK (fun a => allK (fun b => memK (mulK 6 a b) E9K) E9K) E9K = true := by
    decide +kernel
  intro x hx y hy
  have h1 := of9 (of9 h hx) hy
  rw [← enc_mul6] at h1
  exact mem_E9K.2 (memK_iff.1 h1)

theorem e9_one : (1 : Perm (Fin 6)) ∈ e9 := mem_e9.2 (by decide +kernel)

theorem e9_comm : ∀ x ∈ e9, ∀ y ∈ e9, x * y = y * x := by
  have h : allK (fun a => allK (fun b => commLaneK 6 a b) E9K) E9K = true := by decide +kernel
  intro x hx y hy
  exact (commLaneK_iff (by norm_num) x y).1 (of9 (of9 h hx) hy)

theorem e9_cube : ∀ x ∈ e9, x ^ 3 = 1 := by
  have h : allK (fun a => Nat.beq (mulK 6 a (mulK 6 a a)) ID6) E9K = true := by decide +kernel
  intro x hx
  have h1 := of9 h hx
  rw [← enc_mul6, ← enc_mul6, ← enc_one6] at h1
  rw [pow_three]
  exact enc_inj (by norm_num) (Nat.eq_of_beq_eq_true h1)

theorem e9_inv : ∀ x ∈ e9, x⁻¹ ∈ e9 := by
  intro x hx
  have e : x⁻¹ = x * x := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact e9_cube x hx
  rw [e]
  exact e9_mul x hx x hx

theorem e9_sign : ∀ x ∈ e9, Perm.sign x = 1 := by
  have s1 : Perm.sign c1 = 1 := by decide +kernel
  have s2 : Perm.sign c2 = 1 := by decide +kernel
  intro x hx
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
  rw [map_mul, map_pow, map_pow, s1, s2, one_pow, one_pow, one_mul]

theorem e9_card : e9.card = 9 := by
  rw [e9_eq]
  decide +kernel

theorem j_sign : Perm.sign jj = 1 := by decide +kernel

theorem j_conj_ne : ∀ r ∈ e9, r ≠ 1 →
    jj * r * jj⁻¹ ≠ 1 ∧ jj * r * jj⁻¹ ≠ r ∧ jj * r * jj⁻¹ ≠ r ^ 2 := by
  have h : allK (fun r => Nat.beq r ID6 || (!Nat.beq (mulK 6 (mulK 6 JK r) JIK) ID6 &&
      !Nat.beq (mulK 6 (mulK 6 JK r) JIK) r &&
      !Nat.beq (mulK 6 (mulK 6 JK r) JIK) (mulK 6 r r))) E9K = true := by
    decide +kernel
  intro r hr hr1
  have h1 := of9 h hr
  rw [← enc_jj, ← enc_jjinv, ← enc_mul6, ← enc_mul6, ← enc_mul6, ← enc_one6] at h1
  simp only [ne_one_beq hr1, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨⟨a1, a2⟩, a3⟩ := h1
  rw [pow_two]
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e, Nat.beq_refl] at a1
    exact absurd a1 (by decide)
  · rw [e, Nat.beq_refl] at a2
    exact absurd a2 (by decide)
  · rw [e, Nat.beq_refl] at a3
    exact absurd a3 (by decide)

theorem j_normalizes : ∀ h : Perm (Fin 6), h ∈ e9 ↔ jj * h * jj⁻¹ ∈ e9 := by
  have f1 : allK (fun h => memK (mulK 6 (mulK 6 JK h) JIK) E9K) E9K = true := by decide +kernel
  have f2 : allK (fun h => memK (mulK 6 (mulK 6 JIK h) JK) E9K) E9K = true := by decide +kernel
  intro h
  constructor
  · intro hh
    have h1 := of9 f1 hh
    rw [← enc_jj, ← enc_jjinv, ← enc_mul6, ← enc_mul6] at h1
    exact mem_E9K.2 (memK_iff.1 h1)
  · intro hh
    have h1 := of9 f2 hh
    rw [← enc_jj, ← enc_jjinv, ← enc_mul6, ← enc_mul6] at h1
    have e : jj⁻¹ * (jj * h * jj⁻¹) * jj = h := by group
    rw [← e]
    exact mem_E9K.2 (memK_iff.1 h1)

@[expose] noncomputable def paK (c : ℕ) : Bool :=
  allLtK (fun i => Nat.blt (rd c i) 3 == Nat.blt i 3) 6 ||
    allLtK (fun i => Nat.blt i 3 == !Nat.blt (rd c i) 3) 6

theorem lane1 : ∀ a b : Fin 6,
    (Nat.blt (b : ℕ) 3 == Nat.blt (a : ℕ) 3) = true ↔ (a.val < 3 ↔ b.val < 3) := by
  decide +kernel

theorem lane2 : ∀ a b : Fin 6,
    (Nat.blt (a : ℕ) 3 == !Nat.blt (b : ℕ) 3) = true ↔ (a.val < 3 ↔ ¬ b.val < 3) := by
  decide +kernel

theorem paK_iff (g : Perm (Fin 6)) : paK (enc g) = true ↔ PA g := by
  unfold paK
  rw [Bool.or_eq_true, allLtK_iff, allLtK_iff]
  refine or_congr ⟨fun h x => ?_, fun h j hj => ?_⟩ ⟨fun h x => ?_, fun h j hj => ?_⟩
  · have e := h x x.2
    rw [rd_enc (n := 6) (by norm_num)] at e
    exact (lane1 x (g x)).1 e
  · have e : rd (enc g) j = (g ⟨j, hj⟩ : ℕ) := rd_enc (by norm_num) g ⟨j, hj⟩
    rw [e]
    exact (lane1 ⟨j, hj⟩ (g ⟨j, hj⟩)).2 (h ⟨j, hj⟩)
  · have e := h x x.2
    rw [rd_enc (n := 6) (by norm_num)] at e
    exact (lane2 x (g x)).1 e
  · have e : rd (enc g) j = (g ⟨j, hj⟩ : ℕ) := rd_enc (by norm_num) g ⟨j, hj⟩
    rw [e]
    exact (lane2 ⟨j, hj⟩ (g ⟨j, hj⟩)).2 (h ⟨j, hj⟩)

theorem e9_PA : ∀ x ∈ e9, PA x := by
  have h : allK paK E9K = true := by decide +kernel
  intro x hx
  exact (paK_iff x).1 (of9 h hx)

theorem j_PA : PA jj := (paK_iff jj).1 (by rw [enc_jj]; decide +kernel)

theorem nPA : allK (fun p => !allK (fun h => memK (mulK 6 (mulK 6 (lo6 p) h) (hi6 p)) E9K) E9K ||
    paK (lo6 p)) allCodes6 = true := by
  decide +kernel

theorem Q0_normalizer_PA : ∀ x : Perm (Fin 6), (∀ h ∈ e9, x * h * x⁻¹ ∈ e9) → PA x := by
  intro x hx
  have h1 := allK_iff.1 nPA _ (memK_iff.1 (pc6_mem_all x))
  rw [lo6_pc6, hi6_pc6] at h1
  have h2 : allK (fun h => memK (mulK 6 (mulK 6 (enc x) h) (enc x⁻¹)) E9K) E9K = true := by
    rw [allK_iff]
    intro c hc
    rw [← pin9, List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    rw [← enc_mul6, ← enc_mul6, memK_iff]
    exact mem_E9K.1 (hx y (mem_e9.2 hy))
  rw [h2, Bool.not_true, Bool.false_or] at h1
  exact (paK_iff x).1 h1

theorem nR : allK (fun p => paK (lo6 p) || allK (fun r => Nat.beq r ID6 ||
    !(Nat.beq (mulK 6 (mulK 6 (lo6 p) r) (hi6 p)) r ||
      Nat.beq (mulK 6 (mulK 6 (lo6 p) r) (hi6 p)) (mulK 6 r r))) E9K) allCodes6 = true := by
  decide +kernel

theorem normalizes_r : ∀ r ∈ e9, r ≠ 1 → ∀ x : Perm (Fin 6),
    (x * r * x⁻¹ = r ∨ x * r * x⁻¹ = r ^ 2) → PA x := by
  intro r hr hr1 x hx
  have h1 := allK_iff.1 nR _ (memK_iff.1 (pc6_mem_all x))
  rw [lo6_pc6, hi6_pc6] at h1
  cases hP : paK (enc x)
  · rw [hP, Bool.false_or] at h1
    have h2 := allK_iff.1 h1 _ (mem_E9K.1 hr)
    rw [← enc_mul6, ← enc_mul6, ← enc_mul6, ← enc_one6] at h2
    have e1 : Nat.beq (enc r) (enc 1) = false :=
      Bool.eq_false_iff.2 fun h => hr1 (enc_inj (by norm_num) (Nat.eq_of_beq_eq_true h))
    have e2 : (Nat.beq (enc (x * r * x⁻¹)) (enc r) ||
        Nat.beq (enc (x * r * x⁻¹)) (enc (r * r))) = true := by
      rcases hx with h | h
      · rw [h, Nat.beq_refl, Bool.true_or]
      · rw [h, pow_two, Nat.beq_refl, Bool.or_true]
    rw [e1, e2] at h2
    exact absurd h2 (by decide)
  · exact (paK_iff x).1 hP

@[expose] def JP : List ℕ := [5517840, 2102595, 5456385, 2164020]

theorem pinJ : [jj ^ 0, jj ^ 1, jj ^ 2, jj ^ 3].map enc = JP := by decide +kernel

theorem cov : allK (fun p => !paK (lo6 p) ||
    anyK (fun a => anyK (fun q => Nat.beq (lo6 p) (mulK 6 a q)) JP) E9K) evenCodes6 = true := by
  decide +kernel

theorem cover : ∀ g : Perm (Fin 6), Perm.sign g = 1 → PA g →
    ∃ a ∈ e9, ∃ k : Fin 4, g = a * jj ^ (k : ℕ) := by
  intro g hs hP
  have h1 := allK_iff.1 cov _ (memK_iff.1 (pc6_mem_even g hs))
  rw [lo6_pc6, (paK_iff g).2 hP, Bool.not_true, Bool.false_or, anyK_iff] at h1
  obtain ⟨c, hc, h2⟩ := h1
  rw [anyK_iff] at h2
  obtain ⟨q, hq, h3⟩ := h2
  rw [← pin9, List.mem_map] at hc
  obtain ⟨A, hA, rfl⟩ := hc
  rw [← pinJ] at hq
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
  have key : ∀ Q : Perm (Fin 6), Nat.beq (enc g) (mulK 6 (enc A) (enc Q)) = true → g = A * Q :=
    fun Q h => enc_inj (by norm_num) (by rw [enc_mul6]; exact Nat.eq_of_beq_eq_true h)
  refine ⟨A, mem_e9.2 hA, ?_⟩
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨0, key _ h3⟩
  · exact ⟨1, key _ h3⟩
  · exact ⟨2, key _ h3⟩
  · exact ⟨3, key _ h3⟩

theorem c36 : Nat.beq (CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack.cntK (fun c => paK (lo6 c))
    evenCodes6) 36 = true := by
  decide +kernel

theorem card36 : (univ.filter fun g : Perm (Fin 6) => Perm.sign g = 1 ∧ PA g).card = 36 := by
  rw [Finset.filter_congr (q := fun g : Perm (Fin 6) => Perm.sign g = 1 ∧ paK (enc g) = true)
    (fun g _ => and_congr_right fun _ => (paK_iff g).symm), card_even_filter paK]
  exact Nat.eq_of_beq_eq_true c36

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AltSixK

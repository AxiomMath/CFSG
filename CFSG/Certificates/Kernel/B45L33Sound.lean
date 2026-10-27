module

public import Certificates.Data.Kernel.B45L33
public import CFSG.Quasithin.Background.SmithB45ExcL33Mat

public section

namespace CFSG.KC.B45L33

open Matrix CFSG.Quasithin.B45Exc.L33 CFSG.Quasithin.B45Exc.L33.M3

variable {K : Type} [Field K] [CharP K 3]

theorem eqM_iff {x y : M3} : eqM x y = true ↔ x = y := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  obtain ⟨a', b', c', d', e', f', g', h', i'⟩ := y
  simp [eqM, and_assoc]

theorem eqM_eq_decide (x y : M3) : eqM x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, eqM_iff, decide_eq_true_iff]

theorem beq_eq_eqM (x y : M3) : (x == y) = eqM x y := by
  rw [Bool.eq_iff_iff, beq_iff_eq, eqM_iff]

theorem eqL_eq : ∀ {l l' : List M3}, eqL l l' = true → l = l'
  | [], [], _ => rfl
  | x :: l, y :: l', h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [eqM_iff.1 h.1, eqL_eq h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem eqL2_eq : ∀ {l l' : List (M3 × M3)}, eqL2 l l' = true → l = l'
  | [], [], _ => rfl
  | x :: l, y :: l', h => by
    simp only [eqL2, Bool.and_eq_true] at h
    rw [Prod.ext (eqM_iff.1 h.1.1) (eqM_iff.1 h.1.2), eqL2_eq h.2]
  | [], _ :: _, h => by simp [eqL2] at h
  | _ :: _, [], h => by simp [eqL2] at h

theorem isSOK_eq (B x : M3) : isSOK B x = isSO B x := by
  simp only [isSOK, isSO, beq_eq_eqM]

theorem goodK_eq (A t u : M3) (w : M3 × M3 × M3) : goodK A t u w = good A t u w := by
  simp only [goodK, good, isSOK_eq, ord13K, ord13, beq_eq_eqM, bne]

theorem mem_invEnum {x : M3} (hx : x.R) (hdet : x.det = 1) (h2 : mul x x = one)
    (h1 : x ≠ one) : x ∈ invEnum := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh, hi⟩ := hx
  have e00 : (a * a + b * d + c * g) % 3 = 1 := congrArg M3.a h2
  have e01 : (a * b + b * e + c * h) % 3 = 0 := congrArg M3.b h2
  have e10 : (d * a + e * d + f * g) % 3 = 0 := congrArg M3.d h2
  have e11 : (d * b + e * e + f * h) % 3 = 1 := congrArg M3.e h2
  have c00 : ((a * a + b * d + c * g) % 3 == 1) = true := by rw [e00]; rfl
  have c01 : ((a * b + b * e + c * h) % 3 == 0) = true := by rw [e01]; rfl
  have c1x : ((d * a + e * d + f * g) % 3 == 0 && (d * b + e * e + f * h) % 3 == 1) = true := by
    rw [e10, e11]; rfl
  unfold invEnum
  refine List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_flatMap.2 ⟨b, List.mem_range.2 hb,
    List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, List.mem_flatMap.2 ⟨d, List.mem_range.2 hd,
    List.mem_flatMap.2 ⟨g, List.mem_range.2 hg, ?_⟩⟩⟩⟩⟩
  rw [if_pos c00]
  refine List.mem_flatMap.2 ⟨e, List.mem_range.2 he,
    List.mem_flatMap.2 ⟨h, List.mem_range.2 hh, ?_⟩⟩
  rw [if_pos c01]
  refine List.mem_flatMap.2 ⟨f, List.mem_range.2 hf, ?_⟩
  rw [if_pos c1x]
  refine List.mem_filter.2 ⟨List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, ?_⟩
  simp [eqM_eq_decide, h2, hdet, h1]

theorem mem_symInv {A : M3} (hA : A.R) (hs : M3.tr A = A) (hd : A.det ≠ 0) : A ∈ symInv := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := A
  obtain ⟨ha, hb, hc, -, he, hf, -, -, hi⟩ := hA
  have hdb : d = b := congrArg M3.b hs
  have hgc : g = c := congrArg M3.c hs
  have hhf : h = f := congrArg M3.f hs
  subst hdb hgc hhf
  refine List.mem_filter.2 ⟨?_, by simpa using hd⟩
  exact List.mem_flatMap.2 ⟨_, List.mem_range.2 ha, List.mem_flatMap.2 ⟨_, List.mem_range.2 hb,
    List.mem_flatMap.2 ⟨_, List.mem_range.2 hc, List.mem_flatMap.2 ⟨_, List.mem_range.2 he,
    List.mem_flatMap.2 ⟨_, List.mem_range.2 hf, List.mem_map.2 ⟨_, List.mem_range.2 hi, rfl⟩⟩⟩⟩⟩⟩

theorem det_eq_one_of {x : M3} (h : (x.toK K).det = 1) : M3.det x = 1 := by
  have h1 : ((M3.det x : ℕ) : K) = ((1 : ℕ) : K) := by rw [toK_det, h, Nat.cast_one]
  exact natCast_inj_of_lt (K := K) (Nat.mod_lt _ (by norm_num)) (by norm_num) h1

theorem mem_I {I : List M3} (hI : invOK I = true) {x : M3} (hx : x.R)
    (hdet : (x.toK K).det = 1) (h2 : x.toK K * x.toK K = 1) (h1 : x.toK K ≠ 1) : x ∈ I := by
  rw [← eqL_eq hI]
  exact mem_invEnum hx (det_eq_one_of hdet)
    (toK_inj (K := K) (R_mul x x) R_one (by rw [toK_mul, h2, toK_one]))
    (fun h => h1 (by rw [h, toK_one]))

theorem mem_pairs {I : List M3} {Pr : List (M3 × M3 × M3)} (hP : pairsOK I Pr = true)
    {t u : M3} (ht : t ∈ I) (hu : u ∈ I) (hne : t ≠ u) (hc : mul t u = mul u t) :
    ∃ g, (t, u, g) ∈ Pr ∧ c2ok t u g = true := by
  simp only [pairsOK, Bool.and_eq_true, List.all_eq_true] at hP
  have h1 : eqM t u = false := by
    cases h : eqM t u
    · rfl
    · exact absurd (eqM_iff.1 h) hne
  have hf : (!eqM t u && eqM (mul t u) (mul u t)) = true := by
    rw [h1, eqM_iff.2 hc]
    rfl
  have hm : (t, u) ∈ pairsEnum I := by
    unfold pairsEnum
    exact List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨u, List.mem_filter.2 ⟨hu, hf⟩, rfl⟩⟩
  rw [eqL2_eq hP.1] at hm
  obtain ⟨⟨t', u', g⟩, he, hEq⟩ := List.mem_map.1 hm
  have e1 : t' = t := congrArg Prod.fst hEq
  have e2 : u' = u := congrArg Prod.snd hEq
  subst e1 e2
  have hg := hP.2 _ he
  dsimp only at hg
  exact ⟨g, he, hg⟩

theorem sym_entry {S : List (M3 × M3 × M3)} (hS : symOK S = true) {a : M3} (ha : a.R)
    (hA : (a.toK K)ᵀ = a.toK K) (hdet : (a.toK K).det ≠ 0) :
    ∃ y P, (a, y, P) ∈ S ∧ c1ok a y P = true := by
  simp only [symOK, Bool.and_eq_true, List.all_eq_true] at hS
  have hm : a ∈ symInv := mem_symInv ha (toK_inj (K := K) (R_tr ha) ha (by rw [toK_tr, hA]))
    (fun h0 => hdet (by rw [← toK_det, h0, Nat.cast_zero]))
  rw [eqL_eq hS.1] at hm
  obtain ⟨⟨a', y, P⟩, he, e1⟩ := List.mem_map.1 hm
  dsimp only at e1
  subst e1
  have hc := hS.2 _ he
  dsimp only at hc
  exact ⟨y, P, he, hc⟩

theorem of_c1ok {a y P : M3} (h : c1ok a y P = true) :
    (y.toK K).det = 1 ∧ y.toK K * a.toK K = a.toK K * (y.toK K)ᵀ ∧ y.toK K ^ 13 = 1 ∧
      y.toK K ≠ 1 ∧ (P.toK K).det = 1 ∧ P.toK K * (adj P).toK K = 1 ∧
      (adj P).toK K * P.toK K = 1 ∧ ∃ c : K, c * c = 1 ∧ P.toK K * a.toK K * (P.toK K)ᵀ = c • 1 := by
  simp only [c1ok, eqM_eq_decide, ← decide_not, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hy1, hyA⟩, hy13⟩, hyne⟩, hP1⟩, hPa⟩, hPb⟩, hQ⟩ := h
  refine ⟨by rw [← toK_det, hy1, Nat.cast_one], by rw [← toK_tr, ← toK_mul, ← toK_mul, hyA],
    by rw [← toK_pow, hy13, toK_one], fun h1 => hyne ?_, by rw [← toK_det, hP1, Nat.cast_one],
    by rw [← toK_mul, hPa, toK_one], by rw [← toK_mul, hPb, toK_one], ?_⟩
  · exact toK_inj (K := K) (R_mul _ _) R_one (by rw [toK_mul, toK_one, h1, Matrix.one_mul])
  · have e : P.toK K * a.toK K * (P.toK K)ᵀ = (mul P (mul a (tr P))).toK K := by
      rw [toK_mul, toK_mul, toK_tr, Matrix.mul_assoc]
    rcases hQ with hQ | hQ
    · exact ⟨1, one_mul 1, by rw [e, hQ, toK_one, one_smul]⟩
    · exact ⟨-1, by norm_num, by rw [e, hQ, toK_negOne, neg_smul, one_smul]⟩

theorem of_c2ok {t u g : M3} (h : c2ok t u g = true) :
    (g.toK K).det = 1 ∧ g.toK K * t.toK K = t.toK K * g.toK K ∧ g.toK K * (adj g).toK K = 1 ∧
      (u.toK K * (g.toK K * u.toK K * (adj g).toK K)) ^ 4 = 1 ∧
      (u.toK K * (g.toK K * u.toK K * (adj g).toK K)) ^ 2 ≠ 1 := by
  simp only [c2ok, eqM_eq_decide, ← decide_not, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hg1, hgt⟩, hgi⟩, hw4, hw2⟩ := h
  have hw : (mul u (mul g (mul u (adj g)))).toK K =
      u.toK K * (g.toK K * u.toK K * (adj g).toK K) := by
    simp only [toK_mul, Matrix.mul_assoc]
  refine ⟨by rw [← toK_det, hg1, Nat.cast_one], by rw [← toK_mul, ← toK_mul, hgt],
    by rw [← toK_mul, hgi, toK_one], by rw [← hw, ← toK_pow, hw4, toK_one], fun h2 => hw2 ?_⟩
  exact toK_inj (K := K) (R_pow _ _) R_one (by rw [toK_pow, hw, h2, toK_one])

theorem c1_of {S : List (M3 × M3 × M3)} (hS : symOK S = true)
    (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) (A : Matrix (Fin 3) (Fin 3) K) (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) :
    ∃ Y : Matrix (Fin 3) (Fin 3) K, Y.det = 1 ∧ Y * A = A * Yᵀ ∧ Y ^ 13 = 1 ∧ Y ≠ 1 := by
  obtain ⟨a, ha, rfl⟩ := exists_toK hrep A
  obtain ⟨y, P, -, hc⟩ := sym_entry hS ha hA hdet
  obtain ⟨h1, h2, h3, h4, -⟩ := of_c1ok (K := K) hc
  exact ⟨y.toK K, h1, h2, h3, h4⟩

theorem c2_of {I : List M3} {Pr : List (M3 × M3 × M3)} (hI : invOK I = true)
    (hP : pairsOK I Pr = true) (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k)
    (T U : Matrix (Fin 3) (Fin 3) K) (hT : T.det = 1) (hU : U.det = 1) (hT2 : T * T = 1)
    (hT1 : T ≠ 1) (hU2 : U * U = 1) (hU1 : U ≠ 1) (hTU : T ≠ U) (hc : T * U = U * T) :
    ∃ G Gi : Matrix (Fin 3) (Fin 3) K, G.det = 1 ∧ G * T = T * G ∧ G * Gi = 1 ∧
      (U * (G * U * Gi)) ^ 4 = 1 ∧ (U * (G * U * Gi)) ^ 2 ≠ 1 := by
  obtain ⟨t, ht, rfl⟩ := exists_toK hrep T
  obtain ⟨u, hu, rfl⟩ := exists_toK hrep U
  obtain ⟨g, -, hg⟩ := mem_pairs hP (mem_I hI ht hT hT2 hT1) (mem_I hI hu hU hU2 hU1)
    (fun h => hTU (by rw [h]))
    (toK_inj (K := K) (R_mul _ _) (R_mul _ _) (by rw [toK_mul, toK_mul, hc]))
  obtain ⟨h1, h2, h3, h4, h5⟩ := of_c2ok (K := K) hg
  exact ⟨g.toK K, (adj g).toK K, h1, h2, h3, h4, h5⟩

theorem c3_one {I : List M3} {Pr : List (M3 × M3 × M3)} {W : List ((M3 × M3) × (M3 × M3 × M3))}
    (hI : invOK I = true) (hP : pairsOK I Pr = true) (h3 : c3OK Pr W = true)
    (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k) (T U : Matrix (Fin 3) (Fin 3) K)
    (hT : T.det = 1) (hU : U.det = 1) (hT2 : T * T = 1) (hT1 : T ≠ 1) (hU2 : U * U = 1)
    (hU1 : U ≠ 1) (hTU : T ≠ U) (hc : T * U = U * T) (hTo : T * Tᵀ = 1) (hUo : U * Uᵀ = 1) :
    ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
      X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * X₁ᵀ = 1 ∧ X₂ * T * X₂ᵀ = T ∧
      X₃ * U * X₃ᵀ = U ∧ ((X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃)) ^ 13 = 1 ∧
      (X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃) ≠ 1 := by
  obtain ⟨t, ht, rfl⟩ := exists_toK hrep T
  obtain ⟨u, hu, rfl⟩ := exists_toK hrep U
  obtain ⟨g, he, -⟩ := mem_pairs hP (mem_I hI ht hT hT2 hT1) (mem_I hI hu hU hU2 hU1)
    (fun h => hTU (by rw [h]))
    (toK_inj (K := K) (R_mul _ _) (R_mul _ _) (by rw [toK_mul, toK_mul, hc]))
  have hso : ∀ {x : M3}, (x.toK K).det = 1 → x.toK K * (x.toK K)ᵀ = 1 → isSOK one x = true :=
    fun hd h => by
      rw [isSOK_eq]
      exact isSO_of hd R_one (by rw [toK_one, Matrix.mul_one, h])
  have h3' := List.all_eq_true.1 h3 _ he
  simp only [hso hT hTo, hso hU hUo, Bool.and_true, Bool.not_true, Bool.false_or] at h3'
  obtain ⟨w, -, hw⟩ := List.any_eq_true.1 h3'
  simp only [Bool.and_eq_true] at hw
  have hg := hw.2
  rw [goodK_eq] at hg
  simp only [M3.good, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨h1S, h2S⟩, h3S⟩, h1i⟩, h2i⟩, h3i⟩, h13⟩ := hg
  obtain ⟨d1, s1⟩ := of_isSO (K := K) h1S
  obtain ⟨d2, s2⟩ := of_isSO (K := K) h2S
  obtain ⟨d3, s3⟩ := of_isSO (K := K) h3S
  simp only [M3.ord13, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h13
  rw [toK_mul, toK_one, Matrix.mul_one] at s2 s3
  rw [toK_one, Matrix.mul_one] at s1
  have hZ : (M3.mul (M3.mul (M3.conj t w.2.1) (M3.conj t w.2.2.1)) (M3.conj t w.2.2.2)).toK K =
      (w.2.1.toK K * t.toK K * (M3.adj w.2.1).toK K) *
        (w.2.2.1.toK K * t.toK K * (M3.adj w.2.2.1).toK K) *
        (w.2.2.2.toK K * t.toK K * (M3.adj w.2.2.2).toK K) := by
    simp only [M3.conj, toK_mul, Matrix.mul_assoc]
  refine ⟨w.2.1.toK K, (M3.adj w.2.1).toK K, w.2.2.1.toK K, (M3.adj w.2.2.1).toK K,
    w.2.2.2.toK K, (M3.adj w.2.2.2).toK K, d1, d2, d3, ?_, ?_, ?_, s1, s2, s3, ?_, ?_⟩
  · rw [← toK_mul, h1i, toK_one]
  · rw [← toK_mul, h2i, toK_one]
  · rw [← toK_mul, h3i, toK_one]
  · rw [← hZ, ← toK_pow, h13.1, toK_one]
  · rw [← hZ]
    exact toK_ne_one (R_mul _ _) h13.2

omit [CharP K 3] in
theorem transport
    (H : ∀ T' U' : Matrix (Fin 3) (Fin 3) K, T'.det = 1 → U'.det = 1 → T' * T' = 1 → T' ≠ 1 →
      U' * U' = 1 → U' ≠ 1 → T' ≠ U' → T' * U' = U' * T' → T' * T'ᵀ = 1 → U' * U'ᵀ = 1 →
      ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
        X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * X₁ᵀ = 1 ∧ X₂ * T' * X₂ᵀ = T' ∧
        X₃ * U' * X₃ᵀ = U' ∧ ((X₁ * T' * Y₁) * (X₂ * T' * Y₂) * (X₃ * T' * Y₃)) ^ 13 = 1 ∧
        (X₁ * T' * Y₁) * (X₂ * T' * Y₂) * (X₃ * T' * Y₃) ≠ 1)
    {P Pi A T U : Matrix (Fin 3) (Fin 3) K} (c : K) (hPdet : P.det = 1) (hPPi : P * Pi = 1)
    (hPiP : Pi * P = 1) (hcc : c * c = 1) (hQ : P * A * Pᵀ = c • 1) (hT : T.det = 1)
    (hU : U.det = 1) (hT2 : T * T = 1) (hT1 : T ≠ 1) (hU2 : U * U = 1) (hU1 : U ≠ 1)
    (hTU : T ≠ U) (hc : T * U = U * T) (hTA : T * A * Tᵀ = A) (hUA : U * A * Uᵀ = A) :
    ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
      X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * A * X₁ᵀ = A ∧
      X₂ * (T * A) * X₂ᵀ = T * A ∧ X₃ * (U * A) * X₃ᵀ = U * A ∧
      ((X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃)) ^ 13 = 1 ∧
      (X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃) ≠ 1 := by
  have hPidet : Pi.det = 1 := by
    have := congrArg Matrix.det hPiP
    rwa [Matrix.det_mul, hPdet, mul_one, Matrix.det_one] at this
  have mulφ : ∀ X Y : Matrix (Fin 3) (Fin 3) K, (Pi * X * P) * (Pi * Y * P) = Pi * (X * Y) * P := by
    intro X Y
    calc (Pi * X * P) * (Pi * Y * P) = Pi * X * (P * Pi) * Y * P := by
          simp only [Matrix.mul_assoc]
      _ = Pi * (X * Y) * P := by
          rw [hPPi, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have mulψ : ∀ X Y : Matrix (Fin 3) (Fin 3) K, (P * X * Pi) * (P * Y * Pi) = P * (X * Y) * Pi := by
    intro X Y
    calc (P * X * Pi) * (P * Y * Pi) = P * X * (Pi * P) * Y * Pi := by
          simp only [Matrix.mul_assoc]
      _ = P * (X * Y) * Pi := by
          rw [hPiP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have unφ : ∀ X : Matrix (Fin 3) (Fin 3) K, P * (Pi * X * P) * Pi = X := by
    intro X
    calc P * (Pi * X * P) * Pi = (P * Pi) * X * (P * Pi) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  have unψ : ∀ X : Matrix (Fin 3) (Fin 3) K, Pi * (P * X * Pi) * P = X := by
    intro X
    calc Pi * (P * X * Pi) * P = (Pi * P) * X * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  have powφ : ∀ (Z : Matrix (Fin 3) (Fin 3) K) (n : ℕ), (Pi * Z * P) ^ n = Pi * Z ^ n * P := by
    intro Z n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPiP]
    | succ n ih => rw [pow_succ, ih, mulφ, ← pow_succ]
  have hAc : A = c • (Pi * Piᵀ) := by
    calc A = (Pi * P) * A * (Pi * P)ᵀ := by
          rw [hPiP, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Pi * (P * A * Pᵀ) * Piᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = c • (Pi * Piᵀ) := by rw [hQ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have ortho : ∀ X : Matrix (Fin 3) (Fin 3) K, X * A * Xᵀ = A →
      (P * X * Pi) * (P * X * Pi)ᵀ = 1 := by
    intro X hX
    have key : c • ((P * X * Pi) * (P * X * Pi)ᵀ) = c • 1 := by
      calc c • ((P * X * Pi) * (P * X * Pi)ᵀ) = P * (X * (c • (Pi * Piᵀ)) * Xᵀ) * Pᵀ := by
            simp only [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = c • 1 := by rw [← hAc, hX, hQ]
    calc (P * X * Pi) * (P * X * Pi)ᵀ = (c * c) • ((P * X * Pi) * (P * X * Pi)ᵀ) := by
          rw [hcc, one_smul]
      _ = c • (c • 1) := by rw [mul_smul, key]
      _ = 1 := by rw [smul_smul, hcc, one_smul]
  have detψ : ∀ X : Matrix (Fin 3) (Fin 3) K, X.det = 1 → (P * X * Pi).det = 1 := by
    intro X hX
    rw [Matrix.det_mul, Matrix.det_mul, hPdet, hX, hPidet, one_mul, one_mul]
  have detφ : ∀ X : Matrix (Fin 3) (Fin 3) K, X.det = 1 → (Pi * X * P).det = 1 := by
    intro X hX
    rw [Matrix.det_mul, Matrix.det_mul, hPdet, hX, hPidet, one_mul, one_mul]
  have neψ : ∀ X Y : Matrix (Fin 3) (Fin 3) K, X ≠ Y → P * X * Pi ≠ P * Y * Pi := by
    intro X Y hXY h
    apply hXY
    have := congrArg (fun Z => Pi * Z * P) h
    simpa only [unψ] using this
  have hone : P * 1 * Pi = 1 := by rw [Matrix.mul_one, hPPi]
  obtain ⟨X₁, Y₁, X₂, Y₂, X₃, Y₃, d1, d2, d3, i1, i2, i3, s1, s2, s3, z13, z1⟩ :=
    H (P * T * Pi) (P * U * Pi) (detψ T hT) (detψ U hU) (by rw [mulψ, hT2, hone])
      (fun h => neψ T 1 hT1 (h.trans hone.symm)) (by rw [mulψ, hU2, hone])
      (fun h => neψ U 1 hU1 (h.trans hone.symm)) (neψ T U hTU) (by rw [mulψ, mulψ, hc])
      (ortho T hTA) (ortho U hUA)
  have formφ : ∀ X B : Matrix (Fin 3) (Fin 3) K, X * B * Xᵀ = B →
      (Pi * X * P) * (c • (Pi * B * Piᵀ)) * (Pi * X * P)ᵀ = c • (Pi * B * Piᵀ) := by
    intro X B hX
    calc (Pi * X * P) * (c • (Pi * B * Piᵀ)) * (Pi * X * P)ᵀ
        = c • (Pi * (X * (P * Pi) * B * (P * Pi)ᵀ * Xᵀ) * Piᵀ) := by
          simp only [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = c • (Pi * B * Piᵀ) := by
          rw [hPPi, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, hX]
  have hA1 : A = c • (Pi * 1 * Piᵀ) := by rw [Matrix.mul_one]; exact hAc
  have hXA : ∀ X : Matrix (Fin 3) (Fin 3) K, X * A = c • (Pi * (P * X * Pi) * Piᵀ) := by
    intro X
    rw [hAc, Matrix.mul_smul]
    simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hprod : ∀ X Y : Matrix (Fin 3) (Fin 3) K,
      (Pi * X * P) * T * (Pi * Y * P) = Pi * (X * (P * T * Pi) * Y) * P := by
    intro X Y
    simp only [Matrix.mul_assoc]
  refine ⟨Pi * X₁ * P, Pi * Y₁ * P, Pi * X₂ * P, Pi * Y₂ * P, Pi * X₃ * P, Pi * Y₃ * P,
    detφ X₁ d1, detφ X₂ d2, detφ X₃ d3, by rw [mulφ, i1, Matrix.mul_one, hPiP],
    by rw [mulφ, i2, Matrix.mul_one, hPiP], by rw [mulφ, i3, Matrix.mul_one, hPiP], ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hA1]
    exact formφ X₁ 1 (by rw [Matrix.mul_one]; exact s1)
  · rw [hXA T]
    exact formφ X₂ _ s2
  · rw [hXA U]
    exact formφ X₃ _ s3
  · rw [hprod, hprod, hprod, mulφ, mulφ, powφ, z13, Matrix.mul_one, hPiP]
  · rw [hprod, hprod, hprod, mulφ, mulφ]
    intro h
    apply z1
    have := congrArg (fun Z => P * Z * Pi) h
    simpa only [unφ, Matrix.mul_one, hPPi] using this

theorem c3_of {I : List M3} {S : List (M3 × M3 × M3)} {Pr : List (M3 × M3 × M3)}
    {W : List ((M3 × M3) × (M3 × M3 × M3))} (hI : invOK I = true) (hS : symOK S = true)
    (hP : pairsOK I Pr = true) (h3 : c3OK Pr W = true)
    (hrep : ∀ k : K, ∃ n : ℕ, n < 3 ∧ (n : K) = k)
    (A T U : Matrix (Fin 3) (Fin 3) K) (hA : Aᵀ = A) (hAdet : A.det ≠ 0) (hT : T.det = 1)
    (hU : U.det = 1) (hT2 : T * T = 1) (hT1 : T ≠ 1) (hU2 : U * U = 1) (hU1 : U ≠ 1)
    (hTU : T ≠ U) (hc : T * U = U * T) (hTA : T * A * Tᵀ = A) (hUA : U * A * Uᵀ = A) :
    ∃ X₁ Y₁ X₂ Y₂ X₃ Y₃ : Matrix (Fin 3) (Fin 3) K, X₁.det = 1 ∧ X₂.det = 1 ∧ X₃.det = 1 ∧
      X₁ * Y₁ = 1 ∧ X₂ * Y₂ = 1 ∧ X₃ * Y₃ = 1 ∧ X₁ * A * X₁ᵀ = A ∧
      X₂ * (T * A) * X₂ᵀ = T * A ∧ X₃ * (U * A) * X₃ᵀ = U * A ∧
      ((X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃)) ^ 13 = 1 ∧
      (X₁ * T * Y₁) * (X₂ * T * Y₂) * (X₃ * T * Y₃) ≠ 1 := by
  obtain ⟨a, ha, rfl⟩ := exists_toK hrep A
  obtain ⟨y, p, -, hc1⟩ := sym_entry hS ha hA hAdet
  obtain ⟨-, -, -, -, hPdet, hPPi, hPiP, c, hcc, hQ⟩ := of_c1ok (K := K) hc1
  exact transport (fun T' U' => c3_one hI hP h3 hrep T' U') c hPdet hPPi hPiP hcc hQ hT hU hT2
    hT1 hU2 hU1 hTU hc hTA hUA

end CFSG.KC.B45L33

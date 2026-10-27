module

public import CFSG.ClassicalInvolution.Phan.PhanQ27Alg

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Hyp

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem inW2_add' {x y : V8 K} (hx : InW2 x) (hy : InW2 y) : InW2 (x + y) := by
  intro i hi
  obtain ⟨a1, a2⟩ := hx i hi
  obtain ⟨b1, b2⟩ := hy i hi
  simp [a1, a2, b1, b2]

theorem inW2_smul' (κ : K) {x : V8 K} (hx : InW2 x) : InW2 (κ • x) := by
  intro i hi
  obtain ⟨a1, a2⟩ := hx i hi
  simp [a1, a2]

theorem inW0_add' {x y : V8 K} (hx : InW0 x) (hy : InW0 y) : InW0 (x + y) := by
  intro i hi
  obtain ⟨a1, a2⟩ := hx i hi
  obtain ⟨b1, b2⟩ := hy i hi
  simp [a1, a2, b1, b2]

theorem inW0_smul' (κ : K) {x : V8 K} (hx : InW0 x) : InW0 (κ • x) := by
  intro i hi
  obtain ⟨a1, a2⟩ := hx i hi
  simp [a1, a2]

structure HypBasis (r r' s s' : V8 K) : Prop where
  wr : InW2 r
  wr' : InW2 r'
  ws : InW2 s
  ws' : InW2 s'
  fr : conj D r = r
  fr' : conj D r' = r'
  fs : conj D s = s
  fs' : conj D s' = s'
  qr : Q8 r = 0
  qr' : Q8 r' = 0
  qs : Q8 s = 0
  qs' : Q8 s' = 0
  rr' : B8 r r' = 1
  rs : B8 r s = 0
  rs' : B8 r s' = 0
  r's : B8 r' s = 0
  r's' : B8 r' s' = 0
  ss' : B8 s s' = 1

variable {D}

@[expose] def HypBasis.vec (r r' s s' : V8 K) (x1 x2 x3 x4 : K) : V8 K :=
  x1 • r + x2 • r' + x3 • s + x4 • s'

theorem HypBasis.inW2_vec {r r' s s' : V8 K} (H : HypBasis D r r' s s') (x1 x2 x3 x4 : K) :
    InW2 (HypBasis.vec r r' s s' x1 x2 x3 x4) :=
  inW2_add' (inW2_add' (inW2_add' (inW2_smul' _ H.wr) (inW2_smul' _ H.wr')) (inW2_smul' _ H.ws))
    (inW2_smul' _ H.ws')

theorem HypBasis.conj_vec {r r' s s' : V8 K} (H : HypBasis D r r' s s') (x1 x2 x3 x4 : K) :
    conj D (HypBasis.vec r r' s s' x1 x2 x3 x4) =
      HypBasis.vec r r' s s' (D.τ x1) (D.τ x2) (D.τ x3) (D.τ x4) := by
  unfold HypBasis.vec
  rw [conj_add, conj_add, conj_add, conj_smul, conj_smul, conj_smul, conj_smul, H.fr, H.fr', H.fs,
    H.fs']

theorem HypBasis.B8_vec {r r' s s' : V8 K} (H : HypBasis D r r' s s')
    (x1 x2 x3 x4 y1 y2 y3 y4 : K) :
    B8 (HypBasis.vec r r' s s' x1 x2 x3 x4) (HypBasis.vec r r' s s' y1 y2 y3 y4) =
      x1 * y2 + x2 * y1 + x3 * y4 + x4 * y3 := by
  have rr : B8 r r = 0 := B8_zero_self H.qr
  have r'r' : B8 r' r' = 0 := B8_zero_self H.qr'
  have ss : B8 s s = 0 := B8_zero_self H.qs
  have s's' : B8 s' s' = 0 := B8_zero_self H.qs'
  have r'r : B8 r' r = 1 := by rw [B8_comm]; exact H.rr'
  have sr : B8 s r = 0 := by rw [B8_comm]; exact H.rs
  have s'r : B8 s' r = 0 := by rw [B8_comm]; exact H.rs'
  have sr' : B8 s r' = 0 := by rw [B8_comm]; exact H.r's
  have s'r' : B8 s' r' = 0 := by rw [B8_comm]; exact H.r's'
  have s's : B8 s' s = 1 := by rw [B8_comm]; exact H.ss'
  unfold HypBasis.vec
  simp only [B8_add_left, B8_add_right, B8_smul_left, B8_smul_right, rr, r'r', ss, s's', r'r,
    sr, s'r, sr', s'r', s's, H.rr', H.rs, H.rs', H.r's, H.r's', H.ss']
  ring

theorem HypBasis.Q8_vec (h2 : (2 : K) ≠ 0) {r r' s s' : V8 K} (H : HypBasis D r r' s s')
    (x1 x2 x3 x4 : K) : Q8 (HypBasis.vec r r' s s' x1 x2 x3 x4) = x1 * x2 + x3 * x4 := by
  have h := H.B8_vec x1 x2 x3 x4 x1 x2 x3 x4
  rw [B8_self] at h
  apply mul_left_cancel₀ h2
  rw [h]
  ring

theorem exists_hypBasis {r1 r2 r3 r4 : K} (hr1 : D.τ r1 = r1) (hr2 : D.τ r2 = r2)
    (hr3 : D.τ r3 = r3) (hr4 : D.τ r4 = r4) (hr : r1 * r3 + r2 * r4 = 0)
    (hne : r1 ≠ 0 ∨ r2 ≠ 0 ∨ r3 ≠ 0 ∨ r4 ≠ 0) :
    ∃ r' s s' : V8 K, HypBasis D (wvec r1 r2 r3 r4) r' s s' := by
  have hQ : Q8 (wvec r1 r2 r3 r4) = 0 := by rw [Q8_wvec]; exact hr
  have hF : conj D (wvec r1 r2 r3 r4) = wvec r1 r2 r3 r4 := by
    rw [conj_wvec, hr1, hr2, hr3, hr4]
  by_cases h1 : r1 = 0
  · by_cases h2 : r2 = 0
    · by_cases h3 : r3 = 0
      · have h4 : r4 ≠ 0 := by
          rcases hne with h | h | h | h
          · exact absurd h1 h
          · exact absurd h2 h
          · exact absurd h3 h
          · exact h
        refine ⟨wvec 0 (r4⁻¹) 0 0, wvec 0 0 1 0, wvec 1 0 0 0, ?_⟩
        refine ⟨inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, hF, ?_,
          ?_, ?_, hQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [conj_wvec, map_inv₀, hr4]; simp
        · rw [conj_wvec]; simp
        · rw [conj_wvec]; simp
        · rw [Q8_wvec]; ring
        · rw [Q8_wvec]; ring
        · rw [Q8_wvec]; ring
        · rw [B8_wvec_wvec, h1, h2, h3]; field_simp; ring
        · rw [B8_wvec_wvec, h1, h2, h3]; ring
        · rw [B8_wvec_wvec, h1, h2, h3]; ring
        · rw [B8_wvec_wvec]; ring
        · rw [B8_wvec_wvec]; ring
        · rw [B8_wvec_wvec]; ring
      · refine ⟨wvec (r3⁻¹) 0 0 0, wvec 0 0 0 1, wvec (-r4 * r3⁻¹) 1 0 0, ?_⟩
        refine ⟨inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, hF, ?_,
          ?_, ?_, hQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [conj_wvec, map_inv₀, hr3]; simp
        · rw [conj_wvec]; simp
        · rw [conj_wvec, map_mul, map_neg, map_inv₀, hr3, hr4]; simp
        · rw [Q8_wvec]; ring
        · rw [Q8_wvec]; ring
        · rw [Q8_wvec]; ring
        · rw [B8_wvec_wvec, h1, h2]; field_simp; ring
        · rw [B8_wvec_wvec, h1, h2]; ring
        · rw [B8_wvec_wvec, h1, h2]; field_simp; ring
        · rw [B8_wvec_wvec]; ring
        · rw [B8_wvec_wvec]; ring
        · rw [B8_wvec_wvec]; ring
    · refine ⟨wvec 0 0 0 (r2⁻¹), wvec 1 0 0 (-r3 * r2⁻¹), wvec 0 0 1 0, ?_⟩
      refine ⟨inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, hF, ?_,
        ?_, ?_, hQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [conj_wvec, map_inv₀, hr2]; simp
      · rw [conj_wvec, map_mul, map_neg, map_inv₀, hr3, hr2]; simp
      · rw [conj_wvec]; simp
      · rw [Q8_wvec]; ring
      · rw [Q8_wvec]; ring
      · rw [Q8_wvec]; ring
      · rw [B8_wvec_wvec, h1]; field_simp; ring
      · rw [B8_wvec_wvec, h1]; field_simp; ring
      · rw [B8_wvec_wvec, h1]; ring
      · rw [B8_wvec_wvec]; ring
      · rw [B8_wvec_wvec]; ring
      · rw [B8_wvec_wvec]; ring
  · refine ⟨wvec 0 0 (r1⁻¹) 0, wvec 0 1 (-r4 * r1⁻¹) 0, wvec 0 0 (-r2 * r1⁻¹) 1, ?_⟩
    refine ⟨inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, inW2_wvec _ _ _ _, hF, ?_,
      ?_, ?_, hQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [conj_wvec, map_inv₀, hr1]; simp
    · rw [conj_wvec, map_mul, map_neg, map_inv₀, hr4, hr1]; simp
    · rw [conj_wvec, map_mul, map_neg, map_inv₀, hr2, hr1]; simp
    · rw [Q8_wvec]; ring
    · rw [Q8_wvec]; ring
    · rw [Q8_wvec]; ring
    · rw [B8_wvec_wvec]; field_simp; ring
    · rw [B8_wvec_wvec]; field_simp; ring
    · rw [B8_wvec_wvec]; field_simp; ring
    · rw [B8_wvec_wvec]; ring
    · rw [B8_wvec_wvec]; ring
    · rw [B8_wvec_wvec]; ring

end Hyp

end CFSG.ClassicalInvolution.PhanQ

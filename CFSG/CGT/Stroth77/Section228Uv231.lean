module

public import CFSG.CGT.Stroth77.Section228Uv

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

theorem t231_uv_c {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φuv Torus.c =
      (-i : ℤ) • Torus.c + (4 + 8 * (2 : ℤ) ^ s) • Torus.a + (-4 : ℤ) • Torus.b := by
  refine (matAct_gen_of (Type231.uvM s i F H) (Type231.compat_uv h) 0 (-i)
    (4 + 8 * (2 : ℤ) ^ s) (-4) ?_ ?_ ?_).trans ?_ <;>
    first
      | simp [Type231.uvM, Type231.uvA, Type231.tM, Type231.ρM, ofCols_apply,
          Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_mul]
      | simp [Type231.action, SigmaFourAction.ofMatEq, Torus.c, Torus.a, Torus.b]

theorem t231_uv_a {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φuv Torus.a =
      (2 * (2 : ℤ) ^ s + F * i) • Torus.c + (-5 * i + 8 * (2 : ℤ) ^ s) • Torus.a +
        (2 * i + 4 * (2 : ℤ) ^ s) • Torus.b := by
  refine (matAct_gen_of (Type231.uvM s i F H) (Type231.compat_uv h) 1
    (2 * (2 : ℤ) ^ s + F * i) (-5 * i + 8 * (2 : ℤ) ^ s) (2 * i + 4 * (2 : ℤ) ^ s)
    ?_ ?_ ?_).trans ?_ <;>
    first
      | simp [Type231.uvM, Type231.uvA, Type231.tM, Type231.ρM, ofCols_apply,
          Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_mul]
      | simp [Type231.action, SigmaFourAction.ofMatEq, Torus.c, Torus.a, Torus.b]

theorem t231_uv_b {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φuv Torus.b =
      (-384 * H ^ 3 - 88 * ((2 : ℤ) ^ s) ^ 2 + 512 * (2 : ℤ) ^ s * H -
          3296 * H ^ 2 + 1208 * (2 : ℤ) ^ s - 9142 * H - 8265) • Torus.c +
        (-256 * (2 : ℤ) ^ s * H ^ 2 - 96 * ((2 : ℤ) ^ s) ^ 2 -
          192 * (2 : ℤ) ^ s * H - 1920 * H ^ 2 + 972 * (2 : ℤ) ^ s - 9088 * H -
          10754) • Torus.a +
        (-256 * (2 : ℤ) ^ s * H ^ 2 - 80 * ((2 : ℤ) ^ s) ^ 2 -
          928 * (2 : ℤ) ^ s * H + 192 * H ^ 2 - 768 * (2 : ℤ) ^ s + 928 * H +
          1121) • Torus.b := by
  refine (matAct_gen_of (Type231.uvM s i F H) (Type231.compat_uv h) 2
    (-384 * H ^ 3 - 88 * ((2 : ℤ) ^ s) ^ 2 + 512 * (2 : ℤ) ^ s * H -
      3296 * H ^ 2 + 1208 * (2 : ℤ) ^ s - 9142 * H - 8265)
    (-256 * (2 : ℤ) ^ s * H ^ 2 - 96 * ((2 : ℤ) ^ s) ^ 2 -
      192 * (2 : ℤ) ^ s * H - 1920 * H ^ 2 + 972 * (2 : ℤ) ^ s - 9088 * H - 10754)
    (-256 * (2 : ℤ) ^ s * H ^ 2 - 80 * ((2 : ℤ) ^ s) ^ 2 -
      928 * (2 : ℤ) ^ s * H + 192 * H ^ 2 - 768 * (2 : ℤ) ^ s + 928 * H + 1121)
    ?_ ?_ ?_).trans ?_ <;>
    first
      | (simp [Type231.uvM, Type231.uvA, Type231.tM, Type231.ρM, ofCols_apply,
          Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, pow_mul,
          h.hi, h.hF] <;> ring1)
      | simp [Type231.action, SigmaFourAction.ofMatEq, Torus.c, Torus.a, Torus.b]

theorem t231_u_a {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φu Torus.a =
      (-2 * F + 2 * (2 : ℤ) ^ s) • Torus.c + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (Type231.uM s i F H) (Type231.compat_u h) 1
    (-2 * F + 2 * (2 : ℤ) ^ s) 0 1 ?_ ?_ ?_).trans ?_ <;>
    first
      | simp [Type231.uM, uMat, ofCols_apply]
      | simp [Type231.action, SigmaFourAction.ofMatEq, Torus.c, Torus.a, Torus.b]

theorem t231_u_b {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φu Torus.b =
      (-(-2 * F + 2 * (2 : ℤ) ^ s) * (-1 + 2 * (2 : ℤ) ^ s)) • Torus.c +
        (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (Type231.uM s i F H) (Type231.compat_u h) 2
    (-(-2 * F + 2 * (2 : ℤ) ^ s) * (-1 + 2 * (2 : ℤ) ^ s)) 1 0 ?_ ?_ ?_).trans ?_ <;>
    first
      | (simp [Type231.uM, uMat, ofCols_apply] <;> ring1)
      | simp [Type231.action, SigmaFourAction.ofMatEq, Torus.c, Torus.a, Torus.b]

theorem t231_u_a_half (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φu
        ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k)) =
      (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) := by
  show (Type231.action (Type231.data s)).φu
      ((2 ^ (s + 3) : ℕ) • Torus.a (k := Type231.k s)) =
    (2 ^ (s + 3) : ℕ) • Torus.b (k := Type231.k s)
  have hva : (2 ^ (s + 3) : ℕ) • Torus.a (k := Type231.k s) =
      Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 3), 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.a, Torus.b, Torus.c]
  have hvb : (2 ^ (s + 3) : ℕ) • Torus.b (k := Type231.k s) =
      Torus.ofInt (Type231.k s) ![0, 0, (2 : ℤ) ^ (s + 3)] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.a, Torus.b, Torus.c]
  rw [hva, hvb]
  change matAct (Type231.k s) (Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4))
      (Type120.GV (s + 4))) (Type231.compat_u (Type231.data s))
      (Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 3), 0]) =
    Torus.ofInt (Type231.k s) ![0, 0, (2 : ℤ) ^ (s + 3)]
  rw [matAct_ofInt]
  have hmul : Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) *ᵥ
      ![0, (2 : ℤ) ^ (s + 3), 0] =
      ![((2 : ℤ) ^ (s + 3)) *
          (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s), 0, (2 : ℤ) ^ (s + 3)] := by
    rw [show Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) =
        uMat ![-1 + 2 * (2 : ℤ) ^ s, 0, 0] (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s)
        from rfl, uMat_mulVec]
    funext j
    fin_cases j <;> simp <;> ring
  rw [hmul, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change ((2 : ℤ) ^ (s + 3)) *
        (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) ≡ 0 [ZMOD (2 : ℤ) ^ (s + 2)]
    rw [Int.modEq_iff_dvd]
    exact ⟨-4 * ((2 : ℤ) ^ s - Type120.FV (s + 4)),
      by rw [show s + 3 = (s + 2) + 1 by omega, pow_succ]; ring⟩
  · exact Int.ModEq.refl _
  · exact Int.ModEq.refl _

theorem t231_uv_fixes_a_half (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φuv
        ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k)) =
      (2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k) := by
  show (Type231.action (Type231.data s)).φuv
      ((2 ^ (s + 3) : ℕ) • Torus.a (k := Type231.k s)) =
    (2 ^ (s + 3) : ℕ) • Torus.a (k := Type231.k s)
  have hva : (2 ^ (s + 3) : ℕ) • Torus.a (k := Type231.k s) =
      Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 3), 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    simp [Torus.a, Torus.b, Torus.c]
  conv_lhs => rw [hva]
  conv_rhs => rw [hva]
  change matAct (Type231.k s) (Type231.uvM s (Type120.iV (s + 4)) (Type120.FV (s + 4))
      (Type120.GV (s + 4))) (Type231.compat_uv (Type231.data s))
      (Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 3), 0]) =
    Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 3), 0]
  rw [matAct_ofInt]
  have hmul : Type231.uvM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) *ᵥ
      ![0, (2 : ℤ) ^ (s + 3), 0] =
      ![((2 : ℤ) ^ (s + 3)) * (2 * (2 : ℤ) ^ s +
          Type120.FV (s + 4) * Type120.iV (s + 4)),
        ((2 : ℤ) ^ (s + 3)) * (-5 * Type120.iV (s + 4) + 8 * (2 : ℤ) ^ s),
        ((2 : ℤ) ^ (s + 3)) * (2 * Type120.iV (s + 4) + 4 * (2 : ℤ) ^ s)] := by
    rw [show Type231.uvM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) =
        ofCols ![-Type120.iV (s + 4), 4 + 8 * (2 : ℤ) ^ s, -4]
          (Type231.uvA s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)))
          (Type231.ρM *ᵥ (Type231.tM s (Type120.iV (s + 4)) (Type120.FV (s + 4))
            (Type120.GV (s + 4)) *ᵥ Type231.uvA s (Type120.iV (s + 4))
              (Type120.FV (s + 4)) (Type120.GV (s + 4)))) from rfl, ofCols_mulVec]
    funext j
    fin_cases j <;> simp [Type231.uvA] <;> ring
  rw [hmul, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change ((2 : ℤ) ^ (s + 3)) * (2 * (2 : ℤ) ^ s +
        Type120.FV (s + 4) * Type120.iV (s + 4)) ≡ 0 [ZMOD (2 : ℤ) ^ (s + 2)]
    rw [Int.modEq_iff_dvd]
    exact ⟨-2 * (2 * (2 : ℤ) ^ s + Type120.FV (s + 4) * Type120.iV (s + 4)),
      by rw [show s + 3 = (s + 2) + 1 by omega, pow_succ]; ring⟩
  · change ((2 : ℤ) ^ (s + 3)) * (-5 * Type120.iV (s + 4) + 8 * (2 : ℤ) ^ s) ≡
      (2 : ℤ) ^ (s + 3) [ZMOD (2 : ℤ) ^ (s + 4)]
    rw [Int.modEq_iff_dvd]
    rw [show Type120.iV (s + 4) = 8 * Type120.GV (s + 4) + 19 from (Type231.data s).hi]
    refine ⟨20 * Type120.GV (s + 4) + 48 - 4 * (2 : ℤ) ^ s, ?_⟩
    rw [show s + 3 = (s + 2) + 1 by omega, pow_succ]
    ring
  · change ((2 : ℤ) ^ (s + 3)) * (2 * Type120.iV (s + 4) + 4 * (2 : ℤ) ^ s) ≡
      0 [ZMOD (2 : ℤ) ^ (s + 4)]
    rw [Int.modEq_iff_dvd]
    exact ⟨-(Type120.iV (s + 4) + 2 * (2 : ℤ) ^ s),
      by rw [show s + 3 = (s + 2) + 1 by omega, pow_succ]; ring⟩

theorem t231_uv_fixes_b_half (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φuv
        ((2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k)) =
      (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) := by
  have hcomm : ∀ v : Torus (StrothTypeIndex.t231 s hs).k,
      (StrothTypeIndex.t231 s hs).action.φu
          ((StrothTypeIndex.t231 s hs).action.φuv v) =
        (StrothTypeIndex.t231 s hs).action.φuv
          ((StrothTypeIndex.t231 s hs).action.φu v) :=
    fun v => DFunLike.congr_fun (StrothTypeIndex.t231 s hs).action.rels.uv_comm_u v
  calc (StrothTypeIndex.t231 s hs).action.φuv
        ((2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k))
      = (StrothTypeIndex.t231 s hs).action.φuv
          ((StrothTypeIndex.t231 s hs).action.φu
            ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k))) := by
          rw [t231_u_a_half s hs]
    _ = (StrothTypeIndex.t231 s hs).action.φu
          ((StrothTypeIndex.t231 s hs).action.φuv
            ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k))) :=
          (hcomm _).symm
    _ = (StrothTypeIndex.t231 s hs).action.φu
          ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k)) := by
          rw [t231_uv_fixes_a_half s hs]
    _ = (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) :=
          t231_u_a_half s hs

theorem t231_u_swaps_a_half {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    (dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)) :
    dD.u⁻¹ * ((dD.a : G) ^ 2 ^ (s + 3)) * dD.u = (dD.b : G) ^ 2 ^ (s + 3) := by
  have h := dD.conj_ofTorus dD.u_mem dD.u_conj
    ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k))
  rw [t231_u_a_half s hs] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq] at h
  rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq] at h
  exact h

theorem t231_φu_ab_half (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φu
        ((2 ^ (s + 2) : ℕ) • (Torus.a (k := (StrothTypeIndex.t231 s hs).k) +
          Torus.b (k := (StrothTypeIndex.t231 s hs).k))) =
      (2 ^ (s + 2) : ℕ) • (Torus.a (k := (StrothTypeIndex.t231 s hs).k) +
        Torus.b (k := (StrothTypeIndex.t231 s hs).k)) := by
  show (Type231.action (Type231.data s)).φu
      ((2 ^ (s + 2) : ℕ) • (Torus.a (k := Type231.k s) + Torus.b (k := Type231.k s))) =
    (2 ^ (s + 2) : ℕ) • (Torus.a (k := Type231.k s) + Torus.b (k := Type231.k s))
  have hva : (2 ^ (s + 2) : ℕ) • (Torus.a (k := Type231.k s) + Torus.b (k := Type231.k s)) =
      Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply, zsmul_eq_mul]
  conv_lhs => rw [hva]
  conv_rhs => rw [hva]
  change matAct (Type231.k s) (Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4))
      (Type120.GV (s + 4))) (Type231.compat_u (Type231.data s))
      (Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)]) =
    Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)]
  rw [matAct_ofInt]
  have hmul : Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) *ᵥ
      ![0, (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)] =
      ![((2 : ℤ) ^ (s + 2)) * ((-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) -
        (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) * (-1 + 2 * (2 : ℤ) ^ s)),
        (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)] := by
    rw [show Type231.uM s (Type120.iV (s + 4)) (Type120.FV (s + 4)) (Type120.GV (s + 4)) =
        uMat ![-1 + 2 * (2 : ℤ) ^ s, 0, 0] (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s)
        from rfl, uMat_mulVec]
    funext j
    fin_cases j <;> simp <;> ring
  rw [hmul, Torus.ofInt_eq_ofInt_iff]
  intro j
  fin_cases j
  · change ((2 : ℤ) ^ (s + 2)) *
        ((-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) -
          (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) * (-1 + 2 * (2 : ℤ) ^ s)) ≡
      0 [ZMOD (2 : ℤ) ^ (s + 2)]
    rw [Int.modEq_iff_dvd]
    refine ⟨-2 * (-2 * Type120.FV (s + 4) + 2 * (2 : ℤ) ^ s) *
      (1 - (2 : ℤ) ^ s), ?_⟩
    ring
  · exact Int.ModEq.refl _
  · exact Int.ModEq.refl _

theorem t231_φuv_a_add_b {s : ℕ} {i F H : ℤ} (h : Type231.Data s i F H) :
    (Type231.action h).φuv (Torus.a + Torus.b) =
      Torus.ofInt (Type231.k s) ![
        -384 * H ^ 3 - 88 * ((2 : ℤ) ^ s) ^ 2 + 512 * (2 : ℤ) ^ s * H -
          3264 * H ^ 2 + 1210 * (2 : ℤ) ^ s - 8994 * H - 8094,
        -256 * (2 : ℤ) ^ s * H ^ 2 - 96 * ((2 : ℤ) ^ s) ^ 2 -
          192 * (2 : ℤ) ^ s * H - 1920 * H ^ 2 + 980 * (2 : ℤ) ^ s - 9128 * H - 10849,
        -256 * (2 : ℤ) ^ s * H ^ 2 - 80 * ((2 : ℤ) ^ s) ^ 2 -
          928 * (2 : ℤ) ^ s * H + 192 * H ^ 2 - 764 * (2 : ℤ) ^ s + 944 * H + 1159] := by
  rw [map_add, t231_uv_a h, t231_uv_b h]
  funext j
  fin_cases j <;>
    simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply, Torus.ofInt, zsmul_eq_mul,
      h.hi, h.hF]
  all_goals ring

theorem t231_uv_preimage (s : ℕ) (hs : 1 ≤ s) :
    ∃ v : Torus (StrothTypeIndex.t231 s hs).k,
      (StrothTypeIndex.t231 s hs).action.φuv v - v =
        (2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) • (Torus.a + Torus.b) := by
  have hnexp : (StrothTypeIndex.t231 s hs).n - 2 = s + 2 := by
    have hn : (StrothTypeIndex.t231 s hs).n = s + 4 := by
      simp [StrothTypeIndex.n, StrothTypeIndex.k, Type231.k]
    omega
  rw [hnexp]
  show ∃ v : Torus (Type231.k s),
    (Type231.action (Type231.data s)).φuv v - v =
      (2 ^ (s + 2) : ℕ) • (Torus.a (k := Type231.k s) + Torus.b (k := Type231.k s))
  let N : ℤ := -5 * (2 : ℤ) ^ (s + 1)
  let v : Torus (Type231.k s) :=
    Torus.ofInt (Type231.k s) ![0, N, N]
  refine ⟨v, ?_⟩
  have hv : v = N • (Torus.a + Torus.b) := by
    dsimp only [v]
    rw [Torus.ofInt_eq_zsmul_gens, smul_add]
    simp [Torus.a, Torus.b]
  set c0 : ℤ := -384 * Type120.GV (s + 4) ^ 3 - 88 * ((2 : ℤ) ^ s) ^ 2 +
      512 * (2 : ℤ) ^ s * Type120.GV (s + 4) - 3264 * Type120.GV (s + 4) ^ 2 +
      1210 * (2 : ℤ) ^ s - 8994 * Type120.GV (s + 4) - 8094 with hc0def
  set c1 : ℤ := -256 * (2 : ℤ) ^ s * Type120.GV (s + 4) ^ 2 -
      96 * ((2 : ℤ) ^ s) ^ 2 - 192 * (2 : ℤ) ^ s * Type120.GV (s + 4) -
      1920 * Type120.GV (s + 4) ^ 2 + 980 * (2 : ℤ) ^ s -
      9128 * Type120.GV (s + 4) - 10849 with hc1def
  set c2 : ℤ := -256 * (2 : ℤ) ^ s * Type120.GV (s + 4) ^ 2 -
      80 * ((2 : ℤ) ^ s) ^ 2 - 928 * (2 : ℤ) ^ s * Type120.GV (s + 4) +
      192 * Type120.GV (s + 4) ^ 2 - 764 * (2 : ℤ) ^ s +
      944 * Type120.GV (s + 4) + 1159 with hc2def
  have hφv : (Type231.action (Type231.data s)).φuv v =
      Torus.ofInt (Type231.k s) ![N * c0, N * c1, N * c2] := by
    rw [hv, map_zsmul, t231_φuv_a_add_b (Type231.data s), ← Torus.ofInt_zsmul]
    congr 1
    rw [← hc0def, ← hc1def, ← hc2def]
    funext j
    fin_cases j <;> simp [Pi.smul_apply]
  have hw : (2 ^ (s + 2) : ℕ) • (Torus.a (k := Type231.k s) + Torus.b (k := Type231.k s)) =
      Torus.ofInt (Type231.k s) ![0, (2 : ℤ) ^ (s + 2), (2 : ℤ) ^ (s + 2)] := by
    rw [Torus.ofInt_eq_zsmul_gens]
    funext j
    fin_cases j <;> simp [Torus.a, Torus.b, Torus.c, gen, Pi.single_apply, zsmul_eq_mul]
  rw [hφv, hw, ← Torus.ofInt_sub, Torus.ofInt_eq_ofInt_iff]
  have hr : (2 : ℤ) ^ s = 2 * (2 : ℤ) ^ (s - 1) := by
    conv_lhs => rw [show s = (s - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have ht0 : c0 = 2 * (-192 * Type120.GV (s + 4) ^ 3 - 44 * ((2 : ℤ) ^ s) ^ 2 +
      256 * (2 : ℤ) ^ s * Type120.GV (s + 4) - 1632 * Type120.GV (s + 4) ^ 2 +
      605 * (2 : ℤ) ^ s - 4497 * Type120.GV (s + 4) - 4047) := by
    rw [hc0def]; ring
  have hw1 : c1 = 8 * (-64 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) ^ 2 -
      48 * ((2 : ℤ) ^ (s - 1)) ^ 2 - 48 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) -
      240 * Type120.GV (s + 4) ^ 2 + 245 * (2 : ℤ) ^ (s - 1) -
      1141 * Type120.GV (s + 4) - 1356) - 1 := by
    rw [hc1def, hr]; ring
  have hw2 : c2 = 8 * (-64 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) ^ 2 -
      40 * ((2 : ℤ) ^ (s - 1)) ^ 2 - 232 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) +
      24 * Type120.GV (s + 4) ^ 2 - 191 * (2 : ℤ) ^ (s - 1) +
      118 * Type120.GV (s + 4) + 145) - 1 := by
    rw [hc2def, hr]; ring
  intro j
  fin_cases j
  · change N * c0 - 0 ≡ 0 [ZMOD (2 : ℤ) ^ (s + 2)]
    rw [Int.modEq_iff_dvd]
    refine ⟨5 * (-192 * Type120.GV (s + 4) ^ 3 - 44 * ((2 : ℤ) ^ s) ^ 2 +
      256 * (2 : ℤ) ^ s * Type120.GV (s + 4) - 1632 * Type120.GV (s + 4) ^ 2 +
      605 * (2 : ℤ) ^ s - 4497 * Type120.GV (s + 4) - 4047), ?_⟩
    rw [ht0]
    dsimp only [N]
    ring
  · change N * c1 - N ≡ (2 : ℤ) ^ (s + 2) [ZMOD (2 : ℤ) ^ (s + 4)]
    rw [Int.modEq_iff_dvd]
    refine ⟨5 * (-64 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) ^ 2 -
      48 * ((2 : ℤ) ^ (s - 1)) ^ 2 - 48 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) -
      240 * Type120.GV (s + 4) ^ 2 + 245 * (2 : ℤ) ^ (s - 1) -
      1141 * Type120.GV (s + 4) - 1356) - 1, ?_⟩
    rw [hw1]
    dsimp only [N]
    rw [show s + 4 = (s + 2) + 2 by omega, pow_add]
    ring
  · change N * c2 - N ≡ (2 : ℤ) ^ (s + 2) [ZMOD (2 : ℤ) ^ (s + 4)]
    rw [Int.modEq_iff_dvd]
    refine ⟨5 * (-64 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) ^ 2 -
      40 * ((2 : ℤ) ^ (s - 1)) ^ 2 - 232 * (2 : ℤ) ^ (s - 1) * Type120.GV (s + 4) +
      24 * Type120.GV (s + 4) ^ 2 - 191 * (2 : ℤ) ^ (s - 1) +
      118 * Type120.GV (s + 4) + 145) - 1, ?_⟩
    rw [hw2]
    dsimp only [N]
    rw [show s + 4 = (s + 2) + 2 by omega, pow_add]
    ring

theorem t231_φuv_ab_half (s : ℕ) (hs : 1 ≤ s) :
    (StrothTypeIndex.t231 s hs).action.φuv
        ((2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) • (Torus.a + Torus.b)) =
      -((2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) • (Torus.a + Torus.b)) := by
  obtain ⟨v, hv⟩ := t231_uv_preimage s hs
  have hsq := (StrothTypeIndex.t231 s hs).action.rels.uv_sq
  have hvv : (StrothTypeIndex.t231 s hs).action.φuv
      ((StrothTypeIndex.t231 s hs).action.φuv v) = v := by
    have := DFunLike.congr_fun hsq v
    simpa using this
  have h2 : (StrothTypeIndex.t231 s hs).action.φuv
      ((StrothTypeIndex.t231 s hs).action.φuv v - v) =
      -((StrothTypeIndex.t231 s hs).action.φuv v - v) := by
    rw [map_sub, hvv]
    abel
  rwa [hv] at h2


theorem t231_d2_ofTorus {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)} :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2) =
      dD.ofTorus ((2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) •
        (Torus.a (k := (StrothTypeIndex.t231 s hs).k) +
          Torus.b (k := (StrothTypeIndex.t231 s hs).k))) := by
  rw [show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t231 s hs).k)) from dD.a_eq,
    show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t231 s hs).k)) from dD.b_eq,
    ← dD.ofTorus_add, ← dD.ofTorus_nsmul]

theorem t231_d2_sq_eq {F : StrothFrame G} {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)} (h : F.IsD D dD) :
    (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2)) *
        (((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2)) =
      ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
  have hexp : (StrothTypeIndex.t231 s hs).n - 2 = s + 2 := by
    have hn : (StrothTypeIndex.t231 s hs).n = s + 4 := by
      simp [StrothTypeIndex.n, StrothTypeIndex.k, Type231.k]
    omega
  rw [hexp]
  set x : G := (F.dA.a : G)⁻¹ with hx
  set y : G := (F.dA.b : G)⁻¹ with hy
  set ah : G := (dD.a : G) ^ 2 ^ (s + 3) with hah
  set bh : G := (dD.b : G) ^ 2 ^ (s + 3) with hbh
  set ab : G := (dD.a : G) * (dD.b : G) with hab
  change ab ^ 2 ^ (s + 2) * ab ^ 2 ^ (s + 2) = x ^ 2 * y ^ 2
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have haord : orderOf (dD.a : G) = 2 ^ (s + 4) := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_a]
    rfl
  have hbord : orderOf (dD.b : G) = 2 ^ (s + 4) := by
    rw [Subgroup.orderOf_coe, StrothWeakTypeData.orderOf_b]
    rfl
  have hah2 : ah * ah = 1 := by
    rw [show ah * ah = (dD.a : G) ^ (2 ^ (s + 3) + 2 ^ (s + 3)) by
      rw [hah, ← pow_add]]
    rw [show 2 ^ (s + 3) + 2 ^ (s + 3) = 2 ^ (s + 4) by
      rw [← two_mul, ← pow_succ', show s + 3 + 1 = s + 4 by omega]]
    rw [← haord, pow_orderOf_eq_one]
  have hbh2 : bh * bh = 1 := by
    rw [show bh * bh = (dD.b : G) ^ (2 ^ (s + 3) + 2 ^ (s + 3)) by
      rw [hbh, ← pow_add]]
    rw [show 2 ^ (s + 3) + 2 ^ (s + 3) = 2 ^ (s + 4) by
      rw [← two_mul, ← pow_succ', show s + 3 + 1 = s + 4 by omega]]
    rw [← hbord, pow_orderOf_eq_one]
  have hah_mem_D : ah ∈ D := by
    rw [hah]
    exact D.pow_mem dD.a.2 _
  have hbh_mem_D : bh ∈ D := by
    rw [hbh]
    exact D.pow_mem dD.b.2 _
  have hahΩ : ah ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hah_mem_D hah2
  have hbhΩ : bh ∈ omegaIn 1 D := mem_omegaIn_one_of_mul_self hbh_mem_D hbh2
  have hah_ofT : ah = dD.ofTorus
      ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k)) := by
    rw [hah, show (dD.a : G) = dD.ofTorus
        (Torus.a (k := (StrothTypeIndex.t231 s hs).k)) from dD.a_eq, ← dD.ofTorus_nsmul]
  have hbh_ofT : bh = dD.ofTorus
      ((2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k)) := by
    rw [hbh, show (dD.b : G) = dD.ofTorus
        (Torus.b (k := (StrothTypeIndex.t231 s hs).k)) from dD.b_eq, ← dD.ofTorus_nsmul]
  have huv_ah : dD.uv⁻¹ * ah * dD.uv = ah := by
    rw [hah_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k))
    rwa [t231_uv_fixes_a_half s hs] at hfix
  have huv_bh : dD.uv⁻¹ * bh * dD.uv = bh := by
    rw [hbh_ofT]
    have hfix := dD.conj_ofTorus dD.uv_mem dD.uv_conj
      ((2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k))
    rwa [t231_uv_fixes_b_half s hs] at hfix
  have hahK : ah ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : ah ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hahΩ, huv_ah⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hbhK : bh ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G) := by
    have hfix : bh ∈ {g : G | g ∈ omegaIn 1 D ∧ dD.uv⁻¹ * g * dD.uv = g} :=
      ⟨hbhΩ, huv_bh⟩
    rw [IsD.omegaIn_one_uv_fixed_eq h] at hfix
    simpa [hx, hy] using hfix
  have hx4 : x ^ 4 = 1 := by
    rw [hx]
    exact F.dA.pow_four_a_inv
  have hy4 : y ^ 4 = 1 := by
    rw [hy]
    exact F.dA.pow_four_b_inv
  have hx2sq : x ^ 2 * x ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hx4
  have hy2sq : y ^ 2 * y ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show 2 * 2 = 4 by norm_num]
    exact hy4
  have hcomm_xy : x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2 := by
    have hx2A : x ^ 2 ∈ F.A := by
      rw [hx]
      exact F.A.pow_mem (F.A.inv_mem F.dA.a.2) 2
    have hy2A : y ^ 2 ∈ F.A := by
      rw [hy]
      exact F.A.pow_mem (F.A.inv_mem F.dA.b.2) 2
    exact mul_comm_mem_of_isMulCommutative (D := F.A) hx2A hy2A
  have hXXY : x ^ 2 * (x ^ 2 * y ^ 2) = y ^ 2 := by
    rw [← mul_assoc, hx2sq, one_mul]
  have hYXY : y ^ 2 * (x ^ 2 * y ^ 2) = x ^ 2 := by
    rw [← mul_assoc, hcomm_xy.symm, mul_assoc, hy2sq, mul_one]
  have hXYXY : (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2) = 1 := by
    calc (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)
        = x ^ 2 * (y ^ 2 * x ^ 2) * y ^ 2 := by group
      _ = x ^ 2 * (x ^ 2 * y ^ 2) * y ^ 2 := by rw [hcomm_xy.symm]
      _ = (x ^ 2 * x ^ 2) * (y ^ 2 * y ^ 2) := by group
      _ = 1 := by rw [hx2sq, hy2sq, mul_one]
  have hXinv : (x ^ 2)⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right hx2sq
  have hYinv : (y ^ 2)⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right hy2sq
  have hXYinv : (x ^ 2 * y ^ 2)⁻¹ = x ^ 2 * y ^ 2 :=
    inv_eq_of_mul_eq_one_right hXYXY
  have hKsub : ∀ z ∈ Subgroup.closure ({x ^ 2, y ^ 2} : Set G),
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2 := by
    intro z hz
    refine Subgroup.closure_induction (p := fun z _ =>
      z = 1 ∨ z = x ^ 2 ∨ z = y ^ 2 ∨ z = x ^ 2 * y ^ 2) ?_ ?_ ?_ ?_ hz
    · intro u hu
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro a b _ _ iha ihb
      rcases iha with rfl | rfl | rfl | rfl <;>
        rcases ihb with rfl | rfl | rfl | rfl <;>
        simp [hx2sq, hy2sq, hcomm_xy.symm, hXXY, hYXY, hXYXY, mul_assoc]
    · intro a _ iha
      rcases iha with rfl | rfl | rfl | rfl <;>
        simp [hXinv, hYinv, hXYinv]
  have hux : F.dA.u⁻¹ * x * F.dA.u = y := by
    rw [hx, hy]
    exact StrothWeakTypeData.u_conj_a_inv F.dA
  have huy : F.dA.u⁻¹ * y * F.dA.u = x := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * y * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * x * F.dA.u) * F.dA.u := by rw [hux]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * x * (F.dA.u * F.dA.u) := by group
      _ = x := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hux2 : F.dA.u⁻¹ * x ^ 2 * F.dA.u = y ^ 2 := by
    calc F.dA.u⁻¹ * x ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * x * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := x) (i := 2)).symm
      _ = y ^ 2 := by rw [hux]
  have huy2 : F.dA.u⁻¹ * y ^ 2 * F.dA.u = x ^ 2 := by
    calc F.dA.u⁻¹ * y ^ 2 * F.dA.u
        = (F.dA.u⁻¹ * y * F.dA.u) ^ 2 := by
            simpa [inv_inv] using
              (conj_pow (a := F.dA.u⁻¹) (b := y) (i := 2)).symm
      _ = x ^ 2 := by rw [huy]
  have hufix : F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u = x ^ 2 * y ^ 2 := by
    calc F.dA.u⁻¹ * (x ^ 2 * y ^ 2) * F.dA.u
        = (F.dA.u⁻¹ * x ^ 2 * F.dA.u) * (F.dA.u⁻¹ * y ^ 2 * F.dA.u) := by group
      _ = y ^ 2 * x ^ 2 := by rw [hux2, huy2]
      _ = x ^ 2 * y ^ 2 := hcomm_xy.symm
  have hswap_d : dD.u⁻¹ * ah * dD.u = bh := by
    simpa [hah, hbh] using t231_u_swaps_a_half dD
  have hswap : F.dA.u⁻¹ * ah * F.dA.u = bh := by
    rw [← h.u_eq]
    exact hswap_d
  have hu_bh : F.dA.u⁻¹ * bh * F.dA.u = ah := by
    have hu : F.dA.u⁻¹ = F.dA.u := inv_eq_of_mul_eq_one_right F.dA.u_sq
    calc F.dA.u⁻¹ * bh * F.dA.u
        = F.dA.u⁻¹ * (F.dA.u⁻¹ * ah * F.dA.u) * F.dA.u := by rw [hswap]
      _ = (F.dA.u⁻¹ * F.dA.u⁻¹) * ah * (F.dA.u * F.dA.u) := by group
      _ = ah := by rw [hu, F.dA.u_sq, one_mul, mul_one]
  have hltpow : 2 ^ (s + 3) < 2 ^ (s + 4) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hah_ne_one : ah ≠ 1 := by
    have hlt : 2 ^ (s + 3) < orderOf (dD.a : G) := by
      simpa [haord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.a : G)) (n := 2 ^ (s + 3))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hah] using h
  have hbh_ne_one : bh ≠ 1 := by
    have hlt : 2 ^ (s + 3) < orderOf (dD.b : G) := by
      simpa [hbord] using hltpow
    have h := pow_ne_one_of_lt_orderOf (x := (dD.b : G)) (n := 2 ^ (s + 3))
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hlt
    simpa [hbh] using h
  have hua_ne : (2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k) ≠
      (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) := by
    have hva : (2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k) =
        Torus.ofInt (StrothTypeIndex.t231 s hs).k ![0, (2 : ℤ) ^ (s + 3), 0] := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.a, Torus.b, Torus.c]
    have hvb : (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) =
        Torus.ofInt (StrothTypeIndex.t231 s hs).k ![0, 0, (2 : ℤ) ^ (s + 3)] := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.a, Torus.b, Torus.c]
    intro htor
    rw [hva, hvb, Torus.ofInt_eq_ofInt_iff] at htor
    have h2 := htor 2
    rw [Int.modEq_iff_dvd] at h2
    have h2' : (2 : ℕ) ^ (s + 4) ∣ 2 ^ (s + 3) := by
      have h2'' : ((2 : ℤ) ^ (s + 4)) ∣ ((2 : ℤ) ^ (s + 3)) := by
        simpa [StrothTypeIndex.k, Type231.k] using h2
      exact_mod_cast h2''
    exact Nat.not_dvd_of_pos_of_lt (by positivity)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) h2'
  have hahb_ne : ah ≠ bh := by
    intro heq
    have htor : (2 ^ (s + 3) : ℕ) • Torus.a (k := (StrothTypeIndex.t231 s hs).k) =
        (2 ^ (s + 3) : ℕ) • Torus.b (k := (StrothTypeIndex.t231 s hs).k) := by
      apply dD.ofTorus_inj
      rw [← hah_ofT, ← hbh_ofT]
      exact heq
    exact hua_ne htor
  have hah_ne_xy : ah ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hbh_eq : bh = x ^ 2 * y ^ 2 := by
      rw [← hswap, hxy, hufix]
    exact hahb_ne (hxy.trans hbh_eq.symm)
  have hbh_ne_xy : bh ≠ x ^ 2 * y ^ 2 := by
    intro hxy
    have hah_eq : ah = x ^ 2 * y ^ 2 := by
      rw [← hu_bh, hxy, hufix]
    exact hahb_ne (hah_eq.trans hxy.symm)
  have hcomm_ab : Commute (dD.a : G) (dD.b : G) :=
    mul_comm_mem_of_isMulCommutative (D := D) dD.a.2 dD.b.2
  have hLHS : ab ^ 2 ^ (s + 2) * ab ^ 2 ^ (s + 2) = ah * bh := by
    have hpow : 2 ^ (s + 2) + 2 ^ (s + 2) = 2 ^ (s + 3) := by
      rw [← two_mul, ← pow_succ', show s + 2 + 1 = s + 3 by omega]
    calc ab ^ 2 ^ (s + 2) * ab ^ 2 ^ (s + 2)
        = ab ^ (2 ^ (s + 2) + 2 ^ (s + 2)) := (pow_add ab _ _).symm
      _ = ab ^ 2 ^ (s + 3) := by rw [hpow]
      _ = (dD.a : G) ^ 2 ^ (s + 3) * (dD.b : G) ^ 2 ^ (s + 3) := by
            rw [hab]
            exact hcomm_ab.mul_pow _
      _ = ah * bh := by rw [← hah, ← hbh]
  have hmain : ah * bh = x ^ 2 * y ^ 2 := by
    rcases hKsub ah hahK with hah1 | hahx | hahy | hahxy
    · exact absurd hah1 hah_ne_one
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · exact absurd (hahx.trans hbhx.symm) hahb_ne
      · rw [hahx, hbhy]
      · exact absurd hbhxy hbh_ne_xy
    · rcases hKsub bh hbhK with hbh1 | hbhx | hbhy | hbhxy
      · exact absurd hbh1 hbh_ne_one
      · rw [hahy, hbhx, hcomm_xy.symm]
      · exact absurd (hahy.trans hbhy.symm) hahb_ne
      · exact absurd hbhxy hbh_ne_xy
    · exact absurd hahxy hah_ne_xy
  exact hLHS.trans hmain

theorem t231_d2_mem_A {F : StrothFrame G} {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2) ∈ F.A := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2)
  let x : G := (F.dA.a : G)⁻¹
  let y : G := (F.dA.b : G)⁻¹
  change d2 ∈ F.A
  haveI : IsMulCommutative D := dD.isMulCommutative
  haveI : IsMulCommutative F.A := F.dA.isMulCommutative
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hxA : x ∈ F.A := by dsimp only [x]; exact F.A.inv_mem F.dA.a.2
  have hyA : y ∈ F.A := by dsimp only [y]; exact F.A.inv_mem F.dA.b.2
  have hxyA : x * y ∈ F.A := F.A.mul_mem hxA hyA
  have hxyD : x * y ∈ D := h.A_le hxyA
  have hxy_sq : (x * y) * (x * y) = x ^ 2 * y ^ 2 := by
    have hxy_comm : x * y = y * x :=
      mul_comm_mem_of_isMulCommutative (D := F.A) hxA hyA
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy_comm]
      _ = (x * x) * (y * y) := by group
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
  have hd2sq : d2 * d2 = x ^ 2 * y ^ 2 := by
    simpa [d2, x, y] using t231_d2_sq_eq (dD := dD) h
  have hcomm : Commute d2 (x * y) :=
    mul_comm_mem_of_isMulCommutative (D := D) hd2D hxyD
  have hcomm_inv : Commute d2 (x * y)⁻¹ := hcomm.inv_right
  have hz2 : (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹) = 1 := by
    calc (d2 * (x * y)⁻¹) * (d2 * (x * y)⁻¹)
        = d2 * ((x * y)⁻¹ * d2) * (x * y)⁻¹ := by group
      _ = d2 * (d2 * (x * y)⁻¹) * (x * y)⁻¹ := by rw [hcomm_inv.eq.symm]
      _ = (d2 * d2) * ((x * y)⁻¹ * (x * y)⁻¹) := by group
      _ = (x ^ 2 * y ^ 2) * (((x * y) * (x * y))⁻¹) := by
            rw [hd2sq, ← _root_.mul_inv_rev]
      _ = (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2)⁻¹ := by rw [hxy_sq]
      _ = 1 := mul_inv_cancel _
  have hzA : d2 * (x * y)⁻¹ ∈ F.A :=
    h.mem_A_of_mul_self (D.mul_mem hd2D (D.inv_mem hxyD)) hz2
  have hd2_eq : d2 = (d2 * (x * y)⁻¹) * (x * y) := by group
  rw [hd2_eq]
  exact F.A.mul_mem hzA hxyA

theorem t231_d2_eq_xy {F : StrothFrame G} {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)} (h : F.IsD D dD) :
    ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2) =
        F.dA.toConfig.x * F.dA.toConfig.y ∨
      ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2) =
        (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2)
  let w : Torus (StrothTypeIndex.t231 s hs).k :=
    (2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) • (Torus.a + Torus.b)
  change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
    d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹
  have hd2A : d2 ∈ F.A := by
    simpa [d2] using t231_d2_mem_A (dD := dD) h
  have hd2D : d2 ∈ D := by
    dsimp only [d2]
    exact D.pow_mem (D.mul_mem dD.a.2 dD.b.2) _
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t231_d2_ofTorus (dD := dD)
  have hφu : (StrothTypeIndex.t231 s hs).action.φu w = w := by
    dsimp only [w]
    rw [show (StrothTypeIndex.t231 s hs).n - 2 = s + 2 from by
      have hn : (StrothTypeIndex.t231 s hs).n = s + 4 := by
        simp [StrothTypeIndex.n, StrothTypeIndex.k, Type231.k]
      omega]
    exact t231_φu_ab_half s hs
  have hφuv : (StrothTypeIndex.t231 s hs).action.φuv w = -w := by
    dsimp only [w]
    exact t231_φuv_ab_half s hs
  have hdu : dD.u⁻¹ * d2 * dD.u = d2 := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.u_mem dD.u_conj w
    rwa [hφu] at hconj
  have hduv : dD.uv⁻¹ * d2 * dD.uv = d2⁻¹ := by
    rw [hd2_ofT]
    have hconj := dD.conj_ofTorus dD.uv_mem dD.uv_conj w
    rw [hφuv, dD.ofTorus_neg] at hconj
    exact hconj
  have hduA : F.dA.u⁻¹ * d2 * F.dA.u = d2 := by
    rw [← h.u_eq]
    exact hdu
  have hduvA : F.dA.uv⁻¹ * d2 * F.dA.uv = d2⁻¹ := by
    rw [← h.uv_eq]
    exact hduv
  obtain ⟨δ, hδ⟩ := F.dA.exists_ofTorus hd2A
  have hδ2 : δ + δ = (2 : ℕ) • Torus.a + (2 : ℕ) • Torus.b := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_add, F.dA.ofTorus_add, F.dA.ofTorus_nsmul, F.dA.ofTorus_nsmul]
    rw [← hδ]
    have hd2sq : d2 * d2 =
        ((F.dA.a : G)⁻¹) ^ 2 * ((F.dA.b : G)⁻¹) ^ 2 := by
      simpa [d2] using t231_d2_sq_eq (dD := dD) h
    rw [hd2sq, F.a_inv_sq, F.b_inv_sq]
    rfl
  have hδu : (StrothTypeIndex.t100 1).action.φu δ = δ := by
    apply F.dA.ofTorus_inj
    have hconj := F.dA.conj_ofTorus F.dA.u_mem F.dA.u_conj δ
    rw [← hconj, ← hδ]
    exact hduA
  have hδuv : (StrothTypeIndex.t100 1).action.φuv δ = -δ := by
    apply F.dA.ofTorus_inj
    rw [F.dA.ofTorus_neg]
    have hconj := F.dA.conj_ofTorus F.dA.uv_mem F.dA.uv_conj δ
    rw [← hconj, ← hδ]
    exact hduvA
  have hxy : F.dA.toConfig.x * F.dA.toConfig.y =
      F.dA.ofTorus (-(Torus.a + Torus.b)) := by
    rw [StrothWeakTypeData.toConfig_x, StrothWeakTypeData.toConfig_y,
      neg_add, F.dA.ofTorus_add, F.dA.ofTorus_neg, F.dA.ofTorus_neg,
      ← F.dA.a_eq, ← F.dA.b_eq]
  rcases Stroth43Fus.t100_one_xy δ hδ2 hδu hδuv with hδab | hδab
  · right
    rw [hδ, hδab, hxy, ← F.dA.ofTorus_neg, neg_neg]
  · left
    rw [hδ, hδab, hxy]

theorem t231_isConj_uv_xyuv {F : StrothFrame G} {D : Subgroup G} {s : ℕ} {hs : 1 ≤ s}
    {dD : StrothWeakTypeData D (StrothTypeIndex.t231 s hs)} (h : F.IsD D dD) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  let d2 : G := ((dD.a : G) * (dD.b : G)) ^ 2 ^ ((StrothTypeIndex.t231 s hs).n - 2)
  let w : Torus (StrothTypeIndex.t231 s hs).k :=
    (2 ^ ((StrothTypeIndex.t231 s hs).n - 2) : ℕ) • (Torus.a + Torus.b)
  have hd2_ofT : d2 = dD.ofTorus w := by
    simpa [d2, w] using t231_d2_ofTorus (dD := dD)
  have hd2 : d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ := by
    have h := t231_d2_eq_xy (dD := dD) h
    change d2 = F.dA.toConfig.x * F.dA.toConfig.y ∨
      d2 = (F.dA.toConfig.x * F.dA.toConfig.y)⁻¹ at h
    exact h
  obtain ⟨v, hv⟩ := t231_uv_preimage s hs
  have hφ : dD.ofTorus ((StrothTypeIndex.t231 s hs).action.φuv v - v) = d2 := by
    rw [hv, hd2_ofT]
  exact isConj_uv_xyuv_of_d2 (τ := StrothTypeIndex.t231 s hs) h hd2 hφ

end StrothFrame.IsD

end CFSG.CGT.Stroth77

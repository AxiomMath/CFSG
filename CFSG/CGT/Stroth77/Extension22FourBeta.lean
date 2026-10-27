module

public import CFSG.CGT.Stroth77.Extension22FourClassify4

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

namespace TorusBasisEquivFour

variable {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}

theorem even_of_mul_two_pow_succ_eq_zero (m : ℕ) (A : ℤ)
    (h : (A : ZMod (2 ^ (m + 2))) * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0) :
    Even A := by
  have h' : ((A * (2 ^ (m + 1) : ℕ) : ℤ) : ZMod (2 ^ (m + 2))) = 0 := by
    push_cast
    exact h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have hpow : ((2 ^ (m + 2) : ℕ) : ℤ) = 2 * ((2 ^ (m + 1) : ℕ) : ℤ) := by
    rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
    push_cast
    ring
  rw [hpow] at h'
  have hN : ((2 ^ (m + 1) : ℕ) : ℤ) ≠ 0 := by positivity
  exact even_iff_two_dvd.mpr ((mul_dvd_mul_iff_right hN).mp h')

theorem even_of_smul_eBasis_one_add_two_eq_zero (m : ℕ) (A B : ℤ)
    (h : A • eBasis m 1 + B • eBasis m 2 = 0) : Even A ∧ Even B := by
  constructor
  · apply even_of_mul_two_pow_succ_eq_zero m A
    have h1 := congrFun h 1
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul,
      eBasis_one, eBasis_two] at h1
    simp only [Pi.smul_apply, Pi.add_apply, gen, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1),
      Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2),
      Pi.zero_apply, Pi.one_apply, nsmul_eq_mul, mul_one, mul_zero, add_zero, one_mul,
      zero_mul, zero_add] at h1
    rw [Nat.cast_pow, Nat.cast_ofNat] at h1
    change (↑A : ZMod (2 ^ (m + 2))) * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 at h1
    exact h1
  · apply even_of_mul_two_pow_succ_eq_zero m B
    have h2 := congrFun h 2
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul,
      eBasis_one, eBasis_two] at h2
    simp only [Pi.smul_apply, Pi.add_apply, gen, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1),
      Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2),
      Pi.zero_apply, Pi.one_apply, nsmul_eq_mul, mul_one, mul_zero, add_zero, one_mul,
      zero_mul, zero_add] at h2
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    change (↑B : ZMod (2 ^ (m + 2))) * (2 : ZMod (2 ^ (m + 2))) ^ (m + 1) = 0 at h2
    exact h2

theorem eBit_eq_zero_or_one (x : Torus (Type200.k m)) (i : Fin 3) :
    eBit x i = 0 ∨ eBit x i = 1 := by
  by_cases h0 : x i = 0
  · left; simp only [eBit]; rw [if_pos h0]
  · right; simp only [eBit]; rw [if_neg h0]

theorem eBit_eq_zero_of_even (x : Torus (Type200.k m)) (i : Fin 3)
    (h : Even (eBit x i)) : eBit x i = 0 := by
  rcases eBit_eq_zero_or_one x i with h0 | h1
  · exact h0
  · rw [h1] at h; norm_num at h

theorem eq_of_even_add_of_bits {a b : ℤ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : Even (a + b)) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exfalso; norm_num [Even] at h
  · exfalso; norm_num [Even] at h
  · rfl

theorem cocycleUV_two_smul (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (x : Torus (Type200.k m)) :
    2 • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  have h2p : 2 • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen1 he hf E hL
  have h2q : 2 • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen2 he hf E hL
  have hδ : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL =
      piBasis h2p h2q :=
    hom_eq_piBasis (cocycleUV_gen0 he hf E hL) h2p h2q
  rw [hδ]
  exact piBasis_two_smul h2p h2q x

theorem cocycleT_two_smul (E : TorusBasisEquivFour D hBC e f)
    (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (x : Torus (Type200.k m)) :
    2 • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x = 0 := by
  have h2p : 2 • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen1 he hf E hL
  have h2q : 2 • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen2 he hf E hL
  have hδ : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL =
      piBasis h2p h2q :=
    hom_eq_piBasis (cocycleT_gen0 he hf E hL) h2p h2q
  rw [hδ]
  exact piBasis_two_smul h2p h2q x


theorem cocycleUV_uv_sq
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (x : Torus (Type200.k m)) :
    (Type200.action m).φuv (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) +
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv x) = 0 := by
  have hββ : (Type200.action m).φuv ((Type200.action m).φuv x) = x := by
    have h := congrArg (fun f => f x) (Type200.action m).rels.uv_sq
    simpa [AddMonoidHom.comp_apply] using h
  have hδδ : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) = 0 :=
    cocycleUV_eq_zero_of_two_torsion he hf E hL (cocycleUV_two_smul E hL he hf x)
  have hαα : conjTorusFour D hBC E (hL D.uv_mem_L)
      (conjTorusFour D hBC E (hL D.uv_mem_L) x) = x := by
    have h := congrArg (fun f => f x) (conjTorusFour_rels (E := E) hL).uv_sq
    simpa [AddMonoidHom.comp_apply] using h
  have hexp : conjTorusFour D hBC E (hL D.uv_mem_L)
      (conjTorusFour D hBC E (hL D.uv_mem_L) x) =
      (Type200.action m).φuv ((Type200.action m).φuv x) +
        (Type200.action m).φuv
          (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) +
        (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
            ((Type200.action m).φuv x) +
          cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
            (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x)) := by
    calc conjTorusFour D hBC E (hL D.uv_mem_L) (conjTorusFour D hBC E (hL D.uv_mem_L) x)
        = (Type200.action m).φuv (conjTorusFour D hBC E (hL D.uv_mem_L) x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              (conjTorusFour D hBC E (hL D.uv_mem_L) x) :=
          action_eq_printed_add_cocycle E (hL D.uv_mem_L)
            ((Type200.action m).φuv) _
      _ = (Type200.action m).φuv
            ((Type200.action m).φuv x +
              cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φuv x +
                cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) := by
          rw [action_eq_printed_add_cocycle E (hL D.uv_mem_L)
            ((Type200.action m).φuv)]
          rfl
      _ = (Type200.action m).φuv ((Type200.action m).φuv x) +
            (Type200.action m).φuv
              (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) +
            (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
                ((Type200.action m).φuv x) +
              cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
                (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x)) := by
          rw [map_add, map_add]
  rw [hαα, hββ, hδδ, add_zero] at hexp
  have h' : x + ((Type200.action m).φuv
        (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) +
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv x)) = x + 0 := by
    rw [add_zero]
    simpa [add_assoc] using hexp.symm
  exact add_left_cancel h'

theorem cocycleUV_uv_rho
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (x : Torus (Type200.k m)) :
    (Type200.action m).φρ (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL x) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φρ x) := by
  have hαρ : ∀ y : Torus (Type200.k m),
      conjTorusFour D hBC E (hL D.ρ_mem_L) y = (Type200.action m).φρ y := by
    intro y
    rw [action_eq_printed_add_cocycle E (hL D.ρ_mem_L) ((Type200.action m).φρ)]
    have h0 : cocycle (D := D) (hBC := hBC) (e := e) (f := f)
        ((Type200.action m).φρ) E (hL D.ρ_mem_L) y = 0 := by
      change cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL y = 0
      rw [hρ]; rfl
    rw [h0, add_zero]
  have hrel := congrArg (fun f => f x) (conjTorusFour_rels (E := E) hL).uv_rho
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at hrel
  rw [hαρ, hαρ] at hrel
  rw [action_eq_printed_add_cocycle E (hL D.uv_mem_L) ((Type200.action m).φuv)] at hrel
  rw [action_eq_printed_add_cocycle E (hL D.t_mem_L) ((Type200.action m).φt)] at hrel
  rw [map_add] at hrel
  have hβ : (Type200.action m).φρ ((Type200.action m).φuv x) =
      (Type200.action m).φt ((Type200.action m).φρ x) := by
    have h := congrArg (fun f => f x) (Type200.action m).rels.uv_rho
    simpa [AddMonoidHom.comp_apply] using h
  rw [hβ] at hrel
  exact add_left_cancel hrel

theorem cocycleUV_cocycleT_t_u
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (x : Torus (Type200.k m)) :
    (Type200.action m).φu (cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) =
      (Type200.action m).φt
          (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
            ((Type200.action m).φu x)) +
        cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          ((Type200.action m).φuv ((Type200.action m).φu x)) := by
  have hαu : ∀ y : Torus (Type200.k m),
      conjTorusFour D hBC E (hL D.u_mem_L) y = (Type200.action m).φu y := by
    intro y
    rw [action_eq_printed_add_cocycle E (hL D.u_mem_L) ((Type200.action m).φu)]
    have h0 : cocycle (D := D) (hBC := hBC) (e := e) (f := f)
        ((Type200.action m).φu) E (hL D.u_mem_L) y = 0 := by
      change cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL y = 0
      rw [hu]; rfl
    rw [h0, add_zero]
  have hδδ : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φu x)) = 0 :=
    cocycleT_eq_zero_of_two_torsion he hf E hL
      (cocycleUV_two_smul E hL he hf ((Type200.action m).φu x))
  have hαt : ∀ y : Torus (Type200.k m),
      conjTorusFour D hBC E (hL D.t_mem_L) y =
        (Type200.action m).φt y + cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL y :=
    fun y => action_eq_printed_add_cocycle E (hL D.t_mem_L) ((Type200.action m).φt) y
  have hαuv : ∀ y : Torus (Type200.k m),
      conjTorusFour D hBC E (hL D.uv_mem_L) y =
        (Type200.action m).φuv y + cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL y :=
    fun y => action_eq_printed_add_cocycle E (hL D.uv_mem_L) ((Type200.action m).φuv) y
  have hrel := congrArg (fun f => f x) (conjTorusFour_rels (E := E) hL).t_u
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at hrel
  have hrel' : (Type200.action m).φu
        (conjTorusFour D hBC E (hL D.t_mem_L) x) =
      conjTorusFour D hBC E (hL D.t_mem_L)
        (conjTorusFour D hBC E (hL D.uv_mem_L) ((Type200.action m).φu x)) := by
    simpa only [hαu] using hrel
  have hβ : (Type200.action m).φu ((Type200.action m).φt x) =
      (Type200.action m).φt ((Type200.action m).φuv ((Type200.action m).φu x)) := by
    have h := congrArg (fun f => f x) (Type200.action m).rels.t_u
    simpa [AddMonoidHom.comp_apply] using h
  have hmain : (Type200.action m).φu (cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) =
      (Type200.action m).φt
          (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
            ((Type200.action m).φu x)) +
        cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          ((Type200.action m).φuv ((Type200.action m).φu x)) := by
    have hLHS : (Type200.action m).φu
          (conjTorusFour D hBC E (hL D.t_mem_L) x) =
        (Type200.action m).φu ((Type200.action m).φt x +
          cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) :=
      congrArg (fun y => (Type200.action m).φu y) (hαt x)
    have hRHS1 : conjTorusFour D hBC E (hL D.t_mem_L)
          (conjTorusFour D hBC E (hL D.uv_mem_L) ((Type200.action m).φu x)) =
        conjTorusFour D hBC E (hL D.t_mem_L)
          ((Type200.action m).φuv ((Type200.action m).φu x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φu x)) :=
      congrArg (fun y => conjTorusFour D hBC E (hL D.t_mem_L) y)
        (hαuv ((Type200.action m).φu x))
    have h : (Type200.action m).φu ((Type200.action m).φt x +
          cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) =
        conjTorusFour D hBC E (hL D.t_mem_L)
          ((Type200.action m).φuv ((Type200.action m).φu x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φu x)) := by
      rw [← hLHS, ← hRHS1]
      exact hrel'
    have hRHS2 : conjTorusFour D hBC E (hL D.t_mem_L)
          ((Type200.action m).φuv ((Type200.action m).φu x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φu x)) =
        ((Type200.action m).φt ((Type200.action m).φuv ((Type200.action m).φu x) +
            cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φu x)) +
          cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
            ((Type200.action m).φuv ((Type200.action m).φu x) +
              cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
                ((Type200.action m).φu x))) := hαt _
    rw [hRHS2] at h
    rw [map_add] at h
    rw [map_add, map_add] at h
    rw [hβ, hδδ, add_zero] at h
    have h' : (Type200.action m).φt ((Type200.action m).φuv ((Type200.action m).φu x)) +
        (Type200.action m).φu (cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL x) =
        (Type200.action m).φt ((Type200.action m).φuv ((Type200.action m).φu x)) +
          ((Type200.action m).φt
              (cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
                ((Type200.action m).φu x)) +
            cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
              ((Type200.action m).φuv ((Type200.action m).φu x))) := by
      simpa [add_assoc] using h
    exact add_left_cancel h'
  exact hmain


theorem cocycleUV_uv_gen1
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv (gen (Type200.k m) 1)) =
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) := by
  rw [show (Type200.action m).φuv (gen (Type200.k m) 1) =
      (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
        (2 : ℤ) • gen (Type200.k m) 2 by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.uv_a m]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    cocycleUV_gen0 he hf E hL]
  have h2q : (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen2 he hf E hL
  rw [one_zsmul, one_zsmul, h2q]
  simp

theorem cocycleUV_uv_gen2
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv (gen (Type200.k m) 2)) =
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) := by
  rw [show (Type200.action m).φuv (gen (Type200.k m) 2) =
      (1 : ℤ) • gen (Type200.k m) 0 + (2 : ℤ) • gen (Type200.k m) 1 +
        (1 : ℤ) • gen (Type200.k m) 2 by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.uv_b m]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    cocycleUV_gen0 he hf E hL]
  have h2p : (2 : ℤ) • cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleUV_two_gen1 he hf E hL
  rw [one_zsmul, one_zsmul, h2p]
  simp

theorem cocycleT_uv_gen1
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv (gen (Type200.k m) 1)) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) := by
  rw [show (Type200.action m).φuv (gen (Type200.k m) 1) =
      (1 : ℤ) • gen (Type200.k m) 0 + (1 : ℤ) • gen (Type200.k m) 1 +
        (2 : ℤ) • gen (Type200.k m) 2 by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.uv_a m]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    cocycleT_gen0 he hf E hL]
  have h2s : (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen2 he hf E hL
  rw [one_zsmul, one_zsmul, h2s]
  simp

theorem cocycleT_uv_gen2
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φuv (gen (Type200.k m) 2)) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) := by
  rw [show (Type200.action m).φuv (gen (Type200.k m) 2) =
      (1 : ℤ) • gen (Type200.k m) 0 + (2 : ℤ) • gen (Type200.k m) 1 +
        (1 : ℤ) • gen (Type200.k m) 2 by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.uv_b m]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    cocycleT_gen0 he hf E hL]
  have h2r : (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen1 he hf E hL
  rw [one_zsmul, one_zsmul, h2r]
  simp

theorem cocycleT_rho_gen2
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩) :
    cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        ((Type200.action m).φρ (gen (Type200.k m) 2)) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1) +
        cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2) := by
  rw [show (Type200.action m).φρ (gen (Type200.k m) 2) =
      (-1 : ℤ) • gen (Type200.k m) 0 + (-1 : ℤ) • gen (Type200.k m) 1 +
        (-1 : ℤ) • gen (Type200.k m) 2 by
    simpa [Torus.c, Torus.a, Torus.b] using Type200.rho_b m]
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
    cocycleT_gen0 he hf E hL]
  have h2r : (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen1 he hf E hL
  have h2s : (2 : ℤ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using cocycleT_two_gen2 he hf E hL
  have h2r' : (2 : ℕ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0 := by
    simpa [two_zsmul, two_nsmul] using h2r
  have h2s' : (2 : ℕ) • cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0 := by
    simpa [two_zsmul, two_nsmul] using h2s
  have hrneg : -cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 1) := by
    rw [neg_eq_iff_add_eq_zero]
    rw [← two_nsmul]
    exact h2r'
  have hsneg : -cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) =
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
        (gen (Type200.k m) 2) := by
    rw [neg_eq_iff_add_eq_zero]
    rw [← two_nsmul]
    exact h2s'
  simp [neg_smul, hrneg, hsneg]


theorem cocycleUV_cocycleT_forms
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0) :
    ∃ β : ℤ, (β = 0 ∨ β = (2 : ℤ) ^ (m + 1)) ∧
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1) = β • gen (Type200.k m) 2 ∧
      cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 ∧
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 1) = β • gen (Type200.k m) 1 ∧
      cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
          (gen (Type200.k m) 2) = β • gen (Type200.k m) 1 + β • gen (Type200.k m) 2 := by
  classical
  let p : Torus (Type200.k m) := cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let q : Torus (Type200.k m) := cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  let r : Torus (Type200.k m) := cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 1)
  let s : Torus (Type200.k m) := cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
    (gen (Type200.k m) 2)
  have h2p : 2 • p = 0 := by
    simpa [p, two_zsmul, two_nsmul] using cocycleUV_two_gen1 he hf E hL
  have h2q : 2 • q = 0 := by
    simpa [q, two_zsmul, two_nsmul] using cocycleUV_two_gen2 he hf E hL
  have h2r : 2 • r = 0 := by
    simpa [r, two_zsmul, two_nsmul] using cocycleT_two_gen1 he hf E hL
  have h2s : 2 • s = 0 := by
    simpa [s, two_zsmul, two_nsmul] using cocycleT_two_gen2 he hf E hL
  have hδβuv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φuv (gen (Type200.k m) 1)) = p := by
    simpa [p] using cocycleUV_uv_gen1 E hL he hf
  have hδβuv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φuv (gen (Type200.k m) 2)) = q := by
    simpa [q] using cocycleUV_uv_gen2 E hL he hf
  have huv1 : (Type200.action m).φuv p + p = 0 := by
    have h := cocycleUV_uv_sq E hL he hf (gen (Type200.k m) 1)
    rw [show cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = p from rfl, hδβuv1] at h
    exact h
  have huv2 : (Type200.action m).φuv q + q = 0 := by
    have h := cocycleUV_uv_sq E hL he hf (gen (Type200.k m) 2)
    rw [show cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = q from rfl, hδβuv2] at h
    exact h
  have hp0 : eBit p 0 = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 2 ^ Type200.k 0 0 = 1 := by
        rw [show Type200.k 0 0 = 0 from rfl]; norm_num
      haveI : Subsingleton (ZMod (2 ^ Type200.k 0 0)) := by rw [h1]; infer_instance
      have hpzero : p 0 = 0 := Subsingleton.elim _ _
      simp [eBit, hpzero]
    · have h := huv1
      rw [two_torsion_decomp h2p] at h
      simp only [map_add, map_zsmul, phiUV_eBasis_zero m hm, phiUV_eBasis_one,
        phiUV_eBasis_two] at h
      rw [smul_add, smul_add] at h
      have hgroup : (eBit p 0 • eBasis m 0 + eBit p 0 • eBasis m 1 +
            eBit p 0 • eBasis m 2 + eBit p 1 • eBasis m 1 +
              eBit p 2 • eBasis m 2) +
          (eBit p 0 • eBasis m 0 + eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2) =
          (eBit p 0 • eBasis m 1 + eBit p 0 • eBasis m 2) +
            ((eBit p 0 • eBasis m 0 + eBit p 0 • eBasis m 0) +
              (eBit p 1 • eBasis m 1 + eBit p 1 • eBasis m 1) +
              (eBit p 2 • eBasis m 2 + eBit p 2 • eBasis m 2)) := by
        abel
      rw [hgroup, smul_eBasis_add_self, smul_eBasis_add_self,
        smul_eBasis_add_self] at h
      simp only [add_zero] at h
      exact eBit_eq_zero_of_even p 0
        (even_of_smul_eBasis_one_add_two_eq_zero m (eBit p 0) (eBit p 0) h).1
  have hq0 : eBit q 0 = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 2 ^ Type200.k 0 0 = 1 := by
        rw [show Type200.k 0 0 = 0 from rfl]; norm_num
      haveI : Subsingleton (ZMod (2 ^ Type200.k 0 0)) := by rw [h1]; infer_instance
      have hqzero : q 0 = 0 := Subsingleton.elim _ _
      simp [eBit, hqzero]
    · have h := huv2
      rw [two_torsion_decomp h2q] at h
      simp only [map_add, map_zsmul, phiUV_eBasis_zero m hm, phiUV_eBasis_one,
        phiUV_eBasis_two] at h
      rw [smul_add, smul_add] at h
      have hgroup : (eBit q 0 • eBasis m 0 + eBit q 0 • eBasis m 1 +
            eBit q 0 • eBasis m 2 + eBit q 1 • eBasis m 1 +
              eBit q 2 • eBasis m 2) +
          (eBit q 0 • eBasis m 0 + eBit q 1 • eBasis m 1 + eBit q 2 • eBasis m 2) =
          (eBit q 0 • eBasis m 1 + eBit q 0 • eBasis m 2) +
            ((eBit q 0 • eBasis m 0 + eBit q 0 • eBasis m 0) +
              (eBit q 1 • eBasis m 1 + eBit q 1 • eBasis m 1) +
              (eBit q 2 • eBasis m 2 + eBit q 2 • eBasis m 2)) := by
        abel
      rw [hgroup, smul_eBasis_add_self, smul_eBasis_add_self,
        smul_eBasis_add_self] at h
      simp only [add_zero] at h
      exact eBit_eq_zero_of_even q 0
        (even_of_smul_eBasis_one_add_two_eq_zero m (eBit q 0) (eBit q 0) h).1
  have hp : p = eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2 := by
    calc p = eBit p 0 • eBasis m 0 + eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2 :=
          two_torsion_decomp h2p
      _ = eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2 := by
          rw [hp0, zero_smul, zero_add]
  have hq : q = eBit q 1 • eBasis m 1 + eBit q 2 • eBasis m 2 := by
    calc q = eBit q 0 • eBasis m 0 + eBit q 1 • eBasis m 1 + eBit q 2 • eBasis m 2 :=
          two_torsion_decomp h2q
      _ = eBit q 1 • eBasis m 1 + eBit q 2 • eBasis m 2 := by
          rw [hq0, zero_smul, zero_add]
  have hβρ1 : (Type200.action m).φρ (gen (Type200.k m) 1) = gen (Type200.k m) 2 := by
    simpa [Torus.a, Torus.b] using Type200.rho_a m
  have hs_eq : (Type200.action m).φρ p = s := by
    have h := cocycleUV_uv_rho E hL he hf hρ (gen (Type200.k m) 1)
    simpa [p, s, hβρ1] using h
  have hs_form : s = eBit p 2 • eBasis m 1 +
      (eBit p 1 + eBit p 2) • eBasis m 2 := by
    rw [← hs_eq]
    conv_lhs => rw [hp]
    rw [map_add, map_zsmul, map_zsmul, phiR_eBasis_one, phiR_eBasis_two,
      smul_add, add_smul]
    abel
  have hδtβρ2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φρ (gen (Type200.k m) 2)) = r + s := by
    simpa [r, s] using cocycleT_rho_gen2 E hL he hf
  have hrs_eq : (Type200.action m).φρ q = r + s := by
    have h := cocycleUV_uv_rho E hL he hf hρ (gen (Type200.k m) 2)
    simpa [q, hδtβρ2] using h
  have hrs_form : r + s = eBit q 2 • eBasis m 1 +
      (eBit q 1 + eBit q 2) • eBasis m 2 := by
    rw [← hrs_eq]
    conv_lhs => rw [hq]
    rw [map_add, map_zsmul, map_zsmul, phiR_eBasis_one, phiR_eBasis_two,
      smul_add, add_smul]
    abel
  have hβu1 : (Type200.action m).φu (gen (Type200.k m) 1) = gen (Type200.k m) 2 := by
    simpa [Torus.a, Torus.b] using Type200.u_a m
  have hβu2 : (Type200.action m).φu (gen (Type200.k m) 2) = gen (Type200.k m) 1 := by
    simpa [Torus.a, Torus.b] using Type200.u_b m
  have hδuvu1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φu (gen (Type200.k m) 1)) = q := by
    rw [hβu1]
  have hδuvu2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φu (gen (Type200.k m) 2)) = p := by
    rw [hβu2]
  have hδtu1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φuv ((Type200.action m).φu (gen (Type200.k m) 1))) = s := by
    rw [hβu1]
    simpa [s] using cocycleT_uv_gen2 E hL he hf
  have hδtu2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      ((Type200.action m).φuv ((Type200.action m).φu (gen (Type200.k m) 2))) = r := by
    rw [hβu2]
    simpa [r] using cocycleT_uv_gen1 E hL he hf
  have hC : (Type200.action m).φu r = (Type200.action m).φt q + s := by
    have h := cocycleUV_cocycleT_t_u E hL he hf hu (gen (Type200.k m) 1)
    simpa [r, q, s, hδuvu1, hδtu1] using h
  have hD : (Type200.action m).φu s = (Type200.action m).φt p + r := by
    have h := cocycleUV_cocycleT_t_u E hL he hf hu (gen (Type200.k m) 2)
    simpa [r, p, s, hδuvu2, hδtu2] using h
  have hβu_s : (Type200.action m).φu s =
      eBit p 2 • eBasis m 2 + (eBit p 1 + eBit p 2) • eBasis m 1 := by
    rw [hs_form, map_add, map_zsmul, map_zsmul, phiU_eBasis_one, phiU_eBasis_two]
  have hβt_p : (Type200.action m).φt p =
      eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2 := by
    conv_lhs => rw [hp]
    rw [map_add, map_zsmul, map_zsmul, phiT_eBasis_one, phiT_eBasis_two]
  have hr_form : r = eBit p 2 • eBasis m 1 := by
    have h := hD
    rw [hβu_s, hβt_p] at h
    have hr_eq : r = (eBit p 2 • eBasis m 2 + (eBit p 1 + eBit p 2) • eBasis m 1) -
        (eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2) := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]
      exact h.symm
    rw [hr_eq]
    have hcalc : (eBit p 2 • eBasis m 2 + (eBit p 1 + eBit p 2) • eBasis m 1) -
        (eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2) =
        eBit p 2 • eBasis m 1 := by
      calc (eBit p 2 • eBasis m 2 + (eBit p 1 + eBit p 2) • eBasis m 1) -
          (eBit p 1 • eBasis m 1 + eBit p 2 • eBasis m 2)
          = ((eBit p 1 + eBit p 2) • eBasis m 1 - eBit p 1 • eBasis m 1) +
              (eBit p 2 • eBasis m 2 - eBit p 2 • eBasis m 2) := by abel
        _ = eBit p 2 • eBasis m 1 := by
              rw [← sub_smul, ← sub_smul]
              rw [show eBit p 1 + eBit p 2 - eBit p 1 = eBit p 2 by ring]
              rw [sub_self, zero_smul, add_zero]
    rw [hcalc]
  have hE0 : eBit q 2 • eBasis m 1 +
      (eBit q 1 + eBit q 2 - eBit p 1 - eBit p 2) • eBasis m 2 = 0 := by
    have h := hrs_form
    rw [hr_form, hs_form] at h
    have hleft : eBit p 2 • eBasis m 1 +
        (eBit p 2 • eBasis m 1 + (eBit p 1 + eBit p 2) • eBasis m 2) =
        (eBit p 1 + eBit p 2) • eBasis m 2 := by
      rw [← add_assoc, smul_eBasis_add_self, zero_add]
    rw [hleft] at h
    have hBA : (eBit q 2 • eBasis m 1 + (eBit q 1 + eBit q 2) • eBasis m 2) -
        (eBit p 1 + eBit p 2) • eBasis m 2 = 0 :=
      sub_eq_zero.mpr h.symm
    have hBA' : eBit q 2 • eBasis m 1 +
        ((eBit q 1 + eBit q 2) • eBasis m 2 - (eBit p 1 + eBit p 2) • eBasis m 2) = 0 := by
      rw [sub_eq_add_neg] at hBA ⊢
      simpa [add_assoc] using hBA
    rw [← sub_smul] at hBA'
    rw [show (eBit q 1 + eBit q 2) - (eBit p 1 + eBit p 2) =
      eBit q 1 + eBit q 2 - eBit p 1 - eBit p 2 by ring] at hBA'
    simpa [add_assoc] using hBA' 
  have hq2 : eBit q 2 = 0 :=
    eBit_eq_zero_of_even q 2
      (even_of_smul_eBasis_one_add_two_eq_zero m (eBit q 2)
        (eBit q 1 + eBit q 2 - eBit p 1 - eBit p 2) hE0).1
  have hβu_r : (Type200.action m).φu r = eBit p 2 • eBasis m 2 := by
    rw [hr_form, map_zsmul, phiU_eBasis_one]
  have hβt_q : (Type200.action m).φt q =
      eBit q 1 • eBasis m 1 + eBit q 2 • eBasis m 2 := by
    conv_lhs => rw [hq]
    rw [map_add, map_zsmul, map_zsmul, phiT_eBasis_one, phiT_eBasis_two]
  have hE1 : eBit p 2 • eBasis m 2 =
      (eBit q 1 + eBit p 2) • eBasis m 1 +
        (eBit q 2 + eBit p 1 + eBit p 2) • eBasis m 2 := by
    have h := hC
    rw [hβu_r, hβt_q, hs_form] at h
    rw [h]
    simp only [add_smul]
    abel
  have hE1sub : (eBit q 1 + eBit p 2) • eBasis m 1 +
      ((eBit q 2 + eBit p 1 + eBit p 2) - eBit p 2) • eBasis m 2 = 0 := by
    have hz : (eBit q 1 + eBit p 2) • eBasis m 1 +
        (eBit q 2 + eBit p 1 + eBit p 2) • eBasis m 2 -
          eBit p 2 • eBasis m 2 = 0 :=
      sub_eq_zero.mpr hE1.symm
    have hz' : (eBit q 1 + eBit p 2) • eBasis m 1 +
        ((eBit q 2 + eBit p 1 + eBit p 2) • eBasis m 2 - eBit p 2 • eBasis m 2) = 0 := by
      rw [sub_eq_add_neg] at hz ⊢
      simpa [add_assoc] using hz
    rw [← sub_smul] at hz'
    rw [show (eBit q 2 + eBit p 1 + eBit p 2) - eBit p 2 =
      eBit q 2 + eBit p 1 by ring] at hz'
    simpa using hz' 
  have hE1' : (eBit q 1 + eBit p 2) • eBasis m 1 + eBit p 1 • eBasis m 2 = 0 := by
    have h := hE1sub
    rw [hq2] at h
    rw [show (0 + eBit p 1 + eBit p 2) - eBit p 2 = eBit p 1 by ring] at h
    exact h
  have hpar1 := even_of_smul_eBasis_one_add_two_eq_zero m
    (eBit q 1 + eBit p 2) (eBit p 1) hE1'
  have hp1 : eBit p 1 = 0 := eBit_eq_zero_of_even p 1 hpar1.2
  have hq1 : eBit q 1 = eBit p 2 :=
    eq_of_even_add_of_bits (eBit_eq_zero_or_one q 1) (eBit_eq_zero_or_one p 2) hpar1.1
  let β : ℤ := eBit p 2 * ((2 ^ (m + 1) : ℕ) : ℤ)
  have hβbit : β = 0 ∨ β = (2 : ℤ) ^ (m + 1) := by
    rcases eBit_eq_zero_or_one p 2 with h | h
    · left; simp [β, h]
    · right; simp [β, h, Nat.cast_pow]
  have hp_form : p = β • gen (Type200.k m) 2 := by
    conv_lhs => rw [hp]
    rw [hp1, zero_smul, zero_add, eBasis_two, ← natCast_zsmul]
    rw [smul_smul]
  have hq_form : q = β • gen (Type200.k m) 1 := by
    conv_lhs => rw [hq]
    rw [hq1, hq2, zero_smul, add_zero, eBasis_one, ← natCast_zsmul]
    rw [smul_smul]
  have hr_form' : r = β • gen (Type200.k m) 1 := by
    conv_lhs => rw [hr_form]
    rw [eBasis_one, ← natCast_zsmul]
    rw [smul_smul]
  have hp2_eq : eBit p 2 • eBasis m 2 = β • gen (Type200.k m) 2 := by
    have h1 : p = eBit p 2 • eBasis m 2 := by
      conv_lhs => rw [hp]
      rw [hp1, zero_smul, zero_add]
    rw [← h1]
    exact hp_form
  have hs_form' : s = β • gen (Type200.k m) 2 + β • gen (Type200.k m) 1 := by
    conv_lhs => rw [hs_form]
    rw [hp1, zero_add, ← hr_form, hr_form', hp2_eq]
    abel
  refine ⟨β, hβbit, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hp_form
  · simpa [q] using hq_form
  · simpa [r] using hr_form'
  · rw [show cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = s from rfl, hs_form']
    abel




theorem type200Images_of_cocycle_values_eq_zero
    (E : TorusBasisEquivFour D hBC e f) (hL : D.L ≤ Subgroup.normalizer C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (hu : cocycleU (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (hρ : cocycleR (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0)
    (huv1 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0)
    (huv2 : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0)
    (ht1 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 1) = 0)
    (ht2 : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL
      (gen (Type200.k m) 2) = 0) :
    Type200Images D hBC hL e f E := by
  have huv : cocycleUV (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 := by
    refine cocycle_eq_zero_of_gen_eq_zero E (hL D.uv_mem_L)
      ((Type200.action m).φuv) ?_
    intro j
    fin_cases j
    · exact cocycleUV_gen0 he hf E hL
    · exact huv1
    · exact huv2
  have ht : cocycleT (D := D) (hBC := hBC) (e := e) (f := f) E hL = 0 := by
    refine cocycle_eq_zero_of_gen_eq_zero E (hL D.t_mem_L)
      ((Type200.action m).φt) ?_
    intro j
    fin_cases j
    · exact cocycleT_gen0 he hf E hL
    · exact ht1
    · exact ht2
  exact type200Images_of_cocycle_eq_zero E hL huv ht hu hρ

end TorusBasisEquivFour

end CFSG.CGT.Stroth77

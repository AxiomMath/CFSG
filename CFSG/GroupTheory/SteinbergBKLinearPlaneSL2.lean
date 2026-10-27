module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvections
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NoncommRing
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.GroupTheory.SteinbergBK

open Matrix

variable {k : Type*} [Field k]

theorem gl2_sub_one_mul_self_eq_zero {p : ℕ} [Fact p.Prime] [CharP k p] (g : GL (Fin 2) k)
    (hg : g ^ p = 1) :
    ((g : Matrix (Fin 2) (Fin 2) k) - 1) * ((g : Matrix (Fin 2) (Fin 2) k) - 1) = 0 := by
  set N := (g : Matrix (Fin 2) (Fin 2) k) - 1 with hN
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute p (Commute.one_right _), one_pow,
      ← Units.val_pow_eq_pow_val, hg, Units.val_one, sub_self]
  have hnil : IsNilpotent N := ⟨p, hNp⟩
  have hcp : N.charpoly = Polynomial.X ^ 2 := by
    have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
    rw [Fintype.card_fin] at h
    exact sub_eq_zero.mp h.eq_zero
  have := Matrix.aeval_self_charpoly N
  rw [hcp, map_pow, Polynomial.aeval_X, pow_two] at this
  exact this

theorem exists_line_of_mul_self_eq_zero_fin2 {N : Matrix (Fin 2) (Fin 2) k} (hN2 : N * N = 0)
    (hN : N ≠ 0) :
    ∃ v : Fin 2 → k, v ≠ 0 ∧ N *ᵥ v = 0 ∧ (∀ w, ∃ c : k, N *ᵥ w = c • v) ∧
      ∀ u, N *ᵥ u = 0 → ∃ c : k, u = c • v := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, N *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hN
    ext i j
    have := congrFun (hall j) i
    simpa [Matrix.mulVec_single_one] using this
  set v := N *ᵥ Pi.single j 1 with hv
  have hNv : N *ᵥ v = 0 := by rw [hv, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  set K := LinearMap.ker (Matrix.toLin' N) with hK
  have hvK : v ∈ K := by rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hNv
  have hKtop : K ≠ ⊤ := by
    intro htop
    apply hj
    have : Pi.single j 1 ∈ K := htop ▸ Submodule.mem_top
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
  have hKlt : Module.finrank k K < 2 := by
    have := Submodule.finrank_lt hKtop
    rwa [Module.finrank_fin_fun] at this
  have hspan : k ∙ v ≤ K := (Submodule.span_singleton_le_iff_mem _ _).mpr hvK
  have hKeq : k ∙ v = K := by
    refine Submodule.eq_of_le_of_finrank_eq hspan ?_
    have h1 := Submodule.finrank_mono hspan
    rw [finrank_span_singleton hj] at h1 ⊢
    omega
  have hmemK : ∀ u, N *ᵥ u = 0 → ∃ c : k, u = c • v := by
    intro u hu
    have : u ∈ k ∙ v := by rw [hKeq, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hu
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  refine ⟨v, hj, hNv, fun w => hmemK _ ?_, hmemK⟩
  rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]

@[expose] def gl2UnipotentAt (v : Fin 2 → k) : Subgroup (GL (Fin 2) k) where
  carrier := {g | ((g : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ v = 0 ∧
    ∀ w, ∃ c : k, ((g : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ w = c • v}
  one_mem' := ⟨by simp, fun w => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg⟩ ⟨hh0, hh⟩
    have hsplit : ∀ u, (((g * h : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u =
        ((g : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u + ((h : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u +
          ((g : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ (((h : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u) := by
      intro u
      rw [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, Units.val_mul]
      congr 1
      noncomm_ring
    refine ⟨?_, fun w => ?_⟩
    · rw [hsplit, hg0, hh0, Matrix.mulVec_zero, add_zero, add_zero]
    · obtain ⟨c, hc⟩ := hg w
      obtain ⟨d, hd⟩ := hh w
      refine ⟨c + d, ?_⟩
      rw [hsplit, hc, hd, Matrix.mulVec_smul, hg0, smul_zero, add_zero, add_smul]
  inv_mem' := by
    rintro g ⟨hg0, hg⟩
    have hgv : (g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hg0
      exact hg0
    have hginv : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := by
      conv_lhs => rw [← hgv]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hsplit : ∀ u, (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u =
        -(((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ
          (((g : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ u)) := by
      intro u
      rw [Matrix.mulVec_mulVec, ← Matrix.neg_mulVec]
      congr 1
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, neg_sub]
    refine ⟨by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hginv, sub_self], fun w => ?_⟩
    obtain ⟨c, hc⟩ := hg w
    exact ⟨-c, by rw [hsplit, hc, Matrix.mulVec_smul, hginv, neg_smul]⟩

theorem pow_eq_one_of_mem_gl2UnipotentAt {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    {v : Fin 2 → k} {g : GL (Fin 2) k} (hg : g ∈ gl2UnipotentAt v) : g ^ p = 1 := by
  classical
  obtain ⟨hg0, hg⟩ := hg
  set N := (g : Matrix (Fin 2) (Fin 2) k) - 1 with hN
  have hN2 : N * N = 0 := by
    have hw : ∀ w, (N * N) *ᵥ w = 0 := by
      intro w
      obtain ⟨c, hc⟩ := hg w
      rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hg0, smul_zero]
    ext i j
    simpa [Matrix.mulVec_single_one] using congrFun (hw (Pi.single j 1)) i
  have hNp : N ^ p = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
    rw [hm, pow_add, pow_two, hN2, mul_zero]
  have hgN : (g : Matrix (Fin 2) (Fin 2) k) = 1 + N := by rw [hN, add_sub_cancel]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hgN, add_pow_char_of_commute p (Commute.one_left _), one_pow, hNp,
    add_zero, Units.val_one]


@[expose] def gl2ColMatrix (v w : Fin 2 → k) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.of fun i j => ![v, w] j i

theorem mul_gl2ColMatrix {M : Matrix (Fin 2) (Fin 2) k} {v w : Fin 2 → k} {a b c d : k}
    (h1 : M *ᵥ v = a • v + c • w) (h2 : M *ᵥ w = b • v + d • w) :
    M * gl2ColMatrix v w = gl2ColMatrix v w * !![a, b; c, d] := by
  ext i j
  fin_cases j
  · have := congrFun h1 i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [gl2ColMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    simp
    linear_combination this
  · have := congrFun h2 i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [gl2ColMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    simp
    linear_combination this

omit [Field k] in
theorem gl2ColMatrix_col (v w : Fin 2 → k) : (gl2ColMatrix v w).col = ![v, w] := by
  funext j i
  fin_cases j <;> rfl


theorem exists_sl2_mulVec_single (u : Fin 2 → k) (hu : u ≠ 0) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) k,
      (s : Matrix (Fin 2) (Fin 2) k) *ᵥ Pi.single 0 1 = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq (u w : Fin 2 → k) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) k, (s : Matrix (Fin 2) (Fin 2) k) *ᵥ u = w := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_single u hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_single w hw
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((b * a⁻¹ * a : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (b : Matrix (Fin 2) (Fin 2) k) := by rw [inv_mul_cancel_right]
  rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, h1, hb]


theorem sl2_le_of_no_normal_pgroup {p : ℕ} [hp : Fact p.Prime] [Finite k] (hk : Nat.card k = p)
    (A : Subgroup (GL (Fin 2) k)) (hpA : p ∣ Nat.card A)
    (hA : ∀ N : Subgroup A, N.Normal → IsPGroup p N → N = ⊥) :
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k).range ≤ A := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : CharP k p := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hk])
  obtain ⟨g₁, hg₁⟩ := exists_prime_orderOf_dvd_card' p hpA
  have hg₁p' : g₁ ^ p = 1 := by rw [← hg₁, pow_orderOf_eq_one]
  have hg₁p : (g₁ : GL (Fin 2) k) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hg₁p', Subgroup.coe_one]
  have hg₁1 : (g₁ : GL (Fin 2) k) ≠ 1 := fun h => by
    have : g₁ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg₁
    exact hp.out.one_lt.ne hg₁
  set N₁ := ((g₁ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) - 1 with hN₁def
  have hN₁2 : N₁ * N₁ = 0 := gl2_sub_one_mul_self_eq_zero _ hg₁p
  have hN₁ : N₁ ≠ 0 := fun h => hg₁1 (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h))
  obtain ⟨v₁, hv₁0, hN₁v₁, hN₁rng, -⟩ := exists_line_of_mul_self_eq_zero_fin2 hN₁2 hN₁
  obtain ⟨g₂, hg₂A, hg₂p, hg₂v⟩ : ∃ g₂ ∈ A, g₂ ^ p = 1 ∧
      (g₂ : Matrix (Fin 2) (Fin 2) k) *ᵥ v₁ ≠ v₁ := by
    by_contra hall
    push Not at hall
    have hU : ∀ x : A, x ^ p = 1 → (x : GL (Fin 2) k) ∈ gl2UnipotentAt v₁ := by
      intro x hx
      have hxp : (x : GL (Fin 2) k) ^ p = 1 := by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
      have hxv : ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ v₁ = v₁ := hall _ x.2 hxp
      have hx0 : (((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ v₁ = 0 := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hxv, sub_self]
      refine ⟨hx0, fun w => ?_⟩
      by_cases hN : ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) - 1 = 0
      · exact ⟨0, by rw [hN, Matrix.zero_mulVec, zero_smul]⟩
      obtain ⟨v, -, -, hrng, hker⟩ :=
        exists_line_of_mul_self_eq_zero_fin2 (gl2_sub_one_mul_self_eq_zero _ hxp) hN
      obtain ⟨c₀, hc₀⟩ := hker v₁ hx0
      have hc₀0 : c₀ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc₀
        exact hv₁0 hc₀
      obtain ⟨c, hc⟩ := hrng w
      refine ⟨c * c₀⁻¹, ?_⟩
      rw [hc, hc₀, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]
    set T : Subgroup A := Subgroup.closure {x : A | x ^ p = 1} with hT
    have hTn : T.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      refine top_unique (Subgroup.le_normalizer_closure_iff.mpr ?_)
      intro g _ x hx
      refine Subgroup.subset_closure ?_
      change (g * x * g⁻¹) ^ p = 1
      rw [conj_pow, show x ^ p = 1 from hx, mul_one, mul_inv_cancel]
    have hTU : T.map A.subtype ≤ gl2UnipotentAt v₁ := by
      rw [hT, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact hU x hx
    have hTp : IsPGroup p T := by
      intro x
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      have hmem : ((x : A) : GL (Fin 2) k) ∈ gl2UnipotentAt v₁ := hTU ⟨x, x.2, rfl⟩
      have h := pow_eq_one_of_mem_gl2UnipotentAt (p := p) hmem
      simpa using h
    have hT1 : T ≠ ⊥ := by
      intro hbot
      have hg₁T : g₁ ∈ T := Subgroup.subset_closure hg₁p'
      rw [hbot, Subgroup.mem_bot] at hg₁T
      exact hg₁1 (by rw [hg₁T]; rfl)
    exact hT1 (hA T hTn hTp)
  set N₂ := (g₂ : Matrix (Fin 2) (Fin 2) k) - 1 with hN₂def
  have hN₂2 : N₂ * N₂ = 0 := gl2_sub_one_mul_self_eq_zero _ hg₂p
  set w := N₂ *ᵥ v₁ with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hg₂v
    rw [hw, hN₂def, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hN₂w : N₂ *ᵥ w = 0 := by rw [hw, Matrix.mulVec_mulVec, hN₂2, Matrix.zero_mulVec]
  have hind : LinearIndependent k ![v₁, w] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h := congrArg (fun u => N₂ *ᵥ u) hst
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN₂w, smul_zero, add_zero,
      Matrix.mulVec_zero] at h
    have hs : s = 0 := (smul_eq_zero.mp h).resolve_right hw0
    subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hw0⟩
  set P := gl2ColMatrix v₁ w with hP
  have hPunit : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hP, gl2ColMatrix_col]
    exact hind
  set PG : GL (Fin 2) k := hPunit.unit with hPG
  have hPGval : (PG : Matrix (Fin 2) (Fin 2) k) = P := rfl
  obtain ⟨r, hr⟩ := hN₁rng w
  have hg₁v₁ : ((g₁ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ v₁ =
      (1 : k) • v₁ + (0 : k) • w := by
    rw [one_smul, zero_smul, add_zero]
    have := hN₁v₁
    rw [hN₁def, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this
  have hg₁w : ((g₁ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ w = r • v₁ + (1 : k) • w := by
    rw [one_smul, ← hr, hN₁def, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  have hg₂v₁ : (g₂ : Matrix (Fin 2) (Fin 2) k) *ᵥ v₁ = (1 : k) • v₁ + (1 : k) • w := by
    rw [one_smul, one_smul, hw, hN₂def, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  have hg₂w : (g₂ : Matrix (Fin 2) (Fin 2) k) *ᵥ w = (0 : k) • v₁ + (1 : k) • w := by
    rw [zero_smul, zero_add, one_smul]
    have := hN₂w
    rw [hN₂def, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hN₁
    have h1 : N₁ * P = 0 := by
      have h := mul_gl2ColMatrix (M := N₁) (v := v₁) (w := w) (a := 0) (b := 0) (c := 0) (d := 0)
        (by rw [hN₁v₁, zero_smul, zero_smul, add_zero])
        (by rw [hr, zero_smul, zero_smul, add_zero])
      rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    calc N₁ = N₁ * P * (PG⁻¹ : GL (Fin 2) k) := by
          rw [mul_assoc, ← hPGval, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = 0 := by rw [h1, zero_mul]
  have hg₁P := mul_gl2ColMatrix hg₁v₁ hg₁w
  have hg₂P := mul_gl2ColMatrix hg₂v₁ hg₂w
  let _ : Algebra (ZMod p) k := ZMod.algebra k p
  have hfin : Module.finrank (ZMod p) k = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := k)
    rw [hk, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.out.two_le (h.symm.trans (pow_one p).symm))
  have htop := CFSG.Glauberman.Dickson.standard_two_transvections_generate_of_finrank_one r hr0 hfin
  simp only at htop
  set C := Subgroup.closure ({(g₁ : GL (Fin 2) k), g₂} : Set (GL (Fin 2) k)) with hC
  have hCA : C ≤ A := by
    rw [hC, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact g₁.2
    · exact hg₂A
  let φ : Matrix.SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k :=
    (MulAut.conj PG).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
  have hconj : ∀ (g : GL (Fin 2) k) (M : Matrix (Fin 2) (Fin 2) k) (hM : M.det = 1),
      (g : Matrix (Fin 2) (Fin 2) k) * P = P * M → φ ⟨M, hM⟩ = g := by
    intro g M hM hgM
    apply Units.ext
    change (PG : Matrix (Fin 2) (Fin 2) k) * M *
      ((PG⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = g
    rw [hPGval, ← hgM, mul_assoc, ← hPGval, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      mul_one]
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) ≤ C.comap φ := by
    rw [← htop, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · change φ _ ∈ C
      rw [hconj (g₁ : GL (Fin 2) k) _ _ hg₁P]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · change φ _ ∈ C
      rw [hconj g₂ _ _ hg₂P]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rintro _ ⟨s, rfl⟩
  apply hCA
  set s' : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨((PG⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (s : Matrix (Fin 2) (Fin 2) k) *
      (PG : Matrix (Fin 2) (Fin 2) k), by
      rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.det_one]⟩ with hs'
  have h := hle (Subgroup.mem_top s')
  have hφ : φ s' = Matrix.SpecialLinearGroup.toGL s := by
    apply Units.ext
    change (PG : Matrix (Fin 2) (Fin 2) k) * (((PG⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      (s : Matrix (Fin 2) (Fin 2) k) * (PG : Matrix (Fin 2) (Fin 2) k)) *
        ((PG⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = s
    simp only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [Subgroup.mem_comap, hφ] at h
  exact h


theorem p_reduced_linear_plane_contains_SL2 {p : ℕ} [hp : Fact p.Prime] [Finite k]
    (hk : Nat.card k = p) (A : Subgroup (GL (Fin 2) k)) (hpA : p ∣ Nat.card A)
    (hA : ∀ N : Subgroup A, N.Normal → IsPGroup p N → N = ⊥) :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) k →* GL (Fin 2) k).range ≤ A ∧
      (∀ W : Submodule k (Fin 2 → k),
        (∀ g ∈ A, ∀ w ∈ W, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (∀ u w : Fin 2 → k, u ≠ 0 → w ≠ 0 →
        ∃ g ∈ A, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ u = w) ∧
      (∀ ℓ₁ ℓ₂ : Submodule k (Fin 2 → k), Module.finrank k ℓ₁ = 1 → Module.finrank k ℓ₂ = 1 →
        ∃ g ∈ A, ℓ₁.map (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) k)) = ℓ₂) ∧
      (Odd p → (-1 : GL (Fin 2) k) ∈ A) := by
  have hSL := sl2_le_of_no_normal_pgroup hk A hpA hA
  have htrans : ∀ u w : Fin 2 → k, u ≠ 0 → w ≠ 0 →
      ∃ g ∈ A, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ u = w := by
    intro u w hu hw
    obtain ⟨s, hs⟩ := exists_sl2_mulVec_eq u w hu hw
    exact ⟨Matrix.SpecialLinearGroup.toGL s, hSL ⟨s, rfl⟩, hs⟩
  have hline : ∀ ℓ : Submodule k (Fin 2 → k), Module.finrank k ℓ = 1 →
      ∃ u : Fin 2 → k, u ≠ 0 ∧ ℓ = k ∙ u := by
    intro ℓ hℓ
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hℓ
    refine ⟨v, fun h => hv0 (Subtype.ext h), le_antisymm (fun x hx => ?_)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr v.2)⟩
    obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  refine ⟨hSL, fun W hW => ?_, htrans, fun ℓ₁ ℓ₂ h₁ h₂ => ?_, fun _ => ?_⟩
  · by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    right
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW0
    refine eq_top_iff.mpr fun u _ => ?_
    by_cases hu0 : u = 0
    · rw [hu0]
      exact W.zero_mem
    obtain ⟨g, hgA, hg⟩ := htrans w u hw0 hu0
    rw [← hg]
    exact hW g hgA w hwW
  · obtain ⟨u₁, hu₁, rfl⟩ := hline ℓ₁ h₁
    obtain ⟨u₂, hu₂, rfl⟩ := hline ℓ₂ h₂
    obtain ⟨g, hgA, hg⟩ := htrans u₁ u₂ hu₁ hu₂
    refine ⟨g, hgA, ?_⟩
    rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hg]
  · have hdet : (-1 : Matrix (Fin 2) (Fin 2) k).det = 1 := by
      simp [Matrix.det_fin_two]
    have h := hSL ⟨⟨-1, hdet⟩, rfl⟩
    have heq : Matrix.SpecialLinearGroup.toGL (⟨-1, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) k) =
        (-1 : GL (Fin 2) k) := Units.ext rfl
    rwa [heq] at h

end CFSG.GroupTheory.SteinbergBK

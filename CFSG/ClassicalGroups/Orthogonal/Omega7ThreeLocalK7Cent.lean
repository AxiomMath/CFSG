module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalBlock
public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK7Norm
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

theorem mem_Omega7_isometry {g : GL Idx K} (hg : g ∈ Omega7 K) (w : Idx → K) :
    StatedQuadOdd 3 K ((g : Matrix Idx Idx K) *ᵥ w) = StatedQuadOdd 3 K w := by
  let Iso : Subgroup (GL Idx K) :=
    { carrier := {A | ∀ v, StatedQuadOdd 3 K ((A : Matrix Idx Idx K) *ᵥ v) = StatedQuadOdd 3 K v}
      one_mem' := fun v => by simp
      mul_mem' := fun {A B} hA hB v => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
      inv_mem' := fun {A} hA v => by
        have h := hA (((A⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] at h
        exact h.symm }
  have hS : Subgroup.closure
      {A : GL Idx K | ∀ v, StatedQuadOdd 3 K ((A : Matrix Idx Idx K) *ᵥ v) =
        StatedQuadOdd 3 K v} ≤ Iso :=
    (Subgroup.closure_le Iso).2 (fun A hA => hA)
  have hΩ : Omega7 K ≤ Iso := by
    unfold Omega7 StatedOmega
    refine (Subgroup.commutator_mono hS hS).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Iso.mul_mem (Iso.mul_mem (Iso.mul_mem ha hb) (Iso.inv_mem ha)) (Iso.inv_mem hb)
  exact hΩ hg w

theorem modelQuad_conj_mulVec_of_mem_Omega7 (F : Frame K) {g : GL Idx K} (hg : g ∈ Omega7 K)
    (w : Idx → K) :
    modelQuad K F.a (((F.P⁻¹ * g * F.P : GL Idx K) : Matrix Idx Idx K) *ᵥ w) =
      modelQuad K F.a w := by
  have hPP : (F.P : Matrix Idx Idx K) * ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (F.P : Matrix Idx Idx K) *ᵥ
      (((F.P⁻¹ * g * F.P : GL Idx K) : Matrix Idx Idx K) *ᵥ w) =
        (g : Matrix Idx Idx K) *ᵥ ((F.P : Matrix Idx Idx K) *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  rw [← F.isometry, ← F.isometry w, h1, mem_Omega7_isometry hg]

theorem conj_mul_rotMat_of_commute_c₀ (F : Frame K) (v : F3Cube) {g : GL Idx K}
    (h : g * c₀GL F v = c₀GL F v * g) :
    ((F.P⁻¹ * g * F.P : GL Idx K) : Matrix Idx Idx K) * rotMat K (Multiplicative.toAdd v) =
      rotMat K (Multiplicative.toAdd v) * ((F.P⁻¹ * g * F.P : GL Idx K) : Matrix Idx Idx K) := by
  have hc : c₀GL F v = F.P * rotGL K v * F.P⁻¹ := rfl
  rw [hc] at h
  have hrot : (F.P⁻¹ * g * F.P) * rotGL K v = rotGL K v * (F.P⁻¹ * g * F.P) :=
    calc F.P⁻¹ * g * F.P * rotGL K v
        = F.P⁻¹ * (g * (F.P * rotGL K v * F.P⁻¹)) * F.P := by group
      _ = F.P⁻¹ * ((F.P * rotGL K v * F.P⁻¹) * g) * F.P := by rw [h]
      _ = rotGL K v * (F.P⁻¹ * g * F.P) := by group
  simpa [rotGL, rotHom, Units.val_mul] using
    congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) hrot

private theorem eq_one_of_isometry_commute_of_pow_eq_one [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hndvd : ¬ p ∣ cardMinusPi (Nat.card K)) {M : GL Idx K}
    (hiso : ∀ w, modelQuad K F.a ((M : Matrix Idx Idx K) *ᵥ w) = modelQuad K F.a w)
    (hcomm : ∀ v : Fin 3 → ZMod 3,
      (M : Matrix Idx Idx K) * rotMat K v = rotMat K v * (M : Matrix Idx Idx K))
    (hMp : (M : Matrix Idx Idx K) ^ p = 1) : M = 1 := by
  obtain ⟨s, c, hs, hdet, hc2, hm⟩ :=
    eq_blockMat_of_isometry_commute F.h3 F.a_ne_zero hiso hcomm
  obtain ⟨hsp, hcp⟩ := blockMat_injective (s := fun i => s i ^ p) (c := c ^ p)
    (s' := fun _ => 1) (c' := 1) (by rw [← blockMat_pow, ← hm, hMp, blockMat_one])
  have hsp' : ∀ i, s i ^ p = 1 := fun i => congrFun hsp i
  have hs1 : s = fun _ => 1 := funext fun i =>
    eq_one_of_commute_cubeRootMat_of_pow_eq_one F.hK F.h3 hp hndvd (hs i) (hdet i) (hsp' i)
  have hc1 : c = 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have h : c ^ p = c := by rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul]
    rw [← h, hcp]
  apply Units.ext
  rw [hm, hs1, hc1, blockMat_one, Units.val_one]

theorem eq_one_of_mem_centralizer_range_of_pow_eq_one [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hndvd : ¬ p ∣ cardMinusPi (Nat.card K)) {g : ↥(Omega7 K)}
    (hg : g ∈ Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K))) (hpow : g ^ p = 1) :
    g = 1 := by
  set M : GL Idx K := F.P⁻¹ * (g : GL Idx K) * F.P with hM
  have hcomm : ∀ v : Fin 3 → ZMod 3,
      (M : Matrix Idx Idx K) * rotMat K v = rotMat K v * (M : Matrix Idx Idx K) := by
    intro v
    have hgl : (g : GL Idx K) * c₀GL F (Multiplicative.ofAdd v) =
        c₀GL F (Multiplicative.ofAdd v) * (g : GL Idx K) := by
      have h := (Subgroup.mem_centralizer_iff.mp hg) (c₀ F (Multiplicative.ofAdd v))
        (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd v, rfl⟩)
      have h2 : ((c₀ F (Multiplicative.ofAdd v) : ↥(Omega7 K)) : GL Idx K) * (g : GL Idx K) =
          (g : GL Idx K) *
            ((c₀ F (Multiplicative.ofAdd v) : ↥(Omega7 K)) : GL Idx K) :=
        congrArg (fun z : ↥(Omega7 K) => (z : GL Idx K)) h
      rw [coe_c₀] at h2
      exact h2.symm
    have hrot := conj_mul_rotMat_of_commute_c₀ F (Multiplicative.ofAdd v) hgl
    simpa [hM] using hrot
  have hiso : ∀ w, modelQuad K F.a ((M : Matrix Idx Idx K) *ᵥ w) = modelQuad K F.a w := by
    intro w
    have := modelQuad_conj_mulVec_of_mem_Omega7 F (g := (g : GL Idx K)) g.2 w
    simpa [hM] using this
  have hgpow : (g : GL Idx K) ^ p = 1 := by
    have h := congrArg (fun z : ↥(Omega7 K) => (z : GL Idx K)) hpow
    simpa [Subgroup.coe_pow] using h
  have hMp : (M : Matrix Idx Idx K) ^ p = 1 := by
    have h : M ^ p = 1 := by
      rw [hM]
      have hconj : F.P⁻¹ * (g : GL Idx K) * F.P =
          (MulAut.conj F.P⁻¹) (g : GL Idx K) := by
        rw [MulAut.conj_apply, inv_inv]
      rw [hconj, ← map_pow, hgpow, map_one]
    have h' := congrArg (fun z : GL Idx K => (z : Matrix Idx Idx K)) h
    simpa using h'
  have hM1 := eq_one_of_isometry_commute_of_pow_eq_one F hp hp2 hndvd hiso hcomm hMp
  apply Subtype.ext
  have hgM : (g : GL Idx K) = F.P * M * F.P⁻¹ := by rw [hM]; group
  rw [hgM, hM1, mul_one, mul_inv_cancel, Subgroup.coe_one]

theorem not_dvd_natCard_centralizer_range [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardPlusPi (Nat.card K)) :
    ¬ p ∣ Nat.card (Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K))) := by
  intro hpC
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hndvd := not_dvd_cardMinusPi_of_dvd_cardPlusPi hp hp2 hq hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpC
  set g : ↥(Omega7 K) := (x : ↥(Omega7 K)) with hg
  have hgmem : g ∈ Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K)) := x.2
  have hgord : orderOf g = p := by rw [hg, Subgroup.orderOf_coe, hx]
  have hpow : g ^ p = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one g
  have hg1 := eq_one_of_mem_centralizer_range_of_pow_eq_one F hp hp2 hndvd hgmem hpow
  exact hp.ne_one (by rw [← hgord, hg1, orderOf_one])

theorem planeGL_mem_Omega7 [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K = cubeRootMat K * (s : Matrix _ _ K))
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (hord : orderOf s = p) (i : Fin 3) :
    F.P * planeGL K i s * F.P⁻¹ ∈ Omega7 K := by
  refine F.mem_Omega7_conj_of_odd (m := planeGL K i s) (fun w => ?_) ?_
  · exact modelQuad_planeGL_mulVec hs hdet i F.a w
  · rw [orderOf_injective (planeGL K i) (planeGL_injective i) s, hord]
    exact hp.odd_of_ne_two hp2

private theorem mem_centralizer_range_conj_planeGL [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (s : Matrix _ _ K))
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (hord : orderOf s = p) (i : Fin 3) :
    (⟨F.P * planeGL K i s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord i⟩ : ↥(Omega7 K)) ∈
      Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp ha
  rw [← hv]
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (mem_centralizer_c₀_of_model F v
      (planeGL_mem_Omega7 F hp hp2 hs hdet hord i)
      (planeGL_mul_rotMat hs i (Multiplicative.toAdd v)))).symm

private theorem orderOf_conj_planeGL [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (s : Matrix _ _ K))
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (hord : orderOf s = p) (i : Fin 3) :
    orderOf (⟨F.P * planeGL K i s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord i⟩ : ↥(Omega7 K)) = p := by
  rw [orderOf_modelElt F (planeGL_mem_Omega7 F hp hp2 hs hdet hord i),
    orderOf_injective (planeGL K i) (planeGL_injective i) s, hord]

private theorem commute_conj_planeGL [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (s : Matrix _ _ K))
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (hord : orderOf s = p) :
    Commute
      (⟨F.P * planeGL K 0 s * F.P⁻¹,
        planeGL_mem_Omega7 F hp hp2 hs hdet hord 0⟩ : ↥(Omega7 K))
      (⟨F.P * planeGL K 1 s * F.P⁻¹,
        planeGL_mem_Omega7 F hp hp2 hs hdet hord 1⟩ : ↥(Omega7 K)) := by
  have hc := planeGL_commute_of_ne (by decide : (0 : Fin 3) ≠ 1) s s
  have hGL : Commute (F.P * planeGL K 0 s * F.P⁻¹)
      (F.P * planeGL K 1 s * F.P⁻¹) := by
    have := hc.map (MulAut.conj F.P)
    simpa [MulAut.conj_apply] using this
  apply Subtype.ext
  simpa only [Subgroup.coe_mul] using hGL.eq

private theorem not_mem_zpowers_conj_planeGL [Finite K] (F : Frame K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K =
      cubeRootMat K * (s : Matrix _ _ K))
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (hord : orderOf s = p) :
    (⟨F.P * planeGL K 1 s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord 1⟩ : ↥(Omega7 K)) ∉
      Subgroup.zpowers (⟨F.P * planeGL K 0 s * F.P⁻¹,
        planeGL_mem_Omega7 F hp hp2 hs hdet hord 0⟩ : ↥(Omega7 K)) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcoe : ((⟨F.P * planeGL K 0 s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord 0⟩ : ↥(Omega7 K)) : GL Idx K) ^ k =
      (⟨F.P * planeGL K 1 s * F.P⁻¹,
        planeGL_mem_Omega7 F hp hp2 hs hdet hord 1⟩ : ↥(Omega7 K)) := by
    rw [← Subgroup.coe_zpow]
    exact congrArg (fun z : ↥(Omega7 K) => (z : GL Idx K)) hk
  have hxA : ((⟨F.P * planeGL K 0 s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord 0⟩ : ↥(Omega7 K)) : GL Idx K) =
      (MulAut.conj F.P) (planeGL K 0 s) := by rw [MulAut.conj_apply]
  have hyB : ((⟨F.P * planeGL K 1 s * F.P⁻¹,
      planeGL_mem_Omega7 F hp hp2 hs hdet hord 1⟩ : ↥(Omega7 K)) : GL Idx K) =
      (MulAut.conj F.P) (planeGL K 1 s) := by rw [MulAut.conj_apply]
  rw [hxA, hyB] at hcoe
  have hAB : (planeGL K 0 s) ^ k = planeGL K 1 s :=
    (MulAut.conj F.P).injective (by simpa only [← map_zpow] using hcoe)
  have h2 : planeGL K 1 s = planeGL K 0 (s ^ k) := by
    rw [← hAB]
    exact (map_zpow (planeGL K 0) s k).symm
  have hs1 : s = 1 := eq_one_of_planeGL_eq_planeGL (by decide : (1 : Fin 3) ≠ 0) h2
  exact hp.ne_one (by rw [← hord, hs1, orderOf_one])

theorem exists_commuting_pair_centralizer_range [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardMinusPi (Nat.card K)) :
    ∃ x y : ↥(Omega7 K),
      x ∈ Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K)) ∧
      y ∈ Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K)) ∧
      orderOf x = p ∧ orderOf y = p ∧ Commute x y ∧ y ∉ Subgroup.zpowers x := by
  obtain ⟨s, hs, hdet, hord⟩ := exists_gl_commute_cubeRootMat_orderOf_eq F.hK F.h3 hp hdvd
  refine ⟨⟨F.P * planeGL K 0 s * F.P⁻¹, planeGL_mem_Omega7 F hp hp2 hs hdet hord 0⟩,
    ⟨F.P * planeGL K 1 s * F.P⁻¹, planeGL_mem_Omega7 F hp hp2 hs hdet hord 1⟩,
    mem_centralizer_range_conj_planeGL F hp hp2 hs hdet hord 0,
    mem_centralizer_range_conj_planeGL F hp hp2 hs hdet hord 1,
    orderOf_conj_planeGL F hp hp2 hs hdet hord 0,
    orderOf_conj_planeGL F hp hp2 hs hdet hord 1,
    commute_conj_planeGL F hp hp2 hs hdet hord,
    not_mem_zpowers_conj_planeGL F hp hp2 hs hdet hord⟩

theorem two_le_pRank_centralizer_range [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardMinusPi (Nat.card K)) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hx, hy, hxp, hyp, hxy, hyx⟩ :=
    exists_commuting_pair_centralizer_range F hp hp2 hdvd
  exact CFSG.GroupTheory.two_le_pRank_of_commute hx hy hxp hyp hxy hyx

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

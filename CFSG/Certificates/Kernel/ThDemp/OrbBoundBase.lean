
module

public import CFSG.Certificates.Kernel.ThDemp.OrbEltBase
public import CFSG.Certificates.Kernel.ThDemp.OrbMain

@[expose] public section

namespace CFSG.Certificates.ThDemp.Bound

open MulAction CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp CFSG.KC.Loop
  CFSG.Certificates.ThDemp.Act CFSG.Certificates.ThDemp.Lanes CFSG.Certificates.ThDemp.Batches
  CFSG.Certificates.ThDemp.Key CFSG.Certificates.ThDemp.Rows CFSG.Certificates.ThDemp.Stab
  CFSG.Certificates.ThDemp.USp CFSG.Certificates.ThDemp.Cent CFSG.Certificates.ThDemp.Elt
  CFSG.Certificates.ThDemp.Pts

set_option exponentiation.threshold 2000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

variable {J : Subgroup (GL (Fin 248) (ZMod 2))} {D : DempData} {O : OrbData}

structure OrbChecks (D : DempData) (O : OrbData) : Prop where
  inv : invChk D O = true
  batch : ∀ i < 9, ∀ y3 < 24, batchChk D O i y3 = true
  cross56 : ∀ y3 < 24, crossChk D O 5 6 y3 = true
  cross78 : ∀ y3 < 24, crossChk D O 7 8 y3 = true
  ky : ∀ i < 9, kyChk D O i = true
  low : ∀ i < 9, lowChk D O i = true
  orb : orbChk D O = true
  codes : codesChk D O = true
  elt1 : eltChk1 D O = true
  cent : centChk D O = true
  q : qChk D O = true
  norm : normChk D O = true
  sb : ∀ i : Fin 9, lget O.sb i = OrbMain.sOf i
  w9 : lgetL O.words 9 ≠ []

theorem codesChk_facts (h : codesChk D O = true) :
    codeChk D O.x5 = true ∧ codeChk D O.x31 = true ∧ codeChk D O.yb = true ∧
      codeChk D O.dm = true := by
  unfold codesChk at h
  obtain ⟨h1, h⟩ := Unfold.andB_split h
  obtain ⟨h2, h⟩ := Unfold.andB_split h
  obtain ⟨h3, h4⟩ := Unfold.andB_split h
  exact ⟨h1, h2, h3, h4⟩

theorem vecMul_ne_zero (g : J) {w : Fin 248 → ZMod 2} (hw : w ≠ 0) : Matrix.vecMul w (𝕄 g) ≠ 0 := by
  intro h
  apply hw
  have := congrArg (fun u => Matrix.vecMul u (𝕄 g⁻¹)) h
  simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
  rwa [mat_mul_inv, Matrix.vecMul_one] at this

theorem not_kill_map {A X Y : Matrix (Fin 248) (Fin 248) (ZMod 2)} (g : J) (hg : 𝕄 g = A)
    (hAX : A * X = Y * A) (q : ℕ) (hY : ¬ KillU D (Qm q Y)) :
    ∃ w ∈ mapM A (sp (U0 D)), Matrix.vecMul w (Qm q X) ≠ 0 := by
  unfold KillU at hY
  obtain ⟨w', hw', hne⟩ := not_forall₂.mp hY
  refine ⟨Matrix.vecMul w' A, Submodule.mem_map_of_mem (f := Matrix.vecMulLinear A) hw', ?_⟩
  rw [Matrix.vecMul_vecMul, Qm_semiconj q hAX, ← Matrix.vecMul_vecMul, ← hg]
  exact vecMul_ne_zero g hne

namespace Ctx


theorem pow_mul_inv {G : Type*} [Group G] {x m : G} (h : x * m⁻¹ = m⁻¹ * x ^ 5) :
    ∀ k : ℕ, x ^ k * m⁻¹ = m⁻¹ * x ^ (5 * k)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, mul_assoc, h, ← mul_assoc, pow_mul_inv h k, mul_assoc, ← pow_add]
    congr 2

end Ctx

end CFSG.Certificates.ThDemp.Bound

end

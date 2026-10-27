
module

public import CFSG.Certificates.Kernel.ThCent.WitSoundBase

public import CFSG.Certificates.Kernel.ThCent.Model
public import CFSG.Certificates.Kernel.Th.Spec.FwdRel
import CFSG.Certificates.Kernel.Th.Max3S.Words

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.Sporadic.Bridge

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem conj_of_witOK {p : TauCeti.GroupPresentation} {J : Subgroup (GL (Fin 248) (ZMod 2))}
    (a b : J) (ψ : p.Group →* J) {RB : ℕ → ℕ}
    {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE GR IR Bi : ℕ}
    (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hx : ∀ g < 8, 𝕄 (ψ (presGen p g)) = pkMat (RB (BigS.regAt GR g)) ∧
      𝕄 ((ψ (presGen p g))⁻¹ : J) = pkMat (RB (BigS.regAt IR g)))
    (hA : 𝕄 a = pkMat (RB 1)) (hB : 𝕄 b = pkMat (RB 2)) (hBi : 𝕄 (b⁻¹ : J) = pkMat Bi)
    {Z hw hn tw tn : ℕ} (h : witOK RB c rm ONE Bi GR IR Z hw hn tw tn = true) (z : J)
    (hz : 𝕄 z = pkMat Z) : IsConj z (ψ (wval (presGen p) (codes4 tw tn))) := by
  let L : ℕ → J := fun d => if d = 0 then a else if d = 1 then b else b⁻¹
  have hL : ∀ d, 𝕄 (L d) = pkMat (wordLetter (RB 1) (RB 2) Bi d) := by
    intro d
    unfold wordLetter
    by_cases h0 : d = 0
    · simp only [L, if_pos h0]
      exact hA
    · by_cases h1 : d = 1
      · simp only [L, if_neg h0, if_pos h1]
        exact hB
      · simp only [L, if_neg h0, if_neg h1]
        exact hBi
  let H : J := ((List.range hn).map fun i => L (BigS.bitsN hw (2 * i) 2)).prod
  have hH : 𝕄 H = pkMat (BigS.wordAB c rm ONE (RB 1) (RB 2) Bi hw hn) := by
    rw [CFSG.KC.Th.Max3S.pkMat_wordAB_range hk, mat_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => hL _
  have hT := pkMat_prodWord (fun g => ψ (presGen p g)) (fun g hg => (hx g hg).1)
    (fun g hg => (hx g hg).2) hk tw tn
  rw [← wordProd_hom ψ (presGen p)] at hT
  have e : H * z = ψ (wordProd (presGen p) (codeWord tw tn)) * H := by
    apply mat_injective
    change 𝕄 H * 𝕄 z = 𝕄 (ψ (wordProd (presGen p) (codeWord tw tn))) * 𝕄 H
    rw [hH, hz, ← hT, ← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h]
  rw [← wordProd_codeWord]
  refine isConj_iff.2 ⟨H, ?_⟩
  rw [e, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.KC.ThCent

end

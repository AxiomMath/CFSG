
module

public import CFSG.Certificates.Kernel.ThCent.Model
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
import CFSG.Certificates.Kernel.Th.Max3S.WordsBase
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.Sporadic.Bridge

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem wordProd_hom {G H : Type*} [Group G] [Group H] (ψ : G →* H) (x : ℕ → G) :
    ∀ w : List (ℕ × Bool), ψ (wordProd x w) = wordProd (fun g => ψ (x g)) w
  | [] => by simp [wordProd]
  | l :: w => by
    have ih := wordProd_hom ψ x w
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, ih]
    split <;> simp

theorem letter_code {G : Type*} [Group G] (x : ℕ → G) {y : ℕ} (hy : y < 16) :
    (if (codeLetter y).2 then x (codeLetter y).1 else (x (codeLetter y).1)⁻¹) =
      CFSG.Certificates.LCE.letV x y := by
  unfold codeLetter CFSG.Certificates.LCE.letV
  have h255 : y ≠ 255 := by omega
  by_cases h : y % 2 = 0
  · simp [h, h255]
  · simp [h, h255]

theorem wordProd_codeWord {G : Type*} [Group G] (x : ℕ → G) (tw tn : ℕ) :
    wordProd x (codeWord tw tn) = wval x (codes4 tw tn) := by
  unfold wordProd codeWord wval codes4
  rw [List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  have hlt : BigS.bitsN tw (4 * i) 4 < 16 := by
    rw [bitsN_eq]
    exact Nat.mod_lt _ (by norm_num)
  exact letter_code x hlt

end CFSG.KC.ThCent

end

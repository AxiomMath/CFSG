module

public import Certificates.Data.Kernel.LyY.Pair
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut

public section

namespace CFSG.KC.LyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Enum CFSG.KS.Mathieu
open CFSG.Sporadic.Recognition.LyonsSims.Ly1080 (pairG)
open CFSG.Sporadic.Th (wordG)

theorem strictN_eqW (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

section Letters

variable {n : ℕ} {x xi f g : ℕ → ℕ} {α β : Equiv.Perm (Fin n)}
  (hx : ∀ p (h : p < n), x p = α ⟨p, h⟩) (hxi : ∀ p (h : p < n), xi p = α⁻¹ ⟨p, h⟩)
  (hf : ∀ p (h : p < n), f p = β ⟨p, h⟩) (hg : ∀ p (h : p < n), g p = β⁻¹ ⟨p, h⟩)
include hx hxi hf hg

theorem letP_icode {l : ℤ} (hl : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) (p : ℕ) (hp : p < n) :
    letP x xi f g (icode l) p = (pairG α β l ⟨p, hp⟩ : ℕ) := by
  rcases hl with rfl | rfl | rfl | rfl
  · change x p = _
    rw [hx p hp]
    rfl
  · change xi p = _
    rw [hxi p hp]
    unfold pairG
    rw [if_neg (by decide), if_pos rfl]
  · change f p = _
    rw [hf p hp]
    unfold pairG
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  · change g p = _
    rw [hg p hp]
    unfold pairG
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem wP_eq : ∀ wd : List ℤ, (∀ l ∈ wd, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) →
    ∀ p (hp : p < n), wP x xi f g wd p = (wordG (pairG α β) wd ⟨p, hp⟩ : ℕ)
  | [], _, p, hp => rfl
  | z :: zs, hw, p, hp => by
    have ih := wP_eq zs (fun l hl => hw l (List.mem_cons_of_mem z hl)) p hp
    change strictN (wP x xi f g zs p) (fun q => letP x xi f g (icode z) q) = _
    rw [strictN_eqW, ih, letP_icode hx hxi hf hg (hw z List.mem_cons_self) _ (Fin.is_lt _)]
    simp only [wordG, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

end Letters

theorem wordFix_iff {n w X XI Y YI : ℕ} {α β : Equiv.Perm (Fin n)} (hX : Raw.Orb.PRep n w X α)
    (hXI : Raw.Orb.PRep n w XI α⁻¹) (hY : Raw.Orb.PRep n w Y β) (hYI : Raw.Orb.PRep n w YI β⁻¹)
    {wd : List ℤ} (hw : ∀ l ∈ wd, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    wordFix n w X XI Y YI wd = true ↔ wordG (pairG α β) wd = 1 := by
  have e := wP_eq (x := fun q => pg w (mask w) X q) (xi := fun q => pg w (mask w) XI q)
    (f := fun q => pg w (mask w) Y q) (g := fun q => pg w (mask w) YI q)
    (fun p h => hX ⟨p, h⟩) (fun p h => hXI ⟨p, h⟩) (fun p h => hY ⟨p, h⟩) (fun p h => hYI ⟨p, h⟩)
    wd hw
  unfold wordFix
  rw [Raw.Orb.allN_iff]
  constructor
  · intro h
    refine Equiv.ext fun q => Fin.ext ?_
    have := Nat.eq_of_beq_eq_true (h q q.2)
    rw [e q q.2] at this
    exact this
  · intro h p hp
    rw [e p hp, h]
    exact Nat.beq_refl p

end CFSG.KC.LyY

end

module

public import Certificates.Data.S5Ext
public import CFSG.CGT.PushingUpLit.J42.S5Model

public section

namespace CFSG.CGT.PushingUpLit.SolK.S5Ext

theorem pmul_eq (i j : Fin 32) : pmul i j = extraMulFin i j := rfl

theorem word_eval : ∀ i : Fin 32, evalW pgen (pword i) = i := by decide

theorem pmul_self_eq : ∀ x : Fin 32, pmul x x = x → x = 0 := by decide

theorem foldl_hom (f : Fin 32 → Fin 32) (hf : ∀ i j, f (pmul i j) = pmul (f i) (f j))
    (g : Nat → Fin 32) (w : List Nat) : ∀ a : Fin 32,
    f (w.foldl (fun acc k => pmul acc (g k)) a) =
      w.foldl (fun acc k => pmul acc (f (g k))) (f a) := by
  induction w with
  | nil => intro a; rfl
  | cons k w ih => intro a; simp only [List.foldl_cons]; rw [ih, hf]

theorem hom_evalW (f : Fin 32 → Fin 32) (hf : ∀ i j, f (pmul i j) = pmul (f i) (f j))
    (h0 : f 0 = 0) (g : Nat → Fin 32) (w : List Nat) :
    f (evalW g w) = evalW (fun k => f (g k)) w := by
  unfold evalW; rw [foldl_hom f hf g w 0, h0]

theorem gens4_eq (f : Fin 32 → Fin 32) :
    gens4 (f 1) (f 2) (f 8) (f 16) = fun k => f (pgen k) := by
  funext k; unfold gens4 pgen; split_ifs <;> rfl

theorem hom_ext_gens (f g : Fin 32 → Fin 32) (hf : ∀ i j, f (pmul i j) = pmul (f i) (f j))
    (hg : ∀ i j, g (pmul i j) = pmul (g i) (g j)) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h8 : f 8 = g 8) (h16 : f 16 = g 16) : f = g := by
  have hk : (fun k => f (pgen k)) = fun k => g (pgen k) := by
    rw [← gens4_eq f, ← gens4_eq g, h1, h2, h8, h16]
  funext i
  calc f i = f (evalW pgen (pword i)) := by rw [word_eval]
    _ = evalW (fun k => f (pgen k)) (pword i) := hom_evalW f hf hf0 _ _
    _ = evalW (fun k => g (pgen k)) (pword i) := by rw [hk]
    _ = g (evalW pgen (pword i)) := (hom_evalW g hg hg0 _ _).symm
    _ = g i := by rw [word_eval]

end CFSG.CGT.PushingUpLit.SolK.S5Ext


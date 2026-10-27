module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.ParrottCert

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

open CFSG.LocalAnalysis.EvenBN.Tits.Model

abbrev Mat5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 2)

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] noncomputable def pbasis : Fin 5 → Equiv.Perm (Fin 1755) :=
  ![parrottV 12, parrottV 11, parrottV 10, parrottV 9, parrottV 7]

@[expose] def Acts (π : Equiv.Perm (Fin 1755)) (M : Mat5) : Prop :=
  ∀ i, π * pbasis i * π⁻¹ = (List.ofFn fun j => pbasis j ^ (M i j).val).prod

@[expose] def xMat (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) : Mat6 :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    d₁, d₂, d₃, 0, 1, 0; e₁, e₂, e₃, e₄, 0, 1]

@[expose] def sMat (T : Mat5) : Mat6 :=
  Matrix.of fun i j =>
    if h : i.val < 5 ∧ j.val < 5 then T ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if i.val = 5 ∧ j.val = 5 then 1 else 0

@[expose] def blk (M : Mat6) : Mat5 := fun i j => M i.castSucc j.castSucc

@[expose] def prodRev (ls : List Mat6) : Mat6 := ls.foldr (fun a acc => acc * a) 1

abbrev Letter : Type := Option (Fin 4)

@[expose] def letterMat (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) (T : Fin 4 → Mat5) : Letter → Mat6
  | none => xMat e₁ e₂ e₃ e₄ d₁ d₂ d₃
  | some j => sMat (T j)

@[expose] def WordOK (SL : Set Mat5) (T : Fin 4 → Mat5) (w : List Letter)
    (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) : Prop :=
  (∀ j : Fin 6, (prodRev (w.map (letterMat e₁ e₂ e₃ e₄ d₁ d₂ d₃ T))) 5 j = if j = 5 then 1 else 0) ∧
    blk (prodRev (w.map (letterMat e₁ e₂ e₃ e₄ d₁ d₂ d₃ T))) ∉ SL

theorem pow_val_add {G : Type*} [Group G] {b : G} (hb : b * b = 1) (x y : ZMod 2) :
    b ^ (x + y).val = b ^ x.val * b ^ y.val := by
  have h2 : ∀ k : ℕ, b ^ (k % 2) = b ^ k := fun k => by
    conv_rhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, sq, hb, one_pow, one_mul]
  rw [ZMod.val_add, h2, pow_add]

theorem ofFn_prod_pow_add {G : Type*} [Group G] {m : ℕ} (b : Fin m → G)
    (hc : ∀ i j, b i * b j = b j * b i) (hs : ∀ i, b i * b i = 1) (n n' : Fin m → ZMod 2) :
    (List.ofFn fun j => b j ^ (n j + n' j).val).prod =
      (List.ofFn fun j => b j ^ (n j).val).prod * (List.ofFn fun j => b j ^ (n' j).val).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih (fun j => b j.succ) (fun i j => hc _ _) (fun i => hs _) (fun j => n j.succ)
      (fun j => n' j.succ), pow_val_add (hs 0)]
    set P := (List.ofFn fun j : Fin m => b j.succ ^ (n j.succ).val).prod
    set P' := (List.ofFn fun j : Fin m => b j.succ ^ (n' j.succ).val).prod
    have hcm : Commute (b 0 ^ (n' 0).val) P := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (show Commute (b 0) (b j.succ) from hc _ _).pow_pow _ _
    calc b 0 ^ (n 0).val * b 0 ^ (n' 0).val * (P * P')
        = b 0 ^ (n 0).val * ((b 0 ^ (n' 0).val * P) * P') := by simp only [mul_assoc]
      _ = b 0 ^ (n 0).val * ((P * b 0 ^ (n' 0).val) * P') := by rw [hcm.eq]
      _ = _ := by simp only [mul_assoc]

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

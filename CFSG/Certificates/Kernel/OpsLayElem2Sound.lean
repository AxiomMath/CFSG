module

public import Certificates.Data.Kernel.OpsLayElem2
public import CFSG.Certificates.Kernel.OpsLayGKFSound

public section

namespace CFSG.KC.OpsLayElem2

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsV4

variable {M V₀ V : Type} {O₀ : Ops M V₀} {O : Ops Nat V}

theorem letterN_of (S : Sim O₀ O) {X Y : M × M} {x y : Nat × Nat} (hx₁ : S.R X.1 x.1)
    (hx₂ : S.R X.2 x.2) (hy₁ : S.R Y.1 y.1) (hy₂ : S.R Y.2 y.2) (l : ℤ) :
    S.R (letterN O₀ X Y l) (letterN O x y l) := by
  unfold letterN
  split_ifs
  · exact hx₁
  · exact hx₂
  · exact hy₁
  · exact hy₂
  · exact S.one

theorem signedWordN_of (S : Sim O₀ O) {X Y : M × M} {x y : Nat × Nat} (hx₁ : S.R X.1 x.1)
    (hx₂ : S.R X.2 x.2) (hy₁ : S.R Y.1 y.1) (hy₂ : S.R Y.2 y.2) :
    ∀ w : List ℤ, S.R (signedWordN O₀ X Y w) (signedWordN O x y w)
  | [] => S.one
  | l :: w => S.mul (letterN_of S hx₁ hx₂ hy₁ hy₂ l) (signedWordN_of S hx₁ hx₂ hy₁ hy₂ w)

theorem forall₂_signedWordN (S : Sim O₀ O) {X Y : M × M} {x y : Nat × Nat} (hx₁ : S.R X.1 x.1)
    (hx₂ : S.R X.2 x.2) (hy₁ : S.R Y.1 y.1) (hy₂ : S.R Y.2 y.2) :
    ∀ ws : List (List ℤ),
      List.Forall₂ S.R (ws.map (signedWordN O₀ X Y)) (ws.map (signedWordN O x y))
  | [] => .nil
  | w :: ws => .cons (signedWordN_of S hx₁ hx₂ hy₁ hy₂ w)
      (forall₂_signedWordN S hx₁ hx₂ hy₁ hy₂ ws)

theorem kerOK2_of (S : Sim O₀ O) {Xs : List M} {xs : List Nat} (h : List.Forall₂ S.R Xs xs)
    {tests : List Nat} (hT : ∀ k ∈ tests, S.T k) (hk : kerOK2 O xs tests = true) :
    kerOK2 O₀ Xs tests = true := by
  unfold kerOK2 at hk ⊢
  rw [h.length_eq]
  refine List.all_eq_true.2 fun n hn => ?_
  obtain ⟨k, hk', hv⟩ := List.any_eq_true.1 (List.all_eq_true.1 hk n hn)
  exact List.any_eq_true.2 ⟨k, hk', S.vne
    (CFSG.KC.OpsLayGKF.appBase_of S 2 h (n + 1) (S.unit (hT k hk'))) (S.unit (hT k hk')) hv⟩

theorem elem2OK_of (S : Sim O₀ O) {Xs : List M} {xs : List Nat} (h : List.Forall₂ S.R Xs xs)
    {tests : List Nat} (hT : ∀ k ∈ tests, S.T k) (he : elem2OK O xs tests = true) :
    elem2OK O₀ Xs tests = true := by
  unfold elem2OK at he ⊢
  simp only [Bool.and_eq_true] at he ⊢
  exact ⟨⟨all_of_forall₂ (p := sqOK O₀) (q := sqOK O)
    (fun _ _ hX hs => S.eq (S.mul hX hX) S.one hs) h he.1.1, S.commsOK h he.1.2⟩,
    kerOK2_of S h hT he.2⟩

theorem forceL_eq : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    change strictB x (fun v => forceL xs fun vs => k (v :: vs)) = _
    rw [SecS.strictB_eq, forceL_eq xs]

theorem elem2K_sound {c : Lay} {d A B : Nat} (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    {X Y : Array CFSG.F3.Native.V × Array CFSG.F3.Native.V} (hX₁ : Snd.LRel c X.1 A) (hX₂ : Snd.LRel c X.2 A)
    (hY₁ : Snd.LRel c Y.1 B) (hY₂ : Y.2 = (ops3 c.d).pow Y.1 12) {ws : List (List ℤ)}
    {tests : List Nat} (h : elem2K c A B ws tests = true) :
    elem2OK (ops3 d) (ws.map (signedWordN (ops3 d) X Y)) tests = true := by
  subst hd
  unfold elem2K at h
  rw [SecS.strictB_eq, forceL_eq, Bool.and_eq_true] at h
  have hY₂' : Snd.LRel c Y.2 (powK c B 12) := by
    rw [hY₂]
    exact Snd.rel_pow hc hp hY₁ (by norm_num)
  exact elem2OK_of (Sim.ofL3 c hc hp)
    (forall₂_signedWordN (Sim.ofL3 c hc hp) (x := (A, A)) (y := (B, powK c B 12)) hX₁ hX₂ hY₁ hY₂'
      ws) (fun k hk => Snd.lt_of_all h.1 hk) h.2

end CFSG.KC.OpsLayElem2

end

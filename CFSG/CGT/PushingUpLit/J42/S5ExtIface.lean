module

public import CFSG.CGT.PushingUpLit.J42.S5Model

public section

namespace CFSG.CGT.PushingUpLit.SolK

structure S5Iface where
  N : ℕ
  tab : ℕ → Fin 32 → Fin 32
  cm : ℕ → ℕ → ℕ
  inv : ℕ → ℕ
  ide : ℕ
  ci : Fin 32 → ℕ
  InCat : (ℕ → Prop) → Prop
  complete : ∀ f : Fin 32 → Fin 32, (∀ i j, f (extraMulFin i j) = extraMulFin (f i) (f j)) →
    Function.Injective f → ∃ e, e < N ∧ tab e = f
  tab_inj : ∀ e e', e < N → e' < N → tab e = tab e' → e = e'
  cm_lt : ∀ e f, e < N → f < N → cm e f < N
  cm_tab : ∀ e f, e < N → f < N → ∀ x, tab (cm e f) x = tab e (tab f x)
  ide_lt : ide < N
  ide_tab : ∀ x, tab ide x = x
  inv_lt : ∀ e, e < N → inv e < N
  cm_inv : ∀ e, e < N → cm e (inv e) = ide
  ci_lt : ∀ i, ci i < N
  ci_tab : ∀ i x, extraMulFin (tab (ci i) x) i = extraMulFin i x
  cat_one : InCat (fun e => e = ide)
  cat_step : ∀ S : ℕ → Prop, InCat S → ∀ g, g < N → ¬ S g → S (cm g g) →
    (∀ c, c < N → S c → S (cm (cm g c) (inv g))) →
    InCat (fun e => S e ∨ ∃ c, c < N ∧ S c ∧ cm g c = e)
  cat_wit : ∀ S : ℕ → Prop, InCat S → ∃ (as : List ℕ) (ts : List (Fin 32)),
    as.length + ts.length ≤ 4 ∧ (∀ a ∈ as, a < N ∧ S a) ∧ (∀ t ∈ ts, S (ci t)) ∧
    (∀ P : ℕ → Prop, (∀ i, S (ci i) → P (ci i)) →
      (∀ a ∈ as, ∀ x, x < N → P x → P (cm a x)) → ∀ α, α < N → S α → P α) ∧
    (∀ Q : Fin 32 → Prop, (∀ α, α < N → S α → ∀ t ∈ ts, Q (tab α t)) →
      (∀ x y, Q x → Q y → Q (extraMulFin x y)) → ∀ i, S (ci i) → Q i)

structure S5Rho {K : Type*} [Group K] (D : ExtraData K) (I : S5Iface) where
  rho : K → ℕ
  rho_lt : ∀ k, rho k < I.N
  rho_conj : ∀ k i, D.nf (I.tab (rho k) i) = k * D.nf i * k⁻¹
  rho_mul : ∀ k k', rho (k * k') = I.cm (rho k) (rho k')
  rho_one : rho 1 = I.ide
  rho_inv : ∀ k, I.inv (rho k) = rho k⁻¹
  rho_ker : ∀ k k', rho k = rho k' → k' = k ∨ k' = k * D.nf 4
  rho_nf : ∀ i, rho (D.nf i) = I.ci i
  rho_z : rho (D.nf 4) = I.ide
  z_central : ∀ k : K, k * D.nf 4 = D.nf 4 * k
  z_sq : D.nf 4 * D.nf 4 = 1

end CFSG.CGT.PushingUpLit.SolK

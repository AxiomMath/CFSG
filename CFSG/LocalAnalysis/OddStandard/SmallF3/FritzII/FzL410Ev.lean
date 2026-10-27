module

public import Certificates.Data.FzL410Norm
import Mathlib.Tactic.Abel

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open _root_.Certificates

theorem fz410_ev_add {g1 g2 g3 g4 : FzL410.A} (h3 : (2 : ℕ) • g3 = 0) (h4 : (2 : ℕ) • g4 = 0)
    (p q : FzL410.A) :
    FzL410.ev g1 g2 g3 g4 (p + q) = FzL410.ev g1 g2 g3 g4 p + FzL410.ev g1 g2 g3 g4 q := by
  have h4g : ∀ g : FzL410.A, (4 : ℕ) • g = 0 := by decide +kernel
  have key : ∀ {g : FzL410.A} {n : ℕ}, n • g = 0 → ∀ m : ℕ, (m % n) • g = m • g := by
    intro g n h m
    conv_rhs => rw [← Nat.mod_add_div m n]
    rw [add_nsmul, mul_nsmul, h]
    simp
  unfold FzL410.ev
  simp only [Prod.fst_add, Prod.snd_add, ZMod.val_add]
  rw [key (h4g g1), key (h4g g2), key h3, key h4]
  simp only [add_nsmul]
  abel

theorem fz410_ev_zero (g1 g2 g3 g4 : FzL410.A) : FzL410.ev g1 g2 g3 g4 0 = 0 := by
  simp [FzL410.ev]

@[expose] def fz410EvHom (g1 g2 g3 g4 : FzL410.A) (h3 : (2 : ℕ) • g3 = 0)
    (h4 : (2 : ℕ) • g4 = 0) : FzL410.A →+ FzL410.A where
  toFun := FzL410.ev g1 g2 g3 g4
  map_zero' := fz410_ev_zero g1 g2 g3 g4
  map_add' := fz410_ev_add h3 h4

theorem fz410_hom_eq_ev (f : FzL410.A →+ FzL410.A) (p : FzL410.A) :
    f p = FzL410.ev (f (1, 0, 0, 0)) (f (0, 1, 0, 0)) (f (0, 0, 1, 0)) (f (0, 0, 0, 1)) p := by
  have h : FzL410.ev (1, 0, 0, 0) (0, 1, 0, 0) (0, 0, 1, 0) (0, 0, 0, 1) p = p := by
    revert p
    decide +kernel
  calc f p = f (FzL410.ev (1, 0, 0, 0) (0, 1, 0, 0) (0, 0, 1, 0) (0, 0, 0, 1) p) := by rw [h]
    _ = _ := by simp only [FzL410.ev, map_add, map_nsmul]

theorem fz410_hom_gen_two (f : FzL410.A →+ FzL410.A) :
    (2 : ℕ) • f (0, 0, 1, 0) = 0 ∧ (2 : ℕ) • f (0, 0, 0, 1) = 0 := by
  have h1 : (2 : ℕ) • ((0, 0, 1, 0) : FzL410.A) = 0 := by decide +kernel
  have h2 : (2 : ℕ) • ((0, 0, 0, 1) : FzL410.A) = 0 := by decide +kernel
  exact ⟨by rw [← map_nsmul, h1, map_zero], by rw [← map_nsmul, h2, map_zero]⟩

theorem fz410_rho_add (p q : FzL410.A) :
    FzL410.rho (p + q) = FzL410.rho p + FzL410.rho q := by
  revert p q
  decide +kernel

theorem fz410_rho_cube (p : FzL410.A) :
    FzL410.rho (FzL410.rho (FzL410.rho p)) = p := by
  revert p
  decide +kernel

theorem fz410_tt_tt (p : FzL410.A) : FzL410.tt (FzL410.tt p) = p := by
  revert p
  decide +kernel

theorem fz410_tt_ss (p : FzL410.A) : FzL410.tt (FzL410.ss p) = FzL410.ss (FzL410.tt p) := by
  revert p
  decide +kernel

theorem fz410_evEq_add {c d : FzL410.A} (hd : (2 : ℕ) • d = 0) (p q : FzL410.A) :
    FzL410.evEq c d (p + q) = FzL410.evEq c d p + FzL410.evEq c d q := by
  have h4 : (2 : ℕ) • FzL410.rho d = 0 := by
    have h := fz410_rho_add d d
    have h0 : FzL410.rho 0 = 0 := by decide +kernel
    rw [two_nsmul, ← h, ← two_nsmul, hd, h0]
  exact fz410_ev_add hd h4 p q

theorem fz410_evEq_zero (c d : FzL410.A) : FzL410.evEq c d 0 = 0 := by
  exact fz410_ev_zero _ _ _ _

@[expose] def fz410EvEqHom (c d : FzL410.A) (hd : (2 : ℕ) • d = 0) : FzL410.A →+ FzL410.A where
  toFun := FzL410.evEq c d
  map_zero' := fz410_evEq_zero c d
  map_add' := fz410_evEq_add hd

theorem fz410_eq_evEq (σ : FzL410.A →+ FzL410.A)
    (hσ : ∀ p, σ (FzL410.rho p) = FzL410.rho (σ p)) (p : FzL410.A) :
    σ p = FzL410.evEq (σ (1, 0, 0, 0)) (σ (0, 0, 1, 0)) p := by
  have h := fz410_hom_eq_ev σ p
  have h1 : σ (0, 1, 0, 0) = FzL410.rho (σ (1, 0, 0, 0)) := by
    rw [← hσ]; rfl
  have h2 : σ (0, 0, 0, 1) = FzL410.rho (σ (0, 0, 1, 0)) := by
    rw [← hσ]; rfl
  rw [h, h1, h2]
  rfl

theorem fz410_eq_evAn (σ : FzL410.A →+ FzL410.A)
    (hσ : ∀ p, σ (FzL410.rho p) = FzL410.rho (FzL410.rho (σ p))) (p : FzL410.A) :
    σ p = FzL410.evAn (σ (1, 0, 0, 0)) (σ (0, 0, 1, 0)) p := by
  have h := fz410_hom_eq_ev σ p
  have h1 : σ (0, 1, 0, 0) = FzL410.rho (FzL410.rho (σ (1, 0, 0, 0))) := by
    rw [← hσ]; rfl
  have h2 : σ (0, 0, 0, 1) = FzL410.rho (FzL410.rho (σ (0, 0, 1, 0))) := by
    rw [← hσ]; rfl
  rw [h, h1, h2]
  rfl

theorem fz410_hom_inv (ψ : FzL410.A →+ FzL410.A) (hψ : Function.Injective ψ) :
    ∃ ψ' : FzL410.A →+ FzL410.A, (∀ p, ψ (ψ' p) = p) ∧ ∀ p, ψ' (ψ p) = p := by
  have hb : Function.Bijective ψ := Finite.injective_iff_bijective.mp hψ
  let e : FzL410.A ≃+ FzL410.A := AddEquiv.ofBijective ψ hb
  exact ⟨e.symm.toAddMonoidHom, fun p => e.apply_symm_apply p, fun p => e.symm_apply_apply p⟩

end CFSG.OddStandard.SmallF3.FritzII

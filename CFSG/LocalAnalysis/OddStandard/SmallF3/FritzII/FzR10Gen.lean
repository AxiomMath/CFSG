module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Rules
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10 Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

open Classical in
@[expose] noncomputable def fzrOrdClass (g : G) : ℕ :=
  if g = 1 then 1 else if g ^ 2 = 1 then 2 else if g ^ 4 = 1 then 4 else
    if g ^ 8 = 1 then 8 else 16

structure FzRNum (t x₁ x₂ lam rho tau : G) (T₂ : Subgroup G) : Type where
  par : Par
  mu : ℕ → G
  mu_mem : ∀ n, mu n ∈ T₂
  mu_zero : mu 0 = 1
  mu_mul : ∀ n m, n < 512 → m < 512 → mu (par.e n m) = mu n * mu m
  mu_inj : ∀ n m, n < 512 → m < 512 → mu n = mu m → n = m
  mu_surj : ∀ g ∈ T₂, ∃ n, n < 512 ∧ mu n = g
  tI_eq : par.tI = 64
  sI_eq : par.sI = 128
  mu_tI : mu 64 = t
  mu_sI : mu 128 = tau
  e_lt : ∀ x y, x < 512 → y < 512 → par.e x y < 512
  gens_lt : ∀ g ∈ par.gens.toList, g < 512
  rho_lt : ∀ x, x < 256 → par.rhoMap x < 512
  mu_rho : ∀ x, x < 256 → mu (par.rhoMap x) = rho * mu x * rho⁻¹
  mu_inW : ∀ x, par.inW x = true → mu x ∈ ctxW t x₁ x₂
  mu_inTL : ∀ x, x < 512 → par.inTL x = true → mu x ∈ wreathGrp x₁ x₂ lam
  mu_inTZ : ∀ z ∈ fourGrp x₁ x₂, ∀ x, x < 512 → mu x = t * z → par.inTZ x = true
  t_mem : t ∈ T₂
  t_sq : t ^ 2 = 1
  tau_sq1 : tau ^ 2 = 1
  tau_t : tau * t * tau⁻¹ = t

variable {t : G} {x₁ x₂ lam rho tau : G} {T₂ : Subgroup G}
variable (D : FzRNum t x₁ x₂ lam rho tau T₂)

@[expose] def fzrMu (n : ℕ) : G := D.mu n

@[expose] def fzrPar : Par := D.par

@[expose] def fzrTh (n : ℕ) : Prop := n < 512 ∧ ∃ g : G, g * t * g⁻¹ = fzrMu D n

theorem fzrMu_mem (n : ℕ) : fzrMu D n ∈ T₂ := D.mu_mem n

theorem fzrMu_zero : fzrMu D 0 = 1 := D.mu_zero

theorem fzrMu_mul {n m : ℕ} (hn : n < 512) (hm : m < 512) :
    fzrMu D ((fzrPar D).e n m) = fzrMu D n * fzrMu D m := D.mu_mul n m hn hm

theorem fzrMu_inj {n m : ℕ} (hn : n < 512) (hm : m < 512) (h : fzrMu D n = fzrMu D m) :
    n = m := D.mu_inj n m hn hm h

theorem fzrMu_surj {g : G} (hg : g ∈ T₂) : ∃ n, n < 512 ∧ fzrMu D n = g := D.mu_surj g hg

theorem fzrMu_tI : fzrMu D 64 = t := D.mu_tI

theorem fzrMu_sI : fzrMu D 128 = tau := D.mu_sI

theorem fzrPar_nums : (fzrPar D).tI = 64 ∧ (fzrPar D).sI = 128 := ⟨D.tI_eq, D.sI_eq⟩

theorem fzrPar_mul : FzMul (fzrPar D).e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact D.e_lt x y hx hy
  · intro x y z hx hy hz
    have hxy : (fzrPar D).e x y < 512 := D.e_lt x y hx hy
    have hyz : (fzrPar D).e y z < 512 := D.e_lt y z hy hz
    apply fzrMu_inj D (D.e_lt _ _ hxy hz) (D.e_lt _ _ hx hyz)
    calc fzrMu D ((fzrPar D).e ((fzrPar D).e x y) z)
        = fzrMu D ((fzrPar D).e x y) * fzrMu D z := fzrMu_mul D hxy hz
      _ = (fzrMu D x * fzrMu D y) * fzrMu D z := by rw [fzrMu_mul D hx hy]
      _ = fzrMu D x * (fzrMu D y * fzrMu D z) := mul_assoc _ _ _
      _ = fzrMu D x * fzrMu D ((fzrPar D).e y z) := by rw [fzrMu_mul D hy hz]
      _ = fzrMu D ((fzrPar D).e x ((fzrPar D).e y z)) := (fzrMu_mul D hx hyz).symm
  · intro x hx
    apply fzrMu_inj D (D.e_lt x 0 hx (by decide)) hx
    have h := fzrMu_mul D (n := x) (m := 0) hx (by decide)
    rw [fzrMu_zero, mul_one] at h
    exact h
  · intro x hx
    apply fzrMu_inj D (D.e_lt 0 x (by decide) hx) hx
    have h := fzrMu_mul D (n := 0) (m := x) (by decide) hx
    rw [fzrMu_zero, one_mul] at h
    exact h

theorem fzrPar_lt : (fzrPar D).tI < 512 ∧ (fzrPar D).sI < 512 ∧
    (∀ g ∈ (fzrPar D).gens.toList, g < 512) ∧ (∀ x, x < 256 → (fzrPar D).rhoMap x < 512) := by
  refine ⟨?_, ?_, D.gens_lt, D.rho_lt⟩
  · show D.par.tI < 512
    rw [D.tI_eq]
    decide
  · show D.par.sI < 512
    rw [D.sI_eq]
    decide

theorem fzrMu_rho {x : ℕ} (hx : x < 256) :
    fzrMu D ((fzrPar D).rhoMap x) = rho * fzrMu D x * rho⁻¹ := D.mu_rho x hx

theorem fzrMu_inW {x : ℕ} (h : (fzrPar D).inW x = true) : fzrMu D x ∈ ctxW t x₁ x₂ :=
  D.mu_inW x h

theorem fzrMu_inTL {x : ℕ} (hx : x < 512) (h : (fzrPar D).inTL x = true) :
    fzrMu D x ∈ wreathGrp x₁ x₂ lam := D.mu_inTL x hx h

theorem fzrMu_inTZ {z : G} (hz : z ∈ fourGrp x₁ x₂) {x : ℕ} (hx : x < 512)
    (h : fzrMu D x = t * z) : (fzrPar D).inTZ x = true := D.mu_inTZ z hz x hx h

open Classical in
private noncomputable def fzrAux_pow2 (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 => (fzrPar D).e (fzrAux_pow2 x n) (fzrAux_pow2 x n)

private theorem fzrAux_pow2_lt (x : ℕ) (hx : x < 512) (n : ℕ) :
    fzrAux_pow2 D x n < 512 := by
  induction n with
  | zero => simpa [fzrAux_pow2] using hx
  | succ n ih =>
      simpa [fzrAux_pow2] using
        (fzrPar_mul D).lt (fzrAux_pow2 D x n) (fzrAux_pow2 D x n) ih ih

private theorem fzrAux_pow2_mu (x : ℕ) (hx : x < 512) (n : ℕ) :
    fzrMu D (fzrAux_pow2 D x n) = (fzrMu D x) ^ (2 ^ n) := by
  induction n with
  | zero => simp [fzrAux_pow2]
  | succ n ih =>
      have hlt := fzrAux_pow2_lt D x hx n
      rw [fzrAux_pow2, fzrMu_mul D hlt hlt, ih]
      have h2 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
        rw [pow_succ]
        ring
      rw [← pow_add, h2]

private theorem fzrAux_eq_zero_iff (y : ℕ) (hy : y < 512) :
    y = 0 ↔ fzrMu D y = 1 := by
  constructor
  · rintro rfl
    exact fzrMu_zero D
  · intro h
    apply fzrMu_inj D hy (by decide)
    rw [h, fzrMu_zero]

private theorem fzrAux_pow2_zero (x : ℕ) (hx : x < 512) (n : ℕ) :
    fzrAux_pow2 D x n = 0 ↔ (fzrMu D x) ^ (2 ^ n) = 1 := by
  rw [fzrAux_eq_zero_iff D _ (fzrAux_pow2_lt D x hx n), fzrAux_pow2_mu D x hx n]

theorem fzrMu_kord {x : ℕ} (hx : x < 512) :
    kord (fzrPar D).e x = fzrOrdClass (fzrMu D x) := by
  classical
  have h0 : x = 0 ↔ fzrMu D x = 1 := fzrAux_eq_zero_iff D x hx
  have h1 : (fzrPar D).e x x = 0 ↔ (fzrMu D x) ^ 2 = 1 := by
    simpa [fzrAux_pow2] using fzrAux_pow2_zero D x hx 1
  have h2 : (fzrPar D).e ((fzrPar D).e x x) ((fzrPar D).e x x) = 0 ↔
      (fzrMu D x) ^ 4 = 1 := by
    simpa [fzrAux_pow2] using fzrAux_pow2_zero D x hx 2
  have h3 : (fzrPar D).e ((fzrPar D).e ((fzrPar D).e x x) ((fzrPar D).e x x))
      ((fzrPar D).e ((fzrPar D).e x x) ((fzrPar D).e x x)) = 0 ↔
      (fzrMu D x) ^ 8 = 1 := by
    simpa [fzrAux_pow2] using fzrAux_pow2_zero D x hx 3
  unfold kord fzrOrdClass
  exact if_congr h0 rfl (if_congr h1 rfl (if_congr h2 rfl (if_congr h3 rfl rfl)))

end CFSG.OddStandard.SmallF3.FritzII

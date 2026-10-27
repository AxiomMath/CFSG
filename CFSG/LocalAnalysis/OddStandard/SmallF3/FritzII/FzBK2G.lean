module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK1A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU

structure FzbExact {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P) (c : Bool)
    (q s lam : G) : Prop where
  hq : ∀ x < 64, q * C.dec x * q⁻¹ = C.dec ((modl c ()).aq[x]!)
  hs : ∀ x < 64, s * C.dec x * s⁻¹ = C.dec ((modl c ()).as[x]!)
  hy : ∀ x < 64, lam * C.dec x * lam⁻¹ = C.dec ((modl c ()).ay[x]!)
  aq_lt : ∀ x < 64, (modl c ()).aq[x]! < 64
  as_lt : ∀ x < 64, (modl c ()).as[x]! < 64
  ay_lt : ∀ x < 64, (modl c ()).ay[x]! < 64
  q_pow : q ^ 4 = 1
  s_sq : s ^ 2 = 1
  y_sq : lam ^ 2 = 1
  s_q : s * q * s⁻¹ = q⁻¹
  y_q : lam * q = q * lam
  y_s : lam * s = s * lam

@[expose] def fzbBeta {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P) (q s lam : G)
    (x : ℕ) : G :=
  C.dec (x % 64) * fzbAlpha q s lam (x / 64)

private theorem fzb_conj_mul {G : Type} [Group G] (a b x : G) :
    (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  rw [mul_inv_rev a b]
  simp only [mul_assoc]

private theorem fzb_conj_mul3 {G : Type} [Group G] (a b c x : G) :
    a * b * c * x * (a * b * c)⁻¹ = a * (b * (c * x * c⁻¹) * b⁻¹) * a⁻¹ := by
  rw [mul_assoc a b c, fzb_conj_mul a (b * c) x, fzb_conj_mul b c x]

private theorem fzb_conj_mul_cancel {G : Type} [Group G] (u v a b : G) :
    u * (a * v * a⁻¹) * (a * b) = u * a * (v * b) := by
  calc u * (a * v * a⁻¹) * (a * b)
      = u * ((a * v) * (a⁻¹ * (a * b))) := by simp only [mul_assoc]
    _ = u * a * (v * b) := by
          rw [← mul_assoc a⁻¹ a b, inv_mul_cancel, one_mul]
          simp only [mul_assoc]

private theorem fzb_iter_conj {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P)
    {g : G} {f : Array ℕ}
    (hg : ∀ x < 64, g * C.dec x * g⁻¹ = C.dec (f[x]!))
    (hf : ∀ x < 64, f[x]! < 64) (n u : ℕ) (hu : u < 64) :
    g ^ n * C.dec u * (g ^ n)⁻¹ = C.dec (iterA f n u) ∧ iterA f n u < 64 := by
  revert u
  induction n with
  | zero =>
    intro u hu
    exact ⟨by simp [iterA], hu⟩
  | succ n ih =>
    intro u hu
    obtain ⟨heq, hlt⟩ := ih u hu
    have hstep : iterA f (n + 1) u = f[iterA f n u]! := rfl
    refine ⟨?_, ?_⟩
    · rw [pow_succ', fzb_conj_mul, heq, hg _ hlt, hstep]
    · rw [hstep]
      exact hf _ hlt

section Chart

variable {G : Type} [Group G] {P : Subgroup G} {C : FzbCoding P} {c : Bool} {q s lam : G}

theorem fzb_alpha_act (hE : FzbExact C c q s lam) {w u : ℕ} (hw : w < 16) (hu : u < 64) :
    fzbAlpha q s lam w * C.dec u * (fzbAlpha q s lam w)⁻¹ = C.dec ((modl c ()).act w u) ∧
      (modl c ()).act w u < 64 := by
  obtain ⟨hlam_eq, hlam_lt⟩ :=
    fzb_iter_conj C (g := lam) (f := (modl c ()).ay) hE.hy hE.ay_lt (w / 8) u hu
  obtain ⟨hs_eq, hs_lt⟩ :=
    fzb_iter_conj C (g := s) (f := (modl c ()).as) hE.hs hE.as_lt (w / 4 % 2)
      (iterA (modl c ()).ay (w / 8) u) hlam_lt
  obtain ⟨hq_eq, hq_lt⟩ :=
    fzb_iter_conj C (g := q) (f := (modl c ()).aq) hE.hq hE.aq_lt (w % 4)
      (iterA (modl c ()).as (w / 4 % 2) (iterA (modl c ()).ay (w / 8) u)) hs_lt
  refine ⟨?_, ?_⟩
  · simp only [fzbAlpha, Mod.act]
    rw [fzb_conj_mul3, hlam_eq, hs_eq, hq_eq]
  · simp only [Mod.act]
    exact hq_lt

theorem fzb_beta_mul (hE : FzbExact C c q s lam) {x y : ℕ} (hx : x < 1024) (hy : y < 1024) :
    fzbBeta C q s lam (fzbMul c x y) = fzbBeta C q s lam x * fzbBeta C q s lam y := by
  have hx64 : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hy64 : y % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hxw : x / 64 < 16 := by omega
  have hyw : y / 64 < 16 := by omega
  obtain ⟨hact_eq, hact_lt⟩ := fzb_alpha_act hE hxw hy64
  have hu : uMul (x % 64) ((modl c ()).act (x / 64) (y % 64)) < 64 :=
    fzb_uMul_lt hx64 hact_lt
  have hmod : (uMul (x % 64) ((modl c ()).act (x / 64) (y % 64)) +
      64 * amul (x / 64) (y / 64)) % 64 =
      uMul (x % 64) ((modl c ()).act (x / 64) (y % 64)) := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
  have hdiv : (uMul (x % 64) ((modl c ()).act (x / 64) (y % 64)) +
      64 * amul (x / 64) (y / 64)) / 64 = amul (x / 64) (y / 64) := by
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 64), Nat.div_eq_of_lt hu, Nat.zero_add]
  rw [fzb_mul_eq_mulA]
  unfold Mod.mulA fzbBeta
  rw [hmod, hdiv, C.dec_mul hx64 hact_lt,
    ← fzb_alpha_mul hE.q_pow hE.s_sq hE.y_sq hE.s_q hE.y_q hE.y_s hxw hyw, ← hact_eq]
  exact fzb_conj_mul_cancel _ _ _ _

end Chart

end CFSG.OddStandard.SmallF3.FritzII

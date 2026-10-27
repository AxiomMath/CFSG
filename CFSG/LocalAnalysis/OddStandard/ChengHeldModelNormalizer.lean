module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartStd
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupNormalizer
public import Certificates.Certificate6136
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOutSquare

public section

namespace CFSG.OddStandard.ChengHeld.H3

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

theorem dGL_pow_three : dGL ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; decide)

theorem g₄_pow_three : g₄ ^ 3 = 1 := by
  rw [g₄, ← map_pow, dGL_pow_three, map_one]

theorem g₅_g₄ : g₅ * g₄ * g₅⁻¹ = g₄ ^ 2 := by
  rw [g₄, ← map_pow]
  refine (rho_frob ?_ ?_).symm
  · rw [Units.val_pow_eq_pow_val]
    decide
  · rw [← inv_pow, Units.val_pow_eq_pow_val]
    decide

theorem invTranspose_dGL : invTranspose dGL = dGL ^ 2 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; decide)

theorem g₆_g₄ : g₆ * g₄ * g₆⁻¹ = g₄ ^ 2 := by
  rw [g₄, ← map_pow, ← invTranspose_dGL, rho_invTranspose]

theorem g₅_g₆ : g₅ * g₆ = g₆ * g₅ := by
  refine Equiv.ext fun i => ?_
  show g5Fun (g6Fun i) = g6Fun (g5Fun i)
  revert i
  decide

section Dihedral

variable {Q : Type*} [Group Q]

theorem mul_pow_eq_of_mul_eq {y z : Q} (h : y * z = z ^ 2 * y) (n : ℕ) :
    y * z ^ n = z ^ (2 * n) * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_add,
      show 2 * n + 2 = 2 * (n + 1) by ring]

theorem pow_mul_pow_eq_of_mul_eq {y z : Q} (h : y * z = z ^ 2 * y) (b n : ℕ) :
    y ^ b * z ^ n = z ^ (n * 2 ^ b) * y ^ b := by
  induction b generalizing n with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, mul_assoc, mul_pow_eq_of_mul_eq h, ← mul_assoc, ih, mul_assoc,
      show 2 * n * 2 ^ b = n * 2 ^ (b + 1) by ring]

variable {x u v : Q}

theorem uv_mul_x_pow (hux : u * x = x ^ 2 * u) (hvx : v * x = x ^ 2 * v) (b c n : ℕ) :
    u ^ b * v ^ c * x ^ n = x ^ (n * 2 ^ c * 2 ^ b) * (u ^ b * v ^ c) := by
  rw [mul_assoc, pow_mul_pow_eq_of_mul_eq hvx, ← mul_assoc, pow_mul_pow_eq_of_mul_eq hux,
    mul_assoc]

theorem nf_mul_x (hux : u * x = x ^ 2 * u) (hvx : v * x = x ^ 2 * v) (a b c n : ℕ) :
    x ^ a * u ^ b * v ^ c * x ^ n = x ^ (a + n * 2 ^ c * 2 ^ b) * u ^ b * v ^ c := by
  rw [mul_assoc (x ^ a * u ^ b), mul_assoc (x ^ a), ← mul_assoc (u ^ b),
    uv_mul_x_pow hux hvx, ← mul_assoc, ← pow_add, ← mul_assoc]

theorem nf_mul_u (huv : u * v = v * u) (a b c : ℕ) :
    x ^ a * u ^ b * v ^ c * u = x ^ a * u ^ (b + 1) * v ^ c := by
  have hc : v ^ c * u = u * v ^ c := (Commute.pow_left (show Commute v u from huv.symm) c).eq
  rw [mul_assoc, hc, ← mul_assoc, mul_assoc (x ^ a), ← pow_succ]

theorem nf_mul_v (a b c : ℕ) : x ^ a * u ^ b * v ^ c * v = x ^ a * u ^ b * v ^ (c + 1) := by
  rw [mul_assoc, ← pow_succ]

theorem nf_sq (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (huv : u * v = v * u)
    (hux : u * x = x ^ 2 * u) (hvx : v * x = x ^ 2 * v) (a b c : ℕ) :
    (x ^ a * u ^ b * v ^ c) ^ 2 = x ^ (a + a * 2 ^ c * 2 ^ b) := by
  have hc : v ^ c * u ^ b = u ^ b * v ^ c :=
    (Commute.pow_pow (show Commute v u from huv.symm) c b).eq
  have h1 : u ^ b * v ^ c * (u ^ b * v ^ c) = 1 := by
    rw [mul_assoc, ← mul_assoc (v ^ c), hc, mul_assoc, ← mul_assoc, ← pow_add, ← pow_add,
      ← two_mul, ← two_mul, pow_mul, pow_mul, hu2, hv2, one_pow, one_pow, one_mul]
  calc (x ^ a * u ^ b * v ^ c) ^ 2
      = x ^ a * (u ^ b * v ^ c * x ^ a) * (u ^ b * v ^ c) := by
        rw [pow_two]; simp only [mul_assoc]
    _ = x ^ a * x ^ (a * 2 ^ c * 2 ^ b) * (u ^ b * v ^ c * (u ^ b * v ^ c)) := by
        rw [uv_mul_x_pow hux hvx]; simp only [mul_assoc]
    _ = x ^ (a + a * 2 ^ c * 2 ^ b) := by rw [h1, mul_one, ← pow_add]

theorem nf_eq_pow_of_cube (hx3 : x ^ 3 = 1) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (huv : u * v = v * u) (hux : u * x = x ^ 2 * u) (hvx : v * x = x ^ 2 * v) (a b c : ℕ)
    (h3 : (x ^ a * u ^ b * v ^ c) ^ 3 = 1) :
    ∃ m : ℕ, x ^ a * u ^ b * v ^ c = x ^ m := by
  refine ⟨2 * (a + a * 2 ^ c * 2 ^ b), ?_⟩
  have hy2 := nf_sq hu2 hv2 huv hux hvx a b c
  set y := x ^ a * u ^ b * v ^ c with hy
  set k := a + a * 2 ^ c * 2 ^ b with hk
  have e1 : y = y ^ 3 * (y ^ 2)⁻¹ := by group
  have e2 : x ^ (2 * k) * x ^ k = 1 := by
    rw [← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, hx3, one_pow]
  rw [e1, h3, hy2, one_mul]
  exact (eq_inv_of_mul_eq_one_left e2).symm

end Dihedral

section RmodS

theorem exists_mul_g₄_pow_of_pow_three_mem {r : Equiv.Perm (Fin 42)} (hr : r ∈ R)
    (hr3 : r ^ 3 ∈ S) : ∃ s ∈ S, ∃ k < 3, r = s * g₄ ^ k := by
  have : (S.subgroupOf R).Normal := S_normal
  set π : ↥R →* ↥R ⧸ S.subgroupOf R := QuotientGroup.mk' _ with hπ
  have hS : ∀ (y : Equiv.Perm (Fin 42)) (hy : y ∈ R), y ∈ S → π ⟨y, hy⟩ = 1 := fun y hy hyS =>
    (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hyS)
  set x := π ⟨g₄, g₄_mem_R⟩ with hx
  set u := π ⟨g₅, g₅_mem_R⟩ with hu
  set v := π ⟨g₆, g₆_mem_R⟩ with hv
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨g₄, g₄_mem_R⟩ : ↥R) ^ 3 = 1 := Subtype.ext g₄_pow_three
    rw [this, map_one]
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← map_pow]
    have : (⟨g₅, g₅_mem_R⟩ : ↥R) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact g₅_mul_g₅)
    rw [this, map_one]
  have hv2 : v ^ 2 = 1 := by
    rw [hv, ← map_pow]
    have : (⟨g₆, g₆_mem_R⟩ : ↥R) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact g₆_mul_g₆)
    rw [this, map_one]
  have huv : u * v = v * u := by
    rw [hu, hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext g₅_g₆
  have hux : u * x = x ^ 2 * u := by
    rw [hu, hx, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show g₅ * g₄ = g₄ ^ 2 * g₅
    rw [← g₅_g₄]
    group
  have hvx : v * x = x ^ 2 * v := by
    rw [hv, hx, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show g₆ * g₄ = g₄ ^ 2 * g₆
    rw [← g₆_g₄]
    group
  have hxi : x⁻¹ = x ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])).symm
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hu2])
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hv2])
  have key : ∀ (y : Equiv.Perm (Fin 42)),
      y ∈ closure ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))) →
      ∀ hy : y ∈ R, ∃ a b c : ℕ, π ⟨y, hy⟩ = x ^ a * u ^ b * v ^ c := by
    intro y hy'
    refine Subgroup.closure_induction_right (p := fun y _ => ∀ hy : y ∈ R,
      ∃ a b c : ℕ, π ⟨y, hy⟩ = x ^ a * u ^ b * v ^ c) ?_ ?_ ?_ hy'
    · intro _
      exact ⟨0, 0, 0, by rw [pow_zero, pow_zero, pow_zero, mul_one, mul_one]; exact map_one π⟩
    · intro y hy' g hg ih hyg
      have hyR : y ∈ R := hy'
      have hgR : g ∈ R := subset_closure hg
      obtain ⟨a, b, c, habc⟩ := ih hyR
      have e : π ⟨y * g, hyg⟩ = π ⟨y, hyR⟩ * π ⟨g, hgR⟩ := map_mul π ⟨y, hyR⟩ ⟨g, hgR⟩
      rw [e, habc]
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨a, b, c, by rw [hS _ hgR g₁_mem_S, mul_one]⟩
      · exact ⟨a, b, c, by rw [hS _ hgR g₂_mem_S, mul_one]⟩
      · exact ⟨a, b, c, by rw [hS _ hgR g₃_mem_S, mul_one]⟩
      · refine ⟨a + 1 * 2 ^ c * 2 ^ b, b, c, ?_⟩
        rw [← nf_mul_x hux hvx, pow_one]
      · exact ⟨a, b + 1, c, nf_mul_u huv a b c⟩
      · exact ⟨a, b, c + 1, nf_mul_v a b c⟩
    · intro y hy' g hg ih hyg
      have hyR : y ∈ R := hy'
      have hgR : g ∈ R := subset_closure hg
      obtain ⟨a, b, c, habc⟩ := ih hyR
      have e : π ⟨y * g⁻¹, hyg⟩ = π ⟨y, hyR⟩ * (π ⟨g, hgR⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e, habc]
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨a, b, c, by rw [hS _ hgR g₁_mem_S, inv_one, mul_one]⟩
      · exact ⟨a, b, c, by rw [hS _ hgR g₂_mem_S, inv_one, mul_one]⟩
      · exact ⟨a, b, c, by rw [hS _ hgR g₃_mem_S, inv_one, mul_one]⟩
      · refine ⟨a + 2 * 2 ^ c * 2 ^ b, b, c, ?_⟩
        rw [← nf_mul_x hux hvx]
        exact congrArg _ hxi
      · exact ⟨a, b + 1, c, by rw [← nf_mul_u huv a b c]; exact congrArg _ hui⟩
      · exact ⟨a, b, c + 1, by rw [← nf_mul_v a b c]; exact congrArg _ hvi⟩
  obtain ⟨a, b, c, habc⟩ := key r hr hr
  have h3 : (x ^ a * u ^ b * v ^ c) ^ 3 = 1 := by
    rw [← habc, ← map_pow]
    exact hS _ (pow_mem hr 3) hr3
  obtain ⟨m, hm⟩ := nf_eq_pow_of_cube hx3 hu2 hv2 huv hux hvx a b c h3
  have hq : π (⟨r, hr⟩ * ((⟨g₄, g₄_mem_R⟩ : ↥R) ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, habc, hm, ← hx, mul_inv_cancel]
  have hs : r * (g₄ ^ m)⁻¹ ∈ S := by
    have h1 := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)
    simpa using h1
  have hm3 : g₄ ^ (m % 3) = g₄ ^ m := (pow_eq_pow_mod m g₄_pow_three).symm
  exact ⟨r * (g₄ ^ m)⁻¹, hs, m % 3, Nat.mod_lt _ (by norm_num), by rw [hm3]; group⟩

end RmodS

section Multiplier

noncomputable def zt (y : ZMod 4 × ZMod 4) (c : ZMod 3) : Cover :=
  zHom (Multiplicative.ofAdd y.1, Multiplicative.ofAdd y.2, Multiplicative.ofAdd c)

theorem zt_mul (y y' : ZMod 4 × ZMod 4) (c c' : ZMod 3) :
    zt y c * zt y' c' = zt (y + y') (c + c') := by
  rw [zt, zt, zt, ← map_mul]
  rfl

theorem zt_pow (y : ZMod 4 × ZMod 4) (c : ZMod 3) (n : ℕ) :
    zt y c ^ n = zt (n • y) (n • c) := by
  rw [zt, zt, ← map_pow]
  rfl

theorem zt_injective {y y' : ZMod 4 × ZMod 4} {c c' : ZMod 3} (h : zt y c = zt y' c') :
    y = y' ∧ c = c' := by
  have h1 := zHom_injective h
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h1
  exact ⟨Prod.ext h1.1 h1.2.1, h1.2.2⟩

theorem zt_eq_pow (y : ZMod 4 × ZMod 4) (c : ZMod 3) :
    zt y c = zt (1, 0) 0 ^ y.1.val * zt (0, 1) 0 ^ y.2.val * zt 0 1 ^ c.val := by
  rw [zt_pow, zt_pow, zt_pow, zt_mul, zt_mul]
  congr 1
  · refine Prod.ext ?_ ?_ <;> simp
  · simp

theorem z₁_eq : z₁ = zt (1, 0) 0 := by
  simp [zt, zHom_apply, show (1 : ZMod 4).val = 1 from rfl]

theorem z₂_eq : z₂ = zt (0, 1) 0 := by
  simp [zt, zHom_apply, show (1 : ZMod 4).val = 1 from rfl]

theorem z₃_eq : z₃ = zt 0 1 := by
  simp [zt, zHom_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem cv_zOf (e : ℕ × ℕ × ℕ × ℕ) :
    cv (zOf e) = zt ((e.2.1 : ZMod 4), (e.2.2.1 : ZMod 4)) (e.2.2.2 : ZMod 3) := by
  rw [zOf, cv_zword, zt, zHom_apply]
  simp only [toAdd_ofAdd, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ z₁_pow, ← pow_eq_pow_mod _ z₂_pow, ← pow_eq_pow_mod _ z₃_pow,
    mul_assoc]

end Multiplier

theorem cube_eq_one_m4 : ∀ b : Multiplicative (ZMod 4), b ^ 3 = 1 → b = 1 := by decide

theorem repPerm_four : repPerm 4 = g₄ := by simp [repPerm, rPerm, realRepWords, genR]

theorem repPerm_five : repPerm 5 = g₄ ^ 2 := by
  simp [repPerm, rPerm, realRepWords, genR, pow_two]

theorem lift_unique
    {ρ : Equiv.Perm (Fin 42)} {α α' : Cover →* Cover}
    (h : ∀ c, sigma (α c) = ρ * sigma c * ρ⁻¹) (h' : ∀ c, sigma (α' c) = ρ * sigma c * ρ⁻¹) :
    α = α' :=
  hom_ext_of_central commutator_cover sigma ker_sigma_le_center
    (MonoidHom.ext fun c => by simp only [MonoidHom.comp_apply]; rw [h, h'])

section Lifts

theorem alpha_zt {i : ℕ} (hi : i < 36) {α : Cover →* Cover}
    (hα : ∀ w, α (cv w) = cv (substWord (aut i) w))
    (hσα : ∀ c, sigma (α c) = repPerm i * sigma c * (repPerm i)⁻¹) (y : ZMod 4 × ZMod 4)
    (c : ZMod 3) : ∃ c' : ZMod 3, α (zt y c) = zt (mact i y) c' := by
  have h1 : α (zt (1, 0) 0) = zt (((alphaEntry i 64).2.1 : ZMod 4),
      ((alphaEntry i 64).2.2.1 : ZMod 4)) ((alphaEntry i 64).2.2.2 : ZMod 3) := by
    rw [← z₁_eq, show z₁ = cv (zGen 0) from rfl, hα, alphaZ_spec hi (j := 0) (by norm_num),
      cv_zOf]
  have h2 : α (zt (0, 1) 0) = zt (((alphaEntry i 65).2.1 : ZMod 4),
      ((alphaEntry i 65).2.2.1 : ZMod 4)) ((alphaEntry i 65).2.2.2 : ZMod 3) := by
    rw [← z₂_eq, show z₂ = cv (zGen 1) from rfl, hα, alphaZ_spec hi (j := 1) (by norm_num),
      cv_zOf]
  obtain ⟨d, hd⟩ : ∃ d : ZMod 3, α (zt 0 1) = zt 0 d := by
    have hk : α (zt 0 1) ∈ sigma.ker := by
      rw [MonoidHom.mem_ker, hσα, ← z₃_eq, sigma_z₃, mul_one, mul_inv_cancel]
    rw [← range_zHom] at hk
    obtain ⟨⟨t₁, t₂, t₃⟩, ht⟩ := hk
    have ht3 : zHom ((t₁, t₂, t₃) ^ 3) = zHom 1 := by
      rw [map_pow, ht, map_one, ← map_pow, ← z₃_eq, z₃_pow, map_one]
    have h3 := zHom_injective ht3
    simp only [Prod.pow_mk, Prod.mk_eq_one] at h3
    obtain rfl := cube_eq_one_m4 t₁ h3.1
    obtain rfl := cube_eq_one_m4 t₂ h3.2.1
    exact ⟨Multiplicative.toAdd t₃, by rw [← ht]; rfl⟩
  refine ⟨y.1.val • ((alphaEntry i 64).2.2.2 : ZMod 3) +
    y.2.val • ((alphaEntry i 65).2.2.2 : ZMod 3) + c.val • d, ?_⟩
  rw [zt_eq_pow y c, map_mul, map_mul, map_pow, map_pow, map_pow, h1, h2, hd, zt_pow, zt_pow,
    zt_pow, zt_mul, zt_mul]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp [mact, nsmul_eq_mul]

theorem mact_zero (y : ZMod 4 × ZMod 4) : mact 0 y = y := by
  obtain ⟨α, hα, hσα⟩ := exists_alpha (i := 0) (by norm_num)
  have hid : α = MonoidHom.id Cover := lift_unique (ρ := 1) (fun c => by rw [hσα]; rfl)
    (fun c => by simp)
  obtain ⟨c', hc'⟩ := alpha_zt (by norm_num) hα hσα y 0
  rw [hid, MonoidHom.id_apply] at hc'
  exact (zt_injective hc').1.symm

theorem mact_five (y : ZMod 4 × ZMod 4) : mact 5 y = mact 4 (mact 4 y) := by
  obtain ⟨α₄, hα₄, hσα₄⟩ := exists_alpha (i := 4) (by norm_num)
  obtain ⟨α₅, hα₅, hσα₅⟩ := exists_alpha (i := 5) (by norm_num)
  have h54 : α₅ = α₄.comp α₄ := lift_unique hσα₅ (fun c => by
    rw [MonoidHom.comp_apply, hσα₄, hσα₄, repPerm_five, repPerm_four, pow_two]
    group)
  obtain ⟨c₅, hc₅⟩ := alpha_zt (by norm_num) hα₅ hσα₅ y 0
  obtain ⟨c₁, hc₁⟩ := alpha_zt (by norm_num) hα₄ hσα₄ y 0
  obtain ⟨c₂, hc₂⟩ := alpha_zt (by norm_num) hα₄ hσα₄ (mact 4 y) c₁
  rw [h54, MonoidHom.comp_apply, hc₁, hc₂] at hc₅
  exact (zt_injective hc₅).1.symm

theorem mact_four_cube (y : ZMod 4 × ZMod 4) : mact 4 (mact 4 (mact 4 y)) = y := by
  obtain ⟨α₄, hα₄, hσα₄⟩ := exists_alpha (i := 4) (by norm_num)
  have h3 : α₄.comp (α₄.comp α₄) = MonoidHom.id Cover := lift_unique (ρ := 1) (fun c => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hσα₄, hσα₄, hσα₄, repPerm_four]
    have h3 : g₄ * g₄ * g₄ = 1 := by rw [← pow_three', g₄_pow_three]
    calc g₄ * (g₄ * (g₄ * sigma c * g₄⁻¹) * g₄⁻¹) * g₄⁻¹
        = g₄ * g₄ * g₄ * sigma c * (g₄ * g₄ * g₄)⁻¹ := by group
      _ = 1 * sigma c * 1⁻¹ := by rw [h3]) (fun c => by simp)
  obtain ⟨c₁, hc₁⟩ := alpha_zt (by norm_num) hα₄ hσα₄ y 0
  obtain ⟨c₂, hc₂⟩ := alpha_zt (by norm_num) hα₄ hσα₄ (mact 4 y) c₁
  obtain ⟨c₃, hc₃⟩ := alpha_zt (by norm_num) hα₄ hσα₄ (mact 4 (mact 4 y)) c₂
  have := congrArg (fun f => f (zt y 0)) h3
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at this
  rw [hc₁, hc₂, hc₃] at this
  exact (zt_injective this).1

end Lifts

@[expose] def h3OK : Bool :=
  [4, 5].all fun i => kGensC.all (fun κ => !liftsK κ i) && kap2Gens.all fun ab => !lifts2 ab i

@[expose] def matA (p₁ q₁ p₂ q₂ : ZMod 4) (x : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (x.1 * p₁ + x.2 * p₂, x.1 * q₁ + x.2 * q₂)

@[expose] def noInvK (M : ZMod 4 × ZMod 4 → ZMod 4 × ZMod 4) : Bool :=
  (kGensC.all fun κ => !(([0, 1, 2, 3] : List (ZMod 4)).all fun m =>
      decide (inKC κ (M (m * κ.1, m * κ.2)).1 (M (m * κ.1, m * κ.2)).2))) &&
    kap2Gens.all fun ab => !(allPairs.all fun x => !inN2 ab x || inN2 ab (M x))

theorem h3OK_eq : h3OK = (noInvK (mact 4) && (noInvK (mact 5) && true)) := rfl

theorem mact_eq_matA (i : ℕ) :
    mact i = matA ((alphaEntry i 64).2.1 : ZMod 4) ((alphaEntry i 64).2.2.1 : ZMod 4)
      ((alphaEntry i 65).2.1 : ZMod 4) ((alphaEntry i 65).2.2.1 : ZMod 4) := rfl

theorem noInvK_matA : ∀ p₁ q₁ p₂ q₂ : ZMod 4,
    matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (1, 0))) = (1, 0) →
    matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (0, 1))) = (0, 1) →
    (matA p₁ q₁ p₂ q₂ (1, 0), matA p₁ q₁ p₂ q₂ (0, 1)) ≠ ((1, 0), (0, 1)) →
    noInvK (matA p₁ q₁ p₂ q₂) = true ∧
      noInvK (fun x => matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ x)) = true := by
  decide

@[expose] def twistGen (M₀ M₄ M₅ : ZMod 4 × ZMod 4 → ZMod 4 × ZMod 4) : Bool :=
  kGensC.all fun κ => [M₀, M₄, M₅].any fun M => kapStd.any fun κs =>
    allPairs.all fun x => decide (inKC κ (M x).1 (M x).2 ↔ inKC κs x.1 x.2)

theorem twistOK_eq : twistOK = twistGen (mact 0) (mact 4) (mact 5) := rfl

theorem noInvK_of_twist (p₁ q₁ p₂ q₂ : ZMod 4)
    (ht : twistGen id (matA p₁ q₁ p₂ q₂) (fun x => matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ x)) =
      true)
    (h1 : matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (1, 0))) = (1, 0))
    (h2 : matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ (0, 1))) = (0, 1)) :
    noInvK (matA p₁ q₁ p₂ q₂) = true ∧
      noInvK (fun x => matA p₁ q₁ p₂ q₂ (matA p₁ q₁ p₂ q₂ x)) = true := by
  refine noInvK_matA p₁ q₁ p₂ q₂ h1 h2 fun h => ?_
  simp only [matA, Prod.mk.injEq, one_mul, zero_mul, add_zero, zero_add] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
  revert ht
  decide

theorem h3OK_true :
    h3OK = true := by
  have hM := mact_eq_matA 4
  have h0 : mact 0 = id := funext mact_zero
  have h5 : mact 5 = fun x => mact 4 (mact 4 x) := funext mact_five
  have hc1 := mact_four_cube (1, 0)
  have hc2 := mact_four_cube (0, 1)
  have ht := (M1b.chCoverParts Certificates.certificate6136).twist
  rw [twistOK_eq, h0, h5, hM] at ht
  rw [hM] at hc1 hc2
  obtain ⟨h₄, h₅⟩ := noInvK_of_twist _ _ _ _ ht hc1 hc2
  rw [h3OK_eq, h5, hM, h₄, h₅]
  rfl

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem false_of_diag (h : Hyp G A) (hF : h3OK = true) (d : Datum A) (P : M1b.Pos d) {i : ℕ}
    (hi : i = 4 ∨ i = 5) {β : Jhat A ≃* Jhat A}
    (hβ : ∀ e, P.q (β e) = repPerm i * P.q e * (repPerm i)⁻¹) : False := by
  have hi36 : i < 36 := by rcases hi with rfl | rfl <;> norm_num
  have hβl : ∀ w, β (P.l (cv w)) = P.l (cv (substWord (aut i) w)) :=
    beta_cv_of P.isQ.ker.le P.isQ.ql hβ (abPerm_uA hi36) (abPerm_uB hi36)
  have hinv : ∀ a b : ZMod 4, zz P.l a b = 1 →
      zz P.l (mact i (a, b)).1 (mact i (a, b)).2 = 1 := by
    intro a b hab
    have h1 := beta_zz P.isQ hi36 hβl a b
    rw [hab, map_one] at h1
    exact h1.symm
  have hF' : kGensC.all (fun κ => !liftsK κ i) = true ∧
      kap2Gens.all (fun ab => !lifts2 ab i) = true := by
    simp only [h3OK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hF
    rcases hi with rfl | rfl
    · exact hF.1
    · exact hF.2
  obtain ⟨hk, hkc⟩ := M1b.ker_card d P h
  obtain ⟨hc24, hcyc⟩ := d.center_two_part h
  rcases hc24 with h2 | h4
  · obtain ⟨ab, hab, hN⟩ := M1b.exists_kappa2 P.isQ (hk.trans h2)
    have hl : lifts2 ab i = true := by
      unfold lifts2
      rw [List.all_eq_true]
      intro x _
      by_cases hx : inN2 ab x = true
      · have h1 : inN2 ab (mact i x) = true :=
          (hN _ _).1 (hinv x.1 x.2 ((hN x.1 x.2).2 hx))
        rw [h1, Bool.or_true]
      · rw [Bool.not_eq_true] at hx
        rw [hx, Bool.not_false, Bool.true_or]
    have h1 := List.all_eq_true.1 hF'.2 ab hab
    rw [hl] at h1
    exact absurd h1 (by decide)
  · obtain ⟨κ, hκ, hN⟩ := exists_kappa P.isQ (hkc hcyc) (hk.trans h4)
    have hl : liftsK κ i = true := by
      unfold liftsK
      rw [List.all_eq_true]
      intro m _
      have h1 := hinv _ _ ((hN (m * κ.1) (m * κ.2)).2 ⟨m, rfl, rfl⟩)
      simp only [decide_eq_true_eq]
      exact (hN _ _).1 h1
    have h1 := List.all_eq_true.1 hF'.1 κ hκ
    rw [hl] at h1
    exact absurd h1 (by decide)

end Main

end CFSG.OddStandard.ChengHeld.H3

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.H3
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Hyp.hpow_of_finite_facts (h : Hyp G A) (hF : h3OK = true) :
    ∀ n ∈ normalizer (A : Set G), n ^ 3 ∈ A ⊔ centralizer (A : Set G) →
      n ∈ A ⊔ centralizer (A : Set G) := by
  intro n hn hn3
  obtain ⟨d⟩ := h.exists_datum
  obtain ⟨P⟩ := M1b.exists_pos h d
  have hQ := P.isQ
  have hA : ⁅A, A⁆ = A :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr h.commutator_eq_top)
  have hperf : Group.IsPerfect ↥A := Group.isPerfect_def.mpr h.commutator_eq_top
  obtain ⟨r, hrR, hr⟩ := M1b.exists_real hQ.qS hQ.qsurj hQ.ker hn
  have hr3 : r ^ 3 ∈ S := by
    have hmem : n ^ 3 ∈ withKernel A := by
      unfold withKernel
      rwa [CFSG.OddStandard.coreActionKernel_eq_centralizer hperf h.pPrimeCore_le_center]
    obtain ⟨e₀, he₀⟩ := exists_inner hmem (pow_mem hn 3)
    have h3 := betaHat_pow hn hr 3
    have hc : P.q e₀ * r ^ 3 ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun t ht => ?_,
        R.mul_mem (S_le_R (hQ.qS e₀)) (pow_mem hrR 3)⟩
      obtain ⟨e, rfl⟩ := hQ.qsurj t ht
      have h1 := h3 e
      rw [he₀ e, map_mul, map_mul, map_inv] at h1
      calc P.q e * (P.q e₀ * r ^ 3) = P.q e₀ * ((P.q e₀)⁻¹ * P.q e * P.q e₀) * r ^ 3 := by
            group
        _ = P.q e₀ * (r ^ 3 * P.q e * (r ^ 3)⁻¹) * r ^ 3 := by rw [h1]
        _ = P.q e₀ * r ^ 3 * P.q e := by group
    rw [centralizer_S_inf_R, mem_bot] at hc
    rw [eq_inv_of_mul_eq_one_right hc]
    exact S.inv_mem (hQ.qS e₀)
  obtain ⟨s, hs, k, hk, rfl⟩ := exists_mul_g₄_pow_of_pow_three_mem hrR hr3
  obtain ⟨e₁, he₁⟩ := hQ.qsurj s hs
  obtain ⟨⟨a, ha⟩, rfl⟩ := jq_surjective A e₁
  have haN : a ∈ normalizer (A : Set G) := le_normalizer ha
  have hxN : n * a ∈ normalizer (A : Set G) := mul_mem hn haN
  have hx : ∀ e, P.q (betaHat A hxN e) = g₄ ^ k * P.q e * (g₄ ^ k)⁻¹ := by
    intro e
    rw [betaHat_mul A hn haN, betaHat_of_mem ha haN, map_mul, map_mul, map_inv, hr, he₁]
    group
  interval_cases k
  ·
    have hid : (betaHat A hxN).toMonoidHom = MonoidHom.id (Jhat A) :=
      hom_ext_of_central (commutator_jhat hA) P.q hQ.ker.le
        (MonoidHom.ext fun e => by simpa using hx e)
    have hxC := M1b.mem_centralizer_of_betaHat_eq h hxN fun e => DFunLike.congr_fun hid e
    rw [show n = n * a * a⁻¹ by group]
    exact mul_mem (mem_sup_right hxC) (mem_sup_left (inv_mem ha))
  · exact (false_of_diag h hF d P (Or.inl rfl) (β := betaHat A hxN)
      fun e => by rw [hx, repPerm_four, pow_one]).elim
  · exact (false_of_diag h hF d P (Or.inr rfl) (β := betaHat A hxN)
      fun e => by rw [hx, repPerm_five]).elim

theorem Hyp.not_three_dvd_of_finite_facts (h : Hyp G A) (hF : h3OK = true) :
    ¬ 3 ∣ (A ⊔ centralizer (A : Set G)).relIndex (normalizer (A : Set G)) :=
  not_three_dvd_relIndex_of_forall_pow_three h (h.hpow_of_finite_facts hF)

theorem Datum.normalizer_eq_of_finite_facts (d : Datum A) (h : Hyp G A) (hF : h3OK = true) :
    normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ d.X :=
  d.normalizer_eq h (h.not_three_dvd_of_finite_facts hF)

theorem Datum.normalizer_eq_cert (d : Datum A) (h : Hyp G A) :
    normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ d.X :=
  d.normalizer_eq_of_finite_facts h h3OK_true

end CFSG.OddStandard.ChengHeld

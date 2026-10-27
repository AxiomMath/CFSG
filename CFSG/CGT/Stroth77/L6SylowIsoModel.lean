module

public import CFSG.CGT.Foote81L6.Bridge.TModel
public import CFSG.CGT.Stroth77.L6SylowIsoPres

public section

namespace CFSG.CGT.Stroth77

open CFSG.CGT.Foote81L6.Bridge

namespace L6Model

section Torus

variable {n : ℕ}

@[expose] def tor (v₁ v₂ v₃ : ZMod (2 ^ n)) : PHat n := ⟨⟨v₁, 0⟩, ⟨v₂, 0⟩, ⟨v₃, 0⟩, 0⟩

theorem tor_mul (v₁ v₂ v₃ w₁ w₂ w₃ : ZMod (2 ^ n)) :
    tor v₁ v₂ v₃ * tor w₁ w₂ w₃ = tor (v₁ + w₁) (v₂ + w₂) (v₃ + w₃) := by
  ext <;> simp [tor]

theorem tor_zero : tor (0 : ZMod (2 ^ n)) 0 0 = 1 := rfl

theorem tor_inv (v₁ v₂ v₃ : ZMod (2 ^ n)) : (tor v₁ v₂ v₃)⁻¹ = tor (-v₁) (-v₂) (-v₃) := by
  ext <;> simp [tor]

theorem tor_eq_tor {v₁ v₂ v₃ w₁ w₂ w₃ : ZMod (2 ^ n)} (h₁ : v₁ = w₁) (h₂ : v₂ = w₂)
    (h₃ : v₃ = w₃) : tor v₁ v₂ v₃ = tor w₁ w₂ w₃ := by
  rw [h₁, h₂, h₃]

theorem c_eq_tor : (PHat.c : PHat n) = tor (hf n) (hf n) (hf n) := rfl

@[expose] def torHom : Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n) × ZMod (2 ^ n)) →* PHat n where
  toFun v := tor v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2
  map_one' := rfl
  map_mul' v w := (tor_mul _ _ _ _ _ _).symm

theorem tor_eq_torHom (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    tor v₁ v₂ v₃ = torHom (Multiplicative.ofAdd (v₁, v₂, v₃)) := rfl

theorem tor_zpow (v₁ v₂ v₃ : ZMod (2 ^ n)) (k : ℤ) :
    tor v₁ v₂ v₃ ^ k = tor ((k : ZMod (2 ^ n)) * v₁) ((k : ZMod (2 ^ n)) * v₂)
      ((k : ZMod (2 ^ n)) * v₃) := by
  rw [tor_eq_torHom, ← map_zpow, ← ofAdd_zsmul, tor_eq_torHom]
  simp [zsmul_eq_mul]

theorem tor_pow (v₁ v₂ v₃ : ZMod (2 ^ n)) (k : ℕ) :
    tor v₁ v₂ v₃ ^ k = tor ((k : ZMod (2 ^ n)) * v₁) ((k : ZMod (2 ^ n)) * v₂)
      ((k : ZMod (2 ^ n)) * v₃) := by
  rw [← zpow_natCast, tor_zpow]
  simp

theorem sd_conj_one (s v : ZMod (2 ^ n)) :
    (⟨s, 1⟩ : SD n)⁻¹ * ⟨v, 0⟩ * ⟨s, 1⟩ = ⟨θ n * v, 0⟩ := by
  ext
  · simp only [SD.mul_i, SD.inv_i, SD.inv_j, SD.mul_j, tw_one, tw_zero, add_zero]
    ring
  · simp only [SD.mul_j, SD.inv_j]
    rfl

theorem sd_conj_zero (s v : ZMod (2 ^ n)) :
    (⟨s, 0⟩ : SD n)⁻¹ * ⟨v, 0⟩ * ⟨s, 0⟩ = ⟨v, 0⟩ := by
  ext
  · simp only [SD.mul_i, SD.inv_i, SD.inv_j, SD.mul_j, tw_zero, add_zero]
    ring
  · simp only [SD.mul_j, SD.inv_j]
    rfl

theorem blk_conj_tor (x₁ x₂ x₃ : SD n) (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    (⟨x₁, x₂, x₃, 0⟩ : PHat n)⁻¹ * tor v₁ v₂ v₃ * ⟨x₁, x₂, x₃, 0⟩ =
      ⟨x₁⁻¹ * ⟨v₁, 0⟩ * x₁, x₂⁻¹ * ⟨v₂, 0⟩ * x₂, x₃⁻¹ * ⟨v₃, 0⟩ * x₃, 0⟩ := by
  ext <;> simp [tor]

end Torus

section Elements

variable (n : ℕ)

@[expose] def yc : PHat n := tor 2 2 2
@[expose] def ya : PHat n := tor (-1) 0 (-1)
@[expose] def yb : PHat n := tor 0 (-1) (-1)
@[expose] def yuv : PHat n := ⟨⟨0, 1⟩, ⟨0, 1⟩, 1, 0⟩
@[expose] def yt : PHat n := ⟨⟨0, 1⟩, 1, ⟨qr n, 1⟩, 0⟩
@[expose] def yu : PHat n := ⟨1, 1, 1, 1⟩
@[expose] def yf : PHat n := ⟨⟨qr n + 1, 1⟩, ⟨qr n + 1, 1⟩, ⟨1, 1⟩, 0⟩

variable {n}

theorem yuv_conj_tor (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    (yuv n)⁻¹ * tor v₁ v₂ v₃ * yuv n = tor (θ n * v₁) (θ n * v₂) v₃ := by
  rw [yuv, blk_conj_tor, sd_conj_one, sd_conj_one]
  have h1 : (1 : SD n) = ⟨0, 0⟩ := rfl
  rw [h1, sd_conj_zero]
  rfl

theorem yt_conj_tor (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    (yt n)⁻¹ * tor v₁ v₂ v₃ * yt n = tor (θ n * v₁) v₂ (θ n * v₃) := by
  rw [yt, blk_conj_tor, sd_conj_one, sd_conj_one]
  have h1 : (1 : SD n) = ⟨0, 0⟩ := rfl
  rw [h1, sd_conj_zero]
  rfl

theorem yu_conj_tor (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    (yu n)⁻¹ * tor v₁ v₂ v₃ * yu n = tor v₂ v₁ v₃ := by
  ext <;> simp [yu, tor] <;> decide

theorem yf_conj_tor (v₁ v₂ v₃ : ZMod (2 ^ n)) :
    (yf n)⁻¹ * tor v₁ v₂ v₃ * yf n = tor (θ n * v₁) (θ n * v₂) (θ n * v₃) := by
  rw [yf, blk_conj_tor, sd_conj_one, sd_conj_one, sd_conj_one]
  rfl

theorem par_two {n : ℕ} (hn : 1 ≤ n) : par (2 : ZMod (2 ^ n)) = 0 := by
  have h := par_two_mul hn (1 : ZMod (2 ^ n))
  rwa [mul_one] at h

theorem yc_mem (hn : 1 ≤ n) : yc n ∈ P n := by
  rw [mem_P]
  simp [yc, tor, PHat.det, SD.det, par_two hn]

theorem ya_mem (hn : 1 ≤ n) : ya n ∈ P n := by
  rw [mem_P]
  simp only [ya, tor, PHat.det, SD.det, par_neg, par_one hn, par_zero, add_zero]
  rfl

theorem yb_mem (hn : 1 ≤ n) : yb n ∈ P n := by
  rw [mem_P]
  simp only [yb, tor, PHat.det, SD.det, par_neg, par_one hn, par_zero, add_zero, zero_add]
  rfl

theorem yuv_mem : yuv n ∈ P n := by
  rw [mem_P]
  simp only [yuv, PHat.det, SD.det, par_zero, zero_add, SD.one_i, SD.one_j, add_zero]
  rfl

theorem yt_mem (hn : 3 ≤ n) : yt n ∈ P n := by
  rw [mem_P]
  simp only [yt, PHat.det, SD.det, par_zero, zero_add, SD.one_i, SD.one_j, add_zero, par_qr hn]
  rfl

theorem yu_mem : yu n ∈ P n := by
  rw [mem_P]
  simp [yu, PHat.det]

theorem yf_mem (hn : 3 ≤ n) : yf n ∈ P n := by
  rw [mem_P]
  simp only [yf, PHat.det, SD.det, par_add, par_qr hn, par_one (show 1 ≤ n by omega), zero_add]
  rfl

end Elements

section Relations

variable (m : ℕ)

theorem four_mul_two_pow : (4 : ZMod (2 ^ (m + 2))) * 2 ^ m = 0 := by
  have h : (4 : ZMod (2 ^ (m + 2))) * 2 ^ m = ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2))) := by
    push_cast
    ring
  rw [h, ZMod.natCast_self]

theorem two_mul_two_pow_sq (hm : 1 ≤ m) : (2 : ZMod (2 ^ (m + 2))) * (2 ^ m) ^ 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : (2 : ZMod (2 ^ (k + 1 + 2))) * (2 ^ (k + 1)) ^ 2 =
      ((2 ^ (k + 1 + 2) : ℕ) : ZMod (2 ^ (k + 1 + 2))) * 2 ^ k := by
    push_cast
    ring
  rw [h, ZMod.natCast_self, zero_mul]

theorem hf_eq_two_mul : hf (m + 2) = 2 * (2 : ZMod (2 ^ (m + 2))) ^ m := by
  simp [hf]

theorem θ_eq : θ (m + 2) = 2 * (2 : ZMod (2 ^ (m + 2))) ^ m - 1 := by
  rw [θ, hf_eq_two_mul]

theorem qr_eq_two_pow : qr (m + 2) = (2 : ZMod (2 ^ (m + 2))) ^ m := by
  simp [qr]

set_option hygiene false in
local macro "zring" : tactic =>
  `(tactic| first
    | rfl
    | decide
    | ring1
    | linear_combination hP
    | linear_combination -hP
    | linear_combination 2 * hP
    | linear_combination hP2
    | linear_combination -hP2
    | linear_combination -hP + hP2
    | linear_combination ((2 : ZMod (2 ^ (m + 2))) ^ m + 1) * hP)

theorem rel_modC (hm : 1 ≤ m) : ∀ q ∈ eqns201 m (yc (m + 2)) (ya (m + 2)) (yb (m + 2))
    (yuv (m + 2)) (yt (m + 2)) (yu (m + 2)) (yf (m + 2)), q.1 = q.2 ∨ q.1 = q.2 * PHat.c := by
  have hP := four_mul_two_pow m
  have hP2 := two_mul_two_pow_sq m hm
  have hθ := θ_eq m
  have hq := qr_eq_two_pow m
  have hh := hf_eq_two_mul m
  intro q hq'
  simp only [eqns201, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right
    rw [yc, tor_pow, one_mul, c_eq_tor, hh]
    apply tor_eq_tor <;> push_cast <;> ring
  · left
    rw [ya, tor_pow, ← tor_zero]
    apply tor_eq_tor <;> simp
  · left
    rw [yb, tor_pow, ← tor_zero]
    apply tor_eq_tor <;> simp
  · left
    rw [yc, ya, tor_mul, tor_mul]
    apply tor_eq_tor <;> ring
  · left
    rw [yc, yb, tor_mul, tor_mul]
    apply tor_eq_tor <;> ring
  · left
    rw [ya, yb, tor_mul, tor_mul]
    apply tor_eq_tor <;> ring
  · left
    rw [yc, yuv_conj_tor, ya, yb, tor_zpow, tor_zpow, tor_zpow, tor_mul, tor_mul, hθ]
    apply tor_eq_tor <;> push_cast <;> zring
  · right
    rw [ya, yuv_conj_tor, yc, yb, tor_pow, tor_mul, tor_mul, c_eq_tor, tor_mul, hθ, hh]
    apply tor_eq_tor <;> push_cast <;> zring
  · right
    rw [yb, yuv_conj_tor, yc, ya, tor_pow, tor_mul, tor_mul, c_eq_tor, tor_mul, hθ, hh]
    apply tor_eq_tor <;> push_cast <;> zring
  · left
    rw [yc, yt_conj_tor, ya, tor_pow, tor_mul, hθ]
    apply tor_eq_tor <;> push_cast <;> zring
  · left
    rw [ya, yt_conj_tor, tor_zpow, hθ]
    apply tor_eq_tor <;> push_cast <;> zring
  · right
    rw [yb, yt_conj_tor, yc, ya, tor_zpow, tor_zpow, tor_zpow, tor_mul, tor_mul, c_eq_tor,
      tor_mul, hθ, hh]
    apply tor_eq_tor <;> push_cast <;> zring
  · left
    rw [yc, yu_conj_tor]
  · left
    rw [ya, yu_conj_tor, yb]
  · left
    rw [yb, yu_conj_tor, ya]
  · left
    rw [yc, yf_conj_tor, tor_inv, hθ]
    apply tor_eq_tor <;> zring
  · left
    rw [ya, yf_conj_tor, tor_inv, tor_pow, tor_mul, hθ]
    apply tor_eq_tor <;> push_cast <;> zring
  · left
    rw [yb, yf_conj_tor, tor_inv, tor_pow, tor_mul, hθ]
    apply tor_eq_tor <;> push_cast <;> zring
  · left
    ext <;> simp [yuv] <;> zring
  · left
    ext <;> simp [yt, hq, tw, hθ] <;> zring
  · left
    ext <;> simp [yu] <;> zring
  · left
    ext <;> simp [yuv, yt] <;> zring
  · left
    ext <;> simp [yuv, yu] <;> zring
  · left
    ext <;> simp [yuv, yt, yu] <;> zring
  · right
    ext <;> simp [yf, PHat.c, SD.z, hq, hh, tw, hθ] <;> zring
  · left
    rw [yc, ya, yb, tor_mul, tor_mul, tor_pow]
    ext <;> simp [yf, yuv, tor, hq, tw, hθ, PHat.one_add_one_zmod_two] <;> zring
  · left
    rw [ya, tor_inv, tor_pow]
    ext <;> simp [yf, yt, tor, hq, tw, hθ, PHat.one_add_one_zmod_two] <;> zring
  · left
    ext <;> simp [yf, yu] <;> zring

end Relations

section SModel

abbrev πS (n : ℕ) : P n →* SModel n := QuotientGroup.mk' (Subgroup.zpowers (cP n))

@[expose] def pc (m : ℕ) : P (m + 2) := ⟨yc (m + 2), yc_mem (by omega)⟩
@[expose] def pa (m : ℕ) : P (m + 2) := ⟨ya (m + 2), ya_mem (by omega)⟩
@[expose] def pb (m : ℕ) : P (m + 2) := ⟨yb (m + 2), yb_mem (by omega)⟩
@[expose] def puv (m : ℕ) : P (m + 2) := ⟨yuv (m + 2), yuv_mem⟩
@[expose] def pu (m : ℕ) : P (m + 2) := ⟨yu (m + 2), yu_mem⟩
@[expose] def pt {m : ℕ} (hm : 1 ≤ m) : P (m + 2) := ⟨yt (m + 2), yt_mem (by omega)⟩
@[expose] def pf {m : ℕ} (hm : 1 ≤ m) : P (m + 2) := ⟨yf (m + 2), yf_mem (by omega)⟩

variable {m : ℕ} (hm : 1 ≤ m)

theorem rel_sModel : Rel201 m (πS _ (pc m)) (πS _ (pa m)) (πS _ (pb m))
    (πS _ (puv m)) (πS _ (pt hm)) (πS _ (pu m)) (πS _ (pf hm)) := by
  intro q hq
  rw [← eqns201_map, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hr' : ((r.1 : PHat (m + 2)), (r.2 : PHat (m + 2))) ∈ eqns201 m (yc (m + 2)) (ya (m + 2))
      (yb (m + 2)) (yuv (m + 2)) (yt (m + 2)) (yu (m + 2)) (yf (m + 2)) := by
    have h := eqns201_map (P (m + 2)).subtype m (pc m) (pa m) (pb m) (puv m) (pt hm) (pu m) (pf hm)
    rw [← show eqns201 m ((P (m + 2)).subtype (pc m)) ((P (m + 2)).subtype (pa m))
        ((P (m + 2)).subtype (pb m)) ((P (m + 2)).subtype (puv m)) ((P (m + 2)).subtype (pt hm))
        ((P (m + 2)).subtype (pu m)) ((P (m + 2)).subtype (pf hm)) =
        eqns201 m (yc (m + 2)) (ya (m + 2)) (yb (m + 2)) (yuv (m + 2)) (yt (m + 2)) (yu (m + 2))
          (yf (m + 2)) from rfl, ← h, List.mem_map]
    exact ⟨r, hr, rfl⟩
  change (QuotientGroup.mk r.1 : SModel (m + 2)) = QuotientGroup.mk r.2
  rcases rel_modC m hm _ hr' with h | h
  · exact congrArg _ (Subtype.ext h)
  · dsimp only at h
    rw [SModel.mk_eq_mk_iff]
    right
    apply Subtype.ext
    change (r.2 : PHat (m + 2)) = (r.1 : PHat (m + 2)) * PHat.c
    rw [h, mul_assoc, PHat.c_mul_c, mul_one]

end SModel

section Pattern

variable {n : ℕ}

@[expose] def sdPat : SD n →* SD 0 where
  toFun x := ⟨0, x.j⟩
  map_one' := rfl
  map_mul' x y := by
    ext
    · exact zmod_two_pow_zero_eq _ _
    · rfl

@[expose] def pat : PHat n →* PHat 0 where
  toFun a := ⟨sdPat a.x₁, sdPat a.x₂, sdPat a.x₃, a.e⟩
  map_one' := rfl
  map_mul' a b := by
    obtain ⟨a₁, a₂, a₃, ae⟩ := a
    rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
      ext <;> simp [sdPat] <;> exact zmod_two_pow_zero_eq _ _

theorem pat_eq_one {y : PHat n} (h : pat y = 1) :
    y.x₁.j = 0 ∧ y.x₂.j = 0 ∧ y.x₃.j = 0 ∧ y.e = 0 := by
  have h1 := congrArg (fun z : PHat 0 => z.x₁.j) h
  have h2 := congrArg (fun z : PHat 0 => z.x₂.j) h
  have h3 := congrArg (fun z : PHat 0 => z.x₃.j) h
  have h4 := congrArg (fun z : PHat 0 => z.e) h
  exact ⟨h1, h2, h3, h4⟩

theorem pattern_words (j₁ j₂ j₃ e : ZMod 2) :
    (⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, 0⟩ : PHat 0) ^ (j₁ + j₃).val *
      (⟨⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, 0⟩ : PHat 0) ^ (j₁ + j₂).val *
      (⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, 0⟩ : PHat 0) ^ (j₁ + j₂ + j₃).val *
      (⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 1⟩ : PHat 0) ^ e.val = ⟨⟨0, j₁⟩, ⟨0, j₂⟩, ⟨0, j₃⟩, e⟩ := by
  fin_cases j₁ <;> fin_cases j₂ <;> fin_cases j₃ <;> fin_cases e <;> rfl

end Pattern

section Generation

variable {m : ℕ} (hm : 1 ≤ m)

theorem exists_two_mul_eq {n : ℕ} {s : ZMod (2 ^ n)} (h : par s = 0) : ∃ r, 2 * r = s := by
  have h2 : 2 ∣ s.val := by
    rw [par] at h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h
  obtain ⟨k, hk⟩ := h2
  refine ⟨(k : ZMod (2 ^ n)), ?_⟩
  rw [← ZMod.natCast_zmod_val s, hk]
  push_cast
  ring

theorem tor_mem_closure (y₁ y₂ y₃ : ZMod (2 ^ (m + 2))) (hy : par y₁ + par y₂ + par y₃ = 0) :
    ∃ i j l : ℕ, yc (m + 2) ^ i * ya (m + 2) ^ j * yb (m + 2) ^ l = tor y₁ y₂ y₃ := by
  have hs : par (y₁ + y₂ - y₃) = 0 := by
    rw [par_sub, par_add, hy]
  obtain ⟨r, hr⟩ := exists_two_mul_eq hs
  refine ⟨r.val, (2 * r - y₁).val, (2 * r - y₂).val, ?_⟩
  rw [yc, ya, yb, tor_pow, tor_pow, tor_pow, tor_mul, tor_mul]
  simp only [ZMod.natCast_zmod_val]
  apply tor_eq_tor <;> first | ring1 | linear_combination -hr

@[expose] def gensS : Set (SModel (m + 2)) :=
  {πS _ (pc m), πS _ (pa m), πS _ (pb m), πS _ (puv m), πS _ (pt hm),
    πS _ (pu m), πS _ (pf hm)}

theorem closure_sModel_eq_top : Subgroup.closure (gensS hm) = ⊤ := by
  set H := Subgroup.closure (gensS hm)
  have hc : πS _ (pc m) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have ha : πS _ (pa m) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have hb : πS _ (pb m) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have huv : πS _ (puv m) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have ht : πS _ (pt hm) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have hu : πS _ (pu m) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have hf : πS _ (pf hm) ∈ H := Subgroup.subset_closure (by simp [gensS])
  have htor : ∀ y : P (m + 2), pat (y : PHat (m + 2)) = 1 → πS _ y ∈ H := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := pat_eq_one hy
    obtain ⟨⟨⟨y₁, j₁⟩, ⟨y₂, j₂⟩, ⟨y₃, j₃⟩, e⟩, hyP⟩ := y
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    have hdet : par y₁ + par y₂ + par y₃ = 0 := by
      have := mem_P.1 hyP
      simpa [PHat.det, SD.det] using this
    obtain ⟨i, j, l, hijl⟩ := tor_mem_closure y₁ y₂ y₃ hdet
    have hy' : (⟨⟨⟨y₁, 0⟩, ⟨y₂, 0⟩, ⟨y₃, 0⟩, 0⟩, hyP⟩ : P (m + 2)) =
        pc m ^ i * pa m ^ j * pb m ^ l :=
      Subtype.ext hijl.symm
    rw [hy', map_mul, map_mul, map_pow, map_pow, map_pow]
    exact H.mul_mem (H.mul_mem (H.pow_mem hc i) (H.pow_mem ha j)) (H.pow_mem hb l)
  rw [eq_top_iff]
  intro z _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers (cP (m + 2))) z
  set p := pat (x : PHat (m + 2))
  let w : P (m + 2) := puv m ^ (p.x₁.j + p.x₃.j).val * pt hm ^ (p.x₁.j + p.x₂.j).val *
    pf hm ^ (p.x₁.j + p.x₂.j + p.x₃.j).val * pu m ^ p.e.val
  have hw : pat (w : PHat (m + 2)) = p := by
    simp only [w, Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow]
    exact pattern_words _ _ _ _
  have hwH : πS _ w ∈ H := by
    simp only [w, map_mul, map_pow]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.pow_mem huv _) (H.pow_mem ht _)) (H.pow_mem hf _))
      (H.pow_mem hu _)
  have hxw : pat ((x * w⁻¹ : P (m + 2)) : PHat (m + 2)) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hw, mul_inv_cancel]
  have h1 := htor _ hxw
  have : x = x * w⁻¹ * w := by group
  change πS _ x ∈ H
  rw [this, map_mul]
  exact H.mul_mem h1 hwH

end Generation

theorem mk_ab_pow {m : ℕ} : πS _ ((pa m * pb m) ^ 2 ^ (m + 1)) = zS (m + 2) := by
  rw [zS]
  change (QuotientGroup.mk _ : SModel (m + 2)) = QuotientGroup.mk (zP (m + 2))
  rw [SModel.mk_eq_mk_iff]
  right
  apply Subtype.ext
  change PHat.zF = (ya (m + 2) * yb (m + 2)) ^ 2 ^ (m + 1) * PHat.c
  have hP := four_mul_two_pow m
  have hh := hf_eq_two_mul m
  rw [ya, yb, tor_mul, tor_pow, c_eq_tor, tor_mul, hh]
  change tor 0 0 (hf (m + 2)) = _
  rw [hh]
  apply tor_eq_tor <;> push_cast <;>
    first | ring1 | linear_combination hP | linear_combination -hP | linear_combination 2 * hP

end L6Model

end CFSG.CGT.Stroth77

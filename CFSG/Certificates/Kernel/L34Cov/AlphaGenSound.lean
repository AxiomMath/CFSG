
module

public import CFSG.Certificates.Kernel.L34Cov.AlphaOKSound
public import Certificates.Data.Kernel.L34Cov.AlphaGen
public import CFSG.Certificates.Kernel.L34W.ModelSound

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real Subgroup

theorem zpow3_eq_zHom (a b c : ℕ) :
    z₁ ^ a * z₂ ^ b * z₃ ^ c = zHom (Multiplicative.ofAdd (a : ZMod 4),
      Multiplicative.ofAdd (b : ZMod 4), Multiplicative.ofAdd (c : ZMod 3)) := by
  rw [zHom_apply, mul_assoc]
  simp only [toAdd_ofAdd, ZMod.val_natCast]
  rw [← pow_eq_pow_mod a z₁_pow, ← pow_eq_pow_mod b z₂_pow, ← pow_eq_pow_mod c z₃_pow]

theorem comp_corr {n : ℕ} (hn : n ∣ 12) {t c x y eA eB : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12]) (heA : eA ≤ 12) (heB : eB ≤ 12)
    (ht : (t : ZMod n) = (c : ZMod n) + ((12 - eA : ℕ) : ZMod n) * x +
      ((12 - eB : ℕ) : ZMod n) * y) :
    Multiplicative.ofAdd (t : ZMod n) * (Multiplicative.ofAdd (x : ZMod n)) ^ E₀ *
      (Multiplicative.ofAdd (y : ZMod n)) ^ E₁ = Multiplicative.ofAdd (c : ZMod n) := by
  rw [← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_add]
  congr 1
  obtain ⟨a, ha⟩ := Int.ModEq.dvd h₀
  obtain ⟨b, hb⟩ := Int.ModEq.dvd h₁
  have eE₀ : E₀ = eA + 12 * a := by linarith
  have eE₁ : E₁ = eB + 12 * b := by linarith
  have h12 : (12 : ZMod n) = 0 := by
    have := (ZMod.natCast_eq_zero_iff 12 n).2 hn
    exact_mod_cast this
  rw [ht, eE₀, eE₁, zsmul_eq_mul, zsmul_eq_mul]
  push_cast [Nat.cast_sub heA, Nat.cast_sub heB]
  linear_combination ((x : ZMod n) + y + a * x + b * y) * h12

theorem corr_spec {e vA vB eA eB : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12]) (heA : eA ≤ 12)
    (heB : eB ≤ 12) :
    zc (corrC e vA vB eA eB) * zc vA ^ E₀ * zc vB ^ E₁ =
      z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3) := by
  set t₁ := (e % 48 / 12 + (12 - eA) * (vA % 4) + (12 - eB) * (vB % 4)) % 4 with ht₁
  set t₂ := (e % 12 / 3 + (12 - eA) * (vA / 4 % 4) + (12 - eB) * (vB / 4 % 4)) % 4 with ht₂
  set t₃ := (e % 3 + (12 - eA) * (vA / 16) + (12 - eB) * (vB / 16)) % 3 with ht₃
  have hc : corrC e vA vB eA eB = t₁ + 4 * t₂ + 16 * t₃ := rfl
  have l₁ : t₁ < 4 := Nat.mod_lt _ (by norm_num)
  have l₂ : t₂ < 4 := Nat.mod_lt _ (by norm_num)
  have l₃ : t₃ < 3 := Nat.mod_lt _ (by norm_num)
  have c₁ : (t₁ + 4 * t₂ + 16 * t₃) % 4 = t₁ := by omega
  have c₂ : (t₁ + 4 * t₂ + 16 * t₃) / 4 % 4 = t₂ := by omega
  have c₃ : (t₁ + 4 * t₂ + 16 * t₃) / 16 = t₃ := by omega
  rw [hc, zc, c₁, c₂, c₃, zpow3_eq_zHom, zc_eq_zHom, zc_eq_zHom, zpow3_eq_zHom, ← map_zpow,
    ← map_zpow, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · refine comp_corr (by norm_num) h₀ h₁ heA heB ?_
    rw [ht₁, ZMod.natCast_mod]
    push_cast [ZMod.natCast_mod]
    rfl
  · refine comp_corr (by norm_num) h₀ h₁ heA heB ?_
    rw [ht₂, ZMod.natCast_mod]
    push_cast [ZMod.natCast_mod]
    rfl
  · refine comp_corr (by norm_num) h₀ h₁ heA heB ?_
    rw [ht₃, ZMod.natCast_mod]
    push_cast
    rfl

theorem eN_le (j : ℕ) (w : List ℕ) : eN j w ≤ 12 := by
  unfold eN
  have := Nat.mod_lt (w.foldl (fun s c => Nat.add s (cond (Nat.beq c (Nat.mul 2 j)) 1
    (cond (Nat.beq c (Nat.add (Nat.mul 2 j) 1)) 11 0))) 0) (show 12 > 0 by norm_num)
  omega

theorem alGen_sound {V : ℕ} {TA TB A : ℕ → ℕ}
    (hV : vtOK V = true) (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1) (hAl : AlOf A)
    {C : List (List ℕ)} (hC : ∀ k, (tw k).map letterCode = C.getD k [])
    {uA uB : List (Fin 2 × Bool)} {vA vB i k : ℕ} (hi : i < 36) (hk : k < 64)
    (h : alGenOK V TA TB C A (uA.map letterCode) (uB.map letterCode) vA vB i k = true) :
    cv (substWord [uA, uB] (tw k)) * zc vA ^ expOf 0 (tw k) * zc vB ^ expOf 1 (tw k) =
      cv (tw (alphaEntry i k).1) * cv (zOf (alphaEntry i k)) := by
  unfold alGenOK at h
  rw [bindB_eq] at h
  have hU : [uA.map letterCode, uB.map letterCode] = [uA, uB].map (List.map letterCode) := rfl
  rw [← hC, ← hC, hU, ← map_letterCode_substWord, ← map_letterCode_invRev, ← List.map_append] at h
  have hid : cv (substWord [uA, uB] (tw k) ++ FreeGroup.invRev (tw (ent A i k / 48))) =
      zc (corrC (ent A i k) vA vB (eN 0 ((tw k).map letterCode)) (eN 1 ((tw k).map letterCode))) :=
    cv_of_zvOK hV hA hB h
  rw [cv_append, cv_invRev] at hid
  have e0 := eN_modEq 0 (tw k)
  have e1 := eN_modEq 1 (tw k)
  rw [Fin.val_zero] at e0
  rw [Fin.val_one] at e1
  have hcorr := corr_spec (e := ent A i k) (vA := vA) (vB := vB) e0 e1 (eN_le _ _) (eN_le _ _)
  have hq : alphaEntry i k = quad (ent A i k) := hAl i k hi (by omega)
  have hsub : cv (substWord [uA, uB] (tw k)) =
      zc (corrC (ent A i k) vA vB (eN 0 ((tw k).map letterCode)) (eN 1 ((tw k).map letterCode))) *
        cv (tw (ent A i k / 48)) := by
    rw [← hid]
    group
  have hcen := zc_mem_center
    (corrC (ent A i k) vA vB (eN 0 ((tw k).map letterCode)) (eN 1 ((tw k).map letterCode)))
  rw [hq]
  simp only [zOf, quad]
  rw [cv_zword, hsub, (mem_center_iff.1 hcen _).symm]
  simp only [mul_assoc] at hcorr ⊢
  rw [hcorr]

end CFSG.Certificates.L34Cov

end

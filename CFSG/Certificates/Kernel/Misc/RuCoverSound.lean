module

public import Certificates.Data.Kernel.Misc.RuCoverK
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermSound
public import CFSG.Certificates.Kernel.Misc.RuScanSound

public section

namespace CFSG.KC.Misc.RuCover

open CFSG.KC.Enum CFSG.KC.MiscCoset CFSG.KC.MiscCoset.Act CFSG.KC.Misc.RuInv CFSG.Certificates
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.KS.Raw.Orb
  CFSG.KC.Misc.RuScan CFSG.Certificates.CosetEnumeration

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem walk_codes {m N : ℕ} {A : ℕ → ℕ} {σ : Fin m → Equiv.Perm (Fin N)} (hA : Act.Rep A m N σ) :
    ∀ (u : List (Fin m × Bool)) (x : Fin N), walk A (Nat.add m m) (u.map letterCode) x.val =
      ((signedProd (fun g => (σ g)⁻¹) u)⁻¹ x).val
  | [], x => by
    change x.val = _
    simp only [signedProd_nil, inv_one, Equiv.Perm.one_apply]
  | (g, b) :: u, x => by
    have hs : walk A (Nat.add m m) (((g, b) :: u).map letterCode) x.val =
        walk A (Nat.add m m) (u.map letterCode)
          (A (x.val * (m + m) + letterCode (g, b))) := rfl
    rw [hs, signedProd_cons, mul_inv_rev, Equiv.Perm.mul_apply]
    cases b
    · have e : A (x.val * (m + m) + letterCode (g, false)) = ((σ g)⁻¹ x).val := by
        have := (hA g x).2
        simpa [letterCode] using this
      rw [e, walk_codes hA u]
      simp
    · have e : A (x.val * (m + m) + letterCode (g, true)) = (σ g x).val := by
        have := (hA g x).1
        simpa [letterCode] using this
      rw [e, walk_codes hA u]
      simp

theorem signedProd_invRev {m : ℕ} {G : Type*} [Group G] (τ : Fin m → G)
    (u : List (Fin m × Bool)) : signedProd τ (FreeGroup.invRev u) = (signedProd τ u)⁻¹ := by
  rw [← lift_mk_eq_signedProd, ← lift_mk_eq_signedProd, ← FreeGroup.inv_mk, map_inv]

theorem letters_cons {l : ℤ} {w : List ℤ} (h : Native.lettersOK 2 (l :: w) = true) :
    (l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) ∧ Native.lettersOK 2 w = true := by
  simp only [Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨h0, h2⟩, hw⟩ := h
  refine ⟨by omega, ?_⟩
  simpa [Native.lettersOK, List.all_eq_true] using hw

variable {G : Type*} [Group G]

theorem wordIn_cons1 (gs : ℕ → G) (w : List ℤ) : wordIn 2 gs (1 :: w) = gs 0 * wordIn 2 gs w := by
  rw [show (1 :: w : List ℤ) = [1] ++ w from rfl, wordIn_append]
  congr 1
  simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_cons_true]

theorem wordIn_consN1 (gs : ℕ → G) (w : List ℤ) :
    wordIn 2 gs (-1 :: w) = (gs 0)⁻¹ * wordIn 2 gs w := by
  rw [show (-1 :: w : List ℤ) = [-1] ++ w from rfl, wordIn_append]
  congr 1
  simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_cons_false]

theorem wordIn_cons2 (gs : ℕ → G) (w : List ℤ) : wordIn 2 gs (2 :: w) = gs 1 * wordIn 2 gs w := by
  rw [show (2 :: w : List ℤ) = [2] ++ w from rfl, wordIn_append]
  congr 1
  simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_cons_true]

theorem wordIn_consN2 (gs : ℕ → G) (w : List ℤ) :
    wordIn 2 gs (-2 :: w) = (gs 1)⁻¹ * wordIn 2 gs w := by
  rw [show (-2 :: w : List ℤ) = [-2] ++ w from rfl, wordIn_append]
  congr 1
  simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_cons_false]

theorem walkW_sound {N : ℕ} {A : ℕ → ℕ} {σ : Fin 3 → Equiv.Perm (Fin N)} (hA : Act.Rep A 3 N σ)
    (φ : G →* Equiv.Perm (Fin N)) {gs : ℕ → G} {u₀ u₁ : List (Fin 3 × Bool)}
    (h₀ : φ (gs 0) = signedProd (fun g => (σ g)⁻¹) u₀)
    (h₁ : φ (gs 1) = signedProd (fun g => (σ g)⁻¹) u₁) {Q₀ Q₁ Q₂ Q₃ : List ℕ}
    (e₀ : u₀.map letterCode = Q₀) (e₁ : (FreeGroup.invRev u₀).map letterCode = Q₁)
    (e₂ : u₁.map letterCode = Q₂) (e₃ : (FreeGroup.invRev u₁).map letterCode = Q₃) :
    ∀ w : List ℤ, Native.lettersOK 2 w = true → ∀ x : Fin N,
      walkW A Q₀ Q₁ Q₂ Q₃ w x.val = ((φ (wordIn 2 gs w))⁻¹ x).val
  | [], _, x => by
    change x.val = _
    simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_nil]
  | l :: w, hw, x => by
    obtain ⟨hl, hw'⟩ := letters_cons hw
    have hs : walkW A Q₀ Q₁ Q₂ Q₃ (l :: w) x.val =
        walkW A Q₀ Q₁ Q₂ Q₃ w (walk A (nat_lit 6) (selL Q₀ Q₁ Q₂ Q₃ l) x.val) := by
      change strictN _ _ = _
      rw [strictN_eq']
      rfl
    have hwalk : ∀ u : List (Fin 3 × Bool), walk A (nat_lit 6) (u.map letterCode) x.val =
        ((signedProd (fun g => (σ g)⁻¹) u)⁻¹ x).val := fun u => walk_codes hA u x
    have ih := walkW_sound hA φ h₀ h₁ e₀ e₁ e₂ e₃ w hw'
    rw [hs]
    rcases hl with rfl | rfl | rfl | rfl
    · have e : selL Q₀ Q₁ Q₂ Q₃ (1 : ℤ) = Q₀ := rfl
      have h := hwalk u₀
      rw [e₀, ← h₀] at h
      rw [e, h, ih, wordIn_cons1]
      simp only [map_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    · have e : selL Q₀ Q₁ Q₂ Q₃ (-1 : ℤ) = Q₁ := rfl
      have h := hwalk (FreeGroup.invRev u₀)
      rw [e₁, signedProd_invRev, ← h₀] at h
      rw [e, h, ih, wordIn_consN1]
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]
    · have e : selL Q₀ Q₁ Q₂ Q₃ (2 : ℤ) = Q₂ := rfl
      have h := hwalk u₁
      rw [e₂, ← h₁] at h
      rw [e, h, ih, wordIn_cons2]
      simp only [map_mul, mul_inv_rev, Equiv.Perm.mul_apply]
    · have e : selL Q₀ Q₁ Q₂ Q₃ (-2 : ℤ) = Q₃ := rfl
      have h := hwalk (FreeGroup.invRev u₁)
      rw [e₃, signedProd_invRev, ← h₁] at h
      rw [e, h, ih, wordIn_consN2]
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

theorem walkP_sound {f : ℕ → Equiv.Perm (Fin 4060)} {P₀ P₁ P₂ P₃ : ℕ}
    (h₀ : PRep 4060 12 P₀ (f 0)⁻¹) (h₁ : PRep 4060 12 P₁ (f 0))
    (h₂ : PRep 4060 12 P₂ (f 1)⁻¹) (h₃ : PRep 4060 12 P₃ (f 1)) :
    ∀ w : List ℤ, Native.lettersOK 2 w = true → ∀ x : Fin 4060,
      walkP P₀ P₁ P₂ P₃ w x.val = ((wordIn 2 f w)⁻¹ x).val
  | [], _, x => by
    change x.val = _
    simp [wordIn, toLetters, Quiver.SchreierGraph.evalWord_nil]
  | l :: w, hw, x => by
    obtain ⟨hl, hw'⟩ := letters_cons hw
    have hs : walkP P₀ P₁ P₂ P₃ (l :: w) x.val =
        walkP P₀ P₁ P₂ P₃ w (apP (selL P₀ P₁ P₂ P₃ l) x.val) := by
      change strictN _ _ = _
      rw [strictN_eq']
      rfl
    have ih := walkP_sound h₀ h₁ h₂ h₃ w hw'
    rw [hs]
    rcases hl with rfl | rfl | rfl | rfl
    · have e : selL P₀ P₁ P₂ P₃ (1 : ℤ) = P₀ := rfl
      rw [e, apP_eq h₀, ih, wordIn_cons1]
      simp only [mul_inv_rev, Equiv.Perm.mul_apply]
    · have e : selL P₀ P₁ P₂ P₃ (-1 : ℤ) = P₁ := rfl
      rw [e, apP_eq h₁, ih, wordIn_consN1]
      simp only [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]
    · have e : selL P₀ P₁ P₂ P₃ (2 : ℤ) = P₂ := rfl
      rw [e, apP_eq h₂, ih, wordIn_cons2]
      simp only [mul_inv_rev, Equiv.Perm.mul_apply]
    · have e : selL P₀ P₁ P₂ P₃ (-2 : ℤ) = P₃ := rfl
      rw [e, apP_eq h₃, ih, wordIn_consN2]
      simp only [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply]

theorem etaW_succ (c m : ℕ) :
    etaW c (m + 1) =
      etaW c m ++ cond (c.testBit m) (CFSG.Quasithin.KGC31.RuCover.eW.getD m []) [] := rfl

theorem lettersOK_append {u v : List ℤ} (hu : Native.lettersOK 2 u = true)
    (hv : Native.lettersOK 2 v = true) :
    Native.lettersOK 2 (u ++ v) = true := by
  simp only [Native.lettersOK, List.all_append, Bool.and_eq_true] at hu hv ⊢
  exact ⟨hu, hv⟩

theorem eq_of_onePoint {J : Type*} [Group J] [Finite G] {N : ℕ} (π : G →* J)
    (hπ : Function.Surjective π) (hcard : Nat.card G ≤ 2 * Nat.card J) {z : G}
    (hz : π z = 1) (hz1 : z ≠ 1) (φ : G →* Equiv.Perm (Fin N)) {p : Fin N} (hzp : φ z p ≠ p)
    {x y : G} (hxy : π x = π y) (hp : (φ x)⁻¹ p = (φ y)⁻¹ p) : x = y := by
  have hJ : Finite J := Finite.of_surjective _ hπ
  have hG : Nat.card G = Nat.card J * Nat.card π.ker := by
    rw [π.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hπ).toEquiv]
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hk : Nat.card π.ker ≤ 2 := by
    rw [hG] at hcard
    exact Nat.le_of_mul_le_mul_left (by linarith) hJpos
  have hzk : Subgroup.zpowers z ≤ π.ker := by
    rw [Subgroup.zpowers_le]
    exact hz
  have ho1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have ho2 : orderOf z ≤ 2 := by
    rw [← Nat.card_zpowers]
    exact (Subgroup.card_le_of_le hzk).trans hk
  have ho : orderOf z = 2 := by
    have := orderOf_pos z
    omega
  have hkz : π.ker = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hzk (by rw [Nat.card_zpowers, ho]; exact hk)).symm
  have hu : y * x⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  rw [hkz] at hu
  have hfix : φ (y * x⁻¹) p = p := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, hp, ← Equiv.Perm.mul_apply, mul_inv_cancel,
      Equiv.Perm.one_apply]
  obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hmod : z ^ k = z ^ (k % 2) := by
    rw [← zpow_mod_orderOf, ho]
    rfl
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hmod, h0, zpow_zero] at hk'
    exact (mul_inv_eq_one.mp hk'.symm).symm
  · rw [hmod, h1, zpow_one] at hk'
    rw [← hk'] at hfix
    exact absurd hfix hzp

end CFSG.KC.Misc.RuCover

end

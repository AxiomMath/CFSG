module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Schur
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec122_exists_W {s : (Fin 5 → ZMod 2) → G}
    (hadd : ∀ n m, IsEvenVec n → IsEvenVec m → s (n + m) = s n * s m) :
    ∃ W : Subgroup G, ∀ x, x ∈ W ↔ ∃ n, IsEvenVec n ∧ x = s n := by
  have hzero : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have hs0 : s 0 = 1 := by
    have h := hadd 0 0 hzero hzero
    rw [add_zero] at h
    have h2 := congrArg (fun z => z * (s 0)⁻¹) h
    simp at h2
    exact h2.symm
  have hss : ∀ n, IsEvenVec n → s n * s n = 1 := by
    intro n hn
    have h := hadd n n hn hn
    rw [show n + n = 0 from by funext i; exact CharTwo.add_self_eq_zero (n i), hs0] at h
    exact h.symm
  have heven_add : ∀ n m : Fin 5 → ZMod 2, IsEvenVec n → IsEvenVec m → IsEvenVec (n + m) := by
    intro n m hn hm
    unfold IsEvenVec at hn hm ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hn, hm, add_zero]
  refine ⟨{ carrier := {x | ∃ n, IsEvenVec n ∧ x = s n}
            one_mem' := ⟨0, hzero, hs0.symm⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨n + m, heven_add n m hn hm, (hadd n m hn hm).symm⟩
  · rintro x ⟨n, hn, rfl⟩
    exact ⟨n, hn, by rw [inv_eq_of_mul_eq_one_right (hss n hn)]⟩

theorem sec122_W_inv {B Y W : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    {s : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ B Y (alternatingGroup (Fin 5)))
    (hsY : ∀ y ∈ Y, ∀ σ : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
        ∀ n, IsEvenVec n → y * s n * y⁻¹ = s (permVec σ n))
    (hW : ∀ x, x ∈ W ↔ ∃ n, IsEvenVec n ∧ x = s n) :
    ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
  intro y hy w hw
  obtain ⟨n, hn, rfl⟩ := (hW w).mp hw
  obtain ⟨σ, hσ, hconj⟩ := hperm.2.2.2.1 y hy
  rw [hW (y * s n * y⁻¹)]
  exact ⟨permVec σ n, isEvenVec_permVec σ hn, hsY y hy σ hconj n hn⟩

theorem sec122_complements {V B Y : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} {f : G → G}
    {s : (Fin 5 → ZMod 2) → G}
    (hcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hsq : ∀ v ∈ V, v * v = 1) (hBV : B ≤ V)
    (hperm : IsPermModuleVia IsEvenVec φ B Y (alternatingGroup (Fin 5)))
    (hfB : ∀ v ∈ V, f v ∈ B) (hfmul : ∀ v ∈ V, ∀ w ∈ V, f (v * w) = f v * f w)
    (hfker : ∀ v ∈ V, f v = 1 ↔ v ∈ B)
    (hsV : ∀ n, IsEvenVec n → s n ∈ V)
    (hsadd : ∀ n m, IsEvenVec n → IsEvenVec m → s (n + m) = s n * s m)
    (hsf : ∀ n, IsEvenVec n → f (s n) = φ n)
    (hsY : ∀ y ∈ Y, ∀ σ : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ (permVec σ v)) →
        ∀ n, IsEvenVec n → y * s n * y⁻¹ = s (permVec σ n))
    {W' : Subgroup G} (hW'V : W' ≤ V) (hW'B : W' ⊓ B = ⊥)
    (hW'sup : ∀ x ∈ V, ∃ w ∈ W', ∃ b ∈ B, x = w * b)
    (hW'Y : ∀ y ∈ Y, ∀ w ∈ W', y * w * y⁻¹ ∈ W') :
    (∀ x, x ∈ W' ↔ ∃ n, IsEvenVec n ∧ x = s n) ∨
      (∀ x, x ∈ W' ↔ ∃ n, IsEvenVec n ∧ x = s n * φ n) := by
  have heven_add : ∀ n m : Fin 5 → ZMod 2, IsEvenVec n → IsEvenVec m → IsEvenVec (n + m) := by
    intro n m hn hm
    unfold IsEvenVec at hn hm ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hn, hm, add_zero]
  have phi0 : φ 0 = 1 := by
    have h := hperm.1 0 0 (by simp [IsEvenVec]) (by simp [IsEvenVec])
    rw [add_zero] at h
    have h2 := congrArg (fun z => z * (φ 0)⁻¹) h
    simp at h2
    exact h2.symm
  have hphiB : ∀ n, IsEvenVec n → φ n ∈ B :=
    fun n hn => (hperm.2.2.1 (φ n)).mpr ⟨n, hn, rfl⟩
  have hphiinj : ∀ n m, IsEvenVec n → IsEvenVec m → φ n = φ m → n = m :=
    fun n m hn hm h => hperm.2.1 n m hn hm h
  have hphiadd : ∀ n m, IsEvenVec n → IsEvenVec m → φ (n + m) = φ n * φ m :=
    fun n m hn hm => hperm.1 n m hn hm
  have hBmem : ∀ n, IsEvenVec n → φ n ∈ V := fun n hn => hBV (hphiB n hn)
  have hVinv : ∀ x ∈ V, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hsq x hx)
  have hex : ∀ n, IsEvenVec n → ∃ w : G, ∃ d : Fin 5 → ZMod 2,
      w ∈ W' ∧ IsEvenVec d ∧ s n = w * φ d := by
    intro n hn
    obtain ⟨w, hw, b, hb, hswb⟩ := hW'sup (s n) (hsV n hn)
    obtain ⟨d, hd, hphid⟩ := (hperm.2.2.1 b).mp hb
    exact ⟨w, d, hw, hd, by rw [hswb, ← hphid]⟩
  have hex' : ∀ n : Fin 5 → ZMod 2, ∃ p : G × (Fin 5 → ZMod 2),
      (IsEvenVec n → p.1 ∈ W' ∧ IsEvenVec p.2 ∧ s n = p.1 * φ p.2) := by
    intro n
    by_cases hn : IsEvenVec n
    · obtain ⟨w, d, hw, hd, hsd⟩ := hex n hn
      exact ⟨(w, d), fun _ => ⟨hw, hd, hsd⟩⟩
    · exact ⟨(1, 0), fun h => absurd h hn⟩
  let w' : (Fin 5 → ZMod 2) → G := fun n => (Classical.choose (hex' n)).1
  let δ : (Fin 5 → ZMod 2) → (Fin 5 → ZMod 2) := fun n => (Classical.choose (hex' n)).2
  have hp : ∀ n (hn : IsEvenVec n), w' n ∈ W' ∧ IsEvenVec (δ n) ∧ s n = w' n * φ (δ n) :=
    fun n hn => Classical.choose_spec (hex' n) hn
  have hw'mem : ∀ n (hn : IsEvenVec n), w' n ∈ W' := fun n hn => (hp n hn).1
  have hδeven : ∀ n (hn : IsEvenVec n), IsEvenVec (δ n) := fun n hn => (hp n hn).2.1
  have hδeq : ∀ n (hn : IsEvenVec n), s n = w' n * φ (δ n) := fun n hn => (hp n hn).2.2
  have huniq : ∀ w₁ ∈ W', ∀ w₂ ∈ W', ∀ d₁ d₂, IsEvenVec d₁ → IsEvenVec d₂ →
      w₁ * φ d₁ = w₂ * φ d₂ → w₁ = w₂ ∧ d₁ = d₂ := by
    intro w₁ h₁ w₂ h₂ d₁ d₂ hd₁ hd₂ heq
    have hkey : w₂⁻¹ * w₁ = φ d₂ * (φ d₁)⁻¹ := by
      have h := congrArg (fun z => w₂⁻¹ * z * (φ d₁)⁻¹) heq
      rw [show w₂⁻¹ * (w₁ * φ d₁) * (φ d₁)⁻¹ = w₂⁻¹ * w₁ from by group,
        show w₂⁻¹ * (w₂ * φ d₂) * (φ d₁)⁻¹ = φ d₂ * (φ d₁)⁻¹ from by group] at h
      exact h
    have hconv : φ d₂ * (φ d₁)⁻¹ = φ (d₂ + d₁) := by
      rw [hVinv (φ d₁) (hBmem d₁ hd₁), ← hphiadd d₂ d₁ hd₂ hd₁]
    have hmemW : w₂⁻¹ * w₁ ∈ W' := W'.mul_mem (W'.inv_mem h₂) h₁
    have hmemB : φ (d₂ + d₁) ∈ B := hphiB _ (heven_add d₂ d₁ hd₂ hd₁)
    have hbot : w₂⁻¹ * w₁ ∈ (⊥ : Subgroup G) := by
      rw [← hW'B]
      exact ⟨hmemW, by rw [hkey, hconv]; exact hmemB⟩
    have h1 : w₂⁻¹ * w₁ = 1 := by simpa using hbot
    have hw : w₁ = w₂ := by
      have h := h1
      rw [inv_mul_eq_one] at h
      exact h.symm
    have hd : d₁ = d₂ := by
      apply hphiinj d₁ d₂ hd₁ hd₂
      rw [hw] at heq
      exact mul_left_cancel heq
    exact ⟨hw, hd⟩
  have hδadd : ∀ n m, IsEvenVec n → IsEvenVec m → δ (n + m) = δ n + δ m := by
    intro n m hn hm
    have hnm : IsEvenVec (n + m) := heven_add n m hn hm
    have heq : w' (n + m) * φ (δ (n + m)) = (w' n * w' m) * φ (δ n + δ m) := by
      rw [← hδeq (n + m) hnm, hsadd n m hn hm, hδeq n hn, hδeq m hm,
        hphiadd (δ n) (δ m) (hδeven n hn) (hδeven m hm)]
      exact Commute.mul_mul_mul_comm
        (hcomm (φ (δ n)) (hBmem (δ n) (hδeven n hn)) (w' m) (hW'V (hw'mem m hm))) _ _
    exact (huniq (w' (n + m)) (hw'mem _ hnm) (w' n * w' m) (W'.mul_mem (hw'mem n hn) (hw'mem m hm))
      (δ (n + m)) (δ n + δ m) (hδeven _ hnm) (heven_add _ _ (hδeven n hn) (hδeven m hm)) heq).2
  have hδcomm : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEvenVec v →
      δ (permVec σ v) = permVec σ (δ v) := by
    intro σ hσ v hv
    obtain ⟨y, hy, hconj⟩ := hperm.2.2.2.2 σ hσ
    have hpy : y * s v * y⁻¹ = s (permVec σ v) := hsY y hy σ hconj v hv
    have hpv : IsEvenVec (permVec σ v) := isEvenVec_permVec σ hv
    have hleft : y * s v * y⁻¹ = (y * w' v * y⁻¹) * φ (permVec σ (δ v)) := by
      rw [hδeq v hv, ← hconj (δ v) (hδeven v hv)]
      group
    have heq : (y * w' v * y⁻¹) * φ (permVec σ (δ v)) =
        w' (permVec σ v) * φ (δ (permVec σ v)) := by
      rw [← hleft, hpy, hδeq (permVec σ v) hpv]
    have hyw : y * w' v * y⁻¹ ∈ W' := hW'Y y hy (w' v) (hw'mem v hv)
    have hpd : IsEvenVec (permVec σ (δ v)) := isEvenVec_permVec σ (hδeven v hv)
    exact ((huniq (y * w' v * y⁻¹) hyw (w' (permVec σ v)) (hw'mem _ hpv)
      (permVec σ (δ v)) (δ (permVec σ v)) hpd (hδeven _ hpv) heq).2).symm
  rcases sec122_schur δ hδeven hδadd hδcomm with hzero | hid
  ·
    left
    intro x
    constructor
    · intro hx
      have hxV : x ∈ V := hW'V hx
      have hfxB : f x ∈ B := hfB x hxV
      obtain ⟨m, hm, hφm⟩ := (hperm.2.2.1 (f x)).mp hfxB
      have hsmW : s m ∈ W' := by
        rw [hδeq m hm, hzero m hm, phi0, mul_one]
        exact hw'mem m hm
      have hfxsm : f (x * s m) = 1 := by
        rw [hfmul x hxV (s m) (hsV m hm), hsf m hm, hφm]
        exact hsq (f x) (hBV hfxB)
      have hxB : x * s m ∈ B :=
        (hfker (x * s m) (V.mul_mem hxV (hsV m hm))).mp hfxsm
      have hxW : x * s m ∈ W' := W'.mul_mem hx hsmW
      have hone : x * s m = 1 := by
        have hbot : x * s m ∈ (⊥ : Subgroup G) := by
          rw [← hW'B]
          exact ⟨hxW, hxB⟩
        simpa using hbot
      exact ⟨m, hm, by rw [eq_inv_of_mul_eq_one_left hone, hVinv (s m) (hsV m hm)]⟩
    · rintro ⟨n, hn, rfl⟩
      rw [hδeq n hn, hzero n hn, phi0, mul_one]
      exact hw'mem n hn
  ·
    right
    intro x
    constructor
    · intro hx
      have hxV : x ∈ V := hW'V hx
      have hfxB : f x ∈ B := hfB x hxV
      obtain ⟨m, hm, hφm⟩ := (hperm.2.2.1 (f x)).mp hfxB
      have hxmW : s m * φ m ∈ W' := by
        rw [hδeq m hm, hid m hm, mul_assoc, hsq (φ m) (hBmem m hm), mul_one]
        exact hw'mem m hm
      have hfx'' : f (s m * φ m) = φ m := by
        rw [hfmul (s m) (hsV m hm) (φ m) (hBmem m hm), hsf m hm,
          (hfker (φ m) (hBmem m hm)).mpr (hphiB m hm), mul_one]
      have hmemV : s m * φ m ∈ V := V.mul_mem (hsV m hm) (hBmem m hm)
      have hxx'' : f (x * (s m * φ m)) = 1 := by
        rw [hfmul x hxV (s m * φ m) hmemV, hfx'', hφm]
        exact hsq (f x) (hBV hfxB)
      have hmemB : x * (s m * φ m) ∈ B :=
        (hfker (x * (s m * φ m)) (V.mul_mem hxV hmemV)).mp hxx''
      have hmemW : x * (s m * φ m) ∈ W' := W'.mul_mem hx hxmW
      have hone : x * (s m * φ m) = 1 := by
        have hbot : x * (s m * φ m) ∈ (⊥ : Subgroup G) := by
          rw [← hW'B]
          exact ⟨hmemW, hmemB⟩
        simpa using hbot
      exact ⟨m, hm, by rw [eq_inv_of_mul_eq_one_left hone, hVinv _ hmemV]⟩
    · rintro ⟨n, hn, rfl⟩
      rw [hδeq n hn, hid n hn, mul_assoc, hsq (φ n) (hBmem n hn), mul_one]
      exact hw'mem n hn

end CFSG.OddStandard.SmallF3.Omega

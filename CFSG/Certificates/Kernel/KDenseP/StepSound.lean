module

public import CFSG.Certificates.Kernel.KDense.StepSound
public import CFSG.Certificates.Kernel.KStep.Mono
import CFSG.Certificates.Kernel.KDense.Data.Checks
import CFSG.Certificates.Kernel.KDense.Data.KeySort

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.Monster.AxisCount

theorem monoTabOK_get {F : Fix} {MT : MonoTab} (h : monoTabOK F MT = true) :
    ∀ k (hk : k < MT.keys.length), monoEntOK F MT.keys[k] (MT.ents k) = true := by
  have key : ∀ (L : List (List ℕ)) (k0 : ℕ), List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun l _ ih k => andB (monoEntOK F l (MT.ents k)) (ih (Nat.add k (nat_lit 1)))) L k0 = true →
      ∀ i (hi : i < L.length), monoEntOK F L[i] (MT.ents (k0 + i)) = true := by
    intro L
    induction L with
    | nil => intro _ _ i hi; exact absurd hi (Nat.not_lt_zero i)
    | cons x L ih =>
      intro k0 h0 i hi
      obtain ⟨h1, h2⟩ := Benes.andB_true h0
      rcases i with _ | i
      · simpa using h1
      · have := ih (k0 + 1) h2 i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  intro k hk
  have := key MT.keys 0 h k hk
  rwa [Nat.zero_add] at this

theorem dataOKP_parts {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ}
    (h : dataOKP F MT KT TH OCT DU1 = true) :
    KeyBind F ∧ xiOK F = true ∧ poutOK F = true ∧ pi6OK F = true ∧ tauMasksOK F = true ∧
      monoTabOK F MT = true := by
  unfold dataOKP fixOK at h
  simp only [andB_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, ⟨x1, x2, x3, x4⟩, h7⟩ := h
  exact ⟨keyBind_of h1 h2 h3 h4 h5, x1, x2, x3, x4, h7⟩

end CFSG.KC.KStep

namespace CFSG.KC.KDenseP

open CFSG.KC.KStep CFSG.KC.KDense CFSG.Monster.AxisCount

theorem stepN_sound {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} {MT : MonoTab}
    {KT TH OCT DU1 : Nat} (h : dataOKP F MT KT TH OCT DU1 = true)
    (g : Native.Gen) (hg : letterOK g = true) (v : Native.DVec) (s : St) (hs : RepN n v s)
    (hf : (stepN n lg F MT g s).1 = true) :
    g.validB = true ∧ RepN n (Native.applyGen (Native.mkCtx ()) g v) (stepN n lg F MT g s) := by
  obtain ⟨hK, hx, hp, h6, hm, ht⟩ := dataOKP_parts h
  have hG : KeysGood := CFSG.KC.KDense.keys_sound CFSG.KD.KDF.F CFSG.KD.KDF.KT CFSG.KD.KDF.TH
      CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 CFSG.KD.KDK.NK CFSG.KD.KDF.th_ok CFSG.KD.KDF.oct_ok
      CFSG.KD.KDF.du1_ok CFSG.KD.KDF.keys_ok CFSG.KD.KDF.keyPlanes_ok CFSG.KD.KDK.keys_distinct
  obtain ⟨ok, X, A, W⟩ := s
  cases g with
  | rho q =>
    obtain ⟨qs, qa, qd⟩ := q
    have ha : qa < 4096 := by
      have : Nat.blt qa 4096 = true := hg
      rwa [Nat.blt_eq] at this
    refine ⟨rfl, ?_⟩
    have e : stepN n lg F MT (.rho (qs, qa, qd)) (ok, X, A, W) =
        (andB ok true, (rhoG (opsN n lg) F qs.toNat qa qd X A W).2) := by
      cases qs <;> rfl
    rw [e]
    exact rho_sound (opsN_law hn hlg) hn hK hG qs ha qd hs _
  | perm arr =>
    have hsz : arr.size = 24 := by
      have : Nat.beq arr.size 24 = true := hg
      rwa [Nat.beq_eq] at this
    have e : stepN n lg F MT (.perm arr) (ok, X, A, W) =
        (andB ok (findIdx (arrList arr) MT.keys).1,
          monoStepN n (MT.ents (findIdx (arrList arr) MT.keys).2) X A W) :=
      rfl
    rw [e] at hf ⊢
    have hf' : (findIdx (arrList arr) MT.keys).1 = true := by
      have : andB ok (findIdx (arrList arr) MT.keys).1 = true := hf
      rw [andB_eq', Bool.and_eq_true] at this
      exact this.2
    obtain ⟨hk, hkl⟩ := findIdx_spec hf'
    have he := monoTabOK_get ht _ hk
    rw [hkl] at he
    exact monoPerm_sound hn hlg hK hG hsz he hs _
  | sign a =>
    have e : stepN n lg F MT (.sign a) (ok, X, A, W) =
        (andB ok (findIdx [a] MT.keys).1, monoStepN n (MT.ents (findIdx [a] MT.keys).2) X A W) :=
      rfl
    rw [e] at hf ⊢
    have hf' : (findIdx [a] MT.keys).1 = true := by
      have : andB ok (findIdx [a] MT.keys).1 = true := hf
      rw [andB_eq', Bool.and_eq_true] at this
      exact this.2
    obtain ⟨hk, hkl⟩ := findIdx_spec hf'
    have he := monoTabOK_get ht _ hk
    rw [hkl] at he
    exact ⟨rfl, monoSign_sound hn hlg hK hG he hs _⟩
  | xi =>
    exact ⟨rfl, xi_sound (opsN_law hn hlg) hn hK hG hx hp hs ok⟩
  | tau =>
    exact ⟨rfl, tau_sound (opsN_law hn hlg) hn h6 hm hs ok⟩

end CFSG.KC.KDenseP

end

module

public import Certificates.Data.Kernel.SporSch.ConjKey
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.KS.ConjKey

open CFSG.KC.Loop CFSG.KC.ConjKey Matrix

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictKB_eq (y : Nat) (k : Nat → Bool) : strictKB y k = k y := by
  cases y <;> rfl

theorem eqK_spec {a b : Nat} (h : eqK a b = true) : a = b := Nat.eq_of_beq_eq_true h

variable {G : Type*} [Group G]

@[expose] def elF (g : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | fuel + 1, c => if c = 0 then 1 else g (c % 8 - 1) * elF g fuel (c / 8)

theorem elF_zero (g : ℕ → G) (c : ℕ) : elF g 0 c = 1 := by simp [elF]

theorem elF_succ_zero (g : ℕ → G) (fuel : ℕ) : elF g (fuel + 1) 0 = 1 := by simp [elF]

theorem elF_succ (g : ℕ → G) (fuel : ℕ) {c : ℕ} (hc : c ≠ 0) :
    elF g (fuel + 1) c = g (c % 8 - 1) * elF g fuel (c / 8) := by simp [elF, hc]

theorem letter_lt (c : ℕ) : c % 8 - 1 < 7 := by omega

theorem beq_ne {c : ℕ} (hc : c ≠ 0) : Nat.beq c 0 = false :=
  Bool.eq_false_iff.2 fun h => hc (Nat.eq_of_beq_eq_true h)

theorem appF_succ (vm : ℕ → ℕ → ℕ) (GL : ℕ → ℕ) (fuel : ℕ) {c : ℕ} (hc : c ≠ 0) (v : ℕ) :
    appF vm GL (fuel + 1) c v = appF vm GL fuel (c / 8) (vm v (GL (c % 8 - 1))) := by
  change Bool.rec (motive := fun _ => Nat) (strictN (vm v (GL (Nat.sub (Nat.mod c 8) 1)))
    (fun u => appF vm GL fuel (Nat.div c 8) u)) v (Nat.beq c 0) = _
  rw [beq_ne hc, strictN_eq] <;> rfl

theorem appI_succ (vm : ℕ → ℕ → ℕ) (GIL : ℕ → ℕ) (fuel : ℕ) {c : ℕ} (hc : c ≠ 0) (v : ℕ) :
    appI vm GIL (fuel + 1) c v = vm (appI vm GIL fuel (c / 8) v) (GIL (c % 8 - 1)) := by
  change Bool.rec (motive := fun _ => Nat) (strictN (appI vm GIL fuel (Nat.div c 8) v)
    (fun u => vm u (GIL (Nat.sub (Nat.mod c 8) 1)))) v (Nat.beq c 0) = _
  rw [beq_ne hc, strictN_eq] <;> rfl

section Sound

variable {n p : ℕ} {ρ : G →* Matrix (Fin n) (Fin n) (ZMod p)} {g : ℕ → G}
  {vm : ℕ → ℕ → ℕ} {Ok : ℕ → Prop} {toV : ℕ → Fin n → ZMod p} {GL GIL : ℕ → ℕ}

theorem appF_sound
    (hG : ∀ v l, l < 7 → Ok v → Ok (vm v (GL l)) ∧ toV (vm v (GL l)) = toV v ᵥ* ρ (g l)) :
    ∀ fuel c v, Ok v → Ok (appF vm GL fuel c v) ∧
      toV (appF vm GL fuel c v) = toV v ᵥ* ρ (elF g fuel c)
  | 0, c, v, hv => by
    refine ⟨hv, ?_⟩
    change toV v = _
    rw [elF_zero, map_one, vecMul_one]
  | fuel + 1, c, v, hv => by
    by_cases hc : c = 0
    · subst hc
      refine ⟨hv, ?_⟩
      change toV v = _
      rw [elF_succ_zero, map_one, vecMul_one]
    · obtain ⟨h1, h2⟩ := hG v _ (letter_lt c) hv
      obtain ⟨h3, h4⟩ := appF_sound hG fuel (c / 8) _ h1
      rw [appF_succ vm GL fuel hc]
      refine ⟨h3, ?_⟩
      rw [h4, h2, vecMul_vecMul, ← map_mul, elF_succ g fuel hc]

theorem appI_sound
    (hG : ∀ v l, l < 7 → Ok v → Ok (vm v (GIL l)) ∧ toV (vm v (GIL l)) = toV v ᵥ* ρ (g l)⁻¹) :
    ∀ fuel c v, Ok v → Ok (appI vm GIL fuel c v) ∧
      toV (appI vm GIL fuel c v) = toV v ᵥ* ρ (elF g fuel c)⁻¹
  | 0, c, v, hv => by
    refine ⟨hv, ?_⟩
    change toV v = _
    rw [elF_zero, inv_one, map_one, vecMul_one]
  | fuel + 1, c, v, hv => by
    by_cases hc : c = 0
    · subst hc
      refine ⟨hv, ?_⟩
      change toV v = _
      rw [elF_succ_zero, inv_one, map_one, vecMul_one]
    · obtain ⟨h1, h2⟩ := appI_sound hG fuel (c / 8) v hv
      obtain ⟨h3, h4⟩ := hG _ _ (letter_lt c) h1
      rw [appI_succ vm GIL fuel hc]
      refine ⟨h3, ?_⟩
      rw [h4, h2, vecMul_vecMul, ← map_mul, elF_succ g fuel hc, mul_inv_rev]

theorem keyOf_sound
    (hG : ∀ v l, l < 7 → Ok v → Ok (vm v (GL l)) ∧ toV (vm v (GL l)) = toV v ᵥ* ρ (g l))
    (hGI : ∀ v l, l < 7 → Ok v → Ok (vm v (GIL l)) ∧ toV (vm v (GIL l)) = toV v ᵥ* ρ (g l)⁻¹)
    {Y : ℕ} {y : G} (hY : ∀ v, Ok v → Ok (vm v Y) ∧ toV (vm v Y) = toV v ᵥ* ρ y)
    (fuel : ℕ) {e : ℕ} (he : Ok e) (c : ℕ) :
    Ok (keyOf vm GL GIL fuel Y e c) ∧
      toV (keyOf vm GL GIL fuel Y e c) =
        toV e ᵥ* ρ (elF g fuel c * y * (elF g fuel c)⁻¹) := by
  unfold keyOf
  rw [strictN_eq, strictN_eq]
  obtain ⟨h1, h2⟩ := appF_sound hG fuel c e he
  obtain ⟨h3, h4⟩ := hY _ h1
  obtain ⟨h5, h6⟩ := appI_sound hGI fuel c _ h3
  refine ⟨h5, ?_⟩
  rw [h6, h4, h2, vecMul_vecMul, vecMul_vecMul, ← map_mul, ← map_mul, mul_assoc]

end Sound

theorem incK_spec (key : ℕ → ℕ) :
    ∀ (L : List ℕ) (p : ℕ), incK key L p = true →
      (L.map key).Pairwise (· < ·) ∧ ∀ k ∈ L.map key, p < k
  | [], _, _ => ⟨List.Pairwise.nil, by simp⟩
  | c :: L, p, h => by
    have e : incK key (c :: L) p = strictKB (key c) (fun k => bAnd(Nat.blt p k, incK key L k)) :=
      rfl
    rw [e, strictKB_eq] at h
    cases h1 : Nat.blt p (key c)
    · rw [h1] at h
      exact absurd h Bool.false_ne_true
    · rw [h1] at h
      obtain ⟨h2, h3⟩ := incK_spec key L (key c) h
      have hp : p < key c := Nat.blt_eq ▸ h1
      rw [List.map_cons]
      refine ⟨List.Pairwise.cons (fun k hk => h3 k hk) h2, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hp
      · exact hp.trans (h3 k hk)

theorem conjKeysOK_spec {vm : ℕ → ℕ → ℕ} {GL GIL : ℕ → ℕ} {fuel Y e : ℕ} {L : List ℕ} {n : ℕ}
    (h : conjKeysOK vm GL GIL fuel Y e L n = true) :
    L.length = n ∧ (L.map (keyOf vm GL GIL fuel Y e)).Nodup := by
  have h' : bAnd(Nat.beq (List.length L) n, incK (keyOf vm GL GIL fuel Y e) L 0) = true := h
  cases hb : Nat.beq (List.length L) n
  · rw [hb] at h'
    exact absurd h' Bool.false_ne_true
  · rw [hb] at h'
    exact ⟨Nat.eq_of_beq_eq_true hb,
      (incK_spec _ L 0 h').1.imp fun hab => Nat.ne_of_lt hab⟩

theorem conj_mul_of_comm {a b y : G} (hb : b * y = y * b) : a * b * y * (a * b)⁻¹ = a * y * a⁻¹ := by
  rw [mul_inv_rev, mul_assoc a b y, hb]
  group

theorem length_mul_card_le (C : Subgroup G) (y : G) (L : List G) (hL : ∀ x ∈ L, x ∈ C)
    (hn : (L.map fun c => c * y * c⁻¹).Nodup) (hC : Nat.card C ≠ 0) :
    L.length * Nat.card (C ⊓ Subgroup.centralizer {y} : Subgroup G) ≤ Nat.card C := by
  have : Finite C := Nat.finite_of_card_ne_zero hC
  let f : Fin L.length × (C ⊓ Subgroup.centralizer {y} : Subgroup G) → C := fun q =>
    ⟨L[q.1] * q.2, C.mul_mem (hL _ (List.getElem_mem _)) (Subgroup.mem_inf.1 q.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have h' : L[i] * (s : G) = L[j] * t := congrArg Subtype.val h
    have hs : (s : G) * y = y * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 s.2).2
    have ht : (t : G) * y = y * t :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 t.2).2
    have hc : L[i] * y * L[i]⁻¹ = L[j] * y * L[j]⁻¹ := by
      rw [← conj_mul_of_comm (a := L[i]) hs, ← conj_mul_of_comm (a := L[j]) ht, h']
    have e1 : (L.map fun c => c * y * c⁻¹)[i.val]'(by simp) =
        (L.map fun c => c * y * c⁻¹)[j.val]'(by simp) := by
      simp only [List.getElem_map]
      exact hc
    have hij : i = j := Fin.ext ((hn.getElem_inj_iff).1 e1)
    subst hij
    have hst : s = t := Subtype.ext (mul_left_cancel h')
    rw [hst]
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h

end CFSG.KS.ConjKey

end

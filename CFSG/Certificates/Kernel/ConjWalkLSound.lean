module

public import Certificates.Data.Kernel.ConjWalkL
public import CFSG.Certificates.Kernel.ConjWalkSound

public section

namespace CFSG.KC.ConjWalk

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.ConjCount

section Group

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

@[expose] def kapL (n : ℕ) [MulAction Γ (Fin n)] (ps : List ℕ) (g : Γ) : ℕ :=
  ps.foldr (fun a k => act n g a + n * k) 0

theorem keyL_eq {ps : List ℕ} {C : ℕ} {g : Γ} (hps : ∀ a ∈ ps, a < n) (hC : Rp n C g) :
    keyL n ps C = kapL n ps g := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    have e : keyL n (a :: ps) C = ln C a + n * keyL n ps C := rfl
    rw [e, ih (fun x hx => hps x (List.mem_cons_of_mem a hx)), hC a (hps a List.mem_cons_self)]
    rfl

variable {H : Subgroup Γ} {x0 x1 t : Γ} {ps : List ℕ} {X0 X0I X1 X1I : ℕ}

theorem walkLAux_sound (h0 : x0 ∈ H) (h1 : x1 ∈ H) (hX0 : Rp n X0 x0) (hX0I : Rp n X0I x0⁻¹)
    (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹) (hps : ∀ a ∈ ps, a < n) :
    ∀ (recs s : List ℕ) (S d : ℕ) (L : List Γ),
      walkLAux n ps X0 X0I X1 X1I recs s S d = true → s.length = d →
      (∀ C ∈ s, ∃ g ∈ H, Rp n C (g * t * g⁻¹)) → (∀ g ∈ L, g ∈ H) →
      (L.map fun g => kapL n ps (g * t * g⁻¹)).Nodup →
      (∀ k, S.testBit k = true ↔ k ∈ L.map fun g => kapL n ps (g * t * g⁻¹)) →
      ∃ L' : List Γ, (∀ g ∈ L', g ∈ H) ∧ (L'.map fun g => kapL n ps (g * t * g⁻¹)).Nodup ∧
        L'.length = L.length + recs.length
  | [], _, _, _, L, _, _, _, hL, hnd, _ => ⟨L, hL, hnd, rfl⟩
  | r :: rs, s, S, d, L, hw, hs, hC, hL, hnd, hS => by
    have e : walkLAux n ps X0 X0I X1 X1I (r :: rs) s S d = strictB (Nat.shiftRight r 1) fun p =>
        Nat.blt p d &&
        strictB (Bool.rec (motive := fun _ => Nat) (cjP n X1 X1I (topS (popS p s)))
          (cjP n X0 X0I (topS (popS p s))) (Nat.beq (Nat.land r 1) 0)) fun C =>
        strictB (keyL n ps C) fun k =>
        Nat.beq (Nat.land (Nat.shiftRight S k) 1) 0 &&
        strictB (Nat.lor S (Nat.shiftLeft 1 k)) fun S' =>
        strictB (Nat.succ (Nat.sub d p)) fun d' =>
          walkLAux n ps X0 X0I X1 X1I rs (C :: popS p s) S' d' := rfl
    rw [e] at hw
    simp only [strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hw
    obtain ⟨hp, hbit, hw⟩ := hw
    set p := Nat.shiftRight r 1
    have hne : popS p s ≠ [] := by
      rw [popS_eq, ne_eq, List.drop_eq_nil_iff]
      omega
    obtain ⟨g, hg, hpar⟩ := hC (topS (popS p s))
      (List.mem_of_mem_drop (i := p) (by rw [← popS_eq]; exact topS_mem hne))
    have hnew : ∀ B : Bool, ∃ g' ∈ H, Rp n (Bool.rec (motive := fun _ => Nat)
        (cjP n X1 X1I (topS (popS p s))) (cjP n X0 X0I (topS (popS p s))) B) (g' * t * g'⁻¹) := by
      intro B
      have conj : ∀ x : Γ, x * (g * t * g⁻¹) * x⁻¹ = (x * g) * t * (x * g)⁻¹ := fun x => by group
      cases B
      · exact ⟨x1 * g, H.mul_mem h1 hg, conj x1 ▸ rp_cjP hX1 hX1I hpar⟩
      · exact ⟨x0 * g, H.mul_mem h0 hg, conj x0 ▸ rp_cjP hX0 hX0I hpar⟩
    obtain ⟨g', hg', hC'⟩ := hnew (Nat.beq (Nat.land r 1) 0)
    rw [keyL_eq hps hC'] at hbit hw
    have hk := testBit_of_land hbit
    have hnot : kapL n ps (g' * t * g'⁻¹) ∉ L.map fun g => kapL n ps (g * t * g⁻¹) := by
      intro hm
      rw [← hS] at hm
      rw [hm] at hk
      exact Bool.noConfusion hk
    obtain ⟨L', hL', hnd', hlen⟩ := walkLAux_sound h0 h1 hX0 hX0I hX1 hX1I hps rs _ _ _
      (g' :: L) hw (by rw [List.length_cons, popS_eq, List.length_drop, hs]; rfl)
      (fun C hm => by
        rcases List.mem_cons.1 hm with rfl | hm
        · exact ⟨g', hg', hC'⟩
        · exact hC C (List.mem_of_mem_drop (popS_eq s p ▸ hm)))
      (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hg'
        · exact hL x hx)
      (by rw [List.map_cons]; exact List.nodup_cons.2 ⟨hnot, hnd⟩)
      (fun k => by rw [testBit_lor_one, hS, List.map_cons, List.mem_cons]; exact or_comm)
    refine ⟨L', hL', hnd', ?_⟩
    rw [hlen, List.length_cons, List.length_cons]
    omega

theorem walkKL_sound {T : ℕ} {recs : List ℕ} (h0 : x0 ∈ H) (h1 : x1 ∈ H) (hX0 : Rp n X0 x0)
    (hX0I : Rp n X0I x0⁻¹) (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹) (hT : Rp n T t)
    (hps : ∀ a ∈ ps, a < n) (h : walkKL n ps X0 X0I X1 X1I T recs = true) :
    ∃ L : List Γ, (∀ g ∈ L, g ∈ H) ∧ (L.map fun g => g * t * g⁻¹).Nodup ∧
      L.length = recs.length + 1 := by
  unfold walkKL at h
  simp only [strictB_eq] at h
  have hT' : Rp n T ((1 : Γ) * t * (1 : Γ)⁻¹) := by rw [one_mul, inv_one, mul_one]; exact hT
  rw [keyL_eq hps hT'] at h
  obtain ⟨L, hL, hnd, hlen⟩ := walkLAux_sound h0 h1 hX0 hX0I hX1 hX1I hps recs [T] _ 1 [1] h
    rfl (fun C hm => by rw [List.mem_singleton.1 hm]; exact ⟨1, H.one_mem, hT'⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact H.one_mem) (List.nodup_singleton _)
    (fun k => by
      rw [show Nat.shiftLeft 1 (kapL n ps ((1 : Γ) * t * (1 : Γ)⁻¹)) =
        Nat.lor 0 (Nat.shiftLeft 1 (kapL n ps ((1 : Γ) * t * (1 : Γ)⁻¹))) from
        (Nat.zero_or _).symm, testBit_lor_one, Nat.zero_testBit]
      simp)
  refine ⟨L, hL, ?_, by rw [hlen, List.length_singleton, Nat.add_comm]⟩
  have e : (L.map fun g => kapL n ps (g * t * g⁻¹)) =
      (L.map fun g => g * t * g⁻¹).map (kapL n ps) := by
    rw [List.map_map]
    rfl
  rw [e] at hnd
  exact hnd.of_map _

theorem walkKL_noFifteen [Finite Γ] {T m : ℕ} {recs : List ℕ} (h0 : x0 ∈ H) (h1 : x1 ∈ H)
    (hX0 : Rp n X0 x0) (hX0I : Rp n X0I x0⁻¹) (hX1 : Rp n X1 x1) (hX1I : Rp n X1I x1⁻¹)
    (hT : Rp n T t) (hps : ∀ a ∈ ps, a < n) (h : walkKL n ps X0 X0I X1 X1I T recs = true)
    (htH : t ∈ H) (ht : orderOf t = 5) (hH : Nat.card H = 5 * m) (hm : ¬ 5 ∣ m)
    (hlen : Nat.card H < 15 * (recs.length + 1)) :
    ∀ z ∈ H, orderOf z ≠ 15 := by
  obtain ⟨L, hL, hnd, hl⟩ := walkKL_sound h0 h1 hX0 hX0I hX1 hX1I hT hps h
  exact no_orderOf_fifteen hH hm htH ht L hL hnd (by rw [hl]; exact hlen)

end Group

end CFSG.KC.ConjWalk

end

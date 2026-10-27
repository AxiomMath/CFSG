module

public import Certificates.Data.Kernel.D43.Base
public import CFSG.Milestones.ASVolI.F48.Small.Pres
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.D43

open CFSG.ASVolI CFSG.KS.PackFld CFSG.KC.Enum

section Group

variable {G : Type*} [Group G]

@[expose] noncomputable def dV (γ : ℕ → G) (φ : G) (d : ℕ) : G :=
  if d < 8 then γ d else if d < 16 then (γ (d - 8))⁻¹ else if d = 16 then φ else φ⁻¹

@[expose] noncomputable def wV (γ : ℕ → G) (φ : G) (w : List ℕ) : G := (w.map (dV γ φ)).prod

theorem wV_nil (γ : ℕ → G) (φ : G) : wV γ φ [] = 1 := rfl

theorem wV_cons (γ : ℕ → G) (φ : G) (d : ℕ) (w : List ℕ) :
    wV γ φ (d :: w) = dV γ φ d * wV γ φ w := by
  simp [wV]

theorem wV_append (γ : ℕ → G) (φ : G) (u v : List ℕ) :
    wV γ φ (u ++ v) = wV γ φ u * wV γ φ v := by
  simp [wV, List.map_append, List.prod_append]

theorem dV_digG (γ : ℕ → G) (φ : G) (l : Fin 8 × Bool) :
    dV γ φ (digG l) = cond l.2 (γ l.1) (γ l.1)⁻¹ := by
  obtain ⟨k, b⟩ := l
  have hk := k.2
  cases b
  · have e : digG (k, false) = k.val + 8 := rfl
    rw [e]
    unfold dV
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]
    rfl
  · have e : digG (k, true) = k.val := rfl
    rw [e]
    unfold dV
    rw [if_pos hk]
    rfl

theorem wV_flatG (γ : ℕ → G) (φ : G) (w : List (Fin 8 × Bool)) :
    wV γ φ (flatG w) = burnsideF48s_ev (fun k : Fin 8 => γ k) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [flatG, List.map_cons, ← flatG, wV_cons, ih, dV_digG, burnsideF48s_ev_cons]

theorem ev_invW {m : ℕ} (h : Fin m → G) (w : List (Fin m × Bool)) :
    burnsideF48s_ev h (invW w) = (burnsideF48s_ev h w)⁻¹ := by
  induction w with
  | nil => simp [invW, burnsideF48s_ev]
  | cons l w ih =>
    have e : invW (l :: w) = invW w ++ [(l.1, !l.2)] := by simp [invW]
    rw [e, burnsideF48s_ev_append, ih, burnsideF48s_ev_cons, burnsideF48s_ev_cons, mul_inv_rev]
    obtain ⟨j, b⟩ := l
    cases b <;> simp [burnsideF48s_ev]

theorem wV_mem {H : Subgroup G} {γ : ℕ → G} {φ : G} (hγ : ∀ k < 8, γ k ∈ H) (h3 : φ ^ 3 = 1)
    (hn : ∀ h ∈ H, φ * h * φ⁻¹ ∈ H) :
    ∀ w : List ℕ, ∃ h ∈ H, wV γ φ w = h * φ ^ cntD w := by
  have hφi : φ⁻¹ = φ * φ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact h3
  intro w
  induction w with
  | nil => exact ⟨1, H.one_mem, by simp [wV_nil, cntD]⟩
  | cons d w ih =>
    obtain ⟨h, hh, e⟩ := ih
    have ec : cntD (d :: w) = (if d < 16 then 0 else if d = 16 then 1 else 2) + cntD w := by
      change Nat.add (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 2 1 (Nat.beq d 16)) 0 (Nat.blt d 16)) (cntD w) = _
      by_cases h16 : d < 16
      · rw [Nat.blt_eq.mpr h16, if_pos h16]
        rfl
      · have hb : Nat.blt d 16 = false := by
          rw [Bool.eq_false_iff]
          intro hb
          exact h16 (Nat.blt_eq.mp hb)
        rw [hb, if_neg h16]
        by_cases he : d = 16
        · subst he
          rfl
        · have hb2 : Nat.beq d 16 = false := by
            rw [Bool.eq_false_iff]
            intro hb2
            exact he (Nat.eq_of_beq_eq_true hb2)
          rw [hb2, if_neg he]
          rfl
    rw [wV_cons, e, ec]
    by_cases h16 : d < 16
    · rw [if_pos h16, zero_add]
      refine ⟨dV γ φ d * h, H.mul_mem ?_ hh, by rw [mul_assoc]⟩
      unfold dV
      by_cases h8 : d < 8
      · rw [if_pos h8]
        exact hγ d h8
      · rw [if_neg h8, if_pos h16]
        exact H.inv_mem (hγ (d - 8) (by omega))
    · rw [if_neg h16]
      unfold dV
      rw [if_neg (by omega), if_neg h16]
      by_cases he : d = 16
      · rw [if_pos he, if_pos he]
        refine ⟨φ * h * φ⁻¹, hn h hh, ?_⟩
        rw [pow_add, pow_one]
        simp only [mul_assoc, inv_mul_cancel_left]
      · rw [if_neg he, if_neg he]
        refine ⟨φ * (φ * h * φ⁻¹) * φ⁻¹, hn _ (hn h hh), ?_⟩
        rw [pow_add, pow_two]
        simp only [mul_assoc, inv_mul_cancel_left]
        rw [hφi, mul_assoc]

end Group

section Points

variable {F P : ℕ → ℕ} {γ : ℕ → Equiv.Perm (Fin 26572)} {φ : Equiv.Perm (Fin 26572)}

theorem inv_apply_of_cube {g : Equiv.Perm (Fin 26572)} (h3 : g ^ 3 = 1) (p : Fin 26572) :
    g⁻¹ p = g (g p) := by
  have e : g⁻¹ = g * g := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_three]
    exact h3
  rw [e, Equiv.Perm.mul_apply]

theorem dPt_spec (hγ : ∀ k < 8, ∀ p : Fin 26572, (γ k p : ℕ) = tabAt F k p)
    (h3 : ∀ k < 8, γ k ^ 3 = 1) (hφ : ∀ p : Fin 26572, (φ p : ℕ) = tabAt P 0 p) (hφ3 : φ ^ 3 = 1)
    (d : ℕ) (p : Fin 26572) : dPt F P d p = (dV γ φ d p : ℕ) := by
  unfold dPt dV
  by_cases h8 : d < 8
  · rw [Nat.blt_eq.mpr h8, if_pos h8]
    exact (hγ d h8 p).symm
  have hb8 : Nat.blt d 8 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact h8 (Nat.blt_eq.mp hb)
  rw [hb8, if_neg h8]
  by_cases h16 : d < 16
  · rw [Nat.blt_eq.mpr h16, if_pos h16]
    change strictN (tabAt F (d - 8) p) (tabAt F (d - 8)) = _
    rw [strictN_eqP, inv_apply_of_cube (h3 (d - 8) (by omega)), ← hγ (d - 8) (by omega) p,
      ← hγ (d - 8) (by omega)]
  have hb16 : Nat.blt d 16 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact h16 (Nat.blt_eq.mp hb)
  rw [hb16, if_neg h16]
  by_cases he : d = 16
  · subst he
    rw [if_pos rfl]
    exact (hφ p).symm
  have hbe : Nat.beq d 16 = false := by
    rw [Bool.eq_false_iff]
    intro hb
    exact he (Nat.eq_of_beq_eq_true hb)
  rw [hbe, if_neg he]
  change strictN (tabAt P 0 p) (tabAt P 0) = _
  rw [strictN_eqP, inv_apply_of_cube hφ3, ← hφ p, ← hφ]

theorem wPt_spec (hγ : ∀ k < 8, ∀ p : Fin 26572, (γ k p : ℕ) = tabAt F k p)
    (h3 : ∀ k < 8, γ k ^ 3 = 1) (hφ : ∀ p : Fin 26572, (φ p : ℕ) = tabAt P 0 p) (hφ3 : φ ^ 3 = 1) :
    ∀ (w : List ℕ) (p : Fin 26572), wPt F P w p = (wV γ φ w p : ℕ) := by
  intro w
  induction w with
  | nil => intro p; rfl
  | cons d w ih =>
    intro p
    change strictN (wPt F P w p) (dPt F P d) = _
    rw [strictN_eqP, ih p, dPt_spec hγ h3 hφ hφ3, wV_cons, Equiv.Perm.mul_apply]

theorem fixL_spec {w : List ℕ} : ∀ {bs : List ℕ}, fixL F P w bs = true → ∀ b ∈ bs, wPt F P w b = b
  | [], _ => by simp
  | b :: bs, h => by
    change Bool.rec (motive := fun _ => Bool) false (fixL F P w bs) (Nat.beq (wPt F P w b) b) =
      true at h
    cases hb : Nat.beq (wPt F P w b) b
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact Nat.eq_of_beq_eq_true hb
      · exact fixL_spec h c hc

theorem wV_one_of_wOK {H : Subgroup (Equiv.Perm (Fin 26572))}
    (hγ : ∀ k < 8, ∀ p : Fin 26572, (γ k p : ℕ) = tabAt F k p) (h3 : ∀ k < 8, γ k ^ 3 = 1)
    (hφ : ∀ p : Fin 26572, (φ p : ℕ) = tabAt P 0 p) (hφ3 : φ ^ 3 = 1)
    (hH : ∀ k < 8, γ k ∈ H) (hn : ∀ h ∈ H, φ * h * φ⁻¹ ∈ H)
    (hbase : ∀ h ∈ H, (∀ b ∈ baseL, ∀ hb : b < 26572, h ⟨b, hb⟩ = ⟨b, hb⟩) → h = 1)
    {w : List ℕ} (hw : wOK F P w = true) : wV γ φ w = 1 := by
  change Bool.rec (motive := fun _ => Bool) false (fixL F P w baseL)
    (Nat.beq (Nat.mod (cntD w) 3) 0) = true at hw
  cases hc : Nat.beq (Nat.mod (cntD w) 3) 0
  · rw [hc] at hw
    exact absurd hw Bool.false_ne_true
  rw [hc] at hw
  have hc3 : cntD w % 3 = 0 := Nat.eq_of_beq_eq_true hc
  obtain ⟨h, hh, e⟩ := wV_mem hH hφ3 hn w
  have hp : φ ^ cntD w = 1 := by
    rw [← Nat.div_add_mod (cntD w) 3, hc3, add_zero, pow_mul, hφ3, one_pow]
  rw [hp, mul_one] at e
  rw [e]
  refine hbase h hh fun b hb hb' => Fin.ext ?_
  have h1 := fixL_spec hw b hb
  rw [wPt_spec hγ h3 hφ hφ3 w ⟨b, hb'⟩, e] at h1
  exact h1

end Points

end CFSG.KC.D43

end

module

public import Certificates.Data.Kernel.Spor.RecMul
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KS.RecMul

open CFSG.KS.PEnum

variable {G : Type*} [Group G] {k cnt : ℕ} {POS PL : ℕ → ℕ} {x g : ℕ → G}

theorem mulRf_spec (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → parOf PL i < i ∧ labOf PL i < k ∧
      x i = x (parOf PL i) * g (labOf PL i))
    (hpos : ∀ i < cnt, ∀ j < k, r32 POS (i * k + j) < cnt ∧
      x (r32 POS (i * k + j)) = x i * g j) :
    ∀ f a b, a < cnt → b < cnt → reachRf PL f b = true →
      mulRf k POS PL f a b < cnt ∧ x (mulRf k POS PL f a b) = x a * x b := by
  intro f
  induction f with
  | zero =>
    intro a b ha _ hr
    have hb : b = 0 := by simpa [reachRf] using hr
    subst hb
    simp [mulRf, ha, hx0]
  | succ f ih =>
    intro a b ha hb hr
    by_cases h0 : b = 0
    · subst h0
      simp [mulRf, ha, hx0]
    · have hr' : reachRf PL f (parOf PL b) = true := by simpa [reachRf, h0] using hr
      obtain ⟨hp, hl, hxb⟩ := htree b (Nat.pos_of_ne_zero h0) hb
      obtain ⟨hm, hxm⟩ := ih a (parOf PL b) ha (by omega) hr'
      obtain ⟨hq, hxq⟩ := hpos _ hm _ hl
      have e : mulRf k POS PL (f + 1) a b =
          r32 POS (mulRf k POS PL f a (parOf PL b) * k + labOf PL b) := by
        simp [mulRf, h0]
      rw [e]
      refine ⟨hq, ?_⟩
      rw [hxq, hxm, hxb, mul_assoc]

theorem oddRf_spec {odd : ℕ → Bool} {P : Subgroup G} {u : G} (hu2 : u * u = 1)
    (hu : ∀ p ∈ P, u * p * u⁻¹ ∈ P) (hx0 : x 0 = 1)
    (htree : ∀ i, 0 < i → i < cnt → parOf PL i < i ∧ labOf PL i < k ∧
      x i = x (parOf PL i) * g (labOf PL i))
    (hg : ∀ j < k, (odd j = false → g j ∈ P) ∧ (odd j = true → g j * u ∈ P)) :
    ∀ f a, a < cnt → reachRf PL f a = true →
      (oddRf PL odd f a = false → x a ∈ P) ∧ (oddRf PL odd f a = true → x a * u ∈ P) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  intro f
  induction f with
  | zero =>
    intro a _ hr
    have ha : a = 0 := by simpa [reachRf] using hr
    subst ha
    exact ⟨fun _ => by rw [hx0]; exact P.one_mem, fun h => by simp [oddRf] at h⟩
  | succ f ih =>
    intro a ha hr
    by_cases h0 : a = 0
    · subst h0
      exact ⟨fun _ => by rw [hx0]; exact P.one_mem, fun h => by simp [oddRf] at h⟩
    · have hr' : reachRf PL f (parOf PL a) = true := by simpa [reachRf, h0] using hr
      obtain ⟨hp, hl, hxa⟩ := htree a (Nat.pos_of_ne_zero h0) ha
      obtain ⟨ih1, ih2⟩ := ih (parOf PL a) (by omega) hr'
      obtain ⟨hg1, hg2⟩ := hg _ hl
      have e : oddRf PL odd (f + 1) a =
          xor (oddRf PL odd f (parOf PL a)) (odd (labOf PL a)) := by
        simp [oddRf, h0]
      rw [e, hxa]
      cases hpar : oddRf PL odd f (parOf PL a) <;> cases hod : odd (labOf PL a)
      · exact ⟨fun _ => P.mul_mem (ih1 hpar) (hg1 hod), fun h => by simp at h⟩
      · refine ⟨fun h => by simp at h, fun _ => ?_⟩
        rw [mul_assoc]
        exact P.mul_mem (ih1 hpar) (hg2 hod)
      · refine ⟨fun h => by simp at h, fun _ => ?_⟩
        have e2 : x (parOf PL a) * g (labOf PL a) * u =
            x (parOf PL a) * u * (u * g (labOf PL a) * u⁻¹) := by
          rw [hui]
          simp only [mul_assoc]
          rw [← mul_assoc u u, hu2, one_mul]
        rw [e2]
        exact P.mul_mem (ih2 hpar) (hu _ (hg1 hod))
      · refine ⟨fun _ => ?_, fun h => by simp at h⟩
        have e2 : x (parOf PL a) * g (labOf PL a) =
            x (parOf PL a) * u * (u * (g (labOf PL a) * u) * u⁻¹) := by
          simp only [mul_assoc]
          rw [mul_inv_cancel, mul_one, ← mul_assoc u u, hu2, one_mul]
        rw [e2]
        exact P.mul_mem (ih2 hpar) (hu _ (hg2 hod))

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KS.Raw.Orb

theorem prep_unique {n w P : ℕ} {σ τ : Equiv.Perm (Fin n)} (h1 : PRep n w P σ)
    (h2 : PRep n w P τ) : σ = τ :=
  Equiv.ext fun y => Fin.ext ((h1 y).symm.trans (h2 y))

theorem penumRight_rec {n w k cnt cap : ℕ} {G GI T PL POS SRT SRI : ℕ → ℕ}
    {g : ℕ → Equiv.Perm (Fin n)} (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hG : ∀ j < k, G j = pidn n w) (hg : ∀ j < k, PRep n w (GI j) (g j))
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true) :
    ∃ x : ℕ → Equiv.Perm (Fin n), x 0 = 1 ∧ (∀ i < cnt, PRep n w (T i) (x i)) ∧
      (∀ i, 0 < i → i < cnt → parOf PL i < i ∧ labOf PL i < k ∧
        x i = x (parOf PL i) * g (labOf PL i)) ∧
      (∀ i < cnt, ∀ j < k, r32 POS (i * k + j) < cnt ∧ x (r32 POS (i * k + j)) = x i * g j) ∧
      (∀ a < cnt, ∀ b < cnt, x a = x b → a = b) := by
  classical
  unfold penumHdK at hh
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, -, hT0, -⟩ := hh
  have hT0' : T 0 = pidn n w := Nat.eq_of_beq_eq_true hT0
  have sp := fun i (hi : i < cnt) => penumPt_specH (hp i hi)
  have hn32 : n < 2 ^ 32 := by omega
  have hid : PRep n w (pidn n w) 1 := prep_pidn hn hw
  have hstep : ∀ j < k, ∀ t (σ : Equiv.Perm (Fin n)), PRep n w t σ →
      PRep n w (stepK n w (mask w) true G GI j t) (σ * g j) := by
    intro j hj t σ h
    have e : stepK n w (mask w) true G GI j t =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j) := rfl
    rw [e, hG j hj]
    have h' := prep_pcomp hn32 (prep_pcomp hn32 hid h) (hg j hj)
    rwa [one_mul] at h'
  have hex : ∀ i < cnt, ∃ σ : Equiv.Perm (Fin n), PRep n w (T i) σ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, by rw [hT0']; exact hid⟩
      · obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
        obtain ⟨σ, hσ⟩ := ih _ h1 (by omega)
        exact ⟨σ * g (labOf PL i), by rw [h3]; exact hstep _ h2 _ σ hσ⟩
  let x : ℕ → Equiv.Perm (Fin n) := fun i => if h : i < cnt then (hex i h).choose else 1
  have hx : ∀ i < cnt, PRep n w (T i) (x i) := by
    intro i hi
    simp only [x, dif_pos hi]
    exact (hex i hi).choose_spec
  have hx0 : x 0 = 1 := prep_unique (hx 0 hc0) (by rw [hT0']; exact hid)
  have htree : ∀ i, 0 < i → i < cnt → parOf PL i < i ∧ labOf PL i < k ∧
      x i = x (parOf PL i) * g (labOf PL i) := by
    intro i hpos hi
    obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
    refine ⟨h1, h2, prep_unique (hx i hi) ?_⟩
    rw [h3]
    exact hstep _ h2 _ _ (hx _ (by omega))
  have hpos : ∀ i < cnt, ∀ j < k, r32 POS (i * k + j) < cnt ∧
      x (r32 POS (i * k + j)) = x i * g j := by
    intro i hi j hj
    obtain ⟨h1, h2, -⟩ := (sp i hi).2.2.1 j hj
    refine ⟨h1, prep_unique (hx _ h1) ?_⟩
    rw [h2]
    exact hstep j hj _ _ (hx i hi)
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  have hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b := by
    intro a ha b hb e
    refine hinjT a ha b hb (unpack_injH (sp a ha).1 (sp b hb).1 ?_)
    have h1 := hx a ha
    have h2 := hx b hb
    rw [e] at h1
    unfold unpack
    congr 1
    funext i
    rw [h1 i, h2 i]
  exact ⟨x, hx0, hx, htree, hpos, hinj⟩

end CFSG.KS.RecMul

end

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {K G E : Type*} [Field K] [Group G] [Group E]

theorem pow_apply_eq_of_conj_fixed {φ : MulAut E} {y z : E} (hφz : φ z = z)
    (hzy : z = φ y * y⁻¹) (i : ℕ) : (φ ^ i) y = z ^ i * y := by
  induction i with
  | zero => rw [pow_zero, pow_zero, one_mul, MulAut.one_apply]
  | succ i ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφz, pow_succ, mul_assoc,
      show φ y = z * y by rw [hzy, inv_mul_cancel_right]]

theorem ker_eq_bot_of_two_weights [Finite E] [Group.IsPerfect E] (R : HeisenbergRoots K G)
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = R.S) (η : E →* G) (hη : Function.Surjective η)
    (hK : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) (φ₁ φ₂ : MulAut E) {r₁ r₂ : K}
    (hr₁ : r₁ ≠ 1) (hr₂ : r₂ ≠ 1) (hφ₁C : ∀ z ∈ η.ker, φ₁ z = z)
    (hφ₂C : ∀ z ∈ η.ker, φ₂ z = z) {m : ℕ} (hm : Odd m) (hφ₂m : φ₂ ^ m = 1)
    (hφ₁x : ∀ e a, η e = R.x a → η (φ₁ e) = R.x a)
    (hφ₁w : ∀ e c, η e = R.w c → η (φ₁ e) = R.w (r₁ * c))
    (hφ₂x : ∀ e a, η e = R.x a → η (φ₂ e) = R.x (r₂ * a))
    (hφ₂y : ∀ e b, η e = R.y b → η (φ₂ e) = R.y b)
    (hφ₂w : ∀ e c, η e = R.w c → η (φ₂ e) = R.w (r₂ * c)) :
    η.ker = ⊥ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hK hz
  have comm_eq : ∀ {x x' y y' : E}, η x = η x' → η y = η y' → ⁅x, y⁆ = ⁅x', y'⁆ :=
    fun hx hy => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker hx hy
  let lx : K → E := fun a => (hη (R.x a)).choose
  let ly : K → E := fun b => (hη (R.y b)).choose
  let lw : K → E := fun c => (hη (R.w c)).choose
  have hlx : ∀ a, η (lx a) = R.x a := fun a => (hη (R.x a)).choose_spec
  have hly : ∀ b, η (ly b) = R.y b := fun b => (hη (R.y b)).choose_spec
  have hlw : ∀ c, η (lw c) = R.w c := fun c => (hη (R.w c)).choose_spec
  have hWcomm := R.preimage_w_comm η hker hη
  have hf : ∀ c a, ⁅lw c, lx a⁆ = 1 := by
    have hfc : ∀ c a, ⁅lw c, lx a⁆ ∈ center E := fun c a =>
      R.commutatorElement_mem_center_of_w_x η hker (hlw c) (hlx a)
    have hadd : ∀ c c' a, ⁅lw (c + c'), lx a⁆ = ⁅lw c, lx a⁆ * ⁅lw c', lx a⁆ := fun c c' a => by
      rw [comm_eq (x' := lw c * lw c') (by rw [hlw, map_mul, hlw, hlw, R.w_add]) rfl,
        commutatorElement_mul_left_of_mem_center (hfc c' a)]
    have hinv : ∀ c a, ⁅lw (r₁ * c), lx a⁆ = ⁅lw c, lx a⁆ := fun c a => by
      have h := hφ₁C _ (show η ⁅lw c, lx a⁆ = 1 by
        rw [map_commutatorElement, hlw, hlx, R.commutatorElement_w_x])
      rw [map_commutatorElement] at h
      rw [← h]
      exact comm_eq (by rw [hlw, hφ₁w _ c (hlw c)]) (by rw [hlx, hφ₁x _ a (hlx a)])
    intro c a
    have hr : r₁ - 1 ≠ 0 := sub_ne_zero.mpr hr₁
    have h := hinv ((r₁ - 1)⁻¹ * c) a
    rw [show r₁ * ((r₁ - 1)⁻¹ * c) = c + (r₁ - 1)⁻¹ * c by field_simp; ring, hadd] at h
    exact mul_eq_right.mp h
  have hg : ∀ c b, ⁅lw c, ly b⁆ = 1 := by
    have hgc : ∀ c b, ⁅lw c, ly b⁆ ∈ center E := fun c b =>
      R.commutatorElement_mem_center_of_w_y η hker (hlw c) (hly b)
    have hadd : ∀ c c' b, ⁅lw (c + c'), ly b⁆ = ⁅lw c, ly b⁆ * ⁅lw c', ly b⁆ := fun c c' b => by
      rw [comm_eq (x' := lw c * lw c') (by rw [hlw, map_mul, hlw, hlw, R.w_add]) rfl,
        commutatorElement_mul_left_of_mem_center (hgc c' b)]
    have hinv : ∀ c b, ⁅lw (r₂ * c), ly b⁆ = ⁅lw c, ly b⁆ := fun c b => by
      have h := hφ₂C _ (show η ⁅lw c, ly b⁆ = 1 by
        rw [map_commutatorElement, hlw, hly, R.commutatorElement_w_y])
      rw [map_commutatorElement] at h
      rw [← h]
      exact comm_eq (by rw [hlw, hφ₂w _ c (hlw c)]) (by rw [hly, hφ₂y _ b (hly b)])
    intro c b
    have h := hinv ((r₂ - 1)⁻¹ * c) b
    have hr : r₂ - 1 ≠ 0 := sub_ne_zero.mpr hr₂
    rw [show r₂ * ((r₂ - 1)⁻¹ * c) = c + (r₂ - 1)⁻¹ * c by field_simp; ring, hadd] at h
    exact mul_eq_right.mp h
  set X : Set E := (η.ker : Set E) ∪ Set.range lx ∪ Set.range ly ∪ Set.range lw with hXdef
  have hXW : ∀ w : E, (∃ c, η w = R.w c) → ∀ t ∈ closure X, t * w = w * t := by
    rintro w ⟨c, hc⟩ t ht
    have hle : closure X ≤ Subgroup.centralizer {w} := by
      rw [closure_le]
      rintro s (((hs | ⟨a, rfl⟩) | ⟨b, rfl⟩) | ⟨c', rfl⟩)
      · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hker s hs) w).symm
      · have h : ⁅w, lx a⁆ = 1 := (comm_eq (by rw [hc, hlw]) rfl).trans (hf c a)
        exact mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp h).symm
      · have h : ⁅w, ly b⁆ = 1 := (comm_eq (by rw [hc, hlw]) rfl).trans (hg c b)
        exact mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp h).symm
      · exact mem_centralizer_singleton_iff.mpr (hWcomm _ _ ⟨c', hlw c'⟩ ⟨c, hc⟩)
    exact mem_centralizer_singleton_iff.mp (hle ht)
  have hsub : ∀ s ∈ X, s ∈ closure X := fun s hs => subset_closure hs
  let d : K → K → E := fun a b => ⁅lx a, ly b⁆
  have hd : ∀ a b, η (d a b) = R.w (a * b) := fun a b => by
    change η ⁅lx a, ly b⁆ = _
    rw [map_commutatorElement, hlx, hly, R.commutatorElement_x_y]
  have hd_add : ∀ a a' b, d (a + a') b = d a b * d a' b := fun a a' b => by
    change ⁅lx (a + a'), ly b⁆ = ⁅lx a, ly b⁆ * ⁅lx a', ly b⁆
    rw [comm_eq (x' := lx a * lx a') (by rw [hlx, map_mul, hlx, hlx, R.x_add]) rfl,
      commutatorElement_mul_left_eq,
      hXW _ ⟨_, hd a' b⟩ (lx a) (hsub _ (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))),
      mul_inv_cancel_right]
    exact hWcomm _ _ ⟨_, hd a' b⟩ ⟨_, hd a b⟩
  have hφd : ∀ a b, φ₂ (d a b) = d (r₂ * a) b := fun a b => by
    change φ₂ ⁅lx a, ly b⁆ = ⁅lx (r₂ * a), ly b⁆
    rw [map_commutatorElement]
    exact comm_eq (by rw [hlx, hφ₂x _ a (hlx a)]) (by rw [hly, hφ₂y _ b (hly b)])
  set D : Subgroup E := closure (Set.range fun p : K × K => d p.1 p.2) with hDdef
  have hDW : ∀ r ∈ D, ∃ c, η r = R.w c := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨p, rfl⟩ := hs
      exact ⟨_, hd p.1 p.2⟩
    | one => exact ⟨0, by rw [map_one, R.w_zero]⟩
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁
      obtain ⟨c₂, h₂⟩ := ih₂
      exact ⟨c₁ + c₂, by rw [map_mul, h₁, h₂, R.w_add]⟩
    | inv r _ ih =>
      obtain ⟨c, h⟩ := ih
      exact ⟨-c, by rw [map_inv, h, inv_eq_iff_mul_eq_one, ← R.w_add, add_neg_cancel, R.w_zero]⟩
  have hDcomm : ∀ r₁ ∈ D, ∀ r₂ ∈ D, r₁ * r₂ = r₂ * r₁ := fun r₁ h₁ r₂ h₂ =>
    hWcomm _ _ (hDW r₁ h₁) (hDW r₂ h₂)
  have hψ : ∀ z ∈ D, ∃ y ∈ D, z = φ₂ y * y⁻¹ := by
    have hr : r₂ - 1 ≠ 0 := sub_ne_zero.mpr hr₂
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hs
      refine ⟨d ((r₂ - 1)⁻¹ * a) b, subset_closure ⟨((r₂ - 1)⁻¹ * a, b), rfl⟩, ?_⟩
      rw [hφd, show r₂ * ((r₂ - 1)⁻¹ * a) = a + (r₂ - 1)⁻¹ * a by field_simp; ring, hd_add,
        mul_inv_cancel_right]
    | one => exact ⟨1, one_mem _, by rw [map_one, inv_one, mul_one]⟩
    | mul z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
      obtain ⟨y₁, hy₁, rfl⟩ := ih₁
      obtain ⟨y₂, hy₂, rfl⟩ := ih₂
      refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, ?_⟩
      have hc : y₁⁻¹ * (φ₂ y₂ * y₂⁻¹) = (φ₂ y₂ * y₂⁻¹) * y₁⁻¹ :=
        hDcomm _ (inv_mem hy₁) _ hz₂
      rw [map_mul, _root_.mul_inv_rev]
      calc φ₂ y₁ * y₁⁻¹ * (φ₂ y₂ * y₂⁻¹) = φ₂ y₁ * (y₁⁻¹ * (φ₂ y₂ * y₂⁻¹)) := by group
        _ = φ₂ y₁ * ((φ₂ y₂ * y₂⁻¹) * y₁⁻¹) := by rw [hc]
        _ = φ₂ y₁ * φ₂ y₂ * (y₂⁻¹ * y₁⁻¹) := by group
    | inv z hz ih =>
      obtain ⟨y, hy, rfl⟩ := ih
      refine ⟨y⁻¹, inv_mem hy, ?_⟩
      rw [map_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
      exact hDcomm _ hy _ (inv_mem (show φ₂ y ∈ D from by
        have := mul_mem hz hy
        rwa [inv_mul_cancel_right] at this))
  have hnorm : ∀ g ∈ closure X, ∀ r ∈ D, g * r * g⁻¹ ∈ D := fun g hg r hr => by
    rw [hXW r (hDW r hr) g hg, mul_inv_cancel_right]
    exact hr
  have hWX : ∀ s ∈ X, (s ∈ (η.ker : Set E) ∨ s ∈ Set.range lw) → ∃ c, η s = R.w c := by
    rintro s - (hs | ⟨c, rfl⟩)
    · exact ⟨0, by rw [R.w_zero]; exact hs⟩
    · exact ⟨c, hlw c⟩
  have hX : ∀ s ∈ X, ∀ s' ∈ X, ⁅s, s'⁆ ∈ D := by
    intro s hs s' hs'
    by_cases hs'W : s' ∈ (η.ker : Set E) ∨ s' ∈ Set.range lw
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXW s' (hWX s' hs' hs'W) s (hsub s hs))]
      exact one_mem _
    by_cases hsW : s ∈ (η.ker : Set E) ∨ s ∈ Set.range lw
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXW s (hWX s hs hsW) s' (hsub s' hs')).symm]
      exact one_mem _
    rcases hs with ((hs | ⟨a, rfl⟩) | ⟨b, rfl⟩) | ⟨c, rfl⟩
    · exact absurd (Or.inl hs) hsW
    · rcases hs' with ((hs' | ⟨a', rfl⟩) | ⟨b', rfl⟩) | ⟨c', rfl⟩
      · exact absurd (Or.inl hs') hs'W
      · have h1 : ⁅lx a, lx a'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          (R.preimage_x_comm η hker hη _ _ ⟨a, hlx a⟩ ⟨a', hlx a'⟩)
        rw [h1]
        exact one_mem _
      · exact subset_closure ⟨(a, b'), rfl⟩
      · exact absurd (Or.inr ⟨c', rfl⟩) hs'W
    · rcases hs' with ((hs' | ⟨a', rfl⟩) | ⟨b', rfl⟩) | ⟨c', rfl⟩
      · exact absurd (Or.inl hs') hs'W
      · rw [← commutatorElement_inv]
        exact inv_mem (subset_closure ⟨(a', b), rfl⟩)
      · have h1 : ⁅ly b, ly b'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          (R.preimage_y_comm η hker hη _ _ ⟨b, hly b⟩ ⟨b', hly b'⟩)
        rw [h1]
        exact one_mem _
      · exact absurd (Or.inr ⟨c', rfl⟩) hs'W
    · exact absurd (Or.inr ⟨c, rfl⟩) hsW
  have hTX : R.S.comap η ≤ closure X := R.comap_S_le_closure η lx ly lw hlx hly hlw
  obtain ⟨S, hS⟩ := hS
  obtain ⟨P, hP, hzP⟩ := exists_sylow_map_eq_twoPart_le η hη hK S
  have hPT : (P : Subgroup E) ≤ R.S.comap η := by
    rw [← map_le_iff_le_comap, hP, hS]
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  obtain ⟨n, hn⟩ := h2 ⟨z, hz⟩
  have hn' : z ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hzD : z ∈ D := (commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    commutatorElement_mem_of_mem_closure hnorm hX (hTX (hPT hg₁)) (hTX (hPT hg₂)))
    (hzP z hz ⟨n, hn'⟩)
  obtain ⟨y, -, hzy⟩ := hψ z hzD
  have hm1 := pow_apply_eq_of_conj_fixed (hφ₂C z hz) hzy m
  rw [hφ₂m, MulAut.one_apply] at hm1
  have hzm : z ^ m = 1 := mul_eq_right.mp hm1.symm
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right n hm.coprime_two_right
  have h := pow_gcd_eq_one.mpr ⟨hzm, hn'⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial

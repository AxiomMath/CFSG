module

public import CFSG.GH74.KGroups.Generic3

public section

namespace CFSG.GH74.KGroups

section Calculus

variable {K : Type*} [Group K]

@[expose] def cmm (a b : K) : K := a * b * a⁻¹ * b⁻¹

theorem cmm_mul_left {Z : Subgroup K} (hZ : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (a a' b : K)
    (h : cmm a' b ∈ Z) : cmm (a * a') b = cmm a' b * cmm a b := by
  have hc : a' * b * a'⁻¹ = cmm a' b * b := by simp only [cmm]; group
  calc cmm (a * a') b = a * (a' * b * a'⁻¹) * a⁻¹ * b⁻¹ := by simp only [cmm]; group
    _ = a * (cmm a' b * b) * a⁻¹ * b⁻¹ := by rw [hc]
    _ = (a * cmm a' b) * b * a⁻¹ * b⁻¹ := by group
    _ = (cmm a' b * a) * b * a⁻¹ * b⁻¹ := by rw [hZ _ h a]
    _ = cmm a' b * cmm a b := by simp only [cmm]; group

theorem cmm_mul_right {Z : Subgroup K} (hZ : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (a b b' : K)
    (h : cmm a b' ∈ Z) : cmm a (b * b') = cmm a b' * cmm a b := by
  have hc : a * b' * a⁻¹ = cmm a b' * b' := by simp only [cmm]; group
  calc cmm a (b * b') = (a * b * a⁻¹) * (a * b' * a⁻¹) * b'⁻¹ * b⁻¹ := by simp only [cmm]; group
    _ = (a * b * a⁻¹) * (cmm a b' * b') * b'⁻¹ * b⁻¹ := by rw [hc]
    _ = ((a * b * a⁻¹) * cmm a b') * b⁻¹ := by group
    _ = (cmm a b' * (a * b * a⁻¹)) * b⁻¹ := by rw [hZ _ h (a * b * a⁻¹)]
    _ = cmm a b' * cmm a b := by simp only [cmm]; group

theorem cmm_central_left {z : K} (hz : ∀ g : K, g * z = z * g) (a b : K) :
    cmm (a * z) b = cmm a b := by
  calc cmm (a * z) b = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by simp only [cmm]; group
    _ = a * b * a⁻¹ * b⁻¹ := by
      have : z * b * z⁻¹ = b := by rw [← hz b]; group
      rw [this]

theorem cmm_central_right {z : K} (hz : ∀ g : K, g * z = z * g) (a b : K) :
    cmm a (b * z) = cmm a b := by
  calc cmm a (b * z) = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by simp only [cmm]; group
    _ = a * b * a⁻¹ * b⁻¹ := by
      have : z * a⁻¹ * z⁻¹ = a⁻¹ := by rw [← hz a⁻¹]; group
      rw [this]

end Calculus

theorem exists_kappa {K G : Type*} [Group K] [Group G] (ε : K →* G) (Z : Subgroup K)
    (hZc : ∀ z ∈ Z, ∀ g : K, g * z = z * g) (hZcard : Nat.card Z = 2) (hker : ε.ker = Z)
    (S E : Subgroup G) (hES : E ≤ S) (hEz : ∀ w ∈ E, ∀ s ∈ S, w * s = s * w)
    (hεS : ∀ s ∈ S, ∃ k, ε k = s)
    (hAab : ∀ a b : K, ε a ∈ E → ε b ∈ E → a * b = b * a)
    (hnd : ∀ a : K, ε a ∈ E → ε a ≠ 1 → ∃ p : K, ε p ∈ S ∧ p * a * p⁻¹ * a⁻¹ ≠ 1) :
    ∃ κ : G → G → ZMod 2,
      (∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y) ∧
      (∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y') ∧
      (∀ w ∈ E, ∀ y ∈ E, κ w y = 0) ∧
      (∀ (ψ : K ≃* K) (g : G), (∀ k, ε (ψ k) = g * ε k * g⁻¹) →
        ∀ x ∈ S, ∀ y ∈ E, κ (g * x * g⁻¹) (g * y * g⁻¹) = κ x y) ∧
      (∀ x ∈ S, κ x (x ^ 2) = 0) ∧
      (∀ y ∈ E, y ≠ 1 → ∃ x ∈ S, κ x y ≠ 0) := by
  classical
  obtain ⟨z0, hz0Z, hz01, hZe⟩ := exists_unique_ne_one_of_card_two Z hZcard
  have hZsq : ∀ z ∈ Z, z * z = 1 := fun z hz => by
    rw [← pow_two]; exact sq_eq_one_of_card_two Z hZcard z hz
  let ζ : K → ZMod 2 := fun z => if z = 1 then 0 else 1
  have hζ : ∀ z ∈ Z, ∀ z' ∈ Z, ζ (z * z') = ζ z + ζ z' := by
    intro z hz z' hz'
    by_cases h1 : z = 1
    · subst h1; simp [ζ]
    by_cases h2 : z' = 1
    · subst h2; simp [ζ]
    have hzz : z = z0 := (hZe z hz).resolve_left h1
    have hzz' : z' = z0 := (hZe z' hz').resolve_left h2
    have h3 : z * z' = 1 := by rw [hzz, hzz']; exact hZsq z0 hz0Z
    show (if z * z' = 1 then (0 : ZMod 2) else 1) =
      (if z = 1 then (0 : ZMod 2) else 1) + (if z' = 1 then (0 : ZMod 2) else 1)
    simp only [h3, h1, h2, ↓reduceIte]
    decide
  have hζ1 : ζ 1 = 0 := by simp [ζ]
  have : Nonempty K := ⟨1⟩
  let lift : G → K := fun s => Classical.epsilon (fun k => ε k = s)
  have hlift : ∀ s, (∃ k, ε k = s) → ε (lift s) = s := fun s hs => Classical.epsilon_spec hs
  have hliftS : ∀ s ∈ S, ε (lift s) = s := fun s hs => hlift s (hεS s hs)
  have hdiff : ∀ a b : K, ε a = ε b → ∃ z ∈ Z, a = b * z := fun a b h =>
    ⟨b⁻¹ * a, by rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel], by group⟩
  have hcmZ : ∀ x ∈ S, ∀ y ∈ E, cmm (lift x) (lift y) ∈ Z := by
    intro x hx y hy
    rw [← hker, MonoidHom.mem_ker]
    simp only [cmm, map_mul, map_inv, hliftS x hx, hliftS y (hES hy)]
    have := hEz y hy x hx
    calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [this]
      _ = 1 := by group
  refine ⟨fun x y => ζ (cmm (lift x) (lift y)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx x' hx' y hy
    have hxx' : x * x' ∈ S := S.mul_mem hx hx'
    obtain ⟨z, hz, hcz⟩ := hdiff (lift (x * x')) (lift x * lift x')
      (by rw [map_mul, hliftS _ hxx', hliftS _ hx, hliftS _ hx'])
    show ζ (cmm (lift (x * x')) (lift y)) = ζ (cmm (lift x) (lift y)) + ζ (cmm (lift x') (lift y))
    rw [hcz, cmm_central_left (hZc z hz), cmm_mul_left hZc _ _ _ (hcmZ x' hx' y hy),
      hζ _ (hcmZ x' hx' y hy) _ (hcmZ x hx y hy), add_comm]
  ·
    intro x hx y hy y' hy'
    have hyy' : y * y' ∈ E := E.mul_mem hy hy'
    obtain ⟨z, hz, hcz⟩ := hdiff (lift (y * y')) (lift y * lift y')
      (by rw [map_mul, hliftS _ (hES hyy'), hliftS _ (hES hy), hliftS _ (hES hy')])
    show ζ (cmm (lift x) (lift (y * y'))) = ζ (cmm (lift x) (lift y)) + ζ (cmm (lift x) (lift y'))
    rw [hcz, cmm_central_right (hZc z hz), cmm_mul_right hZc _ _ _ (hcmZ x hx y' hy'),
      hζ _ (hcmZ x hx y' hy') _ (hcmZ x hx y hy), add_comm]
  ·
    intro w hw y hy
    have hcomm := hAab (lift w) (lift y) (by rw [hliftS w (hES hw)]; exact hw)
      (by rw [hliftS y (hES hy)]; exact hy)
    show ζ (cmm (lift w) (lift y)) = 0
    have : cmm (lift w) (lift y) = 1 := by
      calc cmm (lift w) (lift y) = (lift y * lift w) * (lift w)⁻¹ * (lift y)⁻¹ := by
            simp only [cmm]; rw [hcomm]
        _ = 1 := by group
    rw [this, hζ1]
  ·
    intro ψ g hψ x hx y hy
    have hψZ : ∀ z ∈ Z, ψ z = z := by
      intro z hz
      have hz1 : ε z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hz
      have hψzZ : ψ z ∈ Z := by
        rw [← hker, MonoidHom.mem_ker, hψ, hz1]; group
      rcases hZe z hz with h | h
      · rw [h]; exact map_one ψ
      · rcases hZe (ψ z) hψzZ with h' | h'
        · have h1 : z = 1 := ψ.injective (by rw [h', map_one])
          exact absurd (h.symm.trans h1) hz01
        · rw [h] at h' ⊢; exact h'
    have ha : ε (ψ (lift x)) = g * x * g⁻¹ := by rw [hψ, hliftS x hx]
    have hb : ε (ψ (lift y)) = g * y * g⁻¹ := by rw [hψ, hliftS y (hES hy)]
    have hlx : ∃ k, ε k = g * x * g⁻¹ := ⟨ψ (lift x), ha⟩
    have hly : ∃ k, ε k = g * y * g⁻¹ := ⟨ψ (lift y), hb⟩
    obtain ⟨z1, hz1, h1⟩ := hdiff (lift (g * x * g⁻¹)) (ψ (lift x)) (by rw [hlift _ hlx, ha])
    obtain ⟨z2, hz2, h2⟩ := hdiff (lift (g * y * g⁻¹)) (ψ (lift y)) (by rw [hlift _ hly, hb])
    show ζ (cmm (lift (g * x * g⁻¹)) (lift (g * y * g⁻¹))) = ζ (cmm (lift x) (lift y))
    rw [h1, h2, cmm_central_left (hZc z1 hz1), cmm_central_right (hZc z2 hz2)]
    have : cmm (ψ (lift x)) (ψ (lift y)) = ψ (cmm (lift x) (lift y)) := by simp [cmm]
    rw [this, hψZ _ (hcmZ x hx y hy)]
  ·
    intro x hx
    have hx2 : x ^ 2 ∈ S := S.pow_mem hx 2
    obtain ⟨z, hz, hcz⟩ := hdiff (lift (x ^ 2)) (lift x ^ 2)
      (by rw [map_pow, hliftS _ hx2, hliftS _ hx])
    show ζ (cmm (lift x) (lift (x ^ 2))) = 0
    rw [hcz, cmm_central_right (hZc z hz)]
    have : cmm (lift x) (lift x ^ 2) = 1 := by simp only [cmm]; group
    rw [this, hζ1]
  ·
    intro y hy hy1
    have hb : ε (lift y) = y := hliftS y (hES hy)
    obtain ⟨p, hpS, hp⟩ := hnd (lift y) (by rw [hb]; exact hy) (by rw [hb]; exact hy1)
    refine ⟨ε p, hpS, ?_⟩
    obtain ⟨z, hz, hcz⟩ := hdiff (lift (ε p)) p (by rw [hliftS _ hpS])
    show ζ (cmm (lift (ε p)) (lift y)) ≠ 0
    rw [hcz, cmm_central_left (hZc z hz)]
    have hne : cmm p (lift y) ≠ 1 := hp
    simp only [ζ, hne, ↓reduceIte]
    decide

section Vanish

variable {G : Type*} [Group G]

@[expose] def pr3 (x : Fin 3 → G) (a : Fin 3 → ZMod 2) : G :=
  x 0 ^ (a 0).val * x 1 ^ (a 1).val * x 2 ^ (a 2).val

@[expose, reducible] def InvMat (M N u : Fin 3 → Fin 3 → ZMod 2) : Prop :=
  ∀ i j, u i j = ∑ k, ∑ l, M k i * N l j * u k l

@[expose, reducible] def CycMat (q : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (u : Fin 3 → Fin 3 → ZMod 2) : Prop :=
  ∀ a : Fin 3 → ZMod 2, ∑ i, ∑ j, a i * q a j * u i j = 0

theorem zmod2_self (a : ZMod 2) (h : a = a + a) : a = 0 := by
  revert a; decide

variable {S E : Subgroup G} {κ : G → G → ZMod 2}

theorem kappa_one_left (h1 : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y)
    {t : G} (ht : t ∈ E) : κ 1 t = 0 := by
  have := h1 1 S.one_mem 1 S.one_mem t ht
  rw [mul_one] at this
  exact zmod2_self _ this

theorem kappa_one_right (h2 : ∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y')
    {s : G} (hs : s ∈ S) : κ s 1 = 0 := by
  have := h2 s hs 1 E.one_mem 1 E.one_mem
  rw [mul_one] at this
  exact zmod2_self _ this

theorem kappa_pow_left (h1 : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y)
    {s : G} (hs : s ∈ S) {t : G} (ht : t ∈ E) (n : ℕ) :
    κ (s ^ n) t = (n : ZMod 2) * κ s t := by
  induction n with
  | zero => simp [kappa_one_left h1 ht]
  | succ n ih =>
    rw [pow_succ, h1 _ (S.pow_mem hs n) _ hs _ ht, ih]
    push_cast; ring

theorem kappa_pow_right (h2 : ∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y')
    {s : G} (hs : s ∈ S) {t : G} (ht : t ∈ E) (n : ℕ) :
    κ s (t ^ n) = (n : ZMod 2) * κ s t := by
  induction n with
  | zero => simp [kappa_one_right h2 hs]
  | succ n ih =>
    rw [pow_succ, h2 _ hs _ (E.pow_mem ht n) _ ht, ih]
    push_cast; ring

theorem pr3_mem {x : Fin 3 → G} {H : Subgroup G} (hx : ∀ i, x i ∈ H) (a : Fin 3 → ZMod 2) :
    pr3 x a ∈ H :=
  H.mul_mem (H.mul_mem (H.pow_mem (hx 0) _) (H.pow_mem (hx 1) _)) (H.pow_mem (hx 2) _)

theorem kappa_expand_left (h1 : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y)
    {x : Fin 3 → G} (hx : ∀ i, x i ∈ S) (a : Fin 3 → ZMod 2) {t : G} (ht : t ∈ E) :
    κ (pr3 x a) t = ∑ i, a i * κ (x i) t := by
  unfold pr3
  rw [h1 _ (S.mul_mem (S.pow_mem (hx 0) _) (S.pow_mem (hx 1) _)) _ (S.pow_mem (hx 2) _) _ ht,
    h1 _ (S.pow_mem (hx 0) _) _ (S.pow_mem (hx 1) _) _ ht, kappa_pow_left h1 (hx 0) ht,
    kappa_pow_left h1 (hx 1) ht, kappa_pow_left h1 (hx 2) ht, Fin.sum_univ_three]
  simp

theorem kappa_expand_right (h2 : ∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y')
    {y : Fin 3 → G} (hy : ∀ j, y j ∈ E) (b : Fin 3 → ZMod 2) {s : G} (hs : s ∈ S) :
    κ s (pr3 y b) = ∑ j, b j * κ s (y j) := by
  unfold pr3
  rw [h2 _ hs _ (E.mul_mem (E.pow_mem (hy 0) _) (E.pow_mem (hy 1) _)) _ (E.pow_mem (hy 2) _),
    h2 _ hs _ (E.pow_mem (hy 0) _) _ (E.pow_mem (hy 1) _), kappa_pow_right h2 hs (hy 0),
    kappa_pow_right h2 hs (hy 1), kappa_pow_right h2 hs (hy 2), Fin.sum_univ_three]
  simp

theorem kappa_expand (hES : E ≤ S)
    (h1 : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y)
    (h2 : ∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y')
    (h3 : ∀ w ∈ E, ∀ y ∈ E, κ w y = 0) {x y : Fin 3 → G} (hx : ∀ i, x i ∈ S)
    (hy : ∀ j, y j ∈ E) (a b : Fin 3 → ZMod 2) {w : G} (hw : w ∈ E) :
    κ (pr3 x a * w) (pr3 y b) = ∑ i, ∑ j, a i * b j * κ (x i) (y j) := by
  have hpy : pr3 y b ∈ E := pr3_mem hy b
  have hpx : pr3 x a ∈ S := pr3_mem hx a
  have e1 : κ (pr3 x a * w) (pr3 y b) = κ (pr3 x a) (pr3 y b) := by
    rw [h1 _ hpx _ (hES hw) _ hpy, h3 w hw _ hpy, add_zero]
  rw [e1, kappa_expand_left h1 hx a hpy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kappa_expand_right h2 hy b (hx i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kappa_vanish (hES : E ≤ S)
    (h1 : ∀ x ∈ S, ∀ x' ∈ S, ∀ y ∈ E, κ (x * x') y = κ x y + κ x' y)
    (h2 : ∀ x ∈ S, ∀ y ∈ E, ∀ y' ∈ E, κ x (y * y') = κ x y + κ x y')
    (h3 : ∀ w ∈ E, ∀ y ∈ E, κ w y = 0) {x y : Fin 3 → G} (hx : ∀ i, x i ∈ S)
    (hy : ∀ j, y j ∈ E)
    (hdecS : ∀ s ∈ S, ∃ a : Fin 3 → ZMod 2, ∃ w ∈ E, s = pr3 x a * w)
    (hdecE : ∀ t ∈ E, ∃ b : Fin 3 → ZMod 2, t = pr3 y b)
    (g₁ g₂ : G)
    (h4₁ : ∀ s ∈ S, ∀ t ∈ E, κ (g₁ * s * g₁⁻¹) (g₁ * t * g₁⁻¹) = κ s t)
    (h4₂ : ∀ s ∈ S, ∀ t ∈ E, κ (g₂ * s * g₂⁻¹) (g₂ * t * g₂⁻¹) = κ s t)
    (h5 : ∀ s ∈ S, κ s (s ^ 2) = 0)
    (M₁ N₁ M₂ N₂ : Fin 3 → Fin 3 → ZMod 2)
    (hM₁ : ∀ i, ∃ w ∈ E, g₁ * x i * g₁⁻¹ = pr3 x (fun k => M₁ k i) * w)
    (hN₁ : ∀ j, g₁ * y j * g₁⁻¹ = pr3 y (fun l => N₁ l j))
    (hM₂ : ∀ i, ∃ w ∈ E, g₂ * x i * g₂⁻¹ = pr3 x (fun k => M₂ k i) * w)
    (hN₂ : ∀ j, g₂ * y j * g₂⁻¹ = pr3 y (fun l => N₂ l j))
    (q : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))
    (hq : ∀ a, pr3 x a ^ 2 = pr3 y (q a))
    (halg : ∀ u : Fin 3 → Fin 3 → ZMod 2, InvMat M₁ N₁ u → InvMat M₂ N₂ u → CycMat q u →
      ∀ i j, u i j = 0) :
    ∀ s ∈ S, ∀ t ∈ E, κ s t = 0 := by
  set u : Fin 3 → Fin 3 → ZMod 2 := fun i j => κ (x i) (y j) with hu
  have hinv : ∀ (g : G) (M N : Fin 3 → Fin 3 → ZMod 2)
      (h4 : ∀ s ∈ S, ∀ t ∈ E, κ (g * s * g⁻¹) (g * t * g⁻¹) = κ s t)
      (hM : ∀ i, ∃ w ∈ E, g * x i * g⁻¹ = pr3 x (fun k => M k i) * w)
      (hN : ∀ j, g * y j * g⁻¹ = pr3 y (fun l => N l j)), InvMat M N u := by
    intro g M N h4 hM hN i j
    obtain ⟨w, hw, hwe⟩ := hM i
    have := h4 (x i) (hx i) (y j) (hy j)
    rw [hwe, hN j, kappa_expand hES h1 h2 h3 hx hy _ _ hw] at this
    exact this.symm
  have hcyc : CycMat q u := by
    intro a
    have hs := h5 (pr3 x a) (pr3_mem hx a)
    rw [hq a] at hs
    have := kappa_expand hES h1 h2 h3 hx hy a (q a) (w := 1) E.one_mem
    rw [mul_one] at this
    rw [this] at hs
    simpa [hu] using hs
  have hzero := halg u (hinv g₁ M₁ N₁ h4₁ hM₁ hN₁) (hinv g₂ M₂ N₂ h4₂ hM₂ hN₂) hcyc
  intro s hs t ht
  obtain ⟨a, w, hw, rfl⟩ := hdecS s hs
  obtain ⟨b, rfl⟩ := hdecE t ht
  rw [kappa_expand hES h1 h2 h3 hx hy a b hw]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have := hzero i j
  simp only [hu] at this
  rw [this, mul_zero]

end Vanish

end CFSG.GH74.KGroups

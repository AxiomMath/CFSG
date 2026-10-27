module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Orb

public section

namespace CFSG.QuasithinUnique.Bridge.ThreeA7Excl

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.B42A57

variable {W : Type} [CommGroup W]

theorem pow_apply_apply (g : MulAut W) (a b : ℕ) (w : W) :
    (g ^ a) ((g ^ b) w) = (g ^ (a + b)) w := by
  rw [← MulAut.mul_apply, ← pow_add]

theorem pow_apply_eq_of_apply_eq {g : MulAut W} {u : W} (h : g u = u) (n : ℕ) :
    (g ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem nrmW_five (x : MulAut W) (t : W) :
    nrmW 5 x t = t * x t * (x ^ 2) t * (x ^ 3) t * (x ^ 4) t := by
  simp [nrmW, Finset.prod_range_succ]

def kerNrm (x : MulAut W) : Subgroup W := (nrmHom 5 x).ker

theorem mem_kerNrm {x : MulAut W} {u : W} : u ∈ kerNrm x ↔ nrmW 5 x u = 1 := by
  rw [kerNrm, MonoidHom.mem_ker, nrmHom_apply]

theorem nrmW_apply_of_comm (p : ℕ) {x g : MulAut W} (h : g * x = x * g) (t : W) :
    nrmW p x (g t) = g (nrmW p x t) := by
  unfold nrmW
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : g * x ^ i = x ^ i * g := ((show Commute g x from h).pow_right i).eq
  have h2 := congrArg (fun m : MulAut W => m t) h1
  simpa only [MulAut.mul_apply] using h2.symm

theorem apply_mem_kerNrm {x g : MulAut W} (h : g * x = x * g) {u : W} (hu : u ∈ kerNrm x) :
    g u ∈ kerNrm x := by
  rw [mem_kerNrm] at hu ⊢
  rw [nrmW_apply_of_comm 5 h, hu, map_one]

theorem nrmW_apply_of_conj {x y : MulAut W} (hx : x ^ 5 = 1) (hyx : y * x * y⁻¹ = x ^ 2)
    (t : W) : nrmW 5 x (y t) = y (nrmW 5 x t) := by
  have hc : ∀ j : ℕ, ∀ w : W, y ((x ^ j) w) = (x ^ (2 * j)) (y w) := by
    intro j w
    have h1 : y * x ^ j * y⁻¹ = x ^ (2 * j) := by rw [← conj_pow, hyx, ← pow_mul]
    have h2 : y * x ^ j = x ^ (2 * j) * y := by
      calc y * x ^ j = (y * x ^ j * y⁻¹) * y := by group
        _ = x ^ (2 * j) * y := by rw [h1]
    have := congrArg (fun m : MulAut W => m w) h2
    simpa only [MulAut.mul_apply] using this
  have e1 : x (y t) = y ((x ^ 3) t) := by
    have h6 : x ^ (2 * 3) = x := by
      rw [show 2 * 3 = 5 + 1 from rfl, pow_add, hx, one_mul, pow_one]
    rw [hc 3 t, h6]
  have e2 : (x ^ 2) (y t) = y (x t) := by
    have := hc 1 t
    simpa using this.symm
  have e3 : (x ^ 3) (y t) = y ((x ^ 4) t) := by
    have h8 : x ^ (2 * 4) = x ^ 3 := by
      rw [show 2 * 4 = 5 + 3 from rfl, pow_add, hx, one_mul]
    rw [hc 4 t, h8]
  have e4 : (x ^ 4) (y t) = y ((x ^ 2) t) := by
    have := hc 2 t
    simpa using this.symm
  rw [nrmW_five, nrmW_five, e1, e2, e3, e4, map_mul, map_mul, map_mul, map_mul]
  ac_rfl

theorem inv_mem_of_finite [Finite W] {K : Subgroup W} {g : MulAut W} (h : ∀ k ∈ K, g k ∈ K) :
    ∀ k ∈ K, g⁻¹ k ∈ K := by
  intro k hk
  have hinj : Function.Injective (fun a : K => (⟨g a, h a a.2⟩ : K)) := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hinj ⟨k, hk⟩
  have h1 : g (a : W) = k := congrArg Subtype.val ha
  have h2 : g⁻¹ k = a := by rw [← h1]; simp
  rw [h2]
  exact a.2

theorem eq_one_of_fixed_mem_kerNrm (hW : ∀ w : W, w * w = 1) {x : MulAut W} {u : W}
    (hu : u ∈ kerNrm x) (hxu : x u = u) : u = 1 := by
  have hfix : ∀ i : ℕ, (x ^ i) u = u := fun i => pow_apply_eq_of_apply_eq hxu i
  have h : nrmW 5 x u = u ^ 5 := by simp [nrmW, hfix]
  rw [mem_kerNrm, h, pow_odd_eq_self_W hW (by decide)] at hu
  exact hu

theorem card_kerNrm_modEq [Finite W] (hW : ∀ w : W, w * w = 1) {x : MulAut W}
    (hx : x ^ 5 = 1) : Nat.card (kerNrm x) ≡ 1 [MOD 5] := by
  have hrange : (nrmHom 5 x).range = fixSub x := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact apply_nrmW 5 hx v
    · intro hw
      refine ⟨w, ?_⟩
      have hfix : ∀ i : ℕ, (x ^ i) w = w := fun i => pow_apply_eq_of_apply_eq hw i
      rw [nrmHom_apply]
      have h : nrmW 5 x w = w ^ 5 := by simp [nrmW, hfix]
      rw [h, pow_odd_eq_self_W hW (by decide)]
  have hcard := Subgroup.card_ker_mul_card_range (nrmHom 5 x)
  rw [hrange] at hcard
  have hmod := card_modEq_fixed x hx
  obtain ⟨k, j, -, hj, -⟩ := card_fix_pow hW x
  have hcop : Nat.gcd 5 (Nat.card (fixSub x)) = 1 := by
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have h1 : Nat.card (kerNrm x) * Nat.card (fixSub x) ≡ 1 * Nat.card (fixSub x) [MOD 5] := by
    rw [one_mul]
    have h2 : Nat.card (kerNrm x) * Nat.card (fixSub x) = Nat.card W := hcard
    rw [h2]
    exact hmod
  exact Nat.ModEq.cancel_right_of_coprime hcop h1

def sOp (x : MulAut W) (u : W) : W := x u * (x ^ 4) u

theorem sOp_mul (x : MulAut W) (a b : W) : sOp x (a * b) = sOp x a * sOp x b := by
  simp only [sOp, map_mul]
  ac_rfl

theorem sOp_one (x : MulAut W) : sOp x 1 = 1 := by simp [sOp]

theorem sOp_mem {x : MulAut W} {u : W} (hu : u ∈ kerNrm x) : sOp x u ∈ kerNrm x :=
  Subgroup.mul_mem _ (apply_mem_kerNrm rfl hu)
    (apply_mem_kerNrm ((Commute.refl x).pow_left 4).eq hu)

theorem sOp_apply_of_comm {x g : MulAut W} (h : g * x = x * g) (u : W) :
    sOp x (g u) = g (sOp x u) := by
  have h1 : g * x ^ 4 = x ^ 4 * g := ((show Commute g x from h).pow_right 4).eq
  have e1 : x (g u) = g (x u) := by
    have := congrArg (fun m : MulAut W => m u) h
    simpa only [MulAut.mul_apply] using this.symm
  have e2 : (x ^ 4) (g u) = g ((x ^ 4) u) := by
    have := congrArg (fun m : MulAut W => m u) h1
    simpa only [MulAut.mul_apply] using this.symm
  rw [sOp, e1, e2, sOp, map_mul]

theorem sOp_sOp (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x ^ 5 = 1) (u : W) :
    sOp x (sOp x u) = (x ^ 2) u * (x ^ 3) u := by
  have h5 : ∀ w : W, (x ^ 5) w = w := fun w => by rw [hx]; rfl
  have a1 : x (x u) = (x ^ 2) u := by rw [← MulAut.mul_apply, ← pow_two]
  have a2 : x ((x ^ 4) u) = u := by
    rw [← MulAut.mul_apply, ← pow_succ']
    exact h5 u
  have a3 : (x ^ 4) (x u) = u := by
    rw [← MulAut.mul_apply, ← pow_succ]
    exact h5 u
  have a4 : (x ^ 4) ((x ^ 4) u) = (x ^ 3) u := by
    rw [pow_apply_apply]
    have : x ^ (4 + 4) = x ^ 3 := by
      rw [show 4 + 4 = 5 + 3 from rfl, pow_add, hx, one_mul]
    rw [this]
  rw [sOp, sOp, map_mul, map_mul, a1, a2, a3, a4]
  calc (x ^ 2) u * u * (u * (x ^ 3) u) = (x ^ 2) u * (x ^ 3) u * (u * u) := by ac_rfl
    _ = (x ^ 2) u * (x ^ 3) u := by rw [hW u, mul_one]

theorem sOp_rel (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x ^ 5 = 1) {u : W}
    (hu : u ∈ kerNrm x) : sOp x (sOp x u) * sOp x u * u = 1 := by
  rw [sOp_sOp hW hx, sOp]
  have h := mem_kerNrm.1 hu
  rw [nrmW_five] at h
  calc (x ^ 2) u * (x ^ 3) u * (x u * (x ^ 4) u) * u
      = u * x u * (x ^ 2) u * (x ^ 3) u * (x ^ 4) u := by ac_rfl
    _ = 1 := h

theorem sOp_cube (hW : ∀ w : W, w * w = 1) {x : MulAut W} (hx : x ^ 5 = 1) {u : W}
    (hu : u ∈ kerNrm x) : sOp x (sOp x (sOp x u)) = u := by
  have hrel := sOp_rel hW hx hu
  have h2 : sOp x (sOp x u) = sOp x u * u := by
    have h3 : sOp x (sOp x u) * (sOp x u * u) = 1 := by rw [← mul_assoc]; exact hrel
    have h4 : (sOp x u * u) * (sOp x u * u) = 1 := by
      calc (sOp x u * u) * (sOp x u * u) = (sOp x u * sOp x u) * (u * u) := by ac_rfl
        _ = 1 := by rw [hW, hW, mul_one]
    exact mul_right_cancel (h3.trans h4.symm)
  rw [h2, sOp_mul, h2]
  calc (sOp x u * u) * sOp x u = u * (sOp x u * sOp x u) := by ac_rfl
    _ = u := by rw [hW, mul_one]

theorem sOp_conj (hW : ∀ w : W, w * w = 1) {x y : MulAut W} (hx : x ^ 5 = 1)
    (hyx : y * x * y⁻¹ = x ^ 2) (u : W) : y (sOp x (y⁻¹ u)) = sOp x (sOp x u) := by
  have h1 : y (x (y⁻¹ u)) = (x ^ 2) u := by
    have := congrArg (fun m : MulAut W => m u) hyx
    simpa only [MulAut.mul_apply] using this
  have h2 : y ((x ^ 4) (y⁻¹ u)) = (x ^ 3) u := by
    have h4 : y * x ^ 4 * y⁻¹ = x ^ 3 := by
      rw [← conj_pow, hyx, ← pow_mul, show 2 * 4 = 5 + 3 from rfl, pow_add, hx, one_mul]
    have := congrArg (fun m : MulAut W => m u) h4
    simpa only [MulAut.mul_apply] using this
  rw [sOp_sOp hW hx, sOp, map_mul, h1, h2]

theorem mul_pow_pow {x z : MulAut W} (h : z * x = x * z) (m n m' n' : ℕ) :
    (x ^ m * z ^ n) * (x ^ m' * z ^ n') = x ^ (m + m') * z ^ (n + n') := by
  have hc : z ^ n * x ^ m' = x ^ m' * z ^ n := ((show Commute z x from h).pow_pow n m').eq
  calc (x ^ m * z ^ n) * (x ^ m' * z ^ n') = x ^ m * (z ^ n * x ^ m') * z ^ n' := by
        simp only [mul_assoc]
    _ = x ^ m * (x ^ m' * z ^ n) * z ^ n' := by rw [hc]
    _ = x ^ (m + m') * z ^ (n + n') := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem fixed_lemma (hW : ∀ w : W, w * w = 1) {x z : MulAut W} (hx5 : x ^ 5 = 1)
    (hz3 : z ^ 3 = 1) (hzx : z * x = x * z) (hzf : ∀ w : W, z w = w → w = 1) {u : W}
    (hu : u ∈ kerNrm x) (c d : ℕ) (h : (x ^ c * z ^ d) u = u) : u = 1 ∨ (5 ∣ c ∧ 3 ∣ d) := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc : Commute (x ^ c) (z ^ d) := ((show Commute z x from hzx).pow_pow d c).symm
  have hpow : (x ^ c * z ^ d) ^ 5 = z ^ (5 * d) := by
    rw [hc.mul_pow, ← pow_mul, mul_comm c 5, pow_mul, hx5, one_pow, one_mul, ← pow_mul,
      mul_comm d 5]
  have hfix5 : (z ^ (5 * d)) u = u := by
    rw [← hpow]
    exact pow_apply_eq_of_apply_eq h 5
  by_cases hd : 3 ∣ d
  · obtain ⟨k, rfl⟩ := hd
    have hz1 : z ^ (3 * k) = 1 := by rw [pow_mul, hz3, one_pow]
    rw [hz1, mul_one] at h
    by_cases hc5 : 5 ∣ c
    · exact Or.inr ⟨hc5, ⟨k, rfl⟩⟩
    · obtain ⟨n, hn⟩ := exists_pow_pow_eq_self_W hx5 hc5
      have hxu : x u = u := by
        have := pow_apply_eq_of_apply_eq h n
        rwa [hn] at this
      exact Or.inl (eq_one_of_fixed_mem_kerNrm hW hu hxu)
  · have hd' : ¬ 3 ∣ 5 * d := by
      intro hdvd
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).1 hdvd with h5' | h5'
      · norm_num at h5'
      · exact hd h5'
    obtain ⟨n, hn⟩ := exists_pow_pow_eq_self_W hz3 hd'
    have hzu : z u = u := by
      have := pow_apply_eq_of_apply_eq hfix5 n
      rwa [hn] at this
    exact Or.inl (hzf u hzu)

theorem surj_of_inj_aux {G : Type*} [Group G] [Finite G] {α : Type*} [Finite α] (f : α → G)
    (hf : Function.Injective f) (hne : ∀ p, f p ≠ 1) (hcard : Nat.card G = Nat.card α + 1) :
    ∀ g : G, g ≠ 1 → ∃ p, f p = g := by
  classical
  intro g hg1
  by_contra hcon
  push Not at hcon
  have : Fintype G := Fintype.ofFinite G
  have : Fintype α := Fintype.ofFinite α
  set s : Finset G := Finset.univ.image f with hs
  have hscard : s.card = Nat.card α := by
    rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Nat.card_eq_fintype_card]
  have hgs : g ∉ s := by
    intro h
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
    exact hcon p hp
  have h1s : (1 : G) ∉ insert g s := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hg1 h.symm
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
      exact hne p hp
  have hcard' : (insert 1 (insert g s)).card = Nat.card α + 2 := by
    rw [Finset.card_insert_of_notMem h1s, Finset.card_insert_of_notMem hgs, hscard]
  have hle := Finset.card_le_univ (insert 1 (insert g s))
  rw [Nat.card_eq_fintype_card] at hcard
  omega

theorem card_gt_of_fusion [Finite W] (hW : ∀ w : W, w * w = 1) {x y z : MulAut W}
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hyx : y * x * y⁻¹ = x ^ 2) (hzx : z * x = x * z)
    (hzy : z * y = y * z) (hz3 : z ^ 3 = 1) (hzf : ∀ w : W, z w = w → w = 1) :
    2 ^ 6 < Nat.card W := by
  by_contra hle
  push Not at hle
  obtain ⟨v, hv⟩ : ∃ v : W, x v ≠ v := by
    by_contra h
    push Not at h
    exact hx1 (MulEquiv.ext h)
  set K := kerNrm x with hK
  have hv0K : x v * v⁻¹ ∈ K := mem_kerNrm.2 (nrmW_comm_image 5 hx5 v)
  have hv01 : x v * v⁻¹ ≠ 1 := fun h => hv (mul_inv_eq_one.1 h)
  generalize x v * v⁻¹ = v0 at hv0K hv01
  have hKT : ∀ a b : ℕ, ∀ u ∈ K, (x ^ a * z ^ b) u ∈ K := by
    intro a b u hu
    refine apply_mem_kerNrm ?_ hu
    exact (Commute.mul_left ((Commute.refl x).pow_left a)
      ((show Commute z x from hzx).pow_left b)).eq
  have hKy : ∀ u ∈ K, y u ∈ K := by
    intro u hu
    rw [hK, mem_kerNrm] at hu ⊢
    rw [nrmW_apply_of_conj hx5 hyx, hu, map_one]
  have hKyinv : ∀ u ∈ K, y⁻¹ u ∈ K := inv_mem_of_finite hKy
  have hKcard : Nat.card K = 16 := by
    have hmod := card_kerNrm_modEq hW hx5
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 ((isPGroup_two hW).to_subgroup K)
    have hle' : Nat.card K ≤ Nat.card W := Subgroup.card_le_card_group K
    have hK1 : Nat.card K ≠ 1 := by
      intro h
      have hbot := Subgroup.eq_bot_of_card_eq K h
      rw [hbot, Subgroup.mem_bot] at hv0K
      exact hv01 hv0K
    rw [hn] at hmod hle' hK1 ⊢
    have hn7 : n < 7 := by
      by_contra hcon
      push Not at hcon
      have : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    interval_cases n <;> simp_all [Nat.ModEq]
  let f : Fin 5 × Fin 3 → K := fun p => ⟨(x ^ (p.1 : ℕ) * z ^ (p.2 : ℕ)) v0, hKT _ _ v0 hv0K⟩
  have hf_ne : ∀ p, f p ≠ 1 := by
    intro p h
    apply hv01
    have h1 : (x ^ (p.1 : ℕ) * z ^ (p.2 : ℕ)) v0 = 1 := congrArg Subtype.val h
    exact (MulEquiv.map_eq_one_iff _).1 h1
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have hab' : (x ^ a * z ^ b) v0 = (x ^ a' * z ^ b') v0 := congrArg Subtype.val hab
    have hDA' : (x ^ (5 - a') * z ^ (3 - b')) * (x ^ a' * z ^ b') = 1 := by
      rw [mul_pow_pow hzx, show 5 - a' + a' = 5 by omega, show 3 - b' + b' = 3 by omega, hx5,
        hz3, mul_one]
    have hDA : (x ^ (5 - a') * z ^ (3 - b')) * (x ^ a * z ^ b) =
        x ^ (5 - a' + a) * z ^ (3 - b' + b) := mul_pow_pow hzx _ _ _ _
    have hfix : (x ^ (5 - a' + a) * z ^ (3 - b' + b)) v0 = v0 := by
      rw [← hDA, MulAut.mul_apply, hab', ← MulAut.mul_apply, hDA']
      rfl
    rcases fixed_lemma hW hx5 hz3 hzx hzf hv0K _ _ hfix with h | ⟨h5, h3⟩
    · exact absurd h hv01
    · have e1 : a = a' := by omega
      have e2 : b = b' := by omega
      subst e1 e2
      rfl
  have hcard' : Nat.card K = Nat.card (Fin 5 × Fin 3) + 1 := by
    rw [hKcard]
    simp [Nat.card_eq_fintype_card]
  have hreg : ∀ u ∈ K, u ≠ 1 → ∃ a < 5, ∃ b < 3, (x ^ a * z ^ b) v0 = u := by
    intro u hu hu1
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hp⟩ :=
      surj_of_inj_aux f hf_inj hf_ne hcard' ⟨u, hu⟩ (fun h => hu1 (congrArg Subtype.val h))
    exact ⟨a, ha, b, hb, congrArg Subtype.val hp⟩
  have hSv0K : sOp x v0 ∈ K := sOp_mem hv0K
  have hSv01 : sOp x v0 ≠ 1 := by
    intro h
    have := sOp_rel hW hx5 hv0K
    rw [h, sOp_one, one_mul, one_mul] at this
    exact hv01 this
  obtain ⟨a, ha, b, hb, hab⟩ := hreg _ hSv0K hSv01
  have hcomm : ∀ i j : ℕ, (x ^ i * z ^ j) * x = x * (x ^ i * z ^ j) := fun i j =>
    (Commute.mul_left ((Commute.refl x).pow_left i) ((show Commute z x from hzx).pow_left j)).eq
  have hST : ∀ u ∈ K, sOp x u = (x ^ a * z ^ b) u := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1, sOp_one, map_one]
    · obtain ⟨i, hi, j, hj, rfl⟩ := hreg u hu hu1
      rw [sOp_apply_of_comm (hcomm i j), ← hab, ← MulAut.mul_apply, ← MulAut.mul_apply,
        mul_pow_pow hzx, mul_pow_pow hzx, add_comm i a, add_comm j b]
  have hconj : ∀ u ∈ K, u = (z ^ b) u := by
    intro u hu
    have hu' : y⁻¹ u ∈ K := hKyinv u hu
    have h2 : y (sOp x (y⁻¹ u)) = y ((x ^ a * z ^ b) (y⁻¹ u)) := by rw [hST _ hu']
    rw [sOp_conj hW hx5 hyx] at h2
    have hya : y * x ^ a * y⁻¹ = x ^ (2 * a) := by rw [← conj_pow, hyx, ← pow_mul]
    have hyb : y * z ^ b * y⁻¹ = z ^ b := by
      have : y * z ^ b = z ^ b * y := ((show Commute y z from hzy.symm).pow_right b).eq
      rw [this, mul_inv_cancel_right]
    have hyT : y * (x ^ a * z ^ b) * y⁻¹ = x ^ (2 * a) * z ^ b := by
      calc y * (x ^ a * z ^ b) * y⁻¹ = (y * x ^ a * y⁻¹) * (y * z ^ b * y⁻¹) := by group
        _ = x ^ (2 * a) * z ^ b := by rw [hya, hyb]
    have h3 : y ((x ^ a * z ^ b) (y⁻¹ u)) = (x ^ (2 * a) * z ^ b) u := by
      have := congrArg (fun m : MulAut W => m u) hyT
      simpa only [MulAut.mul_apply] using this
    have h4 : sOp x (sOp x u) = (x ^ (2 * a) * z ^ (2 * b)) u := by
      rw [hST u hu, hST _ (hKT a b u hu), ← MulAut.mul_apply, mul_pow_pow hzx, ← two_mul,
        ← two_mul]
    rw [h3] at h2
    have h5 : (x ^ (2 * a) * z ^ b) u = (x ^ (2 * a) * z ^ (2 * b)) u := h2.symm.trans h4
    have h6 : (z ^ b) u = (z ^ (2 * b)) u := by
      refine (x ^ (2 * a)).injective ?_
      simpa only [MulAut.mul_apply] using h5
    have h7 : (z ^ (2 * b)) u = (z ^ b) ((z ^ b) u) := by rw [pow_apply_apply, two_mul]
    exact (z ^ b).injective (h6.trans h7)
  have hb0 : b = 0 := by
    have h := hconj v0 hv0K
    interval_cases b
    · rfl
    · exfalso
      apply hv01
      apply hzf
      simpa using h.symm
    · exfalso
      apply hv01
      apply hzf
      have h2 : (z ^ 2) v0 = v0 := h.symm
      calc z v0 = z ((z ^ 2) v0) := by rw [h2]
        _ = (z ^ 3) v0 := by rw [← MulAut.mul_apply, ← pow_succ']
        _ = v0 := by rw [hz3]; rfl
  subst hb0
  have hST' : ∀ u ∈ K, sOp x u = (x ^ a) u := fun u hu => by simpa using hST u hu
  have hcube : ∀ u ∈ K, (x ^ (a + a + a)) u = u := by
    intro u hu
    have hu1 : (x ^ a) u ∈ K := by simpa using hKT a 0 u hu
    have hu2 : (x ^ a) ((x ^ a) u) ∈ K := by simpa using hKT a 0 _ hu1
    have h1 : sOp x (sOp x (sOp x u)) = (x ^ a) ((x ^ a) ((x ^ a) u)) := by
      rw [hST' u hu, hST' _ hu1, hST' _ hu2]
    rw [sOp_cube hW hx5 hu, pow_apply_apply, pow_apply_apply] at h1
    exact h1.symm
  have ha0 : a = 0 := by
    by_contra ha0
    have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hnd : ¬ 5 ∣ a + a + a := by omega
    obtain ⟨n, hn⟩ := exists_pow_pow_eq_self_W hx5 hnd
    have hxv : x v0 = v0 := by
      have := pow_apply_eq_of_apply_eq (hcube v0 hv0K) n
      rwa [hn] at this
    exact hv01 (eq_one_of_fixed_mem_kerNrm hW hv0K hxv)
  subst ha0
  have h1 : sOp x v0 = v0 := by simpa using hST' v0 hv0K
  have h2 := sOp_rel hW hx5 hv0K
  rw [h1, h1, hW v0, one_mul] at h2
  exact hv01 h2

end CFSG.QuasithinUnique.Bridge.ThreeA7Excl

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Equiv Equiv.Perm Subgroup

theorem a8_pair2 {G : Type*} [Group G] (S : Set G) (hinv : ∀ s ∈ S, s * s = 1)
    (hc : ∀ s ∈ S, ∀ u ∈ S, s * u = u * s) : IsPGroup 2 (closure S) := by
  have h1 : ∀ x ∈ closure S, ∀ s ∈ S, x * s = s * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact fun s hs => hc x hx s hs
    | one => exact fun s _ => by simp
    | mul x y _ _ hx hy =>
      exact fun s hs => by rw [mul_assoc, hy s hs, ← mul_assoc, hx s hs, mul_assoc]
    | inv x _ hx => exact fun s hs => (Commute.inv_left (hx s hs : Commute x s))
  have h2 : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h1 x hx y hy
    | one => simp
    | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]
    | inv y _ hy => exact (Commute.inv_right (hy : Commute x y))
  have h3 : ∀ x ∈ closure S, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hinv x hx
    | one => simp
    | mul x y hx' hy hx hy' =>
      have hxy : y * x = x * y := (h2 x hx' y hy).symm
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx, hy', mul_one]
    | inv x hx' hx => rw [← mul_inv_rev, hx, inv_one]
  exact fun g => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (h3 g.1 g.2)⟩

section Klein

variable {a b c d : Fin 8}

theorem a8_app_inv (n : Perm (Fin 8)) (x : Fin 8) : n (n⁻¹ x) = x := by simp [Perm.inv_def]

theorem a8_inv_app (n : Perm (Fin 8)) (x : Fin 8) : n⁻¹ (n x) = x := by simp [Perm.inv_def]

theorem a8_kl_AB (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : swap a b * swap c d * (swap a c * swap b d) = swap a d * swap b c := by
  refine Equiv.ext fun i => ?_
  by_cases h1 : i = a <;> by_cases h2 : i = b <;> by_cases h3 : i = c <;>
    by_cases h4 : i = d <;> simp_all [Perm.mul_apply, swap_apply_def, hab.symm, hac.symm,
      had.symm, hbc.symm, hbd.symm, hcd.symm]

theorem a8_kl_sq (x y z u : Fin 8) (hxy : x ≠ y) (hzu : z ≠ u) (hxz : x ≠ z) (hxu : x ≠ u)
    (hyz : y ≠ z) (hyu : y ≠ u) : swap x y * swap z u * (swap x y * swap z u) = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases h1 : i = x <;> by_cases h2 : i = y <;> by_cases h3 : i = z <;>
    by_cases h4 : i = u <;> simp_all [Perm.mul_apply, swap_apply_def, hxy.symm, hxz.symm,
      hxu.symm, hyz.symm, hyu.symm, hzu.symm]

theorem a8_klein_classify (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (σ : Perm (Fin 8)) (hσ : σ * σ = 1)
    (hout : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → σ x = x)
    (hfp : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → σ x ≠ x) :
    σ = swap a b * swap c d ∨ σ = swap a c * swap b d ∨ σ = swap a d * swap b c := by
  have hinv : ∀ x, σ (σ x) = x := fun x => by simpa using congrArg (fun π : Perm (Fin 8) => π x) hσ
  have hF : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → σ x = a ∨ σ x = b ∨ σ x = c ∨ σ x = d := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    have h2 := hinv x
    rw [hout (σ x) hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2] at h2
    exact hfp x hx h2
  rcases hF a (by simp) with h | h | h | h
  · exact absurd h (hfp a (by simp))
  · have hb : σ b = a := by have := hinv a; rwa [h] at this
    have hc : σ c = d := by
      rcases hF c (by simp) with h1 | h1 | h1 | h1
      · have e := hinv c; rw [h1, h] at e; exact absurd e hbc
      · have e := hinv c; rw [h1, hb] at e; exact absurd e hac
      · exact absurd h1 (hfp c (by simp))
      · exact h1
    have hd : σ d = c := by have := hinv c; rwa [hc] at this
    refine Or.inl (Equiv.ext fun x => ?_)
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;>
      by_cases h4 : x = d <;> simp_all [Perm.mul_apply, swap_apply_def, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
  · have hc : σ c = a := by have := hinv a; rwa [h] at this
    have hb : σ b = d := by
      rcases hF b (by simp) with h1 | h1 | h1 | h1
      · have e := hinv b; rw [h1, h] at e; exact absurd e.symm hbc
      · exact absurd h1 (hfp b (by simp))
      · have e := hinv b; rw [h1, hc] at e; exact absurd e hab
      · exact h1
    have hd : σ d = b := by have := hinv b; rwa [hb] at this
    refine Or.inr (Or.inl (Equiv.ext fun x => ?_))
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;>
      by_cases h4 : x = d <;> simp_all [Perm.mul_apply, swap_apply_def, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]
  · have hd : σ d = a := by have := hinv a; rwa [h] at this
    have hb : σ b = c := by
      rcases hF b (by simp) with h1 | h1 | h1 | h1
      · have e := hinv b; rw [h1, h] at e; exact absurd e.symm hbd
      · exact absurd h1 (hfp b (by simp))
      · exact h1
      · have e := hinv b; rw [h1, hd] at e; exact absurd e hab
    have hc : σ c = b := by have := hinv b; rwa [hb] at this
    refine Or.inr (Or.inr (Equiv.ext fun x => ?_))
    by_cases h1 : x = a <;> by_cases h2 : x = b <;> by_cases h3 : x = c <;>
      by_cases h4 : x = d <;> simp_all [Perm.mul_apply, swap_apply_def, hab.symm, hac.symm,
        had.symm, hbc.symm, hbd.symm, hcd.symm]

theorem a8_dt_fix {x y z u : Fin 8} (hxy : x ≠ y) (hzu : z ≠ u) (hxz : x ≠ z) (hxu : x ≠ u)
    (hyz : y ≠ z) (hyu : y ≠ u) (w : Fin 8) (hw : w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ w ≠ u) :
    (swap x y * swap z u) w = w := by
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]

theorem a8_dt_fp {x y z u : Fin 8} (hxy : x ≠ y) (hzu : z ≠ u) (hxz : x ≠ z) (hxu : x ≠ u)
    (hyz : y ≠ z) (hyu : y ≠ u) (w : Fin 8) (hw : w = x ∨ w = y ∨ w = z ∨ w = u) :
    (swap x y * swap z u) w ≠ w := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [Perm.mul_apply, swap_apply_def, hxy, hxz, hxu, hyz, hyu, hzu, hxy.symm, hxz.symm,
      hxu.symm, hyz.symm, hyu.symm, hzu.symm]

@[expose] def a8_kW (a b c d : Fin 8) : Subgroup (Perm (Fin 8)) :=
  closure {swap a b * swap c d, swap a c * swap b d}

theorem a8_kW_isPGroup (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : IsPGroup 2 (a8_kW a b c d) := by
  have hA := a8_kl_sq a b c d hab hcd hac had hbc hbd
  have hB := a8_kl_sq a c b d hac hbd hab had hbc.symm hcd
  have hC := a8_kl_sq a d b c had hbc hab hac hbd.symm hcd.symm
  have hAB := a8_kl_AB hab hac had hbc hbd hcd
  refine a8_pair2 _ ?_ ?_
  · rintro s (rfl | rfl)
    · exact hA
    · exact hB
  · have hAi := inv_eq_of_mul_eq_one_right hA
    have hBi := inv_eq_of_mul_eq_one_right hB
    have hCi := inv_eq_of_mul_eq_one_right hC
    have hBA : swap a c * swap b d * (swap a b * swap c d) =
        (swap a b * swap c d * (swap a c * swap b d))⁻¹ := by rw [mul_inv_rev, hAi, hBi]
    have hBA' : swap a c * swap b d * (swap a b * swap c d) = swap a d * swap b c := by
      rw [hBA, hAB, hCi]
    rintro s (rfl | rfl) u (rfl | rfl)
    · rfl
    · rw [hAB, hBA']
    · rw [hBA', hAB]
    · rfl

theorem a8_kW_le_alt (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : a8_kW a b c d ≤ alternatingGroup (Fin 8) := by
  refine (closure_le _).2 ?_
  rintro s (rfl | rfl)
  · rw [SetLike.mem_coe, mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hcd]; norm_num
  · rw [SetLike.mem_coe, mem_alternatingGroup, Perm.sign_mul, sign_swap hac, sign_swap hbd]; norm_num

theorem a8_kW_comm (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (r : Perm (Fin 8)) (hr : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d → r x = x) :
    ∀ w ∈ a8_kW a b c d, r * w = w * r := by
  have hA : Commute r (swap a b * swap c d) := Disjoint.commute (disjoint_iff_eq_or_eq.2 fun x => by
    by_cases hx : x = a ∨ x = b ∨ x = c ∨ x = d
    · exact Or.inl (hr x hx)
    · push_neg at hx
      exact Or.inr (a8_dt_fix hab hcd hac had hbc hbd x ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩))
  have hB : Commute r (swap a c * swap b d) := Disjoint.commute (disjoint_iff_eq_or_eq.2 fun x => by
    by_cases hx : x = a ∨ x = b ∨ x = c ∨ x = d
    · exact Or.inl (hr x hx)
    · push_neg at hx
      exact Or.inr (a8_dt_fix hac hbd hab had hbc.symm hcd x ⟨hx.1, hx.2.2.1, hx.2.1, hx.2.2.2⟩))
  have hcen : a8_kW a b c d ≤ Subgroup.centralizer {r} := by
    refine (closure_le _).2 ?_
    rintro s (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hA.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 hB.symm.eq
  intro w hw
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcen hw)).symm

theorem a8_kW_conjA (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (n : Perm (Fin 8))
    (hn : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) ↔ (n x = a ∨ n x = b ∨ n x = c ∨ n x = d)) :
    n * (swap a b * swap c d) * n⁻¹ ∈ a8_kW a b c d := by
  have hA := a8_kl_sq a b c d hab hcd hac had hbc hbd
  have hmA : swap a b * swap c d ∈ a8_kW a b c d := subset_closure (by simp)
  have hmB : swap a c * swap b d ∈ a8_kW a b c d := subset_closure (by simp)
  have hmC : swap a d * swap b c ∈ a8_kW a b c d := by
    rw [← a8_kl_AB hab hac had hbc hbd hcd]; exact mul_mem hmA hmB
  have hσ : (n * (swap a b * swap c d) * n⁻¹) * (n * (swap a b * swap c d) * n⁻¹) = 1 := by
    calc _ = n * (swap a b * swap c d * (swap a b * swap c d)) * n⁻¹ := by group
      _ = 1 := by rw [hA]; group
  have hout : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      (n * (swap a b * swap c d) * n⁻¹) x = x := by
    intro x h1 h2 h3 h4
    have hy : ¬(n⁻¹ x = a ∨ n⁻¹ x = b ∨ n⁻¹ x = c ∨ n⁻¹ x = d) := fun hF => by
      have := (hn (n⁻¹ x)).1 hF
      rw [a8_app_inv] at this
      tauto
    have hA' := a8_dt_fix hab hcd hac had hbc hbd (n⁻¹ x) ⟨by tauto, by tauto, by tauto, by tauto⟩
    show n ((swap a b * swap c d) (n⁻¹ x)) = x
    rw [hA', a8_app_inv]
  have hfp : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → (n * (swap a b * swap c d) * n⁻¹) x ≠ x := by
    intro x hx h
    have hmem : n⁻¹ x = a ∨ n⁻¹ x = b ∨ n⁻¹ x = c ∨ n⁻¹ x = d :=
      (hn (n⁻¹ x)).2 (by rw [a8_app_inv]; exact hx)
    have h' : n ((swap a b * swap c d) (n⁻¹ x)) = x := h
    have h2 : n⁻¹ (n ((swap a b * swap c d) (n⁻¹ x))) = n⁻¹ x := by rw [h']
    rw [a8_inv_app] at h2
    exact a8_dt_fp hab hcd hac had hbc hbd (n⁻¹ x) hmem h2
  rcases a8_klein_classify hab hac had hbc hbd hcd _ hσ hout hfp with h | h | h <;>
    rw [h] <;> assumption

theorem a8_kW_normal (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (n : Perm (Fin 8))
    (hn : ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) ↔ (n x = a ∨ n x = b ∨ n x = c ∨ n x = d)) :
    ∀ w ∈ a8_kW a b c d, n * w * n⁻¹ ∈ a8_kW a b c d := by
  have hBeq : a8_kW a b c d = a8_kW a c b d := by unfold a8_kW; rw [Set.pair_comm]
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | rfl
    · exact a8_kW_conjA hab hac had hbc hbd hcd n hn
    · rw [hBeq]
      exact a8_kW_conjA hac hab had hbc.symm hcd hbd n (fun x => by have := hn x; tauto)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact inv_mem hx

end Klein

theorem a8_card_four_dvd {G : Type*} [Group G] [Finite G] (H : Subgroup G) (hH : IsPGroup 2 H)
    (x y z : G) (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    4 ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hH
  have h3 : 3 ≤ Nat.card H := by
    have := Nat.card_le_card_of_injective (fun i : Fin 3 => (![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩] i : H))
      (by
        intro i j hij
        have h := congrArg Subtype.val hij
        fin_cases i <;> fin_cases j <;> simp_all)
    simpa using this
  rw [hn] at h3 ⊢
  have hn2 : 2 ≤ n := by
    by_contra hc
    push_neg at hc
    interval_cases n <;> norm_num at h3
  exact (pow_dvd_pow 2 hn2 : 2 ^ 2 ∣ 2 ^ n)

theorem a8_sign_involution (σ : Perm (Fin 8)) (hσ : σ ^ 2 = 1) :
    sign σ = (-1 : ℤˣ) ^ (σ.support.card / 2) := by
  have hall : ∀ c ∈ σ.cycleType, c = 2 := fun c hc => by
    have h1 : c ∣ 2 := (dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one hσ)
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) (two_le_of_mem_cycleType hc)
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 2 :=
    ⟨σ.cycleType.card, Multiset.eq_replicate.2 ⟨rfl, hall⟩⟩
  have hs := σ.sum_cycleType
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hs
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, ← hs,
    Nat.mul_div_cancel k (by norm_num : (0:ℕ) < 2), pow_add, pow_mul]
  simp

theorem a8_card_alt_inf (C : Subgroup (Perm (Fin 8))) (x : Perm (Fin 8)) (hx : x ∈ C)
    (hxo : sign x = -1) : Nat.card ↥(C ⊓ alternatingGroup (Fin 8)) * 2 = Nat.card C := by
  let f : C →* ℤˣ := (sign : Perm (Fin 8) →* ℤˣ).comp C.subtype
  have hker : f.ker.map C.subtype = C ⊓ alternatingGroup (Fin 8) := by
    ext y
    simp [f, MonoidHom.mem_ker, Equiv.Perm.mem_alternatingGroup, and_comm]
  have hc1 : Nat.card ↥(f.ker.map C.subtype) = Nat.card f.ker :=
    Subgroup.card_map_of_injective Subtype.val_injective
  have hrange : Nat.card f.range = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, ⟨⟨x, hx⟩, by simp [f, hxo]⟩⟩, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      norm_num at this
    · apply Set.eq_univ_of_forall
      rintro ⟨z, hz⟩
      rcases Int.units_eq_one_or z with rfl | rfl
      · simp
      · simp
  have hidx : f.ker.index = 2 := by rw [index_ker, hrange]
  have := card_mul_index f.ker
  rw [hidx, ← hc1, hker] at this
  exact this

theorem a8_cent3 (g : Perm (Fin 8)) (hc : g.cycleType = {3}) :
    Nat.card (centralizer {g}) = 360 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]; decide

theorem a8_cent33 (g : Perm (Fin 8)) (hc : g.cycleType = {3, 3}) :
    Nat.card (centralizer {g}) = 36 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]; decide

theorem a8_cent5 (g : Perm (Fin 8)) (hc : g.cycleType = {5}) :
    Nat.card (centralizer {g}) = 30 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]; decide

theorem a8_cent7 (g : Perm (Fin 8)) (hc : g.cycleType = {7}) :
    Nat.card (centralizer {g}) = 7 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]; decide

section Pair

theorem a8_t_t (t : Perm (Fin 8)) (ht : t * t = 1) (y : Fin 8) : t (t y) = y := by
  simpa using congrArg (fun π : Perm (Fin 8) => π y) ht

theorem a8_pair_comm (t : Perm (Fin 8)) (ht : t * t = 1) (y z : Fin 8) :
    swap y (t y) * swap z (t z) = swap z (t z) * swap y (t y) := by
  by_cases hz : z = y
  · subst hz; rfl
  by_cases hz2 : z = t y
  · subst hz2
    rw [a8_t_t t ht, swap_comm (t y) y]
  refine Disjoint.commute (disjoint_iff_eq_or_eq.2 fun x => ?_)
  by_cases hx : x = y ∨ x = t y
  · right
    have hxz : x ≠ z := by
      rcases hx with rfl | rfl
      · exact fun h => hz h.symm
      · exact fun h => hz2 h.symm
    have hxtz : x ≠ t z := by
      rcases hx with rfl | rfl
      · intro h
        apply hz2
        rw [h, a8_t_t t ht]
      · intro h
        apply hz
        have := congrArg t h
        rw [a8_t_t t ht, a8_t_t t ht] at this
        exact this.symm
    exact swap_apply_of_ne_of_ne hxz hxtz
  · left
    push_neg at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2

@[expose] def a8_pW (t : Perm (Fin 8)) : Subgroup (Perm (Fin 8)) :=
  closure (Set.range fun y : Fin 8 => swap y (t y)) ⊓ alternatingGroup (Fin 8)

theorem a8_pW_isPGroup (t : Perm (Fin 8)) (ht : t * t = 1) : IsPGroup 2 (a8_pW t) := by
  refine IsPGroup.to_le (a8_pair2 _ ?_ ?_) inf_le_left
  · rintro s ⟨y, rfl⟩
    exact swap_mul_self _ _
  · rintro s ⟨y, rfl⟩ u ⟨z, rfl⟩
    exact a8_pair_comm t ht y z

theorem a8_pW_commute (t : Perm (Fin 8)) (ht : t * t = 1) :
    ∀ w ∈ a8_pW t, t * w = w * t := by
  have hcen : closure (Set.range fun y : Fin 8 => swap y (t y)) ≤ Subgroup.centralizer {t} := by
    refine (closure_le _).2 ?_
    rintro s ⟨y, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := swap_apply_apply t y (t y)
    rw [a8_t_t t ht, swap_comm] at h
    show swap y (t y) * t = t * swap y (t y)
    calc swap y (t y) * t = (t * swap y (t y) * t⁻¹) * t := by rw [← h]
      _ = t * swap y (t y) := by group
  intro w hw
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcen (Subgroup.mem_inf.1 hw).1)).symm

theorem a8_pW_normal (t : Perm (Fin 8)) (ht : t * t = 1) (n : Perm (Fin 8))
    (hnt : ∀ y, n (t y) = t (n y)) : ∀ w ∈ a8_pW t, n * w * n⁻¹ ∈ a8_pW t := by
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
  have hcl : ∀ v ∈ closure (Set.range fun y : Fin 8 => swap y (t y)),
      n * v * n⁻¹ ∈ closure (Set.range fun y : Fin 8 => swap y (t y)) := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨y, rfl⟩ := hs
      have : n * swap y (t y) * n⁻¹ = swap (n y) (t (n y)) := by
        rw [← hnt, ← swap_apply_apply]
      rw [this]
      exact subset_closure ⟨n y, rfl⟩
    | one => simp only [mul_one, mul_inv_cancel, one_mem]
    | mul x y _ _ hx hy =>
      have : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx
  refine Subgroup.mem_inf.2 ⟨hcl w hw1, ?_⟩
  rw [mem_alternatingGroup] at hw2 ⊢
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hw2]
  simp

theorem a8_pW_three (t : Perm (Fin 8)) (ht : t * t = 1) (hfp : ∀ y, t y ≠ y) :
    ∃ a b : Perm (Fin 8), a ∈ a8_pW t ∧ b ∈ a8_pW t ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have htt := a8_t_t t ht
  obtain ⟨y, hy⟩ : ∃ y : Fin 8, y ∉ ({0, t 0} : Finset (Fin 8)) := by
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, t 0} : Finset _))
      (t := (Finset.univ : Finset (Fin 8))) (by
        have := Finset.card_le_two (a := (0 : Fin 8)) (b := t 0)
        rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨e, he⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin 8, z ∉ ({0, t 0, y, t y} : Finset (Fin 8)) := by
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, t 0, y, t y} : Finset _)) (t := (Finset.univ : Finset (Fin 8))) (by
        have h1 := Finset.card_le_four (a := (0 : Fin 8)) (b := t 0) (c := y) (d := t y)
        rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨e, he⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy hz
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
  have hyt : t y ≠ 0 := fun h => hy1 (by rw [← h, htt])
  have hzt : t z ≠ 0 := fun h => hz1 (by rw [← h, htt])
  have hyt0 : t y ≠ t 0 := fun h => hy0 (t.injective h)
  have hytz : y ≠ t z := fun h => hz3 (by rw [h, htt])
  have h0y : (0 : Fin 8) ≠ y := fun h => hy0 h.symm
  have h0ty : (0 : Fin 8) ≠ t y := fun h => hyt h.symm
  have h0z : (0 : Fin 8) ≠ z := fun h => hz0 h.symm
  have h0tz : (0 : Fin 8) ≠ t z := fun h => hzt h.symm
  have h1z : y ≠ z := fun h => hz2 h.symm
  refine ⟨swap 0 (t 0) * swap y (t y), swap 0 (t 0) * swap z (t z), ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.2 ⟨mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨y, rfl⟩),
      mem_alternatingGroup.2 ?_⟩
    rw [Perm.sign_mul, sign_swap (hfp 0).symm, sign_swap (hfp y).symm]
    norm_num
  · refine Subgroup.mem_inf.2 ⟨mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨z, rfl⟩),
      mem_alternatingGroup.2 ?_⟩
    rw [Perm.sign_mul, sign_swap (hfp 0).symm, sign_swap (hfp z).symm]
    norm_num
  · intro h
    have := congrArg (fun π : Perm (Fin 8) => π 0) h
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, h0y, h0ty] at this
    exact hfp 0 this
  · intro h
    have := congrArg (fun π : Perm (Fin 8) => π 0) h
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, h0z, h0tz] at this
    exact hfp 0 this
  · intro h
    have := congrArg (fun π : Perm (Fin 8) => π y) h
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne, hy0, hy1, hyt0, h1z, hytz, hyt] at this
    exact hfp y this

end Pair

theorem a8_comm_normalizer (R : Subgroup (Perm (Fin 8))) (w : Perm (Fin 8))
    (hw : ∀ r ∈ R, r * w = w * r) : w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · rw [← hw h hh, mul_inv_cancel_right]; exact hh
  · have hr : (w * h * w⁻¹) * w = w * (w * h * w⁻¹) := hw _ hh
    have e2 : w⁻¹ * (w * h * w⁻¹) * w = w * h * w⁻¹ := by rw [mul_assoc, hr]; group
    have e3 : h = w * h * w⁻¹ := by rw [← e2]; group
    rw [e3]; exact hh

theorem a8_kW_props {a b c d : Fin 8} (R : Subgroup (Perm (Fin 8))) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hfix : ∀ r ∈ R, ∀ y, (y = a ∨ y = b ∨ y = c ∨ y = d) → r y = y)
    (hnorm : ∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ y,
      (y = a ∨ y = b ∨ y = c ∨ y = d) ↔ (n y = a ∨ n y = b ∨ n y = c ∨ n y = d)) :
    (∀ w ∈ a8_kW a b c d, sign w = 1) ∧ IsPGroup 2 (a8_kW a b c d) ∧
      (∀ w ∈ a8_kW a b c d, w ∈ Subgroup.normalizer (R : Set (Perm (Fin 8)))) ∧
      (∀ n ∈ Subgroup.normalizer (R : Set (Perm (Fin 8))), ∀ w ∈ a8_kW a b c d,
        n * w * n⁻¹ ∈ a8_kW a b c d) :=
  ⟨fun w hw => mem_alternatingGroup.1 (a8_kW_le_alt hab hac had hbc hbd hcd hw),
    a8_kW_isPGroup hab hac had hbc hbd hcd,
    fun w hw => a8_comm_normalizer R w (fun r hr => a8_kW_comm hab hac had hbc hbd hcd r
      (fun y hy => hfix r hr y hy) w hw),
    fun n hn w hw => a8_kW_normal hab hac had hbc hbd hcd n (hnorm n hn) w hw⟩

end CFSG.LocalAnalysis.GLTheoremA

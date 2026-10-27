module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTilData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type*} [Group G]

section FixBound

variable [Finite G] {Q : Subgroup G} (hQ : Nat.card Q = 64) (hQ2 : ∀ q ∈ Q, q * q = 1)
include hQ hQ2

theorem card_fix_step' {k : ℕ} {A : Subgroup G} (hL : Level Q k A) {h : G}
    (hhA : ∀ a ∈ A, h * a * h⁻¹ ∈ A) (hinv : ∀ a ∈ A, h * (h * a * h⁻¹) * h⁻¹ = a)
 :
    64 * Nat.card (pw A 2 ⊓ centralizer ({h} : Set G) : Subgroup G) ≤
      Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) *
        Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) := by
  set X := sqFix hL.comm h
  have hXA : ∀ x ∈ X, x ∈ A := fun x hx => hx.1
  have hsq : ∀ x ∈ X, ∀ y ∈ X, (x * y) * (x * y) = (x * x) * (y * y) := by
    intro x hx y hy
    have hxy := hL.comm x hx.1 y hy.1
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x * x * (y * y) := by group
  let sqX : X →* G :=
    { toFun := fun x => (x : G) * x
      map_one' := by simp
      map_mul' := fun x y => hsq x x.2 y y.2 }
  have hrange : sqX.range = pw A 2 ⊓ centralizer ({h} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 x.2.2⟩
      show (x : G) * x ∈ pw A 2
      rw [← sq]
      exact pow_mem_pw x.2.1 2
    · rintro ⟨hy1, hy2⟩
      obtain ⟨x, hx, rfl⟩ := (mem_pw hL.comm).1 hy1
      refine ⟨⟨x, hx, ?_⟩, by simp [sqX, sq]⟩
      rw [← sq]
      exact mem_centralizer_singleton_iff.1 hy2
  have hQX : Q ≤ X := fun q hq => ⟨hL.Q_le hq, by rw [hQ2 q hq, one_mul, mul_one]⟩
  have hker : sqX.ker = Q.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨fun h1 => hL.mem_Q x x.2.1 h1, fun hq => hQ2 x hq⟩
  have hcardX : Nat.card X = 64 * Nat.card (pw A 2 ⊓ centralizer ({h} : Set G) : Subgroup G) := by
    have := card_mul_index sqX.ker
    rw [index_ker, hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hQX).toEquiv, hQ] at this
    exact this.symm
  have hδmul : ∀ x ∈ X, ∀ y ∈ X,
      (x * y)⁻¹ * (h * (x * y) * h⁻¹) = (x⁻¹ * (h * x * h⁻¹)) * (y⁻¹ * (h * y * h⁻¹)) := by
    intro x hx y hy
    have ha : x⁻¹ * (h * x * h⁻¹) ∈ A := mul_mem (inv_mem hx.1) (hhA x hx.1)
    have hc := hL.comm y⁻¹ (inv_mem hy.1) _ ha
    calc (x * y)⁻¹ * (h * (x * y) * h⁻¹) = y⁻¹ * (x⁻¹ * (h * x * h⁻¹)) * (h * y * h⁻¹) := by
          group
      _ = (x⁻¹ * (h * x * h⁻¹)) * y⁻¹ * (h * y * h⁻¹) := by rw [hc]
      _ = (x⁻¹ * (h * x * h⁻¹)) * (y⁻¹ * (h * y * h⁻¹)) := by group
  let δ : X →* G :=
    { toFun := fun x => (x : G)⁻¹ * (h * x * h⁻¹)
      map_one' := by simp
      map_mul' := fun x y => hδmul x x.2 y y.2 }
  have hfixX : A ⊓ centralizer ({h} : Set G) ≤ X := fun x hx => by
    refine ⟨hx.1, ?_⟩
    have := mem_centralizer_singleton_iff.1 hx.2
    rw [mul_assoc, this, ← mul_assoc, this, mul_assoc]
  have hδker : δ.ker = (A ⊓ centralizer ({h} : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (x : G)⁻¹ * (h * x * h⁻¹) = 1 ↔ _
    constructor
    · intro h1
      have h2 : h * x * h⁻¹ = x := by
        have := congrArg ((x : G) * ·) h1
        simpa using this
      refine ⟨x.2.1, mem_centralizer_singleton_iff.2 ?_⟩
      calc (x : G) * h = h * x * h⁻¹ * h := by rw [h2]
        _ = h * x := by group
    · rintro ⟨-, h2⟩
      have := mem_centralizer_singleton_iff.1 h2
      rw [← this]
      group
  have hδrange : δ.range ≤ Q ⊓ centralizer ({h} : Set G) := by
    rintro _ ⟨x, rfl⟩
    have hx := x.2
    have hxA := hx.1
    have hd : (x : G)⁻¹ * (h * x * h⁻¹) ∈ A := mul_mem (inv_mem hxA) (hhA x hxA)
    have hd2 : ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹)) = 1 := by
      have hc := hL.comm _ (hhA x hxA) _ (inv_mem hxA)
      have e : ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹)) =
          ((x : G) * x)⁻¹ * (h * (x * x) * h⁻¹) := by
        calc ((x : G)⁻¹ * (h * x * h⁻¹)) * ((x : G)⁻¹ * (h * x * h⁻¹))
            = (x : G)⁻¹ * ((h * x * h⁻¹) * (x : G)⁻¹) * (h * x * h⁻¹) := by group
          _ = (x : G)⁻¹ * ((x : G)⁻¹ * (h * x * h⁻¹)) * (h * x * h⁻¹) := by rw [hc]
          _ = ((x : G) * x)⁻¹ * (h * (x * x) * h⁻¹) := by group
      rw [e, ← hx.2, mul_inv_cancel_right, inv_mul_cancel]
    refine ⟨hL.mem_Q _ hd hd2, mem_centralizer_singleton_iff.2 ?_⟩
    have hdinv : ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ = (x : G)⁻¹ * (h * x * h⁻¹) :=
      inv_eq_of_mul_eq_one_right hd2
    have e : h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ = ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ := by
      calc h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ = (h * x * h⁻¹)⁻¹ * (h * (h * x * h⁻¹) * h⁻¹) :=
            by group
        _ = (h * x * h⁻¹)⁻¹ * x := by rw [hinv x hxA]
        _ = ((x : G)⁻¹ * (h * x * h⁻¹))⁻¹ := by group
    rw [hdinv] at e
    calc (x : G)⁻¹ * (h * x * h⁻¹) * h = h * ((x : G)⁻¹ * (h * x * h⁻¹)) * h⁻¹ * h := by rw [e]
      _ = h * ((x : G)⁻¹ * (h * x * h⁻¹)) := by group
  have h1 := card_mul_index δ.ker
  rw [index_ker, hδker, Nat.card_congr (subgroupOfEquivOfLe hfixX).toEquiv] at h1
  have h2 : Nat.card δ.range ≤ Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) :=
    card_le_of_le hδrange
  rw [← hcardX, ← h1]
  exact Nat.mul_le_mul_left _ h2

end FixBound

theorem card_fix2 (R : Array ℕ) :
    (Finset.univ.filter fun v : V6 => toMat 6 6 R *ᵥ v = v).card = fix2c R := by
  have h1 : fix2c R = ((Finset.range 64).filter fun x => (bmulVec 6 6 R x == x) = true).card := by
    rw [fix2c, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp only [Bool.decide_eq_true]
  rw [h1, ← card_filter_vecBits]
  refine congrArg Finset.card (Finset.filter_congr fun v _ => ?_)
  simp only [beq_iff_eq]
  rw [← vecBits_mulVec]
  exact ⟨fun h => by rw [h], fun h => by rw [← toVec_vecBits (toMat 6 6 R *ᵥ v), h,
    toVec_vecBits]⟩

theorem enc4_toVec4_dig4 {n : ℕ} (hn : n < 4096) : enc4 (toVec4 (dig4 n)) = n := by
  have hv : ∀ j : Fin 6, (toVec4 (dig4 n) j).val = n / 4 ^ (j : ℕ) % 4 := by
    intro j
    simp only [toVec4, dig4]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [j.isLt, dite_true, Option.getD_some]
    exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by norm_num))
  simp only [enc4, Fin.sum_univ_six, hv]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  omega

theorem card_filter_enc4 (f : ℕ → Bool) :
    (Finset.univ.filter fun v : Fin 6 → ZMod 4 => f (enc4 v) = true).card =
      ((Finset.range 4096).filter fun n => f n = true).card := by
  apply Finset.card_bij (fun v _ => enc4 v)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv ⊢
    exact ⟨enc4_lt v, hv⟩
  · intro v _ w _ h
    rw [← toVec4_dig4_enc4 v, h, toVec4_dig4_enc4]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨toVec4 (dig4 n), ?_, enc4_toVec4_dig4 hn.1⟩
    simpa [enc4_toVec4_dig4 hn.1] using hn.2

theorem card_fix4 (M : Array (Array ℕ)) :
    (Finset.univ.filter fun v : Fin 6 → ZMod 4 => toMat4 M *ᵥ v = v).card = fix4c M := by
  have h1 : fix4c M = ((Finset.range 4096).filter fun n =>
      (mv4 M (dig4 n) == dig4 n) = true).card := by
    rw [fix4c, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp only [Bool.decide_eq_true]
  rw [h1, ← card_filter_enc4 (fun n => mv4 M (dig4 n) == dig4 n)]
  refine congrArg Finset.card (Finset.filter_congr fun v _ => ?_)
  simp only [beq_iff_eq]
  constructor
  · intro h
    have h2 : toVec4 (mv4 M (dig4 (enc4 v))) = toVec4 (dig4 (enc4 v)) := by
      rw [toVec4_mv4, toVec4_dig4_enc4, h]
    exact eq_of_toVec4_eq (f := fun i => ∑ k : Fin 6, m4Get M i k * (dig4 (enc4 v)).getD k 0)
      (g := fun j => enc4 v / 4 ^ (j : ℕ)) h2
  · intro h
    have := congrArg toVec4 h
    rwa [toVec4_mv4, toVec4_dig4_enc4] at this

theorem two_mul_card_le' [Finite G] {t : G} {n : ℕ}
    (hAb : ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → IsPGroup 2 B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → Nat.card B ≤ n) (ht2 : t * t = 1) {g : G}
    {D : Subgroup G} (hD2 : IsPGroup 2 D) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hDu : ∀ d ∈ D, d * (g * t * g⁻¹) = (g * t * g⁻¹) * d) (huD : g * t * g⁻¹ ∉ D) :
    2 * Nat.card D ≤ n := by
  set u := g * t * g⁻¹ with hu
  have hu2 : u * u = 1 := by
    have e : g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
    rw [hu, e, ht2, mul_one, mul_inv_cancel]
  have hcomm : ∀ d ∈ D, ∀ z ∈ zpowers u, d * z = z * d := by
    intro d hd z hz
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (hDu d hd) n)
  set B : Subgroup G := D ⊔ zpowers u
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    Stage1.sup_comm_of hDc (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm]) hcomm hx hy
  have hu2' : IsPGroup 2 (zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hu2)
    have h2 : orderOf u ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]
      intro h1'
      exact huD (h1' ▸ one_mem D)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  have hB2 : IsPGroup 2 B := IsPGroup.to_sup_of_normal_left' hD2 hu2'
    (zpowers_le.2 (mem_normalizer_of_conj_mem fun d hd => by
      rw [← hDu d hd, mul_inv_cancel_right]; exact hd))
  have hlt : D < B := lt_of_le_of_ne le_sup_left fun h => huD (h ▸ mem_sup_right (mem_zpowers u))
  have hcard : 2 * Nat.card D ≤ Nat.card B := by
    obtain ⟨m, hm⟩ := card_dvd_of_le hlt.le
    have hne : Nat.card D ≠ Nat.card B := fun h => hlt.ne (eq_of_le_of_card_ge hlt.le h.ge)
    have hpos : 0 < Nat.card D := Nat.card_pos
    rcases m with _ | _ | m
    · simp at hm; exact absurd hm (Nat.card_pos.ne')
    · simp only [zero_add, mul_one] at hm; exact absurd hm.symm hne
    · rw [hm]; nlinarith
  set B' := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hB'le : B' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxu : x * u = u * x := hBc x hx u (mem_sup_right (mem_zpowers u))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hu] at hxu
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * x) * g := by rw [hxu]
      _ = t * (g⁻¹ * x * g) := by group
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g⁻¹⁻¹ by group, hBc x hx y hy]
    group
  have h := hAb B' hB'le (hB2.map _) hB'c
  rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at h
  omega

end CFSG.EvenSmallLie.OmegaEight.Chain

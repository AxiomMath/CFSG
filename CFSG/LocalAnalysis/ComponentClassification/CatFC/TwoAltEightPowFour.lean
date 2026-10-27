module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.ComponentClassification.CatFC

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

theorem alt8_eq_of_ne_one {G : Type*} [Group G] {H : Subgroup G} (h2 : Nat.card H = 2)
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h2
  have h := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h' := hy ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h.trans h'.symm)

theorem alt8_sq_eq_one {G : Type*} [Group G] {H : Subgroup G} (h2 : Nat.card H = 2)
    {g : G} (hg : g ∈ H) : g ^ 2 = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨g, hg⟩))
  rw [h2] at h
  simpa using h

theorem alt8_exists_lifts {P : Type*} [Group P] {m : ℕ}
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) :
    ∃ x : Fin m → P, (∀ i, η (x i) = altThreeCycle i) ∧ ∀ i, x i ^ 3 = 1 := by
  have hlift : ∀ i : Fin m, ∃ x : P, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hK2
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  exact ⟨x, hxη, hx3⟩

theorem alt8_closure_eq_top {P : Type*} [Group P] [Group.IsPerfect P] {m : ℕ}
    (η : P →* alternatingGroup (Fin (m + 2))) (hK : η.ker ≤ Subgroup.center P)
    {x : Fin m → P} (hxη : ∀ i, η (x i) = altThreeCycle i) :
    Subgroup.closure (Set.range x) = ⊤ := by
  have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have : η ∘ x = altThreeCycle := funext hxη
    rw [this, closure_altThreeCycle]
  have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
    (Subgroup.closure (Set.range x)) η.ker hK
  rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
  exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))

theorem alt8_sq_ne_one {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] {m : ℕ}
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) (hcard : Nat.card η.ker = 2)
    {x : Fin m → P} (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) : (x i₀ * x i₁) ^ 2 ≠ 1 := by
  intro h
  have hall : ∀ i j : Fin m, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij => by
    rw [lift_sq_eq η hη hK hK2 hxη hx3 hij h01, h]
  have hcl := card_closure_le_of_carmichael m x hx3 hall
  rw [alt8_closure_eq_top η hK hxη, Subgroup.card_top] at hcl
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  rw [hP2, hA, hcard] at hcl
  omega

theorem alt8_sq_eq_of_map_eq {P : Type*} [Group P] {m : ℕ}
    (η : P →* alternatingGroup (Fin (m + 2))) (hK : η.ker ≤ Subgroup.center P)
    (hsq : ∀ k ∈ η.ker, k ^ 2 = 1) {a y : P} (hy : η y = η a) : y ^ 2 = a ^ 2 := by
  have hk : a⁻¹ * y ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hc : Commute a (a⁻¹ * y) := Subgroup.mem_center_iff.mp (hK hk) a
  calc y ^ 2 = (a * (a⁻¹ * y)) ^ 2 := by rw [mul_inv_cancel_left]
    _ = a ^ 2 * (a⁻¹ * y) ^ 2 := hc.mul_pow 2
    _ = a ^ 2 := by rw [hsq _ hk, mul_one]

theorem alt8_exists_root :
    ∃ π : alternatingGroup (Fin (6 + 2)), π ^ 2 = altThreeCycle (n := 6) 0 * altThreeCycle 1 := by
  refine ⟨⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin (6 + 2)) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (1 : Fin (6 + 2)) ≠ 2),
      Equiv.Perm.sign_swap (by decide : (2 : Fin (6 + 2)) ≠ 3),
      Equiv.Perm.sign_swap (by decide : (4 : Fin (6 + 2)) ≠ 5)]
    decide
  · apply Subtype.ext
    show (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin (6 + 2))) ^ 2
      = altThreeCyclePerm 0 * altThreeCyclePerm 1
    decide

theorem exists_pow_four_eq_of_doubleCover_alt8 {B : Type} [Group B] [Finite B]
    (hB : CFSG.GH74.GLS.IsDoubleCoverOfAlt B 8) {z : B} (hz : z ∈ Subgroup.center B)
    (hz1 : z ≠ 1) : ∃ w : B, w ^ 4 = z := by
  obtain ⟨hq, hcard, ⟨e⟩⟩ := hB
  obtain ⟨hperf, -, -⟩ := hq
  haveI : Group.IsPerfect B := hperf
  let η : B →* alternatingGroup (Fin (6 + 2)) :=
    (e : (B ⧸ Subgroup.center B) ≃* alternatingGroup (Fin (6 + 2))).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center B))
  have hη : Function.Surjective η := fun a => by
    obtain ⟨q, hq⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center B) q
    exact ⟨b, hq⟩
  have hker : η.ker = Subgroup.center B := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center B) x) = 1 ↔ x ∈ Subgroup.center B
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hK : η.ker ≤ Subgroup.center B := hker.le
  have hcardK : Nat.card η.ker = 2 := by rw [hker]; exact hcard
  have hK2 : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hcardK, pow_one])
  obtain ⟨x, hxη, hx3⟩ := alt8_exists_lifts η hη hK hK2
  have hx01 : (0 : Fin 6) ≠ 1 := by decide
  have hs1 : (x 0 * x 1) ^ 2 ≠ 1 := alt8_sq_ne_one η hη hK hK2 hcardK hxη hx3 hx01
  have hsK : (x 0 * x 1) ^ 2 ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq hx01]
  have hs_eq : (x 0 * x 1) ^ 2 = z := alt8_eq_of_ne_one hcard (hK hsK) hz hs1 hz1
  have hlift_sq : ∀ y : B, η y = η (x 0 * x 1) → y ^ 2 = z := fun y hy =>
    (alt8_sq_eq_of_map_eq η hK (fun k hk => alt8_sq_eq_one hcardK hk) hy).trans hs_eq
  obtain ⟨π, hπ⟩ := alt8_exists_root
  obtain ⟨w, hw⟩ := hη π
  have h2 : η (w ^ 2) = η (x 0 * x 1) := by
    rw [map_pow, hw, map_mul, hxη, hxη]
    exact hπ
  refine ⟨w, ?_⟩
  calc w ^ 4 = (w ^ 2) ^ 2 := by group
    _ = z := hlift_sq (w ^ 2) h2

end CFSG.ComponentClassification.CatFC

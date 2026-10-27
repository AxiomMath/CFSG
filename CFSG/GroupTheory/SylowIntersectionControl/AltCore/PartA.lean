module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartStab
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.NonEven

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

section Piece

variable {β : Type*} (U Δ : Set β) (t₁ t₂ : Setoid β)

def pieceSetoid : Setoid β where
  r x y := (x ∈ U ∧ y ∈ U ∧ t₁.r x y) ∨ (x ∉ U ∧ y ∉ U ∧ x ∈ Δ ∧ y ∈ Δ) ∨
    (x ∉ U ∧ y ∉ U ∧ x ∉ Δ ∧ y ∉ Δ ∧ t₂.r x y)
  iseqv := by
    refine ⟨fun x => ?_, fun h => ?_, fun h h' => ?_⟩
    · by_cases hU : x ∈ U
      · exact Or.inl ⟨hU, hU, t₁.refl x⟩
      · by_cases hΔ : x ∈ Δ
        · exact Or.inr (Or.inl ⟨hU, hU, hΔ, hΔ⟩)
        · exact Or.inr (Or.inr ⟨hU, hU, hΔ, hΔ, t₂.refl x⟩)
    · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩
      · exact Or.inl ⟨h2, h1, t₁.symm h3⟩
      · exact Or.inr (Or.inl ⟨h2, h1, h4, h3⟩)
      · exact Or.inr (Or.inr ⟨h2, h1, h4, h3, t₂.symm h5⟩)
    · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ <;>
      rcases h' with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4, k5⟩
      · exact Or.inl ⟨h1, k2, t₁.trans h3 k3⟩
      all_goals first
        | exact absurd h2 k1 | exact absurd k1 h2 | exact absurd h4 k3 | exact absurd k3 h4
        | skip
      · exact Or.inr (Or.inl ⟨h1, k2, h3, k4⟩)
      · exact Or.inr (Or.inr ⟨h1, k2, h3, k4, t₂.trans h5 k5⟩)

variable {U Δ t₁ t₂}

theorem pieceSetoid_iff_of_mem {x y : β} (hx : x ∈ U) :
    (pieceSetoid U Δ t₁ t₂).r x y ↔ y ∈ U ∧ t₁.r x y := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨hx, h.1, h.2⟩⟩
  rcases h with ⟨-, h2, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨h2, h3⟩
  · exact absurd hx h1
  · exact absurd hx h1

theorem pieceSetoid_iff_of_mem_delta {x y : β} (hx : x ∉ U) (hxΔ : x ∈ Δ) :
    (pieceSetoid U Δ t₁ t₂).r x y ↔ y ∉ U ∧ y ∈ Δ := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨hx, h.1, hxΔ, h.2⟩)⟩
  rcases h with ⟨h1, -⟩ | ⟨-, h2, -, h4⟩ | ⟨-, -, h3, -⟩
  · exact absurd h1 hx
  · exact ⟨h2, h4⟩
  · exact absurd hxΔ h3

theorem pieceSetoid_iff_of_not_mem {x y : β} (hx : x ∉ U) (hxΔ : x ∉ Δ) :
    (pieceSetoid U Δ t₁ t₂).r x y ↔ y ∉ U ∧ y ∉ Δ ∧ t₂.r x y := by
  refine ⟨fun h => ?_, fun h => Or.inr (Or.inr ⟨hx, h.1, hxΔ, h.2.1, h.2.2⟩)⟩
  rcases h with ⟨h1, -⟩ | ⟨-, -, h3, -⟩ | ⟨-, h2, -, h4, h5⟩
  · exact absurd h1 hx
  · exact absurd h3 hxΔ
  · exact ⟨h2, h4, h5⟩

end Piece

theorem mem_partStab_pieceSetoid {n : ℕ} {U Δ : Set (Fin n)} {t₁ t₂ : Setoid (Fin n)}
    {g : Perm (Fin n)} (hU : ∀ x, g x ∈ U ↔ x ∈ U) (hΔ : ∀ x, g x ∈ Δ ↔ x ∈ Δ)
    (h₁ : ∀ x ∈ U, ∀ y ∈ U, t₁.r (g x) (g y) ↔ t₁.r x y)
    (h₂ : ∀ x, x ∉ U → x ∉ Δ → ∀ y, y ∉ U → y ∉ Δ → (t₂.r (g x) (g y) ↔ t₂.r x y)) :
    g ∈ partStab (pieceSetoid U Δ t₁ t₂) := by
  intro x y
  by_cases hx : x ∈ U
  · rw [pieceSetoid_iff_of_mem ((hU x).mpr hx), pieceSetoid_iff_of_mem hx, hU y]
    exact ⟨fun h => ⟨h.1, (h₁ x hx y h.1).mp h.2⟩, fun h => ⟨h.1, (h₁ x hx y h.1).mpr h.2⟩⟩
  · by_cases hxΔ : x ∈ Δ
    · rw [pieceSetoid_iff_of_mem_delta (by rwa [hU]) ((hΔ x).mpr hxΔ),
        pieceSetoid_iff_of_mem_delta hx hxΔ, hU y, hΔ y]
    · rw [pieceSetoid_iff_of_not_mem (by rwa [hU]) (by rwa [hΔ]),
        pieceSetoid_iff_of_not_mem hx hxΔ, hU y, hΔ y]
      exact ⟨fun h => ⟨h.1, h.2.1, (h₂ x hx hxΔ y h.1 h.2.1).mp h.2.2⟩,
        fun h => ⟨h.1, h.2.1, (h₂ x hx hxΔ y h.1 h.2.1).mpr h.2.2⟩⟩

variable {α : Type} [Fintype α] [DecidableEq α] {H : Subgroup (Perm α)}

omit [DecidableEq α] in
theorem exists_mem_eq_on_orbit_of_sq_mem (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) {a : Perm α}
    (haN : a ∈ normalizer (H : Set (Perm α))) (ha2 : a ^ 2 ∈ H) {x : α}
    (hx : x ∉ orbit (normalizer (H : Set (Perm α))) x₀) :
    ∃ h ∈ H, ∀ y ∈ orbit (normalizer (H : Set (Perm α))) x, a y = h y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrad := isRadical_of_isPIsolatedOver hH hiso
  have hO := orbit_mem_setStab (H := H) x
  refine ⟨restrHom _ ⟨a, hO haN⟩, ?_, fun y hy => (restrHom_apply_of_mem ⟨a, hO haN⟩ hy).symm⟩
  by_contra hr
  have hsq : (restrHom (orbit (normalizer (H : Set (Perm α))) x) ⟨a, hO haN⟩) ^ 2 ∈ H := by
    rw [← map_pow]
    exact restrHom_mem hH hrad hO ha2
  have hev : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x) :=
    ⟨_, restrHom_mem_normalizer hH hrad hO haN, fun z hz => restrHom_apply_of_not_mem _ hz,
      hr, hsq⟩
  exact hx (orbit_eq_iff.mp (orbit_eq_of_isEvenSet hH hiso hev he))

omit [Fintype α] [DecidableEq α] in
theorem orbitRel_apply_iff {K : Subgroup (Perm α)} {a : Perm α}
    (ha : a ∈ normalizer (K : Set (Perm α))) (x y : α) :
    (orbitRel K α).r (a x) (a y) ↔ (orbitRel K α).r x y := by
  change a x ∈ orbit K (a y) ↔ x ∈ orbit K y
  constructor
  · rintro ⟨⟨k, hk⟩, hkx⟩
    refine ⟨⟨a⁻¹ * k * a, by simpa using (mem_normalizer_iff.mp (inv_mem ha) k).mp hk⟩, ?_⟩
    change (a⁻¹ * k * a) y = x
    simp only [Perm.mul_apply]
    rw [show k (a y) = a x from hkx]
    exact a.symm_apply_apply x
  · rintro ⟨⟨k, hk⟩, rfl⟩
    refine ⟨⟨a * k * a⁻¹, (mem_normalizer_iff.mp ha k).mp hk⟩, ?_⟩
    change (a * k * a⁻¹) (a y) = a (k y)
    simp only [Perm.mul_apply]
    rw [show a⁻¹ (a y) = y from a.symm_apply_apply y]

theorem mem_partStab_of_sq_mem {n : ℕ} {H : Subgroup (Perm (Fin n))} (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n)))) H) {x₀ : Fin n}
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀))
    {K : Subgroup (Perm (Fin n))}
    (hK : normalizer (H : Set (Perm (Fin n))) ≤ normalizer (K : Set (Perm (Fin n))))
    {Δ : Set (Fin n)} (hΔ : ∀ a ∈ normalizer (H : Set (Perm (Fin n))), ∀ x, a x ∈ Δ ↔ x ∈ Δ)
    {t : Setoid (Fin n)} (ht : ∀ g ∈ H, ∀ x y, t.r (g x) (g y) ↔ t.r x y)
    (hto : ∀ x y, t.r x y → y ∈ orbit H x) {a : Perm (Fin n)}
    (haN : a ∈ normalizer (H : Set (Perm (Fin n)))) (ha2 : a ^ 2 ∈ H) :
    a ∈ partStab (pieceSetoid (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) Δ
      (orbitRel K (Fin n)) t) := by
  refine mem_partStab_pieceSetoid (orbit_mem_setStab x₀ haN) (hΔ a haN)
    (fun x _ y _ => orbitRel_apply_iff (hK haN) x y) fun x hx _ y hy _ => ?_
  obtain ⟨g, hg, hag⟩ := exists_mem_eq_on_orbit_of_sq_mem hH hiso he haN ha2 hx
  have hHN : ∀ z : Fin n, orbit H z ⊆ orbit (normalizer (H : Set (Perm (Fin n)))) z := by
    rintro z w ⟨⟨h, hh⟩, rfl⟩
    exact ⟨⟨h, le_normalizer hh⟩, rfl⟩
  have hax : a x = g x := hag x (mem_orbit_self x)
  by_cases hyx : y ∈ orbit H x
  · rw [hax, hag y (hHN x hyx)]
    exact ht g hg x y
  · refine iff_of_false (fun h => hyx ?_) fun h => hyx (hto x y h)
    have h1 : a y ∈ orbit H x := by
      have := hto _ _ h
      rw [hax] at this
      rwa [orbit_eq_iff.mpr (⟨⟨g, hg⟩, rfl⟩ : g x ∈ orbit H x)] at this
    have h2 : a y ∈ orbit H y := by
      rw [← orbit_normalizer_eq_orbit hH hiso he hy]
      exact ⟨⟨a, haN⟩, rfl⟩
    rw [orbit_eq_iff.mpr (orbit_eq_iff.mp ((orbit_eq_iff.mpr h1).symm.trans (orbit_eq_iff.mpr h2)))]
    · exact mem_orbit_self y

section Classes

variable {β : Type*} {U Δ : Set β} {K : Subgroup (Perm β)} {t : Setoid β}

theorem card_pieceSetoid_of_mem (hK : ∀ k ∈ K, ∀ y, k y ∈ U ↔ y ∈ U) {x : β} (hx : x ∈ U) :
    Nat.card {y // (pieceSetoid U Δ (orbitRel K β) t).r x y} = Nat.card (orbit K x) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [pieceSetoid_iff_of_mem hx]
  change (y ∈ U ∧ x ∈ orbit K y) ↔ y ∈ orbit K x
  constructor
  · rintro ⟨-, hxy⟩
    exact mem_orbit_symm.mp hxy
  · intro hy
    refine ⟨?_, mem_orbit_symm.mp hy⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    exact (hK k hk x).mpr hx

theorem card_pieceSetoid_of_not_mem {t₁ : Setoid β} {x : β} (hx : x ∉ U) (hxΔ : x ∉ Δ)
    (ht : ∀ y, t.r x y → y ∉ U ∧ y ∉ Δ) :
    Nat.card {y // (pieceSetoid U Δ t₁ t).r x y} = Nat.card {y // t.r x y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [pieceSetoid_iff_of_not_mem hx hxΔ]
    exact ⟨fun h => h.2.2, fun h => ⟨(ht y h).1, (ht y h).2, h⟩⟩)

end Classes

omit [DecidableEq α] in
theorem exists_card_orbit_eq_two_pow' {P : Subgroup (Perm α)} (hP : IsPGroup 2 P)
    (x : α) : ∃ j, Nat.card (orbit P x) = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have h1 : (stabilizer P x).index ∣ Nat.card P := index_dvd_card _
  rw [index_stabilizer, hm] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, by rw [Nat.card_coe_set_eq, hj]⟩

omit [DecidableEq α] in
private theorem omegaOneCenter_bot_of_card_orbit (hH : IsPGroup 2 H) {x₀ : α}
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm α))) x₀)] (hx₀ : x₀ ∉ fixSet H)
    (h : ∀ x ∈ orbit (normalizer (H : Set (Perm α))) x₀,
      Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x) = 2 ^ 0) : False := by
  have hK1 : restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H ≠ ⊥ := by
    intro hbot
    refine hx₀ fun g hg => ?_
    have hr := restrHom_mem_restrSub (O := orbit (normalizer (H : Set (Perm α))) x₀)
      (h := ⟨g, orbit_mem_setStab x₀ (le_normalizer hg)⟩) hg
    rw [hbot, mem_bot] at hr
    have := congrArg (fun f : Perm α => f x₀) hr
    simp only [Perm.one_apply] at this
    rwa [restrHom_apply_of_mem _ (mem_orbit_self x₀)] at this
  refine omegaOneCenter_ne_bot (isPGroup_restrSub hH) hK1 (eq_bot_iff.mpr fun e he => ?_)
  rw [mem_bot]
  ext z
  by_cases hz : z ∈ orbit (normalizer (H : Set (Perm α))) x₀
  · have h1 := h z hz
    rw [pow_zero] at h1
    obtain ⟨w, hw⟩ := Nat.card_eq_one_iff_exists.mp h1
    exact congrArg Subtype.val ((hw ⟨e z, ⟨⟨e, he⟩, rfl⟩⟩).trans (hw ⟨z, mem_orbit_self z⟩).symm)
  · exact restrSub_le_fixOutside (omegaOneCenter_le _ he) z hz

omit [DecidableEq α] in
theorem exists_card_orbit_omegaOneCenterOf_eq_of_le (hH : IsPGroup 2 H) {x₀ : α}
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm α))) x₀)] (hx₀ : x₀ ∉ fixSet H)
    (hle4 : Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
      (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x₀) ≤ 4) :
    ∃ i, (i = 1 ∨ i = 2) ∧ ∀ x ∈ orbit (normalizer (H : Set (Perm α))) x₀,
      Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x) = 2 ^ i := by
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm α)) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H : Set (Perm α)) :=
    fun n hn => mem_normalizer_fintype fun k hk => conj_mem_restrSub hn (hO hn) hk
  have hEN := hKN.trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hconst : ∀ x ∈ orbit (normalizer (H : Set (Perm α))) x₀,
      Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x) =
      Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x₀) := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    exact card_orbit_eq_of_normalizer (hEN hn) x₀
  obtain ⟨j, hj⟩ := exists_card_orbit_eq_two_pow'
    ((isPGroup_restrSub (O := orbit (normalizer (H : Set (Perm α))) x₀) hH).to_le
      (omegaOneCenter_le _)) x₀
  have hle : 2 ^ j ≤ 4 := hj ▸ hle4
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact omegaOneCenter_bot_of_card_orbit hH hx₀ (fun x hx => (hconst x hx).trans hj)
  refine ⟨j, ?_, fun x hx => (hconst x hx).trans hj⟩
  have : j ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

theorem exists_card_orbit_omegaOneCenterOf_eq (hH : IsPGroup 2 H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm α))) H) {x₀ : α}
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm α))) x₀)]
    (he : IsEvenSet H (orbit (normalizer (H : Set (Perm α))) x₀)) (hx₀ : x₀ ∉ fixSet H) :
    ∃ i, (i = 1 ∨ i = 2) ∧ ∀ x ∈ orbit (normalizer (H : Set (Perm α))) x₀,
      Nat.card (orbit (CFSG.Quasithin.omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm α))) x₀) H)) x) = 2 ^ i :=
  exists_card_orbit_omegaOneCenterOf_eq_of_le hH hx₀
    (card_orbit_omegaOneCenter_restrSub_le_four hH hiso he (mem_orbit_self x₀))

end CFSG.GroupTheory.AltCore

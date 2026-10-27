module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePiecesAux
public import CFSG.LocalAnalysis.PreuniquenessRankFour.HyperplaneGeneration

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Pieces

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem exists_fixedPiece_ne_bot [Finite A] [Finite V] {p : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hV : ¬ p ∣ Nat.card V) (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) :
    ∃ F : Subgroup A, F.index = p ∧ (fixedPiece F : Subgroup V) ≠ ⊥ := by
  by_contra hno
  push Not at hno
  have hle : ∀ F : Subgroup A, F.index = 1 ∨ F.index = p →
      (fixedBy F : Subgroup V) ≤ fixedBy (⊤ : Subgroup A) := by
    rintro F (hF | hF)
    · rw [Subgroup.index_eq_one.mp hF]
    · exact fixedPiece_eq_bot_iff.mp (hno F hF)
  have htop := CFSG.PreuniquenessRankFour.Helpers.coprime_group_generated_by_prime_fixedSubgroups
    (acting := A) (source := V) p hV hA
  have hsup : sSup {fixedGroup : Subgroup V | ∃ kernel : Subgroup A,
      (kernel.index = 1 ∨ kernel.index = p) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} ≤
      fixedBy (⊤ : Subgroup A) :=
    sSup_le fun Y ⟨F, hF, hY⟩ =>
      (show Y ≤ fixedBy F from fun y hy a ha => hY a ha y hy).trans (hle F hF)
  obtain ⟨a, v, hav⟩ := hnt
  exact hav (hsup (htop ▸ Subgroup.mem_top v) a (Subgroup.mem_top a))

theorem exists_smul_mul_inv_eq [Finite A] [Finite V] {p : ℕ} (hp : p.Prime) {F : Subgroup A}
    (hF : F.index = p) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) {x : A} (hx : x ∉ F)
    {w : V} (hw : w ∈ (fixedPiece F : Subgroup V)) :
    ∃ u ∈ (fixedPiece F : Subgroup V), (x • u) * u⁻¹ = w := by
  set W : Subgroup V := fixedPiece F with hWdef
  have hsup : F ⊔ Subgroup.zpowers x = ⊤ :=
    sup_eq_top_of_index_eq_prime_of_not_le hp hF fun h => hx (h (Subgroup.mem_zpowers x))
  have htop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card V) := by
    rwa [Subgroup.card_top]
  let f : W →* W :=
    { toFun := fun u => ⟨(x • (u : V)) * (u : V)⁻¹,
        mul_mem (smul_mem_fixedPiece x u.2) (inv_mem u.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u u' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        rw [smul_mul', mul_inv, mul_mul_mul_comm]) }
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun u hu => ?_
    have hxu : x • (u : V) = u := mul_inv_eq_one.mp (congrArg Subtype.val hu)
    have hstab : (⊤ : Subgroup A) ≤ MulAction.stabilizer A (u : V) := by
      rw [← hsup]
      exact sup_le (fun b hb => fixedPiece_le_fixedBy F u.2 b hb) (Subgroup.zpowers_le.mpr hxu)
    have hmem : (u : V) ∈ actCommutator (⊤ : Subgroup V) (⊤ : Subgroup A) ⊓
        fixedBy (⊤ : Subgroup A) :=
      ⟨actCommutator_mono le_top le_rfl u.2, fun a _ => hstab (Subgroup.mem_top a)⟩
    rw [actCommutator_top_inf_fixedBy htop, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hinj ⟨w, hw⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem pairing_fixedPiece_eq_one [Finite A] [Finite V] {Z : Type*} [CommGroup Z] {p : ℕ}
    (hp : p.Prime) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) (B : V →* V →* Z)
    (hB : ∀ (a : A) (v w : V), B (a • v) (a • w) = B v w) {F F' : Subgroup A}
    (hF : F.index = p) (hF' : F'.index = p) (hne : F ≠ F') {v w : V}
    (hv : v ∈ (fixedPiece F : Subgroup V)) (hw : w ∈ (fixedPiece F' : Subgroup V)) :
    B v w = 1 := by
  obtain ⟨x, hxF, hxF'⟩ := exists_mem_not_mem_of_index_eq_prime hp hF' hF (Ne.symm hne)
  obtain ⟨u, -, rfl⟩ := exists_smul_mul_inv_eq hp hF' hcop hxF' hw
  have hxv : x • v = v := fixedPiece_le_fixedBy F hv x hxF
  rw [map_mul, map_inv, ← hB x v u, hxv, mul_inv_cancel]

end Pieces

section Orbit

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem map_mul_toMonoidHom {G : Type*} [Group G] (α γ : MulAut G) (F : Subgroup G) :
    F.map (α * γ).toMonoidHom = (F.map γ.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem pow_apply_smul {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v)
    (k : ℕ) (a : A) (v : V) : (β ^ k) (a • v) = (α ^ k) a • (β ^ k) v := by
  induction k generalizing a v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hαβ, ih]

theorem map_fixedBy_le {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v)
    (F : Subgroup A) :
    (fixedBy F : Subgroup V).map β.toMonoidHom ≤ fixedBy (F.map α.toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨b, hb, rfl⟩
  change α b • β v = β v
  rw [← hαβ, hv b hb]

theorem map_fixedPiece_le {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v)
    (F : Subgroup A) :
    (fixedPiece F : Subgroup V).map β.toMonoidHom ≤ fixedPiece (F.map α.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine actCommutator_le fun u hu a _ => ?_
  change β ((a • u) * u⁻¹) ∈ (fixedPiece (F.map α.toMonoidHom) : Subgroup V)
  rw [map_mul, map_inv, hαβ]
  exact mem_actCommutator (map_fixedBy_le hαβ F ⟨u, hu, rfl⟩) (Subgroup.mem_top _)

theorem exists_injective_fixedPiece_ne_bot [Finite A] [Finite V] {p r : ℕ} [Fact p.Prime]
    (hA : ∀ a : A, a ^ p = 1) (hA2 : p ^ 2 ≤ Nat.card A) (hV : ¬ p ∣ Nat.card V)
    (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ F : Subgroup A, F.map (α ^ k).toMonoidHom = F →
      F = ⊥ ∨ F = ⊤) :
    ∃ F : Fin r → Subgroup A, Function.Injective F ∧ (∀ j, (F j).index = p) ∧
      ∀ j, (fixedPiece (F j) : Subgroup V) ≠ ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨F₀, hF₀, hne⟩ := exists_fixedPiece_ne_bot hA hV hnt
  have hF₀top : F₀ ≠ ⊤ := fun h => by
    rw [h, Subgroup.index_top] at hF₀
    exact hp.one_lt.ne hF₀
  have hF₀bot : F₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.index_bot] at hF₀
    rw [hF₀, pow_two] at hA2
    exact absurd hA2 (not_le.mpr (lt_mul_of_one_lt_right hp.pos hp.one_lt))
  have hmap : ∀ i j : ℕ, i < j → j < r →
      F₀.map (α ^ i).toMonoidHom ≠ F₀.map (α ^ j).toMonoidHom := by
    intro i j hij hjr h
    have hj : α ^ j = α ^ i * α ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hj, map_mul_toMonoidHom] at h
    have hk : F₀.map (α ^ (j - i)).toMonoidHom = F₀ :=
      (Subgroup.map_injective (α ^ i).injective h).symm
    rcases hirr (j - i) (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) F₀ hk with h | h
    · exact hF₀bot h
    · exact hF₀top h
  refine ⟨fun j => F₀.map (α ^ (j : ℕ)).toMonoidHom, ?_, fun j => ?_, fun j => ?_⟩
  · intro i j hij
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact hmap i j h j.2 hij
    · exact hmap j i h i.2 hij.symm
  · change (F₀.map (α ^ (j : ℕ)).toMonoidHom).index = p
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact hF₀
  · intro hbot
    obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    have hmem := map_fixedPiece_le (pow_apply_smul hαβ j) F₀ ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 ((β ^ (j : ℕ)).injective (hmem.trans (map_one _).symm))

theorem pow_le_card_of_equivariant [Finite A] [Finite V] {s p r : ℕ} [Fact s.Prime]
    [Fact p.Prime] (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hA2 : p ^ 2 ≤ Nat.card A)
    (hV : IsPGroup s V) (hnt : ∃ a : A, ∃ v : V, a • v ≠ v) {α : MulAut A} {β : MulAut V}
    (hαβ : ∀ a v, β (a • v) = α a • β v)
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ F : Subgroup A, F.map (α ^ k).toMonoidHom = F →
      F = ⊥ ∨ F = ⊤) :
    s ^ r ≤ Nat.card V := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
  obtain ⟨m, hm⟩ := hAp.exists_card_eq
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    rw [hm, hn]
    exact Nat.coprime_pow_primes m n hp hs hsp.symm
  have hpV : ¬ p ∣ Nat.card V := fun h => by
    rw [hn] at h
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨F, hinj, hF, hne⟩ := exists_injective_fixedPiece_ne_bot hA hA2 hpV hnt hαβ hirr
  simpa using pow_card_le_card_of_fixedPiece_ne_bot hp hV hcop hinj hF hne

end Orbit

section Conjugation

variable {Y : Type*} [Group Y]

theorem coe_normalizerMonoidHom_pow_apply {X : Subgroup Y} {t : Y}
    (htX : t ∈ Subgroup.normalizer (X : Set Y)) (k : ℕ) (x : X) :
    (((X.normalizerMonoidHom ⟨t, htX⟩ ^ k) x : X) : Y) = t ^ k * x * (t ^ k)⁻¹ := by
  rw [← map_pow]
  rfl

theorem eq_bot_or_eq_top_of_map_normalizerMonoidHom_pow {X : Subgroup Y} {t : Y}
    (htX : t ∈ Subgroup.normalizer (X : Set Y)) {r : ℕ}
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ Y₀ : Subgroup Y, Y₀ ≤ X →
      t ^ k ∈ Subgroup.normalizer (Y₀ : Set Y) → Y₀ = ⊥ ∨ Y₀ = X)
    (k : ℕ) (hk : ¬ r ∣ k) (F : Subgroup X)
    (hF : F.map (X.normalizerMonoidHom ⟨t, htX⟩ ^ k).toMonoidHom = F) : F = ⊥ ∨ F = ⊤ := by
  set α := X.normalizerMonoidHom ⟨t, htX⟩ ^ k with hαdef
  have hα : ∀ x : X, ((α x : X) : Y) = t ^ k * x * (t ^ k)⁻¹ :=
    coe_normalizerMonoidHom_pow_apply htX k
  have hnorm : t ^ k ∈ Subgroup.normalizer ((F.map X.subtype : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨α x, ?_, hα x⟩
      rw [← hF]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hx'eq⟩
      have hyX : y ∈ X := by
        have hmem : t ^ k * y * (t ^ k)⁻¹ ∈ X := hx'eq ▸ x'.2
        exact ((Subgroup.mem_normalizer_iff.mp (pow_mem htX k)) y).mpr hmem
      refine ⟨⟨y, hyX⟩, ?_, rfl⟩
      have h1 : α ⟨y, hyX⟩ = x' := Subtype.ext (by rw [hα]; exact hx'eq.symm)
      have h2 : α ⟨y, hyX⟩ ∈ F.map α.toMonoidHom := by rw [hF, h1]; exact hx'
      obtain ⟨z, hz, hzeq⟩ := h2
      rwa [α.injective hzeq] at hz
  rcases hirr k hk _ (Subgroup.map_subtype_le F) hnorm with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h)
  · refine Or.inr (eq_top_iff.mpr fun x _ => ?_)
    obtain ⟨z, hz, hzx⟩ := h.ge x.2
    rwa [Subtype.ext hzx] at hz

end Conjugation

end CFSG.AGLEmbedding

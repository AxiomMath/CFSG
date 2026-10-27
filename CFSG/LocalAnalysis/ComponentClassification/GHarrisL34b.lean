module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL34a

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem mem_S_of_mem_normalizer {k : G} (hk : k ∈ normalizer (D.S : Set G)) {a : ℕ}
    (hka : k ^ (2 ^ a) = 1) : k ∈ (D.S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hka)
  have hK : IsPGroup 2 (zpowers k) := IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hsup := D.S.is_maximal' (D.S.isPGroup'.to_sup_of_normal_left' hK (zpowers_le.mpr hk))
    le_sup_left
  rw [← hsup]
  exact (le_sup_right : zpowers k ≤ (D.S : Subgroup G) ⊔ zpowers k) (mem_zpowers k)

theorem exists_conj_eq_of_maps {H : Subgroup G} {k : G} (hk : ∀ x ∈ H, k⁻¹ * x * k ∈ H) :
    ∀ y ∈ H, ∃ x ∈ H, k⁻¹ * x * k = y := by
  let φ : H → H := fun x => ⟨k⁻¹ * x * k, hk x x.2⟩
  have hφ : Function.Injective φ := by
    intro x₁ x₂ h
    have h' : k⁻¹ * (x₁ : G) * k = k⁻¹ * x₂ * k := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h')
  intro y hy
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

omit [Finite G] in
theorem gen4_mem_E : D.toG (SE.gen 4) ∈ D.E := (D.toG_mem_E_iff).mpr (by decide)

omit [Finite G] in
theorem gen4_not_mem_F : D.toG (SE.gen 4) ∉ D.F := by
  rw [D.toG_mem_F_iff]
  decide

theorem not_conj_E_le_F {g : G} (hg : g ∈ D.M)
    (h : ∀ e ∈ D.E, g⁻¹ * e * g ∈ D.F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : ∀ f ∈ D.F, ∃ e ∈ D.E, g⁻¹ * e * g = f := by
    have hle : D.E.map (MulAut.conj g⁻¹).toMonoidHom ≤ D.F := by
      rintro _ ⟨e, he, rfl⟩
      change g⁻¹ * e * g⁻¹⁻¹ ∈ D.F
      rw [inv_inv]
      exact h e he
    have heq : D.E.map (MulAut.conj g⁻¹).toMonoidHom = D.F := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective,
        card_map_of_injective D.toG_injective, card_map_of_injective D.toG_injective,
        SE.card_Esub, SE.card_Fsub])
    intro f hf
    rw [← heq] at hf
    obtain ⟨e, he, hef⟩ := hf
    refine ⟨e, he, ?_⟩
    rw [← hef]
    change g⁻¹ * e * g = g⁻¹ * e * g⁻¹⁻¹
    rw [inv_inv]
  set K := D.M ⊓ normalizer (D.F : Set G) with hK
  have hSK : (D.S : Subgroup G) ≤ K := fun s hs => mem_inf.mpr ⟨D.S_le_M hs,
    mem_normalizer_of_conj (fun f hf => by
      have := D.conj_mem_F (inv_mem hs) hf
      rwa [inv_inv] at this) fun f hf => D.conj_mem_F hs hf⟩
  set Sg := (D.S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom with hSg
  have hSgK : Sg ≤ K := by
    rintro _ ⟨s, hs, rfl⟩
    change g⁻¹ * s * g⁻¹⁻¹ ∈ K
    rw [inv_inv]
    refine mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) (D.S_le_M hs)) hg, ?_⟩
    have hconj : ∀ s' ∈ (D.S : Subgroup G), ∀ f ∈ D.F,
        (g⁻¹ * s' * g)⁻¹ * f * (g⁻¹ * s' * g) ∈ D.F := by
      intro s' hs' f hf
      obtain ⟨e, he, rfl⟩ := hsurj f hf
      rw [show (g⁻¹ * s' * g)⁻¹ * (g⁻¹ * e * g) * (g⁻¹ * s' * g) =
        g⁻¹ * (s'⁻¹ * e * s') * g by group]
      exact h _ (D.conj_mem_E hs' he)
    refine mem_normalizer_of_conj (fun f hf => ?_) (hconj s hs)
    have := hconj s⁻¹ (inv_mem hs) f hf
    rw [show (g⁻¹ * s⁻¹ * g)⁻¹ = g⁻¹ * s * g by group] at this
    rw [show (g⁻¹ * s * g)⁻¹ = g⁻¹ * s⁻¹ * g by group]
    exact this
  have hSyl : IsSylowOf 2 (D.S : Subgroup G) K := (isSylowOf_top D.S).of_le hSK le_top
  have hSylg : IsSylowOf 2 Sg K := by
    have hP : IsSylowOf 2 Sg ⊤ := isSylowOf_of_card le_top (by
      rw [hSg, card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective, (isSylowOf_top D.S).card_eq])
    exact hP.of_le hSgK le_top
  obtain ⟨c, hcK, hc⟩ := exists_conj_eq_of_isSylowOf hSyl hSylg
  obtain ⟨hcM, hcF⟩ := mem_inf.mp hcK
  set k := g * c⁻¹ with hk
  have hkM : k ∈ D.M := mul_mem hg (inv_mem hcM)
  have hkS : ∀ s ∈ (D.S : Subgroup G), k⁻¹ * s * k ∈ (D.S : Subgroup G) := by
    intro s hs
    have := (hc (g⁻¹ * s * g)).mp ⟨s, hs, by change g⁻¹ * s * g⁻¹⁻¹ = _; rw [inv_inv]⟩
    rwa [show c * (g⁻¹ * s * g) * c⁻¹ = k⁻¹ * s * k by rw [hk]; group] at this
  have hkS' : ∀ s ∈ (D.S : Subgroup G), k * s * k⁻¹ ∈ (D.S : Subgroup G) := by
    intro s hs
    have h1 : c * (c⁻¹ * s * c) * c⁻¹ ∈ (D.S : Subgroup G) := by
      rwa [show c * (c⁻¹ * s * c) * c⁻¹ = s by group]
    obtain ⟨s', hs', hs'eq⟩ := (hc _).mpr h1
    change g⁻¹ * s' * g⁻¹⁻¹ = c⁻¹ * s * c at hs'eq
    rw [inv_inv] at hs'eq
    have hs' : s = c * (g⁻¹ * s' * g) * c⁻¹ := by rw [hs'eq]; group
    have hks : k * s * k⁻¹ = s' := by rw [hk, hs']; group
    rwa [hks]
  have hkN : k ∈ normalizer (D.S : Set G) := mem_normalizer_of_conj hkS' hkS
  have hkE : ∀ e ∈ D.E, k⁻¹ * e * k ∈ D.F := by
    intro e he
    rw [show k⁻¹ * e * k = c * (g⁻¹ * e * g) * c⁻¹ by rw [hk]; group]
    have := conj_mem_of_mem_normalizer (inv_mem hcF) (h e he)
    rwa [inv_inv] at this
  have hkF : ∀ f ∈ D.F, k⁻¹ * f * k ∈ D.E := by
    rcases D.conj_F_le_E_or_F hkM (fun f hf => hkS f (D.F_le_S hf)) with h' | h'
    · exact h'
    · exfalso
      obtain ⟨f, hf, hfe⟩ := exists_conj_eq_of_maps h' _ (hkE _ D.gen4_mem_E)
      have : f = D.toG (SE.gen 4) := by simpa using hfe
      exact D.gen4_not_mem_F (this ▸ hf)
  have hpow : ∀ j : ℕ, ((∀ e ∈ D.E, (k ^ (2 * j))⁻¹ * e * k ^ (2 * j) ∈ D.E) ∧
      ∀ f ∈ D.F, (k ^ (2 * j))⁻¹ * f * k ^ (2 * j) ∈ D.F) ∧
      (∀ e ∈ D.E, (k ^ (2 * j + 1))⁻¹ * e * k ^ (2 * j + 1) ∈ D.F) ∧
      ∀ f ∈ D.F, (k ^ (2 * j + 1))⁻¹ * f * k ^ (2 * j + 1) ∈ D.E := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨fun e he => by simpa using he, fun f hf => by simpa using hf⟩, ?_, ?_⟩
      · intro e he; simpa using hkE e he
      · intro f hf; simpa using hkF f hf
    | succ j ih =>
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ih
      have e1 : ∀ x : G, (k ^ (2 * (j + 1)))⁻¹ * x * k ^ (2 * (j + 1)) =
          k⁻¹ * ((k ^ (2 * j + 1))⁻¹ * x * k ^ (2 * j + 1)) * k := by
        intro x
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ]
        group
      have e2 : ∀ x : G, (k ^ (2 * (j + 1) + 1))⁻¹ * x * k ^ (2 * (j + 1) + 1) =
          k⁻¹ * ((k ^ (2 * (j + 1)))⁻¹ * x * k ^ (2 * (j + 1))) * k := by
        intro x
        rw [pow_succ]
        group
      have h1' : ∀ e ∈ D.E, (k ^ (2 * (j + 1)))⁻¹ * e * k ^ (2 * (j + 1)) ∈ D.E := fun e he => by
        rw [e1]; exact hkF _ (h3 e he)
      have h2' : ∀ f ∈ D.F, (k ^ (2 * (j + 1)))⁻¹ * f * k ^ (2 * (j + 1)) ∈ D.F := fun f hf => by
        rw [e1]; exact hkE _ (h4 f hf)
      refine ⟨⟨h1', h2'⟩, fun e he => ?_, fun f hf => ?_⟩
      · rw [e2]; exact hkE _ (h1' e he)
      · rw [e2]; exact hkF _ (h2' f hf)
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  obtain ⟨j, rfl⟩ := hm
  have hkmS : k ^ (2 * j + 1) ∈ (D.S : Subgroup G) := by
    refine D.mem_S_of_mem_normalizer (pow_mem hkN _) (a := a) ?_
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hEE : ∀ e ∈ D.E, (k ^ (2 * j + 1))⁻¹ * e * k ^ (2 * j + 1) ∈ D.E := fun e he =>
    D.conj_mem_E hkmS he
  obtain ⟨e, he, hee⟩ := exists_conj_eq_of_maps hEE _ D.gen4_mem_E
  exact D.gen4_not_mem_F (hee ▸ (hpow j).2.1 e he)

theorem conj_E_mem_E {g : G} (hg : g ∈ D.M)
    (hS : ∀ e ∈ D.E, g⁻¹ * e * g ∈ (D.S : Subgroup G)) : ∀ e ∈ D.E, g⁻¹ * e * g ∈ D.E :=
  (D.conj_E_le_E_or_F hg hS).resolve_right (D.not_conj_E_le_F hg)

theorem conj_F_mem_F {g : G} (hg : g ∈ D.M)
    (hS : ∀ f ∈ D.F, g⁻¹ * f * g ∈ (D.S : Subgroup G)) : ∀ f ∈ D.F, g⁻¹ * f * g ∈ D.F := by
  refine (D.conj_F_le_E_or_F hg hS).resolve_left fun h => ?_
  refine D.not_conj_E_le_F (g := g⁻¹) (inv_mem hg) fun e he => ?_
  obtain ⟨f, hf, rfl⟩ := exists_conj_eq_of_maps_le h e he
  rw [show g⁻¹⁻¹ * (g⁻¹ * f * g) * g⁻¹ = f by group]
  exact hf
where
  exists_conj_eq_of_maps_le (h : ∀ f ∈ D.F, g⁻¹ * f * g ∈ D.E) :
      ∀ e ∈ D.E, ∃ f ∈ D.F, g⁻¹ * f * g = e := by
    have hle : D.F.map (MulAut.conj g⁻¹).toMonoidHom ≤ D.E := by
      rintro _ ⟨f, hf, rfl⟩
      change g⁻¹ * f * g⁻¹⁻¹ ∈ D.E
      rw [inv_inv]
      exact h f hf
    have heq : D.F.map (MulAut.conj g⁻¹).toMonoidHom = D.E := eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective,
        card_map_of_injective D.toG_injective, card_map_of_injective D.toG_injective,
        SE.card_Esub, SE.card_Fsub])
    intro e he
    rw [← heq] at he
    obtain ⟨f, hf, hfe⟩ := he
    refine ⟨f, hf, ?_⟩
    rw [← hfe]
    change g⁻¹ * f * g = g⁻¹ * f * g⁻¹⁻¹
    rw [inv_inv]

end GHSylow

end CFSG.ComponentClassification.GHarris

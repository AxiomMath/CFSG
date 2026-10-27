module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12D

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Sporadic.Schreier

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {Δ : Set (Subgroup G)}

omit [Finite G] [N.Normal] in
@[expose] def Corr (e : ↥N ≃* ↥NativeSporadic.M12) (K : Subgroup G) (b : Bool) : Prop :=
  ∀ y : Equiv.Perm (Fin 12), y ∈ qL b ↔
    ∃ k : ↥N, (k : G) ∈ K ∧ ((e k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = y

omit [Finite G] [N.Normal] in
theorem eq_of_corr (e : ↥N ≃* ↥NativeSporadic.M12) {K K' : Subgroup G} (hKN : K ≤ N)
    {b : Bool} (h : Corr e K b) (h' : Corr e K' b) : K ≤ K' := by
  intro k hk
  obtain ⟨k', hk', hkk⟩ := (h' _).1 ((h _).2 ⟨⟨k, hKN hk⟩, hk, rfl⟩)
  have h1 : k' = ⟨k, hKN hk⟩ := e.injective (Subtype.ext hkk)
  rw [← show (k' : G) = k from congrArg Subtype.val h1]
  exact hk'

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  let f : ↥H → ↥H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨x, hx⟩ := hsurj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (x : G) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hx
  have h2 : (x : G) = y := by simpa using h1
  rw [← h2]
  exact x.2


namespace Setting

theorem corr_of_rep (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ)
    (hz : IsUniqueInvolution K (S.e.symm r1 : G)) : ∃ b, Corr S.e K b := by
  have hKN := S.le_of_rep hK hz
  obtain ⟨eK⟩ := S.exists_equiv hK
  let ιN : QuaternionGroup 2 →* ↥N := (Subgroup.inclusion hKN).comp eK.symm.toMonoidHom
  let f : QuaternionGroup 2 →* Equiv.Perm (Fin 12) :=
    NativeSporadic.M12.subtype.comp (S.e.toMonoidHom.comp ιN)
  have hf : Function.Injective f := NativeSporadic.M12.subtype_injective.comp
    (S.e.injective.comp ((Subgroup.inclusion_injective hKN).comp eK.symm.injective))
  have ha2 : f (QuaternionGroup.a 2) = m12Rep1 := by
    have h1 : ιN (QuaternionGroup.a 2) = S.e.symm r1 := Subtype.ext (coe_symm_a_two eK hz)
    show ((S.e (ιN (QuaternionGroup.a 2)) : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = _
    rw [h1, MulEquiv.apply_symm_apply, coe_r1]
  have hroot : ∀ p : QuaternionGroup 2, p * p = QuaternionGroup.a 2 → f p * f p = m12Rep1 :=
    fun p hp => by rw [← map_mul, hp, ha2]
  have hM : ∀ p, f p ∈ NativeSporadic.M12 := fun p => (S.e (ιN p)).2
  have hnc : f (QuaternionGroup.a 1) * f (QuaternionGroup.xa 0) ≠
      f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) := by
    rw [← map_mul, ← map_mul]
    exact fun h => absurd (hf h) (by decide)
  obtain ⟨b, hb1, hb2⟩ :=
    qL_same (hM _) (hroot _ (by decide)) (hM _) (hroot _ (by decide)) hnc
  have hall : ∀ p, f p ∈ qL b := fun p => q8L_mem hb1 hb2 (mem_q8L_map f (mem_q8L_quat p))
  refine ⟨b, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · have hsub : Finset.univ.image f ⊆ (qL b).toFinset := fun y hy => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact List.mem_toFinset.2 (hall p)
    have hcard : (qL b).toFinset.card ≤ (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, QuaternionGroup.card]
      exact (List.toFinset_card_le _).trans ((qL_length b).trans (by norm_num)).le
    have hy' : y ∈ Finset.univ.image f := by
      rw [Finset.eq_of_subset_of_card_le hsub hcard]
      exact List.mem_toFinset.2 hy
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy'
    exact ⟨ιN p, (eK.symm p).2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have h1 : ιN (eK ⟨k, hk⟩) = k := by
      show Subgroup.inclusion hKN (eK.symm (eK ⟨k, hk⟩)) = k
      rw [MulEquiv.symm_apply_apply]
      rfl
    have h2 := hall (eK ⟨k, hk⟩)
    rwa [show f (eK ⟨k, hk⟩) = ((S.e k : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) by
      show ((S.e (ιN (eK ⟨k, hk⟩)) : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = _
      rw [h1]] at h2

theorem conj_of_corr (S : Setting N Δ) {K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ Δ) (hK₁ : K₁ ∈ Δ)
    (hK₀N : K₀ ≤ N) (h₀ : Corr S.e K₀ false) (h₁ : Corr S.e K₁ true) {z₀ z₁ : G}
    (hz₀ : IsUniqueInvolution K₀ z₀) (hz₁ : IsUniqueInvolution K₁ z₁) :
    ∃ c : G, conjSub c K₀ = K₁ := by
  obtain ⟨g, hg, x, hx, y, hy, hu1, hu2, hun, hvn⟩ := wit_spec
  obtain ⟨xk, hxk, hxe⟩ := (h₁ x).1 hx
  obtain ⟨yk, hyk, hye⟩ := (h₁ y).1 hy
  set gN : ↥N := S.e.symm ⟨g, hg⟩ with hgN
  have hge : ((S.e gN : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = g := by
    rw [hgN, MulEquiv.apply_symm_apply]
  have hconj : ∀ a b : ↥N, ((S.e (a * b * a⁻¹) : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
      (S.e a : Equiv.Perm (Fin 12)) * (S.e b : Equiv.Perm (Fin 12)) *
        ((S.e a : Equiv.Perm (Fin 12)))⁻¹ := fun a b => by simp
  have hnorm : ∀ w : ↥N, (w : G) ∈ Subgroup.normalizer (K₀ : Set G) ↔ ∀ a ∈ qL false,
      (S.e w : Equiv.Perm (Fin 12)) * a * ((S.e w : Equiv.Perm (Fin 12)))⁻¹ ∈ qL false := by
    intro w
    constructor
    · intro hw a ha
      obtain ⟨k, hk, rfl⟩ := (h₀ a).1 ha
      rw [← hconj]
      exact (h₀ _).2 ⟨w * k * w⁻¹, (Subgroup.mem_normalizer_iff.mp hw k).mp hk, rfl⟩
    · intro hw
      refine mem_normalizer_of_conj_mem fun k hk => ?_
      obtain ⟨k', hk', hke⟩ := (h₀ _).1 (hw _ ((h₀ _).2 ⟨⟨k, hK₀N hk⟩, hk, rfl⟩))
      rw [← hconj] at hke
      rw [S.e.injective (Subtype.ext hke)] at hk'
      exact hk'
  set K₂ := conjSub (gN : G) K₁ with hK₂def
  have hK₂ : K₂ ∈ Δ := S.hyp.hyp.conjInvariant _ K₁ hK₁
  set u : ↥N := gN * xk * gN⁻¹ with hu
  set v : ↥N := gN * yk * gN⁻¹ with hv
  have huK₂ : (u : G) ∈ K₂ := conj_mem_conjSub hxk
  have hvK₂ : (v : G) ∈ K₂ := conj_mem_conjSub hyk
  have hue : ((S.e u : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = g * x * g⁻¹ := by
    rw [hu, hconj, hge, hxe]
  have hve : ((S.e v : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = g * y * g⁻¹ := by
    rw [hv, hconj, hge, hye]
  have huN : (u : G) ∈ Subgroup.normalizer (K₀ : Set G) := (hnorm u).2 (by rw [hue]; exact hun)
  have hvN : (v : G) ∉ Subgroup.normalizer (K₀ : Set G) := fun h =>
    hvn (by rw [← hve]; exact (hnorm v).1 h)
  have hu4 : orderOf (u : G) = 4 := by
    have h4 : (u : G) ^ 2 ^ (1 + 1) = 1 := S.pow_four hK₂ huK₂
    have h2 : ¬ (u : G) ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      intro h
      apply hu2
      have h3 : u * u = 1 := Subtype.ext h
      rw [← hue, ← Subgroup.coe_mul, ← map_mul, h3, map_one, Subgroup.coe_one]
    exact orderOf_eq_prime_pow h2 h4
  have hUK₂ : Subgroup.zpowers (u : G) ≤ K₂ := Subgroup.zpowers_le.mpr huK₂
  have hK₂8 := S.card_eq hK₂
  have hUrel : (Subgroup.zpowers (u : G)).relIndex K₂ = 2 := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (u : G)) K₂
    rw [inf_eq_left.mpr hUK₂, Nat.card_zpowers, hu4, hK₂8] at h1
    omega
  have hUS : Subgroup.zpowers (u : G) ∈ USet Δ :=
    ⟨K₂, mem_RSet_of_isSylow2In hK₂ (TL4.Vtx.isSylow2In_self (S.isPGroup hK₂)), hUK₂,
      inferInstance, hUrel⟩
  have hne : K₂ ≠ K₀ := fun h => hvN (Subgroup.le_normalizer (h ▸ hvK₂))
  have hstar : K₂ ∈ omegaStarNbr Δ K₀ :=
    ⟨hK₂, hne, _, hUS, hUK₂, Subgroup.zpowers_le.mpr huN⟩
  have hnot : K₂ ∉ omegaNbr Δ K₀ := by
    rintro ⟨-, -, R, hR, hRK₂, hRN⟩
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    obtain ⟨eR⟩ : Nonempty (↥R ≃* QuaternionGroup 2) := S.hyp.quat J hJ R hRJ
    have hR8 : Nat.card ↥R = 8 := by rw [Nat.card_congr eR.toEquiv, card_quat]
    have hRK : R = K₂ := Subgroup.eq_of_le_of_card_ge hRK₂ (by rw [hR8, hK₂8])
    exact hvN (hRN (hRK ▸ hvK₂))
  obtain ⟨c, -, hc⟩ := S.hyp.aEmpty K₀ hK₀ K₂ hstar hnot z₀ _ hz₀ (hz₁.conj (gN : G))
  refine ⟨(gN : G)⁻¹ * c, ?_⟩
  rw [conjSub_mul, hc, hK₂def, conjSub_inv_conjSub]

end Setting

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

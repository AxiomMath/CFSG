module

public import CFSG.CGT.Timmesfeld75.ListWCLin

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open Equiv Equiv.Perm

theorem conjSubgroup_comap_eq {H G : Type*} [Group H] [Group G] {f : H →* G} {T : Subgroup G}
    {h : H} (hc : conjSubgroup (f h) T = T) : conjSubgroup h (T.comap f) = T.comap f := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_comap, Subgroup.mem_comap]
  constructor
  · intro hx
    have h1 : f x ∈ conjSubgroup (f h) T := by
      rw [mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul]
      exact hx
    rwa [hc] at h1
  · intro hx
    rw [← hc, mem_conjSubgroup] at hx
    rwa [map_mul, map_mul, map_inv]

theorem IsWC.comap_of_injective {H G : Type*} [Group H] [Group G] {f : H →* G}
    (hf : Function.Injective f) {T : Subgroup G} (hT : IsWC T) (hTf : T ≤ f.range) :
    IsWC (T.comap f) := by
  have hmap : (T.comap f).map f = T := Subgroup.map_comap_eq_self hTf
  have hel : IsElemAbelian 2 (T.comap f) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact elemAbelian_mul_comm hT.1 a.2 b.2
    · rw [map_pow, map_one]
      exact hT.1.2 _ hx
  refine ⟨hel, fun t ht ht1 => ⟨fun x hx => ?_, fun h hh => ?_⟩⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact elemAbelian_mul_comm hel hx ht
  · have hft1 : f t ≠ 1 := fun h1 => ht1 (hf (h1.trans (map_one f).symm))
    have hc : conjSubgroup (f h) T = T := by
      refine (hT.2 (f t) ht hft1).2 (f h) ?_
      rw [← hmap, ← map_conjSubgroup]
      rintro _ ⟨y, hy, rfl⟩
      have hyc := hh hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      rw [← map_mul, ← map_mul, hyc]
    exact conjSubgroup_comap_eq hc

noncomputable abbrev ext89 : Perm (Fin 8) →* Perm (Fin 9) :=
  extendDomainHom (finSuccAboveEquiv (0 : Fin 9))

noncomputable def alt8to9 : alternatingGroup (Fin 8) →* alternatingGroup (Fin 9) :=
  (ext89.comp (alternatingGroup (Fin 8)).subtype).codRestrict (alternatingGroup (Fin 9))
    fun σ => by
      rw [mem_alternatingGroup, MonoidHom.comp_apply, Subgroup.coe_subtype,
        extendDomainHom_apply, sign_extendDomain]
      exact σ.2

theorem alt8to9_injective : Function.Injective alt8to9 := fun _ _ h =>
  Subtype.ext (extendDomainHom_injective _ (congrArg Subtype.val h))

theorem mem_range_alt8to9 {τ : alternatingGroup (Fin 9)} (hτ : (τ : Perm (Fin 9)) 0 = 0) :
    τ ∈ alt8to9.range := by
  set f := finSuccAboveEquiv (0 : Fin 9)
  have hp : ∀ x : Fin 9, (τ : Perm (Fin 9)) x ≠ 0 ↔ x ≠ 0 := fun x => by
    constructor
    · intro hx h
      exact hx (by rw [h, hτ])
    · intro hx h
      exact hx ((τ : Perm (Fin 9)).injective (h.trans hτ.symm))
  let σ : Perm (Fin 8) := (f.permCongr).symm ((τ : Perm (Fin 9)).subtypePerm hp)
  have hσ : extendDomain σ f = (τ : Perm (Fin 9)) := by
    ext b
    by_cases hb : b ≠ 0
    · rw [extendDomain_apply_subtype σ f hb]
      simp [σ]
    · rw [extendDomain_apply_not_subtype σ f hb]
      push Not at hb
      rw [hb, hτ]
  have hσA : σ ∈ alternatingGroup (Fin 8) := by
    rw [mem_alternatingGroup, ← sign_extendDomain σ f, hσ]
    exact τ.2
  exact ⟨⟨σ, hσA⟩, Subtype.ext hσ⟩

theorem exists_fixed_point_of_isPGroup_nine {T : Subgroup (alternatingGroup (Fin 9))}
    (hT : IsPGroup 2 T) : ∃ p : Fin 9, ∀ t ∈ T, (t : Perm (Fin 9)) p = p := by
  have h := hT.card_modEq_card_fixedPoints (α := Fin 9)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hne : Nat.card (MulAction.fixedPoints T (Fin 9)) ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (by decide)
  obtain ⟨⟨p, hp⟩⟩ := Nat.card_ne_zero.1 hne |>.1
  exact ⟨p, fun t ht => hp ⟨t, ht⟩⟩

theorem alt9_wc {G : Type} [Group G] (e : G ≃* alternatingGroup (Fin 9)) {T : Subgroup G}
    (hT : IsWC T) (hT1 : T ≠ ⊥) :
    Nat.card T = 8 ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → IsConj x y := by
  suffices key : ∀ T₁ : Subgroup (alternatingGroup (Fin 9)), IsWC T₁ → T₁ ≠ ⊥ →
      Nat.card T₁ = 8 ∧ ∀ x ∈ T₁, x ≠ 1 → ∀ y ∈ T₁, y ≠ 1 → IsConj x y by
    obtain ⟨hc, hconj⟩ := key (T.map e.toMonoidHom) (hT.map_mulEquiv e)
      (fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h))
    exact ⟨by rw [← hc, Subgroup.card_map_of_injective e.injective],
      isConj_of_map_mulEquiv e hconj⟩
  intro T₁ hT₁ hT₁1
  obtain ⟨p, hp⟩ := exists_fixed_point_of_isPGroup_nine (isPGroup_two_of_isElemAbelian hT₁.1)
  have : MulAction.IsPretransitive (alternatingGroup (Fin 9)) (Fin 9) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 9) (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 9)) p 0
  have hgp : (g : Perm (Fin 9)) p = 0 := hg
  have hT₂ : IsWC (conjSubgroup g T₁) := hT₁.conj g
  have hT₂1 : conjSubgroup g T₁ ≠ ⊥ := fun h => hT₁1 (by
    rw [← conjSubgroup_inj (g := g), h]
    exact (Subgroup.map_bot _).symm)
  have hfix : ∀ t ∈ conjSubgroup g T₁, (t : Perm (Fin 9)) 0 = 0 := by
    intro t ht
    rw [mem_conjSubgroup] at ht
    have h1 := hp _ ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hgp] at h1
    rw [Equiv.Perm.inv_eq_iff_eq, hgp] at h1
    exact h1
  have hle : conjSubgroup g T₁ ≤ alt8to9.range := fun t ht => mem_range_alt8to9 (hfix t ht)
  have hT₃ := hT₂.comap_of_injective alt8to9_injective hle
  have hmap : ((conjSubgroup g T₁).comap alt8to9).map alt8to9 = conjSubgroup g T₁ :=
    Subgroup.map_comap_eq_self hle
  have hT₃1 : (conjSubgroup g T₁).comap alt8to9 ≠ ⊥ := fun h =>
    hT₂1 (by rw [← hmap, h, Subgroup.map_bot])
  obtain ⟨hc₃, hconj₃⟩ := alt8_wc (MulEquiv.refl _) hT₃ hT₃1
  refine ⟨?_, fun x hx hx1 y hy hy1 => ?_⟩
  · rw [← card_conjSubgroup g T₁, ← hmap, Subgroup.card_map_of_injective alt8to9_injective, hc₃]
  · have hmem : ∀ z ∈ T₁, g * z * g⁻¹ ∈ conjSubgroup g T₁ := fun z hz => by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hz
    have hx' := hmem x hx
    have hy' := hmem y hy
    rw [← hmap] at hx' hy'
    obtain ⟨x', hx'T, hx'e⟩ := hx'
    obtain ⟨y', hy'T, hy'e⟩ := hy'
    have hne : ∀ {z' : alternatingGroup (Fin 8)} {z : alternatingGroup (Fin 9)},
        alt8to9 z' = g * z * g⁻¹ → z ≠ 1 → z' ≠ 1 := fun {z'} {z} hz' hz1 h => hz1 (by
      rw [h, map_one] at hz'
      have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
      rw [this, ← hz']
      group)
    have hc := MonoidHom.map_isConj alt8to9
      (hconj₃ x' hx'T (hne hx'e hx1) y' hy'T (hne hy'e hy1))
    rw [hx'e, hy'e] at hc
    exact (isConj_iff.2 ⟨g, rfl⟩).trans (hc.trans (isConj_iff.2 ⟨g, rfl⟩).symm)

end CFSG.CGT.Timmesfeld75

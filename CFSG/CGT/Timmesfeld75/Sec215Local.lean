module

public import CFSG.CGT.Timmesfeld75.Config214

public section

namespace CFSG.CGT.Timmesfeld75

open scoped commutatorElement

section Auxiliary

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

private theorem Cfg.eq_of_comm_eq (c : Cfg T T₁) {x : G} (hx : x ∈ T) (hxL : x ∉ normIn T T₁)
    {y y' : G} (hy : y ∈ normIn T₁ T) (hy' : y' ∈ normIn T₁ T) (h : ⁅x, y⁆ = ⁅x, y'⁆) :
    y = y' := by
  have hxM : x ∉ cfgM T T₁ := fun hM => hxL (by rw [← c.inf_cfgM]; exact ⟨hx, hM⟩)
  have hwL₁ : y'⁻¹ * y ∈ normIn T₁ T := (normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem hy') hy
  have hcomm : ⁅x, y'⁻¹ * y⁆ = 1 := by
    have e : ⁅x, y'⁻¹ * y⁆ = (x * y'⁻¹ * x⁻¹) * ⁅x, y⁆ * y' := by
      simp only [commutatorElement_def]; group
    have e' : (x * y'⁻¹ * x⁻¹) * ⁅x, y'⁆ * y' = 1 := by
      simp only [commutatorElement_def]; group
    rw [e, h, e']
  have hwC : y'⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 hcomm).symm
  have hwL : y'⁻¹ * y ∈ normIn T T₁ := by
    rw [← c.cfgM_inf_centralizer hx hxM]
    exact ⟨Cfg.normIn_le_cfgM_right T T₁ hwL₁, hwC⟩
  have hw1 : y'⁻¹ * y ∈ T ⊓ T₁ := ⟨normIn_le _ _ hwL, normIn_le _ _ hwL₁⟩
  rw [c.inf, Subgroup.mem_bot] at hw1
  exact (inv_mul_eq_one.1 hw1).symm

private theorem Cfg.injective_comm (c : Cfg T T₁) {x : G} (hx : x ∈ T) (hxL : x ∉ normIn T T₁) :
    Function.Injective
      (fun y : normIn T₁ T => (⟨⁅x, (y : G)⁆, c.comm_mem_normIn hx y.2⟩ : normIn T T₁)) :=
  fun y y' h => Subtype.ext (c.eq_of_comm_eq hx hxL y.2 y'.2 (congrArg Subtype.val h))

private theorem commutator_sup_normal_le {T N : Subgroup G} [N.Normal]
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : ⁅T ⊔ N, T ⊔ N⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨t₁, ht₁, ν₁, hν₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₁
  obtain ⟨t₂, ht₂, ν₂, hν₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₂
  have h1 : QuotientGroup.mk' N ν₁ = 1 := (QuotientGroup.eq_one_iff ν₁).2 hν₁
  have h2 : QuotientGroup.mk' N ν₂ = 1 := (QuotientGroup.eq_one_iff ν₂).2 hν₂
  have h3 : QuotientGroup.mk' N t₁ * QuotientGroup.mk' N t₂ =
      QuotientGroup.mk' N t₂ * QuotientGroup.mk' N t₁ := by
    rw [← map_mul, ← map_mul, hT t₁ ht₁ t₂ ht₂]
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' N ⁅t₁ * ν₁, t₂ * ν₂⁆ = 1
  rw [map_commutatorElement, map_mul, map_mul, h1, h2, mul_one, mul_one]
  exact commutatorElement_eq_one_iff_mul_comm.2 h3

private theorem conjSubgroup_le_sup_normal {T N : Subgroup G} [N.Normal] {n : G} (hn : n ∈ N) :
    conjSubgroup n T ≤ T ⊔ N := by
  intro y hy
  have ht : n⁻¹ * y * n ∈ T := mem_conjSubgroup.1 hy
  have hν : n * ((n⁻¹ * y * n) * n⁻¹ * (n⁻¹ * y * n)⁻¹) ∈ N :=
    N.mul_mem hn (Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hn) _)
  have e : y = n * ((n⁻¹ * y * n) * n⁻¹ * (n⁻¹ * y * n)⁻¹) * (n⁻¹ * y * n) := by group
  have hνT : n * ((n⁻¹ * y * n) * n⁻¹ * (n⁻¹ * y * n)⁻¹) ∈ T ⊔ N := Subgroup.mem_sup_right hν
  have h := Subgroup.mul_mem _ hνT (Subgroup.mem_sup_left ht)
  rwa [← e] at h

end Auxiliary

section Local

variable {G : Type*} [Group G] [Finite G] {T T₁ : Subgroup G}

private theorem Cfg.card_normIn_right_le (c : Cfg T T₁) {x : G} (hx : x ∈ T)
    (hxL : x ∉ normIn T T₁) : Nat.card (normIn T₁ T) ≤ Nat.card (normIn T T₁) :=
  Nat.card_le_card_of_injective _ (c.injective_comm hx hxL)

theorem Cfg.card_normIn_eq (c : Cfg T T₁) (hconj : ∃ x : G, T₁ = conjSubgroup x T) :
    Nat.card (normIn T T₁) = Nat.card (normIn T₁ T) := by
  obtain ⟨x, hx⟩ := hconj
  have hconj' : ∃ x' : G, T = conjSubgroup x' T₁ :=
    ⟨x⁻¹, by rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
  obtain ⟨u, huT, huL⟩ := IsConcreteLE.exists_of_lt (c.normIn_lt ⟨x, hx⟩)
  obtain ⟨v, hvT₁, hvL₁⟩ := IsConcreteLE.exists_of_lt (c.symm.normIn_lt hconj')
  exact le_antisymm (c.symm.card_normIn_right_le hvT₁ hvL₁) (c.card_normIn_right_le huT huL)

private theorem Cfg.normIn_le_commutator (c : Cfg T T₁) {x : G} (hx : x ∈ T)
    (hxL : x ∉ normIn T T₁) (hcard : Nat.card (normIn T T₁) ≤ Nat.card (normIn T₁ T)) :
    normIn T T₁ ≤ ⁅T ⊔ T₁, T ⊔ T₁⁆ := by
  intro l hl
  obtain ⟨y, hy⟩ := ((c.injective_comm hx hxL).bijective_of_nat_card_le hcard).2 ⟨l, hl⟩
  have hyl : ⁅x, (y : G)⁆ = l := congrArg Subtype.val hy
  rw [← hyl]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right (normIn_le _ _ y.2))

theorem Cfg.cfgM_le_commutator (c : Cfg T T₁) (hconj : ∃ x : G, T₁ = conjSubgroup x T) :
    cfgM T T₁ ≤ ⁅T ⊔ T₁, T ⊔ T₁⁆ := by
  obtain ⟨x, hx⟩ := hconj
  have hconj' : ∃ x' : G, T = conjSubgroup x' T₁ :=
    ⟨x⁻¹, by rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
  obtain ⟨u, huT, huL⟩ := IsConcreteLE.exists_of_lt (c.normIn_lt ⟨x, hx⟩)
  obtain ⟨v, hvT₁, hvL₁⟩ := IsConcreteLE.exists_of_lt (c.symm.normIn_lt hconj')
  have hcard := c.card_normIn_eq ⟨x, hx⟩
  refine sup_le (c.normIn_le_commutator huT huL hcard.le) ?_
  have h := c.symm.normIn_le_commutator hvT₁ hvL₁ hcard.ge
  rwa [sup_comm T₁ T] at h

theorem cfgM_conj_le_normal {T : Subgroup G} (hT : IsWC T) (N : Subgroup G) [N.Normal] {n : G}
    (hn : n ∈ N) (hne : conjSubgroup n T ≠ T) (hL : normIn T (conjSubgroup n T) ≠ ⊥)
    (_hTN : ¬ T ≤ N) : cfgM T (conjSubgroup n T) ≤ N := by
  have c := Cfg.of_conj hT hne hL
  have h1 := c.cfgM_le_commutator ⟨n, rfl⟩
  have h2 : T ⊔ conjSubgroup n T ≤ T ⊔ N := sup_le le_sup_left (conjSubgroup_le_sup_normal hn)
  exact h1.trans ((Subgroup.commutator_mono h2 h2).trans
    (commutator_sup_normal_le fun x hx y hy => elemAbelian_mul_comm hT.1 hx hy))

theorem commute_conj_mem_of_not_mem_normal {T : Subgroup G} (hT : IsWC T) (N : Subgroup G)
    [N.Normal] {d : G} (hd : d ∈ T) (hdN : d ∉ N) {n : G} (hn : n ∈ N)
    (hcomm : d * (n⁻¹ * d * n) = (n⁻¹ * d * n) * d) : n⁻¹ * d * n ∈ T := by
  by_contra haT
  have hd1 : d ≠ 1 := fun h => hdN (h ▸ N.one_mem)
  have haT' : n⁻¹ * d * n ∈ conjSubgroup n⁻¹ T := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hd
  have hne : conjSubgroup n⁻¹ T ≠ T := fun h => haT (h ▸ haT')
  have ha1 : n⁻¹ * d * n ≠ 1 := by
    intro h
    apply hd1
    have e : d = n * (n⁻¹ * d * n) * n⁻¹ := by group
    rw [e, h]
    simp
  have hdN' : d ∈ Subgroup.normalizer (conjSubgroup n⁻¹ T : Set G) :=
    (hT.conj n⁻¹).centralizer_le_normalizer haT' ha1
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have hL : normIn T (conjSubgroup n⁻¹ T) ≠ ⊥ := fun h => hd1 (by
    have hdL : d ∈ normIn T (conjSubgroup n⁻¹ T) := mem_normIn.2 ⟨hd, hdN'⟩
    rw [h, Subgroup.mem_bot] at hdL
    exact hdL)
  have hM := cfgM_conj_le_normal hT N (N.inv_mem hn) hne hL fun hle => hdN (hle hd)
  have haN : n⁻¹ * d * n ∈ Subgroup.normalizer (T : Set G) :=
    hT.centralizer_le_normalizer hd hd1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have haM : n⁻¹ * d * n ∈ N :=
    hM (Cfg.normIn_le_cfgM_right T (conjSubgroup n⁻¹ T) (mem_normIn.2 ⟨haT', haN⟩))
  have e : d = n * (n⁻¹ * d * n) * n⁻¹ := by group
  exact hdN (e ▸ Subgroup.Normal.conj_mem inferInstance _ haM n)

end Local

end CFSG.CGT.Timmesfeld75

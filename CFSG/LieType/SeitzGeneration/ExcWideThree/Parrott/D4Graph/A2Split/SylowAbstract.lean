module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

section SupNormalForm

variable {G : Type*} [Group G]

theorem range_monoidHomSubgroup {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    (SemidirectProduct.monoidHomSubgroup hK).range = H ⊔ K := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.left.2) (Subgroup.mem_sup_right y.right.2)
  · refine sup_le (fun h hh => ⟨SemidirectProduct.inl ⟨h, hh⟩, ?_⟩)
      (fun k hk => ⟨SemidirectProduct.inr ⟨k, hk⟩, ?_⟩)
    · simp [SemidirectProduct.monoidHomSubgroup]
    · simp [SemidirectProduct.monoidHomSubgroup]

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  rw [← range_monoidHomSubgroup hK] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y.left, y.left.2, y.right, y.right.2, rfl⟩

theorem card_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_sup_of_le_normalizer [Finite G] {H K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (H : Set G))
    (hHK : H ⊓ K = ⊥) : Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have hinj : Function.Injective (SemidirectProduct.monoidHomSubgroup hK) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y.left : G) * y.right = 1 := hy
    have hl : (y.left : G) ∈ H ⊓ K := by
      refine ⟨y.left.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact K.inv_mem y.right.2
    rw [hHK, Subgroup.mem_bot] at hl
    have hr : (y.right : G) = 1 := by
      rw [hl, one_mul] at h1
      exact h1
    ext
    · exact hl
    · exact hr
  rw [← range_monoidHomSubgroup hK, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    SemidirectProduct.card]

end SupNormalForm

section Sylow

variable {G : Type*} [Group G]

theorem inv_mul_conj_mul (φ : MulAut G) (g : G) :
    φ⁻¹ * MulAut.conj g * φ = MulAut.conj (φ⁻¹ g) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]

theorem normal_range_conj : (MulAut.conj : G →* MulAut G).range.Normal := by
  refine ⟨fun n hn φ => ?_⟩
  obtain ⟨g, rfl⟩ := hn
  refine ⟨φ g, ?_⟩
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_normalizer_map_conj [Finite G] (α : MulAut G) (S : Subgroup G)
    (hαS : ∀ x ∈ S, α x ∈ S) : α ∈ Subgroup.normalizer
      ((S.map (MulAut.conj : G →* MulAut G) : Subgroup (MulAut G)) : Set (MulAut G)) := by
  have hsurj : ∀ y ∈ S, ∃ x ∈ S, α x = y := by
    have hinj : Function.Injective (fun x : S => (⟨α x, hαS x x.2⟩ : S)) := fun a b h =>
      Subtype.ext (α.injective (congrArg Subtype.val h))
    intro y hy
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨α g, hαS g hg, ?_⟩
    ext y
    simp only [MonoidHom.coe_coe, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulAut.apply_inv_self]
  · rintro ⟨g, hg, hgeq⟩
    obtain ⟨x, hx, rfl⟩ := hsurj g hg
    refine ⟨x, hx, ?_⟩
    have e : α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
      ext y
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    have hgeq' : MulAut.conj (α x) = α * n * α⁻¹ := hgeq
    rw [← e] at hgeq'
    exact mul_left_cancel (mul_right_cancel hgeq')

theorem inf_zpowers_eq_bot [Finite G] {p : ℕ} [hp : Fact p.Prime] {α : MulAut G}
    (hαp : α ^ p = 1) (hαout : α ∉ (MulAut.conj : G →* MulAut G).range) {H : Subgroup (MulAut G)}
    (hH : H ≤ (MulAut.conj : G →* MulAut G).range) : H ⊓ Subgroup.zpowers α = ⊥ := by
  have hα1 : α ≠ 1 := fun h => hαout (h ▸ one_mem _)
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hcard : Nat.card (Subgroup.zpowers α) = p := by rw [Nat.card_zpowers, hord]
  have hdvd : Nat.card (H ⊓ Subgroup.zpowers α : Subgroup (MulAut G)) ∣ p := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime hp.out).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    have heq : H ⊓ Subgroup.zpowers α = Subgroup.zpowers α :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
    have hmem : α ∈ H ⊓ Subgroup.zpowers α := by
      rw [heq]
      exact Subgroup.mem_zpowers α
    exact hαout (hH hmem.1)

theorem card_le_of_isPGroup_of_fixed [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) {α : MulAut G}
    (hαp : α ^ p = 1) (hαout : α ∉ (MulAut.conj : G →* MulAut G).range) {S : Subgroup G}
    (hS : Nat.card S = p ^ (Nat.card G).factorization p) (hαS : ∀ x ∈ S, α x ∈ S)
    {T : Subgroup G} (hTS : T.relIndex S ≤ p) (hT0 : T.relIndex S ≠ 0) {m : ℕ}
    (hm : ∀ s ∈ S, ∀ j : ℕ, 0 < j → j < p → ∀ F : Subgroup G, F ≤ T →
      (∀ x ∈ F, (MulAut.conj s * α ^ j) x = x) → Nat.card F ≤ m)
    {R : Subgroup G} (hR : IsPGroup p R) (hRα : ∀ x ∈ R, α x = x) : Nat.card R ≤ p * m := by
  classical
  set Inn := (MulAut.conj : G →* MulAut G).range with hInn
  have hInnN : Inn.Normal := normal_range_conj
  set Z := Subgroup.zpowers α with hZ
  have hα1 : α ≠ 1 := fun h => hαout (h ▸ one_mem _)
  have hcardZ : Nat.card Z = p := by rw [Nat.card_zpowers, orderOf_eq_prime hαp hα1]
  have hZN : ∀ H : Subgroup (MulAut G), α ∈ Subgroup.normalizer (H : Set (MulAut G)) →
      Z ≤ Subgroup.normalizer (H : Set (MulAut G)) := fun H hα =>
    (Subgroup.zpowers_le).2 hα
  have hZA : Z ≤ Subgroup.normalizer (Inn : Set (MulAut G)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hInnN]
    exact le_top
  have hcardInn : Nat.card Inn = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  set A := Inn ⊔ Z with hA
  have hcardA : Nat.card A = Nat.card G * p := by
    rw [card_sup_of_le_normalizer hZA (inf_zpowers_eq_bot hαp hαout le_rfl), hcardInn, hcardZ]
  set IS := S.map (MulAut.conj : G →* MulAut G) with hIS
  have hISInn : IS ≤ Inn := Subgroup.map_le_range _ _
  have hZIS : Z ≤ Subgroup.normalizer (IS : Set (MulAut G)) :=
    hZN _ (mem_normalizer_map_conj α S hαS)
  have hcardIS : Nat.card IS = Nat.card S :=
    (Nat.card_congr (Subgroup.equivMapOfInjective S _ hinj).toEquiv).symm
  set P := IS ⊔ Z with hP
  have hcardP : Nat.card P = Nat.card S * p := by
    rw [card_sup_of_le_normalizer hZIS (inf_zpowers_eq_bot hαp hαout hISInn), hcardIS, hcardZ]
  have hPA : P ≤ A := sup_le_sup_right hISInn _
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfacA : (Nat.card A).factorization p = (Nat.card G).factorization p + 1 := by
    rw [hcardA, Nat.factorization_mul hG0 hp.out.ne_zero, Finsupp.add_apply,
      hp.out.factorization_self]
  have hPsyl : Nat.card (P.subgroupOf A) = p ^ (Nat.card A).factorization p := by
    rw [card_subgroupOf_of_le hPA, hcardP, hS, hfacA, pow_succ]
  set PS : Sylow p A := Sylow.ofCard (P.subgroupOf A) hPsyl
  set IR := R.map (MulAut.conj : G →* MulAut G) with hIR
  have hIRInn : IR ≤ Inn := Subgroup.map_le_range _ _
  have hαIR : α ∈ Subgroup.normalizer (IR : Set (MulAut G)) :=
    mem_normalizer_map_conj α R (fun x hx => by
    rw [hRα x hx]; exact hx)
  have hcardIR : Nat.card IR = Nat.card R :=
    (Nat.card_congr (Subgroup.equivMapOfInjective R _ hinj).toEquiv).symm
  set RZ := IR ⊔ Z with hRZ
  have hcardRZ : Nat.card RZ = Nat.card R * p := by
    rw [card_sup_of_le_normalizer (hZN _ hαIR) (inf_zpowers_eq_bot hαp hαout hIRInn), hcardIR,
      hcardZ]
  have hRZA : RZ ≤ A := sup_le_sup_right hIRInn _
  have hRZp : IsPGroup p (RZ.subgroupOf A) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
    refine IsPGroup.of_card (n := k + 1) ?_
    rw [card_subgroupOf_of_le hRZA, hcardRZ, hk, pow_succ]
  obtain ⟨Q, hQ⟩ := hRZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A PS Q
  have hmemQ : ∀ x : MulAut G, x ∈ RZ → (g : MulAut G)⁻¹ * x * g ∈ P := by
    intro x hx
    have hxA : x ∈ A := hRZA hx
    have hxQ : (⟨x, hxA⟩ : A) ∈ (Q : Subgroup A) := hQ (by simpa [Subgroup.mem_subgroupOf] using hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
    have h2 := hxQ
    simp only [MulAut.smul_def, MulAut.conj_apply] at h2
    rw [Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at h2
    simpa [mul_assoc] using h2
  have hnormal : ∀ x ∈ P, ∃ s ∈ S, ∃ k : ℤ, x = MulAut.conj s * α ^ k := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hZIS hx
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ⟨s, hs, k, rfl⟩
  have hInnInv : ∀ φ : MulAut G, ∀ x ∈ Inn, φ⁻¹ * x * φ ∈ Inn := by
    intro φ x hx
    have := hInnN.conj_mem x hx φ⁻¹
    simpa [mul_assoc] using this
  obtain ⟨s, hs, k, hβ⟩ := hnormal _ (hmemQ α (Subgroup.mem_sup_right (Subgroup.mem_zpowers α)))
  set j := (k % (p : ℤ)).toNat with hj
  have hkmod : α ^ k = α ^ j := by
    have hk : k = (k % (p : ℤ)) + p * (k / p) := by
      have := Int.mul_ediv_add_emod k p
      omega
    have hnn : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)
    rw [hk, zpow_add, zpow_mul, zpow_natCast, hαp, one_zpow, mul_one, ← Int.toNat_of_nonneg hnn,
      zpow_natCast]
  have hjlt : j < p := by
    have h1 : k % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp.out.pos)
    omega
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hkmod
      rw [hkmod, mul_one] at hβ
      have h' : (g : MulAut G)⁻¹ * α * g ∈ Inn := ⟨s, hβ.symm⟩
      have := hInnInv (g : MulAut G)⁻¹ _ h'
      rw [inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right] at this
      exact hαout this
    · exact h0
  rw [hkmod] at hβ
  set ψ : MulAut G := (g : MulAut G)⁻¹
  have hRS : ∀ r ∈ R, ψ r ∈ S := by
    intro r hr
    have hx := hmemQ (MulAut.conj r) (Subgroup.mem_sup_left ⟨r, hr, rfl⟩)
    rw [inv_mul_conj_mul] at hx
    obtain ⟨s', hs', k', hk'⟩ := hnormal _ hx
    have hk'Inn : α ^ k' ∈ Inn := by
      refine ⟨s'⁻¹ * ψ r, ?_⟩
      rw [map_mul, map_inv, hk', ← mul_assoc, inv_mul_cancel, one_mul]
    have hbot := inf_zpowers_eq_bot hαp hαout (le_refl Inn)
    have hk1 : α ^ k' = 1 := by
      have : α ^ k' ∈ Inn ⊓ Z := ⟨hk'Inn, Subgroup.zpow_mem_zpowers α k'⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [hk1, mul_one] at hk'
    rw [hinj hk']
    exact hs'
  have hfix : ∀ r ∈ R, (MulAut.conj s * α ^ j) (ψ r) = ψ r := by
    intro r hr
    rw [← hβ]
    simp only [MulAut.mul_apply, ψ, MulAut.apply_inv_self, hRα r hr]
  set F := R.map ψ.toMonoidHom with hF
  have hFS : F ≤ S := by
    rintro _ ⟨r, hr, rfl⟩
    exact hRS r hr
  have hcardF : Nat.card F = Nat.card R :=
    (Nat.card_congr (Subgroup.equivMapOfInjective R _ ψ.injective).toEquiv).symm
  have hFfix : ∀ x ∈ T ⊓ F, (MulAut.conj s * α ^ j) x = x := by
    rintro x ⟨-, r, hr, rfl⟩
    exact hfix r hr
  have hTF := hm s hs j hj0 hjlt (T ⊓ F) inf_le_left hFfix
  have hidx : T.relIndex F ≤ T.relIndex S := Subgroup.relIndex_le_of_le_right hFS hT0
  have hmul := Subgroup.relIndex_mul_card (H := T) (K := F)
  rw [← hcardF, ← hmul]
  calc T.relIndex F * Nat.card (T ⊓ F : Subgroup G) ≤ p * m :=
    Nat.mul_le_mul (hidx.trans hTS) hTF

end Sylow

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

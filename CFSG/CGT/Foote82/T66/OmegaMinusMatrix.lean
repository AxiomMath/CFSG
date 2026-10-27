module

public import CFSG.CGT.Foote82.T66.CitedBAS
import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.Quasithin.Background.G11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.OmegaMinusMat

open Matrix CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}

private theorem glv_mul_apply (a b : GLV V) (v : V) : (a * b) v = a (b v) := rfl

private theorem glv_inv_apply_apply (a : GLV V) (v : V) : a⁻¹ (a v) = v :=
  a.symm_apply_apply v

private theorem glv_apply_inv_apply (a : GLV V) (v : V) : a (a⁻¹ v) = v :=
  a.apply_symm_apply v

theorem apply_mem_commSpace {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ commSpace L ⊤) :
    x w ∈ commSpace L ⊤ := by
  have hle : commSpace L ⊤ ≤ (commSpace L ⊤).comap (x : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    show x (k u - u) ∈ commSpace L ⊤
    have e : x (k u - u) = (x * k * x⁻¹) (x u) - x u := by
      rw [map_sub, glv_mul_apply, glv_mul_apply, glv_inv_apply_apply]
    rw [e]
    exact sub_mem_commSpace ((Subgroup.mem_normalizer_iff.1 hx k).1 hk) Submodule.mem_top
  exact hle hw

theorem apply_mem_fixedSpace {L : Subgroup (GLV V)} {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (L : Set (GLV V))) {w : V} (hw : w ∈ fixedSpace L) :
    x w ∈ fixedSpace L := by
  intro k hk
  have hk' : x⁻¹ * k * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) k).1 hk
    simpa using this
  have := hw _ hk'
  rw [glv_mul_apply, glv_mul_apply] at this
  have h2 := congrArg x this
  rwa [glv_apply_inv_apply] at h2

private theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {e k : G} (he : e * e = 1)
    (hk : k ∈ Subgroup.zpowers e) : k = 1 ∨ k = e := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

theorem injective_alpha {L : Subgroup (GLV V)} {α : ↥L →* ↥(omegaMinusTwo m)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)}
    (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L)
    (hrel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w)
    (hf : FaithfulTildeV L) : Function.Injective α := by
  rw [injective_iff_map_eq_one]
  intro ℓ hℓ
  refine Subtype.ext (hf ℓ ℓ.2 fun w hw => ?_)
  have hw' : (ℓ : GLV V) w ∈ commSpace L ⊤ := apply_mem_commSpace (Subgroup.le_normalizer ℓ.2) hw
  have h := hrel ℓ ⟨w, hw⟩ ⟨_, hw'⟩ rfl
  rw [hℓ, OneMemClass.coe_one, Units.val_one, one_mulVec] at h
  have h0 : β (⟨_, hw'⟩ - ⟨w, hw⟩) = 0 := by
    rw [map_sub, h, sub_self]
  exact (hβk _).1 h0

theorem exists_matrix {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)} (hβs : Function.Surjective β)
    (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L) {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1) :
    ∃ D : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2), D * D = 1 ∧
      ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w →
        β w' = (D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w := by
  let dU : ↥(commSpace L ⊤) → ↥(commSpace L ⊤) := fun w => ⟨d w, apply_mem_commSpace hd w.2⟩
  have hdU_eq : ∀ w₁ w₂, β w₁ = β w₂ → β (dU w₁) = β (dU w₂) := by
    intro w₁ w₂ h
    rw [← sub_eq_zero, ← map_sub, hβk] at h ⊢
    have e : ((dU w₁ - dU w₂ : ↥(commSpace L ⊤)) : V) =
        d ((w₁ - w₂ : ↥(commSpace L ⊤)) : V) := by
      rw [Submodule.coe_sub, Submodule.coe_sub, map_sub]
    rw [e]
    exact apply_mem_fixedSpace hd h
  have hdU_add : ∀ w₁ w₂, dU (w₁ + w₂) = dU w₁ + dU w₂ := fun w₁ w₂ =>
    Subtype.ext (map_add d (w₁ : V) w₂)
  have hdUdU : ∀ w, dU (dU w) = w := fun w => Subtype.ext (by
    show d (d w) = w
    rw [← glv_mul_apply, hdd]
    rfl)
  let w₀ := Function.surjInv hβs
  have hw₀ : ∀ x, β (w₀ x) = x := Function.surjInv_eq hβs
  let f : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    fun x => β (dU (w₀ x))
  have hf : ∀ w, f (β w) = β (dU w) := fun w => hdU_eq _ _ (hw₀ (β w))
  have hfadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have h := hf (w₀ x + w₀ y)
    rw [map_add, hw₀, hw₀, hdU_add, map_add] at h
    exact h
  let fA : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    AddMonoidHom.mk' f hfadd
  let M : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2) :=
    LinearMap.toMatrix' (fA.toZModLinearMap 2)
  have hM : ∀ x, M *ᵥ x = f x := fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hMw : ∀ w, M *ᵥ β w = β (dU w) := fun w => by rw [hM, hf]
  have hMM : M * M = 1 := by
    rw [ext_iff_mulVec]
    intro x
    obtain ⟨w, rfl⟩ := hβs x
    rw [← mulVec_mulVec, hMw, hMw, hdUdU, one_mulVec]
  refine ⟨⟨M, M, hMM, hMM⟩, Units.ext hMM, fun w w' hw' => ?_⟩
  have e : w' = dU w := Subtype.ext hw'
  rw [e]
  exact (hMw w).symm

theorem rel_mul {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)} {x y : GLV V}
    {X Y : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hy : ∀ w ∈ commSpace L ⊤, y w ∈ commSpace L ⊤)
    (hX : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = x w →
      β w' = (X : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w)
    (hY : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = y w →
      β w' = (Y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w) :
    ∀ w w' : ↥(commSpace L ⊤), (w' : V) = (x * y) w →
      β w' = ((X * Y : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w := by
  intro w w' hw'
  rw [Units.val_mul, ← mulVec_mulVec, ← hY w ⟨y w, hy _ w.2⟩ rfl]
  exact hX _ w' hw'

theorem orderOf_dvd {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)} (hβs : Function.Surjective β)
    {x : GLV V} (hx : ∀ w ∈ commSpace L ⊤, x w ∈ commSpace L ⊤)
    {X : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hX : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = x w →
      β w' = (X : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w) :
    orderOf X ∣ orderOf x := by
  have hpow : ∀ n : ℕ, (∀ w ∈ commSpace L ⊤, (x ^ n) w ∈ commSpace L ⊤) ∧
      ∀ w w' : ↥(commSpace L ⊤), (w' : V) = (x ^ n) w →
        β w' = ((X ^ n : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun w hw => hw, fun w w' hw' => ?_⟩
      have e : w' = w := Subtype.ext hw'
      rw [e, pow_zero, Units.val_one, one_mulVec]
    | succ n ih =>
      refine ⟨fun w hw => by
        rw [pow_succ', glv_mul_apply]
        exact hx _ (ih.1 w hw), ?_⟩
      rw [pow_succ', pow_succ']
      exact rel_mul ih.1 hX ih.2
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  rw [Units.val_one, ext_iff_mulVec]
  intro v
  obtain ⟨w, rfl⟩ := hβs v
  rw [one_mulVec]
  refine ((hpow (orderOf x)).2 w w ?_).symm
  rw [pow_orderOf_eq_one]
  rfl

theorem conj_eq {L : Subgroup (GLV V)} {α : ↥L →* ↥(omegaMinusTwo m)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)} (hβs : Function.Surjective β)
    (hrel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w)
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1)
    {D : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)} (hDD : D * D = 1)
    (hD : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w →
      β w' = (D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w) :
    ∀ ℓ ℓ' : ↥L, (ℓ' : GLV V) = d * ℓ * d⁻¹ →
      D * ((α ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) * D⁻¹ =
        ((α ℓ' : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) := by
  intro ℓ ℓ' hℓ'
  have hDinv : D⁻¹ = D := inv_eq_of_mul_eq_one_right hDD
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  rw [hDinv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ext_iff_mulVec]
  intro v
  obtain ⟨w, rfl⟩ := hβs v
  have hw₁ : d w ∈ commSpace L ⊤ := apply_mem_commSpace hd w.2
  have hw₂ : (ℓ : GLV V) (d w) ∈ commSpace L ⊤ :=
    apply_mem_commSpace (Subgroup.le_normalizer ℓ.2) hw₁
  have hw₃ : d ((ℓ : GLV V) (d w)) ∈ commSpace L ⊤ := apply_mem_commSpace hd hw₂
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hD w ⟨_, hw₁⟩ rfl, ← hrel ℓ ⟨_, hw₁⟩ ⟨_, hw₂⟩ rfl,
    ← hD ⟨_, hw₂⟩ ⟨_, hw₃⟩ rfl]
  refine hrel ℓ' w ⟨_, hw₃⟩ ?_
  show d ((ℓ : GLV V) (d w)) = (ℓ' : GLV V) w
  rw [hℓ', hdinv]
  rfl

theorem finrank_range_add [Finite V] {L : Subgroup (GLV V)}
    {β : ↥(commSpace L ⊤) →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)}
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L)
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hdd : d * d = 1)
    {D : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hD : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = d w →
      β w' = (D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w) :
    Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin
        ((D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) - 1))) +
        Module.finrank (ZMod 2) ↥(tildeVBot L) =
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d) := by
  have hTU : BAS.tvComm L d ≤ commSpace L ⊤ :=
    sup_le (commSpace_le_iff.2 fun k hk u hu =>
      (commSpace L ⊤).sub_mem (apply_mem_commSpace ((Subgroup.zpowers_le.2 hd) hk) hu) hu)
      inf_le_right
  let ψ : ↥(BAS.tvComm L d) →ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    (β.toZModLinearMap 2).comp (Submodule.inclusion hTU)
  have hψ : ∀ t : ↥(BAS.tvComm L d), ψ t = β ⟨t, hTU t.2⟩ := fun t => rfl
  have hdU : ∀ u ∈ commSpace L ⊤, d u - u ∈ BAS.tvComm L d := fun u hu =>
    Submodule.mem_sup_left (sub_mem_commSpace (Subgroup.mem_zpowers d) hu)
  have hβd : ∀ (u : V) (hu : u ∈ commSpace L ⊤),
      β ⟨d u - u, hTU (hdU u hu)⟩ =
        ((D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) - 1) *ᵥ
          β ⟨u, hu⟩ := by
    intro u hu
    have e : (⟨d u - u, hTU (hdU u hu)⟩ : ↥(commSpace L ⊤)) =
        ⟨d u, apply_mem_commSpace hd hu⟩ - ⟨u, hu⟩ := rfl
    rw [e, map_sub, hD ⟨u, hu⟩ _ rfl, sub_mulVec, one_mulVec]
  have hrange : LinearMap.range ψ = LinearMap.range (mulVecLin
      ((D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) - 1)) := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      rw [hψ]
      obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := Submodule.mem_sup.1 t.2
      have hle : commSpace (Subgroup.zpowers d) (commSpace L ⊤) ≤
          ((LinearMap.range (mulVecLin ((D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2)
            (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) - 1))).comap
            (β.toZModLinearMap 2)).map (commSpace L ⊤).subtype := by
        refine commSpace_le_iff.2 fun k hk u hu => ?_
        rcases eq_one_or_eq_of_mem_zpowers hdd hk with hk1 | hk1
        · rw [hk1, show (1 : GLV V) u = u from rfl, sub_self]
          exact Submodule.zero_mem _
        · rw [hk1]
          exact ⟨⟨d u - u, hTU (hdU u hu)⟩, ⟨β ⟨u, hu⟩, (hβd u hu).symm⟩, rfl⟩
      obtain ⟨w₁, hw₁, hw₁e⟩ := hle ht₁
      have h2 : β ⟨t₂, ht₂.2⟩ = 0 := (hβk _).2 ht₂.1
      have h3 : (⟨t, hTU t.2⟩ : ↥(commSpace L ⊤)) = w₁ + ⟨t₂, ht₂.2⟩ := by
        apply Subtype.ext
        show (t : V) = (w₁ : V) + t₂
        rw [← ht, ← hw₁e]
        rfl
      rw [h3, map_add, h2, add_zero]
      exact hw₁
    · rintro _ ⟨v, rfl⟩
      obtain ⟨⟨u, hu⟩, rfl⟩ := hβs v
      exact ⟨⟨d u - u, hdU u hu⟩, by rw [hψ, mulVecLin_apply, ← hβd u hu]⟩
  have hker : LinearMap.ker ψ = (tildeVBot L).comap (BAS.tvComm L d).subtype := by
    ext t
    rw [LinearMap.mem_ker, hψ, hβk, Submodule.mem_comap, Submodule.subtype_apply]
    exact ⟨fun h => ⟨h, hTU t.2⟩, fun h => h.1⟩
  have hCT : tildeVBot L ≤ BAS.tvComm L d := le_sup_right
  have h := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hCT).finrank_eq] at h
  exact h

theorem exists_matrix_data [Finite V] {L : Subgroup (GLV V)} (hL : IsOmegaMinusModule L m)
    {d : GLV V} (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hd2 : orderOf d = 2)
    (hodd : ∀ l ∈ L, orderOf (d * (l * d * l⁻¹)) ≤ 2 ∨ Odd (orderOf (d * (l * d * l⁻¹)))) :
    ∃ D : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2), D * D = 1 ∧
      (∀ y ∈ omegaMinusTwo m, D * y * D⁻¹ ∈ omegaMinusTwo m) ∧
      (∀ G ∈ omegaMinusTwo m,
        orderOf (D * (G * D * G⁻¹)) ≤ 2 ∨ Odd (orderOf (D * (G * D * G⁻¹)))) ∧
      Module.finrank (ZMod 2) ↥(LinearMap.range (mulVecLin
          ((D : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) - 1))) +
          Module.finrank (ZMod 2) ↥(tildeVBot L) =
        Module.finrank (ZMod 2) ↥(BAS.tvComm L d) := by
  obtain ⟨α, hαs, β, hβs, hβker, hrel⟩ := hL
  have hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L := L13Aux.ker_iff_of_eq hβker
  have hrel' : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w := hrel
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, sq] at h
    exact h
  obtain ⟨D, hDD, hD⟩ := exists_matrix hβs hβk hd hdd
  have hconj := conj_eq hβs hrel' hd hdd hDD hD
  refine ⟨D, hDD, fun y hy => ?_, fun G hG => ?_, finrank_range_add hβs hβk hd hdd hD⟩
  · obtain ⟨ℓ, hℓ⟩ := hαs ⟨y, hy⟩
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    have h := hconj ℓ ⟨_, hℓ'L⟩ rfl
    rw [hℓ] at h
    have h' : D * y * D⁻¹ = ((α ⟨_, hℓ'L⟩ : ↥(omegaMinusTwo m)) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) := h
    rw [h']
    exact (α _).2
  · obtain ⟨ℓ, hℓ⟩ := hαs ⟨G, hG⟩
    have hαℓ : ((α ℓ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) = G := by
      rw [hℓ]
    have hαℓi : ((α ℓ⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) = G⁻¹ := by
      rw [map_inv, Subgroup.coe_inv, hαℓ]
    have hU : ∀ x ∈ Subgroup.normalizer (L : Set (GLV V)), ∀ w ∈ commSpace L ⊤,
        x w ∈ commSpace L ⊤ := fun x hx w hw => apply_mem_commSpace hx hw
    have hℓN : (ℓ : GLV V) ∈ Subgroup.normalizer (L : Set (GLV V)) := Subgroup.le_normalizer ℓ.2
    have hℓiN : ((ℓ⁻¹ : ↥L) : GLV V) ∈ Subgroup.normalizer (L : Set (GLV V)) :=
      Subgroup.le_normalizer (ℓ⁻¹).2
    have hRℓ : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = (ℓ : GLV V) w →
        β w' = (G : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w :=
      fun w w' h => by rw [← hαℓ]; exact hrel' ℓ w w' h
    have hRℓi : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = ((ℓ⁻¹ : ↥L) : GLV V) w →
        β w' = ((G⁻¹ : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ β w :=
      fun w w' h => by rw [← hαℓi]; exact hrel' ℓ⁻¹ w w' h
    have h1 := rel_mul (hU _ hℓiN) hD hRℓi
    have h2 := rel_mul (hU _ (Subgroup.mul_mem _ hd hℓiN)) hRℓ h1
    have h3 := rel_mul (hU _ (Subgroup.mul_mem _ hℓN (Subgroup.mul_mem _ hd hℓiN))) hD h2
    have hxN : d * ((ℓ : GLV V) * (d * ((ℓ⁻¹ : ↥L) : GLV V))) ∈
        Subgroup.normalizer (L : Set (GLV V)) :=
      Subgroup.mul_mem _ hd (Subgroup.mul_mem _ hℓN (Subgroup.mul_mem _ hd hℓiN))
    have hdvd := orderOf_dvd hβs (hU _ hxN) h3
    have hx : d * ((ℓ : GLV V) * (d * ((ℓ⁻¹ : ↥L) : GLV V))) =
        d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) := by
      rw [Subgroup.coe_inv]
      group
    have hX : D * (G * (D * G⁻¹)) = D * (G * D * G⁻¹) := by group
    rw [hx, hX] at hdvd
    haveI : Finite (GLV V) :=
      Finite.of_injective (fun g : GLV V => (g : V → V)) DFunLike.coe_injective
    have hpos : 0 < orderOf (d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹)) := orderOf_pos _
    rcases hodd (ℓ : GLV V) ℓ.2 with h | h
    · exact Or.inl ((Nat.le_of_dvd hpos hdvd).trans h)
    · exact Or.inr (Odd.of_dvd_nat h hdvd)

end CFSG.CGT.Foote82.OmegaMinusMat

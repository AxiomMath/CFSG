module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorSym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Matrix Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 unitri unitriGL)
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel

@[expose] def repK12 : Representation (ZMod 2) K (Sym3 × Sym3) where
  toFun k := LinearMap.prodMap (symThreeCongrHom k.1).toLinearMap
    (symThreeCongrHom k.2).toLinearMap
  map_one' := LinearMap.ext fun x => Prod.ext (symThreeCongr_one x.1) (symThreeCongr_one x.2)
  map_mul' k k' := LinearMap.ext fun x =>
    Prod.ext (symThreeCongr_mul k.1 k'.1 x.1) (symThreeCongr_mul k.2 k'.2 x.2)

theorem repK12_apply (k : K) (x : Sym3 × Sym3) :
    repK12 k x = (symThreeCongr k.1 x.1, symThreeCongr k.2 x.2) := rfl

@[expose] def swap12 : Module.End (ZMod 2) (Sym3 × Sym3) :=
  (LinearEquiv.prodComm (ZMod 2) Sym3 Sym3).toLinearMap

theorem swap12_mul_swap12 : swap12 * swap12 = 1 := LinearMap.ext fun _ => rfl

theorem swap12_mul_repK12 (k : K) : swap12 * repK12 k = repK12 k.swap * swap12 :=
  LinearMap.ext fun _ => rfl

@[expose] def swapPow12 (ε : Multiplicative (ZMod 2)) : Module.End (ZMod 2) (Sym3 × Sym3) :=
  if Multiplicative.toAdd ε = 0 then 1 else swap12

theorem swapPow12_one : swapPow12 1 = 1 := rfl

theorem swapPow12_s : swapPow12 (Multiplicative.ofAdd 1) = swap12 := rfl

theorem swapPow12_mul (ε ε' : Multiplicative (ZMod 2)) :
    swapPow12 (ε * ε') = swapPow12 ε * swapPow12 ε' := by
  rcases mult_two_cases ε with rfl | rfl <;> rcases mult_two_cases ε' with rfl | rfl
  · rfl
  · simp [swapPow12_one]
  · simp [swapPow12_one]
  · rw [show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 from rfl,
      swapPow12_one, swapPow12_s, swap12_mul_swap12]

theorem swapPow12_mul_repK12 (ε : Multiplicative (ZMod 2)) (k : K) :
    swapPow12 ε * repK12 k = repK12 (swapAct ε k) * swapPow12 ε := by
  rcases mult_two_cases ε with rfl | rfl
  · rw [swapPow12_one, one_mul, mul_one]
    rfl
  · rw [swapPow12_s, swap12_mul_repK12]
    rfl

@[expose] def rep12 : Representation (ZMod 2) Ehat (Sym3 × Sym3) where
  toFun e := repK12 e.left * swapPow12 e.right
  map_one' := by
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, swapPow12_one, mul_one]
  map_mul' e e' := by
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul, swapPow12_mul,
      mul_assoc (repK12 e.left) (swapPow12 e.right), ← mul_assoc (swapPow12 e.right),
      swapPow12_mul_repK12]
    simp only [mul_assoc]

theorem rep12_inl (k : K) : rep12 (SemidirectProduct.inl k) = repK12 k := by
  change repK12 k * swapPow12 1 = repK12 k
  rw [swapPow12_one, mul_one]

theorem rep12_inl_apply (k : K) (x : Sym3 × Sym3) :
    rep12 (SemidirectProduct.inl k) x = (symThreeCongr k.1 x.1, symThreeCongr k.2 x.2) := by
  rw [rep12_inl, repK12_apply]

theorem rep12_sE_apply (x : Sym3 × Sym3) : rep12 sE x = x.swap := by
  change repK12 1 (swap12 x) = x.swap
  rw [map_one]
  rfl

theorem rep12_mul_apply (e e' : Ehat) (x : Sym3 × Sym3) :
    rep12 (e * e') x = rep12 e (rep12 e' x) := by
  rw [map_mul]
  rfl

theorem rep12_inv_apply_apply (e : Ehat) (x : Sym3 × Sym3) : rep12 e⁻¹ (rep12 e x) = x := by
  rw [← rep12_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem rep12_apply_inv_apply (e : Ehat) (x : Sym3 × Sym3) : rep12 e (rep12 e⁻¹ x) = x := by
  rw [← rep12_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem fixed_snd_eq_zero {x : Sym3 × Sym3} (h : ∀ g : S, repK12 ((1 : S), g) x = x) :
    x.2 = 0 :=
  eq_zero_of_forall_fixed fun g => congrArg Prod.snd (h g)

theorem apply_inl_of_commute12 (τ : (Sym3 × Sym3) ≃ₗ[ZMod 2] (Sym3 × Sym3))
    (hτ : ∀ (k : K) (x : Sym3 × Sym3), τ (repK12 k x) = repK12 k (τ x)) (B : Sym3) :
    τ (B, 0) = (B, 0) := by
  have hsnd : ∀ B : Sym3, (τ (B, 0)).2 = 0 := fun B => fixed_snd_eq_zero fun g => by
    rw [← hτ, repK12_apply]
    change τ (symThreeCongr 1 B, symThreeCongr g 0) = τ (B, 0)
    rw [symThreeCongr_one, symThreeCongr_zero]
  let F₁ : Sym3 →ₗ[ZMod 2] Sym3 :=
    LinearMap.fst (ZMod 2) Sym3 Sym3 ∘ₗ τ.toLinearMap ∘ₗ LinearMap.inl (ZMod 2) Sym3 Sym3
  have hF₁ : ∀ B, τ (B, 0) = (F₁ B, 0) := fun B => Prod.ext rfl (hsnd B)
  have hinj : Function.Injective F₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro B hB
    rw [LinearMap.mem_ker] at hB
    have h1 : τ (B, 0) = 0 := by rw [hF₁, hB]; rfl
    have h2 : ((B, 0) : Sym3 × Sym3) = 0 := τ.injective (h1.trans (map_zero τ).symm)
    exact (Submodule.mem_bot _).2 (congrArg Prod.fst h2)
  let F : Sym3 ≃ₗ[ZMod 2] Sym3 := LinearEquiv.ofInjectiveEndo F₁ hinj
  have hFc : ∀ (g : S) (B : Sym3), F (symThreeCongr g B) = symThreeCongr g (F B) :=
    fun g B => by
      change F₁ (symThreeCongr g B) = symThreeCongr g (F₁ B)
      have h1 := hτ (g, 1) (B, 0)
      rw [repK12_apply] at h1
      change τ (symThreeCongr g B, symThreeCongr 1 0) = _ at h1
      rw [symThreeCongr_zero] at h1
      rw [hF₁, hF₁, repK12_apply] at h1
      exact congrArg Prod.fst h1
  have hF := eq_refl_of_commute F hFc
  rw [hF₁]
  have h2 : F B = B := by rw [hF]; rfl
  exact Prod.ext h2 rfl

theorem eq_refl_of_commute12 (τ : (Sym3 × Sym3) ≃ₗ[ZMod 2] (Sym3 × Sym3))
    (hτ : ∀ (k : K) (x : Sym3 × Sym3), τ (repK12 k x) = repK12 k (τ x)) (x : Sym3 × Sym3) :
    τ x = x := by
  let sw : (Sym3 × Sym3) ≃ₗ[ZMod 2] (Sym3 × Sym3) := LinearEquiv.prodComm (ZMod 2) Sym3 Sym3
  let τ' := (sw.trans τ).trans sw
  have hτ' : ∀ (k : K) (x : Sym3 × Sym3), τ' (repK12 k x) = repK12 k (τ' x) := fun k x => by
    change (τ (repK12 k x).swap).swap = repK12 k (τ x.swap).swap
    have h1 : (repK12 k x).swap = repK12 k.swap x.swap := rfl
    rw [h1, hτ]
    rfl
  have h1 := apply_inl_of_commute12 τ hτ x.1
  have h2 := apply_inl_of_commute12 τ' hτ' x.2
  have h2' : τ (0, x.2) = (0, x.2) := by
    have := congrArg Prod.swap h2
    exact this
  calc τ x = τ ((x.1, 0) + (0, x.2)) := by rw [Prod.mk_add_mk, add_zero, zero_add]
    _ = x := by rw [map_add, h1, h2', Prod.mk_add_mk, add_zero, zero_add]

abbrev Fix12 (T : Set Ehat) : Type := {x : Sym3 × Sym3 // ∀ b ∈ T, rep12 b x = x}

theorem card_fix12_anti {T T' : Set Ehat} (h : T ⊆ T') :
    Nat.card (Fix12 T') ≤ Nat.card (Fix12 T) :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, fun b hb => x.2 b (h hb)⟩)
    fun x y hxy => by
      apply Subtype.ext
      have h' := congrArg Subtype.val hxy
      exact h'

theorem card_fix12_conj (e : Ehat) (T : Set Ehat) :
    Nat.card (Fix12 ((fun b => e * b * e⁻¹) '' T)) = Nat.card (Fix12 T) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨rep12 e⁻¹ x.1, fun b hb => ?_⟩
      invFun := fun x => ⟨rep12 e x.1, ?_⟩
      left_inv := fun x => Subtype.ext (rep12_apply_inv_apply e x.1)
      right_inv := fun x => Subtype.ext (rep12_inv_apply_apply e x.1) }
  · have h := x.2 _ ⟨b, hb, rfl⟩
    rw [rep12_mul_apply, rep12_mul_apply] at h
    rw [← rep12_inv_apply_apply e (rep12 b _), h]
  · rintro _ ⟨b, hb, rfl⟩
    rw [rep12_mul_apply, rep12_mul_apply, rep12_inv_apply_apply, x.2 b hb]

theorem card_fix12_inl_ge (k : K) (hk : k * k = 1) :
    256 ≤ Nat.card (Fix12 {SemidirectProduct.inl k}) := by
  have e : Fix12 {SemidirectProduct.inl k} ≃ FixS k.1 × FixS k.2 :=
    { toFun := fun x => (⟨x.1.1, congrArg Prod.fst ((rep12_inl_apply k x.1).symm.trans
          (x.2 _ rfl))⟩, ⟨x.1.2, congrArg Prod.snd ((rep12_inl_apply k x.1).symm.trans
          (x.2 _ rfl))⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), fun b hb => by
        rw [Set.mem_singleton_iff] at hb
        subst hb
        rw [rep12_inl_apply, y.1.2, y.2.2]⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_prod]
  exact le_trans (by norm_num) (Nat.mul_le_mul (sixteen_le_card_fixS (congrArg Prod.fst hk))
    (sixteen_le_card_fixS (congrArg Prod.snd hk)))

abbrev FixSet (P : Subgroup S) : Type := {X : Sym3 // ∀ g : S, g ∈ P → symThreeCongr g X = X}

theorem card_fixSet_le_of_mem {P : Subgroup S} {g : S} (hg : g ∈ P) :
    Nat.card (FixSet P) ≤ Nat.card (FixS g) :=
  Nat.card_le_card_of_injective (fun X => ⟨X.1, X.2 g hg⟩) fun X Y h => by
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'

theorem card_fixSet_mul_card_le {P : Subgroup S} (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hsq : ∀ x ∈ P, x * x = 1) (hP : P ≠ ⊥) : Nat.card (FixSet P) * Nat.card P ≤ 32 := by
  classical
  have h4 := card_le_four_of_elementary hcomm hsq
  obtain ⟨x, hxP, hx1⟩ := exists_ne_one_of_ne_bot hP
  by_cases h2 : Nat.card P ≤ 2
  · calc Nat.card (FixSet P) * Nat.card P ≤ 16 * 2 :=
          Nat.mul_le_mul ((card_fixSet_le_of_mem hxP).trans
            (card_fixS_le_of_ne_one (hsq x hxP) hx1)) h2
      _ = 32 := by norm_num
  ·
    push Not at h2
    obtain ⟨y, hyP, hy⟩ : ∃ y ∈ P, y ≠ 1 ∧ y ≠ x := by
      by_contra hcon
      push Not at hcon
      have hsub : (P : Set S) ⊆ {1, x} := fun y hy => by
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hcon y hy hy1)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair (Ne.symm hx1), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at this
      omega
    have hfix : Nat.card (FixSet P) ≤ 8 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun X : FixSet P => (⟨X.1, X.2 x hxP, X.2 y hyP⟩ :
          {B : Sym3 // symThreeCongr x B = B ∧ symThreeCongr y B = B}))
        fun X Y h => by
          apply Subtype.ext
          have h' := congrArg Subtype.val h
          exact h') ?_
      exact card_fixS_pair_le (hsq x hxP) (hsq y hyP) hx1 hy.1 (Ne.symm hy.2) (hcomm x hxP y hyP)
    calc Nat.card (FixSet P) * Nat.card P ≤ 8 * 4 := Nat.mul_le_mul hfix h4
      _ = 32 := by norm_num

theorem card_fixSet_mul_card_le_sixtyFour {P : Subgroup S}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hsq : ∀ x ∈ P, x * x = 1) :
    Nat.card (FixSet P) * Nat.card P ≤ 64 := by
  by_cases hP : P = ⊥
  · subst hP
    rw [card_bot, mul_one]
    calc Nat.card (FixSet ⊥) ≤ Nat.card Sym3 :=
          Nat.card_le_card_of_injective (fun X => X.1) fun X Y h => Subtype.ext h
      _ = 64 := card_symThree
  · exact (card_fixSet_mul_card_le hcomm hsq hP).trans (by norm_num)

theorem card_fix12_sE : Nat.card (Fix12 {sE}) ≤ 64 := by
  have h : Nat.card (Fix12 {sE}) ≤ Nat.card Sym3 :=
    Nat.card_le_card_of_injective (fun x => x.1.1) fun x y hxy => by
      have hx : x.1.swap = x.1 := (rep12_sE_apply x.1).symm.trans (x.2 sE rfl)
      have hy : y.1.swap = y.1 := (rep12_sE_apply y.1).symm.trans (y.2 sE rfl)
      apply Subtype.ext
      refine Prod.ext hxy ?_
      calc x.1.2 = x.1.1 := congrArg Prod.fst hx
        _ = y.1.1 := hxy
        _ = y.1.2 := (congrArg Prod.fst hy).symm
  exact h.trans card_symThree.le

theorem card_fix12_mul_card_lt (B : Subgroup Ehat) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (hB : B ≠ ⊥) : Nat.card (Fix12 B) * Nat.card B < 4096 := by
  classical
  by_cases hK : ∀ b ∈ B, b.right = 1
  ·
    set B' : Subgroup K := B.comap SemidirectProduct.inl with hB'
    have hinl : ∀ b ∈ B, SemidirectProduct.inl b.left = b := fun b hb =>
      SemidirectProduct.ext rfl (hK b hb).symm
    have hmemB' : ∀ b ∈ B, b.left ∈ B' := fun b hb => by
      change SemidirectProduct.inl b.left ∈ B
      rw [hinl b hb]
      exact hb
    have hcardB : Nat.card B = Nat.card B' := Nat.card_congr
      { toFun := fun b => ⟨b.1.left, hmemB' b.1 b.2⟩
        invFun := fun k => ⟨SemidirectProduct.inl k.1, k.2⟩
        left_inv := fun b => Subtype.ext (hinl b.1 b.2)
        right_inv := fun k => rfl }
    have hB'sq : ∀ k ∈ B', k * k = 1 := fun k hk =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_one]; exact hsq _ hk)
    have hB'comm : ∀ k ∈ B', ∀ k' ∈ B', k * k' = k' * k := fun k hk k' hk' =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_mul]; exact hcomm _ hk _ hk')
    set P₁ := B'.map (MonoidHom.fst S S) with hP₁
    set P₂ := B'.map (MonoidHom.snd S S) with hP₂
    have hP₁comm : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Prod.fst (hB'comm x hx y hy)
    have hP₁sq : ∀ x ∈ P₁, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Prod.fst (hB'sq x hx)
    have hP₂comm : ∀ x ∈ P₂, ∀ y ∈ P₂, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Prod.snd (hB'comm x hx y hy)
    have hP₂sq : ∀ x ∈ P₂, x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Prod.snd (hB'sq x hx)
    have hB'le : Nat.card B' ≤ Nat.card P₁ * Nat.card P₂ := by
      have h := Nat.card_le_card_of_injective
        (fun k : B' => ((⟨k.1.1, k.1, k.2, rfl⟩ : P₁), (⟨k.1.2, k.1, k.2, rfl⟩ : P₂)))
        (fun k k' hkk' => Subtype.ext (Prod.ext (congrArg (fun p => (p.1 : S)) hkk')
          (congrArg (fun p => (p.2 : S)) hkk')))
      rwa [Nat.card_prod] at h
    have hfix : Nat.card (Fix12 B) ≤ Nat.card (FixSet P₁) * Nat.card (FixSet P₂) := by
      have h := Nat.card_le_card_of_injective
        (fun x : Fix12 B => ((⟨x.1.1, fun g hg => by
            obtain ⟨k, hk, rfl⟩ := hg
            exact congrArg Prod.fst ((rep12_inl_apply k x.1).symm.trans (x.2 _ hk))⟩ :
              FixSet P₁),
          (⟨x.1.2, fun g hg => by
            obtain ⟨k, hk, rfl⟩ := hg
            exact congrArg Prod.snd ((rep12_inl_apply k x.1).symm.trans (x.2 _ hk))⟩ :
              FixSet P₂)))
        (fun x y hxy => Subtype.ext (Prod.ext (congrArg (fun p => (p.1 : Sym3)) hxy)
          (congrArg (fun p => (p.2 : Sym3)) hxy)))
      rwa [Nat.card_prod] at h
    have hP : P₁ ≠ ⊥ ∨ P₂ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨b, hbB, hb1⟩ := exists_ne_one_of_ne_bot hB
      apply hb1
      rw [← hinl b hbB]
      have h1 : b.left.1 = 1 := by
        have : b.left.1 ∈ P₁ := ⟨b.left, hmemB' b hbB, rfl⟩
        rw [hcon.1] at this
        exact this
      have h2 : b.left.2 = 1 := by
        have : b.left.2 ∈ P₂ := ⟨b.left, hmemB' b hbB, rfl⟩
        rw [hcon.2] at this
        exact this
      rw [show b.left = 1 from Prod.ext h1 h2, map_one]
    have h1 := card_fixSet_mul_card_le_sixtyFour hP₁comm hP₁sq
    have h2 := card_fixSet_mul_card_le_sixtyFour hP₂comm hP₂sq
    calc Nat.card (Fix12 B) * Nat.card B ≤
          (Nat.card (FixSet P₁) * Nat.card (FixSet P₂)) * (Nat.card P₁ * Nat.card P₂) :=
          Nat.mul_le_mul hfix (hcardB ▸ hB'le)
      _ = (Nat.card (FixSet P₁) * Nat.card P₁) * (Nat.card (FixSet P₂) * Nat.card P₂) := by
          ring
      _ < 4096 := by
          rcases hP with hP | hP
          · have h3 := card_fixSet_mul_card_le hP₁comm hP₁sq hP
            calc _ ≤ 32 * 64 := Nat.mul_le_mul h3 h2
              _ < 4096 := by norm_num
          · have h3 := card_fixSet_mul_card_le hP₂comm hP₂sq hP
            calc _ ≤ 64 * 32 := Nat.mul_le_mul h1 h3
              _ < 4096 := by norm_num
  ·
    push Not at hK
    obtain ⟨b, hbB, hbr⟩ := hK
    obtain ⟨c, hc⟩ := exists_conj_eq_sE hbr (hsq b hbB)
    set B'' := B.map (MulAut.conj c).toMonoidHom with hB''
    have hcoe : (B'' : Set Ehat) = (fun x => c * x * c⁻¹) '' (B : Set Ehat) := by
      ext x
      simp [hB'', MulAut.conj_apply]
    have hfixB : Nat.card (Fix12 B'') = Nat.card (Fix12 B) := by
      rw [hcoe]
      exact card_fix12_conj c B
    have hcardB : Nat.card B'' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    have hsE : sE ∈ B'' := ⟨b, hbB, hc⟩
    have hcomm'' : ∀ x ∈ B'', ∀ y ∈ B'', x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    have hsq'' : ∀ x ∈ B'', x * x = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one]
    have hdiag : ∀ x ∈ B'', x.right = 1 →
        x = SemidirectProduct.inl ((x.left.1, x.left.1) : K) := by
      intro x hx hxr
      have hxl : SemidirectProduct.inl x.left = x := SemidirectProduct.ext rfl hxr.symm
      have h1 : sE * x * sE⁻¹ = x := by
        rw [hcomm'' sE hsE x hx, mul_inv_cancel_right]
      rw [← hxl, sE_conj_inl] at h1
      have h2 : x.left.swap = x.left := SemidirectProduct.inl_injective h1
      calc x = SemidirectProduct.inl x.left := hxl.symm
        _ = SemidirectProduct.inl ((x.left.1, x.left.1) : K) :=
          congrArg _ (Prod.ext rfl (congrArg Prod.snd h2).symm)
    set f := (SemidirectProduct.rightHom : Ehat →* Multiplicative (ZMod 2)).domRestrict B''
    have hrange : Nat.card f.range ≤ 2 := (Subgroup.card_le_card_group _).trans card_mult_two.le
    have hcardker := Subgroup.card_ker_mul_card_range f
    let g₀ : f.ker →* S :=
      { toFun := fun x => (x : B'').1.left.1
        map_one' := rfl
        map_mul' := fun x y => by
          have hx : ((x : B'') : Ehat).right = 1 := x.2
          change (((x : B'') : Ehat) * ((y : B'') : Ehat)).left.1 = _
          rw [SemidirectProduct.mul_left, hx, swapAct_one_apply]
          rfl }
    have hg₀ : Function.Injective g₀ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxr : ((x : B'') : Ehat).right = 1 := x.2
      have h1 := hdiag _ (x : B'').2 hxr
      have hx' : ((x : B'') : Ehat).left.1 = 1 := hx
      rw [hx'] at h1
      exact Subtype.ext (Subtype.ext (h1.trans (by
        rw [show ((1, 1) : K) = 1 from rfl, map_one]
        rfl)))
    have hker4 : Nat.card f.ker ≤ 4 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hg₀).toEquiv]
      refine card_le_four_of_elementary ?_ ?_
      · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subtype.ext (hcomm'' _ (x : B'').2 _ (y : B'').2))
      · rintro _ ⟨x, rfl⟩
        rw [← map_mul, show x * x = 1 from Subtype.ext (Subtype.ext (hsq'' _ (x : B'').2)),
          map_one]
    have hfix : Nat.card (Fix12 B'') ≤ 64 := by
      refine (card_fix12_anti (T := {sE}) ?_).trans card_fix12_sE
      rw [Set.singleton_subset_iff]
      exact hsE
    calc Nat.card (Fix12 B) * Nat.card B = Nat.card (Fix12 B'') * Nat.card B'' := by
          rw [hfixB, hcardB]
      _ ≤ 64 * (4 * 2) := Nat.mul_le_mul hfix (by
          rw [← hcardker]
          exact Nat.mul_le_mul hker4 hrange)
      _ < 4096 := by norm_num

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

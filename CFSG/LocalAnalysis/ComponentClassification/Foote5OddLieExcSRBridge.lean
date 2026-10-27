module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S]

theorem mem_innerPart_of_conj_mem [Finite S] (hZ : center S = ⊥) {α : MulAut S}
    {R : Subgroup (MulAut S)} (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * α = α * r)
    {g : S} (hg : MulAut.conj g ∈ R) : g ∈ innerPart α R := by
  refine mem_inf.2 ⟨subset_closure ⟨?_, ?_⟩, hg⟩
  · apply conj_injective hZ
    rw [conj_apply_eq, ← hRi _ hg, mul_inv_cancel_right]
  · rw [← orderOf_injective _ (conj_injective hZ) g]
    exact odd_orderOf_of_mem hRodd hg

theorem innerPart_eq_bot [Finite S] (hZ : center S = ⊥) {α : MulAut S}
    {R : Subgroup (MulAut S)} (hRodd : Odd (Nat.card R))
    (hRc : ∀ s : S, α s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    (hO : pPrimeCore 2 (fixedSubgroup α) = ⊥) : innerPart α R = ⊥ := by
  set F := fixedSubgroup α with hF
  set T := oddFixed α with hT
  set N := innerPart α R with hN
  have hTF : T ≤ F := (closure_le _).2 fun s hs => hs.1
  have hNT : N ≤ T := inf_le_left
  set TF : Subgroup F := T.subgroupOf F with hTFdef
  have hTn : TF.Normal := by
    refine ⟨fun n hn f => ?_⟩
    rw [hTFdef, mem_subgroupOf] at hn ⊢
    have hf : α (f : S) = f := f.2
    have hmap : T.map (MulAut.conj (f : S)).toMonoidHom ≤ T := by
      rw [hT, oddFixed, MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨s, ⟨hs, hso⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hf, hs]
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
        exact hso
    simpa using hmap ⟨_, hn, rfl⟩
  set M : Subgroup TF := (N.subgroupOf F).subgroupOf TF with hMdef
  have hMn : M.Normal := by
    refine ⟨fun n hn t => ?_⟩
    rw [hMdef, mem_subgroupOf, mem_subgroupOf] at hn ⊢
    have ht : ((t : F) : S) ∈ T := mem_subgroupOf.1 t.2
    simpa using conj_mem_innerPart hRc ht hn
  have hNTF : N.subgroupOf F ≤ TF := fun x hx => mem_subgroupOf.2 (hNT (mem_subgroupOf.1 hx))
  have hMcard : Nat.card M = Nat.card N := by
    rw [hMdef, Nat.card_congr (subgroupOfEquivOfLe hNTF).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (hNT.trans hTF)).toEquiv]
  have hMO : M ≤ pPrimeCore 2 TF := by
    refine le_sSup ⟨hMn, ?_⟩
    rw [hMcard]
    exact Nat.coprime_two_left.2 (odd_card_innerPart hZ hRodd)
  have hsub := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hTn.isSubnormal
  rw [hO] at hsub
  rw [eq_bot_iff]
  intro n hn
  have hnF : n ∈ F := hTF (hNT hn)
  have hnT : (⟨n, hnF⟩ : F) ∈ TF := mem_subgroupOf.2 (hNT hn)
  have hnM : (⟨⟨n, hnF⟩, hnT⟩ : TF) ∈ M := by
    rw [hMdef, mem_subgroupOf, mem_subgroupOf]
    exact hn
  have h1 := hsub ⟨_, hMO hnM, rfl⟩
  rw [mem_bot] at h1
  have h2 := congrArg Subtype.val h1
  exact mem_bot.2 h2

theorem outerCoreTrivAt_of_inner [Finite S] (hZ : center S = ⊥) {α : MulAut S}
    (hO : pPrimeCore 2 (fixedSubgroup α) = ⊥)
    (hinn : ∀ R : Subgroup (MulAut S), Odd (Nat.card R) → (∀ r ∈ R, r * α = α * r) →
      (∀ s : S, α s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r ∈ R, r ∈ (MulAut.conj : S →* MulAut S).range) :
    OuterCoreTrivAt α := by
  intro R hRodd hRi hRc r hr
  obtain ⟨g, rfl⟩ := hinn R hRodd hRi hRc r hr
  have hg := mem_innerPart_of_conj_mem hZ hRodd hRi hr
  rw [innerPart_eq_bot hZ hRodd hRc hO, mem_bot] at hg
  rw [hg, map_one]

theorem outerCoreTrivAt_of_component [Finite S] (hZ : center S = ⊥) {α : MulAut S}
    (hO : pPrimeCore 2 (fixedSubgroup α) = ⊥) {X : Subgroup S}
    (hX : GorensteinWalter.IsComponentOf X (oddFixed α))
    (hinn : ∀ r : MulAut S, Odd (orderOf r) → r * α = α * r → (∀ y ∈ X, r y = y) →
      r ∈ (MulAut.conj : S →* MulAut S).range) :
    OuterCoreTrivAt α :=
  outerCoreTrivAt_of_inner hZ hO fun _ hRodd hRi hRc r hr =>
    hinn r (odd_orderOf_of_mem hRodd hr) (hRi r hr) fun _ hy =>
      fix_of_isComponentOf hRi hRc hZ hRodd hr hX hy

theorem outerCoreAt_of_component [Finite S] (hZ : center S = ⊥) {α : MulAut S}
    {X : Subgroup S} (hX : GorensteinWalter.IsComponentOf X (oddFixed α))
    (hinn : ∀ r : MulAut S, Odd (orderOf r) → r * α = α * r → (∀ y ∈ X, r y = y) →
      r ∈ (MulAut.conj : S →* MulAut S).range)
    (hab : ∀ g h : S, α g = g → α h = h → Odd (orderOf g) → Odd (orderOf h) →
      (∀ y ∈ X, g * y * g⁻¹ = y) → (∀ y ∈ X, h * y * h⁻¹ = y) → g * h = h * g) :
    OuterCoreAt α := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  have hfix : ∀ r ∈ R, ∀ y ∈ X, r y = y := fun r hr _ hy =>
    fix_of_isComponentOf hRi hRc hZ hRodd hr hX hy
  obtain ⟨g₁, rfl⟩ := hinn r₁ (odd_orderOf_of_mem hRodd h₁) (hRi r₁ h₁) (hfix r₁ h₁)
  obtain ⟨g₂, rfl⟩ := hinn r₂ (odd_orderOf_of_mem hRodd h₂) (hRi r₂ h₂) (hfix r₂ h₂)
  have hg₁ := mem_innerPart_of_conj_mem hZ hRodd hRi h₁
  have hg₂ := mem_innerPart_of_conj_mem hZ hRodd hRi h₂
  have hf₁ : α g₁ = g₁ := ((closure_le (fixedSubgroup α)).2 (fun s hs => hs.1)
    (mem_inf.1 hg₁).1)
  have hf₂ : α g₂ = g₂ := ((closure_le (fixedSubgroup α)).2 (fun s hs => hs.1)
    (mem_inf.1 hg₂).1)
  have ho₁ : Odd (orderOf g₁) := by
    rw [← orderOf_injective _ (conj_injective hZ) g₁]
    exact odd_orderOf_of_mem hRodd h₁
  have ho₂ : Odd (orderOf g₂) := by
    rw [← orderOf_injective _ (conj_injective hZ) g₂]
    exact odd_orderOf_of_mem hRodd h₂
  have hc := hab g₁ g₂ hf₁ hf₂ ho₁ ho₂ (fun y hy => hfix _ h₁ y hy)
    (fun y hy => hfix _ h₂ y hy)
  rw [← map_mul, ← map_mul, hc]

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc

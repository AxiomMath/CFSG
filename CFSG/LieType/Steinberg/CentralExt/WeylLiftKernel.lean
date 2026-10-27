module

public import CFSG.LieType.Steinberg.CentralExt.WeylLift

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.WeylLift

variable {τ : Tag}

section Pairing

variable {E : Type*} [Group E] {k : Type} [Field k] [Finite k] {Y Y' : k → E}

theorem commutatorElement_mem_zpowers_of_add (hk : Nat.card k = 3)
    (hY : ∀ s t, Y (s + t) = Y s * Y t) (hY' : ∀ s t, Y' (s + t) = Y' s * Y' t)
    (hc : ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.center E) (s t : k) :
    ⁅Y s, Y' t⁆ ∈ Subgroup.zpowers ⁅Y 1, Y' 1⁆ := by
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hY'0 : Y' 0 = 1 := by
    have h := hY' 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hneg1 : ∀ t, ⁅Y (-1), Y' t⁆ = ⁅Y 1, Y' t⁆⁻¹ := fun t => by
    have h := TorusLift.commutatorElement_mul_left_of_central (a := Y 1) (hc (-1) t)
    rw [← hY, add_neg_cancel, hY0, commutatorElement_one_left] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hneg2 : ∀ s, ⁅Y s, Y' (-1)⁆ = ⁅Y s, Y' 1⁆⁻¹ := fun s => by
    have h := TorusLift.commutatorElement_mul_right_of_central (b := Y' 1) (hc s (-1))
    rw [← hY', add_neg_cancel, hY'0, commutatorElement_one_right] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hm := Subgroup.mem_zpowers ⁅Y 1, Y' 1⁆
  rcases eq_zero_or_one_or_neg_one hk s with rfl | rfl | rfl
  · rw [hY0, commutatorElement_one_left]
    exact Subgroup.one_mem _
  · rcases eq_zero_or_one_or_neg_one hk t with rfl | rfl | rfl
    · rw [hY'0, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · exact hm
    · rw [hneg2]
      exact Subgroup.inv_mem _ hm
  · rcases eq_zero_or_one_or_neg_one hk t with rfl | rfl | rfl
    · rw [hY'0, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [hneg1]
      exact Subgroup.inv_mem _ hm
    · rw [hneg2, hneg1, inv_inv]
      exact hm

theorem commutatorElement_pow_three_of_add (hk : Nat.card k = 3)
    (hY : ∀ s t, Y (s + t) = Y s * Y t) (hc : ∀ s t, ⁅Y s, Y' t⁆ ∈ Subgroup.center E) :
    ⁅Y 1, Y' 1⁆ ^ 3 = 1 := by
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hadd : ∀ s s', ⁅Y (s + s'), Y' 1⁆ = ⁅Y s, Y' 1⁆ * ⁅Y s', Y' 1⁆ := fun s s' => by
    rw [hY]
    exact TorusLift.commutatorElement_mul_left_of_central (hc s' 1)
  have h3 : ⁅Y (1 + 1 + 1), Y' 1⁆ = ⁅Y 1, Y' 1⁆ ^ 3 := by
    rw [hadd, hadd, pow_three, mul_assoc]
  rw [← h3, show (1 : k) + 1 + 1 = 3 by norm_num, three_eq_zero hk, hY0,
    commutatorElement_one_left]

end Pairing

theorem card_le_three_of_le_zpowers {E : Type*} [Group E] {c : E} (hc : c ^ 3 = 1)
    {H : Subgroup E} (h : H ≤ Subgroup.zpowers c) : Nat.card H ≤ 3 := by
  have hfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hc⟩
  have : Finite (Subgroup.zpowers c) := finite_zpowers.2 hfin
  calc Nat.card H ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le h
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hc

inductive PairOrbit (τ : Tag) (γ₀ δ₀ : Fin τ.rank → ℤ) :
    (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Prop
  | base : PairOrbit τ γ₀ δ₀ γ₀ δ₀
  | swap {γ δ : Fin τ.rank → ℤ} : PairOrbit τ γ₀ δ₀ γ δ → PairOrbit τ γ₀ δ₀ δ γ
  | step {γ δ : Fin τ.rank → ℤ} (i : Fin τ.rank) :
      PairOrbit τ γ₀ δ₀ γ δ → PairOrbit τ γ₀ δ₀ (reflect τ i γ) (reflect τ i δ)

theorem PairOrbit.isRoot {γ₀ δ₀ γ δ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀ ∧ IsRoot τ δ₀)
    (h : PairOrbit τ γ₀ δ₀ γ δ) : IsRoot τ γ ∧ IsRoot τ δ := by
  induction h with
  | base => exact h₀
  | swap _ ih => exact ⟨ih.2, ih.1⟩
  | step i _ ih => exact ⟨.reflect i ih.1, .reflect i ih.2⟩

theorem PairOrbit.path {γ₀ δ₀ γ δ : Fin τ.rank → ℤ} (h : PairOrbit τ γ₀ δ₀ γ δ)
    (l : List (Fin τ.rank)) : PairOrbit τ γ₀ δ₀ (reflectPath τ l γ) (reflectPath τ l δ) := by
  induction l generalizing γ δ with
  | nil => exact h
  | cons i l ih => exact ih (h.step i)

section Orbit

variable {G : Type*} [Group G] {hA : TauCeti.IsFiniteType τ.cartan}
  {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k] {x : (Fin τ.rank → ℤ) → k → G}
  {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ} {O : CommOrder (RootSystem.ofCartan hA ∅)}
  (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
  (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O) (T : (Fin τ.rank → kˣ) →* G)
  (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
    T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
  {E : Type*} [Group E] {π : E →* G} (hcen : π.ker ≤ Subgroup.center E)
  (hπ : Function.Surjective π)

include hroots hE hT hcen hπ in
theorem commutatorElement_mem_of_pairOrbit
    (hnT : ∀ i t, ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t')
    {Xf : (Fin τ.rank → ℤ) → k → E} (hlift : ∀ γ, IsRoot τ γ → IsRootLift x T π γ (Xf γ))
    (hsc : ∀ γ, IsRoot τ γ → ∃ t, rootChar k γ t ≠ 1) {H : Subgroup E} [H.Normal]
    {γ₀ δ₀ : Fin τ.rank → ℤ} (h₀ : IsRoot τ γ₀ ∧ IsRoot τ δ₀)
    (hH : ∀ s t, ⁅Xf γ₀ s, Xf δ₀ t⁆ ∈ H) {γ δ : Fin τ.rank → ℤ} (h : PairOrbit τ γ₀ δ₀ γ δ) :
    ∀ s t, ⁅Xf γ s, Xf δ t⁆ ∈ H := by
  induction h with
  | base => exact hH
  | swap _ ih =>
    intro s t
    rw [← commutatorElement_inv]
    exact H.inv_mem (ih t s)
  | @step γ δ i h ih =>
    intro s t
    obtain ⟨hγ, hδ⟩ := h.isRoot h₀
    obtain ⟨εγ, hεγ, hγ1, -⟩ := weyl_conj_root hroots hE i hγ
    obtain ⟨εδ, hεδ, hδ1, -⟩ := weyl_conj_root hroots hE i hδ
    obtain ⟨ñ, hñ⟩ := hπ (weylElement x i 1)
    obtain ⟨t₁, ht₁⟩ := hsc γ hγ
    obtain ⟨t₂, ht₂⟩ := hsc δ hδ
    have hγ' := conj_isRootLift hroots hE T hT hcen hπ (.reflect i hγ) (hlift γ hγ)
      (hlift _ (.reflect i hγ)) hεγ hγ1 (hnT i) ht₁ hñ (εγ * s)
    have hδ' := conj_isRootLift hroots hE T hT hcen hπ (.reflect i hδ) (hlift δ hδ)
      (hlift _ (.reflect i hδ)) hεδ hδ1 (hnT i) ht₂ hñ (εδ * t)
    rw [← mul_assoc, hεγ, one_mul] at hγ'
    rw [← mul_assoc, hεδ, one_mul] at hδ'
    have e : ⁅ñ * Xf γ (εγ * s) * ñ⁻¹, ñ * Xf δ (εδ * t) * ñ⁻¹⁆ =
        ñ * ⁅Xf γ (εγ * s), Xf δ (εδ * t)⁆ * ñ⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← hγ', ← hδ', e]
    exact Subgroup.Normal.conj_mem inferInstance _ (ih (εγ * s) (εδ * t)) ñ

end Orbit

theorem ker_le_closure_of_torus_three {G : Type*} [Group G]
    (hA : TauCeti.IsFiniteType τ.cartan) {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 3)
    {x : (Fin τ.rank → ℤ) → k → G} {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hprim : ∀ γ, IsRoot τ γ → ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1)
    (hnT : ∀ i t, ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t')
    (S : Set ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)))
    (hS : ∀ p ∈ S, IsRoot τ p.1 ∧ IsRoot τ p.2 ∧
      ∀ q : ℕ × ℕ, 0 < q.1 → 0 < q.2 → ¬IsRoot τ (q.1 • p.1 + q.2 • p.2))
    (hsep : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → LinIndepPair γ δ →
      (∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1) ∨ Reach τ γ δ ∨
        (γ, δ) ∈ S)
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    π.ker ≤ Subgroup.closure ((fun p => ⁅X x T π p.1 1, X x T π p.2 1⁆) '' S) := by
  have hmem : ∀ {γ}, γ ∈ (tagDatum τ hA RG).roots → IsRoot τ γ := fun {γ} hγ => by
    rw [hroots] at hγ
    exact hγ
  have hx : ∀ γ, IsRoot τ γ → ∀ c d, x γ (c + d) = x γ c * x γ d := fun γ hγ =>
    x_add hroots hE hγ
  have hw1 : (-1 : kˣ) ≠ 1 := FieldThree.neg_one_ne_one_of_card_three hk
  have hk4 : Nat.card k ≠ 4 := by omega
  have hspec : ∀ γ, IsRoot τ γ → IsRootLift x T π γ (X x T π γ) := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact X_isRootLift T (exists_isRootLift hx T hT hcen hπ hk4 hγ hm hw1)
  have hsc : ∀ γ, IsRoot τ γ → ∃ t, rootChar k γ t ≠ 1 := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact ⟨tvec (-1) m, by rw [rootChar_tvec, hm, zpow_one]; exact hw1⟩
  have hcS : ∀ p ∈ S, ∀ s t, ⁅X x T π p.1 s, X x T π p.2 t⁆ ∈ π.ker := fun p hp s t => by
    obtain ⟨h1, h2, h3⟩ := hS p hp
    rw [MonoidHom.mem_ker, map_commutatorElement, (hspec _ h1).2.1, (hspec _ h2).2.1]
    exact commute_x_of_not_isRoot hroots hE h1 h2 h3 s t
  set N := Subgroup.closure ((fun p => ⁅X x T π p.1 1, X x T π p.2 1⁆) '' S) with hN
  have hNker : N ≤ π.ker := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hcS p hp 1 1
  have : N.Normal := Subgroup.normal_of_le_center (hNker.trans hcen)
  set q := QuotientGroup.mk' N with hq
  let π' : E ⧸ N →* G := QuotientGroup.lift N π hNker
  have hπ'e : ∀ e : E, π' (q e) = π e := fun e => rfl
  have hπ' : Function.Surjective π' := fun g => by
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨q e, rfl⟩
  have hcen' : π'.ker ≤ Subgroup.center (E ⧸ N) := by
    intro y hy
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective N y
    have he : e ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hπ'e]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hcen he) z']
  have hcomm : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → (Reach τ γ δ ∨ (γ, δ) ∈ S) → ∀ s t,
      q (X x T π γ s) * q (X x T π δ t) = q (X x T π δ t) * q (X x T π γ s) := by
    rintro γ δ hγ hδ (hr | hp) s t
    · rw [← map_mul, ← map_mul, commute_X_of_reach hroots hE T hT hcen hπ hk hnT hspec hsc hr s t]
    · have hgen : ⁅X x T π γ 1, X x T π δ 1⁆ ∈ N :=
        Subgroup.subset_closure (Set.mem_image_of_mem _ hp)
      have hz : ⁅X x T π γ s, X x T π δ t⁆ ∈ N := Subgroup.zpowers_le_of_mem hgen
        (commutatorElement_mem_zpowers_of_add hk (hspec γ hγ).1 (hspec δ hδ).1
          (fun s t => hcen (hcS _ hp s t)) s t)
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hq,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hz
  suffices h : ∃ σ : G →* E ⧸ N, ∀ g, π' (σ g) = g by
    obtain ⟨σ, hσ⟩ := h
    have hbot := SL2Closed.ker_eq_bot_of_section π' hcen' σ hσ
    intro e he
    have hqe : q e ∈ π'.ker := by
      rw [MonoidHom.mem_ker, hπ'e]
      exact he
    rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqe
    exact hqe
  refine HalfSpaceLift.exists_section_of_lift' hcen' rfl hE hP
    (X := fun γ s => q (X x T π γ s))
    (tor := fun t : Fin τ.rank → kˣ => q (TorusLift.lift hπ (T t)))
    (χ := fun t γ => (rootChar k γ t : k))
    (fun γ hγ c d => by rw [(hspec γ (hmem hγ)).1, map_mul])
    (fun γ hγ c => by rw [hπ'e, (hspec γ (hmem hγ)).2.1])
    (fun t γ hγ c => by
      rw [← map_inv, ← map_mul, ← map_mul,
        (hspec γ (hmem hγ)).2.2 t _ (TorusLift.map_lift hπ _) c])
    fun γ hγ δ hδ hli => ?_
  rcases hsep γ δ (hmem hγ) (hmem hδ) hli with ⟨t, h1, h2⟩ | hrS
  · exact Or.inl ⟨t, by rw [h1, Units.val_one], fun h => h2 (Units.val_eq_one.1 h)⟩
  · refine Or.inr fun s c => ?_
    rw [hcomm γ δ (hmem hγ) (hmem hδ) hrS s c, mul_inv_cancel_right]
    exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
      (CFSG.LieType.Steinberg.xh_mem_chevRoot (xh := fun γ s => q (X x T π γ s)) δ c))

theorem exists_ker_le_zpowers_of_torus_three {G : Type*} [Group G]
    (hA : TauCeti.IsFiniteType τ.cartan) {RG : (Fin τ.rank → ℤ) → Subgroup G} {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 3)
    {x : (Fin τ.rank → ℤ) → k → G} {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan hA ∅)}
    (hroots : (tagDatum τ hA RG).roots = {γ | IsRoot τ γ})
    (hE : ChevalleyExtras (tagDatum τ hA RG) k x C O)
    (hP : PresentationB (Φ := RootSystem.ofCartan hA ∅) x) (T : (Fin τ.rank → kˣ) →* G)
    (hT : ∀ (t : Fin τ.rank → kˣ) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ c,
      T t * x γ c * (T t)⁻¹ = x γ ((rootChar k γ t : k) * c))
    (hprim : ∀ γ, IsRoot τ γ → ∃ m : Fin τ.rank → ℤ, ∑ j, m j * cartanCoord γ j = 1)
    (hnT : ∀ i t, ∃ t', weylElement x i 1 * T t * (weylElement x i 1)⁻¹ = T t')
    (S : Set ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)))
    (hS : ∀ p ∈ S, IsRoot τ p.1 ∧ IsRoot τ p.2 ∧
      ∀ q : ℕ × ℕ, 0 < q.1 → 0 < q.2 → ¬IsRoot τ (q.1 • p.1 + q.2 • p.2))
    (hsep : ∀ γ δ, IsRoot τ γ → IsRoot τ δ → LinIndepPair γ δ →
      (∃ t : Fin τ.rank → kˣ, rootChar k γ t = 1 ∧ rootChar k δ t ≠ 1) ∨ Reach τ γ δ ∨
        (γ, δ) ∈ S)
    {γ₀ δ₀ : Fin τ.rank → ℤ} (h₀ : (γ₀, δ₀) ∈ S) (horb : ∀ p ∈ S, PairOrbit τ γ₀ δ₀ p.1 p.2)
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* G} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ c : E, c ^ 3 = 1 ∧ π.ker ≤ Subgroup.zpowers c := by
  have hx : ∀ γ, IsRoot τ γ → ∀ c d, x γ (c + d) = x γ c * x γ d := fun γ hγ =>
    x_add hroots hE hγ
  have hw1 : (-1 : kˣ) ≠ 1 := FieldThree.neg_one_ne_one_of_card_three hk
  have hk4 : Nat.card k ≠ 4 := by omega
  have hspec : ∀ γ, IsRoot τ γ → IsRootLift x T π γ (X x T π γ) := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact X_isRootLift T (exists_isRootLift hx T hT hcen hπ hk4 hγ hm hw1)
  have hsc : ∀ γ, IsRoot τ γ → ∃ t, rootChar k γ t ≠ 1 := fun γ hγ => by
    obtain ⟨m, hm⟩ := hprim γ hγ
    exact ⟨tvec (-1) m, by rw [rootChar_tvec, hm, zpow_one]; exact hw1⟩
  obtain ⟨hγ₀, hδ₀, hno⟩ := hS _ h₀
  have hc₀ : ∀ s t, ⁅X x T π γ₀ s, X x T π δ₀ t⁆ ∈ Subgroup.center E := fun s t => hcen (by
    rw [MonoidHom.mem_ker, map_commutatorElement, (hspec _ hγ₀).2.1, (hspec _ hδ₀).2.1]
    exact commute_x_of_not_isRoot hroots hE hγ₀ hδ₀ hno s t)
  set c := ⁅X x T π γ₀ 1, X x T π δ₀ 1⁆ with hc
  have : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le_of_mem (hc₀ 1 1))
  refine ⟨c, commutatorElement_pow_three_of_add hk (hspec _ hγ₀).1 hc₀, ?_⟩
  refine (ker_le_closure_of_torus_three hA hk hroots hE hP T hT hprim hnT S hS hsep hπ
    hcen).trans ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  exact commutatorElement_mem_of_pairOrbit hroots hE T hT hcen hπ hnT hspec hsc ⟨hγ₀, hδ₀⟩
    (commutatorElement_mem_zpowers_of_add hk (hspec _ hγ₀).1 (hspec _ hδ₀).1 hc₀) (horb p hp)
    1 1

end CFSG.LieType.Steinberg.CentralExt.WeylLift

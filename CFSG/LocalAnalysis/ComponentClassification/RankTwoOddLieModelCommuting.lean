module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelTight

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {X G : Type} [Group X] [Group G]

theorem eq_one_of_lift_one [Group.IsPerfect X] (ψ : X →* G) (hker : ψ.ker ≤ center X)
    {σ : MulAut X} (hσ : ∀ x, ψ (σ x) = ψ x) : σ = 1 := by
  have hz : ∀ a : X, a⁻¹ * σ a ∈ center X := fun a =>
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel])
  let Fx : Subgroup X :=
    { carrier := {x | σ x = x}
      mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => show σ (a * b) = a * b by
        rw [map_mul, ha, hb]
      one_mem' := map_one σ
      inv_mem' := fun {a} (ha : σ a = a) => show σ a⁻¹ = a⁻¹ by rw [map_inv, ha] }
  have hcomm : commutator X ≤ Fx := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show σ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, show σ a = a * (a⁻¹ * σ a) by group,
      show σ b = b * (b⁻¹ * σ b) by group]
    exact commutatorElement_mul_center a b (hz a) (hz b)
  rw [Group.IsPerfect.commutator_eq_top] at hcomm
  ext x
  exact hcomm (Subgroup.mem_top x)

@[expose] def liftGroup (ψ : X →* G) (𝒯 : Subgroup (MulAut G)) : Subgroup (MulAut X) where
  carrier := {σ | ∃ τ ∈ 𝒯, ∀ x, ψ (σ x) = τ (ψ x)}
  one_mem' := ⟨1, one_mem _, fun _ => rfl⟩
  mul_mem' := by
    rintro σ₁ σ₂ ⟨τ₁, h₁, e₁⟩ ⟨τ₂, h₂, e₂⟩
    exact ⟨τ₁ * τ₂, mul_mem h₁ h₂, fun x => by simp only [MulAut.mul_apply, e₁, e₂]⟩
  inv_mem' := by
    rintro σ ⟨τ, h, e⟩
    refine ⟨τ⁻¹, inv_mem h, fun x => ?_⟩
    have h1 := e (σ⁻¹ x)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, MulAut.inv_apply_self]

theorem isPGroup_liftGroup [Group.IsPerfect X] (ψ : X →* G) (hker : ψ.ker ≤ center X)
    {𝒯 : Subgroup (MulAut G)} (h𝒯 : IsPGroup 2 𝒯) : IsPGroup 2 (liftGroup ψ 𝒯) := by
  rintro ⟨σ, τ, hτ, hσ⟩
  obtain ⟨k, hk⟩ := h𝒯 ⟨τ, hτ⟩
  refine ⟨k, Subtype.ext (eq_one_of_lift_one ψ hker fun x => ?_)⟩
  have hpow : ∀ n : ℕ, ∀ y, ψ ((σ ^ n) y) = (τ ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hσ]
  have hk' : τ ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  rw [SubgroupClass.coe_pow, hpow, hk', MulAut.one_apply]

open SemidirectProduct in
theorem commuting_of_cover (h3 : SL2OuterComm) [Finite X] [Group.IsPerfect X] (ψ : X →* G)
    (hker : ψ.ker ≤ center X) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {J : Subgroup X} (e : J ≃* SL(2, F))
    (hCZ : centralizer ({centralInv e} : Set X) ≤ normalizer (J : Set X))
    (hU : ∀ L : Subgroup X, L ≤ centralizer ({centralInv e} : Set X) →
      centralizer ({centralInv e} : Set X) ≤ normalizer (L : Set X) →
      Nonempty (L ≃* SL(2, F)) → centralInv e ∈ L → L = J)
    (hlift : ∀ τ : MulAut G, ∃ τ' : MulAut X, ∀ x, ψ (τ' x) = τ (ψ x))
    (𝒯 : Subgroup (MulAut G)) (h𝒯 : IsPGroup 2 𝒯) :
    ∃ g : G, ∀ τ ∈ 𝒯, (conjSubgroup g (J.map ψ)).map τ.toMonoidHom = conjSubgroup g (J.map ψ) ∨
      ∀ a ∈ conjSubgroup g (J.map ψ), ∀ b ∈ (conjSubgroup g (J.map ψ)).map τ.toMonoidHom,
        a * b = b * a := by
  classical
  set Λ := liftGroup ψ 𝒯
  have hΛ2 : IsPGroup 2 Λ := isPGroup_liftGroup ψ hker h𝒯
  have : Finite (MulAut X) := Finite.of_injective (fun σ : MulAut X => (σ : X → X))
    DFunLike.coe_injective
  have : Finite Λ := inferInstance
  have : Finite (X ⋊[Λ.subtype] Λ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  set z := centralInv e
  set JH : Subgroup (X ⋊[Λ.subtype] Λ) := J.map inl
  let eH : JH ≃* SL(2, F) :=
    (J.equivMapOfInjective (inl : X →* X ⋊[Λ.subtype] Λ) inl_injective).symm.trans e
  have hzH : centralInv eH = inl z := rfl
  have hconj : ∀ (k : X) (s : Λ) (a : X), (inl k * inr s : X ⋊[Λ.subtype] Λ) * inl a *
      (inl k * inr s)⁻¹ = inl ((MulAut.conj k * (s : MulAut X)) a) := by
    intro k s a
    rw [MulAut.mul_apply, MulAut.conj_apply,
      show (inl k * inr s : X ⋊[Λ.subtype] Λ) * inl a * (inl k * inr s)⁻¹ =
        inl k * (inr s * inl a * inr s⁻¹) * (inl k)⁻¹ by rw [map_inv]; group,
      ← inl_aut]
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
  have hCZH : centralizer ({centralInv eH} : Set (X ⋊[Λ.subtype] Λ)) ≤ normalizer (JH : Set _) := by
    intro x hx
    rw [hzH, mem_centralizer_singleton_iff] at hx
    obtain ⟨k, s, rfl⟩ : ∃ k s, x = inl k * inr s := ⟨x.left, x.right,
      (inl_left_mul_inr_right x).symm⟩
    set σ : MulAut X := MulAut.conj k * (s : MulAut X)
    have hσ : ∀ a, (inl k * inr s : X ⋊[Λ.subtype] Λ) * inl a * (inl k * inr s)⁻¹ = inl (σ a) :=
      hconj k s
    have hσz : σ z = z := by
      have h1 : (inl k * inr s : X ⋊[Λ.subtype] Λ) * inl z * (inl k * inr s)⁻¹ = inl z := by
        rw [hx, mul_inv_cancel_right]
      rw [hσ] at h1
      exact inl_injective h1
    set L := J.map σ.toMonoidHom
    have hmemL : ∀ w, w ∈ L ↔ σ.symm w ∈ J := fun w => by
      simp only [L, Subgroup.mem_map_equiv]
    have hLJ : L = J := by
      refine hU L ?_ ?_ ⟨(J.equivMapOfInjective _ σ.injective).symm.trans e⟩ ?_
      · rintro _ ⟨j, hj, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have hjz : j * z = z * j := mem_centralizer_iff.mp (centralInv_mem_centralizer e) j hj
        show σ j * z = z * σ j
        calc σ j * z = σ j * σ z := by rw [hσz]
          _ = σ (j * z) := (map_mul σ j z).symm
          _ = σ (z * j) := by rw [hjz]
          _ = σ z * σ j := map_mul σ z j
          _ = z * σ j := by rw [hσz]
      · intro c hc
        rw [mem_centralizer_singleton_iff] at hc
        have hc' : σ.symm c ∈ centralizer ({z} : Set X) := by
          rw [mem_centralizer_singleton_iff]
          apply σ.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hσz, hc]
        have hN := hCZ hc'
        rw [mem_normalizer_iff] at hN ⊢
        intro y
        rw [hmemL, hmemL, map_mul, map_mul, map_inv]
        exact hN (σ.symm y)
      · exact (hmemL z).mpr (by
          rw [show σ.symm z = z by rw [MulEquiv.symm_apply_eq, hσz]]
          exact centralInv_mem e)
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hσ]
      exact ⟨σ j, hLJ ▸ (⟨j, hj, rfl⟩ : σ j ∈ L), rfl⟩
    · rintro ⟨j', hj', hj'e⟩
      have h1 : (inl k * inr s : X ⋊[Λ.subtype] Λ) * inl (σ.symm j') * (inl k * inr s)⁻¹ =
          inl j' := by rw [hσ, MulEquiv.apply_symm_apply]
      have hy : y = inl (σ.symm j') := by
        have h2 := hj'e.symm.trans h1.symm
        exact mul_left_cancel (mul_right_cancel h2)
      rw [hy]
      refine ⟨σ.symm j', ?_, rfl⟩
      exact (hmemL j').mp (hLJ.symm ▸ hj')
  have hJK : JH ≤ (inl : X →* X ⋊[Λ.subtype] Λ).range := map_le_range _ _
  have hTH : IsPGroup 2 (inr : Λ →* X ⋊[Λ.subtype] Λ).range := by
    rw [MonoidHom.range_eq_map]
    exact (hΛ2.to_subgroup ⊤).map _
  have hTK : (inr : Λ →* X ⋊[Λ.subtype] Λ).range ≤
      normalizer ((inl : X →* X ⋊[Λ.subtype] Λ).range : Set _) := by
    rw [range_inl_eq_ker_rightHom, normalizer_eq_top]
    exact le_top
  obtain ⟨gH, hgH, hgprop⟩ := exists_conj_fixed_or_commute h3 hF eH hCZH hJK hTH hTK
  obtain ⟨k, rfl⟩ := hgH
  refine ⟨ψ k, fun τ hτ => ?_⟩
  obtain ⟨σ, hσ⟩ := hlift τ
  have hσΛ : σ ∈ Λ := ⟨τ, hτ, hσ⟩
  have h := hgprop (inr ⟨σ, hσΛ⟩) ⟨⟨σ, hσΛ⟩, rfl⟩
  set Y := conjSubgroup k J
  have hY1 : conjSubgroup (inl k) JH = Y.map inl := by
    simp only [JH, Y, conjSubgroup, Subgroup.map_map]
    congr 1
  have hY2 : conjSubgroup (inr ⟨σ, hσΛ⟩) (Y.map (inl : X →* X ⋊[Λ.subtype] Λ)) =
      (Y.map σ.toMonoidHom).map inl := by
    simp only [conjSubgroup, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show (inr ⟨σ, hσΛ⟩ : X ⋊[Λ.subtype] Λ)⁻¹ = inr ⟨σ, hσΛ⟩⁻¹ from (map_inv _ _).symm,
      ← inl_aut]
    rfl
  have hψY : conjSubgroup (ψ k) (J.map ψ) = Y.map ψ := by
    simp only [Y, conjSubgroup, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun j => ?_
    simp [map_mul, map_inv]
  have hψσ : (Y.map σ.toMonoidHom).map ψ = (Y.map ψ).map τ.toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp [hσ]
  rw [hψY]
  rw [hY1, hY2] at h
  rcases h with h | h
  · left
    have h' : Y.map σ.toMonoidHom = Y := Subgroup.map_injective inl_injective h
    rw [← hψσ, h']
  · right
    rw [← hψσ]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := h (inl a) ⟨a, ha, rfl⟩ (inl b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    rw [← map_mul, ← map_mul, inl_injective h1]

@[expose] def fixedSubgroup (Λ : Subgroup (MulAut X)) : Subgroup X where
  carrier := {x | ∀ σ ∈ Λ, σ x = x}
  mul_mem' := fun ha hb σ hσ => by rw [map_mul, ha σ hσ, hb σ hσ]
  one_mem' := fun σ _ => map_one σ
  inv_mem' := fun ha σ hσ => by rw [map_inv, ha σ hσ]

theorem exists_involution_fixed [Finite X] {Λ : Subgroup (MulAut X)} (hΛ : IsPGroup 2 Λ)
    (heven : Even (Nat.card X)) : ∃ w : X, orderOf w = 2 ∧ ∀ σ ∈ Λ, σ w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hΛ.card_modEq_card_fixedPoints X
  have hcard : Nat.card (MulAction.fixedPoints Λ X) = Nat.card (fixedSubgroup Λ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun h σ hσ => h ⟨σ, hσ⟩, fun h σ => h σ σ.2⟩)
  have h2 : 2 ∣ Nat.card (fixedSubgroup Λ) := by
    rw [← hcard]
    exact (Nat.ModEq.dvd_iff hmod (dvd_refl 2)).mp (even_iff_two_dvd.mp heven)
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' (G := fixedSubgroup Λ) 2 h2
  exact ⟨w, by rwa [Subgroup.orderOf_mk] at hw2, hw⟩

section Transport

variable (α : MulAut X)

theorem mem_map_mulAut {L : Subgroup X} {x : X} :
    x ∈ L.map α.toMonoidHom ↔ α.symm x ∈ L :=
  Subgroup.mem_map_equiv

theorem map_le_centralizer_mulAut {L : Subgroup X} {z : X} (h : L ≤ centralizer ({z} : Set X)) :
    L.map α.toMonoidHom ≤ centralizer ({α z} : Set X) := by
  rintro _ ⟨l, hl, rfl⟩
  have := h hl
  rw [mem_centralizer_singleton_iff] at this ⊢
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, this]

theorem centralizer_le_normalizer_map_mulAut {L : Subgroup X} {z : X}
    (h : centralizer ({z} : Set X) ≤ normalizer (L : Set X)) :
    centralizer ({α z} : Set X) ≤ normalizer (L.map α.toMonoidHom : Set X) := by
  intro c hc
  rw [mem_centralizer_singleton_iff] at hc
  have hc' : α.symm c ∈ centralizer ({z} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc]
  have hN := h hc'
  rw [mem_normalizer_iff] at hN ⊢
  intro y
  rw [mem_map_mulAut, mem_map_mulAut, map_mul, map_mul, map_inv]
  exact hN (α.symm y)

theorem map_symm_map_mulAut (L : Subgroup X) :
    (L.map α.symm.toMonoidHom).map α.toMonoidHom = L := by
  ext x
  rw [mem_map_mulAut, mem_map_mulAut, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

end Transport

theorem eq_or_eq_of_map_mulAut (α : MulAut X) {F : Type} [Field F] {z : X} {A B : Subgroup X}
    (hU : ∀ L : Subgroup X, L ≤ centralizer ({z} : Set X) →
      centralizer ({z} : Set X) ≤ normalizer (L : Set X) →
      Nonempty (L ≃* SL(2, F)) → z ∈ L → L = A ∨ L = B)
    {L : Subgroup X} (hLC : L ≤ centralizer ({α z} : Set X))
    (hCN : centralizer ({α z} : Set X) ≤ normalizer (L : Set X)) (hL : Nonempty (L ≃* SL(2, F)))
    (hzL : α z ∈ L) : L = A.map α.toMonoidHom ∨ L = B.map α.toMonoidHom := by
  obtain ⟨eL⟩ := hL
  have h1 := map_le_centralizer_mulAut α.symm hLC
  rw [MulEquiv.symm_apply_apply] at h1
  have h2 := centralizer_le_normalizer_map_mulAut α.symm hCN
  rw [MulEquiv.symm_apply_apply] at h2
  have h3 : Nonempty (L.map α.symm.toMonoidHom ≃* SL(2, F)) :=
    ⟨(L.equivMapOfInjective _ α.symm.injective).symm.trans eL⟩
  have h4 : z ∈ L.map α.symm.toMonoidHom := by
    rw [mem_map_mulAut, MulEquiv.symm_symm]
    exact hzL
  rcases hU _ h1 h2 h3 h4 with h | h
  · left
    rw [← map_symm_map_mulAut α L, h]
  · right
    rw [← map_symm_map_mulAut α L, h]

theorem commuting_of_cover_pair [Finite X] [Group.IsPerfect X] (ψ : X →* G)
    (hker : ψ.ker ≤ center X) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {J L₀ : Subgroup X} (e : J ≃* SL(2, F))
    (hconj : ∀ x y : X, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hCZ : centralizer ({centralInv e} : Set X) ≤ normalizer (J : Set X))
    (hL₀ : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a)
    (hU : ∀ L : Subgroup X, L ≤ centralizer ({centralInv e} : Set X) →
      centralizer ({centralInv e} : Set X) ≤ normalizer (L : Set X) →
      Nonempty (L ≃* SL(2, F)) → centralInv e ∈ L → L = J ∨ L = L₀)
    (hlift : ∀ τ : MulAut G, ∃ τ' : MulAut X, ∀ x, ψ (τ' x) = τ (ψ x))
    (𝒯 : Subgroup (MulAut G)) (h𝒯 : IsPGroup 2 𝒯) :
    ∃ g : G, ∀ τ ∈ 𝒯, (conjSubgroup g (J.map ψ)).map τ.toMonoidHom = conjSubgroup g (J.map ψ) ∨
      ∀ a ∈ conjSubgroup g (J.map ψ), ∀ b ∈ (conjSubgroup g (J.map ψ)).map τ.toMonoidHom,
        a * b = b * a := by
  set Λ := liftGroup ψ 𝒯
  have hΛ2 : IsPGroup 2 Λ := isPGroup_liftGroup ψ hker h𝒯
  set z := centralInv e
  have hz2 : orderOf z = 2 := orderOf_centralInv e hF
  have heven : Even (Nat.card X) := by
    have := orderOf_dvd_natCard z
    rw [hz2] at this
    exact even_iff_two_dvd.mpr this
  obtain ⟨w, hw2, hwfix⟩ := exists_involution_fixed hΛ2 heven
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj z w hz2 hw2)
  set α := MulAut.conj c
  have hαz : α z = w := by rw [MulAut.conj_apply, hc]
  set J'' := J.map α.toMonoidHom
  set L₀'' := L₀.map α.toMonoidHom
  have hU'' : ∀ L : Subgroup X, L ≤ centralizer ({w} : Set X) →
      centralizer ({w} : Set X) ≤ normalizer (L : Set X) →
      Nonempty (L ≃* SL(2, F)) → w ∈ L → L = J'' ∨ L = L₀'' := by
    intro L h1 h2 h3 h4
    rw [← hαz] at h1 h2 h4
    exact eq_or_eq_of_map_mulAut α hU h1 h2 h3 h4
  have hJC : J ≤ centralizer ({z} : Set X) := fun j hj => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp (centralInv_mem_centralizer e) j hj
  have hJ''C : J'' ≤ centralizer ({w} : Set X) := hαz ▸ map_le_centralizer_mulAut α hJC
  have hCZ'' : centralizer ({w} : Set X) ≤ normalizer (J'' : Set X) :=
    hαz ▸ centralizer_le_normalizer_map_mulAut α hCZ
  have hwJ'' : w ∈ J'' := by
    rw [← hαz]
    exact mem_map_of_mem _ (centralInv_mem e)
  have hL₀'' : ∀ a ∈ J'', ∀ b ∈ L₀'', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hL₀ a ha b hb]
  refine ⟨ψ c, fun τ hτ => ?_⟩
  obtain ⟨σ, hσ⟩ := hlift τ
  have hσΛ : σ ∈ Λ := ⟨τ, hτ, hσ⟩
  have hσw : σ w = w := hwfix σ hσΛ
  set M := J''.map σ.toMonoidHom
  have hM : M = J'' ∨ M = L₀'' := by
    have h1 := map_le_centralizer_mulAut σ hJ''C
    have h2 := centralizer_le_normalizer_map_mulAut σ hCZ''
    rw [hσw] at h1 h2
    refine hU'' M h1 h2 ⟨(J''.equivMapOfInjective _ σ.injective).symm.trans
      ((J.equivMapOfInjective _ α.injective).symm.trans e)⟩ ?_
    rw [← hσw]
    exact mem_map_of_mem _ hwJ''
  have hψJ : conjSubgroup (ψ c) (J.map ψ) = J''.map ψ := by
    simp only [J'', conjSubgroup, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun j => ?_
    simp [α, map_mul, map_inv]
  have hψσ : M.map ψ = (J''.map ψ).map τ.toMonoidHom := by
    simp only [M, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp [hσ]
  rw [hψJ, ← hψσ]
  rcases hM with h | h
  · left
    rw [h]
  · right
    rw [h]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hL₀'' a ha b hb]

end CFSG.ComponentClassification.RankTwoOddLie

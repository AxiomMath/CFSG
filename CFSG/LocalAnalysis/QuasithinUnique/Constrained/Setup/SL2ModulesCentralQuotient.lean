module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuter
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open CFSG.GorensteinWalter Projectivization

section Central

theorem commutator_central_left {G : Type*} [Group G] {z : G} (h : z ∈ Subgroup.center G)
    (a b : G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅z, b⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp h b).symm
  have h2 : z * ⁅a, b⁆ * z⁻¹ = ⁅a, b⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp h _).symm
  rw [h2, h1, mul_one]

theorem commutator_central_right {G : Type*} [Group G] {z : G} (h : z ∈ Subgroup.center G)
    (a b : G) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, z⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp h a)
  have h2 : z * ⁅a, b⁆ * z⁻¹ = ⁅a, b⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp h _).symm
  rw [h1, one_mul, h2]

end Central

section RepOfIso

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (L : Subgroup (Module.End (ZMod 2) W)ˣ) (θ : L ≃* SL(2, F))

@[expose] def repOfIso : Representation (ZMod 2) SL(2, F) W :=
  (repOfSubgroup L).comp θ.symm.toMonoidHom

theorem repOfIso_apply (g : SL(2, F)) (w : W) : repOfIso L θ g w = (θ.symm g).1.val w := rfl

theorem repOfIso_theta (l : L) (w : W) : repOfIso L θ (θ l) w = l.1.val w := by
  rw [repOfIso_apply, MulEquiv.symm_apply_apply]

theorem repOfIso_toHomUnits (g : SL(2, F)) : (repOfIso L θ).toHomUnits g = (θ.symm g).1 :=
  Units.ext rfl

theorem repOfIso_injective : Function.Injective (repOfIso L θ) := by
  intro g h e
  apply θ.symm.injective
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) W => f w) e

theorem repOfIso_range : (repOfIso L θ).toHomUnits.range = L := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    rw [repOfIso_toHomUnits]
    exact (θ.symm g).2
  · intro hu
    refine ⟨θ ⟨u, hu⟩, ?_⟩
    rw [repOfIso_toHomUnits, MulEquiv.symm_apply_apply]

theorem repOfIso_isIrreducible (hirr : (repOfSubgroup L).IsIrreducible) :
    (repOfIso L θ).IsIrreducible := by
  rw [isIrreducible_iff] at hirr ⊢
  obtain ⟨hnt, hWirr⟩ := hirr
  refine ⟨hnt, fun U hU => hWirr U (fun l u hu => ?_)⟩
  have h := hU (θ l) u hu
  rw [repOfIso_theta] at h
  exact h

theorem natCard_endRing_repOfIso :
    Nat.card (EndRing (repOfIso L θ)) = Nat.card (EndRing (repOfSubgroup L)) := by
  rw [natCard_endRing, natCard_endRing]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun φ => ?_))
  constructor
  · intro h l v
    have h' := h (θ l) v
    rw [repOfIso_theta, repOfIso_theta] at h'
    exact h'
  · intro h g v
    exact h (θ.symm g) v

end RepOfIso

section Alternatives

theorem alternatives_of_iso {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (L : Subgroup (Module.End (ZMod 2) W)ˣ) (θ : L ≃* SL(2, F))
    (hirr : (repOfSubgroup L).IsIrreducible)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (L : Set (Module.End (ZMod 2) W)ˣ))
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w}) :
    ((A ≤ L ∧ L ⊔ A = L ∧ ∃ β : W ≃+ (Fin 2 → F),
        (∀ (l : L) (w : W), β (l.1.val w) = (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β w)) ∧
        ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
          (∀ g : SL(2, F), g ∈ (A.subgroupOf L).map θ.toMonoidHom ↔
            ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
              ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)) ∧
          Nat.card (EndRing (repOfSubgroup L)) = 2 ^ n ∧ Nat.card A = 2 ^ n ∧
          (∀ w, (∀ a ∈ A, a.val w = w) ↔ β w ∈ ℓ)) ∨
      (¬ A ≤ L ∧ n = 2 ∧ Nat.card (EndRing (repOfSubgroup L)) = 2 ∧
        Module.finrank (ZMod 2) W = 4 ∧ Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧
        ∃ (ψ : ↥(L ⊔ A) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
          (β : W ≃ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F)))),
          (∀ (l : L) (h : l.1 ∈ L ⊔ A), ψ ⟨l.1, h⟩ = MulAction.toPerm (θ l)) ∧
          (∀ (y : ↥(L ⊔ A)) (w : W),
            ((β ((y : (Module.End (ZMod 2) W)ˣ).val w) : ↥(evenWeight (ℙ F (Fin 2 → F)))) :
                ℙ F (Fin 2 → F) → ZMod 2) =
              permAct (ψ y) (β w : ℙ F (Fin 2 → F) → ZMod 2)) ∧
          ((L.subgroupOf (L ⊔ A)).map ψ.toMonoidHom = alternatingGroup (ℙ F (Fin 2 → F))) ∧
          ((∃ x y, x ≠ y ∧ (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
              Subgroup.closure {Equiv.swap x y}) ∨
            (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
              (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
                Subgroup.closure {Equiv.swap x y, Equiv.swap z t})))) ∧
    Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρirr := repOfIso_isIrreducible L θ hirr
  have hρinj := repOfIso_injective L θ
  have hrange := repOfIso_range L θ
  by_cases hAL : A ≤ L
  ·
    have hAea : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf L) :=
      CFSG.IsElementaryAbelian.subgroupOf hAL
    set A' : Subgroup SL(2, F) := (A.subgroupOf L).map θ.toMonoidHom with hA'
    have hA'ea : CFSG.IsElementaryAbelian 2 A' := CFSG.IsElementaryAbelian.map θ.toMonoidHom
    have hcardA : Nat.card A' = Nat.card A :=
      ((Nat.card_congr ((A.subgroupOf L).equivMapOfInjective θ.toMonoidHom θ.injective).toEquiv).symm
        ).trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv)
    have hA1' : A' ≠ ⊥ := by
      intro h
      apply hA1
      rw [← Subgroup.card_eq_one, ← hcardA, h]
      exact Subgroup.card_bot
    have hfix : ∀ w : W, (∀ a ∈ A', repOfIso L θ a w = w) ↔ ∀ c ∈ A, c.val w = w := by
      intro w
      constructor
      · intro h c hc
        have := h (θ ⟨c, hAL hc⟩) ⟨⟨c, hAL hc⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
        rwa [repOfIso_theta] at this
      · intro h a ha
        obtain ⟨y, hy, rfl⟩ := ha
        show repOfIso L θ (θ y) w = w
        rw [repOfIso_theta]
        exact h y.1 (Subgroup.mem_subgroupOf.mp hy)
    have hfixcard : Nat.card {w : W // ∀ a ∈ A', repOfIso L θ a w = w} =
        Nat.card {w : W // ∀ a ∈ A, a.val w = w} :=
      Nat.card_congr (Equiv.subtypeEquivRight hfix)
    have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
      one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
    have hnt : ∃ g, repOfIso L θ g ≠ 1 :=
      ⟨uElt 1, fun h => hne (hρinj (h.trans (map_one _).symm))⟩
    have hoff' : Nat.card W ≤ Nat.card A' * Nat.card {w : W // ∀ a ∈ A', repOfIso L θ a w = w} := by
      rw [hcardA, hfixcard]
      exact hoff
    obtain ⟨φ, hφ, -, -, hEnd, ℓ, hℓ, hAℓ, hCℓ, hAcard, -, hprod⟩ :=
      binary_SL2_internal_offender_natural_module (n := n) (by omega) hF (repOfIso L θ) hρirr hnt
        A' hA1' hoff'
    refine ⟨Or.inl ⟨hAL, sup_eq_left.mpr hAL, φ, ?_, ℓ, hℓ, hAℓ, ?_, ?_, ?_⟩, ?_⟩
    · intro l w
      have h := hφ (θ l) w
      rwa [repOfIso_theta] at h
    · rw [← natCard_endRing_repOfIso L θ, natCard_endRing]
      exact hEnd
    · rw [← hcardA]
      exact hAcard
    · intro w
      rw [← hfix w]
      exact hCℓ w
    · rw [← hcardA, ← hfixcard]
      exact hprod
  ·
    obtain ⟨hn2, hD2, hfin, hΩ, ψ, β, hψ1, hψ2, hψ3, hψ4, hcard⟩ :=
      binary_SL2_outer_quadratic_offender_deleted_module hn hF (repOfIso L θ) hρinj hρirr L hrange
        A hA1 hAN hquad hoff hAL
    refine ⟨Or.inr ⟨hAL, hn2, ?_, hfin, hΩ, ψ, β, ?_, hψ2, hψ3, hψ4⟩, hcard⟩
    · rw [← natCard_endRing_repOfIso L θ]
      exact hD2
    · intro l h
      have hmem : (repOfIso L θ).toHomUnits (θ l) ∈ L ⊔ A := by
        rw [repOfIso_toHomUnits, MulEquiv.symm_apply_apply]
        exact h
      have h1 := hψ1 (θ l) hmem
      have h3 : l.1 = (repOfIso L θ).toHomUnits (θ l) := by
        rw [repOfIso_toHomUnits, MulEquiv.symm_apply_apply]
      have h2 : (⟨l.1, h⟩ : ↥(L ⊔ A)) = ⟨(repOfIso L θ).toHomUnits (θ l), hmem⟩ :=
        Subtype.ext h3
      rw [h2]
      exact h1

end Alternatives

section Main

theorem central_quotient_SL2_quadratic_offender_alternatives
    {n : ℕ} (hn : 2 ≤ n) {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n) [Fintype (ℙ F (Fin 2 → F))]
    [DecidableEq (ℙ F (Fin 2 → F))] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (L : Subgroup (Module.End (ZMod 2) W)ˣ) (hirr : (repOfSubgroup L).IsIrreducible)
    (hLperf : Group.IsPerfect L) (α : (L ⧸ Subgroup.center L) ≃* SL(2, F))
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (L : Set (Module.End (ZMod 2) W)ˣ))
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b.val (a.val w - w) = a.val w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w}) :
    Subgroup.center L = ⊥ ∧ ∃ θ : L ≃* SL(2, F), (∀ l : L, θ l = α (QuotientGroup.mk l)) ∧
      (((A ≤ L ∧ L ⊔ A = L ∧ ∃ β : W ≃+ (Fin 2 → F),
          (∀ (l : L) (w : W), β (l.1.val w) = (θ l : Matrix (Fin 2) (Fin 2) F).mulVec (β w)) ∧
          ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
            (∀ g : SL(2, F), g ∈ (A.subgroupOf L).map θ.toMonoidHom ↔
              ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
                ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)) ∧
            Nat.card (EndRing (repOfSubgroup L)) = 2 ^ n ∧ Nat.card A = 2 ^ n ∧
            (∀ w, (∀ a ∈ A, a.val w = w) ↔ β w ∈ ℓ)) ∨
        (¬ A ≤ L ∧ n = 2 ∧ Nat.card (EndRing (repOfSubgroup L)) = 2 ∧
          Module.finrank (ZMod 2) W = 4 ∧ Fintype.card (ℙ F (Fin 2 → F)) = 5 ∧
          ∃ (ψ : ↥(L ⊔ A) ≃* Equiv.Perm (ℙ F (Fin 2 → F)))
            (β : W ≃ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F)))),
            (∀ (l : L) (h : l.1 ∈ L ⊔ A), ψ ⟨l.1, h⟩ = MulAction.toPerm (θ l)) ∧
            (∀ (y : ↥(L ⊔ A)) (w : W),
              ((β ((y : (Module.End (ZMod 2) W)ˣ).val w) : ↥(evenWeight (ℙ F (Fin 2 → F)))) :
                  ℙ F (Fin 2 → F) → ZMod 2) =
                permAct (ψ y) (β w : ℙ F (Fin 2 → F) → ZMod 2)) ∧
            ((L.subgroupOf (L ⊔ A)).map ψ.toMonoidHom = alternatingGroup (ℙ F (Fin 2 → F))) ∧
            ((∃ x y, x ≠ y ∧ (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
                Subgroup.closure {Equiv.swap x y}) ∨
              (∃ x y z t, x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
                (A.subgroupOf (L ⊔ A)).map ψ.toMonoidHom =
                  Subgroup.closure {Equiv.swap x y, Equiv.swap z t})))) ∧
        Nat.card A * Nat.card {w : W // ∀ a ∈ A, a.val w = w} = Nat.card W) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F 2 := charP_two_of_card_eq hF
  have hLfin : Finite ↥L := by
    have := finite_units_end (k₀ := ZMod 2) (W := W)
    infer_instance
  have hzodd : ∀ z : L, z ∈ Subgroup.center L → Odd (orderOf z) := by
    intro z hz
    have hcomm : ∀ g : L, z.1.val * repOfSubgroup L g = repOfSubgroup L g * z.1.val := by
      intro g
      have h := Subgroup.mem_center_iff.mp hz g
      have h' := congrArg (fun u : L => u.1.val) h
      simp only [Subgroup.coe_mul, Units.val_mul] at h'
      exact h'.symm
    have h := odd_orderOf_of_commute (repOfSubgroup L) hirr z.1 hcomm
    rwa [Subgroup.orderOf_coe] at h
  have hcenodd : Odd (Nat.card (Subgroup.center L)) := by
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    have h2 : 2 ∣ Nat.card (Subgroup.center L) := even_iff_two_dvd.mp hnot
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have h := hzodd x.1 x.2
    rw [Subgroup.orderOf_coe, hx] at h
    exact absurd h (by decide)
  let π : L →* SL(2, F) := α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := α.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker]
    show α (QuotientGroup.mk' (Subgroup.center L) l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff l
  obtain ⟨s, hs, -, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
    (K := F) (n := 2) (le_refl 2) hπ hker.le (by rw [hker]; exact hcenodd)
  have hcenter : Subgroup.center L = ⊥ := by
    have hdec : ∀ l : L, l * (s (π l))⁻¹ ∈ Subgroup.center L := by
      intro l
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
    have hcomm : commutator L ≤ s.range := by
      show ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ ≤ s.range
      refine Subgroup.commutator_le.mpr (fun l₁ _ l₂ _ => ?_)
      have key : ⁅l₁, l₂⁆ = ⁅s (π l₁), s (π l₂)⁆ := by
        calc ⁅l₁, l₂⁆ = ⁅(l₁ * (s (π l₁))⁻¹) * s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ := by
              rw [inv_mul_cancel_right, inv_mul_cancel_right]
          _ = ⁅s (π l₁), (l₂ * (s (π l₂))⁻¹) * s (π l₂)⁆ :=
              commutator_central_left (hdec l₁) _ _
          _ = ⁅s (π l₁), s (π l₂)⁆ := commutator_central_right (hdec l₂) _ _
      rw [key, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have hRtop : s.range = ⊤ := by
      rw [eq_top_iff, ← Group.isPerfect_def.mp hLperf]
      exact hcomm
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz1 : π z = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hz
    have hzs : z ∈ s.range := by rw [hRtop]; exact Subgroup.mem_top z
    obtain ⟨g, rfl⟩ := hzs
    have hg : g = 1 := by rw [← hs g]; exact hz1
    rw [hg, map_one]
  have hθinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h : l ∈ π.ker := hl
    rw [hker, hcenter] at h
    exact Subgroup.mem_bot.mp h
  let θ : L ≃* SL(2, F) := MulEquiv.ofBijective π ⟨hθinj, hπ⟩
  exact ⟨hcenter, θ, fun l => rfl, alternatives_of_iso hn hF L θ hirr A hA1 hAN hquad hoff⟩

end Main

end CFSG.QuasithinUnique.Setup.SL2Modules

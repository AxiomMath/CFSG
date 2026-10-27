module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Comp

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.PerfectAutomorphisms
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3_card_le_card_actImage_of_trivial_two {G : Type} [Group G] [Finite G] {B J T : Subgroup G}
    (hB : GLAIsBmax 3 B) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hcen : Subgroup.center (PSimple 3 J) = ⊥)
    (F : Subgroup (PSimple 3 J)) (hF : IsElemAbelian 3 F)
    (hTN : T ≤ Subgroup.normalizer (J : Set G)) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hT1 : ∀ t : ↥(Subgroup.normalizer (J : Set G)), (t : G) ∈ T → actHom 3 J t = 1) :
    Nat.card F ≤ Nat.card (actImage 3 J B) := by
  classical
  set N := Subgroup.normalizer (J : Set G) with hN
  set φ : ↥N →* MulAut (PSimple 3 J) := actHom 3 J with hφ
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  let σ : PSimple 3 J →* WQ 3 J := QuotientGroup.lift (Subgroup.center (PQuot 3 J)) (psiHom 3 J)
    (fun x hx => by rw [hZ, Subgroup.mem_bot] at hx; subst hx; exact map_one _)
  have hσmk : ∀ q, σ (QuotientGroup.mk q) = psiHom 3 J q := fun q => rfl
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    rw [MonoidHom.mem_ker, hσmk] at hs
    have : q = 1 := psiHom_injective 3 J (hs.trans (map_one _).symm)
    rw [this]
    exact (Subgroup.mem_bot).2 (QuotientGroup.mk_one _)
  have hcompat : ∀ (γ : ↥N) (s : PSimple 3 J),
      σ (φ γ s) = QuotientGroup.mk γ * σ s * (QuotientGroup.mk γ)⁻¹ := by
    intro γ s
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    have h1 : φ γ (QuotientGroup.mk q) = QuotientGroup.mk (barAut 3 J γ q) :=
      onCenterQuotient_apply_mk (barAut 3 J γ) q
    rw [h1, hσmk, hσmk, psiHom_barAut]
  let f : ↥B' →* MulAut (PSimple 3 J) := φ.comp B'.subtype
  let β : ↥B' →* WQ 3 J := (QuotientGroup.mk' (oqSub 3 J)).comp B'.subtype
  have hBab : ∀ x y : ↥B', x * y = y * x := fun x y =>
    Subtype.ext (Subtype.ext (isElemAbelian_commute hB.1 (Subgroup.mem_subgroupOf.1 x.2)
      (Subgroup.mem_subgroupOf.1 y.2)))
  have hB3 : ∀ x : ↥B', x ^ 3 = 1 := fun x =>
    Subtype.ext (Subtype.ext (hB.1.2 _ (Subgroup.mem_subgroupOf.1 x.2)))
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have h1 : ((b : ↥N) : G) ∈ GLAPPrimeCoreOf 3 J :=
      Subgroup.mem_subgroupOf.1
        ((QuotientGroup.eq_one_iff (N := oqSub 3 J) ((b : ↥B') : ↥N)).1 hb)
    have h2 : ((b : ↥N) : G) ^ 3 = 1 := hB.1.2 _ (Subgroup.mem_subgroupOf.1 b.2)
    let o : ↥(GLAPPrimeCoreOf 3 J) := ⟨_, h1⟩
    have h3 : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext h2)
    have h4 : orderOf o ∣ Nat.card (GLAPPrimeCoreOf 3 J) := orderOf_dvd_natCard o
    have h5 : orderOf o = 1 := Nat.eq_one_of_dvd_coprimes
      (i183_coprime_card_glaPPrimeCoreOf (G := G) Nat.prime_three J) h3 h4
    have h6 : o = 1 := orderOf_eq_one_iff.1 h5
    have h7 : ((b : ↥N) : G) = 1 := congrArg Subtype.val h6
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h7))
  have hrange : f.range = actImage 3 J B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  set B₁ : Subgroup ↥B' := f.ker with hB₁
  have hcomm : ∀ (s : ↥F) (b : ↥B₁),
      Commute ((σ.comp F.subtype) s) ((β.comp B₁.subtype) b) := by
    intro s b
    have hb : f (b : ↥B') = 1 := b.2
    have h1 := hcompat ((b : ↥B') : ↥N) (s : PSimple 3 J)
    have h2 : φ ((b : ↥B') : ↥N) (s : PSimple 3 J) = (s : PSimple 3 J) := by
      have : φ ((b : ↥B') : ↥N) = 1 := hb
      rw [this]
      rfl
    rw [h2] at h1
    show σ (s : PSimple 3 J) * β (b : ↥B') = β (b : ↥B') * σ (s : PSimple 3 J)
    change σ (s : PSimple 3 J) = QuotientGroup.mk ((b : ↥B') : ↥N) * σ (s : PSimple 3 J) *
      (QuotientGroup.mk ((b : ↥B') : ↥N))⁻¹ at h1
    have h3 : σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N) =
        QuotientGroup.mk ((b : ↥B') : ↥N) * σ (s : PSimple 3 J) := by
      rw [eq_mul_inv_iff_mul_eq] at h1
      exact h1
    exact h3
  let μ : ↥F × ↥B₁ →* WQ 3 J :=
    MonoidHom.noncommCoprod (σ.comp F.subtype) (β.comp B₁.subtype) hcomm
  have hμ : ∀ (s : ↥F) (b : ↥B₁), μ (s, b) = σ (s : PSimple 3 J) * β ((b : ↥B') : ↥B') := fun s b =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hμinj : Function.Injective μ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨s, b⟩ hu
    rw [MonoidHom.mem_ker, hμ] at hu
    have hb : f (b : ↥B') = 1 := b.2
    have h1 : QuotientGroup.mk ((b : ↥B') : ↥N) = (σ (s : PSimple 3 J))⁻¹ := by
      change β (b : ↥B') = _
      exact eq_inv_of_mul_eq_one_right hu
    have h2 : ∀ t : PSimple 3 J, φ ((b : ↥B') : ↥N) t = (s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J) := by
      intro t
      apply hσinj
      rw [hcompat, h1, map_mul, map_mul, map_inv, inv_inv]
    have h5 : (s : PSimple 3 J) ∈ Subgroup.center (PSimple 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro t
      have := h2 t
      have h0 : φ ((b : ↥B') : ↥N) t = t := by
        have : φ ((b : ↥B') : ↥N) = 1 := hb
        rw [this]
        rfl
      rw [h0] at this
      calc t * (s : PSimple 3 J) = (s : PSimple 3 J) * (s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J) := by group
        _ = (s : PSimple 3 J) * ((s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J)) := by group
        _ = (s : PSimple 3 J) * t := by rw [← this]
    rw [hcen, Subgroup.mem_bot] at h5
    have h6 : s = 1 := Subtype.ext h5
    rw [h5, map_one, inv_one] at h1
    have h7 : (b : ↥B') = 1 := hβinj (h1.trans (map_one β).symm)
    exact (Subgroup.mem_bot).2 (Prod.ext h6 (Subtype.ext h7))
  have hĒ : IsElemAbelian 3 μ.range := by
    refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hBab _ _))
      exact isElemAbelian_commute hF u.1.2 v.1.2
    · rintro _ ⟨u, rfl⟩
      rw [← map_pow]
      have h1 : u ^ 3 = 1 := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hB3 _))
        exact hF.2 _ u.1.2
      rw [h1, map_one]
  have hcardĒ : Nat.card μ.range = Nat.card F * Nat.card B₁ := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
  set TN : Subgroup ↥N := T.subgroupOf N with hTN'
  set Tb : Subgroup (WQ 3 J) := TN.map (QuotientGroup.mk' (oqSub 3 J)) with hTb
  have hσT : ∀ s : PSimple 3 J, ∀ y ∈ Tb, σ s * y = y * σ s := by
    rintro s _ ⟨t, ht, rfl⟩
    have h0 : φ t = 1 := hT1 t (Subgroup.mem_subgroupOf.1 ht)
    have h1 := hcompat t s
    rw [h0] at h1
    change σ s = QuotientGroup.mk t * σ s * (QuotientGroup.mk t)⁻¹ at h1
    rw [eq_mul_inv_iff_mul_eq] at h1
    exact h1
  have hβT : ∀ b : ↥B', ∀ y ∈ Tb, β b * y * (β b)⁻¹ ∈ Tb := by
    rintro b _ ⟨t, ht, rfl⟩
    refine ⟨((b : ↥N) * t * (b : ↥N)⁻¹), show ((b : ↥N) * t * (b : ↥N)⁻¹) ∈ TN from ?_, ?_⟩
    · have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 (show t ∈ TN from ht)
      rw [hTN', Subgroup.mem_subgroupOf]
      have hbB : ((b : ↥N) : G) ∈ B := Subgroup.mem_subgroupOf.1 b.2
      have := Subgroup.mem_normalizer_iff.1 (hBT hbB) (t : G)
      simpa using this.1 ht'
    · simp [β]
  have hET : μ.range ≤ Subgroup.normalizer (Tb : Set (WQ 3 J)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨⟨s, b⟩, rfl⟩ y hy
    rw [hμ]
    have h1 := hβT ((b : ↥B') : ↥B') y hy
    have h2 : σ (s : PSimple 3 J) * (β (b : ↥B') * y * (β (b : ↥B'))⁻¹) *
        (σ (s : PSimple 3 J))⁻¹ = β (b : ↥B') * y * (β (b : ↥B'))⁻¹ := by
      rw [hσT _ _ h1, mul_assoc, mul_inv_cancel, mul_one]
    have h3 : σ (s : PSimple 3 J) * β (b : ↥B') * y * (σ (s : PSimple 3 J) * β (b : ↥B'))⁻¹
        = σ (s : PSimple 3 J) * (β (b : ↥B') * y * (β (b : ↥B'))⁻¹) *
            (σ (s : PSimple 3 J))⁻¹ := by group
    rw [h3, h2]
    exact h1
  have hTNne : TN ≠ ⊥ := by
    intro h
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have : (⟨t, hTN ht⟩ : ↥N) ∈ TN := Subgroup.mem_subgroupOf.2 ht
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hTN2 : IsPGroup 2 TN := by
    obtain ⟨j, hj⟩ := hT2.exists_card_eq
    exact IsPGroup.of_card (n := j) (by
      rw [hTN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv]
      exact hj)
  have hle := d3_card_le_of_normalizes_image hB (oqSub 3 J) (not_dvd_card_oqSub J) hĒ hTNne hTN2 hET
  have hB'card : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv
  have hc2 : Nat.card ↥B' = Nat.card f.range * Nat.card f.ker := card_eq_range_mul_ker f
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  rw [hcardĒ, ← hB'card, hc2, hrange] at hle
  exact Nat.le_of_mul_le_mul_right hle hkpos

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.GH74.GLS.Stage1.Main.BrG2Y
public import CFSG.GH74.GLS.IVK.Lifted.IIAutC

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Main

section Quat

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

@[expose] def G2Ctx.R : Subgroup (CentralizerBar z) := barOf z S ⊓ (C.K₁ ⊔ C.K₂)

@[expose] def G2Ctx.P₁ : Subgroup (CentralizerBar z) := C.R ⊓ C.K₁

@[expose] def G2Ctx.P₂ : Subgroup (CentralizerBar z) := C.R ⊓ C.K₂

include C in
theorem G2Ctx.sylow_R (hcen : Cen2 G z S) : IsSylowOf 2 C.R (C.K₁ ⊔ C.K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRcard, -⟩ := C.sylow_inf hcen
  have hKfac := y_factorization_K C.v₁ C.v₂ C.e₁ C.e₂ C.comm C.inf_card
  refine isSylowOf_of_card (inf_le_right : barOf z S ⊓ (C.K₁ ⊔ C.K₂) ≤ _) ?_
  show Nat.card ↥(barOf z S ⊓ (C.K₁ ⊔ C.K₂)) = _
  rw [hRcard, hKfac]

theorem G2Ctx.normalizer_K₁ : C.K₁ ⊔ C.K₂ ≤ normalizer (C.K₁ : Set (CentralizerBar z)) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hy
  refine mul_mem (Subgroup.le_normalizer ha) ?_
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact C.comm g hg b hb

theorem G2Ctx.normalizer_K₂ : C.K₁ ⊔ C.K₂ ≤ normalizer (C.K₂ : Set (CentralizerBar z)) := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := y_mem_sup_of_commute C.comm hy
  refine mul_mem ?_ (Subgroup.le_normalizer hb)
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (C.comm a ha g hg).symm

include C in
theorem G2Ctx.sylow_P₁ (hcen : Cen2 G z S) : IsSylowOf 2 C.P₁ C.K₁ :=
  (C.sylow_R hcen).inf_of_le_normalizer le_sup_left C.normalizer_K₁

include C in
theorem G2Ctx.sylow_P₂ (hcen : Cen2 G z S) : IsSylowOf 2 C.P₂ C.K₂ :=
  (C.sylow_R hcen).inf_of_le_normalizer le_sup_right C.normalizer_K₂

include C in
theorem G2Ctx.card_P₁ (hcen : Cen2 G z S) : Nat.card ↥C.P₁ = 2 ^ (C.n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(C.sylow_P₁ hcen).card_eq, Nat.card_congr C.e₁.toEquiv, C.v₁]

include C in
theorem G2Ctx.card_P₂ (hcen : Cen2 G z S) : Nat.card ↥C.P₂ = 2 ^ (C.n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(C.sylow_P₂ hcen).card_eq, Nat.card_congr C.e₂.toEquiv, C.v₂]

end Quat

section QuatCtx

open CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

theorem g2_card_center_two {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : K ≃* StatedSL 2 F) {ζ : K} (hζc : ζ ∈ Subgroup.center K)
    (hζo : orderOf ζ = 2) : Nat.card (Subgroup.center K) = 2 := by
  have hz : Subgroup.center K = zpowers ζ := by
    apply le_antisymm
    · intro x hx
      have := kabs_center_cases hodd (e.trans (specialLinearGroupEquivStatedSL 2 F).symm) hζo hx
      rcases this with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact mem_zpowers ζ
    · exact Subgroup.zpowers_le.2 hζc
  rw [hz, Nat.card_zpowers, hζo]

include C in
theorem G2Ctx.isSL2Or2A7₁ (hcen : Cen2 G z S) : IsSL2Or2A7 ↥C.K₁ := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  refine ⟨Or.inl ⟨C.F₁, inferInstance, inferInstance, ⟨C.odd₁, C.five⟩, ⟨C.e₁⟩⟩, ?_⟩
  refine g2_card_center_two C.odd₁ C.e₁ (ζ := ⟨ζ, hζ₁⟩) ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (C.comm g g.2 ζ hζ₂)
  · rw [orderOf_mk]; exact hζo

include C in
theorem G2Ctx.isSL2Or2A7₂ (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂) : IsSL2Or2A7 ↥C.K₂ := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, -, -⟩ := C.exists_zeta hcen
  refine ⟨Or.inl ⟨C.F₂, inferInstance, inferInstance, ⟨C.odd₂, h5⟩, ⟨C.e₂⟩⟩, ?_⟩
  refine g2_card_center_two C.odd₂ C.e₂ (ζ := ⟨ζ, hζ₂⟩) ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (C.comm ζ hζ₁ g g.2).symm
  · rw [orderOf_mk]; exact hζo

end QuatCtx

section QuatData

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

theorem isQuaternionTwoGroup_exp {Y : Type} [Group Y] {m n : ℕ} (h : IVK.IsQuaternionTwoGroup Y m)
    (hc : Nat.card Y = 2 ^ n) : m = n := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  have hne : NeZero (2 ^ (m - 2)) := ⟨by positivity⟩
  have h1 : Nat.card Y = 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : m = (m - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [pow_add]; ring
    omega
  rw [hc] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

include C in
theorem G2Ctx.P_inf (hcen : Cen2 G z S) : C.P₁ ⊓ C.P₂ = C.K₁ ⊓ C.K₂ := by
  obtain ⟨ζ, hζ₁, hζ₂, hζo, hζT, -⟩ := C.exists_zeta hcen
  have hζR : ζ ∈ C.R := ⟨hζT, Subgroup.mem_sup_left hζ₁⟩
  have hzp : zpowers ζ ≤ C.K₁ ⊓ C.K₂ := Subgroup.zpowers_le.2 ⟨hζ₁, hζ₂⟩
  have hcardz : Nat.card ↥(zpowers ζ) = 2 := by rw [Nat.card_zpowers, hζo]
  have heq : zpowers ζ = C.K₁ ⊓ C.K₂ :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcardz, C.inf_card])
  have hle : C.K₁ ⊓ C.K₂ ≤ C.R := by
    rw [← heq, Subgroup.zpowers_le]; exact hζR
  apply le_antisymm
  · exact inf_le_inf inf_le_right inf_le_right
  · exact le_inf (le_inf hle inf_le_left) (le_inf hle inf_le_right)

include C in
theorem G2Ctx.card_P_inf (hcen : Cen2 G z S) : Nat.card ↥(C.P₁ ⊓ C.P₂) = 2 := by
  rw [C.P_inf hcen]; exact C.inf_card

theorem G2Ctx.P_comm : ∀ a ∈ C.P₁, ∀ b ∈ C.P₂, a * b = b * a :=
  fun _ ha _ hb => C.comm _ ha.2 _ hb.2

include C in
theorem G2Ctx.P_sup (hcen : Cen2 G z S) : C.P₁ ⊔ C.P₂ = C.R := by
  have hle : C.P₁ ⊔ C.P₂ ≤ C.R := sup_le inf_le_left inf_le_left
  have hmul := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C.P₁ C.P₂ C.P_comm).1
  rw [C.card_P_inf hcen, C.card_P₁ hcen, C.card_P₂ hcen] at hmul
  obtain ⟨hRcard, -⟩ := C.sylow_inf hcen
  have hx : Nat.card ↥(C.P₁ ⊔ C.P₂) = 2 ^ (2 * C.n + 1) := by
    have h2 : 2 ^ (C.n + 1) * 2 ^ (C.n + 1) = 2 * 2 ^ (2 * C.n + 1) := by ring
    omega
  apply Subgroup.eq_of_le_of_card_ge hle
  show Nat.card ↥(barOf z S ⊓ (C.K₁ ⊔ C.K₂)) ≤ _
  rw [hRcard, hx]

end QuatData

section QuatQ

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (C : G2Ctx z S)

include C in
theorem G2Ctx.quat₁ (hcen : Cen2 G z S) :
    IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (C.sylow_P₁ hcen).exists_sylow_eq_subgroupOf
  obtain ⟨m, h3, ⟨e⟩⟩ := CFSG.GH74.GLS.IVK.Lifted.sylow_quat_of_sl2or2a7 (C.isSL2Or2A7₁ hcen) Q
  have hP : IVK.IsQuaternionTwoGroup ↥C.P₁ m :=
    ⟨h3, ⟨(Subgroup.subgroupOfEquivOfLe (inf_le_right : C.P₁ ≤ C.K₁)).symm.trans
      ((MulEquiv.subgroupCongr hQ).symm.trans e)⟩⟩
  have hm := isQuaternionTwoGroup_exp hP (C.card_P₁ hcen)
  rwa [hm] at hP

include C in
theorem G2Ctx.quat₂ (hcen : Cen2 G z S) (h5 : 5 ≤ Nat.card C.F₂) :
    IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (C.sylow_P₂ hcen).exists_sylow_eq_subgroupOf
  obtain ⟨m, h3, ⟨e⟩⟩ :=
    CFSG.GH74.GLS.IVK.Lifted.sylow_quat_of_sl2or2a7 (C.isSL2Or2A7₂ hcen h5) Q
  have hP : IVK.IsQuaternionTwoGroup ↥C.P₂ m :=
    ⟨h3, ⟨(Subgroup.subgroupOfEquivOfLe (inf_le_right : C.P₂ ≤ C.K₂)).symm.trans
      ((MulEquiv.subgroupCongr hQ).symm.trans e)⟩⟩
  have hm := isQuaternionTwoGroup_exp hP (C.card_P₂ hcen)
  rwa [hm] at hP

end QuatQ

section Lift

theorem isCentralProd_map {X W : Type} [Group X] [Group W] (f : X →* W) (hf : Function.Injective f)
    {A B C' : Subgroup X} (h : IsCentralProd A B C') :
    IsCentralProd (A.map f) (B.map f) (C'.map f) := by
  obtain ⟨hsup, hcomm, hcard⟩ := h
  refine ⟨by rw [← Subgroup.map_sup, hsup], ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_inf _ _ _ hf, Subgroup.card_map_of_injective hf]
    exact hcard

theorem isCentralProd_subgroupOf {X : Type} [Group X] {T A B C' : Subgroup X} (hA : A ≤ T)
    (hB : B ≤ T) (h : IsCentralProd A B C') :
    IsCentralProd (A.subgroupOf T) (B.subgroupOf T) (C'.subgroupOf T) := by
  obtain ⟨hsup, hcomm, hcard⟩ := h
  refine ⟨by rw [← Subgroup.subgroupOf_sup hA hB, hsup], ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm a ha b hb)
  · have h1 : A.subgroupOf T ⊓ B.subgroupOf T = (A ⊓ B).subgroupOf T := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv

end Lift

section Clause7

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

noncomputable def barLift (hcen : Cen2 G z S) : ↥(barOf z S) →* G :=
  S.subtype.comp (barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen)).symm.toMonoidHom

theorem barLift_injective (hcen : Cen2 G z S) : Function.Injective (barLift hcen) :=
  Subtype.coe_injective.comp (MulEquiv.injective _)

theorem barLift_mem (hcen : Cen2 G z S) (x : ↥(barOf z S)) : barLift hcen x ∈ S :=
  ((barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen)).symm x).2

theorem toBar_barLift (hcen : Cen2 G z S) (x : ↥(barOf z S)) :
    toBar z ⟨barLift hcen x, hcen.sylow.le (barLift_mem hcen x)⟩ = (x : CentralizerBar z) := by
  have h := barEquiv_apply z S hcen.sylow.le (cen2_S_inf_oddCore hcen)
    ((barEquiv z S hcen.sylow.le (cen2_S_inf_oddCore hcen)).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

variable (C : G2Ctx z S)

include C in
theorem G2Ctx.RC_eq (hcen : Cen2 G z S) :
    RC S z = ((C.R).subgroupOf (barOf z S)).map (barLift hcen) := by
  have hSC : S ≤ Cen z := hcen.sylow.le
  ext g
  constructor
  · rintro ⟨hgS, hgL⟩
    set β := barEquiv z S hSC (cen2_S_inf_oddCore hcen) with hβ
    refine ⟨β ⟨g, hgS⟩, ?_, ?_⟩
    · refine ⟨(β ⟨g, hgS⟩).2, ?_⟩
      have := (C.mem_LC_iff hcen hgS (hSC hgS)).1 hgL
      exact this
    · show ((β.symm (β ⟨g, hgS⟩) : ↥S) : G) = g
      rw [MulEquiv.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨barLift_mem hcen x, ?_⟩
    show barLift hcen x ∈ LC z
    rw [C.mem_LC_iff hcen (barLift_mem hcen x) (hSC (barLift_mem hcen x)), toBar_barLift]
    exact hx.2

include C in
theorem G2Ctx.quat_pair (hcen : Cen2 G z S)
    (hq₁ : IVK.IsQuaternionTwoGroup ↥C.P₁ (C.n + 1))
    (hq₂ : IVK.IsQuaternionTwoGroup ↥C.P₂ (C.n + 1)) :
    ∃ (n : ℕ) (A B : Subgroup G), IsCentralProd A B (RC S z) ∧ IVK.IsQuaternionTwoGroup ↥A n ∧
      IVK.IsQuaternionTwoGroup ↥B n := by
  have hR : C.R ≤ barOf z S := inf_le_left
  have hP₁ : C.P₁ ≤ barOf z S := inf_le_left.trans hR
  have hP₂ : C.P₂ ≤ barOf z S := inf_le_left.trans hR
  have hcp : IsCentralProd C.P₁ C.P₂ C.R := ⟨C.P_sup hcen, C.P_comm, C.card_P_inf hcen⟩
  have h1 := isCentralProd_map (barLift hcen) (barLift_injective hcen)
    (isCentralProd_subgroupOf hP₁ hP₂ hcp)
  refine ⟨C.n + 1, (C.P₁.subgroupOf (barOf z S)).map (barLift hcen),
    (C.P₂.subgroupOf (barOf z S)).map (barLift hcen), ?_, ?_, ?_⟩
  · rw [C.RC_eq hcen]
    exact h1
  · obtain ⟨h3, ⟨e⟩⟩ := hq₁
    exact ⟨h3, ⟨((Subgroup.equivMapOfInjective _ (barLift hcen) (barLift_injective hcen)).symm.trans
      (Subgroup.subgroupOfEquivOfLe hP₁)).trans e⟩⟩
  · obtain ⟨h3, ⟨e⟩⟩ := hq₂
    exact ⟨h3, ⟨((Subgroup.equivMapOfInjective _ (barLift hcen) (barLift_injective hcen)).symm.trans
      (Subgroup.subgroupOfEquivOfLe hP₂)).trans e⟩⟩

end Clause7

end CFSG.GH74.GLS.Stage1.Main

module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
  CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_mk)
open scoped commutatorElement MatrixGroups

theorem centralDiff_mul {G H : Type*} [Group G] [Group H] (f₁ f₂ : G →* H)
    (h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center H) (x y : G) :
    (f₁ (x * y))⁻¹ * f₂ (x * y) = ((f₁ x)⁻¹ * f₂ x) * ((f₁ y)⁻¹ * f₂ y) := by
  have hc := Subgroup.mem_center_iff.1 (h x) (f₁ y)⁻¹
  calc (f₁ (x * y))⁻¹ * f₂ (x * y)
      = (f₁ y)⁻¹ * (f₁ x)⁻¹ * f₂ x * f₂ y := by simp only [map_mul, mul_inv_rev, mul_assoc]
    _ = (f₁ y)⁻¹ * ((f₁ x)⁻¹ * f₂ x) * f₂ y := by simp only [mul_assoc]
    _ = ((f₁ x)⁻¹ * f₂ x) * (f₁ y)⁻¹ * f₂ y := by rw [hc]
    _ = ((f₁ x)⁻¹ * f₂ x) * ((f₁ y)⁻¹ * f₂ y) := by simp only [mul_assoc]

@[expose] def centralDiffHom {G H : Type*} [Group G] [Group H] (f₁ f₂ : G →* H)
    (h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center H) : G →* Subgroup.center H where
  toFun g := ⟨(f₁ g)⁻¹ * f₂ g, h g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (centralDiff_mul f₁ f₂ h x y)

theorem eq_of_mul_mem_center_of_perfect {G H : Type*} [Group G] [Group H]
    (hG : commutator G = ⊤) (f₁ f₂ : G →* H)
    (h : ∀ g, (f₁ g)⁻¹ * f₂ g ∈ Subgroup.center H) : f₁ = f₂ := by
  set κ := centralDiffHom f₁ f₂ h with hκ
  have hcomm : ∀ x y : G, κ ⁅x, y⁆ = 1 := by
    intro x y
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.1 (κ y).2 _)
  have hle : commutator G ≤ κ.ker := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact MonoidHom.mem_ker.2 (hcomm x y)
  rw [hG] at hle
  refine MonoidHom.ext fun g => ?_
  have hg : κ g = 1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g))
  have hval : (f₁ g)⁻¹ * f₂ g = 1 := congrArg Subtype.val hg
  exact inv_mul_eq_one.1 hval

theorem map_center_le_comap {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) : Subgroup.center G ≤ (Subgroup.center H).comap π := by
  intro z hz
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro k
  obtain ⟨g, rfl⟩ := hπ k
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]

theorem mk_mem_center_of_map_mem_center {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hker : π.ker ≤ Subgroup.center G) {g : G} (hg : π g ∈ Subgroup.center H) :
    (QuotientGroup.mk g : G ⧸ Subgroup.center G) ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine hker ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
    Subgroup.mem_center_iff.1 hg (π g')]
  exact inv_mul_cancel _

@[expose] noncomputable def centralQuotMap {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) : (G ⧸ Subgroup.center G) →* (H ⧸ Subgroup.center H) :=
  QuotientGroup.map (Subgroup.center G) (Subgroup.center H) π (map_center_le_comap π hπ)

theorem centralQuotMap_mk {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (g : G) :
    centralQuotMap π hπ (QuotientGroup.mk g) = QuotientGroup.mk (π g) := rfl

theorem centralQuotMap_injective {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hG : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) :
    Function.Injective (centralQuotMap π hπ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [centralQuotMap_mk, QuotientGroup.eq_one_iff] at hx
  have hmem := mk_mem_center_of_map_mem_center π hker hx
  rw [hG, Subgroup.mem_bot] at hmem
  exact hmem

theorem centralQuotMap_surjective {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) : Function.Surjective (centralQuotMap π hπ) := by
  intro q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, rfl⟩ := hπ h
  exact ⟨QuotientGroup.mk g, centralQuotMap_mk π hπ g⟩

@[expose] noncomputable def centralQuotEquiv {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hG : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) :
    (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H) :=
  MulEquiv.ofBijective (centralQuotMap π hπ)
    ⟨centralQuotMap_injective π hπ hker hG, centralQuotMap_surjective π hπ⟩

theorem centralQuotEquiv_mk {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hG : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) (g : G) :
    centralQuotEquiv π hπ hker hG (QuotientGroup.mk g) = QuotientGroup.mk (π g) :=
  centralQuotMap_mk π hπ g

theorem congr_centralQuotEquiv {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hG : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) (α : MulAut G) (β : MulAut H)
    (hαβ : ∀ g, π (α g) = β (π g)) :
    MulAut.congr (centralQuotEquiv π hπ hker hG) (autCenterQuot G α) = autCenterQuot H β := by
  ext q
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, rfl⟩ := hπ h
  have hm : (centralQuotEquiv π hπ hker hG).symm (QuotientGroup.mk (π g)) =
      QuotientGroup.mk g := by
    rw [MulEquiv.symm_apply_eq, centralQuotEquiv_mk]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hm]
  simp only [autCenterQuot_mk, centralQuotEquiv_mk, hαβ]

theorem ksMulAut_congr_trans {S S' P : Type} [Group S] [Group S'] [Group P]
    (e : S ≃* S') (f : S' ≃* P) (φ : MulAut S) :
    MulAut.congr (e.trans f) φ = MulAut.congr f (MulAut.congr e φ) := by
  ext x
  simp [MulAut.congr_apply]

theorem ksMulAut_congr_symm_trans {S S' P : Type} [Group S] [Group S'] [Group P]
    (e : S ≃* S') (e₀ : S ≃* P) (φ : MulAut S) :
    MulAut.congr (e.symm.trans e₀) (MulAut.congr e φ) = MulAut.congr e₀ φ := by
  ext x
  simp [MulAut.congr_apply]

theorem fieldAutU_congr {n : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (φ : MulAut S) :
    FieldAutU n S φ ↔ FieldAutU n S' (MulAut.congr e φ) := by
  constructor
  · rintro ⟨K, hK, hfin, e₀, σ, γ, hc, hσ, hodd, hent⟩
    refine ⟨K, hK, hfin, e.symm.trans e₀, σ, γ, hc, hσ, hodd, ?_⟩
    rw [ksMulAut_congr_symm_trans]
    exact hent
  · rintro ⟨K, hK, hfin, e₁, σ, γ, hc, hσ, hodd, hent⟩
    refine ⟨K, hK, hfin, e.trans e₁, σ, γ, hc, hσ, hodd, ?_⟩
    rw [ksMulAut_congr_trans]
    exact hent

theorem exists_sl_conj_statedSU {L : Type} [Field L] [IsAlgClosed L] (F : Subfield L) {q : ℕ}
    (A : GL (Fin 3) F)
    (hA : ∀ g : StatedSU 3 q F, A * (g : GL (Fin 3) F) * A⁻¹ ∈ StatedSU 3 q F) :
    ∃ a : SL(3, L), ∀ g : StatedSU 3 q F,
      statedSUToSL F 3 q ⟨A * (g : GL (Fin 3) F) * A⁻¹, hA g⟩ =
        a * statedSUToSL F 3 q g * a⁻¹ := by
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (by norm_num : 1 ≤ 3)
    (Units.map (RingHom.mapMatrix F.subtype).toMonoidHom A)
  refine ⟨B, fun g => ?_⟩
  have hY := hB (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map F.subtype)
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_statedSUToSL]
  rw [hY, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
  rfl

theorem fieldAutU_of_central_epi {n : ℕ} {G H : Type} [Group G] [Group H] (π : G →* H)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hG : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) (α : MulAut G) (β : MulAut H)
    (hαβ : ∀ g, π (α g) = β (π g))
    (h : FieldAutU n (H ⧸ Subgroup.center H) (autCenterQuot H β)) :
    FieldAutU n (G ⧸ Subgroup.center G) (autCenterQuot G α) := by
  refine (fieldAutU_congr (centralQuotEquiv π hπ hker hG) (autCenterQuot G α)).2 ?_
  rw [congr_centralQuotEquiv π hπ hker hG α β hαβ]
  exact h

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end

module

public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut Subgroup Matrix

namespace GenLocU4Lift

section Generic

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

@[expose] noncomputable def descendHom (hN : ∀ σ : MulAut G, N.map σ.toMonoidHom = N) :
    MulAut G →* MulAut (G ⧸ N) where
  toFun σ := QuotientGroup.congr N N σ (hN σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

variable {N} (hN : ∀ σ : MulAut G, N.map σ.toMonoidHom = N)

theorem descendHom_conj (g : G) :
    descendHom N hN (MulAut.conj g) = MulAut.conj (QuotientGroup.mk g : G ⧸ N) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => rfl

theorem map_inn :
    (MulAut.conj : G →* MulAut G).range.map (descendHom N hN) =
      (MulAut.conj : (G ⧸ N) →* MulAut (G ⧸ N)).range := by
  ext φ
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk g, (descendHom_conj hN g).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, descendHom_conj hN g⟩

theorem innJoin_descend {A : Type} [Group A] (α : A →* MulAut G) (α' : A →* MulAut (G ⧸ N))
    (h : ∀ a, descendHom N hN (α a) = α' a) :
    innJoin α' = (innJoin α).map (descendHom N hN) := by
  unfold innJoin
  rw [Subgroup.map_sup, map_inn hN]
  congr 1
  ext φ
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨α a, ⟨a, rfl⟩, h a⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (h a).symm⟩

theorem sectional_of_descend {A : Type} [Group A] (α : A →* MulAut G) (α' : A →* MulAut (G ⧸ N))
    (hinj : Function.Injective (descendHom N hN)) (h : ∀ a, descendHom N hN (α a) = α' a) {r : ℕ}
    (hsect : SectionalTwoRankLE ↥(innJoin α') r) : SectionalTwoRankLE ↥(innJoin α) r := by
  have heq := innJoin_descend hN α α' h
  have iso := (innJoin α).equivMapOfInjective (descendHom N hN) hinj
  exact SectionalTwoRankLE.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans iso.symm) hsect

theorem gammaAct_quotient_of_gen (hbij : Function.Bijective (descendHom N hN)) {A : Type} [Group A]
    (α' : A →* MulAut (G ⧸ N)) {r : ℕ} (hsect : SectionalTwoRankLE ↥(innJoin α') r)
    (h : ∀ α : A →* MulAut G, SectionalTwoRankLE ↥(innJoin α) r → gammaAct α = ⊤) :
    gammaAct α' = ⊤ := by
  let Φ : MulAut G ≃* MulAut (G ⧸ N) := MulEquiv.ofBijective (descendHom N hN) hbij
  let α : A →* MulAut G := Φ.symm.toMonoidHom.comp α'
  have hαa : ∀ a, descendHom N hN (α a) = α' a := fun a => Φ.apply_symm_apply (α' a)
  exact GenLocDiag.gammaAct_eq_top_of_surj α α' (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (fun a x => by rw [← hαa a]; rfl) (h α (sectional_of_descend hN α α' hbij.1 hαa hsect))

end Generic

section Unitary

variable {K : Type} [Field K] {p f : ℕ}

theorem su4_perfect_center (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Group.IsPerfect ↥(StatedSU 4 (p ^ f) K) ∧ Subgroup.center ↥(StatedSU 4 (p ^ f) K) =
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) := by
  obtain ⟨hperf, hcen⟩ :=
    CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (d := 4) (by norm_num)
  exact ⟨hperf, hcen.trans (unitaryScalars_eq h (by norm_num))⟩

theorem su4_hN (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (σ : MulAut ↥(StatedSU 4 (p ^ f) K)) :
    ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)).map σ.toMonoidHom =
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) := by
  rw [← (su4_perfect_center h hp2).2]
  exact Subgroup.map_center_eq σ

theorem descendHom_injective (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Function.Injective (descendHom ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))
      (su4_hN h hp2)) := by
  have := (su4_perfect_center h hp2).1
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hker : (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))).ker ≤
      Subgroup.center ↥(StatedSU 4 (p ^ f) K) := by
    rw [QuotientGroup.ker_mk', (su4_perfect_center h hp2).2]
  have key := hom_eq_of_central_ker_perfect hker σ.toMonoidHom (MonoidHom.id _) (fun x => by
    have := congrArg (fun φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K)) =>
      φ (QuotientGroup.mk x)) hσ
    exact this)
  refine MulEquiv.ext fun x => ?_
  exact congrArg (fun φ : ↥(StatedSU 4 (p ^ f) K) →* ↥(StatedSU 4 (p ^ f) K) => φ x) key

theorem descendHom_surjective [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Function.Surjective (descendHom ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))
      (su4_hN h hp2)) := by
  intro β
  have hker : (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K))).ker ≤
      Subgroup.center ↥(StatedSU 4 (p ^ f) K) := by
    rw [QuotientGroup.ker_mk', (su4_perfect_center h hp2).2]
  obtain ⟨A, φ, hA, -, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4)
    (by norm_num) (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)))
    (QuotientGroup.mk'_surjective _) hker β
  have hinj : Function.Injective (unitaryConjHom A φ hA) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 := congrArg (fun x : ↥(unitarySU p f K 4) => (x : GL (Fin 4) K)) hg
    simp only [coe_unitaryConjHom, Subgroup.coe_one] at h1
    have h2 : glAut φ (g : GL (Fin 4) K) = 1 := by
      have h3 : A * glAut φ (g : GL (Fin 4) K) * A⁻¹ = 1 := h1
      calc glAut φ (g : GL (Fin 4) K) = A⁻¹ * (A * glAut φ (g : GL (Fin 4) K) * A⁻¹) * A := by group
        _ = 1 := by rw [h3]; group
    exact Subtype.ext ((map_eq_one_iff _ (glAut φ).injective).1 h2)
  have hbij : Function.Bijective (unitaryConjHom A φ hA) :=
    ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  refine ⟨MulEquiv.ofBijective (unitaryConjHom A φ hA) hbij, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => exact hlift x

end Unitary

end GenLocU4Lift

namespace GenLocU4Fam

variable {K : Type} [Field K] [Finite K]

@[expose] def Su4GenStmt (K : Type) [Field K] [Finite K] (q : ℕ) : Prop :=
  ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 q K)),
    IsRank23 A → SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤

theorem gammaAct_projectiveSU4_of_su4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (h : Su4GenStmt K (p ^ f)) {A : Type} [Group A] [Finite A]
    (α' : A →* MulAut (StatedProj (StatedSU 4 (p ^ f) K))) (hA : IsRank23 A)
    (hsect : SectionalTwoRankLE ↥(innJoin α') 4) : gammaAct α' = ⊤ := by
  have hud := GenLocDiagU.unitaryFieldData_of_card hp hK
  exact GenLocU4Lift.gammaAct_quotient_of_gen (GenLocU4Lift.su4_hN hud hp2)
    ⟨GenLocU4Lift.descendHom_injective hud hp2, GenLocU4Lift.descendHom_surjective hud hp2⟩ α' hsect
    (fun α hs => h α hA hs)

theorem genLoc4_projectiveSU4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (h : Su4GenStmt K (p ^ f)) : GenLoc4 (StatedProj (StatedSU 4 (p ^ f) K)) :=
  fun _ _ _ α' hA hsect => Or.inl (gammaAct_projectiveSU4_of_su4 hp hp2 hK h α' hA hsect)

end GenLocU4Fam

end CFSG.GH74.Generic.BProg.B2

module

public import CFSG.LieType.SpecialLinear.Stage.Simple
public import CFSG.LieType.SpecialLinear.BorelTwist.Upper
public import CFSG.RepresentationTheory.FixedBaseChange
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import CFSG.LieType.SpecialLinear.Block222.Borel.Aut
public import CFSG.LieType.SpecialLinear.NormalizerLift.Borel
public import CFSG.LieType.SpecialLinear.NormalizerLift.Commutator
public import CFSG.LieType.SpecialLinear.NormalizerLift.InnerLift

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Theory.Representation
open scoped TensorProduct


section IndexBounds

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]

theorem card_le_two_mul_card_inf_of_graphPart_eq_one_imp (π : SpecialLinearGroup (Fin n) F →* H)
    (hker : π.ker ≤ LinearFlag.scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    (D : Subgroup H) [Finite D] (hD : D ≤ rangeNormalizer π)
    (hD2 : ∀ d ∈ D, d * d = 1)
    (hgf : ∀ d (hd : d ∈ D), graphPart π hker hn ⟨d, hD hd⟩ = 1 →
      fieldPart π hker hn ⟨d, hD hd⟩ = 1) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ π.range) := by
  classical
  let inc : D →* rangeNormalizer π := normalizerInclusion π hD
  let g : D →* Multiplicative (ZMod 2) := (graphPart π hker hn).comp inc
  have hker_g : g.ker = (D ⊓ π.range).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hg' : (graphPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := by
        simpa only [g, inc, normalizerInclusion_apply, MonoidHom.comp_apply] using hd
      have hf' : (fieldPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := hgf d.1 d.2 hg'
      exact ⟨d.2, mem_range_of_fieldPart_graphPart_eq_one π hker hn hodd (hD d.2)
        (hD2 d.1 d.2) hf' hg'⟩
    · intro hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hd
      obtain ⟨x, hx⟩ := hd.2
      have hd_eq : (⟨d.1, hD d.2⟩ : rangeNormalizer π) =
          ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ :=
        Subtype.ext hx.symm
      show g d = 1
      rw [show g d = (graphPart π hker hn) (normalizerInclusion π hD d) from rfl,
        normalizerInclusion_apply, hd_eq]
      exact (fieldPart_graphPart_range π hker hn x).2
  have hgraph_range_le : Nat.card g.range ≤ 2 := by
    have hle : Nat.card g.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
      Nat.card_le_card_of_injective (fun x : g.range => (x : Multiplicative (ZMod 2)))
        Subtype.coe_injective
    have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    rwa [hcard] at hle
  have hcard_ker : Nat.card g.ker = Nat.card ↥(D ⊓ π.range) := by
    rw [hker_g]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardD : Nat.card D = Nat.card g.range * Nat.card ↥(D ⊓ π.range) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hcard_ker]
  calc Nat.card D = Nat.card g.range * Nat.card ↥(D ⊓ π.range) := hcardD
    _ ≤ 2 * Nat.card ↥(D ⊓ π.range) := Nat.mul_le_mul_right _ hgraph_range_le

end IndexBounds

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D] [Finite D]
  {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]
  [IsScalarTower (ZMod 2) E X] [Finite X]

theorem borelStd_one_eq_stdAut_mul_revGL (n : ℕ) (F : Type) [Field F] (A : GL (Fin n) F)
    (σ : F ≃+* F) :
    borelStd n F A σ 1 =
      CFSG.QuasithinUnique.K1.stdAut (A * revGL n F) σ 1 := by
  have h := stdAut_one_eq_borelStd (n := n) (F := F) (A * revGL n F) σ
  rw [mul_assoc, mul_inv_cancel, mul_one] at h
  exact h.symm

theorem borelStd_eq_stdAut_mod_two (n : ℕ) (F : Type) [Field F] (A : GL (Fin n) F)
    (σ : F ≃+* F) (ε : ℕ) :
    borelStd n F A σ ε =
      CFSG.QuasithinUnique.K1.stdAut (A * revGL n F ^ (ε % 2)) σ (ε % 2) := by
  have hγ : (borelGraph n F) ^ ε = (borelGraph n F) ^ (ε % 2) :=
    pow_eq_pow_mod (n := 2) ε (borelGraph_mul_self F n)
  have h1 : CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph n F =
      CFSG.QuasithinUnique.K1.stdAut (A * revGL n F) σ 1 := by
    simpa [borelStd, pow_one] using borelStd_one_eq_stdAut_mul_revGL n F A σ
  rw [borelStd, hγ]
  rcases Nat.mod_two_eq_zero_or_one ε with h | h
  · rw [h, pow_zero, pow_zero, mul_one, mul_one]
  · rw [h, pow_one, pow_one]
    exact h1

theorem unitriangular_eq_curtisDatum_U (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] :
    LinearFlag.unitriangular (n + 1) F = (curtisDatum n F 2).U := by
  ext g
  rw [LinearFlag.mem_unitriangular, mem_curtisDatum_U_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem borelStd_mem_unitriangular {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : GL (Fin (n + 1)) F) (hA : IsUpperGL A) (τ : F ≃+* F) (ε : ℕ)
    {u : SpecialLinearGroup (Fin (n + 1)) F}
    (hu : u ∈ LinearFlag.unitriangular (n + 1) F) :
    borelStd (n + 1) F A τ ε u ∈ LinearFlag.unitriangular (n + 1) F := by
  have hU : LinearFlag.unitriangular (n + 1) F = (curtisDatum n F 2).U :=
    unitriangular_eq_curtisDatum_U n F
  have hγ : ∀ v ∈ (curtisDatum n F 2).U, borelGraph (n + 1) F v ∈ (curtisDatum n F 2).U :=
    fun v hv => borelGraph_mem_U n F hv
  have hγpow : ∀ m, ∀ v ∈ (curtisDatum n F 2).U,
      ((borelGraph (n + 1) F) ^ m) v ∈ (curtisDatum n F 2).U := by
    intro m
    induction m with
    | zero => intro v hv; simpa using hv
    | succ m ih => intro v hv; rw [pow_succ]; exact ih _ (hγ v hv)
  have hu' : u ∈ (curtisDatum n F 2).U := by rw [← hU]; exact hu
  rw [borelStd_apply, hU]
  exact stdAut_zero_mem_U n F A hA τ (hγpow ε u hu')

@[expose] noncomputable def unitRepE {G : Type*} [Group G]
    (σ : Representation E G X) : G →* (X ≃ₗ[E] X) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E X).toMonoidHom.comp σ.asGroupHom

omit [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Module (ZMod 2) X]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem unitRepE_apply {G : Type*} [Group G]
    (σ : Representation E G X) (g : G) (x : X) :
    unitRepE σ g x = σ g x := rfl

omit [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Module (ZMod 2) X]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem unitRepE_coe {G : Type*} [Group G]
    (σ : Representation E G X) (g : G) :
    ((unitRepE σ g : X ≃ₗ[E] X) : X →ₗ[E] X) = σ g := by
  simp [unitRepE, Representation.asGroupHom_apply]

@[expose] noncomputable def actorRepE (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) : D →* (X ≃ₗ[E] X) where
  toFun d :=
    { toFun := δ d
      invFun := δ d
      left_inv := fun x => by
        have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 d)
        simpa [Module.End.mul_apply] using h
      right_inv := fun x => by
        have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 d)
        simpa [Module.End.mul_apply] using h
      map_add' := (δ d).map_add
      map_smul' := hδE d }
  map_one' := by ext x; simp
  map_mul' := by intro a b; ext x; simp [map_mul]

omit [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Finite D] [IsScalarTower (ZMod 2) E X]
  [Finite X] in
theorem actorRepE_apply (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (d : D) (x : X) :
    actorRepE δ hδE hD2 d x = δ d x := rfl


omit [CharP F 2] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Finite D]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem exists_actor_ne_one_of_graph {n : ℕ} (hn : 2 ≤ n)
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hgraph : ∃ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 1 g) (δ d x)) :
    ∃ d, δ d ≠ 1 := by
  classical
  obtain ⟨d, A, _hA, τ, hd⟩ := hgraph
  by_contra h
  push Not at h
  have hd1 : δ d = 1 := h d
  let π : SpecialLinearGroup (Fin (n + 1)) F →* (X →ₗ[E] X)ˣ := σ.asGroupHom
  have hn3 : 3 ≤ n + 1 := by omega
  have hqs : IsQuasisimple (SpecialLinearGroup (Fin (n + 1)) F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple n F hn
  have hσunit : ∃ g, π g ≠ 1 := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, fun hcon => hg ?_⟩
    have h := congrArg (fun u : (X →ₗ[E] X)ˣ => (u : X →ₗ[E] X)) hcon
    simpa [π, Representation.asGroupHom_apply] using h
  have hker : π.ker ≤ LinearFlag.scalars (n + 1) F := by
    have h := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqs hσunit
    rwa [← LinearFlag.scalars_eq_center] at h
  let β : MulAut (SpecialLinearGroup (Fin (n + 1)) F) := borelStd (n + 1) F A τ 1
  have hβ : β = 1 := by
    apply eq_of_comp_proj_eq (π := π) hker hn3 β 1
    intro g
    apply Units.ext
    rw [MulAut.one_apply, Representation.asGroupHom_apply, Representation.asGroupHom_apply]
    ext x
    have h := hd g x
    rw [hd1] at h
    simpa using h.symm
  have hstd : CFSG.QuasithinUnique.K1.stdAut (A * revGL (n + 1) F) τ 1 =
      CFSG.QuasithinUnique.K1.stdAut (1 : GL (Fin (n + 1)) F) (1 : F ≃+* F) 0 := by
    rw [← borelStd_one_eq_stdAut_mul_revGL (n := n + 1) (F := F) A τ]
    rw [show borelStd (n + 1) F A τ 1 = β from rfl, hβ]
    simp [CFSG.QuasithinUnique.K1.stdAut]
  have huniq := stdAut_field_graph_unique (n := n + 1) (F := F) hn3
    (le_refl 1) (Nat.zero_le 1) hstd
  exact one_ne_zero huniq.2


omit [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem card_le_card_range_mul_card_fix
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hoff : IsOffenderOn δ ⊤ ⊤) :
    Nat.card X ≤ Nat.card (actorRepE δ hδE hD2).range *
      Nat.card {y : X // ∀ d ∈ (actorRepE δ hδE hD2).range, d y = y} := by
  classical
  let δE : D →* (X ≃ₗ[E] X) := actorRepE δ hδE hD2
  have hδE_apply : ∀ (d : D) (x : X), δE d x = δ d x :=
    fun d x => actorRepE_apply δ hδE hD2 d x
  have hoff2 := hoff.2
  have hXtop : Nat.card (⊤ : Submodule (ZMod 2) X) = Nat.card X :=
    Nat.card_congr (Submodule.topEquiv).toEquiv
  have hcen : cenOn δ ⊤ ⊤ = δ.ker := by
    ext d
    rw [mem_cenOn, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, hd⟩
      ext x
      exact hd x Submodule.mem_top
    · intro hd
      refine ⟨Subgroup.mem_top d, fun x _ => ?_⟩
      rw [hd]
      rfl
  have hfix : Nat.card (fixOn δ ⊤ ⊤) = Nat.card {y : X // ∀ d : D, δ d y = y} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun v => ⟨v.1, fun d => (mem_fixOn.mp v.2).2 d (Subgroup.mem_top d)⟩
        invFun := fun y => ⟨y.1, mem_fixOn.mpr ⟨Submodule.mem_top, fun d _ => y.2 d⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  rw [hXtop, hcen, hfix, Subgroup.card_top] at hoff2
  have hkerE : δE.ker = δ.ker := by
    ext d
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hd
      ext x
      have hx := congrArg (fun e : X ≃ₗ[E] X => e x) hd
      rw [show (δE d) x = δ d x from hδE_apply d x] at hx
      simpa using hx
    · intro hd
      apply LinearEquiv.ext
      intro x
      rw [show (δE d) x = δ d x from hδE_apply d x, hd]
      rfl
  have hle : Nat.card {y : X // ∀ d : D, δ d y = y} ≤
      Nat.card {y : X // ∀ d ∈ δE.range, d y = y} := by
    refine Nat.card_le_card_of_injective
      (fun y => ⟨y.1, fun d hd => ?_⟩) ?_
    · obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hd
      rw [← he, hδE_apply e y.1]
      exact y.2 e
    · intro y₁ y₂ h
      exact Subtype.ext (congrArg (fun z : {y : X // ∀ d ∈ δE.range, d y = y} => (z : X)) h)
  have hDcard : Nat.card D = Nat.card δE.ker * Nat.card δE.range :=
    (Subgroup.card_ker_mul_card_range δE).symm
  have hpos : 0 < Nat.card δE.ker := Nat.card_pos
  have hmain : Nat.card δE.ker * Nat.card X ≤ Nat.card δE.ker *
      (Nat.card δE.range * Nat.card {y : X // ∀ d ∈ δE.range, d y = y}) := by
    calc Nat.card δE.ker * Nat.card X
        = Nat.card X * Nat.card δE.ker := Nat.mul_comm _ _
      _ ≤ Nat.card D * Nat.card {y : X // ∀ d : D, δ d y = y} := by
          rw [← hkerE] at hoff2
          exact hoff2
      _ = (Nat.card δE.ker * Nat.card δE.range) *
            Nat.card {y : X // ∀ d : D, δ d y = y} := by rw [hDcard]
      _ ≤ (Nat.card δE.ker * Nat.card δE.range) *
            Nat.card {y : X // ∀ d ∈ δE.range, d y = y} :=
          Nat.mul_le_mul_left _ hle
      _ = Nat.card δE.ker * (Nat.card δE.range *
            Nat.card {y : X // ∀ d ∈ δE.range, d y = y}) := by ring
  exact Nat.le_of_mul_le_mul_left hmain hpos

theorem fixSub_zpowers_eq_ker_sub_one {K M G : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Group G] (ρ : Representation K G M) (u : G) :
    fixSub ρ (Subgroup.zpowers u) = LinearMap.ker ((ρ u : M →ₗ[K] M) - 1) := by
  ext v
  rw [mem_fixSub, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    exact h u (Subgroup.mem_zpowers u)
  · intro h g hg
    let T : Subgroup G :=
      { carrier := {g | ρ g v = v}
        mul_mem' := by
          intro a b ha hb
          change ρ (a * b) v = v
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          change ρ 1 v = v
          rw [map_one]
          rfl
        inv_mem' := by
          intro a ha
          change ρ a⁻¹ v = v
          have h1 : ρ a⁻¹ (ρ a v) = ρ a⁻¹ v := by rw [ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at h1
          exact h1.symm }
    exact (Subgroup.zpowers_le.mpr (show u ∈ T from h)) hg

theorem card_fixSub_zpowers {K M G : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Group G] (ρ : Representation K G M) (u : G) :
    Nat.card (fixSub ρ (Subgroup.zpowers u)) = Nat.card {y : M // ρ u y = y} := by
  rw [fixSub_zpowers_eq_ker_sub_one ρ u]
  refine Nat.card_congr ?_
  exact
    { toFun := fun v => ⟨v.1, by
        have h := LinearMap.mem_ker.mp v.2
        rw [LinearMap.sub_apply, Module.End.one_apply] at h
        exact sub_eq_zero.mp h⟩
      invFun := fun y => ⟨y.1, by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        exact y.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

omit [Fintype F] [CharP F 2] [CharP E 2] [Algebra (ZMod 2) E] [CharP k 2] [Algebra F k]
  [Module (ZMod 2) X] [IsScalarTower (ZMod 2) E X] in
theorem pow_finrank_sub_finrank_fixSub_le {n : ℕ}
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (A : Subgroup (SpecialLinearGroup (Fin (n + 1)) F)) [Finite A] {c : ℕ}
    (hcard : Nat.card X ≤ c * Nat.card (fixSub σ A)) :
    Nat.card E ^ (Module.finrank k (k ⊗[E] X) -
        Module.finrank k (fixSub (extendScalars k σ) A)) ≤ c := by
  classical
  have hd : Module.finrank k (k ⊗[E] X) = Module.finrank E X :=
    Module.finrank_baseChange (R := k) (S := E) (M' := X)
  have hX : Nat.card X = Nat.card E ^ Module.finrank k (k ⊗[E] X) := by
    rw [Module.natCard_eq_pow_finrank (K := E) (V := X), hd]
  have hfix : Nat.card (fixSub σ A) =
      Nat.card E ^ Module.finrank k (fixSub (extendScalars k σ) A) :=
    card_fixSub_eq_card_pow_finrank k σ A
  have hle : Module.finrank k (fixSub (extendScalars k σ) A) ≤
      Module.finrank k (k ⊗[E] X) := by
    simpa using Submodule.finrank_le (fixSub (extendScalars k σ) A)
  rw [hX, hfix] at hcard
  rw [← Nat.pow_sub_mul_pow (Nat.card E) hle] at hcard
  exact Nat.le_of_mul_le_mul_right hcard (pow_pos Nat.card_pos _)


omit [Fintype F] [CharP F 2] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Finite D]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem actor_conj_sigma_eq_borel {n : ℕ}
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (π : SpecialLinearGroup (Fin (n + 1)) F →* (X ≃ₗ[E] X))
    (δ : Representation (ZMod 2) D X) (δE : D →* (X ≃ₗ[E] X))
    (hπ : ∀ g x, π g x = σ g x) (hδ : ∀ d x, δE d x = δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    {e : D} {A : GL (Fin (n + 1)) F} {τ : F ≃+* F} {ε : ℕ}
    (hc : ∀ g x, δ e (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ e x)) :
    ∀ g, δE e * π g * (δE e)⁻¹ = π (borelStd (n + 1) F A τ ε g) := by
  have ha2 : δE e * δE e = 1 := by
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 e)
    simpa [hδ, Module.End.mul_apply] using h
  have hinv : (δE e)⁻¹ = δE e := inv_eq_of_mul_eq_one_right ha2
  have haa : ∀ x, δE e (δE e x) = x := by
    intro x
    have h := congrArg (fun f : X ≃ₗ[E] X => f x) ha2
    simpa [LinearEquiv.mul_apply] using h
  intro g
  apply LinearEquiv.ext
  intro x
  calc (δE e * π g * (δE e)⁻¹) x
      = δE e (π g ((δE e)⁻¹ x)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = δE e (π g (δE e x)) := by rw [hinv]
    _ = δE e (σ g (δE e x)) := by rw [hπ]
    _ = δ e (σ g (δE e x)) := by rw [hδ]
    _ = δ e (σ g (δ e x)) := by rw [hδ]
    _ = σ (borelStd (n + 1) F A τ ε g) (δ e (δ e x)) := hc g (δ e x)
    _ = σ (borelStd (n + 1) F A τ ε g) x := by rw [← hδ, ← hδ, haa]
    _ = π (borelStd (n + 1) F A τ ε g) x := by rw [hπ]

omit [CharP F 2] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Finite D]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem liftAut_eq_borelStd_of_hcompat {n : ℕ}
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (π : SpecialLinearGroup (Fin (n + 1)) F →* (X ≃ₗ[E] X))
    (δ : Representation (ZMod 2) D X) (δE : D →* (X ≃ₗ[E] X))
    (hπ : ∀ g x, π g x = σ g x) (hδ : ∀ d x, δE d x = δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hker : π.ker ≤ LinearFlag.scalars (n + 1) F) (hn3 : 3 ≤ n + 1)
    {e : D} {A : GL (Fin (n + 1)) F} {τ : F ≃+* F} {ε : ℕ}
    (hc : ∀ g x, δ e (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ e x))
    (hN : δE e ∈ rangeNormalizer π) :
    liftAut π hker hn3 ⟨δE e, hN⟩ = borelStd (n + 1) F A τ ε := by
  apply eq_of_comp_proj_eq (π := π) hker hn3 _ _
  intro g
  rw [liftAut_spec]
  exact actor_conj_sigma_eq_borel σ π δ δE hπ hδ hD2 hc g

omit [CharP F 2] [Fintype E] [CharP E 2] [Algebra (ZMod 2) E] [Finite D]
  [IsScalarTower (ZMod 2) E X] [Finite X] in
theorem fieldPart_graphPart_of_hcompat {n : ℕ}
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (π : SpecialLinearGroup (Fin (n + 1)) F →* (X ≃ₗ[E] X))
    (δ : Representation (ZMod 2) D X) (δE : D →* (X ≃ₗ[E] X))
    (hπ : ∀ g x, π g x = σ g x) (hδ : ∀ d x, δE d x = δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hker : π.ker ≤ LinearFlag.scalars (n + 1) F) (hn3 : 3 ≤ n + 1)
    {e : D} {A : GL (Fin (n + 1)) F} {τ : F ≃+* F} {ε : ℕ}
    (hc : ∀ g x, δ e (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ e x))
    (hN : δE e ∈ rangeNormalizer π) :
    fieldPart π hker hn3 ⟨δE e, hN⟩ = τ ∧
      graphPart π hker hn3 ⟨δE e, hN⟩ =
        Multiplicative.ofAdd ((ε % 2 : ℕ) : ZMod 2) := by
  have hlift := liftAut_eq_borelStd_of_hcompat σ π δ δE hπ hδ hD2 hker hn3 hc hN
  have hborel := borelStd_eq_stdAut_mod_two (n + 1) F A τ ε
  have hstd : CFSG.QuasithinUnique.K1.stdAut
        (stdData π hker hn3 ⟨δE e, hN⟩).1
        (stdData π hker hn3 ⟨δE e, hN⟩).2.1
        (stdData π hker hn3 ⟨δE e, hN⟩).2.2 =
      CFSG.QuasithinUnique.K1.stdAut
        (A * revGL (n + 1) F ^ (ε % 2)) τ (ε % 2) := by
    rw [← liftAut_eq_stdAut, hlift, hborel]
  have huniq := stdAut_field_graph_unique (n := n + 1) (F := F) hn3
    (stdData_eps_le_one π hker hn3 ⟨δE e, hN⟩)
    (by have h := Nat.mod_lt ε (by norm_num : 0 < 2); omega) hstd
  refine ⟨huniq.1, ?_⟩
  change Multiplicative.ofAdd
      (((stdData π hker hn3 ⟨δE e, hN⟩).2.2 : ℕ) : ZMod 2) =
    Multiplicative.ofAdd ((ε % 2 : ℕ) : ZMod 2)
  rw [huniq.2]


omit [CharP k 2] [Algebra F k] [Algebra (ZMod 2) E] [IsScalarTower (ZMod 2) E X] in
theorem stage_inner_dichotomy {n : ℕ} (hn : 2 ≤ n)
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ)) (hne : ∃ g, σ g ≠ 1)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1) (hD1 : ∃ d, δ d ≠ 1)
    (hquad : ∀ a b x, δ b (δ a x - x) = δ a x - x)
    (hcompat : ∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ (τ : F ≃+* F) (ε : ℕ),
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ ε g) (δ d x))
    (hoff : IsOffenderOn δ ⊤ ⊤) {c : ℕ}
    (hc : c = 4 ∨ (c = 2 ∧
      ((∀ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
          ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x)) ∨
        (∀ d, ∀ A : GL (Fin (n + 1)) F, IsUpperGL A → ∀ τ : F ≃+* F,
          (∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ d x)) →
            τ = RingEquiv.refl F)))) :
    (∃ u ∈ LinearFlag.unitriangular (n + 1) F, u ≠ 1 ∧ u * u = 1 ∧
        Nat.card E ^ Module.finrank k (LinearMap.range (extendScalars k σ u - 1)) ≤ 16) ∨
    (∃ A₀ : Subgroup (SpecialLinearGroup (Fin (n + 1)) F),
        A₀ ≤ LinearFlag.unitriangular (n + 1) F ∧ A₀ ≠ ⊥ ∧ (∀ a ∈ A₀, a * a = 1) ∧
        (∀ a ∈ A₀, ∀ b ∈ A₀, (extendScalars k σ a - 1) * (extendScalars k σ b - 1) = 0) ∧
        Nat.card E ^ (Module.finrank k (k ⊗[E] X) -
            Module.finrank k (fixSub (extendScalars k σ) A₀)) ≤ c * Nat.card A₀) := by
  classical
  have hn3 : 3 ≤ n + 1 := by omega
  let π : SpecialLinearGroup (Fin (n + 1)) F →* (X ≃ₗ[E] X) := unitRepE σ
  let δE : D →* (X ≃ₗ[E] X) := actorRepE δ hδE hD2
  have hπ_apply : ∀ g x, π g x = σ g x := fun g x => unitRepE_apply σ g x
  have hδ_apply : ∀ d x, δE d x = δ d x := fun d x => actorRepE_apply δ hδE hD2 d x
  have hqs : IsQuasisimple (SpecialLinearGroup (Fin (n + 1)) F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple n F hn
  have hσunit : ∃ g, π g ≠ 1 := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, fun hcon => hg ?_⟩
    have h := congrArg (fun e : X ≃ₗ[E] X => (e : X →ₗ[E] X)) hcon
    have h' : (σ g : X →ₗ[E] X) = LinearMap.id := by
      simpa [π, unitRepE_coe] using h
    change (σ g : X →ₗ[E] X) = LinearMap.id
    exact h'
  have hker : π.ker ≤ LinearFlag.scalars (n + 1) F := by
    have h := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqs hσunit
    rwa [← LinearFlag.scalars_eq_center] at h
  have hsimpE : IsSimpleRep σ := isSimpleRep_of_isSimpleRep_extendScalars σ hsimp
  have hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set (X ≃ₗ[E] X)), Odd (orderOf c) := by
    have htwo : ∀ d : X ≃ₗ[E] X, d * d = 1 →
        d ∈ Subgroup.centralizer (π.range : Set (X ≃ₗ[E] X)) → d = 1 := by
      intro d hd2 hdc
      by_contra hne_d
      let f : X →ₗ[E] X := d
      let W : Submodule E X := LinearMap.ker (f - 1)
      have hx : ∃ x : X, f x ≠ x := by
        by_contra h
        push Not at h
        exact hne_d (LinearEquiv.ext h)
      obtain ⟨x, hx⟩ := hx
      have hff : f (f x) = x := by
        have h := congrArg (fun e : X ≃ₗ[E] X => e x) hd2
        simpa [f, LinearEquiv.mul_apply] using h
      have hnegx : -(x : X) = x := by
        refine neg_eq_of_add_eq_zero_right ?_
        rw [← two_smul E x, CharTwo.two_eq_zero, zero_smul]
      have hnegfx : -(f x) = f x := by
        refine neg_eq_of_add_eq_zero_right ?_
        rw [← two_smul E (f x), CharTwo.two_eq_zero, zero_smul]
      have hfix : f ((f - 1) x) = (f - 1) x := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        calc f (f x - x) = f (f x) - f x := map_sub _ _ _
          _ = x - f x := by rw [hff]
          _ = f x - x := by
            rw [sub_eq_add_neg, sub_eq_add_neg, hnegx, hnegfx, add_comm]
      have hmem : (f - 1) x ∈ W := by
        rw [LinearMap.mem_ker]
        show (f - 1) ((f - 1) x) = 0
        rw [LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]
      have hxne : (f - 1) x ≠ 0 := by
        intro hzero
        apply hx
        have h : f x - x = 0 := by
          simpa [LinearMap.sub_apply, Module.End.one_apply] using hzero
        exact sub_eq_zero.mp h
      have hW_bot : W ≠ ⊥ := by
        intro hbot
        have hmem0 : (f - 1) x ∈ (⊥ : Submodule E X) := hbot ▸ hmem
        exact hxne (by simpa using hmem0)
      have hW_top : W = ⊤ := by
        have hinv : ∀ g : SpecialLinearGroup (Fin (n + 1)) F, ∀ w ∈ W, σ g w ∈ W := by
          intro g w hw
          rw [LinearMap.mem_ker] at hw ⊢
          have hcomm : d * π g = π g * d :=
            ((Subgroup.mem_centralizer_iff.mp hdc) (π g)
              (MonoidHom.mem_range.mpr ⟨g, rfl⟩)).symm
          have hdσ : f (σ g w) = σ g (f w) := by
            have h := congrArg (fun e : X ≃ₗ[E] X => e w) hcomm
            simpa [f, LinearEquiv.mul_apply, hπ_apply] using h
          have h1 : (f - 1) (σ g w) = σ g ((f - 1) w) := by
            rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply,
              Module.End.one_apply, hdσ, map_sub]
          rw [h1, hw, map_zero]
        rcases hsimpE.2 W hinv with h | h
        · exact absurd h hW_bot
        · exact h
      have hzero : f - 1 = 0 := LinearMap.ker_eq_top.mp hW_top
      have hdlin : f = 1 := sub_eq_zero.mp hzero
      exact hne_d (LinearEquiv.ext (fun x => by
        have h := congrArg (fun g : X →ₗ[E] X => g x) hdlin
        simpa [f] using h))
    intro c hc
    by_contra hnot
    have heven : Even (orderOf c) := Nat.not_odd_iff_even.mp hnot
    have hpos : 0 < orderOf c := orderOf_pos c
    have htwo_le : 2 ≤ orderOf c := Nat.le_of_dvd hpos (even_iff_two_dvd.mp heven)
    have hhalfpos : 0 < orderOf c / 2 := Nat.div_pos htwo_le (by norm_num)
    let d : X ≃ₗ[E] X := c ^ (orderOf c / 2)
    have hd2 : d * d = 1 := by
      dsimp [d]
      rw [← pow_add]
      have hsum : orderOf c / 2 + orderOf c / 2 = orderOf c := by
        rw [← Nat.two_mul, Nat.two_mul_div_two_of_even heven]
      rw [hsum, pow_orderOf_eq_one]
    have hdcent : d ∈ Subgroup.centralizer (π.range : Set (X ≃ₗ[E] X)) :=
      (Subgroup.centralizer (π.range : Set (X ≃ₗ[E] X))).pow_mem hc _
    have hd1 : d = 1 := htwo d hd2 hdcent
    have hpow : c ^ (orderOf c / 2) = 1 := by simpa [d] using hd1
    have hdvd : orderOf c ∣ orderOf c / 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hle : orderOf c ≤ orderOf c / 2 := Nat.le_of_dvd hhalfpos hdvd
    have hlt : orderOf c / 2 < orderOf c := Nat.div_lt_self hpos (by norm_num)
    omega
  have hDbarN : δE.range ≤ rangeNormalizer π := by
    intro a ha
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨A, hA, τ, ε, hc⟩ := hcompat e
    have hN : δE e ∈ rangeNormalizer π := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨borelStd (n + 1) F A τ ε g,
          (actor_conj_sigma_eq_borel σ π δ δE hπ_apply hδ_apply hD2 hc g).symm⟩
      · intro hh
        obtain ⟨g, hg⟩ := hh
        refine ⟨borelStd (n + 1) F A τ ε g, ?_⟩
        have ha2 : δE e * δE e = 1 := by
          apply LinearEquiv.ext
          intro x
          have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 e)
          simpa [hδ_apply, Module.End.mul_apply] using h
        have hinv : (δE e)⁻¹ = δE e := inv_eq_of_mul_eq_one_right ha2
        have hcalc : h = π (borelStd (n + 1) F A τ ε g) := by
          calc h = (δE e)⁻¹ * (δE e * h * (δE e)⁻¹) * (δE e) := by group
            _ = (δE e)⁻¹ * π g * (δE e) := by rw [hg]
            _ = (δE e) * π g * (δE e)⁻¹ := by rw [hinv]
            _ = π (borelStd (n + 1) F A τ ε g) :=
                actor_conj_sigma_eq_borel σ π δ δE hπ_apply hδ_apply hD2 hc g
        exact hcalc.symm
    exact hN
  have hDbar2 : ∀ d ∈ δE.range, d * d = 1 := by
    intro d hd
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hd
    apply LinearEquiv.ext
    intro x
    have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 e)
    simpa [hδ_apply, Module.End.mul_apply] using h
  have hDbarU : δE.range ≤ Subgroup.normalizer
      ((LinearFlag.unitriangular (n + 1) F).map π : Set (X ≃ₗ[E] X)) := by
    intro a ha
    obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨A, hA, τ, ε, hc⟩ := hcompat e
    have hconj := actor_conj_sigma_eq_borel σ π δ δE hπ_apply hδ_apply hD2 hc
    have hβU : ∀ g : SpecialLinearGroup (Fin (n + 1)) F,
        g ∈ LinearFlag.unitriangular (n + 1) F →
          borelStd (n + 1) F A τ ε g ∈ LinearFlag.unitriangular (n + 1) F :=
      fun g hg => borelStd_mem_unitriangular A hA τ ε hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨g, hgU, hg⟩
      refine Subgroup.mem_map.mpr ⟨borelStd (n + 1) F A τ ε g, hβU g hgU, ?_⟩
      rw [← hconj g, hg]
    · intro hh
      obtain ⟨g, hgU, hg⟩ := Subgroup.mem_map.mp hh
      have ha2 : δE e * δE e = 1 := by
        apply LinearEquiv.ext
        intro x
        have h := congrArg (fun f : X →ₗ[ZMod 2] X => f x) (hD2 e)
        simpa [hδ_apply, Module.End.mul_apply] using h
      have hinv : (δE e)⁻¹ = δE e := inv_eq_of_mul_eq_one_right ha2
      refine Subgroup.mem_map.mpr ⟨borelStd (n + 1) F A τ ε g, hβU g hgU, ?_⟩
      calc π (borelStd (n + 1) F A τ ε g) = (δE e) * π g * (δE e)⁻¹ := (hconj g).symm
        _ = h := by
          rw [hg, hinv]
          calc (δE e) * ((δE e) * h * (δE e)) * (δE e) =
                ((δE e) * (δE e)) * h * ((δE e) * (δE e)) := by group
            _ = h := by rw [ha2]; group
  have hoffBar := card_le_card_range_mul_card_fix δ hδE hD2 hoff
  have hDbarBound : Nat.card δE.range ≤ c * Nat.card ↥(δE.range ⊓ π.range) := by
    rcases hc with rfl | ⟨rfl, hcase | hcase⟩
    · exact card_le_four_mul_card_inf π hker hn3 hodd δE.range hDbarN hDbar2
    · apply card_le_two_mul_card_inf_of_graphPart_eq_one π hker hn3 hodd δE.range hDbarN hDbar2
      intro d hd
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hd
      obtain ⟨A, hA, τ, h0⟩ := hcase e
      have hN : δE e ∈ rangeNormalizer π := hDbarN (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
      exact (fieldPart_graphPart_of_hcompat σ π δ δE hπ_apply hδ_apply hD2 hker hn3
        (ε := 0) h0 hN).2
    · apply card_le_two_mul_card_inf_of_graphPart_eq_one_imp π hker hn3 hodd δE.range hDbarN hDbar2
      intro d hd hgraph
      obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hd
      have hN : δE e ∈ rangeNormalizer π := hDbarN (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
      obtain ⟨A, hA, τ, ε, hc0⟩ := hcompat e
      have hfg := fieldPart_graphPart_of_hcompat σ π δ δE hπ_apply hδ_apply hD2 hker hn3 hc0 hN
      have hcast : ((ε % 2 : ℕ) : ZMod 2) = 0 := by
        have h1 : Multiplicative.ofAdd ((ε % 2 : ℕ) : ZMod 2) = 1 := by
          rw [← hfg.2]
          exact hgraph
        have h := congrArg Multiplicative.toAdd h1
        simpa using h
      have hmod : ε % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one ε with h0 | h1
        · exact h0
        · exfalso
          rw [h1] at hcast
          norm_num at hcast
      have heven : Even ε := by
        rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
        exact hmod
      have hborel0 : borelStd (n + 1) F A τ ε = borelStd (n + 1) F A τ 0 := by
        rw [borelStd_eq_stdAut_mod_two, borelStd_eq_stdAut_mod_two, hmod]
      have hrep0 : ∀ g x, δ e (σ g x) = σ (borelStd (n + 1) F A τ 0 g) (δ e x) := by
        intro g x
        rw [← hborel0]
        exact hc0 g x
      have hτ : τ = RingEquiv.refl F := hcase e A hA τ hrep0
      rw [hfg.1, hτ]
      rfl
  by_cases hinf : δE.range ⊓ π.range = ⊥
  · have hDbar1 : δE.range ≠ ⊥ := by
      obtain ⟨d, hd⟩ := hD1
      intro hbot
      have hmem : δE d ∈ δE.range := MonoidHom.mem_range.mpr ⟨d, rfl⟩
      rw [hbot] at hmem
      have h1 : δE d = 1 := by simpa using hmem
      have hδ1 : δ d = 1 := by
        apply LinearMap.ext
        intro x
        have h := congrArg (fun e : X ≃ₗ[E] X => e x) h1
        rw [hδ_apply d x] at h
        simpa using h
      exact hd hδ1
    obtain ⟨u, huU, hu1, hu2, hcardu⟩ :=
      exists_inner_involution_of_offender_inf_eq_bot (R := E) (Y := X) (n := n + 1) π hker hn3
        hodd δE.range hDbarN hDbar2 hDbar1 hDbarU hinf hoffBar
    have hfix_eq : Nat.card {y : X // π u y = y} =
        Nat.card (fixSub σ (Subgroup.zpowers u)) := by
      rw [card_fixSub_zpowers σ u]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => by rw [hπ_apply]))
    rw [hfix_eq] at hcardu
    refine Or.inl ⟨u, huU, hu1, hu2, ?_⟩
    have hcodim := pow_finrank_sub_finrank_fixSub_le (n := n) (k := k) σ (Subgroup.zpowers u) hcardu
    have hrank : Module.finrank k (LinearMap.range (extendScalars k σ u - 1)) =
        Module.finrank k (k ⊗[E] X) -
          Module.finrank k (fixSub (extendScalars k σ) (Subgroup.zpowers u)) := by
      have h := LinearMap.finrank_range_add_finrank_ker
        (extendScalars k σ u - 1 : (k ⊗[E] X) →ₗ[k] (k ⊗[E] X))
      rw [← fixSub_zpowers_eq_ker_sub_one (K := k) (M := k ⊗[E] X)
        (extendScalars k σ) u] at h
      omega
    rw [hrank]
    exact hcodim
  · let A : Subgroup (X ≃ₗ[E] X) := δE.range ⊓ π.range
    have hA_ne : A ≠ ⊥ := hinf
    have hAr : A ≤ π.range := inf_le_right
    have hA2 : ∀ d ∈ A, d * d = 1 := fun d hd => hDbar2 d hd.1
    have hAU : A ≤ Subgroup.normalizer
        ((LinearFlag.unitriangular (n + 1) F).map π : Set (X ≃ₗ[E] X)) :=
      le_trans inf_le_left hDbarU
    obtain ⟨A₀, hA₀U, hmap, hinj, hcardA₀⟩ :=
      exists_unitriangular_lift π hker hAr hAU hA2
    have hA₀_ne : A₀ ≠ ⊥ := by
      intro hbot
      apply hA_ne
      rw [← hmap, hbot, Subgroup.map_bot]
    have hA₀_2 : ∀ a ∈ A₀, a * a = 1 := by
      intro a ha
      have hmemA : π a ∈ A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem π ha
      have hπa2 : π a * π a = 1 := hDbar2 (π a) hmemA.1
      have h1 : π (a * a) = π (1 : SpecialLinearGroup (Fin (n + 1)) F) := by
        rw [map_mul, hπa2, map_one]
      exact (injOn_unitriangular π hker)
        ((LinearFlag.unitriangular (n + 1) F).mul_mem (hA₀U ha) (hA₀U ha))
        ((LinearFlag.unitriangular (n + 1) F).one_mem) h1
    have hA₀_quad : ∀ a ∈ A₀, ∀ b ∈ A₀,
        (extendScalars k σ a - 1) * (extendScalars k σ b - 1) = 0 := by
      intro a ha b hb
      have hmemA : π a ∈ A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem π ha
      have hmemB : π b ∈ A := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem π hb
      obtain ⟨ea, hea⟩ := MonoidHom.mem_range.mp hmemA.1
      obtain ⟨eb, heb⟩ := MonoidHom.mem_range.mp hmemB.1
      have hfa : (σ a : X →ₗ[E] X) = (δE ea : X →ₗ[E] X) := by
        have h1 : (π a : X ≃ₗ[E] X) = δE ea := hea.symm
        have h2 : (σ a : X →ₗ[E] X) = (π a : X →ₗ[E] X) := by
          ext x
          exact (hπ_apply a x).symm
        rw [h2, h1]
      have hfb : (σ b : X →ₗ[E] X) = (δE eb : X →ₗ[E] X) := by
        have h1 : (π b : X ≃ₗ[E] X) = δE eb := heb.symm
        have h2 : (σ b : X →ₗ[E] X) = (π b : X →ₗ[E] X) := by
          ext x
          exact (hπ_apply b x).symm
        rw [h2, h1]
      have hcomp : ((δE ea : X →ₗ[E] X) - 1) * ((δE eb : X →ₗ[E] X) - 1) = 0 := by
        ext x
        have h := hquad eb ea x
        rw [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sub_apply,
          Module.End.one_apply, Module.End.one_apply]
        have hb : (δE eb : X →ₗ[E] X) x = δ eb x := rfl
        rw [show (δE ea : X →ₗ[E] X) ((δE eb : X →ₗ[E] X) x - x) =
              δ ea (δ eb x - x) from by rw [hb]; rfl]
        rw [h, hb]
        exact sub_self _
      have hbasea : (extendScalars k σ a - 1) =
          LinearMap.baseChange k ((δE ea : X →ₗ[E] X) - 1) := by
        rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
        congr 1
        rw [extendScalars_apply, ← hfa]
      have hbaseb : (extendScalars k σ b - 1) =
          LinearMap.baseChange k ((δE eb : X →ₗ[E] X) - 1) := by
        rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
        congr 1
        rw [extendScalars_apply, ← hfb]
      rw [hbasea, hbaseb, ← LinearMap.baseChange_mul, hcomp, LinearMap.baseChange_zero]
    have hC_le : Nat.card {y : X // ∀ d ∈ δE.range, d y = y} ≤
        Nat.card (fixSub σ A₀) := by
      have hsub : Nat.card {y : X // ∀ d ∈ δE.range, d y = y} ≤
          Nat.card {y : X // ∀ g ∈ A, g y = y} := by
        refine Nat.card_le_card_of_injective
          (fun y => ⟨y.1, fun g hg => y.2 g hg.1⟩) ?_
        intro y₁ y₂ h
        exact Subtype.ext (congrArg (fun z : {y : X // ∀ g ∈ A, g y = y} => (z : X)) h)
      have hfixA : Nat.card {y : X // ∀ g ∈ A, g y = y} = Nat.card (fixSub σ A₀) := by
        refine Nat.card_congr ?_
        exact
          { toFun := fun y => ⟨y.1, by
              rw [mem_fixSub]
              intro a ha
              have hmem : π a ∈ A := by
                rw [← hmap]
                exact Subgroup.mem_map_of_mem π ha
              rw [← hπ_apply]
              exact y.2 (π a) hmem⟩
            invFun := fun y => ⟨y.1, fun g hg => by
              have hg' : g ∈ A₀.map π := by rw [hmap]; exact hg
              obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg'
              rw [hπ_apply]
              exact (mem_fixSub (ρ := σ) (S := A₀)).mp y.2 a ha⟩
            left_inv := fun _ => Subtype.ext rfl
            right_inv := fun _ => Subtype.ext rfl }
      rw [hfixA] at hsub
      exact hsub
    have hoffA : Nat.card X ≤ (c * Nat.card A₀) * Nat.card (fixSub σ A₀) := by
      calc Nat.card X ≤ Nat.card δE.range *
            Nat.card {y : X // ∀ d ∈ δE.range, d y = y} := hoffBar
        _ ≤ Nat.card δE.range * Nat.card (fixSub σ A₀) := Nat.mul_le_mul_left _ hC_le
        _ ≤ (c * Nat.card ↥(δE.range ⊓ π.range)) * Nat.card (fixSub σ A₀) :=
            Nat.mul_le_mul_right _ hDbarBound
        _ = (c * Nat.card A₀) * Nat.card (fixSub σ A₀) := by rw [← hcardA₀]
    refine Or.inr ⟨A₀, hA₀U, hA₀_ne, hA₀_2, hA₀_quad, ?_⟩
    exact pow_finrank_sub_finrank_fixSub_le (n := n) (k := k) σ A₀ hoffA

end CFSG.LieType.SpecialLinear

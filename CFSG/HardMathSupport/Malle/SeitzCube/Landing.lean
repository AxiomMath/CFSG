module

public import CFSG.LieType.SeitzGeneration.HyperExCubeUntw
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInner
public import CFSG.RankThree.PartOne.KE.A1Untwisted
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

section Transport

variable {G : Type*} [Group G] {p r : ℕ}

@[expose] def CubeNormalizing (p r : ℕ) (E R : Subgroup G) : Prop :=
  IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
    ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R

theorem CubeNormalizing.map {H : Type*} [Group H] {E R : Subgroup G}
    (h : CubeNormalizing p r E R) (φ : G →* H) (hφ : Function.Injective φ) :
    CubeNormalizing p r (E.map φ) (R.map φ) := by
  obtain ⟨⟨hEc, hEp⟩, hc, hR, hRp, hN⟩ := h
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_, hRp.map φ, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    refine Subtype.ext ?_
    change φ x * φ y = φ y * φ x
    have := congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg φ this
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEp x hx, map_one]
  · rw [Subgroup.card_map_of_injective hφ, hc]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hφ]
  · rintro _ ⟨x, hx, rfl⟩
    have key : ((MulAut.conj (φ x)).toMonoidHom).comp φ = φ.comp (MulAut.conj x).toMonoidHom :=
      MonoidHom.ext fun y => by simp [MulAut.conj_apply]
    rw [Subgroup.map_map, key, ← Subgroup.map_map, hN x hx]

theorem CubeNormalizing.subgroupOf {T E R : Subgroup G} (h : CubeNormalizing p r E R)
    (hET : E ≤ T) (hRT : R ≤ T) : CubeNormalizing p r (E.subgroupOf T) (R.subgroupOf T) := by
  obtain ⟨⟨hEc, hEp⟩, hc, hR, hRp, hN⟩ := h
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_, ?_, ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    show a.1.1 * b.1.1 = b.1.1 * a.1.1
    exact congrArg Subtype.val
      (hEc.is_comm.comm (⟨a.1.1, a.2⟩ : E) (⟨b.1.1, b.2⟩ : E))
  · exact Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hEp _ hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv, hc]
  · intro hbot
    refine hR ((Subgroup.eq_bot_iff_forall R).2 fun x hx => ?_)
    have hx' : (⟨x, hRT hx⟩ : T) ∈ R.subgroupOf T := hx
    rw [hbot, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRT).symm
  · have hNx := hN x.1 hx
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (x.1 * z.1 * x.1⁻¹) ∈ R
      rw [← hNx]
      exact ⟨z.1, hz, rfl⟩
    · intro hy
      have hy' : y.1 ∈ R.map (MulAut.conj x.1).toMonoidHom := by rw [hNx]; exact hy
      obtain ⟨w, hw, hwy⟩ := hy'
      refine ⟨x⁻¹ * y * x, ?_, ?_⟩
      · change (x.1⁻¹ * y.1 * x.1) ∈ R
        have hw' : x.1⁻¹ * y.1 * x.1 = w := by
          rw [← hwy]; simp [MulAut.conj_apply, mul_assoc]
        rw [hw']
        exact hw
      · refine Subtype.ext ?_
        simp [MulAut.conj_apply, mul_assoc]

end Transport

@[expose] def twistFix (τ : Tag) {L : Type} [Field L] (Fr : L →+* L) (n : ModGL τ L) :
    Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ (negPhi Fr n).eqLocus (MonoidHom.id _)

theorem mem_twistFix {τ : Tag} {L : Type} [Field L] {Fr : L →+* L} {n x : ModGL τ L} :
    x ∈ twistFix τ Fr n ↔
      x ∈ adjointGroup τ L ∧ n * Units.map (entrywiseHom Fr) x * n⁻¹ = x :=
  Iff.rfl

@[expose] def TwistedCube (τ : Tag) (L : Type) [Field L] (Fr : L →+* L) (p r : ℕ) : Prop :=
  ∃ n ∈ adjointGroup τ L, ∃ E R : Subgroup (ModGL τ L), E ≤ twistFix τ Fr n ∧
    R ≤ twistFix τ Fr n ∧ CubeNormalizing p r E R

section E8


theorem mem_map_baseChange_of_frobenius_fixed_E8 {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {x : ModGL .E8 L} (hx : x ∈ adjointGroup .E8 L)
    (hxF : Units.map (entrywiseHom Fr) x = x) :
    x ∈ (adjointGroup .E8 K).map (baseChangeGL (algebraMap K L)) := by
  obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E8 Fr hFr hx hxF
  exact mul_mem (Subgroup.mem_map_of_mem _
    (CFSG.StandardType.RecipeExcLang.rootDiagUnit_mem_adjointGroup_of_det_one
      (Or.inr (Or.inr rfl)) a)) hu

theorem exists_injective_twistFix_E8 {K : Type} [Field K] [Finite K] {L : Type} [Field L]
    [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {n : ModGL .E8 L} (hn : n ∈ adjointGroup .E8 L) :
    ∃ ψ : ↥(twistFix .E8 Fr n) →* ↥(adjointGroup .E8 K), Function.Injective ψ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hFrEq : Fr = iterateFrobenius L (ringChar K) (f : ℕ) := RingHom.ext fun c => by
    rw [hFr, hq]
    exact (iterateFrobenius_def (ringChar K) (f : ℕ) c).symm
  obtain ⟨g0, hg0C, hg0⟩ := CFSG.RankThree.PartOne.KE.lang_conjugator_gen .E8 K
    (ℓ := ringChar K) (f := (f : ℕ)) f.pos L n hn
  rw [← hFrEq] at hg0
  let ι : ↥(adjointGroup .E8 K) →* ModGL .E8 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E8 K).subtype
  have hι : Function.Injective ι := (baseChangeGL_injective _).comp Subtype.val_injective
  have hmem : ∀ x : ↥(twistFix .E8 Fr n),
      (MulAut.conj g0).toMonoidHom.comp (twistFix .E8 Fr n).subtype x ∈ ι.range := by
    rintro ⟨x, hxC, hxF⟩
    have hxF' : n * Units.map (entrywiseHom Fr) x * n⁻¹ = x := hxF
    have hF : Units.map (entrywiseHom Fr) (g0 * x * g0⁻¹) = g0 * x * g0⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Units.map (entrywiseHom Fr) x * (g0 * n)⁻¹
          = g0 * (n * Units.map (entrywiseHom Fr) x * n⁻¹) * g0⁻¹ := by group
        _ = g0 * x * g0⁻¹ := by rw [hxF']
    obtain ⟨y, hy, hyx⟩ := mem_map_baseChange_of_frobenius_fixed_E8 Fr hFr
      (mul_mem (mul_mem hg0C hxC) (inv_mem hg0C)) hF
    exact ⟨⟨y, hy⟩, hyx⟩
  let c : ↥(twistFix .E8 Fr n) →* ι.range :=
    ((MulAut.conj g0).toMonoidHom.comp (twistFix .E8 Fr n).subtype).codRestrict ι.range hmem
  refine ⟨(MonoidHom.ofInjective hι).symm.toMonoidHom.comp c,
    (MonoidHom.ofInjective hι).symm.injective.comp fun x y hxy => ?_⟩
  exact Subtype.ext ((MulAut.conj g0).injective (congrArg Subtype.val hxy))

end E8

section Cat


theorem exists_cube_cat_E8_of_twisted (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ}
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → CharP K q.p →
      ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
        (∀ c, Fr c = c ^ q.card) → TwistedCube .E8 L Fr p q.p) :
    ∃ E : Subgroup (Cat ⟨TauCeti.LieTypeIndex.E8 q, hv⟩), IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ NormalizesRSub ⟨TauCeti.LieTypeIndex.E8 q, hv⟩ E := by
  obtain ⟨K, _, _, hK, hKc, ⟨ε⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  let Fr : L →+* L := iterateFrobenius L q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ q.card := fun c => by
    rw [TauCeti.PrimePower.card_def q]
    exact iterateFrobenius_def q.p q.exponent c
  obtain ⟨n, hn, E, R, hET, hRT, hER⟩ := h K hK hKc L Fr hFr
  obtain ⟨ψ, hψ⟩ := exists_injective_twistFix_E8 (K := K) Fr (fun c => by rw [hFr, hK]) hn
  have hφ : Function.Injective (ε.symm.toMonoidHom.comp ψ) := ε.symm.injective.comp hψ
  obtain ⟨hE, hc, hR, hRp, hN⟩ := (hER.subgroupOf hET hRT).map _ hφ
  refine ⟨_, hE, hc, _, hR, ?_, hN⟩
  rw [TauCeti.LieTypeIndex.characteristic_E8]
  exact hRp

@[expose] def TwistedCubeE8 (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) → ∀ p : ℕ, p.Prime → P (Nat.card K) p →
      TwistedCube .E8 L Fr p (ringChar K)

end Cat

end CFSG.HardMathSupport.Malle.SeitzCube

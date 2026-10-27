module

public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
import CFSG.LieType.Chevalley.NoncentralNormalSolvable
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.RecipeExcLang
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Open


theorem isPerfect_adjointGroup (τ : Tag) (k : Type) [Field k]
    (hk : τ = .G2 → 3 ≤ Nat.card k) : Group.IsPerfect (adjointGroup τ k) := by
  cases τ
  · exact CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k (hk rfl)
  all_goals exact ⟨single_edge_perfect _ k (by decide)⟩

theorem isSimpleGroup_adjointGroup_of_perfect (τ : Tag) (k : Type) [Field k] [Finite k]
    (hperf : Group.IsPerfect (adjointGroup τ k)) :
    IsSimpleGroup (adjointGroup τ k) ∧ ∃ x y : adjointGroup τ k, x * y ≠ y * x := by
  have hnc := (opposite_simple_root_noncommutativity τ k).2.2.1
  have : Nontrivial (adjointGroup τ k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨IsSimpleGroup.mk fun M hM => ?_, hnc⟩
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient τ k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup τ k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv


variable {K : Type} [Field K] [Finite K]

theorem exists_fixed_structure (τ : Tag) (σ : K ≃+* K) :
    ∃ ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K, Function.Injective ι ∧
      ι.range ≤ fixSubgroup (entrywiseAdjointAut τ σ) ∧
      ∃ _ : (ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal,
        Group.IsSolvable (↥(fixSubgroup (entrywiseAdjointAut τ σ)) ⧸
          ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, -, hJnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup τ K,
      x ∈ fixSubgroup (entrywiseAdjointAut τ σ) ↔
        (x : ModGL τ K) ∈ entrywiseFixedGroup τ σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut τ σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ x).trans h)
  let ι : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
    ((baseChangeGL (τ := τ) (fixSubfield σ).subtype).comp
      (adjointGroup τ (fixSubfield σ)).subtype).codRestrict (adjointGroup τ K)
      fun u => baseChangeGL_mem_adjointGroup _ u.2
  have hι : ∀ u, (ι u : ModGL τ K) =
      baseChangeGL (fixSubfield σ).subtype (u : ModGL τ (fixSubfield σ)) := fun _ => rfl
  have hrange : ∀ x : adjointGroup τ K,
      x ∈ ι.range ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, (hι u).symm⟩
    · rintro ⟨u, hu, hux⟩
      exact ⟨⟨u, hu⟩, Subtype.ext (by rw [hι]; exact hux)⟩
  have hJle : ι.range ≤ fixSubgroup (entrywiseAdjointAut τ σ) := fun x hx =>
    (hfix x).2 (hJΓ ((hrange x).1 hx))
  have hJn : (ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hrange, hrange]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL τ K)
  have hsol : Group.IsSolvable
      (↥(fixSubgroup (entrywiseAdjointAut τ σ)) ⧸
        ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : ((x : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix x.1).1 x.2
    have hy : ((y : adjointGroup τ K) : ModGL τ K) ∈ entrywiseFixedGroup τ σ :=
      (hfix y.1).1 y.2
    have hq := hcomm (QuotientGroup.mk ⟨_, hx⟩) (QuotientGroup.mk ⟨_, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hrange]
    exact hq
  exact ⟨ι, fun a b hab => Subtype.ext (hinj (by rw [← hι a, ← hι b, hab])), hJle, hJn, hsol⟩

theorem g2Two_derived_exc {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    IsSimpleGroup ↥(commutator ↥(adjointGroup .G2 k)) ∧
      Nat.card ↥(commutator ↥(adjointGroup .G2 k)) = 6048 := by
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, hsimple⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM
    have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hM
    have hDM : (commutator ↥(adjointGroup .G2 k)).map (adjointGroup .G2 k).subtype =
        ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(adjointGroup .G2 k)) ≃*
        ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
      ((commutator ↥(adjointGroup .G2 k)).equivMapOfInjective _
        (adjointGroup .G2 k).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
    have := hsimple
    exact ⟨eD.isSimpleGroup, by rw [Nat.card_congr eD.toEquiv, hcard]⟩
  all_goals exact absurd h0 (by norm_num)


theorem exists_conj_eq_entrywiseAdjointAut (τ : Tag) {p : ℕ} (hp : p.Prime)
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hα : (MulAut.conj g * exactNormalAut τ K a σ 0) ^ p = 1) :
    ∃ ψ : MulAut (adjointGroup τ K),
      ψ * (MulAut.conj g * exactNormalAut τ K a σ 0) * ψ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hK4 : 4 ≤ Nat.card K := four_le_card_of_ne_one hℓ n.pos hK hσ
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ
  let w : inndiagGroup τ K := ⟨(g : ModGL τ K) * rootDiagUnit τ a,
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)⟩
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (adjointGroup τ K),
      α = MulAut.conj g * exactNormalAut τ K a σ 0 := ⟨_, rfl⟩
  rw [← hαdef] at hα ⊢
  have hαeq : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (w : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (w : ModGL τ K)⁻¹ := by
    intro h
    rw [hαdef, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero]
    simp only [w, mul_inv_rev, one_mul, inv_one, mul_one]
    group
  let ιC : adjointGroup τ K → inndiagGroup τ K := fun h => ⟨h, adjointGroup_le_inndiagGroup h.2⟩
  obtain ⟨X, hXdef⟩ : ∃ X : MulAut (inndiagGroup τ K),
      X = MulAut.conj w * inndiagFieldAut τ K σ := ⟨_, rfl⟩
  have hX1 : ∀ h : adjointGroup τ K, X (ιC h) = ιC (α h) := fun h => Subtype.ext (by
    rw [hXdef, MulAut.mul_apply, MulAut.conj_apply]
    change (w : ModGL τ K) * (inndiagFieldAut τ K σ (ιC h) : ModGL τ K) * (w : ModGL τ K)⁻¹ = _
    rw [hαeq]
    rfl)
  have hXk : ∀ (k : ℕ) (h : adjointGroup τ K), (X ^ k) (ιC h) = ιC ((α ^ k) h) := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ', MulAut.mul_apply, ih, hX1, pow_succ', MulAut.mul_apply]
  have hXp : X ^ p = 1 := by
    refine MulEquiv.ext fun γ => ?_
    rw [MulAut.one_apply]
    obtain ⟨β, hβdef⟩ : ∃ β : MulAut (inndiagGroup τ K), β = X ^ p := ⟨_, rfl⟩
    rw [← hβdef]
    have hβι : ∀ h : adjointGroup τ K, β (ιC h) = ιC h := fun h => by
      rw [hβdef, hXk, hα, MulAut.one_apply]
    have hz : ∀ h ∈ adjointGroup τ K, ((γ⁻¹ * β γ : inndiagGroup τ K) : ModGL τ K) * h =
        h * ((γ⁻¹ * β γ : inndiagGroup τ K) : ModGL τ K) := by
      intro h hh
      have hh' : (γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹ ∈ adjointGroup τ K :=
        conj_mem_adjointGroup_of_mem_inndiag γ.2 hh
      have e2 : β (γ * ιC ⟨h, hh⟩ * γ⁻¹) = β γ * ιC ⟨h, hh⟩ * (β γ)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hβι]
      have e3 : γ * ιC ⟨h, hh⟩ * γ⁻¹ = ιC ⟨_, hh'⟩ := rfl
      rw [e3, hβι] at e2
      have e4 : (γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹ =
          (β γ : ModGL τ K) * h * (β γ : ModGL τ K)⁻¹ := congrArg Subtype.val e2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (γ : ModGL τ K)⁻¹ * (β γ : ModGL τ K) * h =
          (γ : ModGL τ K)⁻¹ * ((β γ : ModGL τ K) * h * (β γ : ModGL τ K)⁻¹) *
            (β γ : ModGL τ K) := by group
        _ = (γ : ModGL τ K)⁻¹ * ((γ : ModGL τ K) * h * (γ : ModGL τ K)⁻¹) *
            (β γ : ModGL τ K) := by rw [e4]
        _ = h * ((γ : ModGL τ K)⁻¹ * (β γ : ModGL τ K)) := by group
    have h1 := eq_one_of_commute_adjointGroup hK4 (γ⁻¹ * β γ).2 hz
    exact (inv_mul_eq_one.1 (Subtype.ext h1)).symm
  obtain ⟨g', hg'⟩ := exists_conj_eq_inndiagFieldAut (τ := τ) n.pos hK hp σ hord w
    (by rw [← hXdef]; exact hXp)
  refine ⟨inndiagConj τ K g', MulEquiv.ext fun h => Subtype.ext ?_⟩
  have e1 := congrArg (fun φ : MulAut (inndiagGroup τ K) => (φ (ιC h) : ModGL τ K)) hg'
  rw [← hXdef] at e1
  have hc1 : ∀ u : adjointGroup τ K,
      (MulAut.conj g') (ιC u) = ιC (inndiagConj τ K g' u) := fun u => Subtype.ext rfl
  have hc2 : ∀ u : adjointGroup τ K,
      (MulAut.conj g')⁻¹ (ιC u) = ιC ((inndiagConj τ K g')⁻¹ u) := fun u => by
    rw [← map_inv, ← map_inv]
    exact Subtype.ext rfl
  simp only [MulAut.mul_apply] at e1 ⊢
  rw [hc2, hX1, hc1] at e1
  exact e1

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy

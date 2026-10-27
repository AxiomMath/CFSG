module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorULinear
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorUField
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBHyperbolic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem map_conj_eq_of_le_center {G : Type*} [Group G] {Z : Subgroup G} (hZ : Z ≤ center G)
    (T : G) : Z.map (MulAut.conj T).toMonoidHom = Z := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change T * w * T⁻¹ ∈ Z
    rw [mem_center_iff.mp (hZ hw) T, mul_inv_cancel_right]
    exact hw
  · intro hz
    refine ⟨z, hz, ?_⟩
    change T * z * T⁻¹ = z
    rw [mem_center_iff.mp (hZ hz) T, mul_inv_cancel_right]

theorem onQuotient_conj {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal] (T : G)
    (hT : Z.map (MulAut.conj T).toMonoidHom = Z) :
    CatalogueBFixedCentralQuotient.onQuotient Z (MulAut.conj T) hT =
      MulAut.conj (QuotientGroup.mk' Z T) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z x
  rw [CatalogueBFixedCentralQuotient.onQuotient_mk, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv]

theorem su_socle_false {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) (hs : SmallSource L)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 5 ≤ n)
    (e : W ≃* StatedProj (StatedSU n (p ^ f) K)) : False := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  let θ : W ≃* hypPSU hud r ε := (e.trans (unitaryPSUEquiv hud (by omega)).symm).trans
    (hypProjTransport hud (R := R) hR).symm
  have : IsSimpleGroup (hypPSU hud r ε) := θ.symm.isSimpleGroup
  have hnab : ∃ x y : hypPSU hud r ε, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnab
    refine ⟨θ x, θ y, fun h => hxy (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  obtain ⟨ρ, X, hinj, -, hX, -, ⟨eLX⟩⟩ := fixed_component_of_socle hCW θ hZ hLCW
  have hsX : SmallSource X := smallSource_of_mulEquiv eLX hs
  have hβ : orderOf (ρ a) = 2 := (orderOf_injective ρ hinj a).trans ha
  obtain ⟨-, -, -, hrep⟩ := odd_unitary_automorphism_semilinear_representation hud hp2 hr hε
    (by omega)
  obtain ⟨Am, τσ, hx, hA, hβeq, hσ, hid, hbar⟩ := hrep (ρ a) hβ
  have happly : ∀ g : hypSU hud r ε,
      ρ a (hypProj hud r ε g) = hypProj hud r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    intro g
    rw [← hβeq]
    exact semilinearAutHom_apply hud hr hε _ g
  have hdim : finrank K (HypIndex r ε → K) = 2 * r + ε := UnitaryHigher.finrank_hypIndex_fun
  let ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  have key : ∀ ψ : MulAut (sesqProjUnitary hud (hypForm hud r ε)),
      (∀ y, ι (ρ a y) = ψ (ι y)) → CFSG.Assembly.IsComponentOf (X.map ι) (fixedSubgroup ψ) := by
    intro ψ he
    have hmap : (fixedSubgroup (ρ a)).map ι = projSpecial hud (hypForm hud r ε) ⊓
        fixedSubgroup ψ := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨(hypModelEquiv hud y).2, ?_⟩
        change ψ (ι y) = ι y
        rw [← he]
        exact congrArg ι hy
      · rintro ⟨hzN, hzψ⟩
        obtain ⟨y, hy⟩ := (hypModelEquiv hud).surjective ⟨z, hzN⟩
        have hyz : ι y = z := congrArg Subtype.val hy
        refine ⟨y, ?_, hyz⟩
        change ρ a y = y
        apply hι
        rw [he, hyz]
        exact hzψ
    have h1 := SymmetricLocal.isComponentOf_map_of_injective ι hι hX
    rw [hmap] at h1
    refine isComponentOf_of_normal_le h1 inf_le_right ?_
    constructor
    intro m hm g
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact ⟨(projSpecial_normal hud (hypForm hud r ε)).conj_mem _ hm.1 (g : sesqProjUnitary hud _),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hm.2) (Subgroup.inv_mem _ g.2)⟩
  have hsX₂ : SmallSource (X.map ι) := smallSource_of_mulEquiv (X.equivMapOfInjective ι hι) hsX
  have hZc := sesqNormOneScalars_le_center hud (hypForm hud r ε)
  rcases hσ with rfl | hσ
  ·
    set T : sesqUnitaryGroup (hypForm hud r ε) := hypUnitaryEquiv hud ⟨Am, hA⟩ with hTdef
    have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary hud (hypForm hud r ε)) = 2 := by
      rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
      exact hid rfl
    have he : ∀ y, ι (ρ a y) =
        MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) T) (ι y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective hud r ε y
      rw [happly]
      refine hypModelEquiv_conj hud ⟨Am, hA⟩ g _ ?_
      have hg : glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) =
          (g : GL (HypIndex r ε) K) :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) K) => φ (g : GL (HypIndex r ε) K))
          (map_one glAut)
      change Am * glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) * Am⁻¹ = _
      rw [hg]
    have hX₂ := key _ he
    have hφZ := map_conj_eq_of_le_center hZc T
    rw [← onQuotient_conj T hφZ] at hX₂
    have hTT : T * T ∈ center (sesqUnitaryGroup (hypForm hud r ε)) := by
      apply hZc
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT,
        pow_orderOf_eq_one]
    have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
      intro g
      rw [MulAut.conj_apply, MulAut.conj_apply]
      have h1 := mem_center_iff.mp hTT g
      calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
        _ = g := by rw [← h1, mul_inv_cancel_right]
    obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ := central_lift _ hZc _ hφZ hφφ hX₂
    rw [fixedSubgroup_conj] at hY
    refine su_linear_false hud hp2 (by rw [hdim]; omega) (hypForm_isSymm hud)
      (hypForm_separatingLeft hud) hT hY σY hσYs hσYk (fun y hy => ?_) hsX₂
    have h1 := hσYv y
    rw [hy] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1.symm
  ·
    obtain ⟨c, hc0, hAc⟩ := hbar hσ
    have hτB := hypForm_semilinearMatrixMap hud hA
    have he : ∀ y, ι (ρ a y) = antiProjConj hud
        (semilinearMatrixMap hud (Am : Matrix (HypIndex r ε) (HypIndex r ε) K))
        (semilinearMatrixMap_bijective hud hc0 hAc) hτB (ι y) := by
      intro y
      obtain ⟨g, rfl⟩ := hypProj_surjective hud r ε y
      rw [happly]
      exact hypModelEquiv_antiConj hud Am hc0 hAc hτB τσ hσ g _
    have hX₂ := key _ he
    obtain ⟨Y, hY, ⟨σY, -, hσYk, -⟩, -⟩ := central_lift _ hZc _
      (map_scalars_unitaryConj hud _ _ hτB)
      (unitaryConj_unitaryConj hud _ _ hτB (Units.mk0 c hc0) (semilinearMatrixMap_sq hud hAc))
      hX₂
    exact su_field_false hud hp2 (by rw [hdim]; omega) (hypForm_isSymm hud)
      (hypForm_separatingLeft hud) _ _ hτB (Units.mk0 c hc0) (semilinearMatrixMap_sq hud hAc)
      hY σY hσYk hsX₂

theorem su_family_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hs : SmallSource L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hn : 5 ≤ n) (hM : LieModel W .PSU n p f) : False := by
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1)
    inf_le_right
  have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
    (by simp [reeTitsTags]) (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact su_socle_false hWs hWnab hCW ha hLCW hs hp hp2 hf hK hn e

end CFSG.ComponentClassification.OddClassSelector

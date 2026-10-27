module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Orth
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Single

public section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

theorem su_linear_false_alt7 (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn3 : 3 ≤ finrank E V)
    (hn4 : finrank E V ≤ 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y)
    (hker : ∀ y : Y, σ y = 1 → (y : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    (hs : SmallSource X) (hA7 : Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  by_cases h4 : finrank E V = 4
  ·
    obtain ⟨-, τ, -, -⟩ := su4_linear_paired_sl h hp h4 hB hBl hT hY σ hσs hσk hker hs
    obtain ⟨e₀⟩ := hA7
    have hp3 : 3 ≤ p := by
      have := h.prime.two_le
      omega
    have hcard : Nat.card E = (p ^ f) ^ 2 := h.card_eq_sq
    have h9 : 9 ≤ Nat.card E := by
      rw [hcard]
      have : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
      nlinarith
    have hEodd : Odd (Nat.card E) := by
      rw [hcard]
      exact ((h.prime.odd_of_ne_two hp).pow).pow
    exact not_surjective_sl2_alt7 hEodd (by omega)
      ((e₀.toMonoidHom.comp (QuotientGroup.mk' (center X))).comp
        (σ.comp τ.toMonoidHom))
      ((e₀.surjective.comp (QuotientGroup.mk'_surjective _)).comp
        (hσs.comp τ.surjective))
  ·
    have h3 : finrank E V = 3 := by omega
    obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
      projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
    have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
    let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) ≃* Y :=
      Subgroup.subgroupOfEquivOfLe hY.1
    rcases hN with hN | hN
    ·
      obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
      have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
        ⟨fun x y => hB.eq (x : V) (y : V)⟩
      rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent e hY₁) with
        h2 | h1
      · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
            (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component e hY₁ h2'
        have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
          intro y hy w hw
          have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
          rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
          exact h4.symm
        refine su_half_false h hp (hsymm _) hsepP (Submodule.one_le_finrank_iff.mpr hP) hM hYF
          (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
          ← MonoidHom.range_eq_map]
        exact hρ₁c
      · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
            ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
        have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
          intro y hy w hw
          have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
          rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
          exact h4.symm
        refine su_half_false h hp (hsymm _) hsepM (Submodule.one_le_finrank_iff.mpr hM) hP hYF
          (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
          ← MonoidHom.range_eq_map]
        exact hρ₁c
    ·
      obtain ⟨-, -, -, hdim2, -⟩ := hpaired hN
      omega

theorem su_field_false_alt7 (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hn3 : 3 ≤ finrank E V)
    (hn4 : finrank E V ≤ 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y
      (FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X)
    (hA7 : Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    have hoddK : Odd (Nat.card h.fixedField) := by
      rw [hK]
      exact hodd.pow
    exact false_of_orth_dim34_component hoddK (CatalogueBOrthogonalDescent.originalQuadratic B')
      hQ (by rw [hfinW]; omega)
      ((fixedCommutingEquiv h τ₀ hτ₀ hτ₀B).trans
        (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2))))
      hY₁ (σ.comp eY.toMonoidHom) (hσs.comp eY.surjective) hA7
  · obtain ⟨B', -, halt, hnd, hev, Φ, -⟩ := hB2 hμ1
    have h4 : finrank E V = 4 := by
      obtain ⟨r, hr⟩ := hev
      omega
    exact sp_component_false h.prime hp h.one_le hK B' halt hnd (by rw [hfinW]; omega)
      ((fixedCommutingEquiv h τ₀ hτ₀ hτ₀B).trans Φ) hY₁ (σ.comp eY.toMonoidHom) hσ₁k hs

section Socle

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem su_socle_alt7 {A : Type} [Group A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hodd7 : Odd (Nat.card (center L))) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn3 : 3 ≤ n)
    (hn4 : n ≤ 4) (e : W ≃* StatedProj (StatedSU n (p ^ f) K)) : False := by
  classical
  have hs : SmallSource L := Or.inr (Or.inl ⟨hsrc, hodd7⟩)
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
  have hsrcX₂ : Nonempty ((X.map ι) ⧸ center (X.map ι) ≃* alternatingGroup (Fin 7)) :=
    ⟨((CFSG.ComponentClassification.ExcSelector.centralQuotientCongr
      (eLX.trans (X.equivMapOfInjective ι hι))).symm).trans hsrc.some⟩
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
      have hg : UnitaryHigher.glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) =
          (g : GL (HypIndex r ε) K) :=
        congrArg (fun φ : MulAut (GL (HypIndex r ε) K) => φ (g : GL (HypIndex r ε) K))
          (map_one UnitaryHigher.glAut)
      change Am * UnitaryHigher.glAut (RingEquiv.refl K) (g : GL (HypIndex r ε) K) * Am⁻¹ = _
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
    refine su_linear_false_alt7 hud hp2 (by rw [hdim]; omega) (by rw [hdim]; omega)
      (hypForm_isSymm hud) (hypForm_separatingLeft hud) hT hY σY hσYs hσYk (fun y hy => ?_)
      hsX₂ hsrcX₂
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
    obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, -⟩, -⟩ := central_lift _ hZc _
      (map_scalars_unitaryConj hud _ _ hτB)
      (unitaryConj_unitaryConj hud _ _ hτB (Units.mk0 c hc0) (semilinearMatrixMap_sq hud hAc))
      hX₂
    exact su_field_false_alt7 hud hp2 (by rw [hdim]; omega) (by rw [hdim]; omega)
      (hypForm_isSymm hud) (hypForm_separatingLeft hud) _ _ hτB (Units.mk0 c hc0)
      (semilinearMatrixMap_sq hud hAc) hY σY hσYs hσYk hsX₂ hsrcX₂

theorem su_family_false_alt7 {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hodd7 : Odd (Nat.card (center L))) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) (hM : LieModel W .PSU n p f) : False := by
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1)
    inf_le_right
  have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
    (by simp [reeTitsTags]) (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact su_socle_alt7 hWs hWnab hCW ha hLCW hsrc hodd7 hp hp2 hf hK hn3 hn4 e

end Socle

end CFSG.ComponentClassification.OddClassSelector

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.IVK
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem ivk714_psu_three_four {n p f : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) : Ivk714Empty (fun X _ => LieModel X .PSU n p f) := by
  intro K _ _ hs hK z hz h
  have hZ : center K = ⊥ := center_eq_bot_of_simple_of_nonab hs h.nonabelian
  obtain ⟨L, hLW, hL, hq, hodd⟩ := h.exists_inner_component hZ
  have hCW := centralizer_inner_eq_bot_of_center_eq_bot hZ
  let e : K ≃* ↥(inner K) := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)
  have hWs : IsSimpleGroup ↥(inner K) := e.symm.isSimpleGroup
  have hWnab : ∃ x y : ↥(inner K), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h'
  exact CFSG.ComponentClassification.OddClassSelector.su_family_false_alt7 (A := MulAut K)
    (W := inner K) hWs hWnab hCW hz hLW hL hq hodd hp hp2 hf hn3 hn4
    (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hK)

theorem ivk714_u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk714Empty (fun X _ => LieModel X .PSU 3 p f) :=
  fun _ _ hp hp2 hf => ivk714_psu_three_four (by norm_num) (by norm_num) hp hp2 hf

theorem ivk714_u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk714Empty (fun X _ => LieModel X .PSU 4 p f) :=
  fun _ _ hp hp2 hf _ => ivk714_psu_three_four (by norm_num) (by norm_num) hp hp2 hf

end CFSG.GH74.GLS.IVK.Proofs2

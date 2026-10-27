module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

namespace HarrisN36

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.HarrisLit.N36 (map_ne_map_of_commute
  ne_of_commute_of_isQuasisimple even_mul_sq_sub_div_two)

theorem isComponentOf_comap_of_intertwine {P D : Type*} [Group P] [Group D] (ι : P →* D)
    (hι : Function.Injective ι) {β : MulAut P} {βD : MulAut D}
    (he : ∀ y, ι (β y) = βD (ι y)) {R : Subgroup D}
    (hR : Assembly.IsComponentOf R (fixedSubgroup βD)) (hRr : R ≤ ι.range) :
    Assembly.IsComponentOf (R.comap ι) (fixedSubgroup β) := by
  have hmap : (fixedSubgroup β).map ι = ι.range ⊓ fixedSubgroup βD := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change βD (ι y) = ι y
      rw [← he]
      exact congrArg ι hy
    · rintro ⟨⟨y, rfl⟩, hzψ⟩
      refine ⟨y, ?_, rfl⟩
      change β y = y
      apply hι
      rw [he]
      exact hzψ
  have h1 : Assembly.IsComponentOf R (ι.range ⊓ fixedSubgroup βD) :=
    isComponentOf_of_le hR (le_inf hRr hR.1) inf_le_right
  have h2 := OddClassSelector.isComponentOf_comap_of_le_range ι hι h1 inf_le_left
  rwa [← hmap, comap_map_eq_self_of_injective hι] at h2

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

set_option maxHeartbeats 400000 in
theorem anti_twin (hp : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {z : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = z • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : Assembly.IsComponentOf Y (fixedSubgroup (antiConjA h hAu)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) :
    (∃ Y₂ : Subgroup (sesqUnitaryGroup (stdHermForm h 4)),
        Assembly.IsComponentOf Y₂ (fixedSubgroup (antiConjA h hAu)) ∧ Y₂ ≠ Y ∧
          Nonempty (Y₂ ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) ∨
      ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
        Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 E') := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hk2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτ₀B := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hμ : ∀ v, antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 z hz0 : Kˣ) : K) • v :=
    CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 z hz0) hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
    finite_conjFixed
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp h1
  have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    exfalso
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    exact OddClassSelector.sp_component_false h.prime hp h.one_le hK B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun]) ((fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ) hY₁
      (σ.comp eY.toMonoidHom) hσ₁k hs
  obtain ⟨B', hB'v, hsym, hnd, Φ, -⟩ := hB1 hμ1
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  have hdim : Module.finrank h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  let Φ' : fixedSubgroup (antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B') :=
    (fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  let eYY' : Y ≃* (Y.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom :=
    eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
  by_cases hsplit : ∃ S : Submodule h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))),
      Module.finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  · left
    obtain ⟨hq5, -⟩ := component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
    obtain ⟨-, -, -, hsplitm, -, -, -⟩ :=
      orthogonal_low_dimensional_fixed_derived_component_coverage _ hQ'
        (Or.inl ⟨hKodd, Or.inr (Or.inl hdim)⟩)
    obtain ⟨-, e₀, -, -, hsup, hq₁, hq₂, hn₁, hn₂, hLR⟩ :=
      hsplitm hdim hsplit (by omega) (by omega)
    have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBOrthogonalDescent.originalQuadratic B')), CFSG.IsQuasisimple M →
        M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')) →
        (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup
          (CatalogueBOrthogonalDescent.originalQuadratic B')))).Normal →
        CFSG.IsComponent M := fun M hMq hMle hMn =>
      ⟨hMq, Subgroup.IsSubnormal.trans hMle hMn.isSubnormal
        (Subgroup.Normal.isSubnormal inferInstance)⟩
    have hL := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
    have hR := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
    have htwin : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBOrthogonalDescent.originalQuadratic B')), CFSG.IsComponent M →
        (Y.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom ≠ M →
        Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField) →
        ∃ Y₂ : Subgroup (sesqUnitaryGroup (stdHermForm h 4)),
          Assembly.IsComponentOf Y₂ (fixedSubgroup (antiConjA h hAu)) ∧ Y₂ ≠ Y ∧
            Nonempty (Y₂ ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
      intro M hM hne ⟨eM⟩
      have hY₂C : (M.map Φ'.symm.toMonoidHom).map (fixedSubgroup (antiConjA h hAu)).subtype ≤
          fixedSubgroup (antiConjA h hAu) := map_subtype_le _
      have hY₂s : ((M.map Φ'.symm.toMonoidHom).map
          (fixedSubgroup (antiConjA h hAu)).subtype).subgroupOf (fixedSubgroup (antiConjA h hAu)) =
          M.map Φ'.symm.toMonoidHom :=
        comap_map_eq_self_of_injective (fixedSubgroup (antiConjA h hAu)).subtype_injective _
      have hMM : (M.map Φ'.symm.toMonoidHom).map Φ'.toMonoidHom = M := by
        ext x
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨Φ'.symm x, ⟨x, hx, rfl⟩, by simp⟩
      refine ⟨_, (isComponentOf_iff_isComponent_subgroupOf hY₂C).mpr ?_, ?_, ?_⟩
      · rw [hY₂s]
        exact isComponent_map_of_isComponent Φ'.symm hM
      · intro heq
        apply hne
        rw [← heq, hY₂s, hMM]
      · exact ⟨(subgroupOfEquivOfLe hY₂C).symm.trans ((MulEquiv.subgroupCongr hY₂s).trans
          ((M.equivMapOfInjective _ Φ'.symm.injective).symm.trans eM))⟩
    have hLR' : (determinantLeftFactor h.fixedField).map e₀.symm.toMonoidHom ≠
        (determinantRightFactor h.fixedField).map e₀.symm.toMonoidHom :=
      ne_of_commute_of_isQuasisimple hq₁ hLR
    have eL : Nonempty ((determinantLeftFactor h.fixedField).map e₀.symm.toMonoidHom ≃*
        Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
      ⟨((determinantLeftFactor h.fixedField).equivMapOfInjective e₀.symm.toMonoidHom
        e₀.symm.injective).symm.trans (MonoidHom.ofInjective (specialRho_inl_injective _)).symm⟩
    have eR : Nonempty ((determinantRightFactor h.fixedField).map e₀.symm.toMonoidHom ≃*
        Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
      ⟨((determinantRightFactor h.fixedField).equivMapOfInjective e₀.symm.toMonoidHom
        e₀.symm.injective).symm.trans (MonoidHom.ofInjective (specialRho_inr_injective _)).symm⟩
    rcases eq_or_eq_of_isComponent hL hR hsup hY' with hYL | hYR
    · exact htwin _ hR (by rw [hYL]; exact hLR') eR
    · exact htwin _ hL (by rw [hYR]; exact hLR'.symm) eL
  · right
    obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
      commutator_equiv_psl_of_nonsplit _ hQ' hKodd hdim hsplit
    have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
    have h3K : 3 ≤ Nat.card h.fixedField := by
      rw [hK]
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h3 : 3 < Nat.card E' := by
      rw [hE', sq]
      exact lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul h3K h3K)
    exact ⟨E', inferInstance, inferInstance, hE', center_quotient_equiv_of_psl h3 σ hσs hσk
      ((eYY'.trans (MulEquiv.subgroupCongr hYeq)).trans eC)⟩

theorem psu4_anti_twin [Finite K] (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSU 4 (p ^ f) K))}
    {X' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hX' : Assembly.IsComponentOf X' (fixedSubgroup β)) (hs : SmallSource X')
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, β (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {z : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      z • 1) :
    (∃ X₂ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)),
        Assembly.IsComponentOf X₂ (fixedSubgroup β) ∧ X₂ ≠ X' ∧ Even (Nat.card X₂)) ∨
      ∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
        Nonempty (X' ⧸ center X' ≃* GorensteinWalter.PSL2 E') := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hKodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  have hτ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτB := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have he : ∀ y, ιU h (β y) = antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))
      hτ hτB (ιU h y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, ιU_mk, ιU_mk, antiProjConj_mk]
    congr 1
    exact (toSesqUnitary_antiConj h hAu g (ψ g) (hψA g)).symm
  have key := isComponentOf_map_of_intertwine (ιU h) (ιU_injective h) (ιU_range_normal h) he hX'
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  have hαα : ∀ x, antiConjA h hAu (antiConjA h hAu x) = x := fun x =>
    unitaryConj_unitaryConj h _ _ hτB (Units.mk0 z hz0)
      (CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA) x
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ := OddClassSelector.central_lift _ hZc _
    (map_scalars_unitaryConj h _ _ hτB) hαα key
  have eX : X' ≃* X'.map (ιU h) := X'.equivMapOfInjective _ (ιU_injective h)
  have hs₂ : SmallSource (X'.map (ιU h)) := OddClassSelector.smallSource_of_mulEquiv eX hs
  rcases anti_twin h hp2 hAu hAA hY σY hσYs hσYk hs₂ with ⟨Y₂, hY₂, hne, ⟨eY₂⟩⟩ |
      ⟨E', _, _, hE', ⟨eP⟩⟩
  swap
  · exact Or.inr ⟨E', inferInstance, inferInstance, hE', ⟨(centerQuotientCongr eX).trans eP⟩⟩
  left
  set Zs := sesqNormOneScalars h (stdHermForm h 4) with hZs
  set π := QuotientGroup.mk' Zs with hπ
  have hR₂ : Assembly.IsComponentOf (Y₂.map π)
      (fixedSubgroup (antiProjConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)) hτ hτB)) :=
    isComponentOf_map_fixed (QuotientGroup.mk'_surjective Zs)
      (by rw [QuotientGroup.ker_mk']; exact hZc) hαα
      (fun x => (antiProjConj_mk h _ hτ hτB x).symm) hY₂
  have hY₂p : ⁅Y₂, Y₂⁆ = Y₂ := by
    have : Group.IsPerfect Y₂ := ⟨hY₂.2.2.1⟩
    exact Subgroup.commutator_eq_self
  have hR₂r : Y₂.map π ≤ (ιU h).range := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := le_range_toSesqUnitary h hY₂p hy
    exact ⟨QuotientGroup.mk g, ιU_mk h g⟩
  refine ⟨_, isComponentOf_comap_of_intertwine (ιU h) (ιU_injective h) he hR₂ hR₂r, ?_, ?_⟩
  ·
    intro heq
    have hYX : X'.map (ιU h) = Y.map π := by
      ext w
      constructor
      · intro hw
        obtain ⟨y, hy⟩ := hσYs ⟨w, hw⟩
        refine ⟨y, y.2, ?_⟩
        have h1 := hσYv y
        rw [hy] at h1
        exact h1.symm
      · rintro ⟨y, hy, rfl⟩
        have h1 := hσYv ⟨y, hy⟩
        rw [← h1]
        exact (σY ⟨y, hy⟩).2
    have h1 : Y₂.map π = Y.map π := by rw [← map_comap_eq_self hR₂r, heq, hYX]
    have hc : ⁅Y, Y₂⁆ = ⊥ := (isComponentOf_eq_or_commute hY hY₂).resolve_left (Ne.symm hne)
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
    have hq : Assembly.IsQuasisimple (Y.map π) := by rw [← hYX]; exact key.2.2
    exact map_ne_map_of_commute π hq (fun x hx y hy => (mem_centralizer_iff.mp (hle hx) y hy).symm)
      h1.symm
  ·
    have hcard : Nat.card ↥((Y₂.map π).comap (ιU h)) = Nat.card ↥(Y₂.map π) := by
      rw [← Subgroup.card_map_of_injective (ιU_injective h), map_comap_eq_self hR₂r]
    let σ₂ : Y₂ →* ↥(Y₂.map π) := (π.comp Y₂.subtype).codRestrict _ fun y => ⟨y, y.2, rfl⟩
    have hσ₂s : Function.Surjective σ₂ := by
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    have hσ₂k : σ₂.ker ≤ center Y₂ := by
      intro y hy
      have h0 : π (y : sesqUnitaryGroup (stdHermForm h 4)) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      have h1 : (y : sesqUnitaryGroup (stdHermForm h 4)) ∈ Zs := by
        rw [← QuotientGroup.ker_mk' Zs]
        exact h0
      rw [mem_center_iff]
      intro w
      exact Subtype.ext (mem_center_iff.mp (hZc h1) w)
    have : Group.IsPerfect Y₂ := ⟨hY₂.2.2.1⟩
    obtain ⟨eQ⟩ := center_quotient_equiv_of_sl σ₂ hσ₂s hσ₂k eY₂
    rw [hcard, Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(Y₂.map π)),
      Nat.card_congr eQ.toEquiv, GSThmB.Catalog7Std.card_psl2_of_odd hKodd rfl]
    exact (even_mul_sq_sub_div_two hKodd).mul_right _

end HarrisN36

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB

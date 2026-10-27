module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorU
public import CFSG.RankThree.CentralLift.LinearScalarCover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Frame
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSmall

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal)

variable {p f : ℕ}

section Sesq

variable {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem inner_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : finrank E V = 4) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {T : sesqUnitaryGroup B}
    (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y)
    (hker : ∀ y : Y, σ y = 1 → (y : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B)
    (hs : SmallSource X)
    (hbound : 2 * Nat.card (X ⧸ center X) < Nat.card E * (Nat.card E ^ 2 - 1)) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
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
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine OddClassSelector.su_half_false h hp (hsymm _) hsepP
        (Submodule.one_le_finrank_iff.mpr hP) hM hYF (ρ₁.comp eY.symm.toMonoidHom)
        (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
        OddClassSelector.restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine OddClassSelector.su_half_false h hp (hsymm _) hsepM
        (Submodule.one_le_finrank_iff.mpr hM) hP hYF (ρ₁.comp eY.symm.toMonoidHom)
        (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨-, -, -, hdim2, -, -, e, -⟩ := hpaired hN
    have hm2 : finrank E (eigenPlus l (unitaryOp T)) = 2 := by omega
    let bP : Basis (Fin 2) E (eigenPlus l (unitaryOp T)) := Module.finBasisOfFinrankEq E _ hm2
    let e' := e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hL' := isComponent_map_of_isComponent e' hY₁
    have : Group.IsPerfect ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
      e'.toMonoidHom) := hL'.1.1
    have : Nontrivial ((Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))).map
      e'.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    have hE9 : 9 ≤ Nat.card E := by
      rw [h.card, pow_mul]
      have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ (p ^ 2) ^ f := Nat.le_self_pow (by have := h.one_le; omega) _
    obtain ⟨hm2', h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters 2 E (by norm_num)
      (by omega)
    have hSL := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange 2 E hm2' h22 h23
      _ hL'.2
    let eY' : Y ≃* SpecialLinearGroup (Fin 2) E :=
      (eY.symm.trans (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)).trans
        ((MulEquiv.subgroupCongr hSL).trans
          (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).symm)
    have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
    have hcardY : Nat.card Y = Nat.card E * (Nat.card E ^ 2 - 1) := by
      rw [Nat.card_congr eY'.toEquiv, LinearFlag.card_SL_eq (by norm_num : 1 ≤ 2)]
      simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, show Finset.Icc 2 2 = {2} from rfl,
        Finset.prod_singleton]
    have hZY : Nat.card (center Y) ≤ 2 := by
      rw [Nat.card_congr (Subgroup.centerCongr eY').toEquiv, ← LinearFlag.scalars_eq_center]
      exact Nat.le_of_dvd two_pos (RankThree.CentralLift.card_scalars_dvd (k := E) (n := 2) 0)
    have hq := (center Y).card_eq_card_quotient_mul_card_subgroup
    rw [hcardY, Nat.card_congr (ShultStronglyClosedTI.centralLiftCenterQuotientEquiv σ hσs
      hσk).toEquiv] at hq
    have : Nat.card E * (Nat.card E ^ 2 - 1) ≤ Nat.card (X ⧸ center X) * 2 := by
      rw [hq]
      exact Nat.mul_le_mul_left _ hZY
    omega

end Sesq

theorem card_bound {q : ℕ} (hq3 : 3 ≤ q) : 2 * (q * (q ^ 2 - 1)) < q ^ 2 * ((q ^ 2) ^ 2 - 1) := by
  have h9 : 9 ≤ q ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
  have e4 : (q ^ 2) ^ 2 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have h1' : 1 ≤ q ^ 2 := by omega
    zify [h1', Nat.one_le_pow 2 (q ^ 2) (by omega)]
    ring
  rw [e4]
  have h2 : 2 < q * (q ^ 2 + 1) :=
    calc 2 < 3 := by norm_num
      _ ≤ q := hq3
      _ ≤ q * (q ^ 2 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
  calc 2 * (q * (q ^ 2 - 1)) = q * (q ^ 2 - 1) * 2 := by ring
    _ < q * (q ^ 2 - 1) * (q * (q ^ 2 + 1)) :=
      Nat.mul_lt_mul_of_pos_left h2 (Nat.mul_pos (by omega) (by omega))
    _ = q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 + 1)) := by ring

variable {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def toSesqU (A : GL (Fin 4) K)
    (hA : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) :
    sesqUnitaryGroup (stdHermForm h 4) :=
  ⟨Matrix.GeneralLinearGroup.toLin A, fun x y => CatFactsL4U4.StabU.stdHermForm_mulVec h hA x y⟩

theorem unitaryOp_toSesqU (A : GL (Fin 4) K)
    (hA : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) :
    unitaryOp (toSesqU h A hA) = Matrix.toLin' (A : Matrix (Fin 4) (Fin 4) K) :=
  LinearMap.ext fun x => (Matrix.toLin'_apply _ x).symm

variable {H : Type} [Group H] [Finite H]

theorem false_of_inner [Finite K] (c : Sp4Rec.Config H)
    (hp2 : p ≠ 2) (φ : ↥(generalizedFitting H) ≃* StatedProj (StatedSU 4 (p ^ f) K))
    {ρ : H →* MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : ↥(generalizedFitting H), ρ w = MulAut.conj (φ w))
    (hZ : center (StatedProj (StatedSU 4 (p ^ f) K)) = ⊥)
    (hKcard : Nat.card c.K ≤ p ^ f * ((p ^ f) ^ 2 - 1)) (hq : IsQuasisimple c.J)
    {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    {ψ : unitarySU p f K 4 →* unitarySU p f K 4}
    (hψ : ∀ g, ρ c.a (QuotientGroup.mk g) = QuotientGroup.mk (ψ g))
    (hψA : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K))
    {c₀ : K} (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = c₀ • 1) :
    False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  set P := StatedProj (StatedSU 4 (p ^ f) K)
  set D := sesqProjUnitary h (stdHermForm h 4)
  have hLc := c.isComponentOf_J hq
  obtain ⟨-, -, -, hL₁⟩ := OddSelector.socle_images φ hinj hρW c.J_le_G hLc
  have hcj := OddClassSelector.conj_injective hZ
  obtain ⟨hX, hXmap⟩ := OddClassSelector.isComponentOf_comap_conj hcj hL₁
  set X := (c.J.map ρ).comap MulAut.conj with hXdef
  have eJX : c.J ≃* X := (c.J.equivMapOfInjective ρ hinj).trans
    ((MulEquiv.subgroupCongr hXmap.symm).trans (X.equivMapOfInjective _ hcj).symm)
  set ι := EscapingNotOddUnitary.projEmbed h 4 (by norm_num) with hιdef
  have hι : Function.Injective ι := EscapingNotOddUnitary.projEmbed_injective h 4 (by norm_num)
  have hιn : ι.range.Normal := by
    rw [hιdef, EscapingNotOddUnitary.range_projEmbed]
    exact EscapingNotOddUnitary.toProj_range_normal h 4
  set T := toSesqU h A hAu with hTdef
  set Zs := sesqNormOneScalars h (stdHermForm h 4)
  have he : ∀ y, ι (ρ c.a y) = MulAut.conj (QuotientGroup.mk' Zs T) (ι y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hψ, MulAut.conj_apply]
    change QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 4 (ψ g)) =
      QuotientGroup.mk' Zs T * QuotientGroup.mk' Zs (EscapingNotOddUnitary.toSesqUnitary h 4 g) *
        (QuotientGroup.mk' Zs T)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    change ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x =
      unitaryOp T (unitaryOp (EscapingNotOddUnitary.toSesqUnitary h 4 g)
        (unitaryOp T⁻¹ x))
    have hTi : unitaryOp T⁻¹ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
      apply LinearMap.ext
      intro v
      have h1 : unitaryOp T (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v) = v := by
        rw [hTdef, unitaryOp_toSesqU, Matrix.toLin'_apply, Matrix.toLin'_apply,
          Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
      have hinvT : unitaryOp T⁻¹ * unitaryOp T = 1 := by
        rw [show unitaryOp T⁻¹ * unitaryOp T = unitaryOp (T⁻¹ * T) from rfl, inv_mul_cancel]
        rfl
      calc unitaryOp T⁻¹ v = unitaryOp T⁻¹ (unitaryOp T
          (Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v)) := by rw [h1]
        _ = Matrix.toLin' (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) v := by
          rw [← Module.End.mul_apply, hinvT, Module.End.one_apply]
    rw [hTi, hTdef, unitaryOp_toSesqU, unitaryOp_toSesqUnitary, Matrix.toLin'_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hψA, Matrix.mul_assoc]
  have key : CFSG.Assembly.IsComponentOf (X.map ι)
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' Zs T))) := by
    have hmap : (fixedSubgroup (ρ c.a)).map ι = ι.range ⊓
        fixedSubgroup (MulAut.conj (QuotientGroup.mk' Zs T)) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨y, rfl⟩, ?_⟩
        change MulAut.conj (QuotientGroup.mk' Zs T) (ι y) = ι y
        rw [← he]
        exact congrArg ι hy
      · rintro ⟨⟨y, rfl⟩, hzψ⟩
        refine ⟨y, ?_, rfl⟩
        change ρ c.a y = y
        apply hι
        rw [he]
        exact hzψ
    have h1 := SymmetricLocal.isComponentOf_map_of_injective ι hι hX
    rw [hmap] at h1
    refine OddClassSelector.isComponentOf_of_normal_le h1 inf_le_right ?_
    constructor
    intro m hm g
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact ⟨hιn.conj_mem _ hm.1 (g : D),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hm.2) (Subgroup.inv_mem _ g.2)⟩
  have hc₀ : h.norm c₀ = 1 := by
    have e1 := unitary_mul h hAu hAu
    rw [hAA, uStar_smul, uStar_one, smul_mul_smul_comm, Matrix.one_mul] at e1
    have e2 := congrFun (congrFun e1 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e2
    rw [UnitaryFieldData.norm, mul_comm]
    exact e2
  have hT2 : (QuotientGroup.mk' Zs T) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨c₀, hc₀, ?_⟩
    change unitaryOp (T * T) = c₀ • 1
    rw [show unitaryOp (T * T) = unitaryOp T * unitaryOp T from rfl, hTdef, unitaryOp_toSesqU,
      Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hAA, map_smul, Matrix.toLin'_one]
    rfl
  have hT1 : QuotientGroup.mk' Zs T ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨d, -, hd⟩ := h1
    change unitaryOp T = d • 1 at hd
    rw [hTdef, unitaryOp_toSesqU] at hd
    have hAd : (A : Matrix (Fin 4) (Fin 4) K) = d • 1 := by
      apply Matrix.toLin'.injective
      rw [hd, map_smul, Matrix.toLin'_one]
      rfl
    have hρa : ρ c.a = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hψ, MulAut.one_apply]
      congr 1
      apply SU_ext
      have h1 : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hAd, Matrix.mul_smul, Matrix.mul_one] at h1
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_smul] at h1
        exact zero_ne_one h1
      have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = d⁻¹ • 1 := by
        calc (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = d⁻¹ • (d • (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :=
              by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
          _ = d⁻¹ • 1 := by rw [h1]
      rw [hψA, hAd, hAi, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha1 : c.a = 1 := hinj (hρa.trans (map_one ρ).symm)
    have := c.orderOf_a
    rw [ha1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hT : orderOf (QuotientGroup.mk T : D) = 2 := orderOf_eq_prime hT2 hT1
  have hZc := sesqNormOneScalars_le_center h (stdHermForm h 4)
  have hφZ := OddClassSelector.map_conj_eq_of_le_center hZc T
  have hX₂ := key
  rw [← OddClassSelector.onQuotient_conj T hφZ] at hX₂
  have hTT : T * T ∈ center (sesqUnitaryGroup (stdHermForm h 4)) := by
    apply hZc
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp hTT g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  obtain ⟨Y, hY, ⟨σY, hσYs, hσYk, hσYv⟩, -⟩ :=
    OddClassSelector.central_lift _ hZc _ hφZ hφφ hX₂
  rw [CatalogueBUnitaryB.fixedSubgroup_conj] at hY
  have eJX' : c.J ≃* X.map ι := eJX.trans (X.equivMapOfInjective ι hι)
  have hs : SmallSource (X.map ι) :=
    OddClassSelector.smallSource_of_mulEquiv eJX' ((ExcSelector.smallSource_iff _).2
      (c.smallType_J hq))
  have hbound : 2 * Nat.card ((X.map ι) ⧸ center (X.map ι)) <
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    obtain ⟨hsimple, hnab⟩ := Sp4Rec.isSimpleGroup_of_isSmallAltOrL2 c.type_J
    have hZJ := Sp4Rec.center_eq_pPrimeCore hq hsimple hnab
    have e1 : Nat.card ((X.map ι) ⧸ center (X.map ι)) = Nat.card (c.J ⧸ pPrimeCore 2 c.J) := by
      rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZJ).toEquiv]
      exact (Nat.card_congr (QuotientGroup.congr (center c.J) (center (X.map ι)) eJX'
        (Subgroup.map_center_eq eJX')).toEquiv).symm
    obtain ⟨eJK⟩ := c.quotient_J_K
    have e2 : Nat.card (c.J ⧸ pPrimeCore 2 c.J) ≤ Nat.card c.K := by
      rw [Nat.card_congr eJK.toEquiv]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [e1]
    have hKq : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    rw [hKq]
    set q := p ^ f with hqdef
    have hq3 : 3 ≤ q := by
      have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
      exact hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have hlt := card_bound hq3
    calc 2 * Nat.card (c.J ⧸ pPrimeCore 2 c.J) ≤ 2 * (q * (q ^ 2 - 1)) :=
          Nat.mul_le_mul_left 2 (e2.trans hKcard)
      _ < q ^ 2 * ((q ^ 2) ^ 2 - 1) := hlt
  exact inner_false h hp2 (Module.finrank_fin_fun K) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) hT hY σY hσYs hσYk
    (fun y hy => by
      have h1 := hσYv y
      rw [hy] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1.symm) hs hbound

end Catalog7U4

end CFSG.ComponentClassification.GSThmB

module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EULift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUCase
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Lift

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj (stdG)
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks (X1)
open CFSG.ComponentClassification.CatFactsL4U4.StabU (scal)

theorem eq_card_of_quotient_psl2 {X : Type} [Group X] {N : Subgroup X} [N.Normal] {p g : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hXm : Blueprint.LieModel (X ⧸ N) .PSL 2 p g) {F₀ : Type}
    [Field F₀] [Finite F₀] (hF₀ : Odd (Nat.card F₀)) (eX : X ⧸ N ≃* GorensteinWalter.PSL2 F₀) :
    p ^ g = Nat.card F₀ := by
  obtain ⟨-, F', _, _, hF', ⟨eF'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hXm
  have hQodd : Odd (p ^ g) := (hp.odd_of_ne_two hp2).pow
  have h1 : Nat.card (X ⧸ N) = p ^ g * ((p ^ g) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (eF'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F').symm).toEquiv,
      Catalog7Std.card_psl2_of_odd hQodd hF']
  have h3 : Nat.card (X ⧸ N) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eX.toEquiv, Catalog7Std.card_psl2_of_odd hF₀ rfl]
  have h4 : p ^ g * ((p ^ g) ^ 2 - 1) = Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    have ha := Catalog7Std.two_dvd_mul_sq_sub (p ^ g)
    have hb := Catalog7Std.two_dvd_mul_sq_sub (Nat.card F₀)
    omega
  exact Catalog7Std.eq_of_mul_sq_sub_eq (Nat.one_le_pow _ _ hp.pos) Nat.card_pos h4

variable {r e : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r e K)

theorem toSesqUnitary_injective :
    Function.Injective (EscapingNotOddUnitary.toSesqUnitary h 4) := fun _ _ hab =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective (congrArg Subtype.val hab))

variable {H : Type} [Group H] [Finite H]

theorem psu4_component_type (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (hr2 : r ≠ 2) (φ : ↥(generalizedFitting H) ≃* StatedProj (StatedSU 4 (r ^ e) K))
    {ρ : H →* MulAut (StatedProj (StatedSU 4 (r ^ e) K))} (hinj : Function.Injective ρ)
    (hρW : ∀ w : ↥(generalizedFitting H), ρ w = MulAut.conj (φ w))
    (hZ : center (StatedProj (StatedSU 4 (r ^ e) K)) = ⊥)
    {x : H} (hx : orderOf x = 2) {X : Subgroup H} (hXF : X ≤ generalizedFitting H)
    (hXx : X ≤ centralizer ({x} : Set H))
    (hX : IsPComponent 2 (X.subgroupOf (centralizer ({x} : Set H))))
    {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ g)
    (hXm : Blueprint.LieModel (X ⧸ pPrimeCore 2 X) .PSL 2 p g) :
    pPrimeCore 2 X = center X ∧ CFSG.IsQuasisimple X ∧
      ∃ (A : GL (Fin 4) K) (ψ : unitarySU r e K 4 →* unitarySU r e K 4),
        uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 ∧
        (∀ y, ρ x (QuotientGroup.mk y) = QuotientGroup.mk (ψ y)) ∧
        ((p ^ g = (r ^ e) ^ 2 ∧
            (∀ y, ((ψ y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (A : Matrix (Fin 4) (Fin 4) K) * ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
            ∃ (Q : GL (Fin 4) K) (l : K), l ≠ 0 ∧
              uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = stdG ∧
              (A : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 l) ∨
          (p ^ g = (r ^ e) ^ 2 ∧
            (∀ y, ((ψ y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (A : Matrix (Fin 4) (Fin 4) K) *
                ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
                (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
            ∀ Y₁ : Subgroup (unitarySU r e K 4), ⁅Y₁, Y₁⁆ = Y₁ → (∀ y ∈ Y₁, ψ y = y) →
              ∀ φq : QuaternionGroup 2 →* Y₁, ¬ Function.Injective φq) ∨
          (p ^ g = r ^ e ∧
            (∀ y, ((ψ y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
              (A : Matrix (Fin 4) (Fin 4) K) *
                ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
                (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) ∧
            (∃ u : K, h.norm u = 1 ∧ (A : Matrix (Fin 4) (Fin 4) K).det = u ^ 2) ∧
            ∃ φq : QuaternionGroup 2 →* unitarySU r e K 4, Function.Injective φq ∧
              ∀ w, φq w ∈ ⁅((X.subgroupOf (generalizedFitting H)).map φ.toMonoidHom).comap
                  (QuotientGroup.mk' (scal r e K)),
                ((X.subgroupOf (generalizedFitting H)).map φ.toMonoidHom).comap
                  (QuotientGroup.mk' (scal r e K))⁆)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨h.prime⟩
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  have : Finite K := h.finite
  obtain ⟨-, F', _, _, hF', ⟨eF'⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hXm
  have hQodd : Odd (p ^ g) := (hp.odd_of_ne_two hp2).pow
  let eB : X ⧸ pPrimeCore 2 X ≃* GorensteinWalter.PSL2 F' :=
    eF'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F').symm
  have hQ3 : 3 < Nat.card F' := by rw [hF']; omega
  have hcardB : Nat.card (X ⧸ pPrimeCore 2 X) = p ^ g * ((p ^ g) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eB.toEquiv, Catalog7Std.card_psl2_of_odd hQodd hF']
  let psi : ↥(generalizedFitting H) ≃* unitaryPSU h 4 :=
    φ.trans (unitaryPSUEquiv h (by norm_num)).symm
  have : Finite (unitaryPSU h 4) := Finite.of_equiv _ psi.toEquiv
  have hXq : CFSG.IsQuasisimple X :=
    Catalog7Std.isQuasisimple_of_model hC hx hXx hXF hX psi fun α hα2 hα1 L' hL' =>
      CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components h hr2 (n := 4)
        (by norm_num) α (orderOf_eq_prime hα2 hα1) 2 Nat.prime_two L' hL'
  have hcore : pPrimeCore 2 X = center X := by
    apply le_antisymm
    · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hXq (pPrimeCore 2 X)
        with h' | h'
      · exact h'
      · exfalso
        have h1 : Nat.card (X ⧸ pPrimeCore 2 X) = 1 := by
          have := Subgroup.index_top (G := X)
          rw [← h'] at this
          exact this
        rw [hcardB] at h1
        have h25 : 25 ≤ (p ^ g) ^ 2 := by nlinarith
        have : 5 * 24 ≤ p ^ g * ((p ^ g) ^ 2 - 1) :=
          Nat.mul_le_mul h5 (by omega)
        omega
    · intro z hz
      have hz' : (QuotientGroup.mk z : X ⧸ pPrimeCore 2 X) ∈ center (X ⧸ pPrimeCore 2 X) := by
        rw [mem_center_iff]
        intro y
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hz) y']
      exact (QuotientGroup.eq_one_iff z).mp
        (OddSelector.Catalog7L3.eq_one_of_mem_center_psl2 hQ3 eB hz')
  have hZodd : Odd (Nat.card (center X)) := by
    rw [← hcore]
    have h' := (pPrimeCore_coprime_card (p := 2) (G := X))
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h')
  let eZ : X ⧸ center X ≃* X ⧸ pPrimeCore 2 X := QuotientGroup.quotientMulEquivOfEq hcore.symm
  have hXmZ : Blueprint.LieModel (X ⧸ center X) .PSL 2 p g :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hXm
  have hXC : CFSG.Assembly.IsComponentOf X (centralizer ({x} : Set H)) := by
    have hsub : (X.subgroupOf (centralizer ({x} : Set H))).IsSubnormal := hX.choose_spec.2.1
    have hq : CFSG.IsQuasisimple (X.subgroupOf (centralizer ({x} : Set H))) :=
      (isQuasisimple_congr (subgroupOfEquivOfLe hXx)).mpr hXq
    exact (isComponentOf_iff_isComponent_subgroupOf hXx).mpr ⟨hq, hsub⟩
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · rw [pow_zero] at h5
      omega
    · exact hg
  have hsX : SmallSource X := Or.inl ⟨p, g, hp, hp2, hg1, h5, hXmZ, hZodd⟩
  obtain ⟨-, -, -, hL₁⟩ := OddSelector.socle_images φ hinj hρW hXF hXC
  have hcj := OddClassSelector.conj_injective hZ
  obtain ⟨hX', hX'map⟩ := OddClassSelector.isComponentOf_comap_conj hcj hL₁
  have hX'eq := comap_conj_map_eq φ hρW hcj hXF
  let eXX' : X ≃* (X.map ρ).comap MulAut.conj :=
    (X.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hX'map.symm).trans
      (((X.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)
  have hsX' : SmallSource ((X.map ρ).comap MulAut.conj) :=
    OddClassSelector.smallSource_of_mulEquiv eXX' hsX
  have hcardrel : ∀ (F₀ : Type) [Field F₀] [Finite F₀], Odd (Nat.card F₀) →
      Nonempty (((X.map ρ).comap MulAut.conj) ⧸ center ((X.map ρ).comap MulAut.conj) ≃*
        GorensteinWalter.PSL2 F₀) → p ^ g = Nat.card F₀ := by
    intro F₀ _ _ hF₀ ⟨eP⟩
    exact eq_card_of_quotient_psl2 hp hp2 hXm hF₀
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans ((centerQuotientCongr eXX').trans eP))
  have hα : ∀ y, ρ x (ρ x y) = y := by
    intro y
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, hx2, map_one, MulAut.one_apply]
  have hρx1 : ρ x ≠ 1 := by
    intro h1
    have hx1 : x = 1 := hinj (h1.trans (map_one ρ).symm)
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := Catalog7U4.exists_lift h hr2 (ρ x) hα
  have hKodd : Odd (Nat.card K) := by
    rw [h.card_eq_sq]
    exact ((h.prime.odd_of_ne_two hr2).pow).pow
  have hk₀odd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hr2).pow
  refine ⟨hcore, hXq, A, ψ, hAu, hψ, ?_⟩
  rcases hcase with ⟨hψA, c₀, hAA⟩ | ⟨hψA, z, hAA⟩
  · obtain ⟨⟨eP⟩, l, Q, hl0, -, hQ, hAQ⟩ := psu4_inner_case h hr2 hρx1 hX' hsX' hAu hψ hψA hAA
    left
    exact ⟨by rw [hcardrel K hKodd ⟨eP⟩, h.card_eq_sq], hψA, Q, l, hl0, hQ, hAQ⟩
  · obtain ⟨-, hcase'⟩ := psu4_anti_case h hr2 hX' hsX' hAu hψ hψA hAA
    rcases hcase' with ⟨-, ⟨eP⟩, hdet, Y, hYp, ⟨φq, hφq⟩, hYX⟩ | ⟨⟨E', _, _, hE', ⟨eP⟩⟩, hno⟩
    · right; right
      refine ⟨by rw [hcardrel _ hk₀odd ⟨eP⟩, h.card_fixedField], hψA, hdet, ?_⟩
      have hYr := le_range_toSesqUnitary h hYp
      let eS := MonoidHom.ofInjective (toSesqUnitary_injective h)
      let φq' : QuaternionGroup 2 →* unitarySU r e K 4 :=
        eS.symm.toMonoidHom.comp ((Subgroup.inclusion hYr).comp φq)
      have hφq' : Function.Injective φq' :=
        eS.symm.injective.comp ((Subgroup.inclusion_injective hYr).comp hφq)
      have hval : ∀ w, EscapingNotOddUnitary.toSesqUnitary h 4 (φq' w) = φq w := by
        intro w
        have h1 := congrArg Subtype.val (eS.apply_symm_apply (Subgroup.inclusion hYr (φq w)))
        exact h1
      set YS := Y.comap (EscapingNotOddUnitary.toSesqUnitary h 4) with hYS
      have hYSmap : YS.map (EscapingNotOddUnitary.toSesqUnitary h 4) = Y :=
        Subgroup.map_comap_eq_self hYr
      have hYSp : ⁅YS, YS⁆ = YS := by
        apply Subgroup.map_injective (toSesqUnitary_injective h)
        rw [Subgroup.map_commutator, hYSmap, hYp]
      have hYSle : YS ≤ ((X.subgroupOf (generalizedFitting H)).map φ.toMonoidHom).comap
          (QuotientGroup.mk' (scal r e K)) := by
        intro y hy
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, ← hX'eq]
        have h1 := hYX _ hy
        rw [← ιU_mk] at h1
        obtain ⟨x', hx', hx'eq⟩ := h1
        rw [← ιU_injective h hx'eq]
        exact hx'
      refine ⟨φq', hφq', fun w => ?_⟩
      have hw : φq' w ∈ YS := by
        rw [hYS, Subgroup.mem_comap, hval]
        exact (φq w).2
      rw [← hYSp] at hw
      exact Subgroup.commutator_mono hYSle hYSle hw
    · right; left
      refine ⟨by rw [hcardrel E' (by rw [hE']; exact hk₀odd.pow) ⟨eP⟩, hE', h.card_fixedField],
        hψA, ?_⟩
      intro Y₁ hY₁p hY₁ψ φq hφq
      have hY₂p : ⁅Y₁.map (EscapingNotOddUnitary.toSesqUnitary h 4),
          Y₁.map (EscapingNotOddUnitary.toSesqUnitary h 4)⁆ =
            Y₁.map (EscapingNotOddUnitary.toSesqUnitary h 4) := by
        rw [← Subgroup.map_commutator, hY₁p]
      have hY₂le : Y₁.map (EscapingNotOddUnitary.toSesqUnitary h 4) ≤
          fixedSubgroup (antiConjA h hAu) := by
        rintro _ ⟨y, hy, rfl⟩
        change antiConjA h hAu (EscapingNotOddUnitary.toSesqUnitary h 4 y) =
          EscapingNotOddUnitary.toSesqUnitary h 4 y
        rw [toSesqUnitary_antiConj h hAu y (ψ y) (hψA y), hY₁ψ y hy]
      let eY := Y₁.equivMapOfInjective _ (toSesqUnitary_injective h)
      exact hno _ hY₂p hY₂le (eY.toMonoidHom.comp φq) (eY.injective.comp hφq)

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB

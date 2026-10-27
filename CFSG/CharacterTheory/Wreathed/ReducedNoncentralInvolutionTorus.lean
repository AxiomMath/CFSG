module

public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionSupport
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearInvolutionClasses
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Wreathed.ReducedInvolution

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
open CFSG.Wreathed.CentralSL2Abelianization CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem weyl_eq_J₀ (F : Type) [Field F] : weyl F = OddFieldTorus.J₀ F := rfl

section Centralizer

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem specialInclusion_mem_centralizer_iff (X : SpecialLinearGroup (Fin 2) F) :
    specialInclusion F b m hm heven X ∈ Subgroup.centralizer {involutionY F b m hm heven} ↔
      X ∈ Subgroup.centralizer {weyl F} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    involutionY]
  have ha : ∀ g : CentralExtension F b m hm heven,
      (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * g =
        g * (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) :=
    fun g => (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven g) (m / 4)).eq
  have key : specialInclusion F b m hm heven X * ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
      specialInclusion F b m hm heven (weyl F)) =
        (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * specialInclusion F b m hm heven
          (X * weyl F) := by
    rw [← mul_assoc, ← ha, mul_assoc, map_mul]
  rw [key, mul_assoc, ← map_mul, mul_right_inj]
  exact (specialInclusion_injective F b m hm heven).eq_iff

theorem range_inf_centralizer :
    (specialInclusion F b m hm heven).range ⊓
        Subgroup.centralizer {involutionY F b m hm heven} =
      (Subgroup.centralizer {weyl F}).map (specialInclusion F b m hm heven) := by
  ext g
  constructor
  · rintro ⟨⟨X, rfl⟩, hX⟩
    exact ⟨X, (specialInclusion_mem_centralizer_iff X).mp hX, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨⟨X, rfl⟩, (specialInclusion_mem_centralizer_iff X).mpr hX⟩

theorem centralizer_involutionY_comm [Fintype F] (hb : ¬ IsSquare b)
    {g g' : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.centralizer {involutionY F b m hm heven})
    (hg' : g' ∈ Subgroup.centralizer {involutionY F b m hm heven}) : g * g' = g' * g := by
  obtain ⟨E, _, _, ⟨basis⟩⟩ := exists_quadratic_extension F b hb
  have h2 := two_ne_zero_of_not_isSquare hb
  have hfix := card_fixed_involutionY (hm := hm) (heven := heven) hb
  have htransport : ∀ (T : Subgroup (CentralExtension F b m hm heven))
      (t : CentralExtension F b m hm heven), IsConj (involutionY F b m hm heven) t →
      Subgroup.centralizer {t} = T → (∀ x ∈ T, ∀ x' ∈ T, x * x' = x' * x) →
      g * g' = g' * g := by
    intro T t hc hT hcomm
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    have hmem : ∀ x ∈ Subgroup.centralizer {involutionY F b m hm heven}, c * x * c⁻¹ ∈ T := by
      intro x hx
      rw [← hT, Subgroup.mem_centralizer_singleton_iff, ← hc]
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      calc c * x * c⁻¹ * (c * involutionY F b m hm heven * c⁻¹)
          = c * (x * involutionY F b m hm heven) * c⁻¹ := by group
        _ = c * (involutionY F b m hm heven * x) * c⁻¹ := by rw [hx]
        _ = c * involutionY F b m hm heven * c⁻¹ * (c * x * c⁻¹) := by group
    have h := hcomm _ (hmem g hg) _ (hmem g' hg')
    have h' : c * (g * g') * c⁻¹ = c * (g' * g) * c⁻¹ := by
      calc c * (g * g') * c⁻¹ = c * g * c⁻¹ * (c * g' * c⁻¹) := by group
        _ = c * g' * c⁻¹ * (c * g * c⁻¹) := h
        _ = c * (g' * g) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  rcases conjugacy_type_exists basis hb (involutionY F b m hm heven) with hA |
      ⟨α, hα, hc⟩ | ⟨t, ht, htA, hc⟩ | ⟨t, ht, htA, hc⟩
  · exact absurd hA (involutionY_not_mem hb)
  · exfalso
    have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_unipotent hα one_ne_zero, hfix] at h1
    by_cases hs : IsSquare (-1 : F)
    · rw [ite_eq_left hs] at h1
      omega
    · rw [ite_eq_right hs] at h1
      omega
  · exact htransport _ t hc (centralizer_splitTorus hb ht htA)
      fun x hx x' hx' => splitTorus_mul_comm F b m hm heven hx hx'
  · obtain ⟨y, hy⟩ : ∃ y : Eˣ, (y : E) * (y : E) ^ Nat.card F = -1 :=
      exists_norm_eq F E basis (-1) |>.imp fun y' hy' => by rw [hy']; simp
    obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
    exact htransport _ t hc (centralizer_nonsplitTorus y hy h2 hb ht htA)
      fun x hx x' hx' => nonsplitTorus_mul_comm z hz hx hx'

theorem fieldSL_eq_of_pow_two_pow [Finite F] (h2 : (2 : F) ≠ 0) {σ : F ≃+* F}
    (hσ : Odd (orderOf σ)) {t : SpecialLinearGroup (Fin 2) F}
    (ht : t ∈ Subgroup.centralizer {weyl F}) {s : ℕ} (hts : t ^ 2 ^ s = 1) :
    fieldSL F σ t = t := by
  have : IsCyclic (OddFieldTorus.torus F) := OddFieldTorus.torus_isCyclic h2
  let ψ : OddFieldTorus.torus F →* OddFieldTorus.torus F :=
    ((fieldSL F σ).toMonoidHom.comp (OddFieldTorus.torus F).subtype).codRestrict _
      fun g => OddFieldTorus.fieldAction_mem_torus σ g.2
  have hiter : ∀ (j : ℕ) (g : OddFieldTorus.torus F),
      ((ψ^[j] g : OddFieldTorus.torus F) : SpecialLinearGroup (Fin 2) F) =
        fieldSL F (σ ^ j) g := by
    intro j
    induction j with
    | zero =>
      intro g
      rw [pow_zero, fieldSL_one]
      rfl
    | succ j ih =>
      intro g
      rw [Function.iterate_succ_apply', pow_succ', fieldSL_mul, MulAut.mul_apply, ← ih]
      rfl
  have hψ : ∀ g, ψ^[orderOf σ] g = g := fun g => Subtype.ext (by
    rw [hiter, pow_orderOf_eq_one, fieldSL_one]
    rfl)
  have h := fix_of_isCyclic ψ hσ hψ (t := ⟨t, ht⟩) (s := s) (Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hts))
  exact congrArg Subtype.val h

end Centralizer

section Field

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem fieldAction_mem_centralizer (σ : Sigma) {g : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.centralizer {involutionY F b m hm heven}) :
    fieldAction F b m hm heven Sigma hSigma σ g ∈
      Subgroup.centralizer {involutionY F b m hm heven} := by
  have hy := fieldAction_involutionY (m := m) (hm := hm) (heven := heven) (hSigma := hSigma) σ
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  calc fieldAction F b m hm heven Sigma hSigma σ g * involutionY F b m hm heven
      = fieldAction F b m hm heven Sigma hSigma σ (g * involutionY F b m hm heven) := by
        rw [map_mul, hy]
    _ = fieldAction F b m hm heven Sigma hSigma σ (involutionY F b m hm heven * g) := by
        rw [hg]
    _ = involutionY F b m hm heven * fieldAction F b m hm heven Sigma hSigma σ g := by
        rw [map_mul, hy]

theorem baseResidue_fieldAction (σ : Sigma) (g : CentralExtension F b m hm heven) :
    baseResidue F b m hm heven (fieldAction F b m hm heven Sigma hSigma σ g) =
      baseResidue F b m hm heven g := by
  obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
  rw [fieldAction_quotientClass, baseResidue_quotientClass, baseResidue_quotientClass]

theorem fieldAction_eq_of_pow_two_pow [Fintype F] (hb : ¬ IsSquare b)
    (hd : Odd (Nat.card Sigma)) (σ : Sigma) {g : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.centralizer {involutionY F b m hm heven}) {s : ℕ}
    (hgs : g ^ 2 ^ s = 1) : fieldAction F b m hm heven Sigma hSigma σ g = g := by
  have h2 := two_ne_zero_of_not_isSquare hb
  have hτg := fieldAction_mem_centralizer (hSigma := hSigma) σ hg
  obtain ⟨c, hc⟩ : ∃ c, c = fieldAction F b m hm heven Sigma hSigma σ g * g⁻¹ := ⟨_, rfl⟩
  have hcD : c ∈ Subgroup.centralizer {involutionY F b m hm heven} := by
    rw [hc]
    exact Subgroup.mul_mem _ hτg (Subgroup.inv_mem _ hg)
  have hcM : c ∈ (specialInclusion F b m hm heven).range := by
    rw [← baseResidue_ker, MonoidHom.mem_ker, hc, map_mul, map_inv, baseResidue_fieldAction,
      mul_inv_cancel]
  obtain ⟨t, ht⟩ := hcM
  have htT : t ∈ Subgroup.centralizer {weyl F} := by
    rw [← specialInclusion_mem_centralizer_iff, ht]
    exact hcD
  have hcomm : Commute (fieldAction F b m hm heven Sigma hSigma σ g) g⁻¹ :=
    centralizer_involutionY_comm hb hτg (Subgroup.inv_mem _ hg)
  have hcs : c ^ 2 ^ s = 1 := by
    rw [hc, hcomm.mul_pow, ← map_pow, hgs, map_one, one_mul, inv_pow, hgs, inv_one]
  have hts : t ^ 2 ^ s = 1 := by
    apply specialInclusion_injective F b m hm heven
    rw [map_pow, ht, hcs, map_one]
  have hσodd : Odd (orderOf (σ : F ≃+* F)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hd (orderOf_dvd_natCard σ)
  have hτc : fieldAction F b m hm heven Sigma hSigma σ c = c := by
    rw [← ht, fieldAction_specialInclusion, fieldSL_eq_of_pow_two_pow h2 hσodd htT hts]
  have hτg' : fieldAction F b m hm heven Sigma hSigma σ g = c * g := by
    rw [hc, inv_mul_cancel_right]
  have hpow : ∀ k : ℕ, (fieldAction F b m hm heven Sigma hSigma σ ^ k) g = c ^ k * g := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, one_mul, MulAut.one_apply]
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hτc, hτg', pow_succ, mul_assoc]
  have hce : c ^ orderOf σ = 1 := by
    have h := hpow (orderOf σ)
    rw [← map_pow, pow_orderOf_eq_one, map_one, MulAut.one_apply] at h
    exact mul_right_cancel (h.symm.trans (one_mul g).symm)
  have hcop : (2 ^ s).Coprime (orderOf σ) :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr (Odd.of_dvd_nat hd (orderOf_dvd_natCard σ)))
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hcs, hce⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
  rw [hτg', hc1, one_mul]

end Field

end CFSG.Wreathed.ReducedInvolution

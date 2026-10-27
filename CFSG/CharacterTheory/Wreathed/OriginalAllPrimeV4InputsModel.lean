module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersLayerElements
public import CFSG.GroupTheory.ABGDGroups.LinearSignalizers
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeV4InputsLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsFrobenius

public section

namespace CFSG.Wreathed.OriginalAllPrime.V4InputsW

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.OriginalAllPrime.IVFacts

section Groups

variable {G : Type*} [Group G]

theorem le_of_index_eq_two_of_odd {H K : Subgroup G} (hH : H.index = 2)
    (hK : Odd (Nat.card K)) : K ≤ H := by
  intro k hk
  have hord : Odd (orderOf k) := hK.of_dvd_nat (by
    rw [← Subgroup.orderOf_mk k hk]
    exact orderOf_dvd_natCard _)
  obtain ⟨j, hj⟩ := hord
  have hk' : k = (k ^ (j + 1)) ^ 2 := by
    rw [← pow_mul, show (j + 1) * 2 = orderOf k + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hk']
  exact Subgroup.sq_mem_of_index_two hH _

theorem eq_one_of_mem_zpowers_of_odd {a c : G} {n k : ℕ} (ha : a ^ 2 ^ n = 1)
    (hc : c ∈ Subgroup.zpowers a) (hk : Odd k) (hck : c ^ k = 1) : c = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h1 : (a ^ j) ^ 2 ^ n = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ha,
      _root_.one_zpow]
  have hcop : Nat.Coprime (2 ^ n) k := (Nat.coprime_two_left.mpr hk).pow_left n
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one hck))

theorem pow_conj_eq_of_conj_eq {g y c : G} (hcg : c * g = g * c) (h : g * y * g⁻¹ = c * y)
    (j : ℕ) : g ^ j * y * (g ^ j)⁻¹ = c ^ j * y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcj : c ^ j * g = g * c ^ j := (Commute.pow_left hcg j).eq
    calc g ^ (j + 1) * y * (g ^ (j + 1))⁻¹ = g * (g ^ j * y * (g ^ j)⁻¹) * g⁻¹ := by group
      _ = g * c ^ j * y * g⁻¹ := by rw [ih]; group
      _ = c ^ j * (g * y * g⁻¹) := by rw [← hcj]; group
      _ = c ^ (j + 1) * y := by rw [h, pow_succ, mul_assoc]

theorem commute_of_conj_eq_mul {g y a c : G} {n : ℕ} (ha : a ^ 2 ^ n = 1)
    (hc : c ∈ Subgroup.zpowers a) (hcg : c * g = g * c) (hg : Odd (orderOf g))
    (h : g * y * g⁻¹ = c * y) : g * y = y * g := by
  have h1 := pow_conj_eq_of_conj_eq hcg h (orderOf g)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hc1 : c ^ orderOf g = 1 := by
    have h2 := congrArg (· * y⁻¹) h1
    simpa using h2.symm
  have hc' : c = 1 := eq_one_of_mem_zpowers_of_odd ha hc hg hc1
  rw [hc', one_mul] at h
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [h]

end Groups

section Matrix

variable {F : Type} [Field F]

theorem toGL_coe (X : SpecialLinearGroup (Fin 2) F) :
    ((SpecialLinearGroup.toGL X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = X := rfl

theorem conj_mul_eq_scalar {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    SpecialLinearGroup.toGL X * G * (SpecialLinearGroup.toGL X)⁻¹ * G =
      GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det G) := by
  obtain ⟨h1, h2⟩ := entries_of_conj hX
  have hs := sq_add_sq_of_conj hX
  obtain ⟨k1, k2⟩ := entries_of_commute_weyl hG
  have hinv : ((SpecialLinearGroup.toGL X)⁻¹ : GL (Fin 2) F) = SpecialLinearGroup.toGL X⁻¹ :=
    (map_inv _ _).symm
  apply Units.ext
  rw [hinv]
  simp only [Units.val_mul, toGL_coe, SL_coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply_two, h1, h2, k1, k2, GeneralLinearGroup.scalar, Matrix.det_fin_two] <;>
    first
    | ring1
    | linear_combination (-(G.val 0 0 * G.val 0 0 + G.val 1 0 * G.val 1 0)) * hs

theorem mk_conj_eq_inv {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL X) * ProjGenLinGroup.mk G *
        (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X))⁻¹ = (ProjGenLinGroup.mk G)⁻¹ := by
  have h := congrArg ProjGenLinGroup.mk (conj_mul_eq_scalar hX hG)
  rw [ProjGenLinGroup.mk_scalar, map_mul, map_mul, map_mul, map_inv] at h
  exact eq_inv_of_mul_eq_one_left h

theorem mul_weyl_eq {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) :
    X * weyl F = minusIdentity F * weyl F * X := by
  rw [← hX, inv_mul_cancel_right]

theorem mul_weyl_ne {X : SpecialLinearGroup (Fin 2) F} (hF : ringChar F ≠ 2)
    (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F) : X * weyl F ≠ weyl F * X := by
  intro h
  rw [mul_weyl_eq hX, mul_assoc] at h
  exact minusIdentity_ne_one F hF (mul_eq_right.mp h)

theorem toPGL_eq_toPGL_iff {Z Z' : SpecialLinearGroup (Fin 2) F} :
    SpecialLinearGroup.toPGL Z = SpecialLinearGroup.toPGL Z' ↔
      Z⁻¹ * Z' ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [← SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem commute_of_toPGL_eq_one {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : SpecialLinearGroup.toPGL Z = 1) (Z' : SpecialLinearGroup (Fin 2) F) :
    Z * Z' = Z' * Z := by
  have h : Z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [← SpecialLinearGroup.toPGL_ker]
    exact hZ
  exact (Subgroup.mem_center_iff.mp h Z').symm

end Matrix

section Model

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem cyclicGenerator_sq_pow_m : (cyclicGenerator F b m hm heven ^ 2) ^ m = 1 := by
  rw [pow_right_comm, cyclicGenerator_pow_m, ← map_pow, minusIdentity_square,
    map_one]

theorem commute_yV_of_projectiveMap (hb : ¬ IsSquare b) {n : ℕ} (hmn : m = 2 ^ n)
    {g : CentralExtension F b m hm heven} (hg : Odd (orderOf g))
    (hκ : projectiveMap F b m hm heven g * projectiveMap F b m hm heven (yV b m hm heven) =
      projectiveMap F b m hm heven (yV b m hm heven) * projectiveMap F b m hm heven g) :
    g * yV b m hm heven = yV b m hm heven * g := by
  set y := yV b m hm heven
  set c := g * y * g⁻¹ * y⁻¹ with hcdef
  have hc : c ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
    rw [← projectiveMap_ker F b m hm heven hb, MonoidHom.mem_ker, hcdef, map_mul, map_mul,
      map_mul, map_inv, map_inv, hκ]
    group
  have hcg : c * g = g * c := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hj]
    exact ((Commute.zpow_left (commute_cyclicGenerator_sq b m hm heven g) j) : _)
  have ha : (cyclicGenerator F b m hm heven ^ 2) ^ 2 ^ n = 1 := by
    rw [← hmn]
    exact cyclicGenerator_sq_pow_m
  exact commute_of_conj_eq_mul ha hc hcg hg (by rw [hcdef]; group)

theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  apply h2
  have h' := ringChar.Nat.cast_ringChar (R := F)
  rw [h] at h'
  exact_mod_cast h'

theorem le_modelC_of_odd
    [Finite F] (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) {n : ℕ} (hmn : m = 2 ^ n) (h4 : 4 ∣ m)
    {Y : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hY : Odd (Nat.card Y))
    (hyY : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (Y : Set _))
    {X : SpecialLinearGroup (Fin 2) F} (hX : X * weyl F * X⁻¹ = minusIdentity F * weyl F)
    (hXY : iota b m hm heven Sigma hSigma X ∈ Subgroup.normalizer (Y : Set _))
    {v : CentralExtension F b m hm heven} (hv : v * v = yV b m hm heven)
    (hvY : (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      Subgroup.normalizer (Y : Set _)) :
    Y ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma := by
  classical
  have hF2 := ringChar_ne_two_of_two_ne_zero h2
  set κ := projectiveMap F b m hm heven with hκdef
  set ι₀ : CentralExtension F b m hm heven →* SemilinearExtension F b m hm heven Sigma hSigma :=
    SemidirectProduct.inl with hι₀
  set Y₁ := Y.comap ι₀ with hY₁def
  set Ys := Y₁.map κ with hYsdef
  have hY₁ : Odd (Nat.card Y₁) :=
    hY.of_dvd_nat (Subgroup.card_comap_dvd_of_injective Y ι₀ SemidirectProduct.inl_injective)
  have hYs : Odd (Nat.card Ys) := hY₁.of_dvd_nat (Subgroup.card_map_dvd Y₁ κ)
  have hYsJ : Ys ≤ Matrix.ProjectiveSpecialLinearGroup.toPGL.range :=
    le_of_index_eq_two_of_odd (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF) hYs
  have hnorm : ∀ g : CentralExtension F b m hm heven,
      ι₀ g ∈ Subgroup.normalizer (Y : Set _) → κ g ∈ Subgroup.normalizer (Ys : Set _) :=
    fun g hg => Subgroup.le_normalizer_map κ ⟨g, Subgroup.le_normalizer_comap ι₀ hg, rfl⟩
  set ι : ProjGenLinGroup (Fin 2) F := SpecialLinearGroup.toPGL (weyl F) with hιdef
  set δ : ProjGenLinGroup (Fin 2) F := SpecialLinearGroup.toPGL X with hδdef
  set γ := κ v with hγdef
  have hκy : κ (yV b m hm heven) = ι := projectiveMap_involutionY hb
  have hκX : κ (specialInclusion F b m hm heven X) = δ :=
    projectiveMap_specialInclusion F b m hm heven X
  have hXJ := mul_weyl_ne hF2 hX
  have hmid : SpecialLinearGroup.toPGL (minusIdentity F) = 1 := by
    rw [← MonoidHom.mem_ker, SpecialLinearGroup.toPGL_ker]
    exact minusIdentity_mem_center F
  have hι2 : ι * ι = 1 := by
    have hww : weyl F * weyl F = minusIdentity F := by
      apply Subtype.ext
      rw [SL_coe_mul, weyl_mul_weyl, minusIdentity_coe]
    rw [hιdef, ← map_mul, hww, hmid]
  have hδ2 : δ * δ = 1 := by
    have hXX : X * X = minusIdentity F := by
      apply Subtype.ext
      rw [SL_coe_mul, mul_self_of_conj hX, minusIdentity_coe]
    rw [hδdef, ← map_mul, hXX, hmid]
  have hι1 : ι ≠ 1 := fun h => hXJ (commute_of_toPGL_eq_one h X).symm
  have hδ1 : δ ≠ 1 := fun h => hXJ (commute_of_toPGL_eq_one h (weyl F))
  have hιδ : ι ≠ δ := by
    intro h
    have hz := toPGL_eq_toPGL_iff.mp h
    apply hXJ
    have hzc := Subgroup.mem_center_iff.mp hz (weyl F)
    calc X * weyl F = weyl F * ((weyl F)⁻¹ * X) * weyl F := by group
      _ = weyl F * (weyl F * ((weyl F)⁻¹ * X)) := by rw [mul_assoc, ← hzc]
      _ = weyl F * X := by group
  have hcomm : Commute ι δ := by
    change SpecialLinearGroup.toPGL (weyl F) * SpecialLinearGroup.toPGL X =
      SpecialLinearGroup.toPGL X * SpecialLinearGroup.toPGL (weyl F)
    rw [← map_mul, ← map_mul, mul_weyl_eq hX]
    simp only [map_mul, hmid, one_mul]
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions ι δ hι2 hδ2 hcomm with hVdef
  have hV : IsKleinFour V := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    ι δ hι2 hδ2 hι1 hδ1 hιδ hcomm
  have hιN : ι ∈ Subgroup.normalizer (Ys : Set _) := by
    rw [← hκy]
    exact hnorm _ hyY
  have hδN : δ ∈ Subgroup.normalizer (Ys : Set _) := by
    rw [← hκX]
    exact hnorm _ hXY
  have hγN : γ ∈ Subgroup.normalizer (Ys : Set _) := hnorm v hvY
  have hVN : V ≤ Subgroup.normalizer (Ys : Set _) := by
    intro x hx
    change x ∈ ({ι * δ, ι, δ, 1} : Set _) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ hιN hδN
    · exact hιN
    · exact hδN
    · exact Subgroup.one_mem _
  obtain ⟨x, hxV, hx1, hYsx⟩ := CFSG.ABGDGroups.pgl2_exists_le_centralizer_of_odd hF hYsJ hYs hV hVN
  obtain ⟨Gc, hGc⟩ := exists_projectiveMap_eq v
  have hvC : v ∈ Subgroup.centralizer {involutionY F b m hm heven} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change v * yV b m hm heven = yV b m hm heven * v
    rw [← hv, mul_assoc]
  have hGcomm := (mem_centralizer_involutionY_iff hGc).mp hvC
  have hγι : γ * γ = ι := by rw [hγdef, ← map_mul, hv, hκy]
  have hδγ : δ * γ * δ⁻¹ = γ⁻¹ := by
    rw [hγdef, hGc]
    exact mk_conj_eq_inv hX hGcomm
  have hγδ : γ * δ * γ⁻¹ = ι * δ := by
    have h1 : δ * γ⁻¹ = γ * δ := by
      calc δ * γ⁻¹ = (δ * γ * δ⁻¹)⁻¹ * δ := by group
        _ = γ * δ := by rw [hδγ, inv_inv]
    calc γ * δ * γ⁻¹ = γ * (δ * γ⁻¹) := by group
      _ = γ * (γ * δ) := by rw [h1]
      _ = ι * δ := by rw [← mul_assoc, hγι]
  have hγιδ : γ * (ι * δ) * γ⁻¹ = δ := by
    have h1 : γ * ι * γ⁻¹ = ι := by rw [← hγι]; group
    calc γ * (ι * δ) * γ⁻¹ = (γ * ι * γ⁻¹) * (γ * δ * γ⁻¹) := by group
      _ = δ := by rw [h1, hγδ, ← mul_assoc, hι2, one_mul]
  have hconj : ∀ z, Ys ≤ Subgroup.centralizer {z} → Ys ≤ Subgroup.centralizer {γ * z * γ⁻¹} := by
    intro z hz y hy
    have hy' : γ⁻¹ * y * γ ∈ Ys := (Subgroup.mem_normalizer_iff''.mp hγN y).mp hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hz hy')
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (γ * z * γ⁻¹) = γ * ((γ⁻¹ * y * γ) * z) * γ⁻¹ := by group
      _ = γ * (z * (γ⁻¹ * y * γ)) * γ⁻¹ := by rw [h1]
      _ = γ * z * γ⁻¹ * y := by group
  have hmul : ∀ z z', Ys ≤ Subgroup.centralizer {z} → Ys ≤ Subgroup.centralizer {z'} →
      Ys ≤ Subgroup.centralizer {z * z'} := by
    intro z z' hz hz' y hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hz hy)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hz' hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * (z * z') = (y * z) * z' := by group
      _ = z * (y * z') := by rw [h1, mul_assoc]
      _ = z * z' * y := by rw [h2, mul_assoc]
  have hδι : ι = (ι * δ) * δ := by rw [mul_assoc, hδ2, mul_one]
  have hYsι : Ys ≤ Subgroup.centralizer {ι} := by
    change x ∈ ({ι * δ, ι, δ, 1} : Set _) at hxV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxV
    rcases hxV with rfl | rfl | rfl | rfl
    · have h1 := hconj _ hYsx
      rw [hγιδ] at h1
      rw [hδι]
      exact hmul _ _ hYsx h1
    · exact hYsx
    · have h1 := hconj _ hYsx
      rw [hγδ] at h1
      rw [hδι]
      exact hmul _ _ h1 hYsx
    · exact absurd rfl hx1
  have hY₁C : ∀ g ∈ Y₁, g * yV b m hm heven = yV b m hm heven * g := by
    intro g hg
    have hgodd : Odd (orderOf g) := hY₁.of_dvd_nat (by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _)
    have hκg := Subgroup.mem_centralizer_singleton_iff.mp (hYsι ⟨g, hg, rfl⟩)
    exact commute_yV_of_projectiveMap hb hmn hgodd (by rw [hκy]; exact hκg)
  intro g hg
  set y0 := ModelSignalizers.modelY b m hm heven Sigma hSigma with hy0
  have hy0sq : y0 * y0 = 1 := ModelSignalizers.modelY_mul_self h4
  have hy0inv : y0⁻¹ = y0 := inv_eq_of_mul_eq_one_right hy0sq
  have hw1 : g⁻¹ * (y0 * g * y0⁻¹) ∈ Y :=
    Y.mul_mem (Y.inv_mem hg) ((Subgroup.mem_normalizer_iff.mp hyY g).mp hg)
  have hy0B : y0 ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma := ⟨yV b m hm heven, rfl⟩
  have hw2 : g⁻¹ * (y0 * g * y0⁻¹) ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma := by
    have h1 : g⁻¹ * (y0 * g * y0⁻¹) = (g⁻¹ * y0 * g⁻¹⁻¹) * y0⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ ((IsWModel.modelBase_normal).conj_mem _ hy0B _)
      (Subgroup.inv_mem _ hy0B)
  obtain ⟨w, hw⟩ := hw2
  have hwY₁ : w ∈ Y₁ := by
    change ι₀ w ∈ Y
    rw [show ι₀ w = SemidirectProduct.inl w from rfl, hw]
    exact hw1
  have hwy : ι₀ w * y0 = y0 * ι₀ w := by
    rw [hy0, modelY_eq_inl_yV, ← map_mul, ← map_mul, hY₁C w hwY₁]
  set k := g⁻¹ * (y0 * g * y0⁻¹) with hkdef
  have hk : ι₀ w = k := hw
  have hkinv : y0 * k * y0⁻¹ = k⁻¹ := by
    rw [hkdef, hy0inv]
    calc y0 * (g⁻¹ * (y0 * g * y0)) * y0 = y0 * g⁻¹ * y0 * g * (y0 * y0) := by
          simp only [mul_assoc]
      _ = (g⁻¹ * (y0 * g * y0))⁻¹ := by
          rw [hy0sq, mul_one]
          simp only [_root_.mul_inv_rev, inv_inv, hy0inv, mul_assoc]
  have hk1 : k = 1 := by
    have hky : k * y0 = y0 * k := by rw [← hk]; exact hwy
    have hkk : k * k = 1 := by
      have h1 : y0 * k * y0⁻¹ = k := by rw [← hky, mul_inv_cancel_right]
      rw [hkinv] at h1
      calc k * k = k * k⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel k
    have hkodd : Odd (orderOf k) := hY.of_dvd_nat (by
      rw [← Subgroup.orderOf_mk k hw1]
      exact orderOf_dvd_natCard _)
    have hk2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hkk)
    rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hkodd
      exact absurd hkodd (by decide)
  rw [hkdef] at hk1
  rw [ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff]
  have h1 : y0 * g * y0⁻¹ = g := by
    have := congrArg (g * ·) hk1
    simpa [mul_assoc] using this
  calc g * y0 = y0 * g * y0⁻¹ * y0 := by rw [h1]
    _ = y0 * g := by group

theorem le_modelC_of_isPGroup
    [Finite F] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    {K : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hK : Odd (Nat.card K))
    (hKM : K ≤ ModelSignalizers.modelLayer b m hm heven Sigma hSigma)
    (hyK : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (K : Set _))
    {w : SpecialLinearGroup (Fin 2) F} (hwT : w ∈ torus F) (hw1 : w ≠ 1)
    (hwodd : Odd (orderOf w)) (hwK : iota b m hm heven Sigma hSigma w ∈ K)
    {Y : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hYK : Y ≤ K) {r : ℕ}
    (hr : r.Prime) (hrp : r ≠ p) (hY : IsPGroup r Y)
    (hyY : ModelSignalizers.modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (Y : Set _)) :
    Y ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP F p := charP_of_card_eq_pow hp hcard
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hpF : p ∣ Nat.card F := by rw [hcard]; exact dvd_pow_self p (by omega)
  have hw2 : w ≠ minusIdentity F := by
    rintro rfl
    rw [minusIdentity_order F hF2] at hwodd
    exact absurd hwodd (by decide)
  set ι := iota b m hm heven Sigma hSigma with hιdef
  have hιinj : Function.Injective ι := iota_injective b m hm heven Sigma hSigma
  set K' := K.comap ι with hK'def
  set Y' := Y.comap ι with hY'def
  have hY'K' : Y' ≤ K' := Subgroup.comap_mono hYK
  set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) with hπdef
  have hK' : Odd (Nat.card K') := hK.of_dvd_nat (Subgroup.card_comap_dvd_of_injective K ι hιinj)
  have hcen : ∀ x ∈ K', x ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) → x = 1 := by
    intro x hx hxc
    rcases (mem_center_iff_eq_one_or_minusIdentity F x).mp hxc with h | h
    · exact h
    · exfalso
      have hord : orderOf x ∣ Nat.card K' := by
        rw [← Subgroup.orderOf_mk x hx]
        exact orderOf_dvd_natCard _
      rw [h, minusIdentity_order F hF2] at hord
      exact (Nat.not_even_iff_odd.mpr hK') (even_iff_two_dvd.mpr hord)
  have hπeq : ∀ x ∈ K', π x = 1 → x = 1 := by
    intro x hx h1
    apply hcen x hx
    rw [← QuotientGroup.ker_mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))]
    exact h1
  set Ks := K'.map π with hKsdef
  have hKs : Odd (Nat.card Ks) := hK'.of_dvd_nat (Subgroup.card_map_dvd K' π)
  have hJK : ∀ x ∈ K', weyl F * x * (weyl F)⁻¹ ∈ K' := by
    intro x hx
    change ι (weyl F * x * (weyl F)⁻¹) ∈ K
    rw [hιdef, ← modelY_conj_iota]
    exact (Subgroup.mem_normalizer_iff.mp hyK _).mp hx
  have hJY : ∀ x ∈ Y', weyl F * x * (weyl F)⁻¹ ∈ Y' := by
    intro x hx
    change ι (weyl F * x * (weyl F)⁻¹) ∈ Y
    rw [hιdef, ← modelY_conj_iota]
    exact (Subgroup.mem_normalizer_iff.mp hyY _).mp hx
  have hYmem : ∀ g ∈ Y, ∃ y ∈ Y', ι y = g := by
    intro g hg
    have hgM := hKM (hYK hg)
    rw [modelLayer_eq_range] at hgM
    obtain ⟨y, hy⟩ := hgM
    refine ⟨y, ?_, hy⟩
    change ι y ∈ Y
    rw [hy]
    exact hg
  suffices hsuff : ∀ y ∈ Y', y * weyl F = weyl F * y by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := hYmem g hg
    exact (inl_specialInclusion_mem_modelC_iff y).mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hsuff y hy))
  rcases CFSG.ABGDGroups.psl2_odd_isCyclic_or_exists_pSubgroup hcard hp2 Ks hKs with
    hcyc | ⟨N, hNK, hN1, hNp, hNall⟩
  ·
    have hcomm : ∀ x ∈ K', ∀ y ∈ K', x * y = y * x := by
      intro x hx y hy
      have h1 : π x * π y = π y * π x :=
        congrArg Subtype.val (IsCyclic.commGroup.mul_comm (⟨π x, x, hx, rfl⟩ : Ks)
          ⟨π y, y, hy, rfl⟩)
      have h2 : (y * x)⁻¹ * (x * y) ∈ K' :=
        K'.mul_mem (K'.inv_mem (K'.mul_mem hy hx)) (K'.mul_mem hx hy)
      have h3 := hπeq _ h2 (by rw [map_mul, map_inv, map_mul, map_mul, h1, inv_mul_cancel])
      exact inv_mul_eq_one.mp h3 |>.symm
    intro y hy
    have hwK' : w ∈ K' := hwK
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (mem_torus_of_commute hwT hw1 hw2 (hcomm y (hY'K' hy) w hwK'))
  ·
    set P := K' ⊓ N.comap π with hPdef
    have hPp : IsPGroup p P := by
      intro x
      obtain ⟨k, hk⟩ := hNp ⟨π x, x.2.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : π ((x : SpecialLinearGroup (Fin 2) F) ^ p ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact hπeq _ (K'.pow_mem x.2.1 _) h1
    have hP1 : P ≠ ⊥ := by
      obtain ⟨n, hn, hn1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN1
      obtain ⟨x, hx, rfl⟩ := hNK hn
      refine fun hbot => hn1 ?_
      have hxP : x ∈ P := ⟨hx, hn⟩
      rw [hbot] at hxP
      rw [(Subgroup.mem_bot.mp hxP), map_one]
    have hPnorm : ∀ g, (∀ x ∈ K', g * x * g⁻¹ ∈ K') →
        g ∈ Subgroup.normalizer (P : Set (SpecialLinearGroup (Fin 2) F)) := by
      intro g hg
      apply mem_normalizer_of_conj_mem
      intro x hx
      refine ⟨hg x hx.1, ?_⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hNp) ⟨π x, hx.2⟩
      have hk' : orderOf (π x) = p ^ k := (Subgroup.orderOf_coe _).trans hk
      apply hNall (π (g * x * g⁻¹)) ⟨_, hg x hx.1, rfl⟩ k
      rw [map_mul, map_mul, map_inv, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk'
    have hJN := hPnorm (weyl F) hJK
    intro y hy
    have hyN := hPnorm y (fun x hx => K'.mul_mem (K'.mul_mem (hY'K' hy) hx)
      (K'.inv_mem (hY'K' hy)))
    have hc := commutator_pow_char_eq_one_of_mem_normalizer hpF hPp hP1 hyN hJN
    set c := y * weyl F * y⁻¹ * (weyl F)⁻¹ with hcdef
    have hcY : c ∈ Y' := by
      have h1 : c = y * (weyl F * y⁻¹ * (weyl F)⁻¹) := by rw [hcdef]; group
      rw [h1]
      exact Y'.mul_mem hy (hJY _ (Y'.inv_mem hy))
    obtain ⟨k, hk⟩ := (hY.comap_of_injective ι hιinj) ⟨c, hcY⟩
    have hck : c ^ r ^ k = 1 := congrArg Subtype.val hk
    have hcop : Nat.Coprime p (r ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp hr).mpr hrp.symm)
    have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hc) (orderOf_dvd_of_pow_eq_one hck))
    rw [hcdef] at hc1
    calc y * weyl F = y * weyl F * y⁻¹ * (weyl F)⁻¹ * (weyl F * y) := by group
      _ = weyl F * y := by rw [hc1, one_mul]

end Model

end CFSG.Wreathed.OriginalAllPrime.V4InputsW

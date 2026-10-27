module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearInvolutions
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizers
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Wreathed.OriginalAllPrime.Sec11W

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2

theorem semidirect_conj_inl_eq {N K : Type*} [Group N] [Group K] {φ : K →* MulAut N}
    (h : N ⋊[φ] K) (x : N) :
    h * SemidirectProduct.inl x * h⁻¹ =
      SemidirectProduct.inl (h.left * φ h.right x * h.left⁻¹) := by
  apply SemidirectProduct.ext <;> simp [mul_assoc]

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem conj_inl_specialInclusion_eq {h : SemilinearExtension F b m hm heven Sigma hSigma}
    {G : GL (Fin 2) F} (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G)
    (A : SpecialLinearGroup (Fin 2) F) :
    h * SemidirectProduct.inl (specialInclusion F b m hm heven A) * h⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven
        (matrixConjugation F G (fieldSL F h.right A))) := by
  rw [semidirect_conj_inl_eq, fieldAction_specialInclusion,
    conj_specialInclusion hG (matrixConjugation_toGL F G _)]

theorem exists_eq_of_commute [Finite F] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f)
    (hb : ¬ IsSquare b) {U : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hU : Nat.card U = Nat.card F) {x : SemilinearExtension F b m hm heven Sigma hSigma}
    (hx : ∀ A ∈ U, x * SemidirectProduct.inl (specialInclusion F b m hm heven A) =
      SemidirectProduct.inl (specialInclusion F b m hm heven A) * x) :
    ∃ A₀ ∈ U, ∃ k : ℤ, x = SemidirectProduct.inl
      ((cyclicGenerator F b m hm heven ^ 2) ^ k * specialInclusion F b m hm heven A₀) := by
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven x.left)
  have hcond : ∀ A ∈ U, G * SpecialLinearGroup.toGL
      (SpecialLinearGroup.map (x.right : F ≃+* F).toRingHom A) * G⁻¹ =
        SpecialLinearGroup.toGL A := by
    intro A hA
    have h1 := conj_inl_specialInclusion_eq hG.symm A
    rw [hx A hA, mul_inv_cancel_right] at h1
    have h2 := CentralSL2Abelianization.specialInclusion_injective F b m hm heven
      (SemidirectProduct.inl_injective h1)
    have h3 := congrArg SpecialLinearGroup.toGL h2
    rw [matrixConjugation_toGL] at h3
    exact h3.symm
  obtain ⟨hσ, A₀, hA₀, c, hGc⟩ :=
    CFSG.SL2MinimalFaithful.semilinear_centralizer_sylow hp hcard hU G _ hcond
  have hright : x.right = 1 := Subtype.ext hσ
  have hκ : x.left * (specialInclusion F b m hm heven A₀)⁻¹ ∈
      (projectiveMap F b m hm heven).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hG, projectiveMap_specialInclusion, hGc,
      map_mul, ProjGenLinGroup.mk_scalar, one_mul, mul_inv_cancel]
  rw [projectiveMap_ker F b m hm heven hb] at hκ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hκ
  refine ⟨A₀, hA₀, k, SemidirectProduct.ext ?_ ?_⟩
  · rw [SemidirectProduct.left_inl, hk, inv_mul_cancel_right]
  · rw [SemidirectProduct.right_inl, hright]

@[expose] noncomputable def layerInclusion :
    SpecialLinearGroup (Fin 2) F →* SemilinearExtension F b m hm heven Sigma hSigma :=
  SemidirectProduct.inl.comp (specialInclusion F b m hm heven)

theorem layerInclusion_injective :
    Function.Injective (layerInclusion (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
      (hSigma := hSigma)) :=
  SemidirectProduct.inl_injective.comp
    (CentralSL2Abelianization.specialInclusion_injective F b m hm heven)

theorem range_layerInclusion :
    (layerInclusion (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
      (hSigma := hSigma)).range = ModelSignalizers.modelLayer b m hm heven Sigma hSigma :=
  MonoidHom.range_comp _ _

theorem card_comap_layerInclusion {P : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hPM : P ≤ ModelSignalizers.modelLayer b m hm heven Sigma hSigma) :
    Nat.card (P.comap layerInclusion) = Nat.card P := by
  have hmap : (P.comap layerInclusion).map layerInclusion = P :=
    Subgroup.map_comap_eq_self (by rwa [range_layerInclusion])
  rw [← Subgroup.card_map_of_injective layerInclusion_injective, hmap]

theorem isCyclic_of_le_centralizer [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ f) (hb : ¬ IsSquare b) (hmp : Nat.Coprime m p)
    {P : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hPM : P ≤ ModelSignalizers.modelLayer b m hm heven Sigma hSigma)
    (hP : Nat.card P = Nat.card F)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : IsPGroup 2 X) (hXP : X ≤ Subgroup.centralizer (P : Set _)) : IsCyclic X := by
  have hU : Nat.card (P.comap layerInclusion) = Nat.card F := by
    rw [card_comap_layerInclusion hPM, hP]
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have hu : (cyclicGenerator F b m hm heven ^ 2) ^ m = 1 := by
    have h := pow_orderOf_eq_one (cyclicGenerator F b m hm heven ^ 2)
    rwa [orderOf_cyclicGenerator_sq F b m hm heven h2] at h
  have hle : X ≤ Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
      SemilinearExtension F b m hm heven Sigma hSigma) := by
    intro x hxX
    have hxc : ∀ A ∈ P.comap layerInclusion,
        x * SemidirectProduct.inl (specialInclusion F b m hm heven A) =
          SemidirectProduct.inl (specialInclusion F b m hm heven A) * x :=
      fun A hA => (Subgroup.mem_centralizer_iff.mp (hXP hxX) _ hA).symm
    obtain ⟨A₀, hA₀, k, rfl⟩ := exists_eq_of_commute hp hcard hb hU hxc
    obtain ⟨n, hn⟩ := hX ⟨_, hxX⟩
    have hxn : ((cyclicGenerator F b m hm heven ^ 2) ^ k *
        specialInclusion F b m hm heven A₀) ^ 2 ^ n = 1 := by
      have h : (SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ k *
          specialInclusion F b m hm heven A₀) :
            SemilinearExtension F b m hm heven Sigma hSigma) ^ 2 ^ n = 1 := by
        simpa using congrArg Subtype.val hn
      rw [← map_pow] at h
      exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)
    have hak : ((cyclicGenerator F b m hm heven ^ 2) ^ k) ^ m = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm k (m : ℤ), _root_.zpow_mul, zpow_natCast,
        hu, _root_.one_zpow]
    have hcomm : Commute ((cyclicGenerator F b m hm heven ^ 2) ^ k)
        (specialInclusion F b m hm heven A₀) :=
      Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven _) k
    have hA₀N : A₀ ^ (2 ^ n * m) = 1 := by
      apply CentralSL2Abelianization.specialInclusion_injective F b m hm heven
      have h1 : ((cyclicGenerator F b m hm heven ^ 2) ^ k *
          specialInclusion F b m hm heven A₀) ^ (2 ^ n * m) = 1 := by
        rw [pow_mul, hxn, one_pow]
      rw [hcomm.mul_pow, mul_comm (2 ^ n) m,
        pow_mul ((cyclicGenerator F b m hm heven ^ 2) ^ k), hak, one_pow, one_mul] at h1
      rw [map_pow, map_one, mul_comm (2 ^ n) m]
      exact h1
    have hA₀q : A₀ ^ (p ^ f) = 1 := by
      have h := Subgroup.orderOf_dvd_natCard _ hA₀
      rw [hU, hcard] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have hcop : Nat.Coprime (2 ^ n * m) (p ^ f) :=
      (Nat.Coprime.mul_left
        (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left n) hmp).pow_right f
    have hA₀1 : A₀ = 1 := by
      have h := pow_gcd_eq_one.mpr ⟨hA₀N, hA₀q⟩
      rwa [hcop.gcd_eq_one, pow_one] at h
    rw [hA₀1, map_one, mul_one, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  exact Subgroup.isCyclic_of_le hle

theorem not_mem_centralizer_of_orderOf [Finite F] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ f) (h3 : 3 < Nat.card F)
    {P : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hPM : P ≤ ModelSignalizers.modelLayer b m hm heven Sigma hSigma)
    (hP : Nat.card P = Nat.card F) {t : SpecialLinearGroup (Fin 2) F}
    (ht : orderOf t = Nat.card F - 1) :
    SemidirectProduct.inl (specialInclusion F b m hm heven t) ∉
      Subgroup.centralizer (P : Set (SemilinearExtension F b m hm heven Sigma hSigma)) := by
  intro hmem
  have hU : Nat.card (P.comap layerInclusion) = Nat.card F := by
    rw [card_comap_layerInclusion hPM, hP]
  obtain ⟨A, hA, hne⟩ := CFSG.SL2MinimalFaithful.exists_not_commute_of_orderOf hp hcard h3 hU ht
  apply hne
  apply layerInclusion_injective (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
    (hSigma := hSigma)
  rw [map_mul, map_mul]
  exact (Subgroup.mem_centralizer_iff.mp hmem _ hA).symm

end CFSG.Wreathed.OriginalAllPrime.Sec11W

module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeR1NLinear

public section

namespace CFSG.Wreathed.OriginalAllPrime.R1NFacts

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers CFSG.Wreathed.CentralSL2

section Groups

variable {G : Type*} [Group G]

theorem conj_eq_inv_of_sq_conj {X : Subgroup G} [Finite X] {t : G}
    (htX : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : ∀ x ∈ X, t * (t * x * t⁻¹) * t⁻¹ = x)
    (hX : X ⊓ Subgroup.centralizer {t} = ⊥) {x : G} (hx : x ∈ X) : t * x * t⁻¹ = x⁻¹ := by
  have hmem : ∀ y ∈ X, t * y * t⁻¹ ∈ X := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp htX y).mp hy
  let φ : X →* X :=
    { toFun := fun y => ⟨t * y * t⁻¹, hmem y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by ext; simp [mul_assoc] }
  have hfree : MonoidHom.FixedPointFree φ := by
    intro y hy
    have hy' : t * (y : G) * t⁻¹ = y := congrArg Subtype.val hy
    have hc : (y : G) ∈ Subgroup.centralizer {t} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : G) * t = t * y * t⁻¹ * t := by rw [hy']
        _ = t * y := by group
    have hyb : (y : G) ∈ X ⊓ Subgroup.centralizer {t} := ⟨y.2, hc⟩
    rw [hX] at hyb
    exact Subtype.ext ((Subgroup.mem_bot).mp hyb)
  have hinv : Function.Involutive φ := fun y => Subtype.ext (ht2 y y.2)
  have h := congrFun (hfree.coe_eq_inv_of_involutive hinv) ⟨x, hx⟩
  exact congrArg Subtype.val h

theorem mem_normalizer_inf_of_normal {X L : Subgroup G} (hL : L.Normal) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp hg x)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hL.conj_mem x h2 g⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := hL.conj_mem _ h2 g⁻¹
    simpa [mul_assoc] using this

end Groups

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem modelLayer_normal :
    (modelLayer b m hm heven Sigma hSigma).Normal := by
  rw [modelLayer_eq_matrixLayer, ← psi_ker]
  infer_instance

theorem modelBase_normal :
    (ModelSignalizers.modelBase b m hm heven Sigma hSigma).Normal := by
  rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem modelY_mem_modelBase :
    modelY b m hm heven Sigma hSigma ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma :=
  ⟨_, rfl⟩

theorem mem_modelLayer_of_pow_eq_one {n : ℕ} (hmn : m = 2 ^ n) {r : ℕ} (hr : Odd r)
    {c : SemilinearExtension F b m hm heven Sigma hSigma}
    (hc : c ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma) (hcr : c ^ r = 1) :
    c ∈ modelLayer b m hm heven Sigma hSigma := by
  obtain ⟨v, rfl⟩ := hc
  rw [modelLayer_eq_matrixLayer, ← psi_ker, MonoidHom.mem_ker]
  set ψ := psi F b m hm heven Sigma hSigma
  have h1 : ψ (SemidirectProduct.inl v) ^ r = 1 := by rw [← map_pow, hcr, map_one]
  have h2 : ψ (SemidirectProduct.inl v) ^ m = 1 := by
    apply Prod.ext
    · rw [Prod.pow_fst, Prod.fst_one]
      have hcard : Nat.card (Multiplicative (ZMod m)) = m := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      have h := pow_card_eq_one' (x := (ψ (SemidirectProduct.inl v)).1)
      rwa [hcard] at h
    · rw [Prod.pow_snd, Prod.snd_one]
      change (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma).right ^ m
        = 1
      rw [SemidirectProduct.right_inl, one_pow]
  have hcop : Nat.Coprime r m := by
    rw [hmn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hr)
  have h := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

theorem exists_eq_inl_of_mem_modelLayer {x : SemilinearExtension F b m hm heven Sigma hSigma}
    (hx : x ∈ modelLayer b m hm heven Sigma hSigma) :
    ∃ Z, SemidirectProduct.inl (specialInclusion F b m hm heven Z) = x :=
  mem_modelLayer_iff.mp hx

theorem pow_eq_one_of_inl_pow {Z : SpecialLinearGroup (Fin 2) F} {r : ℕ}
    (h : (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
      SemilinearExtension F b m hm heven Sigma hSigma) ^ r = 1) : Z ^ r = 1 := by
  rw [inl_specialInclusion_pow] at h
  apply inl_specialInclusion_injective (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
    (hSigma := hSigma)
  change SemidirectProduct.inl (specialInclusion F b m hm heven (Z ^ r)) =
    SemidirectProduct.inl (specialInclusion F b m hm heven 1)
  rw [h, map_one, map_one]

theorem conj_inl_specialInclusion_of_right_eq_one
    {h : SemilinearExtension F b m hm heven Sigma hSigma} {G : GL (Fin 2) F}
    (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G) (hr : h.right = 1)
    (Z : SpecialLinearGroup (Fin 2) F) :
    h * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * h⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven (matrixConjugation F G Z)) := by
  rw [conj_inl_specialInclusion hG, hr]
  simp only [OneMemClass.coe_one, fieldSL_one, MulAut.one_apply]

theorem toGL_weyl_trace : (SpecialLinearGroup.toGL (weyl F)).val 0 0 +
    (SpecialLinearGroup.toGL (weyl F)).val 1 1 = 0 := by
  rw [toGL_weyl_coe]
  simp

theorem trace_eq_zero_of_conj_weyl {G : GL (Fin 2) F}
    (hG : matrixConjugation F G (weyl F) = (weyl F)⁻¹) : G.val 0 0 + G.val 1 1 = 0 := by
  obtain ⟨h11, -⟩ := entries_of_conj_weyl_eq_inv hG
  rw [h11]
  ring

theorem trace_mul_weyl_eq_zero_of_conj_weyl {G : GL (Fin 2) F}
    (hG : matrixConjugation F G (weyl F) = (weyl F)⁻¹) :
    (G * SpecialLinearGroup.toGL (weyl F)).val 0 0 +
      (G * SpecialLinearGroup.toGL (weyl F)).val 1 1 = 0 := by
  obtain ⟨-, h01⟩ := entries_of_conj_weyl_eq_inv hG
  rw [Units.val_mul, toGL_weyl_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01]

theorem commute_of_matrixConjugation_eq {G : GL (Fin 2) F} {Z : SpecialLinearGroup (Fin 2) F}
    (h : matrixConjugation F G Z = Z) :
    SpecialLinearGroup.toGL Z * G = G * SpecialLinearGroup.toGL Z := by
  have h' := congrArg SpecialLinearGroup.toGL h
  rw [matrixConjugation_toGL] at h'
  calc SpecialLinearGroup.toGL Z * G = G * SpecialLinearGroup.toGL Z * G⁻¹ * G := by rw [h']
    _ = G * SpecialLinearGroup.toGL Z := by group

variable [Fintype F]

theorem inf_modelLayer_eq_bot {p : ℕ} [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ∣ m) {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)}
    (hX : IsPGroup p X)
    (hyX : modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (X : Set _))
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma)
    (hr : h.right = 1) (hhX : h ∈ Subgroup.normalizer (X : Set _)) :
    X ⊓ modelLayer b m hm heven Sigma hSigma = ⊥ := by
  set U := X ⊓ modelLayer b m hm heven Sigma hSigma with hUdef
  set y := modelY b m hm heven Sigma hSigma
  have hLn := modelLayer_normal (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
    (hSigma := hSigma)
  obtain ⟨G, hG⟩ := exists_projectiveMap_eq h.left
  have hGJ := (conj_modelY_eq_modelX_mul_iff hG).mp hh
  have hUZ : ∀ x ∈ U, ∃ Z : SpecialLinearGroup (Fin 2) F,
      SemidirectProduct.inl (specialInclusion F b m hm heven Z) = x ∧ Z 0 0 + Z 1 1 = 2 := by
    intro x hx
    obtain ⟨Z, rfl⟩ := exists_eq_inl_of_mem_modelLayer hx.2
    obtain ⟨k, hk⟩ := hX ⟨_, hx.1⟩
    have hk' : (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
        SemilinearExtension F b m hm heven Sigma hSigma) ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact ⟨Z, rfl, trace_eq_two_of_pow_eq_one (pow_eq_one_of_inl_pow hk')⟩
  have hfree : ∀ {g : SemilinearExtension F b m hm heven Sigma hSigma} {A : GL (Fin 2) F},
      A.val 0 0 + A.val 1 1 = 0 →
      (∀ Z, g * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * g⁻¹ =
        SemidirectProduct.inl (specialInclusion F b m hm heven (matrixConjugation F A Z))) →
      U ⊓ Subgroup.centralizer {g} = ⊥ := by
    intro g A hA hconj
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨Z, rfl, htr⟩ := hUZ x hxU
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    have hc : g * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * g⁻¹ =
        SemidirectProduct.inl (specialInclusion F b m hm heven Z) := by
      rw [← hxc, mul_inv_cancel_right]
    rw [hconj] at hc
    have hZ := eq_one_of_commute_of_trace_eq_zero h2 hA htr
      (commute_of_matrixConjugation_eq (inl_specialInclusion_injective hc))
    rw [hZ, map_one, map_one]
    exact Subgroup.one_mem _
  have hconjy : ∀ Z, y * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * y⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven
        (matrixConjugation F (SpecialLinearGroup.toGL (weyl F)) Z)) := by
    intro Z
    rw [modelY_conj_inl_specialInclusion, mul_mul_inv_eq_matrixConjugation]
  have hconjh := conj_inl_specialInclusion_of_right_eq_one hG hr
  have hconjhy : ∀ Z, (h * y) * SemidirectProduct.inl (specialInclusion F b m hm heven Z) *
      (h * y)⁻¹ = SemidirectProduct.inl (specialInclusion F b m hm heven
        (matrixConjugation F (G * SpecialLinearGroup.toGL (weyl F)) Z)) := by
    intro Z
    rw [_root_.mul_inv_rev]
    calc h * y * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * (y⁻¹ * h⁻¹)
        = h * (y * SemidirectProduct.inl (specialInclusion F b m hm heven Z) * y⁻¹) * h⁻¹ := by
          group
      _ = _ := by rw [hconjy, hconjh, map_mul, MulAut.mul_apply]
  have hyU : y ∈ Subgroup.normalizer (U : Set _) := mem_normalizer_inf_of_normal hLn hyX
  have hhU : h ∈ Subgroup.normalizer (U : Set _) := mem_normalizer_inf_of_normal hLn hhX
  have hyinv : ∀ x ∈ U, y * x * y⁻¹ = x⁻¹ := fun x hx =>
    conj_eq_inv_of_inf_centralizer_eq_bot (modelY_mul_self h4) hyU
      (hfree toGL_weyl_trace hconjy) hx
  have hhinv : ∀ x ∈ U, h * x * h⁻¹ = x⁻¹ := by
    intro x hx
    refine conj_eq_inv_of_sq_conj hhU ?_ (hfree (trace_eq_zero_of_conj_weyl hGJ) hconjh) hx
    intro z hz
    obtain ⟨Z, rfl, -⟩ := hUZ z hz
    rw [hconjh, hconjh, matrixConjugation_matrixConjugation (trace_eq_zero_of_conj_weyl hGJ)]
  have hcent := hfree (trace_mul_weyl_eq_zero_of_conj_weyl hGJ) hconjhy
  rw [eq_bot_iff]
  intro x hx
  have hxc : x ∈ U ⊓ Subgroup.centralizer {h * y} := by
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (h * y) * x * (h * y)⁻¹ = x := by
      rw [_root_.mul_inv_rev]
      calc h * y * x * (y⁻¹ * h⁻¹) = h * (y * x * y⁻¹) * h⁻¹ := by group
        _ = (h * x * h⁻¹)⁻¹ := by rw [hyinv x hx]; group
        _ = x := by rw [hhinv x hx, inv_inv]
    calc x * (h * y) = (h * y) * x * (h * y)⁻¹ * (h * y) := by rw [h1]
      _ = (h * y) * x := by group
  rw [hcent] at hxc
  exact hxc

theorem inf_modelBase_eq_bot {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ∣ m) {n : ℕ} (hmn : m = 2 ^ n)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hX : IsPGroup p X)
    (hyX : modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (X : Set _))
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma)
    (hr : h.right = 1) (hhX : h ∈ Subgroup.normalizer (X : Set _)) :
    X ⊓ ModelSignalizers.modelBase b m hm heven Sigma hSigma = ⊥ := by
  have hL := inf_modelLayer_eq_bot h2 h4 hX hyX hh hr hhX
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hxL := mem_modelLayer_of_pow_eq_one hmn hodd hxB hk'
  have : x ∈ X ⊓ modelLayer b m hm heven Sigma hSigma := ⟨hxX, hxL⟩
  rwa [hL] at this

theorem le_modelC {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ∣ m) {n : ℕ} (hmn : m = 2 ^ n)
    {X : Subgroup (SemilinearExtension F b m hm heven Sigma hSigma)} (hX : IsPGroup p X)
    (hyX : modelY b m hm heven Sigma hSigma ∈ Subgroup.normalizer (X : Set _))
    {h : SemilinearExtension F b m hm heven Sigma hSigma}
    (hh : h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma)
    (hr : h.right = 1) (hhX : h ∈ Subgroup.normalizer (X : Set _)) :
    X ≤ modelC b m hm heven Sigma hSigma := by
  have hB := inf_modelBase_eq_bot hp2 h2 h4 hmn hX hyX hh hr hhX
  set y := modelY b m hm heven Sigma hSigma
  intro x hx
  have hc : y * x * y⁻¹ * x⁻¹ ∈ X ⊓ ModelSignalizers.modelBase b m hm heven Sigma hSigma := by
    refine Subgroup.mem_inf.mpr
      ⟨X.mul_mem ((Subgroup.mem_normalizer_iff.mp hyX x).mp hx) (X.inv_mem hx), ?_⟩
    have hBn := modelBase_normal (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
      (hSigma := hSigma)
    have h1 : x * y⁻¹ * x⁻¹ ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma :=
      hBn.conj_mem _ (Subgroup.inv_mem _ modelY_mem_modelBase) x
    have h2' := Subgroup.mul_mem _ modelY_mem_modelBase h1
    simpa [mul_assoc] using h2'
  rw [hB, Subgroup.mem_bot] at hc
  rw [modelC, Subgroup.mem_centralizer_singleton_iff]
  calc x * y = y * x * y⁻¹ * x⁻¹ * (x * y) := by rw [hc, one_mul]
    _ = y * x := by group

end CFSG.Wreathed.OriginalAllPrime.R1NFacts

module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftMatrix
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftMap

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.TorusSplitting
  CFSG.Wreathed.OddFieldTorus CFSG.Wreathed.CentralSL2Abelianization

variable {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
  {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}
  {h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)}
  {J : Subgroup (involutionCentralizer n S e)} [J.Normal]

omit [J.Normal] in
theorem liftMap_injOn (hJR : J ⊓ centralizerOddCore n S e = ⊥) {a b : involutionCentralizer n S e}
    (ha : a ∈ J) (hb : b ∈ J) (hab : liftMap n hn S e Ψ h a = liftMap n hn S e Ψ h b) : a = b :=
  mk_injOn_of_inf_eq_bot hJR ha hb ((liftMap_eq_iff a b).mp hab)

theorem commute_iff_liftMap (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    {j : involutionCentralizer n S e} (hj : j ∈ J) (g : involutionCentralizer n S e) :
    j * g = g * j ↔ liftMap n hn S e Ψ h j * liftMap n hn S e Ψ h g =
      liftMap n hn S e Ψ h g * liftMap n hn S e Ψ h j := by
  rw [commute_iff_mk_commute hJR hj g, ← map_mul, ← map_mul]
  change centralizerOddCoreMap n S e (j * g) = centralizerOddCoreMap n S e (g * j) ↔ _
  rw [← liftMap_eq_iff (Ψ := Ψ) (h := h), map_mul, map_mul]

omit [J.Normal] in
theorem orderOf_liftMap (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    {j : involutionCentralizer n S e} (hj : j ∈ J) :
    orderOf (liftMap n hn S e Ψ h j) = orderOf j := by
  have hinj : Function.Injective ((liftMap n hn S e Ψ h).comp J.subtype) :=
    fun a b hab => Subtype.ext (liftMap_injOn hn hJR a.2 b.2 hab)
  have h1 := orderOf_injective _ hinj ⟨j, hj⟩
  exact h1.trans (Subgroup.orderOf_mk j hj)

theorem commute_y_iff (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hJmem : ∀ j ∈ J, liftMap n hn S e Ψ h j ∈ modelLayer F b n hn Sigma hSigma)
    (y₀ : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (hy : liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n))) =
      modelInl F b n hn Sigma hSigma y₀)
    (hMD : (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
      Subgroup.centralizer {y₀} =
        (OddFieldTorus.torus F).map
          (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)))
    {j : involutionCentralizer n S e} (hj : j ∈ J) :
    j * nModel n hn S e (Original.x2 (2 ^ n)) = nModel n hn S e (Original.x2 (2 ^ n)) * j ↔
      ∃ X ∈ OddFieldTorus.torus F, liftMap n hn S e Ψ h j = modelInl F b n hn Sigma hSigma
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X) := by
  rw [commute_iff_liftMap hn (Ψ := Ψ) (h := h) hJR hj, hy]
  constructor
  · intro hc
    obtain ⟨X, hX⟩ := hJmem j hj
    rw [← hX] at hc
    have hc' : specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X * y₀ =
        y₀ * specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X := by
      apply modelInl_injective F b n hn Sigma hSigma
      simpa only [MonoidHom.comp_apply, map_mul] using hc
    have hmem : specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X ∈
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
          Subgroup.centralizer {y₀} :=
      ⟨⟨X, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr hc'⟩
    rw [hMD] at hmem
    obtain ⟨X', hX', hXX'⟩ := hmem
    refine ⟨X', hX', ?_⟩
    rw [← hX, MonoidHom.comp_apply, ← hXX']
  · rintro ⟨X, hX, hXj⟩
    rw [hXj]
    have hmem : specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X ∈
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
          Subgroup.centralizer {y₀} := by
      rw [hMD]
      exact ⟨X, hX, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
    rw [← map_mul, ← map_mul, hc]

abbrev modelSpecial (F : Type) [Field F] (b : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) :
    SpecialLinearGroup (Fin 2) F →*
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
  (modelInl F b n hn Sigma hSigma).comp
    (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))

omit [J.Normal] in
theorem modelSpecial_injective :
    Function.Injective (modelSpecial F b n hn Sigma hSigma) :=
  (modelInl_injective F b n hn Sigma hSigma).comp
    (specialInclusion_injective F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))

@[expose] noncomputable def oddTorus (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (J : Subgroup (involutionCentralizer n S e)) (WF : Subgroup (SpecialLinearGroup (Fin 2) F)) :
    Subgroup G :=
  ((WF.map (modelSpecial F b n hn Sigma hSigma)).comap
    ((liftMap n hn S e Ψ h).comp J.subtype)).map
      ((involutionCentralizer n S e).subtype.comp J.subtype)

theorem mem_oddTorus_iff (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hJmem : ∀ j ∈ J, liftMap n hn S e Ψ h j ∈ modelLayer F b n hn Sigma hSigma)
    (y₀ : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (hy : liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n))) =
      modelInl F b n hn Sigma hSigma y₀)
    (hMD : (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
      Subgroup.centralizer {y₀} =
        (OddFieldTorus.torus F).map
          (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)))
    (WF : Subgroup (SpecialLinearGroup (Fin 2) F))
    (hWF : ∀ g, g ∈ WF ↔ g ∈ OddFieldTorus.torus F ∧ Odd (orderOf g)) (g : G) :
    g ∈ oddTorus n hn S e Ψ h J WF ↔ g ∈ J.map (involutionCentralizer n S e).subtype ∧
      g * wreathModelHom S e (Original.x2 (2 ^ n)) = wreathModelHom S e (Original.x2 (2 ^ n)) * g ∧
      Odd (orderOf g) := by
  constructor
  · rintro ⟨j, ⟨X, hXWF, hXj⟩, rfl⟩
    have hXT := ((hWF X).mp hXWF).1
    have hc := (commute_y_iff hn hJR hJmem y₀ hy hMD j.2).mpr ⟨X, hXT, hXj.symm⟩
    refine ⟨⟨j, j.2, rfl⟩, congrArg Subtype.val hc, ?_⟩
    change Odd (orderOf ((j : involutionCentralizer n S e) : G))
    rw [Subgroup.orderOf_coe, ← orderOf_liftMap hn (Ψ := Ψ) (h := h) hJR j.2]
    change Odd (orderOf (((liftMap n hn S e Ψ h).comp J.subtype) j))
    rw [← hXj, orderOf_injective _ (modelSpecial_injective hn)]
    exact ((hWF X).mp hXWF).2
  · rintro ⟨⟨j, hj, rfl⟩, hcy, hodd⟩
    have hc : j * nModel n hn S e (Original.x2 (2 ^ n)) =
        nModel n hn S e (Original.x2 (2 ^ n)) * j := Subtype.ext hcy
    obtain ⟨X, hXT, hXj⟩ := (commute_y_iff hn hJR hJmem y₀ hy hMD hj).mp hc
    have hXodd : Odd (orderOf X) := by
      rw [← orderOf_injective _ (modelSpecial_injective hn) X]
      change Odd (orderOf (modelInl F b n hn Sigma hSigma
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X)))
      rw [← hXj, orderOf_liftMap hn hJR hj]
      change Odd (orderOf (j : G)) at hodd
      rwa [Subgroup.orderOf_coe] at hodd
    exact ⟨⟨j, hj⟩, ⟨X, (hWF X).mpr ⟨hXT, hXodd⟩, hXj.symm⟩, rfl⟩

omit [J.Normal] in
theorem exists_oddTorus_equiv (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hJsurj : ∀ g ∈ modelLayer F b n hn Sigma hSigma, ∃ j ∈ J, liftMap n hn S e Ψ h j = g)
    (WF : Subgroup (SpecialLinearGroup (Fin 2) F)) :
    Nonempty (oddTorus n hn S e Ψ h J WF ≃* WF) := by
  set K' := (WF.map (modelSpecial F b n hn Sigma hSigma)).comap
    ((liftMap n hn S e Ψ h).comp J.subtype) with hK'
  have hinjΦ : Function.Injective ((liftMap n hn S e Ψ h).comp J.subtype) :=
    fun a b hab => Subtype.ext (liftMap_injOn hn hJR a.2 b.2 hab)
  have hle : WF.map (modelSpecial F b n hn Sigma hSigma) ≤
      ((liftMap n hn S e Ψ h).comp J.subtype).range := by
    rintro _ ⟨X, -, rfl⟩
    obtain ⟨j, hj, hjX⟩ := hJsurj (modelSpecial F b n hn Sigma hSigma X) ⟨X, rfl⟩
    exact ⟨⟨j, hj⟩, hjX⟩
  have heq : K'.map ((liftMap n hn S e Ψ h).comp J.subtype) =
      WF.map (modelSpecial F b n hn Sigma hSigma) := Subgroup.map_comap_eq_self hle
  have e1 : K' ≃* oddTorus n hn S e Ψ h J WF :=
    K'.equivMapOfInjective _ (Subtype.val_injective.comp Subtype.val_injective)
  have e2 : K' ≃* K'.map ((liftMap n hn S e Ψ h).comp J.subtype) :=
    K'.equivMapOfInjective _ hinjΦ
  have e3 : WF ≃* WF.map (modelSpecial F b n hn Sigma hSigma) :=
    WF.equivMapOfInjective _ (modelSpecial_injective hn)
  exact ⟨e1.symm.trans (e2.trans ((MulEquiv.subgroupCongr heq).trans e3.symm))⟩

theorem swap_inv_oddTorus (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hJmem : ∀ j ∈ J, liftMap n hn S e Ψ h j ∈ modelLayer F b n hn Sigma hSigma)
    (y₀ : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (hy : liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n))) =
      modelInl F b n hn Sigma hSigma y₀)
    (hMD : (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
      Subgroup.centralizer {y₀} =
        (OddFieldTorus.torus F).map
          (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)))
    (WF : Subgroup (SpecialLinearGroup (Fin 2) F))
    (hWF : ∀ g, g ∈ WF ↔ g ∈ OddFieldTorus.torus F ∧ Odd (orderOf g))
    (hd : nModel n hn S e (Original.d (2 ^ n)) ∈ J)
    (hx : liftMap n hn S e Ψ h (centralInvolution n S e) = modelSpecial F b n hn Sigma hSigma
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F))
    (a' : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (ha' : ∀ v, a' * v = v * a')
    (hy₀ : y₀ = a' * specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      (OddFieldTorus.J₀ F))
    {g : G} (hg : g ∈ oddTorus n hn S e Ψ h J WF) :
    wreathModelHom S e (Original.z (2 ^ n)) * g * (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ =
      g⁻¹ := by
  have hgy := ((mem_oddTorus_iff hn hJR hJmem y₀ hy hMD WF hWF g).mp hg).2.1
  obtain ⟨⟨j, hjJ⟩, ⟨X, hXWF, hXj⟩, rfl⟩ := hg
  change modelSpecial F b n hn Sigma hSigma X = liftMap n hn S e Ψ h j at hXj
  have hXT := ((hWF X).mp hXWF).1
  obtain ⟨B, hB⟩ := hJmem _ hd
  change modelSpecial F b n hn Sigma hSigma B = _ at hB
  set iF := specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
  set dN := nModel n hn S e (Original.d (2 ^ n))
  set yN := nModel n hn S e (Original.x2 (2 ^ n))
  have hdy : dN * yN * dN⁻¹ = centralInvolution n S e * yN := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [nModel_d_coe n hn S e]
    exact d_conj_x2 n hn S e
  have h1 := congrArg (liftMap n hn S e Ψ h) hdy
  rw [map_mul, map_mul, map_inv, map_mul, ← hB, hy, hx] at h1
  have h2 : iF B * y₀ * (iF B)⁻¹ =
      iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) * y₀ := by
    apply modelInl_injective F b n hn Sigma hSigma
    simpa only [map_mul, map_inv, MonoidHom.comp_apply] using h1
  rw [hy₀] at h2
  have h3 : iF (B * OddFieldTorus.J₀ F * B⁻¹) =
      iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * OddFieldTorus.J₀ F) := by
    apply mul_left_cancel (a := a')
    calc a' * iF (B * OddFieldTorus.J₀ F * B⁻¹) =
        iF B * (a' * iF (OddFieldTorus.J₀ F)) * (iF B)⁻¹ := by
          rw [map_mul, map_mul, map_inv, ← mul_assoc, ← mul_assoc, ha' (iF B)]
          simp only [mul_assoc]
      _ = iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) *
          (a' * iF (OddFieldTorus.J₀ F)) := h2
      _ = a' * iF (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * OddFieldTorus.J₀ F) := by
          rw [← mul_assoc, ← ha', mul_assoc, ← map_mul]
  have hBJ : B * OddFieldTorus.J₀ F * B⁻¹ =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * OddFieldTorus.J₀ F :=
    specialInclusion_injective F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) h3
  have hBJ' : B * OddFieldTorus.J₀ F =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * OddFieldTorus.J₀ F * B := by
    rw [← hBJ]
    group
  have hinvX := conj_inv_of_anticommute B X hBJ' hXT
  have h4 : liftMap n hn S e Ψ h (dN * j * dN⁻¹) = liftMap n hn S e Ψ h j⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, ← hB, ← hXj, ← map_inv, ← map_mul, ← map_mul,
      hinvX, map_inv]
  have hconjJ : dN * j * dN⁻¹ ∈ J := (inferInstance : J.Normal).conj_mem j hjJ dN
  have h5 : dN * j * dN⁻¹ = j⁻¹ := liftMap_injOn hn hJR hconjJ (J.inv_mem hjJ) h4
  have h6 := congrArg Subtype.val h5
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h6
  rw [nModel_d_coe n hn S e] at h6
  change wreathModelHom S e (Original.z (2 ^ n)) * (j : G) *
    (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ = (j : G)⁻¹
  change (j : G) * wreathModelHom S e (Original.x2 (2 ^ n)) =
    wreathModelHom S e (Original.x2 (2 ^ n)) * (j : G) at hgy
  set y := wreathModelHom S e (Original.x2 (2 ^ n))
  set w := wreathModelHom S e (Original.z (2 ^ n))
  calc w * (j : G) * w⁻¹ = y⁻¹ * ((y * w) * j * (y * w)⁻¹) * y := by group
    _ = y⁻¹ * (j : G)⁻¹ * y := by rw [h6]
    _ = (j : G)⁻¹ := by
      have hc : y⁻¹ * (j : G)⁻¹ = (j : G)⁻¹ * y⁻¹ := by
        rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hgy]
      rw [hc, inv_mul_cancel_right]

end CFSG.Wreathed.NormalComponentLift

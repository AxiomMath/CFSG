module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]

abbrev rangeNormalizer (π : SpecialLinearGroup (Fin n) F →* H) : Subgroup H :=
  Subgroup.normalizer (π.range : Set H)

theorem monoidHom_eq_one_of_isPerfect {G M : Type*} [Group G] [Group M] [IsMulCommutative M]
    [Group.IsPerfect G] (f : G →* M) : f = 1 := by
  have hsub : Subsingleton f.range :=
    @Group.IsPerfect.subsingleton_of_isMulCommutative f.range _
      (Group.IsPerfect.range f) inferInstance
  apply MonoidHom.ext
  intro g
  have hg : f g ∈ f.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have h1 : (⟨f g, hg⟩ : f.range) = 1 := @Subsingleton.elim _ hsub _ _
  simpa using congrArg Subtype.val h1

omit [Finite F] [CharP F 2] in
theorem eq_of_comp_proj_eq {π : SpecialLinearGroup (Fin n) F →* H}
    (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (Φ Ψ : MulAut (SpecialLinearGroup (Fin n) F))
    (h : ∀ g, π (Φ g) = π (Ψ g)) : Φ = Ψ := by
  have hcen : ∀ g, (Φ g)⁻¹ * Ψ g ∈ scalars n F := by
    intro g
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, h g, inv_mul_cancel]
  let ψ : SpecialLinearGroup (Fin n) F →* Subgroup.center (SpecialLinearGroup (Fin n) F) :=
    { toFun := fun g => ⟨(Φ g)⁻¹ * Ψ g, scalars_le_center n F (hcen g)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Subtype.ext
        have hc : ∀ y : SpecialLinearGroup (Fin n) F,
            y * ((Φ g)⁻¹ * Ψ g) = ((Φ g)⁻¹ * Ψ g) * y :=
          Subgroup.mem_center_iff.mp (scalars_le_center n F (hcen g))
        show (Φ (g * h))⁻¹ * Ψ (g * h) =
          ((Φ g)⁻¹ * Ψ g) * ((Φ h)⁻¹ * Ψ h)
        rw [map_mul, map_mul]
        calc (Φ g * Φ h)⁻¹ * (Ψ g * Ψ h)
            = (Φ h)⁻¹ * ((Φ g)⁻¹ * Ψ g) * Ψ h := by group
          _ = (Φ h)⁻¹ * (((Φ g)⁻¹ * Ψ g) * Ψ h) := by group
          _ = (Φ h)⁻¹ * (Ψ h * ((Φ g)⁻¹ * Ψ g)) := by rw [hc (Ψ h)]
          _ = ((Φ h)⁻¹ * Ψ h) * ((Φ g)⁻¹ * Ψ g) := by group
          _ = ((Φ g)⁻¹ * Ψ g) * ((Φ h)⁻¹ * Ψ h) := by
              rw [hc ((Φ h)⁻¹ * Ψ h)] }
  have hψ : ψ = 1 :=
    @monoidHom_eq_one_of_isPerfect (SpecialLinearGroup (Fin n) F)
      (Subgroup.center (SpecialLinearGroup (Fin n) F)) _ _ _
      (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn) ψ
  apply MulEquiv.ext
  intro g
  have h1 : (ψ g : SpecialLinearGroup (Fin n) F) = 1 := by
    rw [hψ]
    rfl
  change (Φ g)⁻¹ * Ψ g = 1 at h1
  exact inv_mul_eq_one.mp h1

section CyclicScalars

omit [CharP F 2] in
theorem isCyclic_scalars {n : ℕ} (hn : 1 ≤ n) : IsCyclic (scalars n F) := by
  rw [scalars_eq_center]
  exact (SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin n)
    (⟨0, hn⟩ : Fin n)).isCyclic.mpr inferInstance

theorem map_mulAut_eq_of_le_cyclic {G : Type*} [Group G] [Finite G] {Z K : Subgroup G}
    (hKZ : K ≤ Z) (hZ : IsCyclic Z) (φ : MulAut G)
    (hφ : Z.map (φ : G →* G) = Z) : K.map (φ : G →* G) = K := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Z).mp hZ
  have hKle : K ≤ Subgroup.zpowers g := hKZ.trans_eq hg.symm
  obtain ⟨m, hm⟩ := (Subgroup.le_zpowers_iff g K).mp hKle
  have hgZ : g ∈ Z := hg ▸ Subgroup.mem_zpowers g
  have hφgZ : φ g ∈ Z := by
    have h := Subgroup.mem_map_of_mem (φ : G →* G) hgZ
    rwa [hφ] at h
  have hφg : φ g ∈ Subgroup.zpowers g := hg.symm ▸ hφgZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφg
  have hmem : φ (g ^ m) ∈ Subgroup.zpowers (g ^ m) := by
    rw [map_pow, ← hk]
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa only [zpow_natCast] using (zpow_comm g k (m : ℤ)).symm
  have hmap : K.map (φ : G →* G) = Subgroup.zpowers (φ (g ^ m)) := by
    rw [hm, MonoidHom.map_zpowers]
    rfl
  have hle : K.map (φ : G →* G) ≤ K := by
    rw [hmap]
    exact Subgroup.zpowers_le.mpr (hm ▸ hmem)
  have hcard : Nat.card K ≤ Nat.card (K.map (φ : G →* G)) := by
    rw [Subgroup.card_map_of_injective φ.injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end CyclicScalars


section CenterQuotient

theorem mem_center_of_mk_mem_center {G : Type*} [Group G] [Group.IsPerfect G]
    {K : Subgroup G} [K.Normal] (hK : K ≤ Subgroup.center G) {y : G}
    (hy : QuotientGroup.mk' K y ∈ Subgroup.center (G ⧸ K)) :
    y ∈ Subgroup.center G := by
  have hdelta : ∀ x : G,
      MulAut.conj y x * ((1 : MulAut G) x)⁻¹ ∈ Subgroup.center G := by
    intro x
    apply hK
    have hcomm : QuotientGroup.mk' K y * QuotientGroup.mk' K x =
        QuotientGroup.mk' K x * QuotientGroup.mk' K y :=
      (Subgroup.mem_center_iff.mp hy (QuotientGroup.mk' K x)).symm
    have h1 : QuotientGroup.mk' K (y * x * y⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      calc QuotientGroup.mk' K y * QuotientGroup.mk' K x *
            (QuotientGroup.mk' K y)⁻¹ * (QuotientGroup.mk' K x)⁻¹
          = (QuotientGroup.mk' K x * QuotientGroup.mk' K y) *
              (QuotientGroup.mk' K y)⁻¹ * (QuotientGroup.mk' K x)⁻¹ := by rw [hcomm]
        _ = 1 := by group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hconj : MulAut.conj y = 1 :=
    CFSG.GorensteinWalter.perfect_central_automorphism_eq inferInstance (MulAut.conj y) 1 hdelta
  rw [Subgroup.mem_center_iff]
  intro x
  have h := congrArg (fun f : MulAut G => f x) hconj
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

end CenterQuotient

section Conjugation

variable (π : SpecialLinearGroup (Fin n) F →* H)

noncomputable def conjLift (h : rangeNormalizer π) (g : SpecialLinearGroup (Fin n) F) :
    SpecialLinearGroup (Fin n) F :=
  Classical.choose (MonoidHom.mem_range.mp
    ((Subgroup.mem_normalizer_iff.mp h.2 (π g)).mp ((MonoidHom.mem_range.mpr ⟨g, rfl⟩))))

omit [Finite F] [CharP F 2] in
theorem conjLift_spec (h : rangeNormalizer π) (g : SpecialLinearGroup (Fin n) F) :
    π (conjLift π h g) = (h : H) * π g * (h : H)⁻¹ :=
  Classical.choose_spec (MonoidHom.mem_range.mp
    ((Subgroup.mem_normalizer_iff.mp h.2 (π g)).mp ((MonoidHom.mem_range.mpr ⟨g, rfl⟩))))

omit [Finite F] [CharP F 2] in
theorem proj_conjLift_one (hker : π.ker ≤ scalars n F) (h : rangeNormalizer π) :
    proj n F (conjLift π h 1) = 1 := by
  rw [proj_eq_one_iff]
  apply hker
  rw [MonoidHom.mem_ker, conjLift_spec, map_one, mul_one, mul_inv_cancel]

omit [Finite F] [CharP F 2] in
theorem proj_conjLift_mul (hker : π.ker ≤ scalars n F) (h : rangeNormalizer π)
    (g₁ g₂ : SpecialLinearGroup (Fin n) F) :
    proj n F (conjLift π h (g₁ * g₂)) =
      proj n F (conjLift π h g₁ * conjLift π h g₂) := by
  rw [proj_eq_proj_iff]
  apply hker
  rw [MonoidHom.mem_ker]
  simp only [map_mul, map_inv, conjLift_spec]
  group

noncomputable def conjHom (hker : π.ker ≤ scalars n F) (h : rangeNormalizer π) :
    SpecialLinearGroup (Fin n) F →* projectiveSL n F where
  toFun g := proj n F (conjLift π h g)
  map_one' := proj_conjLift_one π hker h
  map_mul' := proj_conjLift_mul π hker h

omit [Finite F] [CharP F 2] in
theorem conjHom_ker (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) (h : rangeNormalizer π) :
    scalars n F ≤ (conjHom π hker h).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzcenter : (⟨π z, (MonoidHom.mem_range.mpr ⟨z, rfl⟩)⟩ : π.range) ∈ Subgroup.center (π.range) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, hg⟩ := y.2
    apply Subtype.ext
    change (↑y : H) * π z = π z * ↑y
    rw [← hg]
    show π g * π z = π z * π g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (scalars_le_center n F hz) g]
  let y₀ : π.range := ⟨(h : H) * π z * (h : H)⁻¹, (Subgroup.mem_normalizer_iff.mp h.2
      (π z)).mp ((MonoidHom.mem_range.mpr ⟨z, rfl⟩))⟩
  have hcen_y : y₀ ∈ Subgroup.center (π.range) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, hg⟩ := y.2
    apply Subtype.ext
    change (↑y : H) * ((h : H) * π z * (h : H)⁻¹) =
      ((h : H) * π z * (h : H)⁻¹) * ↑y
    rw [← hg]
    set g' := conjLift (π := π) h⁻¹ g
    have hg' : π g = (h : H) * π g' * (h : H)⁻¹ := by
      rw [conjLift_spec (π := π) (h := h⁻¹) (g := g), Subgroup.coe_inv, inv_inv]
      group
    have hc : π g' * π z = π z * π g' := by
      rw [← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp (scalars_le_center n F hz) g']
    show π g * ((h : H) * π z * (h : H)⁻¹) =
      ((h : H) * π z * (h : H)⁻¹) * π g
    rw [hg']
    show ((h : H) * π g' * (h : H)⁻¹) * ((h : H) * π z * (h : H)⁻¹) =
      ((h : H) * π z * (h : H)⁻¹) * ((h : H) * π g' * (h : H)⁻¹)
    calc ((h : H) * π g' * (h : H)⁻¹) * ((h : H) * π z * (h : H)⁻¹)
        = (h : H) * (π g' * π z) * (h : H)⁻¹ := by group
      _ = (h : H) * (π z * π g') * (h : H)⁻¹ := by rw [hc]
      _ = ((h : H) * π z * (h : H)⁻¹) * ((h : H) * π g' * (h : H)⁻¹) := by group
  let e := QuotientGroup.quotientKerEquivRange π
  have he_mk : ∀ g, e (QuotientGroup.mk' π.ker g) = ⟨π g, (MonoidHom.mem_range.mpr ⟨g, rfl⟩)⟩ := by
    intro g
    rfl
  have hmap : QuotientGroup.mk' π.ker (conjLift π h z) ∈
      Subgroup.center (SpecialLinearGroup (Fin n) F ⧸ π.ker) := by
    have h2 : e (QuotientGroup.mk' π.ker (conjLift π h z)) = y₀ := by
      rw [he_mk]
      apply Subtype.ext
      exact conjLift_spec π h z
    have h1 : e (QuotientGroup.mk' π.ker (conjLift π h z)) ∈ Subgroup.center (π.range) := by
      rw [h2]
      exact hcen_y
    rw [← Subgroup.map_center_eq e] at h1
    rcases Subgroup.mem_map.mp h1 with ⟨w, hw, hwe⟩
    rwa [e.injective hwe] at hw
  have hKcenter : π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
    rwa [← scalars_eq_center]
  have hyZ : conjLift π h z ∈ scalars n F := by
    rw [scalars_eq_center]
    exact @mem_center_of_mk_mem_center (SpecialLinearGroup (Fin n) F) _
      (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn) (π.ker) _
      hKcenter _ hmap
  exact proj_eq_one_iff.mpr hyZ

noncomputable def conjMulAut (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) : MulAut (projectiveSL n F) where
  toFun := QuotientGroup.lift (scalars n F) (conjHom π hker h) (conjHom_ker π hker hn h)
  invFun := QuotientGroup.lift (scalars n F) (conjHom π hker h⁻¹) (conjHom_ker π hker hn h⁻¹)
  left_inv := by
    intro x
    obtain ⟨g, rfl⟩ := proj_surjective n F x
    change (QuotientGroup.lift (scalars n F) (conjHom π hker h⁻¹) (conjHom_ker π hker hn h⁻¹))
      ((QuotientGroup.lift (scalars n F) (conjHom π hker h) (conjHom_ker π hker hn h))
        (g : projectiveSL n F)) = (g : projectiveSL n F)
    rw [QuotientGroup.lift_mk']
    change (QuotientGroup.lift (scalars n F) (conjHom π hker h⁻¹) (conjHom_ker π hker hn h⁻¹))
      (proj n F (conjLift π h g)) = (g : projectiveSL n F)
    rw [show proj n F (conjLift π h g) = (conjLift π h g : projectiveSL n F) from rfl]
    rw [QuotientGroup.lift_mk']
    show proj n F (conjLift π h⁻¹ (conjLift π h g)) = proj n F g
    rw [proj_eq_proj_iff]
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, conjLift_spec, conjLift_spec,
      Subgroup.coe_inv, inv_inv]
    group
  right_inv := by
    intro x
    obtain ⟨g, rfl⟩ := proj_surjective n F x
    change (QuotientGroup.lift (scalars n F) (conjHom π hker h) (conjHom_ker π hker hn h))
      ((QuotientGroup.lift (scalars n F) (conjHom π hker h⁻¹) (conjHom_ker π hker hn h⁻¹))
        (g : projectiveSL n F)) = (g : projectiveSL n F)
    rw [QuotientGroup.lift_mk']
    change (QuotientGroup.lift (scalars n F) (conjHom π hker h) (conjHom_ker π hker hn h))
      (proj n F (conjLift π h⁻¹ g)) = (g : projectiveSL n F)
    rw [show proj n F (conjLift π h⁻¹ g) = (conjLift π h⁻¹ g : projectiveSL n F) from rfl]
    rw [QuotientGroup.lift_mk']
    show proj n F (conjLift π h (conjLift π h⁻¹ g)) = proj n F g
    rw [proj_eq_proj_iff]
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, conjLift_spec, conjLift_spec,
      Subgroup.coe_inv, inv_inv]
    group
  map_mul' := map_mul _

omit [Finite F] [CharP F 2] in
theorem conjMulAut_apply_proj (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) (g : SpecialLinearGroup (Fin n) F) :
    conjMulAut π hker hn h (proj n F g) = proj n F (conjLift π h g) := by
  change (QuotientGroup.lift (scalars n F) (conjHom π hker h) (conjHom_ker π hker hn h))
    (g : projectiveSL n F) = proj n F (conjLift π h g)
  rw [QuotientGroup.lift_mk']
  rfl

end Conjugation


section StandardForm

variable (π : SpecialLinearGroup (Fin n) F →* H)

omit [CharP F 2] in
theorem exists_stdAut (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      ∀ g : SpecialLinearGroup (Fin n) F,
        (h : H) * π g * (h : H)⁻¹ =
          π (CFSG.QuasithinUnique.K1.stdAut A σ ε g) := by
  classical
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := F) (n := n) hn).2 (conjMulAut π hker hn h)
  refine ⟨A, σ, ε, hε, fun g => ?_⟩
  have hdesc : LinearFlag.descendAut n F (CFSG.QuasithinUnique.K1.stdAut A σ ε) =
      conjMulAut π hker hn h := by
    rw [CFSG.QuasithinUnique.K1.descendAut_stdAut, ← hα]
  have hΦZ : (scalars n F).map (CFSG.QuasithinUnique.K1.stdAut A σ ε : _ →* _) =
      scalars n F := LinearFlag.map_scalars_eq n F _
  have hΦK : (π.ker).map (CFSG.QuasithinUnique.K1.stdAut A σ ε : _ →* _) = π.ker :=
    map_mulAut_eq_of_le_cyclic hker (isCyclic_scalars (n := n) (by omega)) _ hΦZ
  let Φbar : SpecialLinearGroup (Fin n) F ⧸ π.ker ≃* SpecialLinearGroup (Fin n) F ⧸ π.ker :=
    QuotientGroup.congr π.ker π.ker (CFSG.QuasithinUnique.K1.stdAut A σ ε) hΦK
  let e := QuotientGroup.quotientKerEquivRange π
  let β : SpecialLinearGroup (Fin n) F ⧸ π.ker ≃* SpecialLinearGroup (Fin n) F ⧸ π.ker :=
    (MulAut.congr e).symm (Subgroup.normalizerMonoidHom (H := π.range) h)
  have he_mk : ∀ x, e (QuotientGroup.mk' π.ker x) =
      ⟨π x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ := fun x => rfl
  have hβ_mk : ∀ x, β (QuotientGroup.mk' π.ker x) =
      QuotientGroup.mk' π.ker (conjLift π h x) := by
    intro x
    change (MulAut.congr e).symm (Subgroup.normalizerMonoidHom (H := π.range) h)
      (QuotientGroup.mk' π.ker x) = _
    rw [MulAut.congr_symm_apply]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, he_mk]
    apply e.injective
    rw [e.apply_symm_apply, he_mk]
    apply Subtype.ext
    change (h : H) * π x * (h : H)⁻¹ = π (conjLift π h x)
    rw [conjLift_spec]
  have hΦbar_mk : ∀ x, Φbar (QuotientGroup.mk' π.ker x) =
      QuotientGroup.mk' π.ker (CFSG.QuasithinUnique.K1.stdAut A σ ε x) := by
    intro x
    exact QuotientGroup.congr_mk' π.ker π.ker _ hΦK x
  have hdelta : ∀ y : SpecialLinearGroup (Fin n) F ⧸ π.ker,
      Φbar y * (β y)⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin n) F ⧸ π.ker) := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro g
    change Φbar (QuotientGroup.mk' π.ker g) * (β (QuotientGroup.mk' π.ker g))⁻¹ ∈
      Subgroup.center (SpecialLinearGroup (Fin n) F ⧸ π.ker)
    rw [hΦbar_mk, hβ_mk]
    have hproj : proj n F (CFSG.QuasithinUnique.K1.stdAut A σ ε g) =
        proj n F (conjLift π h g) := by
      rw [← LinearFlag.descendAut_proj n F _ g]
      rw [hdesc, conjMulAut_apply_proj]
    have hc : (conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g ∈
        scalars n F := proj_eq_proj_iff.mp hproj.symm
    have hc_eq : CFSG.QuasithinUnique.K1.stdAut A σ ε g * (conjLift π h g)⁻¹ =
        (conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g := by
      have hcentral := Subgroup.mem_center_iff.mp (scalars_le_center n F hc)
      have hcomm := hcentral (conjLift π h g)
      have h' : CFSG.QuasithinUnique.K1.stdAut A σ ε g =
          (conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g *
            (conjLift π h g) := by
        calc CFSG.QuasithinUnique.K1.stdAut A σ ε g
            = conjLift π h g * ((conjLift π h g)⁻¹ *
                CFSG.QuasithinUnique.K1.stdAut A σ ε g) := by group
          _ = ((conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g) *
                conjLift π h g := hcomm
      calc CFSG.QuasithinUnique.K1.stdAut A σ ε g * (conjLift π h g)⁻¹
          = ((conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g *
              (conjLift π h g)) * (conjLift π h g)⁻¹ := by
                conv_lhs => rw [h']
        _ = (conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g := by group
    rw [← map_inv, ← map_mul, hc_eq]
    have hc' : (conjLift π h g)⁻¹ * CFSG.QuasithinUnique.K1.stdAut A σ ε g ∈
        Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rwa [← scalars_eq_center]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective π.ker)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' π.ker) hc')
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin n) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn
  have hperfQ : Group.IsPerfect
      (SpecialLinearGroup (Fin n) F ⧸ π.ker) :=
    @Group.IsPerfect.instQuotientSubgroup (SpecialLinearGroup (Fin n) F) _
      (π.ker) _ hperfSL
  have hΦbar_eq : Φbar = β :=
    CFSG.GorensteinWalter.perfect_central_automorphism_eq hperfQ Φbar β hdelta
  have hfinal : (h : H) * π g * (h : H)⁻¹ =
      π (CFSG.QuasithinUnique.K1.stdAut A σ ε g) := by
    have h1 : β (QuotientGroup.mk' π.ker g) = Φbar (QuotientGroup.mk' π.ker g) := by
      rw [hΦbar_eq]
    rw [hβ_mk, hΦbar_mk] at h1
    have h2 := congrArg (fun z => e z) h1
    rw [he_mk, he_mk] at h2
    exact (conjLift_spec π h g).symm.trans (congrArg Subtype.val h2)
  exact hfinal

end StandardForm


section LiftHom

variable (π : SpecialLinearGroup (Fin n) F →* H)

omit [CharP F 2] in
theorem exists_stdAut_data (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) :
    ∃ p : GL (Fin n) F × (F ≃+* F) × ℕ, p.2.2 ≤ 1 ∧
      ∀ g : SpecialLinearGroup (Fin n) F,
        (h : H) * π g * (h : H)⁻¹ =
          π (CFSG.QuasithinUnique.K1.stdAut p.1 p.2.1 p.2.2 g) := by
  obtain ⟨A, σ, ε, hε, hspec⟩ := exists_stdAut π hker hn h
  exact ⟨(A, σ, ε), hε, hspec⟩

@[expose] noncomputable def stdData (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) : GL (Fin n) F × (F ≃+* F) × ℕ :=
  Classical.choose (exists_stdAut_data π hker hn h)

omit [CharP F 2] in
theorem stdData_eps_le_one (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) : (stdData π hker hn h).2.2 ≤ 1 :=
  (Classical.choose_spec (exists_stdAut_data π hker hn h)).1

omit [CharP F 2] in
theorem stdData_spec (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) (g : SpecialLinearGroup (Fin n) F) :
    (h : H) * π g * (h : H)⁻¹ =
      π (CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h).1
        (stdData π hker hn h).2.1 (stdData π hker hn h).2.2 g) :=
  (Classical.choose_spec (exists_stdAut_data π hker hn h)).2 g

@[expose] noncomputable def liftAut (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    rangeNormalizer π →* MulAut (SpecialLinearGroup (Fin n) F) where
  toFun h := CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h).1
    (stdData π hker hn h).2.1 (stdData π hker hn h).2.2
  map_one' := by
    apply eq_of_comp_proj_eq (π := π) hker hn
    intro g
    rw [← stdData_spec, MulAut.one_apply]
    simp
  map_mul' := fun h₁ h₂ => by
    apply eq_of_comp_proj_eq (π := π) hker hn
    intro g
    rw [MulAut.mul_apply]
    simp only [← stdData_spec, Subgroup.coe_mul]
    group

omit [CharP F 2] in
theorem liftAut_spec (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) (g : SpecialLinearGroup (Fin n) F) :
    π (liftAut π hker hn h g) = (h : H) * π g * (h : H)⁻¹ := by
  change π (CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h).1
    (stdData π hker hn h).2.1 (stdData π hker hn h).2.2 g) =
    (h : H) * π g * (h : H)⁻¹
  exact (stdData_spec π hker hn h g).symm

omit [CharP F 2] in
theorem liftAut_eq_stdAut (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (h : rangeNormalizer π) :
    liftAut π hker hn h =
      CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn h).1
        (stdData π hker hn h).2.1 (stdData π hker hn h).2.2 :=
  rfl

omit [CharP F 2] in
theorem liftAut_ker (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n) :
    (liftAut π hker hn).ker =
      (Subgroup.centralizer (π.range : Set H)).subgroupOf (rangeNormalizer π) := by
  ext h
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have h2 : liftAut π hker hn h x = x := by rw [hh]; rfl
    have h3 := liftAut_spec π hker hn h x
    rw [h2] at h3
    calc π x * (h : H) = ((h : H) * π x * (h : H)⁻¹) * (h : H) := by
          conv_lhs => rw [h3]
      _ = (h : H) * π x := by group
  · intro hh
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hh
    apply eq_of_comp_proj_eq (π := π) hker hn _ 1
    intro x
    rw [liftAut_spec, MulAut.one_apply]
    have hc := hh (π x) (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    rw [← hc]
    group

omit [CharP F 2] in
theorem liftAut_range (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (x : SpecialLinearGroup (Fin n) F) :
    liftAut π hker hn
        ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ =
      MulAut.conj x := by
  apply eq_of_comp_proj_eq (π := π) hker hn
  intro g
  rw [liftAut_spec, MulAut.conj_apply, map_mul, map_mul, map_inv]

end LiftHom

end CFSG.LieType.SpecialLinear

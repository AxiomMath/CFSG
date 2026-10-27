module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6Sc
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxFin
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6Main
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiE6Lift

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiE6Sc
  CFSG.SeitzReduction CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false



section Natural

variable {M L : Type} [Field M] [Field L] (ι : M →+* L)

theorem a2Equiv₁_symm_map (A : SL(3, M)) :
    (((a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.map ι A) :
        ↥(subsystemGroup Tag.E6 L support13)) : ModGL Tag.E6 L) =
      baseChangeGL ι (((a2Equiv₁ M).symm A : ↥(subsystemGroup Tag.E6 M support13)) :
        ModGL Tag.E6 M) := by
  have hmem := baseChangeGL_mem_subsystemGroupE6 ι ((a2Equiv₁ M).symm A).2
  have h : (a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.map ι A) =
      ⟨baseChangeGL ι (((a2Equiv₁ M).symm A : ↥(subsystemGroup Tag.E6 M support13)) :
        ModGL Tag.E6 M), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [a2Equiv₁_apply, coe_a2Rep₁]
    show _ = a2Mat₁ (baseChangeGL ι (((a2Equiv₁ M).symm A : ↥(subsystemGroup Tag.E6 M support13)) :
        ModGL Tag.E6 M))
    rw [a2Mat₁_baseChangeGL ι ((a2Equiv₁ M).symm A).2]
    have h2 := congrArg (fun z : SL(3, M) => (z : Matrix (Fin 3) (Fin 3) M))
      ((a2Equiv₁ M).apply_symm_apply A)
    simp only [a2Equiv₁_apply, coe_a2Rep₁] at h2
    rw [h2]
    rfl
  rw [h]

theorem a2Equiv₂_symm_map (A : SL(3, M)) :
    (((a2Equiv₂ L).symm (Matrix.SpecialLinearGroup.map ι A) :
        ↥(subsystemGroup Tag.E6 L support56)) : ModGL Tag.E6 L) =
      baseChangeGL ι (((a2Equiv₂ M).symm A : ↥(subsystemGroup Tag.E6 M support56)) :
        ModGL Tag.E6 M) := by
  have hmem := baseChangeGL_mem_subsystemGroupE6 ι ((a2Equiv₂ M).symm A).2
  have h : (a2Equiv₂ L).symm (Matrix.SpecialLinearGroup.map ι A) =
      ⟨baseChangeGL ι (((a2Equiv₂ M).symm A : ↥(subsystemGroup Tag.E6 M support56)) :
        ModGL Tag.E6 M), hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [a2Equiv₂_apply, coe_a2Rep₂]
    show _ = a2Mat₂ (baseChangeGL ι (((a2Equiv₂ M).symm A : ↥(subsystemGroup Tag.E6 M support56)) :
        ModGL Tag.E6 M))
    rw [a2Mat₂_baseChangeGL ι ((a2Equiv₂ M).symm A).2]
    have h2 := congrArg (fun z : SL(3, M) => (z : Matrix (Fin 3) (Fin 3) M))
      ((a2Equiv₂ M).apply_symm_apply A)
    simp only [a2Equiv₂_apply, coe_a2Rep₂] at h2
    rw [h2]
    rfl
  rw [h]

theorem twoA2Mul_natural (s : SL(3, M) × SL(3, M)) :
    twoA2Mul L (Matrix.SpecialLinearGroup.map ι s.1, Matrix.SpecialLinearGroup.map ι s.2) =
      baseChangeGL ι (twoA2Mul M s) := by
  obtain ⟨A, B⟩ := s
  rw [twoA2Mul_apply, twoA2Mul_apply, map_mul, a2Equiv₁_symm_map, a2Equiv₂_symm_map]

end Natural

section Compat

theorem mem_center_of_twoA2Mul_eq_one {L : Type} [Field L] {s : SL(3, L) × SL(3, L)}
    (h : twoA2Mul L s = 1) : s ∈ Subgroup.center (SL(3, L) × SL(3, L)) := by
  obtain ⟨A, B⟩ := s
  obtain ⟨l, hl, hA, hB⟩ := (twoA2Mul_eq_one_iff A B).1 h
  have hA' : A ∈ Subgroup.center SL(3, L) :=
    Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨l, by rw [Fintype.card_fin]; exact hl, hA.symm⟩
  have hB' : B ∈ Subgroup.center SL(3, L) :=
    Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨l, by rw [Fintype.card_fin]; exact hl, hB.symm⟩
  rw [Subgroup.mem_center_iff]
  rintro ⟨X, Y⟩
  exact Prod.ext (Subgroup.mem_center_iff.1 hA' X) (Subgroup.mem_center_iff.1 hB' Y)

theorem hom_eq_of_perfect {S T : Type*} [Group S] [Group T] (hS : Group.IsPerfect S)
    (u v : S →* T) (h : ∀ s, u s * (v s)⁻¹ ∈ Subgroup.center T) : u = v := by
  have hrel : ∀ s, u s = v s * (u s * (v s)⁻¹) := fun s => by
    have := Subgroup.mem_center_iff.1 (h s) (v s)
    calc u s = (u s * (v s)⁻¹) * v s := by group
      _ = v s * (u s * (v s)⁻¹) := this.symm
  have hcomm : ∀ s t : S, u ⁅s, t⁆ = v ⁅s, t⁆ := by
    intro s t
    rw [map_commutatorElement, map_commutatorElement, hrel s, hrel t,
      CFSG.RankThree.Classical.SteinbergBY.commutatorElement_mul_center _ _ (h s) (h t)]
  have hE : commutator S ≤ MonoidHom.eqLocus u v := by
    rw [commutator_def]
    exact Subgroup.commutator_le.2 fun p _ q _ => hcomm p q
  rw [hS.commutator_eq_top] at hE
  ext s
  exact hE (Subgroup.mem_top s)

theorem hom_eq_of_perfect_prod {A T : Type*} [Group A] [Group T] (hA : Group.IsPerfect A)
    (u v : A × A →* T) (h : ∀ s, u s * (v s)⁻¹ ∈ Subgroup.center T) : u = v := by
  have h1 : u.comp (MonoidHom.inl A A) = v.comp (MonoidHom.inl A A) :=
    hom_eq_of_perfect hA _ _ (fun p => h (p, 1))
  have h2 : u.comp (MonoidHom.inr A A) = v.comp (MonoidHom.inr A A) :=
    hom_eq_of_perfect hA _ _ (fun q => h (1, q))
  ext ⟨p, q⟩
  have e : ((p, q) : A × A) = (p, 1) * (1, q) := by simp
  have a1 := congrArg (fun f => f p) h1
  have a2 := congrArg (fun f => f q) h2
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at a1 a2
  rw [e, map_mul, map_mul, a1, a2]

@[expose] def sigmaL {L : Type} [Field L] (Fr : L →+* L) (a b : SL(3, L)) :
    SL(3, L) × SL(3, L) →* SL(3, L) × SL(3, L) :=
  ((MulAut.conj a).toMonoidHom.comp ((Matrix.SpecialLinearGroup.map Fr).comp
    (MonoidHom.snd SL(3, L) SL(3, L)))).prod
    ((MulAut.conj b).toMonoidHom.comp ((Matrix.SpecialLinearGroup.map Fr).comp
      (MonoidHom.fst SL(3, L) SL(3, L))))

theorem sigmaL_apply {L : Type} [Field L] (Fr : L →+* L) (a b : SL(3, L))
    (s : SL(3, L) × SL(3, L)) :
    sigmaL Fr a b s = (a * Matrix.SpecialLinearGroup.map Fr s.2 * a⁻¹,
      b * Matrix.SpecialLinearGroup.map Fr s.1 * b⁻¹) := rfl

@[expose] def baseS {M L : Type} [Field M] [Field L] (ι : M →+* L) :
    SL(3, M) × SL(3, M) →* SL(3, L) × SL(3, L) :=
  (Matrix.SpecialLinearGroup.map ι).prodMap (Matrix.SpecialLinearGroup.map ι)

theorem baseS_apply {M L : Type} [Field M] [Field L] (ι : M →+* L) (s : SL(3, M) × SL(3, M)) :
    baseS ι s = (Matrix.SpecialLinearGroup.map ι s.1, Matrix.SpecialLinearGroup.map ι s.2) := rfl

theorem bc_entrywise {M L : Type} [Field M] [Field L] (ι : M →+* L) (Fr : L →+* L)
    (σM : M →+* M) (h : ι.comp σM = Fr.comp ι) (x : ModGL Tag.E6 M) :
    baseChangeGL ι (Units.map (entrywiseHom σM) x) =
      Units.map (entrywiseHom Fr) (baseChangeGL ι x) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h]

theorem sigmaL_compat {M L : Type} [Field M] [Finite M] [Field L] (ι : M →+* L)
    (Fr : L →+* L) (σM : M →+* M) (hισ : ι.comp σM = Fr.comp ι) (a b : SL(3, L))
    (hab : ∀ A B : SL(3, L), twoA2Mul L (sigmaL Fr a b (A, B)) =
      canonicalRep (coxeterSystem Tag.E6) L wE6 * Units.map (entrywiseHom Fr) (twoA2Mul L (A, B)) *
        (canonicalRep (coxeterSystem Tag.E6) L wE6)⁻¹)
    (s : SL(3, M) × SL(3, M)) :
    sigmaL Fr a b (baseS ι s) = baseS ι (sigmaHat σM s) := by
  have hperf : Group.IsPerfect SL(3, M) :=
    (isQuasisimple_specialLinearGroup (K := M) (n := 3) le_rfl).1
  have hmu : ∀ s : SL(3, M) × SL(3, M),
      twoA2Mul L (sigmaL Fr a b (baseS ι s)) = twoA2Mul L (baseS ι (sigmaHat σM s)) := by
    intro s
    have h1 := hab (baseS ι s).1 (baseS ι s).2
    rw [show ((baseS ι s).1, (baseS ι s).2) = baseS ι s from rfl] at h1
    rw [h1, baseS_apply, baseS_apply]
    rw [twoA2Mul_natural ι s, twoA2Mul_natural ι (sigmaHat σM s), twoA2Mul_sigmaHat,
      sigmaGL_apply]
    rw [map_mul, map_mul, map_inv, CFSG.RankThree.Chevalley.baseChangeGL_canonicalRep ι wE6,
      bc_entrywise ι Fr σM hισ]
  have hcen : ∀ s : SL(3, M) × SL(3, M),
      ((sigmaL Fr a b).comp (baseS ι)) s * (((baseS ι).comp (sigmaHat σM)) s)⁻¹ ∈
        Subgroup.center (SL(3, L) × SL(3, L)) := by
    intro s
    apply mem_center_of_twoA2Mul_eq_one
    show twoA2Mul L (sigmaL Fr a b (baseS ι s) * (baseS ι (sigmaHat σM s))⁻¹) = 1
    rw [map_mul, map_inv, hmu s, mul_inv_cancel]
  have := hom_eq_of_perfect_prod hperf _ _ hcen
  exact congrArg (fun f => f s) this

theorem lift_core {K M L : Type} [Field K] [Finite K] [Field M] [Finite M] [Field L]
    (κ : K →+* M) (ι : M →+* L) (ρ : K →+* L) (hικ : ι.comp κ = ρ) (Fr : L →+* L) (σM : M →+* M)
    (hισ : ι.comp σM = Fr.comp ι) (hσκ : σM.comp κ = κ) (x₀ : ModGL Tag.E6 K)
    (hx₀ : x₀ ∈ adjointGroup Tag.E6 K) (g₀ : ModGL Tag.E6 M) (hg₀ : g₀ ∈ adjointGroup Tag.E6 M)
    (g : ModGL Tag.E6 L) (hg₀e : baseChangeGL ι g₀ = g)
    (hlangL : Units.map (entrywiseHom Fr) g = g * canonicalRep (coxeterSystem Tag.E6) L wE6)
    (a b : SL(3, L))
    (hab : ∀ A B : SL(3, L), twoA2Mul L (sigmaL Fr a b (A, B)) =
      canonicalRep (coxeterSystem Tag.E6) L wE6 * Units.map (entrywiseHom Fr) (twoA2Mul L (A, B)) *
        (canonicalRep (coxeterSystem Tag.E6) L wE6)⁻¹)
    (s₀ : SL(3, L) × SL(3, L)) (hs₀ : twoA2Mul L s₀ = g⁻¹ * baseChangeGL ρ x₀ * g)
    (A₀ B₀ : SL(3, M)) (hA₀ : Matrix.SpecialLinearGroup.map ι A₀ = s₀.1)
    (hB₀ : Matrix.SpecialLinearGroup.map ι B₀ = s₀.2) :
    ∃ s : SL(3, L) × SL(3, L), sigmaL Fr a b s = s ∧ twoA2Mul L s = g⁻¹ * baseChangeGL ρ x₀ * g := by
  have hlang : Units.map (entrywiseHom σM) g₀ = g₀ * canonicalRep (coxeterSystem Tag.E6) M wE6 := by
    apply baseChangeGL_injective ι
    rw [bc_entrywise ι Fr σM hισ, hg₀e, map_mul, hg₀e,
      CFSG.RankThree.Chevalley.baseChangeGL_canonicalRep ι wE6]
    exact hlangL
  have hsM : twoA2Mul M (A₀, B₀) = g₀⁻¹ * baseChangeGL κ x₀ * g₀ := by
    apply baseChangeGL_injective ι
    rw [← twoA2Mul_natural ι (A₀, B₀)]
    show twoA2Mul L (Matrix.SpecialLinearGroup.map ι A₀, Matrix.SpecialLinearGroup.map ι B₀) = _
    rw [hA₀, hB₀, show ((s₀.1, s₀.2) : SL(3, L) × SL(3, L)) = s₀ from rfl, hs₀, map_mul, map_mul,
      map_inv, hg₀e, baseChangeGL_baseChangeGL, hικ]
  obtain ⟨s', hs'μ, hs'fix⟩ := exists_fixed_pair κ σM hσκ hx₀ hg₀ hlang hsM
  refine ⟨baseS ι s', ?_, ?_⟩
  · have h := sigmaL_compat ι Fr σM hισ a b hab s'
    rw [h, hs'fix]
  · rw [baseS_apply]
    rw [twoA2Mul_natural ι s', hs'μ, map_mul, map_mul, map_inv, hg₀e,
      baseChangeGL_baseChangeGL, hικ]

theorem e6Sc : E6ScStatement := by
  intro K _ _ hK h3 D a b hab y hy
  classical
  obtain ⟨x₀, hx₀, rfl⟩ := D.mem_frameImage.1 hy
  obtain ⟨hx₀adj, hxQ⟩ := (D.frame_mem_iff _ x₀).1 hx₀
  have hyQ : D.g⁻¹ * baseChangeGL (algebraMap K D.L) x₀ * D.g ∈ QuasiE6X2.Q12 D.L := by
    rw [← QuasiE6X2.rootSpan_S₂]
    exact hxQ
  obtain ⟨s₀, hs₀⟩ := twoA2MulSup_surjective (Ω := D.L) ⟨_, hyQ⟩
  have hs₀' : twoA2Mul D.L s₀ = D.g⁻¹ * baseChangeGL (algebraMap K D.L) x₀ * D.g :=
    congrArg Subtype.val hs₀
  have hg : D.g ∈ adjointGroup TwClass.e6Six.tag D.L :=
    parabolicLevi_le_adjointGroup (τ := TwClass.e6Six.tag) (K := D.L) (Jθ _) D.g_mem
  obtain ⟨M, hMfin, ⟨A₀, B₀, hA₀, hB₀⟩, g₀, hg₀, hg₀e⟩ :=
    QuasiFin.exists_finite_subfield D s₀.1 s₀.2 hg
  haveI : Module.Finite K ↥M := hMfin
  haveI : Finite ↥M := Module.finite_of_finite K
  let ι : ↥M →+* D.L := (M.val : ↥M →+* D.L)
  let κ : K →+* ↥M := algebraMap K ↥M
  have hικ : ι.comp κ = algebraMap K D.L := RingHom.ext fun _ => rfl
  let σM : ↥M →+* ↥M := D.Fr.restrict M M (fun x hx => by rw [D.hFr]; exact pow_mem hx _)
  have hισ : ι.comp σM = D.Fr.comp ι := RingHom.ext fun _ => rfl
  have hσκ : σM.comp κ = κ := RingHom.ext fun c => ι.injective (by
    show D.Fr (algebraMap K D.L c) = algebraMap K D.L c
    exact congrArg (fun f => f c) D.Fr_comp_algebraMap)
  obtain ⟨s, hs, hsμ⟩ := lift_core κ ι (algebraMap K D.L) hικ D.Fr σM hισ hσκ x₀ hx₀adj g₀ hg₀
    D.g hg₀e D.lang a b (fun A B => hab A B) s₀ hs₀' A₀ B₀ hA₀ hB₀
  exact ⟨s, hs, hsμ⟩

end Compat

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiE6Lift

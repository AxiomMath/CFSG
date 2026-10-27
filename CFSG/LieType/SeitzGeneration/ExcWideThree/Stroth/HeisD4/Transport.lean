module

public import CFSG.RankThree.Chevalley.SteinbergBID4ThetaFixed
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis


section Torus

variable {L : Type} [Field L]

theorem rootChar_d4Lat (a : Fin Tag.E6.rank → Lˣ) (β : Fin Tag.D4.rank → ℤ) :
    rootChar a (d4Lat β) = rootChar (fun k : Fin Tag.D4.rank => a (d4Idx k)) β := by
  change (∏ i : Fin 6, a i ^ (d4Lat β) i) =
    ∏ i : Fin 4, a (d4Idx i) ^ β i
  rw [Fin.prod_univ_six, Fin.prod_univ_four]
  simp only [d4Lat, d4Idx]
  simp
  rfl


theorem rootDiagUnit_comp_d4Emb (a : Fin Tag.E6.rank → Lˣ) :
    ((rootDiagUnit Tag.E6 a : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) ∘ₗ d4Emb L =
      d4Emb L ∘ₗ ((rootDiagUnit Tag.D4 (fun k : Fin Tag.D4.rank => a (d4Idx k)) :
        ModGL Tag.D4 L) : Module.End L (RootModule Tag.D4 L)) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, d4Emb_single]
  change rootDiag a (Finsupp.single (d4Label b) 1) =
    d4Emb L (rootDiag (fun k : Fin Tag.D4.rank => a (d4Idx k)) (Finsupp.single b 1))
  have h : rootChar a (labelWt Tag.E6 (d4Label b)) =
      rootChar (fun k : Fin Tag.D4.rank => a (d4Idx k)) (labelWt Tag.D4 b) := by
    rcases b with k | β
    · simp [labelWt, d4Label, rootChar_zero]
    · exact rootChar_d4Lat a β.1
  rw [rootDiag_single, rootDiag_single, map_smul, d4Emb_single, h]

theorem rootDiagUnit_mem_d4Preserving (a : Fin Tag.E6.rank → Lˣ) :
    rootDiagUnit Tag.E6 a ∈ d4Preserving L :=
  ⟨rootDiagUnit Tag.D4 (fun k : Fin Tag.D4.rank => a (d4Idx k)), rootDiagUnit_comp_d4Emb a⟩

theorem d4PreservingRes_rootDiagUnit (a : Fin Tag.E6.rank → Lˣ) :
    d4PreservingRes L ⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_d4Preserving a⟩ =
      rootDiagUnit Tag.D4 (fun k : Fin Tag.D4.rank => a (d4Idx k)) :=
  d4PreservingRes_eq (rootDiagUnit_comp_d4Emb a)

theorem torusGroup_le_d4Preserving : torusGroup Tag.E6 L ≤ d4Preserving L := by
  intro h hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mem_d4Preserving l

theorem torus_sup_subsystem_le_d4Preserving :
    torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support ≤ d4Preserving L :=
  sup_le torusGroup_le_d4Preserving subsystemGroup_le_d4Preserving


theorem mapRange_d4Emb (σ : L →+* L) (x : RootModule Tag.D4 L) :
    Finsupp.mapRange σ σ.map_zero (d4Emb L x) = d4Emb L (Finsupp.mapRange σ σ.map_zero x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.mapRange_add (map_add σ), hx, hy, Finsupp.mapRange_add (map_add σ),
      map_add]
  | single b r =>
    rw [d4Emb_single, Finsupp.mapRange_single, Finsupp.mapRange_single, d4Emb_single]

theorem entrywise_comp_d4Emb (σ : L →+* L) {g : Module.End L (RootModule Tag.E6 L)}
    {g' : Module.End L (RootModule Tag.D4 L)} (h : g ∘ₗ d4Emb L = d4Emb L ∘ₗ g') :
    entrywise σ g ∘ₗ d4Emb L = d4Emb L ∘ₗ entrywise σ g' := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, d4Emb_single]
  rw [entrywise_single, entrywise_single, ← mapRange_d4Emb]
  congr 1
  have := LinearMap.congr_fun h (Finsupp.single b 1)
  simp only [LinearMap.comp_apply, d4Emb_single] at this
  exact this

theorem units_map_mem_d4Preserving (σ : L →+* L) {g : ModGL Tag.E6 L} (hg : g ∈ d4Preserving L) :
    Units.map (entrywiseHom σ) g ∈ d4Preserving L := by
  obtain ⟨g', hg'⟩ := hg
  exact ⟨Units.map (entrywiseHom σ) g', entrywise_comp_d4Emb σ hg'⟩

theorem d4PreservingRes_units_map (σ : L →+* L) {g : ModGL Tag.E6 L} (hg : g ∈ d4Preserving L) :
    d4PreservingRes L ⟨Units.map (entrywiseHom σ) g, units_map_mem_d4Preserving σ hg⟩ =
      Units.map (entrywiseHom σ) (d4PreservingRes L ⟨g, hg⟩) :=
  d4PreservingRes_eq (entrywise_comp_d4Emb σ (d4PreservingRes_spec ⟨g, hg⟩))


theorem rootDiagUnit_conj_mem_subsystem (a : Fin Tag.E6.rank → Lˣ) {g : ModGL Tag.E6 L}
    (hg : g ∈ subsystemGroup Tag.E6 L d4Support) :
    rootDiagUnit Tag.E6 a * g * (rootDiagUnit Tag.E6 a)⁻¹ ∈ subsystemGroup Tag.E6 L d4Support := by
  have hle : subsystemGroup Tag.E6 L d4Support ≤ (subsystemGroup Tag.E6 L d4Support).comap
      (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation Tag.E6 L a).1]
      exact xUnit_mem_subsystemGroup hi _
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation Tag.E6 L a).2.1]
      exact yUnit_mem_subsystemGroup hi _
  exact hle hg

theorem torusGroup_le_normalizer_subsystem :
    torusGroup Tag.E6 L ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 L d4Support : Set (ModGL Tag.E6 L)) := by
  intro h hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => rootDiagUnit_conj_mem_subsystem l hg, fun hg => ?_⟩
  have h1 := rootDiagUnit_conj_mem_subsystem l⁻¹ hg
  have e : rootDiagUnit Tag.E6 l⁻¹ * (rootDiagUnit Tag.E6 l * g * (rootDiagUnit Tag.E6 l)⁻¹) *
      (rootDiagUnit Tag.E6 l⁻¹)⁻¹ = g := by
    rw [← rootDiagUnit_inv]
    group
  rwa [e] at h1

theorem torus_sup_subsystem_le_normalizer :
    torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 L d4Support : Set (ModGL Tag.E6 L)) :=
  sup_le torusGroup_le_normalizer_subsystem Subgroup.le_normalizer

theorem coe_d4Triality_pow (e : ℕ) (g : subsystemGroup Tag.E6 L d4Support) :
    (((d4Triality L ^ e : MulAut (subsystemGroup Tag.E6 L d4Support)) g :
      subsystemGroup Tag.E6 L d4Support) : ModGL Tag.E6 L) =
      d4TrialityRep L ^ e * (g : ModGL Tag.E6 L) * (d4TrialityRep L ^ e)⁻¹ := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', MulAut.mul_apply, coe_d4Triality, ih, pow_succ']
    group


theorem d4Res_conj_y {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support) (ε : ℕ)
    (h : subsystemGroup Tag.E6 L d4Support) :
    ∃ h' : subsystemGroup Tag.E6 L d4Support,
      (h' : ModGL Tag.E6 L) = (m * d4TrialityRep L ^ ε) * h * (m * d4TrialityRep L ^ ε)⁻¹ ∧
      d4Res L h' =
        (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ * d4DiagramMap L ^ ε) *
          d4Res L h *
          (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ *
            d4DiagramMap L ^ ε)⁻¹ := by
  set h₁ := (d4Triality L ^ ε : MulAut (subsystemGroup Tag.E6 L d4Support)) h with hh₁def
  have hh₁ : (h₁ : ModGL Tag.E6 L) = d4TrialityRep L ^ ε * (h : ModGL Tag.E6 L) *
      (d4TrialityRep L ^ ε)⁻¹ := coe_d4Triality_pow ε h
  have hmN := torus_sup_subsystem_le_normalizer hm
  have hmem : m * (h₁ : ModGL Tag.E6 L) * m⁻¹ ∈ subsystemGroup Tag.E6 L d4Support :=
    (Subgroup.mem_normalizer_iff.1 hmN _).1 h₁.2
  refine ⟨⟨m * h₁ * m⁻¹, hmem⟩, ?_, ?_⟩
  · show m * (h₁ : ModGL Tag.E6 L) * m⁻¹ = _
    rw [hh₁]
    group
  · have e : d4Res L ⟨m * h₁ * m⁻¹, hmem⟩ =
        d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ * d4Res L h₁ *
          (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩)⁻¹ := by
      have e1 : Subgroup.inclusion subsystemGroup_le_d4Preserving
          (⟨m * h₁ * m⁻¹, hmem⟩ : subsystemGroup Tag.E6 L d4Support) =
          (⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ : d4Preserving L) *
            Subgroup.inclusion subsystemGroup_le_d4Preserving h₁ *
            (⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ : d4Preserving L)⁻¹ := Subtype.ext rfl
      show d4PreservingRes L (Subgroup.inclusion subsystemGroup_le_d4Preserving
        (⟨m * h₁ * m⁻¹, hmem⟩ : subsystemGroup Tag.E6 L d4Support)) = _
      rw [e1, map_mul, map_mul, map_inv]
      rfl
    rw [e, hh₁def, d4Res_d4Triality_pow]
    group

end Torus

section AlgClosed

variable {L : Type} [Field L] [IsAlgClosed L]

theorem rootDiagUnit_D4_mem_adjointGroup (c : Fin Tag.D4.rank → Lˣ) :
    rootDiagUnit Tag.D4 c ∈ adjointGroup Tag.D4 L := by
  have hsq : ∀ u : Lˣ, ∃ v : Lˣ, v ^ 2 = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (by norm_num : 0 < 2)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hz]; simp)
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose b hb using hsq
  have h := CFSG.HardMathSupport.Lang.D4Three.rootDiagUnit_sq_mem_adjointGroup_D4 (K := L)
    (fun j : Fin 4 => b (c j))
  have e : (fun j : Fin 4 => b (c j) ^ 2) = c := funext fun j => hb (c j)
  rw [e] at h
  exact h

theorem d4PreservingRes_torus_sup_mem_adjoint {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support) :
    d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ ∈ adjointGroup Tag.D4 L := by
  set H : Subgroup (ModGL Tag.E6 L) :=
    ((adjointGroup Tag.D4 L).comap (d4PreservingRes L)).map (d4Preserving L).subtype with hH
  have hmemH : ∀ g (hg : g ∈ d4Preserving L),
      d4PreservingRes L ⟨g, hg⟩ ∈ adjointGroup Tag.D4 L → g ∈ H := fun g hg h =>
    ⟨⟨g, hg⟩, h, rfl⟩
  have hHmem : ∀ g, g ∈ H → ∀ hg : g ∈ d4Preserving L,
      d4PreservingRes L ⟨g, hg⟩ ∈ adjointGroup Tag.D4 L := by
    rintro g ⟨g', hg', rfl⟩ hg
    exact hg'
  have hle : torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support ≤ H := by
    refine sup_le (fun h hh => ?_) (fun g hg => ?_)
    · obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      refine hmemH _ (rootDiagUnit_mem_d4Preserving l) ?_
      rw [d4PreservingRes_rootDiagUnit]
      exact rootDiagUnit_D4_mem_adjointGroup _
    · refine hmemH _ (subsystemGroup_le_d4Preserving hg) ?_
      exact d4Res_mem_adjointGroup ⟨g, hg⟩
  exact hHmem m (hle hm) _

end AlgClosed


section Descent

variable {K L : Type} [Field K] [Finite K] [Field L] [IsAlgClosed L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

theorem exists_gamma_descent (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support)
    (hmF : Units.map (entrywiseHom Fr) m = m) :
    ∃ (b : Fin Tag.D4.rank → Kˣ) (j : ModGL Tag.D4 K), j ∈ adjointGroup Tag.D4 K ∧
      d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ =
        baseChangeGL (algebraMap K L) (rootDiagUnit Tag.D4 b * j) := by
  have hγ := d4PreservingRes_torus_sup_mem_adjoint hm
  have hγF : Units.map (entrywiseHom Fr)
      (d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩) =
      d4PreservingRes L ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ := by
    have h := d4PreservingRes_units_map Fr (torus_sup_subsystem_le_d4Preserving hm)
    have e : (⟨Units.map (entrywiseHom Fr) m, units_map_mem_d4Preserving Fr
        (torus_sup_subsystem_le_d4Preserving hm)⟩ : d4Preserving L) =
        ⟨m, torus_sup_subsystem_le_d4Preserving hm⟩ := Subtype.ext hmF
    rw [e] at h
    exact h.symm
  obtain ⟨b, u, hu, hbu⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_mul_of_frobenius_fixed
    Tag.D4 Fr hFr hγ hγF
  obtain ⟨j, hj, rfl⟩ := hu
  exact ⟨b, j, hj, by rw [hbu, map_mul]⟩

end Descent

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

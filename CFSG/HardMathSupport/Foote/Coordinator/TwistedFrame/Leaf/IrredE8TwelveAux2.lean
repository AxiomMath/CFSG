module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux1
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w)

@[expose] def frobGL : ModGL Tag.E8 D.L →* ModGL Tag.E8 D.L := Units.map (entrywiseHom D.Fr)

@[expose] def nW : ModGL Tag.E8 D.L := canonicalRep (coxeterSystem Tag.E8) D.L w

theorem frobGL_baseChange (x : ModGL Tag.E8 K) :
    frobGL D (baseChangeGL (algebraMap K D.L) x) = baseChangeGL (algebraMap K D.L) x :=
  units_map_entrywiseHom_baseChangeGL_algebraMap D.Fr D.hFr x

theorem frobGL_conj_g (u : ModGL Tag.E8 D.L) :
    frobGL D (D.g * u * D.g⁻¹) = D.g * (nW D * frobGL D u * (nW D)⁻¹) * D.g⁻¹ := by
  have hg : frobGL D D.g = D.g * nW D := D.lang
  rw [map_mul, map_mul, map_inv, hg]
  group

theorem frobGL_conj_g_inv_baseChange (x : ModGL Tag.E8 K) :
    frobGL D (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) =
      (nW D)⁻¹ * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g) * nW D := by
  have hg : frobGL D D.g = D.g * nW D := D.lang
  rw [map_mul, map_mul, map_inv, hg, frobGL_baseChange]
  group

theorem exists_rational_Qθ {u : ModGL Tag.E8 D.L} (hu : u ∈ Qθ Tag.E8 D.L)
    (hσ : nW D * frobGL D u * (nW D)⁻¹ = u) :
    ∃ r ∈ Qθ Tag.E8 K, baseChangeGL (algebraMap K D.L) r = D.g * u * D.g⁻¹ := by
  have hgP : D.g ∈ Pθ Tag.E8 D.L := parabolicLevi_le_parabolicSubgroup _ D.g_mem
  have hx : D.g * u * D.g⁻¹ ∈ Qθ Tag.E8 D.L :=
    (Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical _ hgP) u).1 hu
  have hF : frobGL D (D.g * u * D.g⁻¹) = D.g * u * D.g⁻¹ := by rw [frobGL_conj_g, hσ]
  exact fixed_Qθ_rational D.Fr D.hFr hx hF

private theorem finite_setOf_frobGL_eq : {z : ModGL Tag.E8 D.L | frobGL D z = z}.Finite := by
  classical
  let φ : ModGL Tag.E8 D.L → Label Tag.E8 → Label Tag.E8 → D.L := fun z b l =>
    ((z : Module.End D.L (RootModule Tag.E8 D.L)) (Finsupp.single b 1)) l
  have hφ : Function.Injective φ := fun z z' h =>
    Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring
      (Finsupp.ext fun l => congrFun (congrFun h b) l))
  have hsub : {z : ModGL Tag.E8 D.L | frobGL D z = z} ⊆
      φ ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.range (algebraMap K D.L)) := by
    intro z hz b _ l _
    have h1 := congrArg (fun A : ModGL Tag.E8 D.L =>
      ((A : Module.End D.L (RootModule Tag.E8 D.L)) (Finsupp.single b 1)) l) hz
    change (entrywise D.Fr (z : Module.End D.L (RootModule Tag.E8 D.L))
      (Finsupp.single b 1)) l = _ at h1
    rw [entrywise_single, Finsupp.mapRange_apply] at h1
    exact CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq
      (by rw [← D.hFr]; exact h1)
  exact ((Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_range _).preimage
    hφ.injOn).subset hsub

private theorem exists_rational_of_frobGL_eq {y : ModGL Tag.E8 D.L}
    (hyC : y ∈ adjointGroup Tag.E8 D.L) (hyF : frobGL D y = y) :
    ∃ l ∈ adjointGroup Tag.E8 K, baseChangeGL (algebraMap K D.L) l = y := by
  haveI : Algebra.IsAlgebraic K D.L := IsAlgClosure.isAlgebraic
  have hXF : ∀ z ∈ Subgroup.zpowers y, Units.map (entrywiseHom D.Fr) z = z := by
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    show frobGL D (y ^ n) = y ^ n
    rw [map_zpow, hyF]
  haveI : Finite (Subgroup.zpowers y) :=
    Set.Finite.to_subtype ((finite_setOf_frobGL_eq D).subset fun z hz => hXF z hz)
  have h := (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) D.Fr D.hFr (Subgroup.zpowers y)
    ((Subgroup.zpowers_le).2 hyC) hXF).1
  rw [Nat.dvd_one] at h
  exact Subgroup.mem_map.1 (Subgroup.relIndex_eq_one.1 h (Subgroup.mem_zpowers y))

private theorem conj_mem_rootSubgroup_of_baseChange {l : ModGL Tag.E8 K}
    {α : Fin Tag.E8.rank → ℤ}
    (hn : baseChangeGL (algebraMap K D.L) l ∈
      Subgroup.normalizer (rootSubgroup Tag.E8 D.L α : Set (ModGL Tag.E8 D.L)))
    {y : ModGL Tag.E8 K} (hy : y ∈ rootSubgroup Tag.E8 K α) :
    l * y * l⁻¹ ∈ rootSubgroup Tag.E8 K α := by
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hy
  have h1 : baseChangeGL (algebraMap K D.L) (l * pinnedX Tag.E8 K α t * l⁻¹) ∈
      rootSubgroup Tag.E8 D.L α := by
    rw [map_mul, map_mul, map_inv, baseChangeGL_pinnedX]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 (mem_rootSubgroup.2 ⟨_, rfl⟩)
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 h1
  have hF : D.Fr c' = c' := by
    apply pinnedX_injective Tag.E8 D.L α
    have e1 : frobGL D (pinnedX Tag.E8 D.L α c') = pinnedX Tag.E8 D.L α (D.Fr c') :=
      baseChangeGL_pinnedX D.Fr α c'
    rw [← e1, hc', frobGL_baseChange]
  obtain ⟨c, rfl⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K)
    (L := D.L) (c := c') (by rw [← D.hFr]; exact hF)
  refine mem_rootSubgroup.2 ⟨c, baseChangeGL_injective (algebraMap K D.L) ?_⟩
  rw [baseChangeGL_pinnedX, hc']

private theorem mem_Lθ_of_baseChange {l : ModGL Tag.E8 K} (hl : l ∈ adjointGroup Tag.E8 K)
    (hlL : baseChangeGL (algebraMap K D.L) l ∈ Lθ Tag.E8 D.L) : l ∈ Lθ Tag.E8 K := by
  have hlL' : baseChangeGL (algebraMap K D.L) l⁻¹ ∈ Lθ Tag.E8 D.L := by
    rw [map_inv]
    exact inv_mem hlL
  have hθ : baseChangeGL (algebraMap K D.L) l ∈
      Subgroup.normalizer (Uθ Tag.E8 D.L : Set (ModGL Tag.E8 D.L)) :=
    Pθ_le_normalizer_Uθ Tag.E8 D.L (parabolicLevi_le_parabolicSubgroup _ hlL)
  have hP : l ∈ Pθ Tag.E8 K := by
    refine mem_Pθ_of_conj_le Tag.E8 K hl ?_
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_rootSubgroup_of_baseChange D hθ hy
  have hN : l ∈ Pneg Tag.E8 K := by
    refine ⟨hl, Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact conj_mem_rootSubgroup_of_baseChange D (Lθ_le_normalizer_Uneg Tag.E8 D.L hlL) hy
    · have h := conj_mem_rootSubgroup_of_baseChange D
        (Lθ_le_normalizer_Uneg Tag.E8 D.L hlL') hy
      rwa [show l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y by group] at h
  exact Pθ_inf_Pneg_le_Lθ Tag.E8 K hP hN

theorem exists_rational_levi {u : ModGL Tag.E8 D.L} (hu : u ∈ Lθ Tag.E8 D.L)
    (hσ : nW D * frobGL D u * (nW D)⁻¹ = u) :
    ∃ l ∈ adjointGroup Tag.E8 K, l ∈ Lθ Tag.E8 K ∧
      baseChangeGL (algebraMap K D.L) l = D.g * u * D.g⁻¹ := by
  have hxL : D.g * u * D.g⁻¹ ∈ Lθ Tag.E8 D.L :=
    mul_mem (mul_mem D.g_mem hu) (inv_mem D.g_mem)
  have hxF : frobGL D (D.g * u * D.g⁻¹) = D.g * u * D.g⁻¹ := by rw [frobGL_conj_g, hσ]
  obtain ⟨l, hl, hlx⟩ := exists_rational_of_frobGL_eq D
    (parabolicLevi_le_adjointGroup Tag.E8 D.L _ hxL) hxF
  refine ⟨l, hl, mem_Lθ_of_baseChange D hl ?_, hlx⟩
  rw [hlx]
  exact hxL

theorem mem_frame_iff' (S : Set (Fin Tag.E8.rank → ℤ)) (x : ModGL Tag.E8 K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup Tag.E8 K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan Tag.E8 D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

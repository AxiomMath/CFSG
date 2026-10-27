module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoFrameElt
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoFactor
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoSolv
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FivePurityLang

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Close

variable
  {K : Type} [Field K] [Finite K]

@[expose] def cubeHom (L : Type) [Field L] [Algebra K L] (G : ModGL Tag.E8 L) :
    adjointGroup Tag.E8 K →* ModGL Tag.E8 L :=
  (MulAut.conj G⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E8 K).subtype)

theorem cubeHom_apply (L : Type) [Field L] [Algebra K L] (G : ModGL Tag.E8 L)
    (x : adjointGroup Tag.E8 K) :
    cubeHom L G x = G⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) * G := by
  simp [cubeHom, MulAut.conj_apply]

theorem cubeHom_injective (L : Type) [Field L] [Algebra K L] (G : ModGL Tag.E8 L) :
    Function.Injective (cubeHom (K := K) L G) := by
  intro x y h
  rw [cubeHom_apply, cubeHom_apply] at h
  have h2 : baseChangeGL (algebraMap K L) (x : ModGL Tag.E8 K) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) := by
    have := congrArg (fun t => G * t * G⁻¹) h
    simpa [mul_assoc] using this
  exact Subtype.ext (baseChangeGL_injective _ h2)

section Data

structure CubeData (E : Subgroup (adjointGroup Tag.E8 K)) where
  D : LangE8Ten K
  ζ : D.L
  hζ : IsPrimitiveRoot ζ 5
  ξ : ModGL Tag.E8 D.L
  s : ModGL Tag.E8 D.L
  hξ : ξ ∈ adjointGroup Tag.E8 D.L
  hξz : ξ * griessZ hζ = griessZ hζ * ξ
  z' : adjointGroup Tag.E8 K
  x' : adjointGroup Tag.E8 K
  y' : adjointGroup Tag.E8 K
  hz' : cubeHom D.L (D.g * ξ) z' = griessZ hζ
  hx' : cubeHom D.L (D.g * ξ) x' = griessX hζ
  hy' : cubeHom D.L (D.g * ξ) y' = s
  hE : E = Subgroup.closure ({z', x', y'} : Set (adjointGroup Tag.E8 K))
  basis : CubeBasis z' x' y'
  hA : HeisShape (rhoSigmaE8A4 D.L e8VA) (griessZ hζ) (griessX hζ) s
  hB : HeisShape (rhoSigmaE8A4 D.L e8VB) (griessZ hζ) (griessX hζ) s
  htA : HeisShape (rhoSigmaE8A4 D.L e8VA) (griessZ hζ) ((nU D.L)⁻¹ * griessZ hζ * nU D.L)
    ((nU D.L)⁻¹ * s * nU D.L)
  htB : HeisShape (rhoSigmaE8A4 D.L e8VB) (griessZ hζ) ((nU D.L)⁻¹ * griessZ hζ * nU D.L)
    ((nU D.L)⁻¹ * s * nU D.L)

section Line

theorem frames_le_hyperClosure_cube (hK5 : 5 ∣ Nat.card K + 1) (D : LangE8Ten K)
    {p q r : adjointGroup Tag.E8 K} (hb : CubeBasis p q r) (εp εq εr : ModGL Tag.E8 D.L)
    (hιp : baseChangeGL (algebraMap K D.L) (p : ModGL Tag.E8 K) = D.g * εp * D.g⁻¹)
    (hιq : baseChangeGL (algebraMap K D.L) (q : ModGL Tag.E8 K) = D.g * εq * D.g⁻¹)
    (hιr : baseChangeGL (algebraMap K D.L) (r : ModGL Tag.E8 K) = D.g * εr * D.g⁻¹)
    (hA : HeisShape (rhoSigmaE8A4 D.L e8VA) εp εq εr)
    (hB : HeisShape (rhoSigmaE8A4 D.L e8VB) εp εq εr) :
    TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤
      (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K))
        (Subgroup.closure ({p, q, r} : Set (adjointGroup Tag.E8 K)))).map
        (adjointGroup Tag.E8 K).subtype :=
  frames_le_hyperClosure hK5 D _ hb.card p q r εp εq εr (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hιp hιq hιr hA hB
    fun i j hij => hb.line i j hij

theorem g_mem_adjoint {K : Type} [Field K] [Finite K] (D : LangE8Ten K) :
    D.g ∈ adjointGroup Tag.E8 D.L :=
  parabolicLevi_le_adjointGroup (K := D.L) (τ := Tag.E8) _ D.g_mem

theorem griessZ_eq_mulSingle {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    griessZ hζ = rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU hζ)) := by
  rw [griessZ, powVec_czVec]

theorem map_conj_closure_triple {G : Type*} [Group G] (g a b c : G) :
    (Subgroup.closure ({a, b, c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹} : Set G) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

namespace CubeData

variable {E : Subgroup (adjointGroup Tag.E8 K)} (c : CubeData E)

theorem iota_eq {e : adjointGroup Tag.E8 K} {s : ModGL Tag.E8 c.D.L}
    (h : cubeHom c.D.L (c.D.g * c.ξ) e = s) :
    baseChangeGL (algebraMap K c.D.L) (e : ModGL Tag.E8 K) =
      c.D.g * (c.ξ * s * c.ξ⁻¹) * c.D.g⁻¹ := by
  rw [cubeHom_apply] at h
  rw [← h]
  group

theorem frames_le (hK5 : 5 ∣ Nat.card K + 1) :
    TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D ≤
      (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E).map
        (adjointGroup Tag.E8 K).subtype := by
  obtain ⟨⟨MA, hMA⟩, ⟨MB, hMB⟩⟩ := exists_actsBy_of_centralizer c.hζ c.hξ c.hξz
  have := frames_le_hyperClosure_cube hK5 c.D c.basis _ _ _ (c.iota_eq c.hz') (c.iota_eq c.hx')
    (c.iota_eq c.hy') (HeisShape.conj_of_actsBy hMA c.hA)
    (HeisShape.conj_of_actsBy hMB c.hB)
  rwa [← c.hE] at this

theorem exists_conj_x_z (hK5 : 5 ∣ Nat.card K + 1) :
    ∃ g : adjointGroup Tag.E8 K, g * c.x' * g⁻¹ = c.z' := by
  classical
  haveI : IsAlgClosed c.D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hq : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp5 : p ≠ 5 := by
    rintro rfl
    rw [hq] at hK5
    have h1 : 5 ∣ 5 ^ (m : ℕ) := dvd_pow_self 5 m.ne_zero
    have := (Nat.dvd_add_right h1).1 hK5
    omega
  haveI : CharP c.D.L p := charP_of_injective_algebraMap (algebraMap K c.D.L).injective p
  have hFr : c.D.Fr = iterateFrobenius c.D.L p m :=
    RingHom.ext fun x => by rw [c.D.hFr, hq, iterateFrobenius_def]
  have hFDz : entrywiseFrobGL Tag.E8 c.D.L p m c.D.g = c.D.g * c.D.nW := by
    have h := c.D.lang
    rw [hFr] at h
    exact h
  have hQd : c.D.nW * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU c.hζ)) *
      c.D.nW⁻¹ = rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU c.hζ)) ^ 4 := by
    rw [← griessZ_eq_mulSingle c.hζ]
    exact nW_conj_z c.D.L c.hζ
  have hz : baseChangeGL (algebraMap K c.D.L) (c.z' : ModGL Tag.E8 K) =
      c.D.g * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU c.hζ)) *
        c.D.g⁻¹ := by
    have e : c.ξ * griessZ c.hζ * c.ξ⁻¹ = griessZ c.hζ := by
      rw [c.hξz]
      group
    rw [c.iota_eq c.hz', e, griessZ_eq_mulSingle]
  have hP : c.D.g * c.ξ ∈ adjointGroup Tag.E8 c.D.L := mul_mem (g_mem_adjoint c.D) c.hξ
  have ha : rootDiagUnit Tag.E8 (fun k => griessU c.hζ ^ cxVec k) =
      (c.D.g * c.ξ)⁻¹ * baseChangeGL (algebraMap K c.D.L) (c.x' : ModGL Tag.E8 K) *
        (c.D.g * c.ξ) := by
    have h := c.hx'
    rw [cubeHom_apply] at h
    exact h.symm
  have hu : ∀ v : Fin Tag.E8.rank → ℤ, rootChar (fun k => griessU c.hζ ^ cxVec k) (uW • v) =
      rootChar (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU c.hζ)) v := fun v => by
    rw [uW_smul, ← powVec_czVec]
    exact rootChar_powVec_mulVec _ (griessU_prim c.hζ) cxVec czVec _ cx_u_data v
  exact lang_core_five hp5 m.pos hq (griessU c.hζ) (griessU_prim c.hζ).eq_orderOf.symm
    c.D.g c.D.nW (g_mem_adjoint c.D) (canonicalRep_mem_adjointGroup _ _ _) (s := 4)
    (by norm_num) hFDz hQd c.z' hz _ hP c.x' _ ha uW hu

theorem frames_le_conj (hK5 : 5 ∣ Nat.card K + 1) {g : adjointGroup Tag.E8 K}
    (hg : g * c.x' * g⁻¹ = c.z') :
    TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D ≤
      (hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K))
        (E.map (MulAut.conj g).toMonoidHom)).map (adjointGroup Tag.E8 K).subtype := by
  set D := c.D with hD
  set ι := baseChangeGL (algebraMap K D.L) with hι
  set c₁ : ModGL Tag.E8 D.L := D.g⁻¹ * ι (g : ModGL Tag.E8 K) * (D.g * c.ξ) * nU D.L with hc₁
  have hc₁G : c₁ ∈ adjointGroup Tag.E8 D.L := by
    refine mul_mem (mul_mem (mul_mem (inv_mem (g_mem_adjoint D))
      (baseChangeGL_mem_adjointGroup' _ g.2)) (mul_mem (g_mem_adjoint D) c.hξ))
      (canonicalRep_mem_adjointGroup _ _ _)
  have hF3 : ∀ (e : adjointGroup Tag.E8 K) (s : ModGL Tag.E8 D.L),
      cubeHom D.L (D.g * c.ξ) e = s →
      ι ((g * e * g⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        D.g * (c₁ * ((nU D.L)⁻¹ * s * nU D.L) * c₁⁻¹) * D.g⁻¹ := by
    intro e s hes
    rw [cubeHom_apply, ← hι] at hes
    have hie : ι (e : ModGL Tag.E8 K) = (D.g * c.ξ) * s * (D.g * c.ξ)⁻¹ := by
      rw [← hes]
      group
    have hgG : ι (g : ModGL Tag.E8 K) * (D.g * c.ξ) = D.g * c₁ * (nU D.L)⁻¹ := by
      rw [hc₁]
      group
    calc ι ((g * e * g⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)
        = ι (g : ModGL Tag.E8 K) * ι (e : ModGL Tag.E8 K) * (ι (g : ModGL Tag.E8 K))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      _ = (ι (g : ModGL Tag.E8 K) * (D.g * c.ξ)) * s *
            (ι (g : ModGL Tag.E8 K) * (D.g * c.ξ))⁻¹ := by
          rw [hie]
          group
      _ = D.g * (c₁ * ((nU D.L)⁻¹ * s * nU D.L) * c₁⁻¹) * D.g⁻¹ := by
          rw [hgG]
          group
  have hnx : (nU D.L)⁻¹ * griessX c.hζ * nU D.L = griessZ c.hζ := by
    rw [x_eq_conj_z D.L c.hζ]
    group
  have hc₁z : c₁ * griessZ c.hζ = griessZ c.hζ * c₁ := by
    have h1 := hF3 c.x' _ c.hx'
    rw [hg, c.iota_eq c.hz', hnx] at h1
    have e : c.ξ * griessZ c.hζ * c.ξ⁻¹ = griessZ c.hζ := by
      rw [c.hξz]
      group
    rw [e] at h1
    have h2 : griessZ c.hζ = c₁ * griessZ c.hζ * c₁⁻¹ := by
      have := mul_left_cancel (mul_right_cancel h1)
      exact this
    calc c₁ * griessZ c.hζ = (c₁ * griessZ c.hζ * c₁⁻¹) * c₁ := by group
      _ = griessZ c.hζ * c₁ := by rw [← h2]
  obtain ⟨⟨MA, hMA⟩, ⟨MB, hMB⟩⟩ := exists_actsBy_of_centralizer c.hζ hc₁G hc₁z
  have hb2 : CubeBasis (g * c.x' * g⁻¹) (g * c.z' * g⁻¹) (g * c.y' * g⁻¹) :=
    c.basis.swap.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have key := frames_le_hyperClosure_cube hK5 D hb2 (c₁ * griessZ c.hζ * c₁⁻¹)
    (c₁ * ((nU D.L)⁻¹ * griessZ c.hζ * nU D.L) * c₁⁻¹)
    (c₁ * ((nU D.L)⁻¹ * c.s * nU D.L) * c₁⁻¹)
    (by rw [hF3 c.x' _ c.hx', hnx]) (hF3 c.z' _ c.hz') (hF3 c.y' _ c.hy')
    (HeisShape.conj_of_actsBy hMA c.htA)
    (HeisShape.conj_of_actsBy hMB c.htB)
  have hcl : Subgroup.closure ({g * c.x' * g⁻¹, g * c.z' * g⁻¹, g * c.y' * g⁻¹} :
      Set (adjointGroup Tag.E8 K)) = E.map (MulAut.conj g).toMonoidHom := by
    have h1 := congrArg (fun H : Subgroup (adjointGroup Tag.E8 K) =>
      H.map (MulAut.conj g).toMonoidHom) c.hE
    rw [h1, map_conj_closure_triple, Set.insert_comm]
  rwa [hcl] at key

theorem isSolvable_centralizer_pair :
    Group.IsSolvable ↥(Subgroup.centralizer ({c.z', c.x'} : Set (adjointGroup Tag.E8 K))) := by
  have hGadj : (c.D.g * c.ξ) ∈ adjointGroup Tag.E8 c.D.L := mul_mem (g_mem_adjoint c.D) c.hξ
  have hmem : ∀ h : Subgroup.centralizer ({c.z', c.x'} : Set (adjointGroup Tag.E8 K)),
      cubeHom c.D.L (c.D.g * c.ξ) (h : adjointGroup Tag.E8 K) ∈
        familyCentralizer Tag.E8 c.D.L (planeFamily c.hζ) := by
    intro h
    rw [mem_familyCentralizer]
    refine ⟨?_, ?_⟩
    · rw [cubeHom_apply]
      exact mul_mem (mul_mem (inv_mem hGadj) (baseChangeGL_mem_adjointGroup' _ h.1.2)) hGadj
    · have hc := Subgroup.mem_centralizer_iff.1 h.2
      have key : ∀ (t : adjointGroup Tag.E8 K) (s : ModGL Tag.E8 c.D.L),
          t ∈ ({c.z', c.x'} : Set (adjointGroup Tag.E8 K)) →
          cubeHom c.D.L (c.D.g * c.ξ) t = s →
          s * cubeHom c.D.L (c.D.g * c.ξ) (h : adjointGroup Tag.E8 K) * s⁻¹ =
            cubeHom c.D.L (c.D.g * c.ξ) (h : adjointGroup Tag.E8 K) := by
        intro t s ht hts
        have := congrArg (cubeHom c.D.L (c.D.g * c.ξ)) (hc t ht)
        rw [map_mul, map_mul, hts] at this
        rw [this]
        group
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · rw [rootDiagUnit_planeFamily_zero]
        exact key c.z' _ (by simp) c.hz'
      · rw [rootDiagUnit_planeFamily_one]
        exact key c.x' _ (by simp) c.hx'
  let Ψ : Subgroup.centralizer ({c.z', c.x'} : Set (adjointGroup Tag.E8 K)) →*
      familyCentralizer Tag.E8 c.D.L (planeFamily c.hζ) :=
    ((cubeHom c.D.L (c.D.g * c.ξ)).comp (Subgroup.subtype _)).codRestrict _ hmem
  have hΨ : Function.Injective Ψ := by
    intro h h' hh
    have hh' : cubeHom c.D.L (c.D.g * c.ξ) (h : adjointGroup Tag.E8 K) =
        cubeHom c.D.L (c.D.g * c.ξ) (h' : adjointGroup Tag.E8 K) := congrArg Subtype.val hh
    exact Subtype.ext (cubeHom_injective _ _ hh')
  have hsolv := isSolvable_familyCentralizer_plane c.hζ
  exact Group.isSolvable_of_isSolvable_injective hΨ

end CubeData

theorem frameIn_le_of_le_map {A : Subgroup (ModGL Tag.E8 K)} {B : Subgroup (adjointGroup Tag.E8 K)}
    (h : A ≤ B.map (adjointGroup Tag.E8 K).subtype) : frameIn A ≤ B := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := h (Subgroup.mem_subgroupOf.1 hx)
  have : b = x := Subtype.ext hbx
  exact this ▸ hb

theorem hyperGen_of_cubeData (hK5 : 5 ∣ Nat.card K + 1) {E : Subgroup (adjointGroup Tag.E8 K)}
    (c : CubeData E) : HyperGen 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E := by
  obtain ⟨g, hg⟩ := c.exists_conj_x_z hK5
  have hz : baseChangeGL (algebraMap K c.D.L) (c.z' : ModGL Tag.E8 K) =
      c.D.g * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU c.hζ)) *
        c.D.g⁻¹ := by
    have e : c.ξ * griessZ c.hζ * c.ξ⁻¹ = griessZ c.hζ := by
      rw [c.hξz]
      group
    rw [c.iota_eq c.hz', e, griessZ_eq_mulSingle]
  have hX := closingFrame_twisted hK5 c.D (griessU c.hζ) (griessU_prim c.hζ).eq_orderOf.symm
    c.z' hz
  have hXH : frameIn (TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D) ≤
      hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E :=
    frameIn_le_of_le_map (c.frames_le hK5)
  have hX2 : frameIn (TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D) ≤
      hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K))
        (E.map (MulAut.conj g).toMonoidHom) :=
    frameIn_le_of_le_map (c.frames_le_conj hK5 hg)
  have hback : (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = E := by
    rw [Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  have hYH : (frameIn (TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D)).map
      (MulAut.conj g⁻¹).toMonoidHom ≤
      hyperClosure 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E := by
    refine (Subgroup.map_mono hX2).trans ?_
    have := map_hyperClosure_le (p := 5) (⊤ : Subgroup (adjointGroup Tag.E8 K))
      (E.map (MulAut.conj g).toMonoidHom) g⁻¹
    rwa [hback] at this
  have hgx : g⁻¹ * c.z' * g⁻¹⁻¹ = c.x' := by
    rw [← hg]
    group
  have hY : ClosingFrameAt c.x' ((frameIn (TwClass.e8Ten.X₁ c.D ⊔ TwClass.e8Ten.X₂ c.D)).map
      (MulAut.conj g⁻¹).toMonoidHom) := by
    exact (congrArg (fun a => ClosingFrameAt a ((frameIn (TwClass.e8Ten.X₁ c.D ⊔
      TwClass.e8Ten.X₂ c.D)).map (MulAut.conj g⁻¹).toMonoidHom)) hgx).mp (hX.conj g⁻¹)
  have hnot := not_le_normalizer_of_solvable_centralizer hX.centralizes hY.centralizes
    hX.normalizer_solvable hY.nonsolvable c.isSolvable_centralizer_pair
  have htop := hX.closing _ hXH fun hN => hnot (hYH.trans hN)
  exact hyperGen_iff_le.2 htop.ge

end Line

end Data

end Close

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

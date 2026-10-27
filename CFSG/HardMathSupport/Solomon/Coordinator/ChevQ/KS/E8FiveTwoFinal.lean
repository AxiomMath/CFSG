module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoMono
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoToral
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveFrameData

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
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.StandardType.ExcFramesHalf
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Final


theorem exists_conj_to_zD {K : Type} [Field K] [Finite K] (hK5 : 5 ∣ Nat.card K + 1)
    (D : LangE8Ten K) {ζ : D.L} (hζ : IsPrimitiveRoot ζ 5) {P : ModGL Tag.E8 D.L}
    (hP : P ∈ adjointGroup Tag.E8 D.L) {z₀ zD : adjointGroup Tag.E8 K}
    (hz₀ : baseChangeGL (algebraMap K D.L) (z₀ : ModGL Tag.E8 K) = P * griessZ hζ * P⁻¹)
    (hzD : baseChangeGL (algebraMap K D.L) (zD : ModGL Tag.E8 K) =
      D.g * griessZ hζ * D.g⁻¹) :
    ∃ g : adjointGroup Tag.E8 K, g * z₀ * g⁻¹ = zD := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
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
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  have hFr : D.Fr = iterateFrobenius D.L p m :=
    RingHom.ext fun x => by rw [D.hFr, hq, iterateFrobenius_def]
  have hFDz : entrywiseFrobGL Tag.E8 D.L p m D.g = D.g * D.nW := by
    have h := D.lang
    rw [hFr] at h
    exact h
  have hQd : D.nW * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU hζ)) *
      D.nW⁻¹ = rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) (griessU hζ)) ^ 4 := by
    rw [← griessZ_eq_mulSingle hζ]
    exact nW_conj_z D.L hζ
  exact lang_core_five hp5 m.pos hq (griessU hζ) (griessU_prim hζ).eq_orderOf.symm
    D.g D.nW (g_mem_adjoint D) (canonicalRep_mem_adjointGroup _ _ _) (s := 4) (by norm_num)
    hFDz hQd zD (by rw [hzD, griessZ_eq_mulSingle]) P hP z₀ _
    (by rw [hz₀, ← griessZ_eq_mulSingle hζ]; group) 1 (fun v => by rw [one_smul])

end Final

end Two

section Main

open Two CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.StandardType.ExcFramesHalf
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess


theorem e8TwoFiveNonToral_holds : E8TwoFiveNonToral := by
  intro K _ _ hK5 E₀ hE₀ hcard _hN hempty
  classical
  have hnd : ¬ 5 ∣ Nat.card K := by omega
  obtain ⟨Fr, hFr, g, hg, hlang⟩ := exists_langLevi_algebraicClosure TwClass.e8Ten.tag K
    TwClass.e8Ten.w e8Ten_w_theta
  let D : LangE8Ten K := ⟨AlgebraicClosure K, Fr, hFr, g, hg, hlang⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨ω, hω⟩ := exists_fifth_root_langLevi K hnd D
  have hζ : IsPrimitiveRoot (ω : D.L) 5 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hω)
  have h5 : (5 : D.L) ≠ 0 := by simpa using natCast_five_ne_zero (K := K) hnd
  have hEc : ∀ e ∈ E₀, ∀ e' ∈ E₀, e * e' = e' * e := fun e he e' he' =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  have hE5 : ∀ e ∈ E₀, e ^ 5 = 1 := hE₀.2
  have hQ : IsPGroup 5 E₀ := IsPGroup.of_card (n := 3) hcard
  obtain ⟨γ, hγ, hγz⟩ := exists_conj_commute_z hK5 hζ hQ
  have hnt₀ : ¬ IsToralSubgroup Tag.E8 D.L (E₀.map (cubeHom D.L 1)) := by
    rintro ⟨g', hg', hgt⟩
    refine hempty.false (nonempty_langPlaneData_of_toral Nat.prime_five hnd E₀ hE5
      ⟨g', hg', fun x hx => ?_⟩).some
    have := hgt _ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    simpa [cubeHom_apply] using this
  have hnt₁ : ¬ IsToralSubgroup Tag.E8 D.L (E₀.map (cubeHom D.L γ⁻¹)) := by
    refine not_isToralSubgroup_of_conj (w := γ⁻¹) (inv_mem hγ) (fun y hy => ?_) hnt₀
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨x, hx, by simp [cubeHom_apply]⟩
  obtain ⟨z₀, hz₀E, hz₀⟩ := exists_pure_of_nontoral h5 hζ (inv_mem hγ) hE5 hEc hcard
    (fun t ht => by simpa [cubeHom_apply] using hγz t ht) hnt₁
  obtain ⟨zD, hzD'⟩ : ∃ zD : adjointGroup Tag.E8 K,
      baseChangeGL (algebraMap K D.L) (zD : ModGL Tag.E8 K) = D.g * griessZ hζ * D.g⁻¹ := by
    obtain ⟨zD, hzD, -, -, -⟩ := e8TwistedFrame_of K hK5 D (griessU hζ)
      (griessU_prim hζ).eq_orderOf.symm
    exact ⟨zD, hzD.trans (congrArg (fun t => D.g * t * D.g⁻¹) (griessZ_eq_mulSingle hζ).symm)⟩
  have hz₀' : baseChangeGL (algebraMap K D.L) (z₀ : ModGL Tag.E8 K) =
      γ⁻¹ * griessZ hζ * γ⁻¹⁻¹ := by
    have h := hz₀
    rw [cubeHom_apply] at h
    rw [← h]
    group
  obtain ⟨k, hk⟩ := exists_conj_to_zD hK5 D hζ (inv_mem hγ) hz₀' hzD'
  set E : Subgroup (adjointGroup Tag.E8 K) := E₀.map (MulAut.conj k).toMonoidHom with hE
  have hEmem : ∀ y ∈ E, ∃ x ∈ E₀, y = k * x * k⁻¹ := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hE5' : ∀ e ∈ E, e ^ 5 = 1 := fun e he => by
    obtain ⟨x, hx, rfl⟩ := hEmem e he
    have h := conj_pow (a := k) (b := x) (i := 5)
    rw [h, hE5 x hx]
    group
  have hEc' : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := fun e he e' he' => by
    obtain ⟨x, hx, rfl⟩ := hEmem e he
    obtain ⟨x', hx', rfl⟩ := hEmem e' he'
    calc k * x * k⁻¹ * (k * x' * k⁻¹) = k * (x * x') * k⁻¹ := by group
      _ = k * (x' * x) * k⁻¹ := by rw [hEc x hx x' hx']
      _ = k * x' * k⁻¹ * (k * x * k⁻¹) := by group
  have hcard' : Nat.card E = 5 ^ 3 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hcard
  have hzDE : zD ∈ E := Subgroup.mem_map.2 ⟨z₀, hz₀E, by simpa [MulAut.conj_apply] using hk⟩
  have hΦzD : cubeHom D.L D.g zD = griessZ hζ := by
    rw [cubeHom_apply, hzD']
    group
  have hntE : ¬ IsToralSubgroup Tag.E8 D.L (E.map (cubeHom D.L D.g)) := by
    refine not_isToralSubgroup_of_conj
      (w := (baseChangeGL (algebraMap K D.L) (k : ModGL Tag.E8 K))⁻¹ * D.g)
      (mul_mem (inv_mem (baseChangeGL_mem_adjointGroup' _ k.2)) (g_mem_adjoint D))
      (fun y hy => ?_) hnt₀
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨k * x * k⁻¹, Subgroup.mem_map.2 ⟨x, hx, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · simp only [cubeHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      group
  obtain ⟨c⟩ := cubeData_of_nontoral D hζ h5 hE5' hEc' hcard' hzDE hΦzD hntE
  have hH : HyperGen 5 (⊤ : Subgroup (adjointGroup Tag.E8 K)) E := hyperGen_of_cubeData hK5 c
  have hback : E.map (MulAut.conj k⁻¹).toMonoidHom = E₀ := by
    rw [hE, Subgroup.map_map]
    have : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  have := hyperGen_conj k⁻¹ hH
  rwa [hback] at this

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourGroup
public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.LieType.SeitzGeneration.UnitaryCubeClasses

public section

open scoped commutatorElement

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData p f F}

theorem glPi_false_eq_unitaryIsom3 (h : UnitaryFieldData p f F) :
    glPi false 3 (p ^ f) F = unitaryIsom3 h := by
  rw [glPi_false_eq h]
  rfl

theorem unitaryScalars_map_le_zPi (h : UnitaryFieldData p f F)
    (hq : ModThree false (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (unitaryScalars h 3).map (unitarySU p f F 3).subtype ≤ zPi false 3 (p ^ f) F := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨c, -, -, hzc⟩ := mem_unitaryScalars.1 hz
  rw [zPi_eq (π := false) (fun _ => h) (fun _ => hq) hτ hτ1, Subgroup.mem_inf]
  refine ⟨(mem_glPi_false h).mpr (mem_unitaryIsom3.mp (unitarySU_le_unitaryIsom3 z.2)),
    ⟨c, hzc.symm⟩⟩

theorem zPi_eq_ker_psuConj_map (h : UnitaryFieldData p f F)
    (hq : ModThree false (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    zPi false 3 (p ^ f) F = ((psuConj h).ker).map (unitaryIsom3 h).subtype := by
  rw [zPi_eq (π := false) (fun _ => h) (fun _ => hq) hτ hτ1]
  ext z
  constructor
  · rintro ⟨hzG, hzS⟩
    obtain ⟨c, hc⟩ := hzS
    refine Subgroup.mem_map.2 ⟨⟨z, mem_unitaryIsom3.mpr ((mem_glPi_false h).mp hzG)⟩, ?_, rfl⟩
    exact psuConj_eq_one_of_coe_eq_scalar hc.symm
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one A 1
      (by rw [map_one, mul_one, MonoidHom.mem_ker.1 hA])
    rw [Subgroup.mem_inf]
    exact ⟨(mem_glPi_false h).mpr (mem_unitaryIsom3.mp A.2), ⟨c, hc.symm⟩⟩

theorem exists_tau_unitary (h : UnitaryFieldData p f F) (hq6 : p ^ f % 6 = 5) :
    ∃ τ : F, τ ^ 3 = 1 ∧ τ ≠ 1 := by
  obtain ⟨ζ, hζ3, hζ1, -⟩ :=
    CFSG.LieType.SeitzGeneration.NonCube.exists_primitive_cube_root h
      (three_dvd_succ_of_mod_six_eq_five hq6)
  exact ⟨ζ, hζ3, hζ1⟩

private theorem glaPLayer_fixSubgroup_psuConj_ne_bot_of_conj_diagE
    (h : UnitaryFieldData p f F) (hq6 : p ^ f % 6 = 5) (hq3 : 3 ∣ p ^ f + 1)
    {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {n k : unitaryIsom3 h} (hk : k ∈ (psuConj h).ker)
    {g : GL (Fin 3) F} (hg : g ∈ glPi false 3 (p ^ f) F) {e : Fˣ}
    (he : (e : F) = τ ∨ (e : F) = τ ^ 2)
    (hEq : g⁻¹ * (↑(n * k) : GL (Fin 3) F) * g = diagE e) :
    GLAPLayer 3 (fixSubgroup (psuConj h n)) ≠ ⊥ := by
  haveI : Finite F := h.finite
  have he3 : (e : F) ^ 3 = 1 := val_pow_three_eq_one_of_eq_or_eq_sq hτ3 he
  have he1 : e ≠ 1 := ne_one_of_val_eq_or_eq_sq hτ3 hτ1 he
  have hgU : g ∈ unitaryIsom3 h := mem_unitaryIsom3.mpr ((mem_glPi_false h).mp hg)
  have hdiagU : diagE e ∈ unitaryIsom3 h := diagE_mem_unitaryIsom3 h hq3 he3
  have hbz : psuConj h (n * k) = psuConj h n := by
    rw [map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  have hEqU : (⟨g, hgU⟩ : unitaryIsom3 h)⁻¹ * (n * k) * ⟨g, hgU⟩ =
      ⟨diagE e, hdiagU⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hEq
  have hconj : psuConj h n =
      MulAut.congr (psuConj h ⟨g, hgU⟩ : unitaryPSU h 3 ≃* unitaryPSU h 3)
        (psuConj h ⟨diagE e, hdiagU⟩) := by
    have hps := congrArg (psuConj h) hEqU
    rw [map_mul, map_mul, map_inv, hbz] at hps
    show psuConj h n = psuConj h ⟨g, hgU⟩ * psuConj h ⟨diagE e, hdiagU⟩ *
      (psuConj h ⟨g, hgU⟩)⁻¹
    calc psuConj h n
        = psuConj h ⟨g, hgU⟩ * ((psuConj h ⟨g, hgU⟩)⁻¹ * psuConj h n *
            psuConj h ⟨g, hgU⟩) * (psuConj h ⟨g, hgU⟩)⁻¹ := by group
      _ = psuConj h ⟨g, hgU⟩ * psuConj h ⟨diagE e, hdiagU⟩ *
            (psuConj h ⟨g, hgU⟩)⁻¹ := by rw [← hps]
  have hne : GLAPLayer 3 (fixSubgroup (psuConj h ⟨diagE e, hdiagU⟩)) ≠ ⊥ :=
    glaPLayer_fixSubgroup_psuConj_diagE_ne_bot h hq6 he3 he1 hdiagU
  rw [hconj]
  exact (glaPLayer_fixSubgroup_congr_ne_bot_iff Nat.prime_three
    (psuConj h ⟨g, hgU⟩) (psuConj h ⟨diagE e, hdiagU⟩)).2 hne

private theorem diagE_notMem_zPi_false (h : UnitaryFieldData p f F)
    (hq : ModThree false (p ^ f)) {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {e : Fˣ}
    (he1 : e ≠ 1) : diagE e ∉ zPi false 3 (p ^ f) F := by
  intro hmem
  rw [zPi_eq (π := false) (fun _ => h) (fun _ => hq) hτ3 hτ1] at hmem
  obtain ⟨c, hc⟩ := hmem.2
  exact he1 (eq_one_of_eq_scalar_diagE hc)

private theorem psuConj_ne_one_of_conj_diagE (h : UnitaryFieldData p f F)
    (hq : ModThree false (p ^ f)) {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {n k : unitaryIsom3 h} (hk : k ∈ (psuConj h).ker)
    {g : GL (Fin 3) F} {e : Fˣ} (he : (e : F) = τ ∨ (e : F) = τ ^ 2)
    (hEq : g⁻¹ * (↑(n * k) : GL (Fin 3) F) * g = diagE e) :
    psuConj h n ≠ 1 := by
  haveI : Finite F := h.finite
  intro h1
  have he1 : e ≠ 1 := ne_one_of_val_eq_or_eq_sq hτ3 hτ1 he
  have hnot : diagE e ∉ zPi false 3 (p ^ f) F := diagE_notMem_zPi_false h hq hτ3 hτ1 he1
  have hbz : psuConj h (n * k) = psuConj h n := by
    rw [map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  have hnkZ : (↑(n * k) : GL (Fin 3) F) ∈ zPi false 3 (p ^ f) F := by
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1]
    refine Subgroup.mem_map.2 ⟨n * k, ?_, rfl⟩
    rw [MonoidHom.mem_ker, hbz, h1]
  have hnkS : (↑(n * k) : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := by
    rw [zPi_eq (π := false) (fun _ => h) (fun _ => hq) hτ3 hτ1] at hnkZ
    exact hnkZ.2
  have hcen : (↑(n * k) : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hnkS
  have hfix : g⁻¹ * (↑(n * k) : GL (Fin 3) F) * g = ↑(n * k) := by
    rw [Subgroup.mem_center_iff] at hcen
    rw [hcen g⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  exact hnot (by rw [← hEq, hfix]; exact hnkZ)

theorem exists_fourGroup_unitaryPSU (h : UnitaryFieldData p f F) (hq6 : p ^ f % 6 = 5)
    {A : Subgroup (MulAut (unitaryPSU h 3))} (hA : IsElemAbelian 3 A)
    (hlay : LayerTrivialOn (unitaryPSU h 3) A) (hcard : Nat.card A = 9) :
    ∃ T : Subgroup (unitaryPSU h 3), IsElemAbelian 2 T ∧ Nat.card ↥T = 4 ∧
      (∀ α ∈ A, Subgroup.map α.toMonoidHom T = T) ∧
      ∃ α ∈ A, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹ := by
  classical
  haveI : Finite F := h.finite
  have hp : 5 ≤ p := five_le_of_prime_of_pow_mod_six h.prime h.one_le (Or.inr hq6)
  have hq3 : 3 ∣ p ^ f + 1 := three_dvd_succ_of_mod_six_eq_five hq6
  have hq : ModThree false (p ^ f) :=
    (mod_three_eq_two_of_mod_six_eq_five hq6 : ModThree false (p ^ f))
  obtain ⟨τ, hτ3, hτ1⟩ := exists_tau_unitary h hq6
  have hK : PiField false p f F :=
    ⟨h.prime, h.one_le, by rw [h.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have hArange : A ≤ (psuConj h).range :=
    (le_psuConj_range_and_card_le_nine h hq6 hA hlay).1
  let C : Subgroup (unitaryIsom3 h) := A.comap (psuConj h)
  let B : Subgroup (GL (Fin 3) F) := C.map (unitaryIsom3 h).subtype
  have hBH : B ≤ glPi false 3 (p ^ f) F := by
    rw [glPi_false_eq_unitaryIsom3 h]
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hZB : zPi false 3 (p ^ f) F ≤ B := by
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1]
    exact Subgroup.map_mono (Subgroup.ker_le_comap _ A)
  have hB3 : ∀ b ∈ B, b ^ 3 ∈ zPi false 3 (p ^ f) F := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hb
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1]
    refine Subgroup.mem_map.2 ⟨n ^ 3, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_pow, hA.2 (psuConj h n) hn]
  have hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi false 3 (p ^ f) F := by
    intro b hb c hc
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hc
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1]
    refine Subgroup.mem_map.2 ⟨⁅n, m⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨psuConj h n, hn⟩ ⟨psuConj h m, hm⟩)
  have hB9 : (zPi false 3 (p ^ f) F).relIndex B = 9 := by
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1]
    rw [Subgroup.relIndex_map_map_of_injective _ _ (unitaryIsom3 h).subtype_injective,
      Subgroup.relIndex_ker, Subgroup.map_comap_eq, inf_eq_right.2 hArange, hcard]
  have hno : ∀ b ∈ B, ∀ z ∈ zPi false 3 (p ^ f) F, ∀ g ∈ glPi false 3 (p ^ f) F,
      ∀ e : Fˣ, ((e : F) = τ ∨ (e : F) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e := by
    rintro b hb z hz g hg e he hEq
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hb
    rw [zPi_eq_ker_psuConj_map h hq hτ3 hτ1] at hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    exact glaPLayer_fixSubgroup_psuConj_ne_bot_of_conj_diagE h hq6 hq3 hτ3 hτ1 hk hg he hEq
      (hlay (psuConj h n) hn (psuConj_ne_one_of_conj_diagE h hq hτ3 hτ1 hk he hEq))
  obtain ⟨T, hTle, hTcard, hTsq, hTinf, hTnorm, b, hbB, hbcomm⟩ :=
    exists_fourGroup_of_pgl_nine (B := B) hK hp hq hτ3 hτ1 hBH hZB hB3 hBc hB9 hno
  have hTle' : T ≤ unitarySU p f F 3 := hTle
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    exact CFSG.commute_of_sq_eq_one (hTsq x hx) (hTsq y hy) (hTsq (x * y) (T.mul_mem hx hy))
  have hb3 : b ^ 3 ∈ Subgroup.centralizer (T : Set (GL (Fin 3) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hbz : b ^ 3 ∈ zPi false 3 (p ^ f) F := hB3 b hbB
    rw [zPi_eq (π := false) (fun _ => h) (fun _ => hq) hτ3 hτ1] at hbz
    have hcen : b ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hbz.2
    exact Subgroup.mem_center_iff.1 hcen z
  have hsurjT : ∀ t ∈ T, ∃ s ∈ T, t = b * s * b⁻¹ * s⁻¹ :=
    CFSG.exists_eq_conj_mul_inv_of_commutator_zpowers_eq_top hTcomm hTsq hTcard
      (hTnorm b hbB) hb3 hbcomm
  let J : Subgroup (unitarySU p f F 3) := T.comap (unitarySU p f F 3).subtype
  have hJmap : J.map (unitarySU p f F 3).subtype = T := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hTle']
  have hJcard : Nat.card ↥J = 4 := by
    rw [← hTcard, ← hJmap]
    exact (Subgroup.card_map_of_injective Subtype.coe_injective).symm
  have hJsq : ∀ j ∈ J, j ^ 2 = 1 := by
    intro j hj
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hTsq (j : GL (Fin 3) F) hj
  have hJinf : J ⊓ (unitaryProj h 3).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxker⟩ := Subgroup.mem_inf.1 hx
    have hxZ : ((x : unitarySU p f F 3) : GL (Fin 3) F) ∈ zPi false 3 (p ^ f) F := by
      rw [ker_unitaryProj] at hxker
      exact unitaryScalars_map_le_zPi h hq hτ3 hτ1 (Subgroup.mem_map_of_mem _ hxker)
    have hxT : ((x : unitarySU p f F 3) : GL (Fin 3) F) ∈ T := hxJ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one]
    have hmem : ((x : unitarySU p f F 3) : GL (Fin 3) F) ∈ T ⊓ zPi false 3 (p ^ f) F :=
      ⟨hxT, hxZ⟩
    rw [hTinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hpres : ∀ n : unitaryIsom3 h, psuConj h n ∈ A →
      ∀ j ∈ J, suConj h n j ∈ J := by
    intro n hn j hj
    have hjT : ((j : unitarySU p f F 3) : GL (Fin 3) F) ∈ T := hj
    have hbC : (n : GL (Fin 3) F) ∈ B := Subgroup.mem_map_of_mem _ hn
    have hbN : (n : GL (Fin 3) F) ∈ Subgroup.normalizer (T : Set (GL (Fin 3) F)) :=
      hTnorm _ hbC
    rw [Subgroup.mem_comap]
    have hcoe : (unitarySU p f F 3).subtype (suConj h n j) =
        (n : GL (Fin 3) F) * ((j : unitarySU p f F 3) : GL (Fin 3) F) * (n : GL (Fin 3) F)⁻¹ :=
      coe_suConj n j
    rw [hcoe]
    exact (Subgroup.mem_normalizer_iff.1 hbN ((j : unitarySU p f F 3) : GL (Fin 3) F)).1 hjT
  obtain ⟨n₀, hn₀C, hn₀eq⟩ := Subgroup.mem_map.1 hbB
  refine fourGroup_push (unitaryProj h 3) (suConj h) (psuConj h) (fun n x => psuConj_mk n x)
    J hJinf hJcard hJsq A ?_ n₀ hn₀C (hpres n₀ hn₀C) ?_
  · intro α hα
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 (hArange hα)
    have hnA : psuConj h n ∈ A := by rw [hn]; exact hα
    refine ⟨n, hpres n hnA, ?_, hn⟩
    refine hpres n⁻¹ ?_
    rw [map_inv, hn]
    exact A.inv_mem hα
  · intro j hj
    have hjT : ((j : unitarySU p f F 3) : GL (Fin 3) F) ∈ T := hj
    obtain ⟨s, hs, hse⟩ := hsurjT (j : GL (Fin 3) F) hjT
    refine ⟨⟨s, hTle' hs⟩, Subgroup.mem_comap.2 hs, ?_⟩
    apply congrArg (unitaryProj h 3)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj, Subgroup.coe_inv,
      show ((n₀ : unitaryIsom3 h) : GL (Fin 3) F) = b from hn₀eq]
    exact hse

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end

module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryRoots

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open scoped MatrixGroups commutatorElement

section Block

@[expose] def ctuSiegBlk : (Fin 2 ⊕ Fin 2) ⊕ Fin 1 → Fin 3 :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => 2)) (fun _ => 1)

variable {K F : Type} [Field K] [Field F] [CharP K 2] {σ : F ≃+* F} {ι : K →+* F}
  {hι : ∀ c, σ (ι c) = ι c}

omit [CharP K 2] in
theorem ctuDiag_const_apply (s : Kˣ) (w : (Fin 2 ⊕ Fin 2) ⊕ Fin 1) :
    ctuDiag 1 ι (fun _ : Fin 2 => s) (ctuCoord 2 1 w) =
      Sum.elim (Sum.elim (fun _ => ι s) (fun _ => ι ((s⁻¹ : Kˣ) : K))) (fun _ => 1) w := by
  rcases w with (p | p) | i
  · exact ctuDiag_inl_inl _ p
  · exact ctuDiag_inl_inr _ p
  · exact ctuDiag_inr _ i

theorem ctuSieg_apply_eq_zero {s : Kˣ} (hs : (s : K) ≠ 1) {x : SU σ (2 * 2 + 1)}
    (hx : ctuEmbed 1 le_rfl σ ι hι (diagSp K 2 (fun _ => s)) * x =
      x * ctuEmbed 1 le_rfl σ ι hι (diagSp K 2 (fun _ => s)))
    {w w' : (Fin 2 ⊕ Fin 2) ⊕ Fin 1} (hww : ctuSiegBlk w ≠ ctuSiegBlk w') :
    ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)
      (ctuCoord 2 1 w) (ctuCoord 2 1 w') = 0 := by
  have h1 := congrFun (congrFun (congrArg (fun g : SU σ (2 * 2 + 1) =>
    ((g : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)) hx)
      (ctuCoord 2 1 w)) (ctuCoord 2 1 w')
  simp only [Subgroup.coe_mul, Units.val_mul] at h1
  rw [coe_ctuEmbed_diagSp, diagonal_mul, mul_diagonal, ctuDiag_const_apply,
    ctuDiag_const_apply] at h1
  have hs1 : ι (s : K) ≠ 1 := by rw [← map_one ι]; exact ι.injective.ne hs
  have hs2 : ι ((s⁻¹ : Kˣ) : K) ≠ 1 := by
    rw [← map_one ι]
    refine ι.injective.ne fun h => hs ?_
    have h' : s⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.1 h', Units.val_one]
  have hs3 : ι (s : K) ≠ ι ((s⁻¹ : Kˣ) : K) := by
    refine ι.injective.ne fun h => hs ?_
    have h1 : s * s = 1 := by
      rw [show s * s = s * s⁻¹ from congrArg (s * ·) (Units.ext h), mul_inv_cancel]
    have h2 : ((s : K) + 1) * ((s : K) + 1) = 0 := by
      have h3 : (s : K) * s = 1 := by rw [← Units.val_mul, h1, Units.val_one]
      have h4 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h3 + ((s : K) + 1) * h4
    have h5 : (s : K) + 1 = 0 := mul_self_eq_zero.1 h2
    have h4 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h5 - h4
  have hne : Sum.elim (Sum.elim (fun _ => ι (s : K)) (fun _ => ι ((s⁻¹ : Kˣ) : K))) (fun _ => 1) w ≠
      Sum.elim (Sum.elim (fun _ => ι (s : K)) (fun _ => ι ((s⁻¹ : Kˣ) : K))) (fun _ => 1) w' := by
    rcases w with (p | p) | i <;> rcases w' with (p' | p') | i' <;>
      simp only [ctuSiegBlk, Sum.elim_inl, Sum.elim_inr, ne_eq, not_true_eq_false] at hww ⊢ <;>
      first | exact hww.elim | exact hs3 | exact hs3.symm | exact hs1 | exact hs1.symm |
        exact hs2 | exact hs2.symm
  have h2 : (Sum.elim (Sum.elim (fun _ => ι (s : K)) (fun _ => ι ((s⁻¹ : Kˣ) : K)))
      (fun _ => 1) w - Sum.elim (Sum.elim (fun _ => ι (s : K))
        (fun _ => ι ((s⁻¹ : Kˣ) : K))) (fun _ => 1) w') *
      ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)
        (ctuCoord 2 1 w) (ctuCoord 2 1 w') = 0 := by
    rw [sub_mul, h1]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

end Block

section Mult

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] noncomputable def ctuSiegA (x : SU σ (2 * 2 + 1)) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)
    (ctuCoord 2 1 (Sum.inl (Sum.inl i))) (ctuCoord 2 1 (Sum.inl (Sum.inl j)))

@[expose] noncomputable def ctuSiegM (x : SU σ (2 * 2 + 1)) : F :=
  ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)
    (ctuCoord 2 1 (Sum.inr 0)) (ctuCoord 2 1 (Sum.inr 0))

@[expose] def CtuSiegBlockDiag (x : SU σ (2 * 2 + 1)) : Prop :=
  ∀ w w', ctuSiegBlk w ≠ ctuSiegBlk w' →
    ((x : GL (Fin (2 * 2 + 1)) F) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F)
      (ctuCoord 2 1 w) (ctuCoord 2 1 w') = 0

theorem ctuSiegA_one : ctuSiegA (1 : SU σ (2 * 2 + 1)) = 1 := by
  ext i j
  simp only [ctuSiegA, Subgroup.coe_one, Units.val_one, Matrix.one_apply,
    (ctuCoord 2 1).injective.eq_iff, Sum.inl.injEq]

theorem ctuSiegM_one : ctuSiegM (1 : SU σ (2 * 2 + 1)) = 1 := by
  simp [ctuSiegM]

theorem ctuSiegA_mul {x y : SU σ (2 * 2 + 1)} (hx : CtuSiegBlockDiag x) :
    ctuSiegA (x * y) = ctuSiegA x * ctuSiegA y := by
  ext i j
  simp only [ctuSiegA, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  rw [← (ctuCoord 2 1).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∀ p : Fin 2, ((x : GL (Fin (2 * 2 + 1)) F) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) (ctuCoord 2 1 (Sum.inl (Sum.inl i)))
        (ctuCoord 2 1 (Sum.inl (Sum.inr p))) = 0 := fun p =>
    hx _ _ (by simp [ctuSiegBlk])
  have h2 : ∀ k : Fin 1, ((x : GL (Fin (2 * 2 + 1)) F) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) (ctuCoord 2 1 (Sum.inl (Sum.inl i)))
        (ctuCoord 2 1 (Sum.inr k)) = 0 := fun k =>
    hx _ _ (by simp [ctuSiegBlk])
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, add_zero]

theorem ctuSiegM_mul {x y : SU σ (2 * 2 + 1)} (hx : CtuSiegBlockDiag x) :
    ctuSiegM (x * y) = ctuSiegM x * ctuSiegM y := by
  simp only [ctuSiegM, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  rw [← (ctuCoord 2 1).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∀ p : Fin 2, ((x : GL (Fin (2 * 2 + 1)) F) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) (ctuCoord 2 1 (Sum.inr 0))
        (ctuCoord 2 1 (Sum.inl (Sum.inl p))) = 0 := fun p =>
    hx _ _ (by simp [ctuSiegBlk])
  have h2 : ∀ p : Fin 2, ((x : GL (Fin (2 * 2 + 1)) F) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) (ctuCoord 2 1 (Sum.inr 0))
        (ctuCoord 2 1 (Sum.inl (Sum.inr p))) = 0 := fun p =>
    hx _ _ (by simp [ctuSiegBlk])
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, zero_add, Fin.sum_univ_one,
    Fin.fin_one_eq_zero]

theorem ctuSieg_eq_one {x : SU σ (2 * 2 + 1)} (hx : CtuSiegBlockDiag x)
    (hA : ctuSiegA x = 1) (hM : ctuSiegM x = 1) : x = 1 := by
  apply mat_injective
  rw [map_one]
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord 2 1).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord 2 1).surjective b
  have hcol : ∀ (p : Fin 2) (t : (Fin 2 ⊕ Fin 2) ⊕ Fin 1), t ≠ Sum.inl (Sum.inl p) →
      mat σ (2 * 2 + 1) x (ctuCoord 2 1 t) (ctuCoord 2 1 (Sum.inl (Sum.inl p))) = 0 := by
    intro p t ht
    rcases t with (q | q) | k
    · have h := congrFun (congrFun hA q) p
      simp only [ctuSiegA] at h
      rw [mat_apply, h, Matrix.one_apply_ne (fun e => ht (by rw [e]))]
    · exact hx _ _ (by simp [ctuSiegBlk])
    · exact hx _ _ (by simp [ctuSiegBlk])
  rcases w with (p | p) | k
  · rcases w' with (q | q) | k'
    · have h := congrFun (congrFun hA p) q
      simp only [ctuSiegA] at h
      rw [mat_apply, h, Matrix.one_apply, Matrix.one_apply]
      simp [(ctuCoord 2 1).injective.eq_iff]
    · rw [mat_apply, hx _ _ (by simp [ctuSiegBlk]), Matrix.one_apply_ne (by
        rw [Ne, (ctuCoord 2 1).injective.eq_iff]; simp)]
    · rw [mat_apply, hx _ _ (by simp [ctuSiegBlk]), Matrix.one_apply_ne (by
        rw [Ne, (ctuCoord 2 1).injective.eq_iff]; simp)]
  ·
    have h := sum_mat_mul_mat x (ctuCoord 2 1 (Sum.inl (Sum.inl p))) (ctuCoord 2 1 w')
    rw [Finset.sum_eq_single (ctuCoord 2 1 (Sum.inl (Sum.inl p)))] at h
    · have hpp : mat σ (2 * 2 + 1) x (ctuCoord 2 1 (Sum.inl (Sum.inl p)))
          (ctuCoord 2 1 (Sum.inl (Sum.inl p))) = 1 := by
        have h' := congrFun (congrFun hA p) p
        simp only [ctuSiegA] at h'
        rw [mat_apply, h', Matrix.one_apply_eq]
      rw [hpp, map_one, one_mul, ctuCoord_rev le_rfl, ctuPar_inl] at h
      simp only [par_inl] at h
      rw [h, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
    · intro t _ ht
      obtain ⟨t', rfl⟩ := (ctuCoord 2 1).surjective t
      rw [hcol p t' (fun e => ht (by rw [e])), map_zero, zero_mul]
    · simp
  · rcases w' with (q | q) | k'
    · rw [mat_apply, hx _ _ (by simp [ctuSiegBlk]), Matrix.one_apply_ne (by
        rw [Ne, (ctuCoord 2 1).injective.eq_iff]; simp)]
    · rw [mat_apply, hx _ _ (by simp [ctuSiegBlk]), Matrix.one_apply_ne (by
        rw [Ne, (ctuCoord 2 1).injective.eq_iff]; simp)]
    · rw [Fin.fin_one_eq_zero k, Fin.fin_one_eq_zero k', mat_apply]
      exact hM.trans (Matrix.one_apply_eq _).symm

end Mult

section Core

theorem ctuSieg_map_commutatorElement_eq_one {G M : Type*} [Group G] [CommMonoid M] (χ : G →* M)
    (a b : G) : χ ⁅a, b⁆ = 1 := by
  have ha : χ a * χ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hb : χ b * χ b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, map_mul, map_mul, map_mul, mul_right_comm (χ a) (χ b) (χ a⁻¹),
    mul_assoc (χ a * χ a⁻¹), ha, hb, one_mul]

variable {K F : Type} [Field K] [Field F] [Finite F] [CharP K 2] [CharP F 2] {f : ℕ}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}

theorem perfectCore_centralizer_ctuEmbed_siegelTorus_eq (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (hK : ∃ s : K, s ≠ 0 ∧ s ≠ 1) :
    perfectCore (centralizer (((siegelTorus K 2).map
      (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι)) :
        Set (SU (unitaryInvolution F 2 f) (2 * 2 + 1)))) =
      rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) (2 * 2 + 1))
        (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) := by
  set C := centralizer (((siegelTorus K 2).map
    (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι)) :
      Set (SU (unitaryInvolution F 2 f) (2 * 2 + 1))) with hC
  set L₀ := rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
    (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2)) with hL₀
  obtain ⟨s, hs0, hs1⟩ := hK
  obtain ⟨u, rfl⟩ : ∃ u : Kˣ, (u : K) = s := ⟨Units.mk0 s hs0, rfl⟩
  have hblk : ∀ x ∈ C, CtuSiegBlockDiag x := by
    intro x hx w w' hww
    have h := mem_centralizer_iff.1 hx (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι
      (diagSp K 2 (fun _ => u))) ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ctuSieg_apply_eq_zero hs1 h hww
  set χA : C →* F :=
    { toFun := fun x => (ctuSiegA (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1))).det
      map_one' := by simp [ctuSiegA_one]
      map_mul' := fun x y => by
        change (ctuSiegA ((x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) *
          (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1)))).det = _
        rw [ctuSiegA_mul (hblk x x.2), Matrix.det_mul] } with hχA
  set χM : C →* F :=
    { toFun := fun x => ctuSiegM (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1))
      map_one' := by simp [ctuSiegM_one]
      map_mul' := fun x y => by
        change ctuSiegM ((x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) *
          (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1))) = _
        rw [ctuSiegM_mul (hblk x x.2)] } with hχM
  have hker : ∀ x ∈ perfectCore C, ∃ hx : x ∈ C, χA ⟨x, hx⟩ = 1 ∧ χM ⟨x, hx⟩ = 1 := by
    set T : Subgroup (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) :=
      (χA.toHomUnits.ker ⊓ χM.toHomUnits.ker).map C.subtype with hT
    have hle : perfectCore C ≤ T := by
      refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf C 1).trans ?_
      rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
        Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⁅(⟨g₁, hg₁⟩ : C), (⟨g₂, hg₂⟩ : C)⁆, ⟨?_, ?_⟩, rfl⟩
      · exact (MonoidHom.mem_ker).2 (ctuSieg_map_commutatorElement_eq_one _ _ _)
      · exact (MonoidHom.mem_ker).2 (ctuSieg_map_commutatorElement_eq_one _ _ _)
    intro x hx
    obtain ⟨⟨x', hx'⟩, ⟨h1, h2⟩, rfl⟩ := hle hx
    refine ⟨hx', ?_, ?_⟩
    · have := congrArg Units.val (MonoidHom.mem_ker.1 h1)
      simpa using this
    · have := congrArg Units.val (MonoidHom.mem_ker.1 h2)
      simpa using this
  have hdet : ∀ x : perfectCore C,
      (ctuSiegA (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1))).det = 1 := fun x => by
    obtain ⟨hx, h1, -⟩ := hker x x.2
    exact h1
  set φ : perfectCore C → SL(2, F) := fun x =>
    ⟨ctuSiegA (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)), hdet x⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hA : ctuSiegA (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) =
        ctuSiegA (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) := congrArg Subtype.val hxy
    obtain ⟨hxC, -, hxM⟩ := hker x x.2
    obtain ⟨hyC, -, hyM⟩ := hker y y.2
    have hxM' : ctuSiegM (x : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) = 1 := hxM
    have hyM' : ctuSiegM (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) = 1 := hyM
    have hyiC : (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1))⁻¹ ∈ C := inv_mem hyC
    have hAinv : ctuSiegA ((y : SU (unitaryInvolution F 2 f) (2 * 2 + 1))⁻¹) *
        ctuSiegA (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1)) = 1 := by
      rw [← ctuSiegA_mul (hblk _ hyiC), inv_mul_cancel, ctuSiegA_one]
    have hMinv : ctuSiegM ((y : SU (unitaryInvolution F 2 f) (2 * 2 + 1))⁻¹) = 1 := by
      have h := ctuSiegM_mul (y := (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1)))
        (hblk _ hyiC)
      rw [inv_mul_cancel, ctuSiegM_one, hyM', mul_one] at h
      exact h.symm
    have hz : (y : SU (unitaryInvolution F 2 f) (2 * 2 + 1))⁻¹ * x = 1 := by
      refine ctuSieg_eq_one (hblk _ (mul_mem hyiC hxC)) ?_ ?_
      · rw [ctuSiegA_mul (hblk _ hyiC), hA, hAinv]
      · rw [ctuSiegM_mul (hblk _ hyiC), hxM', hMinv, mul_one]
    exact Subtype.ext (inv_mul_eq_one.1 hz).symm
  have hcard : Nat.card (perfectCore C) ≤ Nat.card L₀ := by
    rw [Nat.card_congr (CFSG.LieType.Steinberg.rankOneShortEquiv
      (hσ := unitaryInvolution_involutive hF) (n := 2 * 2 + 1) (k := ⟨0, by norm_num⟩)
        (by norm_num)).toEquiv]
    exact Nat.card_le_card_of_injective φ hφinj
  have hL₀C : L₀ ≤ perfectCore C := by
    refine le_perfectCore_of_perfect ?_ (Subgroup.isPerfect_iff.1
      (isPerfect_rankOne hF hf (n := 2 * 2 + 1) (by norm_num) _))
    intro x hx
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact (commute_rankOne_short_ctuEmbed_diagSp (N := 2) (ε := 1) (hε := le_rfl)
      (j := ⟨0, by norm_num⟩) (by norm_num) (t := fun _ => v) rfl hx).symm
  exact (Subgroup.eq_of_le_of_card_ge hL₀C hcard).symm

end Core

end CFSG.SeitzReduction.SymplecticPilot

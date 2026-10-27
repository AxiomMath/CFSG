module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Uni

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.StandardType
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K]

theorem suMapStable (d : ℕ) (K : Type) [Field K] (q : ℕ) :
    ∀ σ : K ≃+* K, ∀ h ∈ LargeEvenSUGroup (Fin d) K q,
      Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSUGroup (Fin d) K q :=
  fun σ h hh => YS09Field.su_map_mem σ h hh

@[expose] def Induced (q : ℕ) (σ : K ≃+* K)
    (f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K q))) : Prop :=
  ∀ x : LargeEvenSUGroup (Fin d) K q, f (QuotientGroup.mk x) =
    QuotientGroup.mk (matAct (LargeEvenSUGroup (Fin d) K q) (suMapStable d K q) σ x)

theorem exists_induced {q : ℕ} {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K q))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K q))) :
    ∃ σ : K ≃+* K, Induced q σ f :=
  matField_spec _ (suMapStable d K q) hf

section Faithful

variable [Finite K] [CharP K 2] {j : ℕ}

theorem eq_one_of_mk_matAct_eq (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K}
    (h : ∀ x : LargeEvenSUGroup (Fin d) K (2 ^ j),
      (QuotientGroup.mk (matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)) σ x) :
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))) = QuotientGroup.mk x) :
    σ = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ j) ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hord : orderOf γ = (2 ^ j) ^ 2 - 1 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hγ
  have hq : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hsq : (2 ^ j - 1) * (2 ^ j + 1) = (2 ^ j) ^ 2 - 1 := by
    have h1 : 1 ≤ 2 ^ j := by omega
    have h2 : 1 ≤ (2 ^ j) ^ 2 := by
      calc 1 ≤ 2 ^ j := h1
        _ ≤ (2 ^ j) ^ 2 := Nat.le_self_pow (by norm_num) _
    zify [h1, h2]
    ring
  set ζ : Kˣ := γ ^ (2 ^ j - 1) with hζdef
  have hζ : (ζ : K) ^ (2 ^ j + 1) = 1 := by
    rw [hζdef, ← Units.val_pow_eq_pow_val, ← pow_mul, hsq, ← hord, pow_orderOf_eq_one,
      Units.val_one]
  have hζinv : ((ζ⁻¹ : Kˣ) : K) ^ (2 ^ j + 1) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hζ, inv_one]
  set i₀ : Fin d := ⟨0, by omega⟩
  set i₁ : Fin d := ⟨1, by omega⟩
  set i₂ : Fin d := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h20 : i₂ ≠ i₀ := by simp [i₀, i₂, Fin.ext_iff]
  have h21 : i₂ ≠ i₁ := by simp [i₁, i₂, Fin.ext_iff]
  set t : Fin d → Kˣ := TableBUM.swapDiag i₀ i₁ ζ with ht
  have hnorm : ∀ i, (t i : K) ^ (2 ^ j + 1) = 1 := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0, ht, TableBUM.swapDiag_left h01]
      exact hζ
    · by_cases hi1 : i = i₁
      · rw [hi1, ht, TableBUM.swapDiag_right h01]
        exact hζinv
      · rw [ht, TableBUM.swapDiag_of_ne hi0 hi1, Units.val_one, one_pow]
  let x : LargeEvenSUGroup (Fin d) K (2 ^ j) :=
    ⟨diagHom d t, diagHom_mem_su t (TableBUM.prod_swapDiag ζ) hnorm⟩
  have hx := QuotientGroup.eq.mp (h x)
  have hscal : (((matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)) σ x)⁻¹ * x :
      LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    Subgroup.mem_subgroupOf.mp hx
  rw [largeEvenScalars_def] at hscal
  obtain ⟨c, hc⟩ := hscal
  have hmat : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (((matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)) σ x :
        LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        Matrix.scalar (Fin d) (c : K) := by
    have h1 : ((x : LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) =
        ((matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)) σ x :
          LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) *
          Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      change _ = ((matAct _ _ σ x * ((matAct _ _ σ x)⁻¹ * x) : LargeEvenSUGroup (Fin d) K (2 ^ j)) :
        GL (Fin d) K)
      rw [mul_inv_cancel_left]
    have h2 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h1
    simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] using h2
  have hσx : (((matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)) σ x :
      LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal fun i => σ (t i : K) := by
    rw [matAct_coe]
    change ((diagHom d t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ = _
    rw [coe_diagHom, Matrix.diagonal_map (map_zero σ)]
  have hent : ∀ i, (t i : K) = σ (t i : K) * c := by
    intro i
    have h1 := congrFun (congrFun hmat i) i
    rw [hσx, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] at h1
    change ((diagHom d t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = _ at h1
    rw [coe_diagHom, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h1
    exact h1
  have hc1 : (c : K) = 1 := by
    have h1 := hent i₂
    rw [ht, TableBUM.swapDiag_of_ne h20 h21, Units.val_one, map_one, one_mul] at h1
    exact h1.symm
  have hσζ : σ (ζ : K) = ζ := by
    have h1 := hent i₀
    rw [ht, TableBUM.swapDiag_left h01, hc1, mul_one] at h1
    exact h1.symm
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, hfixcard⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
  set r := orderOf σ with hr
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hkcard : Nat.card (fixF σ) = 2 ^ (2 * j / r) := card_fixF.trans hfixcard
  have hζk : (ζ : K) ∈ fixF σ := hσζ
  have hζ0 : (⟨(ζ : K), hζk⟩ : fixF σ) ≠ 0 := by
    intro h0
    exact ζ.ne_zero (congrArg Subtype.val h0)
  have hpowk : (ζ : K) ^ (2 ^ (2 * j / r) - 1) = 1 := by
    have h1 := pow_card_eq_one' (x := Units.mk0 (⟨(ζ : K), hζk⟩ : fixF σ) hζ0)
    rw [Nat.card_units, hkcard] at h1
    have h2 := congrArg (fun u : (fixF σ)ˣ => ((u : fixF σ) : K)) h1
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, SubmonoidClass.coe_pow,
      OneMemClass.coe_one] using h2
  have hdvd' : 2 ^ j + 1 ∣ 2 ^ (2 * j / r) - 1 := by
    have h1 : γ ^ ((2 ^ j - 1) * (2 ^ (2 * j / r) - 1)) = 1 := by
      apply Units.ext
      rw [pow_mul, ← hζdef, Units.val_pow_eq_pow_val, hpowk, Units.val_one]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, ← hsq] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h2
  by_contra hσ1
  have hr1 : r ≠ 1 := fun h1 => hσ1 (orderOf_eq_one_iff.mp h1)
  have hle : 2 * j / r ≤ j := by
    have hr2 : 2 ≤ r := by omega
    calc 2 * j / r ≤ 2 * j / 2 := Nat.div_le_div_left hr2 (by norm_num)
      _ = j := by omega
  have hpos : 1 ≤ 2 * j / r := by
    obtain ⟨c', hc'⟩ := hdvd
    rw [hc', Nat.mul_div_cancel_left _ hr0]
    rcases Nat.eq_zero_or_pos c' with h0 | h0
    · rw [h0, mul_zero] at hc'
      omega
    · exact h0
  have hsmall : 2 ^ (2 * j / r) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hle
  have hge : 2 ≤ 2 ^ (2 * j / r) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * j / r) := Nat.pow_le_pow_right (by norm_num) hpos
  have := Nat.le_of_dvd (by omega) hdvd'
  omega

theorem orderOf_eq_of_induced (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))}
    (hf : Induced (2 ^ j) σ f) : orderOf σ = orderOf f := by
  have key : ∀ n : ℕ, ∀ x : LargeEvenSUGroup (Fin d) K (2 ^ j),
      (f ^ n) (QuotientGroup.mk x) =
        QuotientGroup.mk ((matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j)))
          (σ ^ n) x) := by
    intro n
    induction n with
    | zero =>
        intro x
        simp only [pow_zero, map_one, MulAut.one_apply]
    | succ n ih =>
        intro x
        rw [pow_succ' f n, MulAut.mul_apply, ih x, hf, pow_succ' σ n, map_mul, MulAut.mul_apply]
  refine (orderOf_eq_orderOf_iff (x := σ) (y := f)).mpr fun n => ⟨?_, ?_⟩
  · intro hσ
    have hmat1 : (matAct (LargeEvenSUGroup (Fin d) K (2 ^ j)) (suMapStable d K (2 ^ j))) (σ ^ n) =
        1 := by
      rw [hσ, map_one]
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [key n x, hmat1, MulAut.one_apply, MulAut.one_apply]
  · intro hf1
    refine eq_one_of_mk_matAct_eq hd hj hK (σ := σ ^ n) fun x => ?_
    have hh := key n x
    rw [hf1, MulAut.one_apply] at hh
    exact hh.symm

end Faithful

section Fixed

variable [Finite K] [CharP K 2] {j : ℕ}

theorem fixF_data (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) :
    j = j / orderOf σ * orderOf σ ∧ 1 ≤ j / orderOf σ ∧
      Nat.card (fixF σ) = (2 ^ (j / orderOf σ)) ^ 2 := by
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field (m := 2 * j) (by omega) hK' σ
  have hcop : (orderOf σ).Coprime 2 := (Nat.coprime_two_left.2 hσ).symm
  obtain ⟨j', hjj'⟩ := (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd : orderOf σ ∣ j)
  have hr0 : 0 < orderOf σ := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hj'eq : j / orderOf σ = j' := by
    rw [hjj']
    exact Nat.mul_div_cancel_left _ hr0
  have hee' : 2 * j / orderOf σ = 2 * j' := by
    rw [hjj', ← mul_assoc, mul_comm 2 (orderOf σ), mul_assoc, Nat.mul_div_cancel_left _ hr0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hj'eq, hjj', mul_comm]
  · rw [hj'eq]
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · rw [h0, mul_zero] at hjj'
      omega
    · exact h0
  · rw [hj'eq, card_fixF, hcard, hee', pow_mul']

theorem charP_fixF (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) : CharP (fixF σ) 2 :=
  CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 2 * (j / orderOf σ))
    (by rw [(fixF_data hj hK σ hσ).2.2, ← pow_mul, mul_comm])

theorem fixF_pow (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) (b : fixF σ) : (b : K) ^ 2 ^ j = (b : K) ^ 2 ^ (j / orderOf σ) := by
  obtain ⟨hjr, -, hk⟩ := fixF_data hj hK σ hσ
  have h := pow_two_pow_mul_of_odd hk hσ b
  rw [← hjr] at h
  exact congrArg Subtype.val h

end Fixed

section Sub

variable [Finite K] [CharP K 2] {j : ℕ}

@[expose] noncomputable def subfieldInclusion (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    (σ : K ≃+* K) (hσ : Odd (orderOf σ)) :
    LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) →*
      LargeEvenSUGroup (Fin d) K (2 ^ j) where
  toFun A := ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype A.1,
    (FR.su_hiff hj hK σ hσ A.1).2 A.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

theorem coe_subfieldInclusion (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) (A : LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))) :
    ((subfieldInclusion hj hK σ hσ A : LargeEvenSUGroup (Fin d) K (2 ^ j)) : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A.1 :=
  rfl

@[expose] noncomputable def subfieldHom (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    (σ : K ≃+* K) (hσ : Odd (orderOf σ)) :
    LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)) :=
  (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j))).comp (subfieldInclusion hj hK σ hσ)

theorem ker_subfieldHom (hd : 1 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2) (σ : K ≃+* K)
    (hσ : Odd (orderOf σ)) :
    (subfieldHom (d := d) hj hK σ hσ).ker =
      (LargeEvenScalars (Fin d) (fixF σ)).subgroupOf
        (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  unfold subfieldHom
  rw [← MonoidHom.comap_ker (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
    (subfieldInclusion hj hK σ hσ), QuotientGroup.ker_mk']
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    coe_subfieldInclusion]
  exact (FR.scalar_iff (fixF σ) (x : GL (Fin d) (fixF σ))).symm

theorem range_subfieldHom (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K} (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))} (hf : Induced (2 ^ j) σ f) :
    (subfieldHom hj hK σ hσ).range = ggFixDer f := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  haveI : CharP (fixF σ) 2 := charP_fixF hj hK σ hσ
  let H : Subgroup (GL (Fin d) K) := LargeEvenSUGroup (Fin d) K (2 ^ j)
  let π : H →* LargeEvenProj H := LargeEvenProjMk H
  let ρ : MulAut H := matAct H (suMapStable d K (2 ^ j)) σ
  let C : Subgroup H := FP.fixSub ρ
  let D : Subgroup (LargeEvenProj H) := C.map π
  let T : Subgroup (LargeEvenProj H) := FP.fixSub f
  have hInc : (subfieldInclusion (d := d) hj hK σ hσ).range = C := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨A, rfl⟩
      rw [FP.mem_fixSub]
      apply Subtype.ext
      change ((ρ (subfieldInclusion hj hK σ hσ A) : H) : GL (Fin d) K) =
        ((subfieldInclusion hj hK σ hσ A : H) : GL (Fin d) K)
      rw [matAct_coe H (suMapStable d K (2 ^ j)) σ (subfieldInclusion hj hK σ hσ A),
        coe_subfieldInclusion]
      exact glMap_subtype_fixed σ A.1
    · intro x hx
      rw [FP.mem_fixSub] at hx
      rw [MonoidHom.mem_range]
      have hfix : Matrix.GeneralLinearGroup.map σ.toRingHom (x : GL (Fin d) K) =
          (x : GL (Fin d) K) := by
        rw [← matAct_coe H (suMapStable d K (2 ^ j)) σ x]
        exact congrArg (fun y : H => (y : GL (Fin d) K)) hx
      obtain ⟨A, hA⟩ := exists_descend σ (x : GL (Fin d) K) hfix
      refine ⟨⟨A, ?_⟩, ?_⟩
      · apply (FR.su_hiff hj hK σ hσ A).1
        rw [hA]
        exact x.2
      · apply Subtype.ext
        rw [coe_subfieldInclusion]
        exact hA
  have hRange : (subfieldHom (d := d) hj hK σ hσ).range = D := by
    unfold subfieldHom
    rw [MonoidHom.range_comp, hInc]
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, ← pow_mul, mul_comm]
  have hZc : (LargeEvenScalars (Fin d) K).subgroupOf H ≤ Subgroup.center H :=
    scalars_subgroupOf_le_center H
  have hZodd : Odd (Nat.card ((LargeEvenScalars (Fin d) K).subgroupOf H)) :=
    scalars_subgroupOf_odd (m := 2 * j) (by omega) hK' H
  have hmem : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) := hf
  obtain ⟨hDT, hcomm, -⟩ := FR.subfield_core ((LargeEvenScalars (Fin d) K).subgroupOf H)
    hZc hZodd ρ f hmem
  obtain ⟨-, -, hk⟩ := fixF_data hj hK σ hσ
  haveI hperf : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))) :=
    Subgroup.isPerfect_iff.2 (commutator_su hk hd hdq)
  have hDperf : Group.IsPerfect ↥D := by
    have h1 : Group.IsPerfect ↥((subfieldHom (d := d) hj hK σ hσ).range) :=
      Group.IsPerfect.range (subfieldHom (d := d) hj hK σ hσ)
    rwa [hRange] at h1
  have hT : ggFixSub f = T := Subgroup.ext fun _ => Iff.rfl
  rw [hRange]
  unfold ggFixDer
  rw [hT]
  refine le_antisymm ?_ hcomm
  · haveI := hDperf
    rw [← Subgroup.commutator_eq_self (H := D)]
    exact Subgroup.commutator_mono hDT hDT

@[expose] noncomputable def subfieldEquiv (hd : 3 ≤ d) (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) {σ : K ≃+* K} (hσ : Odd (orderOf σ))
    (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))} (hf : Induced (2 ^ j) σ f) :
    LargeEvenProj (LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))) ≃* ggFixDer f :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_subfieldHom (by omega) hj hK σ hσ).symm).trans
    (QuotientGroup.quotientKerEquivRange (subfieldHom hj hK σ hσ))).trans
    (MulEquiv.subgroupCongr (range_subfieldHom hd hj hK hσ hdq hf))

theorem coe_subfieldEquiv_mk (hd : 3 ≤ d) (hj : 1 ≤ j) (hK : Nat.card K = (2 ^ j) ^ 2)
    {σ : K ≃+* K} (hσ : Odd (orderOf σ)) (hdq : (d, 2 ^ (j / orderOf σ)) ≠ (3, 2))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j)))} (hf : Induced (2 ^ j) σ f)
    (A : LargeEvenSUGroup (Fin d) (fixF σ) (2 ^ (j / orderOf σ))) :
    ((subfieldEquiv hd hj hK hσ hdq hf (QuotientGroup.mk A) : ggFixDer f) :
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ j))) = subfieldHom hj hK σ hσ A :=
  rfl

end Sub

end CFSG.LocalAnalysis.GLTheoremA.T156.Uni

end

module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitarySU2
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Generation
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

set_option linter.unusedSectionVars false

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalInvolution.Phan
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Diag

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem diagGL_mul (d e : Fin 3 → Kˣ) : diagGL d * diagGL e = diagGL (d * e) := by
  apply Units.ext
  rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
  rfl

theorem diagGL_mem_unitaryIsom3 (d : Fin 3 → Kˣ) (hd : ∀ c, h.bar (d c) * d c = 1) :
    (diagGL d : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagGL, diagonal_map (map_zero h.bar), diagonal_transpose,
    diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg _ (funext hd)

theorem glAut_diagGL (τ : K ≃+* K) (d : Fin 3 → Kˣ) :
    glAut τ (diagGL d) = diagGL (fun c => Units.map (τ : K →* K) (d c)) := by
  apply Units.ext
  rw [coe_glAut, coe_diagGL, coe_diagGL, diagonal_map (map_zero τ)]
  rfl

theorem diag_mul_comm (M N : Matrix (Fin 3) (Fin 3) K) (hM : M.IsDiag) (hN : N.IsDiag) :
    M * N = N * M := by
  rw [← hM.diagonal_diag, ← hN.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  exact congrArg _ (funext fun i => mul_comm _ _)

@[expose] def vr (i : Fin 2) (r : Kˣ) : Fin 3 → Kˣ := fun c => if c.val = i.val then r else 1

theorem diagGL_vr_mem (hq3 : 3 ∣ ℓ ^ f + 1) (i : Fin 2) {r : Kˣ} (hr : r ^ 3 = 1) :
    (diagGL (vr i r) : GL (Fin 3) K) ∈ unitaryIsom3 h := by
  apply diagGL_mem_unitaryIsom3
  intro c
  unfold vr
  split_ifs
  · have hμ : (r : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hr
      simpa using this
    exact CFSG.LieType.SeitzGeneration.bar_mul_eq_one_of_cube h hq3 r.ne_zero hμ (one_pow _)
  · simp

end Diag

section Split

open CFSG.RankThree.PartOne.CTP

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

structure SplitDataU (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K)
    (A B : Subgroup (MulAut (unitaryPSU h 3))) : Prop where
  A3 : ∀ a ∈ A, a ^ 3 = 1
  Ad : ∀ a ∈ A, ∃ (d : Fin 3 → Kˣ) (hd : (diagGL d : GL (Fin 3) K) ∈ unitaryIsom3 h),
    a = psuConj h ⟨diagGL d, hd⟩
  Bf : ∀ b ∈ B, ∃ k : ℕ, ∃ a ∈ A, b = psuField h σ ^ k * a

@[expose] def ia (i : Fin 2) : Fin 3 := ⟨i.val, by have := i.isLt; omega⟩

@[expose] def ib (i : Fin 2) : Fin 3 := ⟨i.val + 1, by have := i.isLt; omega⟩

theorem cube_ratio_of_psuConj_pow (d : Fin 3 → Kˣ) (hd : (diagGL d : GL (Fin 3) K) ∈ unitaryIsom3 h)
    (h3 : psuConj h ⟨diagGL d, hd⟩ ^ 3 = 1) (a b : Fin 3) : (d a * (d b)⁻¹) ^ 3 = 1 := by
  have h1 : psuConj h ((⟨diagGL d, hd⟩ : unitaryIsom3 h) ^ 3) = 1 := by rw [map_pow, h3]
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.exists_scalar_of_psuConj_eq_one h1
  have hentry : ∀ x : Fin 3, ((d x : Kˣ) : K) ^ 3 = (c : K) := by
    intro x
    have := congrArg (fun A : GL (Fin 3) K => ((A : Matrix (Fin 3) (Fin 3) K)) x x) hc
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_diagGL, diagonal_pow,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at this
    simpa using this
  have hab : (d a) ^ 3 = (d b) ^ 3 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hentry a, hentry b])
  rw [mul_pow, inv_pow, hab, mul_inv_cancel]

theorem conj_diagGL_block (i : Fin 2) (d : Fin 3 → Kˣ) (y : GL (Fin 3) K)
    (Y : Matrix (Fin 2) (Fin 2) K) (hy : (y : Matrix (Fin 3) (Fin 3) K) = blockMat 3 i.val Y) :
    diagGL d * y * (diagGL d)⁻¹ =
      diagGL (vr i (d (ia i) * (d (ib i))⁻¹)) * y * (diagGL (vr i (d (ia i) * (d (ib i))⁻¹)))⁻¹ := by
  set r : Kˣ := d (ia i) * (d (ib i))⁻¹ with hr
  set V : GL (Fin 3) K := diagGL (vr i r) with hV
  set e : Fin 3 → Kˣ := fun c => d c * (vr i r c)⁻¹ with he
  set E : GL (Fin 3) K := diagGL e with hE
  have hdVE : diagGL d = V * E := by
    rw [hV, hE, diagGL_mul]
    congr 1
    funext c
    show d c = vr i r c * (d c * (vr i r c)⁻¹)
    rw [mul_comm (d c), ← mul_assoc, mul_inv_cancel, one_mul]
  have hvia : vr i r (ia i) = r := by simp [vr, ia]
  have hvib : vr i r (ib i) = 1 := by simp [vr, ib]
  have hee : e (ia i) = e (ib i) := by
    show d (ia i) * (vr i r (ia i))⁻¹ = d (ib i) * (vr i r (ib i))⁻¹
    rw [hvia, hvib, hr]
    simp
  have hcomm : y * E = E * y := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hy, hE, coe_diagGL]
    exact blockMat_mul_diagonal_comm (m := 3) (i := i.val) (by have := i.isLt; omega) (fun c => (e c : K))
      (fun c => (e c).ne_zero) (ia i) (ib i) rfl rfl (by simpa using congrArg (fun u : Kˣ => (u : K)) hee) Y
  have hEy : E * y * E⁻¹ = y := by
    rw [← hcomm]; group
  rw [hdVE]
  calc V * E * y * (V * E)⁻¹ = V * (E * y * E⁻¹) * V⁻¹ := by group
    _ = V * y * V⁻¹ := by rw [hEy]

theorem psuConj_diagGL_block (hq3 : 3 ∣ ℓ ^ f + 1) (i : Fin 2) (d : Fin 3 → Kˣ)
    (hd : (diagGL d : GL (Fin 3) K) ∈ unitaryIsom3 h) {r : Kˣ} (hr3 : r ^ 3 = 1)
    (hr : r = d (ia i) * (d (ib i))⁻¹) (g : unitarySU ℓ f K 3) (Y : Matrix (Fin 2) (Fin 2) K)
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blockMat 3 i.val Y) :
    psuConj h ⟨diagGL d, hd⟩ (g : unitaryPSU h 3) =
      psuConj h ⟨diagGL (vr i r), diagGL_vr_mem hq3 i hr3⟩ (g : unitaryPSU h 3) := by
  rw [psuConj_mk, psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj, coe_suConj]
  have := conj_diagGL_block i d (g : GL (Fin 3) K) Y hg
  rw [← hr] at this
  exact this

theorem act_block (hq3 : 3 ∣ ℓ ^ f + 1) {σ : K ≃+* K} {A B : Subgroup (MulAut (unitaryPSU h 3))}
    (hd : SplitDataU h σ A B) (i : Fin 2) (g : unitarySU ℓ f K 3) (Y : Matrix (Fin 2) (Fin 2) K)
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blockMat 3 i.val Y)
    (hrat : ∀ a b, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b)
    {b : MulAut (unitaryPSU h 3)} (hb : b ∈ B) :
    ∃ (r : Kˣ) (hr : r ^ 3 = 1), b (g : unitaryPSU h 3) =
      psuConj h ⟨diagGL (vr i r), diagGL_vr_mem hq3 i hr⟩ (g : unitaryPSU h 3) := by
  obtain ⟨k, a, ha, rfl⟩ := hd.Bf b hb
  obtain ⟨d, hdI, rfl⟩ := hd.Ad a ha
  have hcube := cube_ratio_of_psuConj_pow d hdI (hd.A3 _ ha) (ia i) (ib i)
  set τ : K ≃+* K := σ ^ k with hτ
  have hτfix : ∀ x : K, σ x = x → τ x = x := fun x hx => pow_apply_of_fixed hx k
  have hf : psuField h σ ^ k = psuField h τ := (map_pow _ _ _).symm
  have hfx : psuField h τ (g : unitaryPSU h 3) = (g : unitaryPSU h 3) := by
    rw [psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut]
    ext a' b'
    exact hτfix _ (hrat a' b')
  set D : unitaryIsom3 h := ⟨diagGL d, hdI⟩ with hD
  set d' : Fin 3 → Kˣ := fun c => Units.map (τ : K →* K) (d c) with hd'
  have hglAut : glAut τ (D : GL (Fin 3) K) = diagGL d' := glAut_diagGL τ d
  have hd'I : (diagGL d' : GL (Fin 3) K) ∈ unitaryIsom3 h := hglAut ▸ glAut_mem_unitaryIsom3 τ D.2
  have hr'3 : (d' (ia i) * (d' (ib i))⁻¹) ^ 3 = 1 := by
    simp only [hd']
    rw [← map_inv, ← map_mul, ← map_pow, hcube, map_one]
  refine ⟨d' (ia i) * (d' (ib i))⁻¹, hr'3, ?_⟩
  have e1 : psuField h τ (psuConj h D (g : unitaryPSU h 3)) =
      (psuField h τ * psuConj h D * (psuField h τ)⁻¹) (psuField h τ (g : unitaryPSU h 3)) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  rw [MulAut.mul_apply, hf, e1, hfx, psuField_mul_psuConj_mul_inv]
  have e2 : (⟨glAut τ (D : GL (Fin 3) K), glAut_mem_unitaryIsom3 τ D.2⟩ : unitaryIsom3 h) =
      ⟨diagGL d', hd'I⟩ := Subtype.ext hglAut
  rw [e2]
  exact psuConj_diagGL_block hq3 i d' hd'I hr'3 rfl g Y hg

theorem ncard_orbit_block_le (hq3 : 3 ∣ ℓ ^ f + 1) {σ : K ≃+* K}
    {A B : Subgroup (MulAut (unitaryPSU h 3))} (hd : SplitDataU h σ A B) (i : Fin 2)
    (g : unitarySU ℓ f K 3) (Y : Matrix (Fin 2) (Fin 2) K)
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blockMat 3 i.val Y)
    (hrat : ∀ a b, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b) :
    (MulAction.orbit B (g : unitaryPSU h 3)).ncard ≤ 3 := by
  classical
  let Ψ : rootsOfUnity 3 K → unitaryPSU h 3 := fun r =>
    psuConj h ⟨diagGL (vr i (r : Kˣ)), diagGL_vr_mem hq3 i ((mem_rootsOfUnity 3 _).1 r.2)⟩
      (g : unitaryPSU h 3)
  have hsub : MulAction.orbit B (g : unitaryPSU h 3) ⊆ Ψ '' Set.univ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨r, hr, hb⟩ := act_block hq3 hd i g Y hg hrat b.2
    exact ⟨⟨r, (mem_rootsOfUnity 3 _).2 hr⟩, Set.mem_univ _, hb.symm⟩
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
  rw [Set.ncard_univ]
  exact card_rootsOfUnity K 3

theorem ncard_orbit_diag_le {σ : K ≃+* K} {A B : Subgroup (MulAut (unitaryPSU h 3))}
    (hd : SplitDataU h σ A B) (hσ : σ ^ 3 = 1) (g : unitarySU ℓ f K 3)
    (hg : ∀ a b : Fin 3, a ≠ b → ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0) :
    (MulAction.orbit B (g : unitaryPSU h 3)).ncard ≤ 3 := by
  classical
  have hf3 : psuField h σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  have hsub : MulAction.orbit B (g : unitaryPSU h 3) ⊆
      (fun k : Fin 3 => (psuField h σ ^ (k : ℕ)) (g : unitaryPSU h 3)) '' Set.univ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, a, ha, hb⟩ := hd.Bf b.1 b.2
    obtain ⟨d, hdI, rfl⟩ := hd.Ad a ha
    have hcx : psuConj h ⟨diagGL d, hdI⟩ (g : unitaryPSU h 3) = (g : unitaryPSU h 3) := by
      rw [psuConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suConj]
      have hcomm : (diagGL d : GL (Fin 3) K) * (g : GL (Fin 3) K) =
          (g : GL (Fin 3) K) * (diagGL d : GL (Fin 3) K) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_diagGL]
        exact diag_mul_comm _ _ (isDiag_diagonal _) (fun a b hab => hg a b hab)
      show (diagGL d : GL (Fin 3) K) * (g : GL (Fin 3) K) * (diagGL d : GL (Fin 3) K)⁻¹ = _
      rw [hcomm, mul_inv_cancel_right]
    refine ⟨⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, Set.mem_univ _, ?_⟩
    have hk : psuField h σ ^ (k % 3) = psuField h σ ^ k := by
      conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hf3, one_pow, one_mul]
    show (psuField h σ ^ (k % 3)) (g : unitaryPSU h 3) = b.1 (g : unitaryPSU h 3)
    rw [hb, MulAut.mul_apply, hcx, hk]
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp)

end Split

section Main

open CFSG.LieType.Universal.Unitary (SUid_eq_statedSU)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem eq_top_of_blockEmb_mem [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f ≠ 2)
    (S : Subgroup (unitarySU ℓ f K 3))
    (hS : ∀ (i : Fin 2) (a : Su K ℓ f 2),
      MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 3) (blockEmb2 K ℓ f 2 i a) ∈ S) :
    S = ⊤ := by
  classical
  let ε : Su K ℓ f 3 ≃* unitarySU ℓ f K 3 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 3)
  let ι : Fin 2 → (Su K ℓ f 2 →* unitarySU ℓ f K 3) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f 2 i)
  have hgen : ⨆ i : Fin 2, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq 2
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hle : ⨆ i : Fin 2, (ι i).range ≤ S :=
    iSup_le fun i => by
      rintro _ ⟨a, rfl⟩
      exact hS i a
  rw [hgen] at hle
  exact top_unique hle

theorem exists_fixed_data [Finite K] (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧ Nat.card (fixF σ) = (ℓ ^ f₀) ^ 2 := by
  have hc := natCard_eq_pow_three hσ
  rw [h.card] at hc
  have hdvd : Nat.card (fixF σ) ∣ ℓ ^ (2 * f) := ⟨Nat.card (fixF σ) ^ 2, by rw [hc]; ring⟩
  obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow h.prime).1 hdvd
  rw [hg, ← pow_mul] at hc
  have := Nat.pow_right_injective h.prime.two_le hc
  refine ⟨f / 3, by omega, ?_⟩
  rw [hg, ← pow_mul]
  congr 1
  omega

theorem three_dvd_of_three_dvd_pow_three_add_one {q₀ : ℕ} (h : 3 ∣ q₀ ^ 3 + 1) : 3 ∣ q₀ + 1 := by
  have key : ∀ x : ZMod 3, x ^ 3 = x := by decide
  have h1 : ((q₀ ^ 3 + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h1
  rw [key] at h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h1)

theorem blockMat_offDiag {i : Fin 2} {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : ∀ a b : Fin 2, a ≠ b → Y a b = 0) (a b : Fin 3) (hab : a ≠ b) :
    blockMat 3 i.val Y a b = 0 := by
  rw [blockMat_apply]
  split_ifs with hh
  · apply hY
    intro hc
    apply hab
    have := congrArg Fin.val hc
    simp only at this
    exact Fin.ext (by omega)
  · exact Matrix.one_apply_ne hab

theorem blockMat_rational {σ : K ≃+* K} {i : Fin 2} {Y : Matrix (Fin 2) (Fin 2) K}
    (hY : ∀ a b : Fin 2, σ (Y a b) = Y a b) (a b : Fin 3) :
    σ (blockMat 3 i.val Y a b) = blockMat 3 i.val Y a b := by
  rw [blockMat_apply]
  split_ifs with hh
  · exact hY _ _
  · by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]

end Main

section Gen

open CFSG.LieType.Universal.Unitary (SUid_eq_statedSU)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem closure_hyperplane_fixed_eq_top_u (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) (hq8 : ℓ ^ f ≠ 8) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {A B : Subgroup (MulAut (unitaryPSU h 3))} (hd : SplitDataU h σ A B) {s : ℕ} (hs : 1 ≤ s)
    (hBc : Nat.card B = 3 ^ s) :
    Subgroup.closure {x : unitaryPSU h 3 | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup (MulAut (unitaryPSU h 3)), H ≤ B ∧ H.relIndex B = 3 ∧
        ∀ b ∈ H, b x = x} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hBc]; positivity)
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨f₀, hf, hK₀⟩ := exists_fixed_data h hσ
  have hqq : ℓ ^ f = (ℓ ^ f₀) ^ 3 := by rw [hf, mul_comm, pow_mul]
  have hq₀ : ℓ ^ f₀ ≠ 2 := by
    intro h2; apply hq8; rw [hqq, h2]; norm_num
  have h3 : 3 ∣ ℓ ^ f₀ + 1 := three_dvd_of_three_dvd_pow_three_add_one (hqq ▸ hq3)
  have hq₀5 : 5 ≤ ℓ ^ f₀ := by
    have : 2 ≤ ℓ ^ f₀ := by
      have hf₀ : 1 ≤ f₀ := by have := h.one_le; omega
      have := (Nat.one_lt_pow (by omega) h.prime.one_lt : 1 < ℓ ^ f₀)
      omega
    omega
  have hq2 : ℓ ^ f ≠ 2 := by
    have : 5 ^ 3 ≤ (ℓ ^ f₀) ^ 3 := Nat.pow_le_pow_left hq₀5 3
    omega
  have hSU2 := closure_threePrime_unitarySU_two h f₀ hf (fixF σ) hK₀ hq₀ h3
  set Sset : Set (unitaryPSU h 3) := {x : unitaryPSU h 3 | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup (MulAut (unitaryPSU h 3)), H ≤ B ∧ H.relIndex B = 3 ∧
        ∀ b ∈ H, b x = x} with hSset
  set S : Subgroup (unitarySU ℓ f K 3) := (Subgroup.closure Sset).comap (unitaryProj h 3)
    with hS
  let ε₂ : Su K ℓ f 2 ≃* unitarySU ℓ f K 2 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 2)
  let ε₃ : Su K ℓ f 3 ≃* unitarySU ℓ f K 3 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 3)
  let β : Fin 2 → (unitarySU ℓ f K 2 →* unitarySU ℓ f K 3) := fun i =>
    ε₃.toMonoidHom.comp ((blockEmb2 K ℓ f 2 i).comp ε₂.symm.toMonoidHom)
  have hβ : ∀ (i : Fin 2) (x : unitarySU ℓ f K 2),
      (((β i x : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        blockMat 3 i.val (((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :=
    fun i x => rfl
  have hgen1 : ∀ (i : Fin 2) (x : unitarySU ℓ f K 2),
      x ∈ ({A : unitarySU ℓ f K 2 | (∀ i j : Fin 2, i ≠ j →
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = 0) ∧ (orderOf A).Coprime 3} ∪
        {A : unitarySU ℓ f K 2 | (∀ i j : Fin 2,
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ fixF σ) ∧
            (orderOf A).Coprime 3} : Set (unitarySU ℓ f K 2)) → β i x ∈ S := by
    intro i x hx
    rw [hS, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    have hord : (orderOf x).Coprime 3 := hx.elim (fun h => h.2) (fun h => h.2)
    refine ⟨?_, ?_⟩
    · exact Nat.Coprime.coprime_dvd_left ((orderOf_map_dvd _ _).trans (orderOf_map_dvd _ _)) hord
    · have horb : (MulAction.orbit B ((β i x : unitarySU ℓ f K 3) : unitaryPSU h 3)).ncard ≤ 3 := by
        rcases hx with ⟨hdiag, -⟩ | ⟨hrat, -⟩
        · exact ncard_orbit_diag_le hd hσ3 (β i x) (fun a b hab => by
            rw [hβ]; exact blockMat_offDiag (fun a' b' hab' => hdiag a' b' hab') a b hab)
        · exact ncard_orbit_block_le hq3 hd i (β i x) _ (hβ i x) (fun a b => by
            rw [hβ]; exact blockMat_rational (fun a' b' => mem_fixF.1 (hrat a' b')) a b)
      obtain ⟨H, hHB, hHi, hHx⟩ := exists_hyperplane_of_orbit_le B hs hBc _ horb
      exact ⟨H, hHB, hHi, fun b hb => hHx b hb⟩
  have hall : ∀ (i : Fin 2) (t : unitarySU ℓ f K 2), β i t ∈ S := by
    intro i t
    have ht : t ∈ Subgroup.closure
        ({A : unitarySU ℓ f K 2 | (∀ i j : Fin 2, i ≠ j →
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = 0) ∧ (orderOf A).Coprime 3} ∪
        {A : unitarySU ℓ f K 2 | (∀ i j : Fin 2,
          ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ fixF σ) ∧
            (orderOf A).Coprime 3}) := by rw [hSU2]; trivial
    induction ht using Subgroup.closure_induction with
    | mem x hx => exact hgen1 i x hx
    | one => rw [map_one]; exact S.one_mem
    | mul a b _ _ ha hb => rw [map_mul]; exact S.mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact S.inv_mem ha
  have hSeq : S = ⊤ := by
    refine eq_top_of_blockEmb_mem h hq2 S (fun i a => ?_)
    have := hall i (ε₂ a)
    simpa [β] using this
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  have : g ∈ S := by rw [hSeq]; trivial
  exact this

end Gen

end CFSG.HardMathSupport.Foote.ModuleExclusions

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks2Base
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaSiegel

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def diagTorusGL (q : ℕ) :
    (Fin 4 → rootsOfUnity q F) →* GL (Fin 4) F :=
  (TauCeti.diagGL (k := F) (ι := Fin 4)).comp
    (MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4))

@[expose] noncomputable def BGL (q : ℕ) : Subgroup (GL (Fin 4) F) :=
  (diagTorusGL (F := F) q).range

@[expose] noncomputable def xGL (s : Fˣ) : GL (Fin 4) F :=
  TauCeti.diagGL (fun _ : Fin 4 => s)

@[expose] noncomputable def SLGL : Subgroup (GL (Fin 4) F) :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F)).range

@[expose] noncomputable def SGL : Subgroup (GL (Fin 4) F) :=
  (unitriangular 4 F).map (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F))

@[expose] noncomputable def leviOmega (hF : 4 ≤ Nat.card F) :
    GL (Fin 4) F →* StatedOmega (StatedQuadPlus 4 F) :=
  MonoidHom.codRestrict
    (((StatedSp 4 F).subtype).comp (leviEmbedGL F 4))
    (StatedOmega (StatedQuadPlus 4 F))
    (fun A => omegaLeviGL_four_le_statedOmega hF (mem_omegaLeviGL.2 ⟨A, rfl⟩))

private theorem leviEmbedGL_injective_four [Field F] :
    Function.Injective (leviEmbedGL F 4) :=
  (CFSG.LieType.Universal.Symplectic.equivStatedSp 4 F).injective.comp
    TauCeti.GLSymplecticFin.leviHom_injective

private theorem compLeft_injective_four (q : ℕ) :
    Function.Injective (MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4)) := by
  intro p p' h
  funext i
  exact Subtype.ext (congrFun h i)

theorem leviOmega_injective (hF : 4 ≤ Nat.card F) :
    Function.Injective (leviOmega (F := F) hF) := by
  intro A B h
  apply leviEmbedGL_injective_four
  have h' : ((leviOmega (F := F) hF A : StatedOmega (StatedQuadPlus 4 F)) :
      GL (Fin 4 ⊕ Fin 4) F) =
      ((leviOmega (F := F) hF B : StatedOmega (StatedQuadPlus 4 F)) :
        GL (Fin 4 ⊕ Fin 4) F) := congrArg Subtype.val h
  simpa [leviOmega, MonoidHom.codRestrict_apply] using h'

theorem diagTorusGL_injective (q : ℕ) :
    Function.Injective (diagTorusGL (F := F) q) :=
  TauCeti.diagGL_injective.comp (compLeft_injective_four (F := F) q)

theorem card_BGL (q : ℕ) (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (BGL (F := F) q) = q ^ 4 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  change Nat.card ↥(diagTorusGL (F := F) q).range = q ^ 4
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (diagTorusGL_injective q)]
  rw [show Nat.card ↥(⊤ : Subgroup (Fin 4 → rootsOfUnity q F)) =
      Nat.card (Fin 4 → rootsOfUnity q F) from
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [Nat.card_pi]
  simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hdvd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isElemAbelian_BGL (q : ℕ) (hdvd : q ∣ Nat.card F - 1) :
    IsElemAbelian q (BGL (F := F) q) := by
  have h := (isElemAbelian_top_pi_rootsOfUnity (K := F) 4 q hdvd).map
    (diagTorusGL (F := F) q)
  change IsElemAbelian q (diagTorusGL (F := F) q).range
  rw [Subgroup.map_top] at h
  exact h

theorem xGL_mem_BGL {q : ℕ} {s : Fˣ} (hs : s ∈ rootsOfUnity q F) :
    xGL (F := F) s ∈ BGL (F := F) q := by
  change xGL (F := F) s ∈ (diagTorusGL (F := F) q).range
  exact MonoidHom.mem_range.2 ⟨fun _ => ⟨s, hs⟩, rfl⟩

theorem xGL_ne_one {s : Fˣ} (hs : s ≠ 1) : xGL (F := F) s ≠ 1 := by
  intro h
  apply hs
  have h' := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simpa [xGL, TauCeti.diagGL_coe, Matrix.diagonal_apply_eq] using h'

theorem diagGL_mem_SLGL {u : Fin 4 → Fˣ} (hdet : (∏ i, u i) = 1) :
    TauCeti.diagGL u ∈ SLGL (F := F) := by
  have hdet' : (∏ i, (u i : F)) = 1 := by
    simpa using congrArg Units.val hdet
  let A : Matrix.SpecialLinearGroup (Fin 4) F :=
    ⟨(TauCeti.diagGL u : Matrix (Fin 4) (Fin 4) F), by
      rw [TauCeti.diagGL_coe, Matrix.det_diagonal]
      exact hdet'⟩
  change TauCeti.diagGL u ∈
    (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F)).range
  exact MonoidHom.mem_range.2 ⟨A, by apply Units.ext; rfl⟩

theorem BGL_le_sup_SLGL_zpowers {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hζ : orderOf s = q) :
    BGL (F := F) q ≤ SLGL (F := F) ⊔ Subgroup.zpowers (xGL (F := F) s) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  intro b hb
  change b ∈ (diagTorusGL (F := F) q).range at hb
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hb
  rw [← hp]
  let t := (MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4)) p
  have hprod : (∏ i, t i) ∈ rootsOfUnity q F :=
    Subgroup.prod_mem _ (fun i _ => (p i).2)
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hcop : Nat.Coprime (Nat.card (rootsOfUnity q F)) 4 := by
    rw [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hdvd]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 (by
      intro hd
      have hle : q ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hd
      have h2 := hq.two_le
      have hq' : q = 2 ∨ q = 3 ∨ q = 4 := by omega
      rcases hq' with rfl | rfl | rfl
      · exact hq2 rfl
      · norm_num at hd
      · norm_num at hq)
  obtain ⟨c, hc⟩ := (powCoprime hcop).surjective
    (⟨∏ i, t i, hprod⟩ : rootsOfUnity q F)
  have hc4 : ((c : Fˣ) ^ 4) = ∏ i, t i := by
    have := congrArg Subtype.val hc
    simpa [powCoprime_apply] using this
  have hc_mem : (c : Fˣ) ∈ Subgroup.zpowers s := by
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hprim : IsPrimitiveRoot s q := hζ ▸ IsPrimitiveRoot.orderOf s
    rw [IsPrimitiveRoot.zpowers_eq hprim]
    exact c.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc_mem
  let u : Fin 4 → Fˣ := fun i => (c : Fˣ)⁻¹ * t i
  have hdetu : (∏ i, u i) = 1 := by
    have hconst : (∏ i : Fin 4, (c : Fˣ)⁻¹) = ((c : Fˣ)⁻¹) ^ 4 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
    calc (∏ i, u i) = (∏ i, (c : Fˣ)⁻¹) * (∏ i, t i) := by
          rw [Finset.prod_mul_distrib]
      _ = ((c : Fˣ)⁻¹) ^ 4 * (c : Fˣ)^4 := by rw [hconst, ← hc4]
      _ = 1 := by rw [inv_pow, inv_mul_cancel]
  have hdetu' : (∏ i, (u i : F)) = 1 := by
    simpa using congrArg Units.val hdetu
  let A : Matrix.SpecialLinearGroup (Fin 4) F :=
    ⟨(TauCeti.diagGL u : Matrix (Fin 4) (Fin 4) F), by
      rw [TauCeti.diagGL_coe, Matrix.det_diagonal]
      exact hdetu'⟩
  have hA : Matrix.SpecialLinearGroup.toGL A = TauCeti.diagGL u := by
    apply Units.ext
    rfl
  have ht : t = (fun _ : Fin 4 => (c : Fˣ)) * u := by
    funext i
    simp [u, mul_assoc]
  have hx : TauCeti.diagGL (fun _ : Fin 4 => (c : Fˣ)) = (xGL (F := F) s) ^ k := by
    rw [xGL]
    calc TauCeti.diagGL (fun _ : Fin 4 => (c : Fˣ))
        = TauCeti.diagGL (fun _ : Fin 4 => s ^ k) := by rw [← hk]
      _ = TauCeti.diagGL ((fun _ : Fin 4 => s) ^ k) := by congr 1
      _ = (TauCeti.diagGL (fun _ : Fin 4 => s)) ^ k := map_zpow _ _ _
  change (diagTorusGL (F := F) q) p ∈ SLGL (F := F) ⊔
    Subgroup.zpowers (xGL (F := F) s)
  change TauCeti.diagGL t ∈ SLGL (F := F) ⊔ Subgroup.zpowers (xGL (F := F) s)
  rw [ht, map_mul, hx]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩))
    (Subgroup.mem_sup_left (diagGL_mem_SLGL hdetu))

@[expose] noncomputable def eParam (q : ℕ) :
    (Fin 3 → rootsOfUnity q F) →* (Fin 4 → rootsOfUnity q F) where
  toFun e i := if i = 0 then e 0 else if i = 1 then e 1 else if i = 2 then e 2
    else (e 0 * e 1 * e 2)⁻¹
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' e e' := by
    funext i
    fin_cases i <;> simp [mul_assoc, mul_left_comm, mul_comm]

@[expose] noncomputable def EGL (q : ℕ) : Subgroup (GL (Fin 4) F) :=
  ((diagTorusGL (F := F) q).comp (eParam (F := F) q)).range

theorem eParam_injective (q : ℕ) : Function.Injective (eParam (F := F) q) := by
  intro e e' h
  funext i
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  fin_cases i
  · simpa [eParam] using h0
  · simpa [eParam] using h1
  · simpa [eParam] using h2

theorem eParam_det (q : ℕ) (e : Fin 3 → rootsOfUnity q F) :
    (∏ i : Fin 4, ((eParam (F := F) q e i : rootsOfUnity q F) : Fˣ)) = 1 := by
  rw [Fin.prod_univ_four]
  simp [eParam, mul_assoc, mul_left_comm, mul_comm]

theorem EGL_le_BGL (q : ℕ) : EGL (F := F) q ≤ BGL (F := F) q := by
  rintro _ ⟨e, rfl⟩
  exact MonoidHom.mem_range.2 ⟨eParam (F := F) q e, rfl⟩

theorem EGL_le_SLGL (q : ℕ) : EGL (F := F) q ≤ SLGL (F := F) := by
  rintro _ ⟨e, rfl⟩
  exact diagGL_mem_SLGL (eParam_det q e)

theorem card_EGL (q : ℕ) (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (EGL (F := F) q) = q ^ 3 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hinj : Function.Injective
      ((diagTorusGL (F := F) q).comp (eParam (F := F) q)) :=
    (diagTorusGL_injective q).comp (eParam_injective q)
  rw [EGL, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj]
  rw [show Nat.card ↥(⊤ : Subgroup (Fin 3 → rootsOfUnity q F)) =
      Nat.card (Fin 3 → rootsOfUnity q F) from
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [Nat.card_pi]
  simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := F) (d := q) hdvd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isElemAbelian_EGL (q : ℕ) (hdvd : q ∣ Nat.card F - 1) :
    IsElemAbelian q (EGL (F := F) q) := by
  have h := (isElemAbelian_top_pi_rootsOfUnity (K := F) 3 q hdvd).map
    ((diagTorusGL (F := F) q).comp (eParam (F := F) q))
  change IsElemAbelian q
    ((diagTorusGL (F := F) q).comp (eParam (F := F) q)).range
  rw [Subgroup.map_top] at h
  exact h

theorem SGL_le_SLGL : SGL (F := F) ≤ SLGL (F := F) := by
  change (unitriangular 4 F).map
    (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F)) ≤
      (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F)).range
  exact Subgroup.map_le_range _ _

theorem isPGroup_two_unitriangular_four {f : ℕ} (hpow : Nat.card F = 2 ^ f) :
    IsPGroup 2 (unitriangular 4 F) := by
  have hcard : Nat.card (unitriangular 4 F) = 2 ^ (6 * f) := by
    rw [card_unitriangular, hpow, ← pow_mul]
    congr 1
    omega
  exact IsPGroup.of_card hcard

theorem isPGroup_two_SGL {f : ℕ} (hpow : Nat.card F = 2 ^ f) :
    IsPGroup 2 (SGL (F := F)) := by
  rw [SGL]
  exact (isPGroup_two_unitriangular_four (F := F) hpow).map
    (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F))

theorem diagGL_conj_mem_SGL (t : Fin 4 → Fˣ)
    {u : Matrix.SpecialLinearGroup (Fin 4) F} (hu : u ∈ unitriangular 4 F) :
    TauCeti.diagGL t * Matrix.SpecialLinearGroup.toGL u *
        (TauCeti.diagGL t)⁻¹ ∈ SGL (F := F) := by
  let M : Matrix (Fin 4) (Fin 4) F :=
    Matrix.diagonal (fun i => (t i : F)) * (u : Matrix (Fin 4) (Fin 4) F) *
      Matrix.diagonal (fun i => ((t i : F))⁻¹)
  have hMdet : M.det = 1 := by
    have hprod : (∏ i : Fin 4, (t i : F)) * (∏ i : Fin 4, ((t i : F))⁻¹) = 1 := by
      calc (∏ i : Fin 4, (t i : F)) * (∏ i : Fin 4, ((t i : F))⁻¹)
          = ∏ i : Fin 4, ((t i : F) * ((t i : F))⁻¹) :=
            (Finset.prod_mul_distrib).symm
        _ = ∏ i : Fin 4, (1 : F) :=
            Finset.prod_congr rfl (fun i _ => mul_inv_cancel₀ (Units.ne_zero (t i)))
        _ = 1 := by simp
    dsimp only [M]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact hprod
  let A' : Matrix.SpecialLinearGroup (Fin 4) F := ⟨M, hMdet⟩
  have hentry : ∀ i j : Fin 4, M i j = (t i : F) * (u : Matrix (Fin 4) (Fin 4) F) i j *
      ((t j : F))⁻¹ := by
    intro i j
    dsimp only [M]
    rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp [mul_assoc]
  have hA' : A' ∈ unitriangular 4 F := by
    rw [mem_unitriangular]
    constructor
    · intro i j hji
      change M i j = 0
      rw [hentry i j, hu.1 i j hji]
      simp
    · intro i
      change M i i = 1
      rw [hentry i i, hu.2 i, mul_one]
      exact mul_inv_cancel₀ (Units.ne_zero (t i))
  have hconj : TauCeti.diagGL t * Matrix.SpecialLinearGroup.toGL u *
      (TauCeti.diagGL t)⁻¹ = Matrix.SpecialLinearGroup.toGL A' := by
    apply Units.ext
    change ((TauCeti.diagGL t : Matrix (Fin 4) (Fin 4) F) *
        (Matrix.SpecialLinearGroup.toGL u : Matrix (Fin 4) (Fin 4) F) *
        (((TauCeti.diagGL t)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) = M
    rw [TauCeti.diagGL_coe]
    rw [show ((TauCeti.diagGL t)⁻¹ : GL (Fin 4) F) =
        TauCeti.diagGL (fun i => (t i)⁻¹) from (map_inv _ _).symm]
    rw [TauCeti.diagGL_coe]
    rw [show ((Matrix.SpecialLinearGroup.toGL u : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) = (u : Matrix (Fin 4) (Fin 4) F) from rfl]
    dsimp only [M]
    simp [Units.val_inv_eq_inv_val]
  rw [hconj]
  change Matrix.SpecialLinearGroup.toGL A' ∈
    (unitriangular 4 F).map (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F))
  exact Subgroup.mem_map.2 ⟨A', hA', by apply Units.ext; rfl⟩

theorem BGL_le_normalizer_SGL (q : ℕ) :
    BGL (F := F) q ≤ Subgroup.normalizer (SGL (F := F) : Set (GL (Fin 4) F)) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb s hs
  change b ∈ (diagTorusGL (F := F) q).range at hb
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hb
  rw [← hp]
  change s ∈ (unitriangular 4 F).map
    (Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := F)) at hs
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hs
  change TauCeti.diagGL ((MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4)) p) *
    Matrix.SpecialLinearGroup.toGL u *
    (TauCeti.diagGL ((MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4)) p))⁻¹ ∈ SGL (F := F)
  exact diagGL_conj_mem_SGL _ hu

theorem diagGL_comm_transvection_eq {t : Fin 4 → Fˣ} {i j : Fin 4} (hij : i ≠ j)
    (hcomm : TauCeti.diagGL t *
        Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (1 : F)) =
      Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (1 : F)) * TauCeti.diagGL t) :
    t i = t j := by
  have hentry := congrArg (fun g : GL (Fin 4) F =>
    (g : Matrix (Fin 4) (Fin 4) F) i j) hcomm
  have hL : ((TauCeti.diagGL t * Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F)) : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) i j = (t i : F) := by
    rw [Units.val_mul, TauCeti.diagGL_coe]
    rw [show ((Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) =
        (Matrix.SpecialLinearGroup.transvection hij (1 : F) :
          Matrix (Fin 4) (Fin 4) F) from rfl]
    rw [Matrix.diagonal_mul, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne hij, Matrix.single_apply]
  have hR : ((Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij (1 : F)) * TauCeti.diagGL t :
        GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) i j = (t j : F) := by
    rw [Units.val_mul, TauCeti.diagGL_coe]
    rw [show ((Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)) : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) =
        (Matrix.SpecialLinearGroup.transvection hij (1 : F) :
          Matrix (Fin 4) (Fin 4) F) from rfl]
    rw [Matrix.mul_diagonal, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply]
  rw [hL, hR] at hentry
  exact Units.ext hentry

theorem BGL_inf_SLGL_inf_centralizer_le_zpowers {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {s : Fˣ} (hζ : orderOf s = q) :
    BGL (F := F) q ⊓ SLGL (F := F) ⊓
      Subgroup.centralizer (SGL (F := F) : Set (GL (Fin 4) F)) ≤
        Subgroup.zpowers (xGL (F := F) s) := by
  intro b hb
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hb
  obtain ⟨⟨hbB, -⟩, hbC⟩ := hb
  change b ∈ (diagTorusGL (F := F) q).range at hbB
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hbB
  let t := (MonoidHom.compLeft (rootsOfUnity q F).subtype (Fin 4)) p
  have hb_eq : b = TauCeti.diagGL t := hp.symm
  have htrans : ∀ {i j : Fin 4} (hijlt : i < j), t i = t j := by
    intro i j hijlt
    apply diagGL_comm_transvection_eq (t := t) hijlt.ne
    have hu : Matrix.SpecialLinearGroup.transvection hijlt.ne (1 : F) ∈ unitriangular 4 F :=
      transvection_mem_unitriangular hijlt 1
    have huS : Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hijlt.ne (1 : F)) ∈ SGL (F := F) :=
      Subgroup.mem_map.2 ⟨_, hu, by apply Units.ext; rfl⟩
    have hcb := (Subgroup.mem_centralizer_iff.mp hbC) _ huS
    rw [hb_eq] at hcb
    exact hcb.symm
  have h01 : t 0 = t 1 := htrans (by decide)
  have h12 : t 1 = t 2 := htrans (by decide)
  have h23 : t 2 = t 3 := htrans (by decide)
  have ht : t = fun _ : Fin 4 => t 0 := by
    funext i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h12.symm.trans h01.symm
    · exact h23.symm.trans (h12.symm.trans h01.symm)
  let c : rootsOfUnity q F := p 0
  have hc_mem : (c : Fˣ) ∈ Subgroup.zpowers s := by
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hprim : IsPrimitiveRoot s q := hζ ▸ IsPrimitiveRoot.orderOf s
    rw [IsPrimitiveRoot.zpowers_eq hprim]
    exact c.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc_mem
  have hx : TauCeti.diagGL (fun _ : Fin 4 => (c : Fˣ)) = (xGL (F := F) s) ^ k := by
    rw [xGL]
    calc TauCeti.diagGL (fun _ : Fin 4 => (c : Fˣ))
        = TauCeti.diagGL (fun _ : Fin 4 => s ^ k) := by rw [← hk]
      _ = TauCeti.diagGL ((fun _ : Fin 4 => s) ^ k) := by congr 1
      _ = (TauCeti.diagGL (fun _ : Fin 4 => s)) ^ k := map_zpow _ _ _
  rw [hb_eq, ht]
  have ht0 : (fun _ : Fin 4 => t 0) = fun _ : Fin 4 => (c : Fˣ) := rfl
  rw [ht0, hx]
  exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩

section Omega

@[expose] noncomputable def BOmega (hF : 4 ≤ Nat.card F) (q : ℕ) :
    Subgroup (StatedOmega (StatedQuadPlus 4 F)) :=
  (BGL (F := F) q).map (leviOmega (F := F) hF)

@[expose] noncomputable def JOmega (hF : 4 ≤ Nat.card F) :
    Subgroup (StatedOmega (StatedQuadPlus 4 F)) :=
  (SLGL (F := F)).map (leviOmega (F := F) hF)

@[expose] noncomputable def SOmega (hF : 4 ≤ Nat.card F) :
    Subgroup (StatedOmega (StatedQuadPlus 4 F)) :=
  (SGL (F := F)).map (leviOmega (F := F) hF)

@[expose] noncomputable def xOmega (s : Fˣ) : StatedOmega (StatedQuadPlus 4 F) :=
  ⟨diagOmega F 4 (fun _ => s), CFSG.SeitzReduction.F4Pilot.diagOmega_mem_statedOmega _⟩

@[simp] theorem BOmega_eq (hF : 4 ≤ Nat.card F) (q : ℕ) :
    BOmega (F := F) hF q = (BGL (F := F) q).map (leviOmega (F := F) hF) := rfl

@[simp] theorem JOmega_eq (hF : 4 ≤ Nat.card F) :
    JOmega (F := F) hF = (SLGL (F := F)).map (leviOmega (F := F) hF) := rfl

@[simp] theorem SOmega_eq (hF : 4 ≤ Nat.card F) :
    SOmega (F := F) hF = (SGL (F := F)).map (leviOmega (F := F) hF) := rfl

theorem leviOmega_xGL (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    ((leviOmega (F := F) hF (xGL (F := F) s) : StatedOmega (StatedQuadPlus 4 F)) :
      GL (Fin 4 ⊕ Fin 4) F) = diagOmega F 4 (fun _ => s) := by
  change ((leviEmbedGL F 4 (TauCeti.diagGL (fun _ : Fin 4 => s)) :
      StatedSp 4 F) : GL (Fin 4 ⊕ Fin 4) F) = diagOmega F 4 (fun _ => s)
  rw [← diagSp_apply]
  exact coe_diagSp_eq_diagOmega _

theorem xOmega_eq_leviOmega_xGL (hF : 4 ≤ Nat.card F) (s : Fˣ) :
    xOmega (F := F) s = leviOmega (F := F) hF (xGL (F := F) s) := by
  apply Subtype.ext
  exact (leviOmega_xGL (F := F) hF s).symm

theorem card_BOmega (hF : 4 ≤ Nat.card F) (q : ℕ) (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) :
    Nat.card (BOmega (F := F) hF q) = q ^ 4 := by
  rw [BOmega_eq, Subgroup.card_map_of_injective (leviOmega_injective hF)]
  exact card_BGL q hq hdvd

theorem isElemAbelian_BOmega (hF : 4 ≤ Nat.card F) (q : ℕ)
    (hdvd : q ∣ Nat.card F - 1) :
    IsElemAbelian q (BOmega (F := F) hF q) := by
  rw [BOmega_eq]
  exact (isElemAbelian_BGL (F := F) q hdvd).map (leviOmega (F := F) hF)

theorem xOmega_mem_BOmega (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hζ : orderOf s = q) :
    xOmega (F := F) s ∈ BOmega (F := F) hF q := by
  rw [BOmega_eq, xOmega_eq_leviOmega_xGL (F := F) hF s]
  exact Subgroup.mem_map.2 ⟨xGL (F := F) s,
    xGL_mem_BGL (by rw [mem_rootsOfUnity q s, ← hζ]; exact pow_orderOf_eq_one s), rfl⟩

theorem xOmega_ne_one (hF : 4 ≤ Nat.card F) {s : Fˣ} (hs : s ≠ 1) : xOmega (F := F) s ≠ 1 := by
  rw [xOmega_eq_leviOmega_xGL (F := F) hF s]
  intro h
  apply xGL_ne_one hs
  exact leviOmega_injective hF (h.trans (map_one _).symm)

theorem BOmega_le_sup_JOmega_zpowers (hF : 4 ≤ Nat.card F) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card F - 1) {s : Fˣ} (hζ : orderOf s = q) :
    BOmega (F := F) hF q ≤ JOmega (F := F) hF ⊔
      Subgroup.zpowers (xOmega (F := F) s) := by
  rw [BOmega_eq, JOmega_eq]
  refine (Subgroup.map_mono
    (BGL_le_sup_SLGL_zpowers (F := F) (s := s) hq hq2 hdvd hζ)).trans ?_
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    ← xOmega_eq_leviOmega_xGL (F := F) hF s]

theorem pRank_BOmega_inf_JOmega_ge_three (hF : 4 ≤ Nat.card F) (q : ℕ) (hq : q.Prime)
    (hdvd : q ∣ Nat.card F - 1) :
    3 ≤ CFSG.Open.pRank q (BOmega (F := F) hF q ⊓ JOmega (F := F) hF) := by
  rw [BOmega_eq, JOmega_eq]
  have hcard : Nat.card ((EGL (F := F) q).map (leviOmega (F := F) hF)) = q ^ 3 := by
    rw [Subgroup.card_map_of_injective (leviOmega_injective hF)]
    exact card_EGL q hq hdvd
  have helem : IsElemAbelian q ((EGL (F := F) q).map (leviOmega (F := F) hF)) :=
    (isElemAbelian_EGL (F := F) q hdvd).map (leviOmega (F := F) hF)
  have hle : (EGL (F := F) q).map (leviOmega (F := F) hF) ≤
      (BGL (F := F) q).map (leviOmega (F := F) hF) ⊓
        (SLGL (F := F)).map (leviOmega (F := F) hF) := by
    refine le_inf ?_ ?_
    · exact Subgroup.map_mono (EGL_le_BGL q)
    · exact Subgroup.map_mono (EGL_le_SLGL q)
  exact CFSG.SectionRank.le_pRank (p := q) hq.one_lt hle helem hcard

theorem SOmega_le_JOmega (hF : 4 ≤ Nat.card F) :
    SOmega (F := F) hF ≤ JOmega (F := F) hF := by
  rw [SOmega_eq, JOmega_eq]
  exact Subgroup.map_mono (SGL_le_SLGL (F := F))

theorem isPGroup_two_SOmega (hF : 4 ≤ Nat.card F) {f : ℕ}
    (hpow : Nat.card F = 2 ^ f) :
    IsPGroup 2 (SOmega (F := F) hF) := by
  rw [SOmega_eq]
  exact (isPGroup_two_SGL (F := F) hpow).map (leviOmega (F := F) hF)

theorem BOmega_le_normalizer_SOmega (hF : 4 ≤ Nat.card F) (q : ℕ) :
    BOmega (F := F) hF q ≤
      Subgroup.normalizer
        (SOmega (F := F) hF : Set (StatedOmega (StatedQuadPlus 4 F))) := by
  rw [BOmega_eq, SOmega_eq, Subgroup.le_normalizer_iff]
  intro b hb s hs
  obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
  have hmem := (Subgroup.le_normalizer_iff.mp (BGL_le_normalizer_SGL (F := F) q)) b' hb' s' hs'
  exact Subgroup.mem_map.2 ⟨b' * s' * b'⁻¹, hmem, by simp⟩

theorem BOmega_inf_JOmega_inf_centralizer_le_zpowers (hF : 4 ≤ Nat.card F) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card F - 1) {s : Fˣ}
    (hζ : orderOf s = q) :
    BOmega (F := F) hF q ⊓ JOmega (F := F) hF ⊓
      Subgroup.centralizer
        (SOmega (F := F) hF : Set (StatedOmega (StatedQuadPlus 4 F))) ≤
        Subgroup.zpowers (xOmega (F := F) s) := by
  rw [BOmega_eq, JOmega_eq, SOmega_eq]
  intro b hb
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at hb
  obtain ⟨⟨hbB, hbJ⟩, hbC⟩ := hb
  obtain ⟨b', hbB', hb_eq⟩ := Subgroup.mem_map.1 hbB
  have hbJ' : b' ∈ SLGL (F := F) := by
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.1 hbJ
    have : a = b' := leviOmega_injective hF (haeq.trans hb_eq.symm)
    rwa [this] at ha
  have hbC' : b' ∈ Subgroup.centralizer (SGL (F := F) : Set (GL (Fin 4) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply leviOmega_injective hF
    rw [map_mul, map_mul]
    have hhS : leviOmega (F := F) hF h ∈ ((SGL (F := F)).map (leviOmega (F := F) hF)) :=
      Subgroup.mem_map.2 ⟨h, hh, rfl⟩
    have := (Subgroup.mem_centralizer_iff.mp hbC) (leviOmega (F := F) hF h) hhS
    rw [← hb_eq] at this
    exact this
  have hmem := BGL_inf_SLGL_inf_centralizer_le_zpowers (F := F) hq hdvd hζ
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hbB', hbJ'⟩, hbC'⟩)
  rw [xOmega_eq_leviOmega_xGL (F := F) hF s]
  rw [← hb_eq]
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by rw [← hk, map_zpow]⟩

end Omega

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaSiegel

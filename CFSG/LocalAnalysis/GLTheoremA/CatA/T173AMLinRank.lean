module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem hasEnoughRootsOfUnity_of_dvd_card_sub_one {F : Type} [Field F] [Finite F]
    {n : ℕ} [NeZero n] (hn : n ∣ Nat.card F - 1) : HasEnoughRootsOfUnity F n := by
  set N := Nat.card F - 1 with hN
  have hNu : Nat.card Fˣ = N := Nat.card_units F
  have hNpos : 0 < N := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : NeZero N := ⟨by omega⟩
  have htop : rootsOfUnity N F = ⊤ := by
    ext x
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    rw [← hNu]
    exact pow_card_eq_one'
  have hNcard : N ≤ Nat.card (rootsOfUnity N F) := by
    rw [htop, Subgroup.card_top, hNu]
  haveI : HasEnoughRootsOfUnity F N := HasEnoughRootsOfUnity.of_card_le hNcard
  exact HasEnoughRootsOfUnity.of_dvd F hn

private noncomputable def linDiagHom (p d : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* GL (Fin d) F where
  toFun v := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal fun i => ((v i : Fˣ) : F)) (by
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => (v i : Fˣ).ne_zero)
  map_one' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  map_mul' v w := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.diagonal_mul_diagonal]
    simp

private def linProdHom (p d : ℕ) (F : Type) [Field F] :
    (Fin d → rootsOfUnity p F) →* rootsOfUnity p F where
  toFun v := ∏ i, v i
  map_one' := by simp
  map_mul' v w := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]

private theorem card_ker_linProdHom {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hp : p.Prime) (hd : 1 ≤ d) (hμ : Nat.card (rootsOfUnity p F) = p) :
    Nat.card (linProdHom p d F).ker = p ^ (d - 1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsurj : Function.Surjective (linProdHom p d F) := by
    intro ζ
    let i0 : Fin d := ⟨0, by omega⟩
    refine ⟨fun i => if i = i0 then ζ else 1, ?_⟩
    show (∏ i, (if i = i0 then ζ else 1)) = ζ
    rw [Finset.prod_eq_single i0]
    · simp
    · intro b _ hb
      exact if_neg hb
    · intro h
      exact absurd (Finset.mem_univ i0) h
  have hrange : (linProdHom p d F).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hsurj
  have h := Subgroup.card_ker_mul_card_range (linProdHom p d F)
  rw [hrange, Subgroup.card_top, Nat.card_fun, Nat.card_fin, hμ] at h
  have hpd : p ^ d = p ^ (d - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpd] at h
  exact Nat.eq_of_mul_eq_mul_right hp.pos h

private noncomputable def linDiagHomSL (p d : ℕ) (F : Type) [Field F] :
    ↥(linProdHom p d F).ker →* ↥(LargeEvenSLGroup (Fin d) F) where
  toFun v := ⟨linDiagHom p d F v, by
    rw [largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff]
    change (Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal fun i => (((v : Fin d → rootsOfUnity p F) i : Fˣ) : F)) _ :
        Matrix (Fin d) (Fin d) F).det = 1
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_diagonal]
    have h1 : linProdHom p d F (v : Fin d → rootsOfUnity p F) = 1 := v.2
    have h2 := congrArg (fun x : rootsOfUnity p F => ((x : Fˣ) : F)) h1
    simpa [linProdHom] using h2
    ⟩
  map_one' := Subtype.ext (by
    show linDiagHom p d F (1 : Fin d → rootsOfUnity p F) = 1
    exact map_one (linDiagHom p d F))
  map_mul' v w := Subtype.ext (by
    show linDiagHom p d F ((v : Fin d → rootsOfUnity p F) * (w : Fin d → rootsOfUnity p F)) =
      linDiagHom p d F (v : Fin d → rootsOfUnity p F) *
        linDiagHom p d F (w : Fin d → rootsOfUnity p F)
    exact map_mul (linDiagHom p d F) _ _)

private theorem psi_eq_one_scalar {Ω : Type} [Group Ω] {S : Subgroup Ω} {d : ℕ} {F : Type}
    [Field F] {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)}
    {ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S} (hψ : GLifts θ ψ)
    (u : ↥(LargeEvenSLGroup (Fin d) F)) (hu : ψ u = 1) :
    (u : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
  have h1 : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) u = 1 := by
    have h2 := hψ u
    rw [hu] at h2
    have h3 : (QuotientGroup.mk (1 : ↥S) : ↥S ⧸ Subgroup.center ↥S) = 1 :=
      map_one (QuotientGroup.mk' (Subgroup.center ↥S))
    rw [h3, map_one] at h2
    exact h2.symm
  have h3 : u ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)).ker := h1
  rw [QuotientGroup.ker_mk'] at h3
  exact Subgroup.mem_subgroupOf.1 h3

private theorem diagonal_conj_transvection {d : ℕ} {F : Type} [Field F]
    {a b : Fin d → F} (hab : ∀ k, a k * b k = 1) (i j : Fin d) (x : F) :
    Matrix.diagonal a * Matrix.transvection i j x * Matrix.diagonal b =
      Matrix.transvection i j (a i * x * b j) := by
  have h1 : Matrix.diagonal a * Matrix.single i j x = Matrix.single i j (a i * x) := by
    ext p q
    by_cases hip : i = p
    · subst hip
      simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hip]
  have h2 : Matrix.single i j (a i * x) * Matrix.diagonal b =
      Matrix.single i j (a i * x * b j) := by
    ext p q
    by_cases hjq : j = q
    · subst hjq
      simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hjq]
  have h3 : Matrix.diagonal (fun k => a k * b k) = (1 : Matrix (Fin d) (Fin d) F) := by
    ext p q
    by_cases h : p = q
    · subst h
      simp [hab p]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  calc Matrix.diagonal a * Matrix.transvection i j x * Matrix.diagonal b
      = Matrix.diagonal a * (1 + Matrix.single i j x) * Matrix.diagonal b := rfl
    _ = (Matrix.diagonal a + Matrix.diagonal a * Matrix.single i j x) * Matrix.diagonal b := by
          rw [Matrix.mul_add, Matrix.mul_one]
    _ = Matrix.diagonal a * Matrix.diagonal b +
          (Matrix.diagonal a * Matrix.single i j x) * Matrix.diagonal b := by
          rw [Matrix.add_mul]
    _ = Matrix.diagonal (fun k => a k * b k) + Matrix.single i j (a i * x * b j) := by
          rw [Matrix.diagonal_mul_diagonal, h1, h2]
    _ = 1 + Matrix.single i j (a i * x * b j) := by rw [h3]
    _ = Matrix.transvection i j (a i * x * b j) := rfl

private theorem linDiagHom_scalar_const {p d : ℕ} {F : Type} [Field F] (hd : 1 ≤ d)
    {v : Fin d → rootsOfUnity p F}
    (h : linDiagHom p d F v ∈ LargeEvenScalars (Fin d) F) :
    ∃ c : rootsOfUnity p F, v = fun _ => c := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h
  let i0 : Fin d := ⟨0, by omega⟩
  have entry : ∀ i : Fin d, c = (v i : Fˣ) := by
    intro i
    apply Units.ext
    have h2 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i i) hc
    simpa [linDiagHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h2
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rw [entry i0]
    exact (v i0).2
  · funext i
    apply Subtype.ext
    exact (entry i).symm

private theorem linDiagHom_val (p d : ℕ) (F : Type) [Field F]
    (v : Fin d → rootsOfUnity p F) :
    ((linDiagHom p d F v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => ((v k : Fˣ) : F)) := by
  change (Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal fun k => ((v k : Fˣ) : F)) _ :
      Matrix (Fin d) (Fin d) F) = Matrix.diagonal _
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private theorem linDiagHom_inv_val (p d : ℕ) (F : Type) [Field F]
    (v : Fin d → rootsOfUnity p F) :
    ((linDiagHom p d F v⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun k => (((v k : Fˣ)⁻¹ : Fˣ) : F)) := by
  rw [linDiagHom_val]
  rfl

private theorem linDiagHom_conj_transv_mat (p d : ℕ) (F : Type) [Field F]
    (v : Fin d → rootsOfUnity p F) (i j : Fin d) :
    ((linDiagHom p d F v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        Matrix.transvection i j (1 : F) *
        ((linDiagHom p d F v⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
      = Matrix.transvection i j (((v i : Fˣ) : F) * (((v j : Fˣ) : F))⁻¹) := by
  rw [linDiagHom_val, linDiagHom_inv_val]
  have hab : ∀ k, ((v k : Fˣ) : F) * (((v k : Fˣ)⁻¹ : Fˣ) : F) = 1 := by
    intro k
    have h := congrArg (fun u : Fˣ => (u : F)) (mul_inv_cancel (v k : Fˣ))
    simpa using h
  have hmain := diagonal_conj_transvection
    (a := fun k => ((v k : Fˣ) : F)) (b := fun k => (((v k : Fˣ)⁻¹ : Fˣ) : F)) hab i j 1
  simpa using hmain

private theorem linDiag_sl_scalar_of_central {p d : ℕ} {F : Type} [Field F] (hd : 2 ≤ d)
    {v : Fin d → rootsOfUnity p F}
    (hv : linDiagHom p d F v ∈ LargeEvenSLGroup (Fin d) F)
    (hcen : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) ⟨linDiagHom p d F v, hv⟩ ∈
      Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) F))) :
    linDiagHom p d F v ∈ LargeEvenScalars (Fin d) F := by
  have hconst : ∀ i j : Fin d, i ≠ j → v i = v j := by
    intro i j hij
    set T : GL (Fin d) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.transvection i j (1 : F))
      (by rw [Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero) with hTdef
    have hTval : (T : Matrix (Fin d) (Fin d) F) = Matrix.transvection i j (1 : F) := by
      rw [hTdef, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    have hTmem : T ∈ LargeEvenSLGroup (Fin d) F := by
      rw [largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff, hTval,
        Matrix.det_transvection_of_ne i j hij]
    let TS : ↥(LargeEvenSLGroup (Fin d) F) := ⟨T, hTmem⟩
    let t : ↥(LargeEvenSLGroup (Fin d) F) := ⟨linDiagHom p d F v, hv⟩
    let x1 : ↥(LargeEvenSLGroup (Fin d) F) := t * TS * t⁻¹
    have hx1 : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) x1 =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) TS := by
      show LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) (t * TS * t⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      have hcomm : LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) t *
          LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) TS =
          LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) TS *
            LargeEvenProjMk (LargeEvenSLGroup (Fin d) F) t :=
        ((Subgroup.mem_center_iff.mp hcen) _).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨z, hzker, hxz⟩ := (QuotientGroup.mk'_eq_mk'
      (N := (LargeEvenScalars (Fin d) F).subgroupOf (LargeEvenSLGroup (Fin d) F))).mp hx1
    have hzsc : (z : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
      Subgroup.mem_subgroupOf.1 hzker
    obtain ⟨ζ, hζ⟩ := MonoidHom.mem_range.1 hzsc
    have hx1mat : (((x1 : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) =
        Matrix.transvection i j (((v i : Fˣ) : F) * (((v j : Fˣ) : F))⁻¹) := by
      show (((t * TS * t⁻¹ : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = _
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show ((linDiagHom p d F v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          (T : Matrix (Fin d) (Fin d) F) *
          (((linDiagHom p d F v : GL (Fin d) F)⁻¹ : GL (Fin d) F) :
            Matrix (Fin d) (Fin d) F) = _
      rw [hTval, ← map_inv]
      exact linDiagHom_conj_transv_mat p d F v i j
    have hmat : (x1 : GL (Fin d) F) * (z : GL (Fin d) F) = T := by
      have := congrArg (fun g : ↥(LargeEvenSLGroup (Fin d) F) => (g : GL (Fin d) F)) hxz
      simpa [x1, TS] using this
    have hmul : ((x1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        ((z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        (T : Matrix (Fin d) (Fin d) F) := by
      have := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F)) hmat
      simpa using this
    have hζm : ((z : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun _ => (ζ : F)) := by
      rw [← hζ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hii : ((x1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i = 1 := by
      rw [hx1mat]
      simp [Matrix.transvection, Matrix.single_apply, hij, Ne.symm hij]
    have hζ1 : ζ = 1 := by
      have h1 := congrArg (fun m : Matrix (Fin d) (Fin d) F => m i i) hmul
      simp [hζm, Matrix.mul_diagonal, hii, hTval, Matrix.transvection, Matrix.single_apply,
        hij, Ne.symm hij] at h1
      exact h1
    have hcoeff : ((v i : Fˣ) : F) * (((v j : Fˣ) : F))⁻¹ = 1 := by
      have h1 := congrArg (fun m : Matrix (Fin d) (Fin d) F => m i j) hmul
      simp [hζm, Matrix.mul_diagonal, hx1mat, hζ1, hTval, Matrix.transvection,
        Matrix.single_apply, hij] at h1
      exact h1
    have hcoeff' : ((v i : Fˣ) : F) = ((v j : Fˣ) : F) :=
      (mul_inv_eq_one₀ (v j : Fˣ).ne_zero).mp hcoeff
    exact Subtype.ext (Units.ext hcoeff')
  let i0 : Fin d := ⟨0, by omega⟩
  have hvconst : v = fun _ => v i0 := by
    funext i
    by_cases hi : i = i0
    · subst hi; rfl
    · exact hconst i i0 hi
  rw [hvconst]
  refine ⟨v i0, ?_⟩
  apply Units.ext
  ext p q
  by_cases h : p = q
  · subst h
    simp [linDiagHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  · simp [linDiagHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, h]

private noncomputable def linConstHom (p d : ℕ) (F : Type) [Field F] (hpd : p ∣ d) :
    rootsOfUnity p F →* ↥(linProdHom p d F).ker where
  toFun c := ⟨fun _ => c, by
    change (∏ _i : Fin d, c) = 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    obtain ⟨k, rfl⟩ := hpd
    rw [pow_mul]
    have hcp : c ^ p = 1 := Subtype.ext c.2
    rw [hcp, one_pow]⟩
  map_one' := Subtype.ext (funext fun _ => rfl)
  map_mul' c c' := Subtype.ext (funext fun _ => rfl)

private theorem linConstHom_injective (p d : ℕ) (F : Type) [Field F] (hpd : p ∣ d)
    (hd : 1 ≤ d) : Function.Injective (linConstHom p d F hpd) := by
  intro c c' h
  have h2 := congrArg (fun v : ↥(linProdHom p d F).ker =>
    ((v : Fin d → rootsOfUnity p F) ⟨0, by omega⟩)) h
  simpa [linConstHom] using h2

private theorem card_linConst_range {p d : ℕ} {F : Type} [Field F] [Finite F]
    (hpd : p ∣ d) (hd : 1 ≤ d) (hμ : Nat.card (rootsOfUnity p F) = p) :
    Nat.card (linConstHom p d F hpd).range = p := by
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (linConstHom_injective p d F hpd hd),
    Subgroup.card_top, hμ]

private theorem isElemAbelian_map {p : ℕ} {G H : Type} [Group G] [Group H]
    (f : G →* H) {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨a', ha', hfa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hfb⟩ := Subgroup.mem_map.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hfa, ← hfb, ← map_mul, ← map_mul,
      hE.comm ha' hb']
  · intro x hx
    obtain ⟨a', ha', hfa⟩ := Subgroup.mem_map.mp hx
    rw [← hfa, ← map_pow, hE.2 a' ha', map_one]

private theorem isElemAbelian_top_fun (p d : ℕ) (F : Type) [Field F] :
    IsElemAbelian p (⊤ : Subgroup (Fin d → rootsOfUnity p F)) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (funext fun i => mul_comm _ _)⟩⟩, ?_⟩
  · intro x hx
    funext i
    exact Subtype.ext (x i).2

private theorem isElemAbelian_top_ker (p d : ℕ) (F : Type) [Field F] :
    IsElemAbelian p (⊤ : Subgroup ↥(linProdHom p d F).ker) := by
  have h := IsElemAbelian.comap (p := p) (isElemAbelian_top_fun p d F)
    (f := (linProdHom p d F).ker.subtype) Subtype.coe_injective
  simpa using h

private noncomputable def linRootHom (d : ℕ) (F : Type) [Field F] (i j : Fin d) (hij : i ≠ j) :
    Multiplicative F →* ↥(LargeEvenSLGroup (Fin d) F) where
  toFun c := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.transvection i j (Multiplicative.toAdd c) : Matrix (Fin d) (Fin d) F)
      (by rw [Matrix.det_transvection_of_ne (R := F) i j hij]; exact one_ne_zero), by
    rw [largeEvenSLGroup_eq_statedSL, StatedAPI.mem_statedSL_iff]
    exact Matrix.det_transvection_of_ne (R := F) i j hij (Multiplicative.toAdd c)⟩
  map_one' := Subtype.ext (by
    apply Matrix.GeneralLinearGroup.ext
    intro p q
    simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.transvection, Matrix.single_apply,
      Matrix.one_apply, toAdd_one])
  map_mul' c c' := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    rw [toAdd_mul]
    exact (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij
      (Multiplicative.toAdd c) (Multiplicative.toAdd c')).symm

private theorem linRootHom_val (d : ℕ) (F : Type) [Field F] (i j : Fin d) (hij : i ≠ j)
    (c : Multiplicative F) :
    (((linRootHom d F i j hij c : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = Matrix.transvection i j (Multiplicative.toAdd c) := by
  simp [linRootHom, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private theorem linRootHom_injective (d : ℕ) (F : Type) [Field F] (i j : Fin d) (hij : i ≠ j) :
    Function.Injective (linRootHom d F i j hij) := by
  intro c c' h
  have h2 := congrArg (fun g : ↥(LargeEvenSLGroup (Fin d) F) =>
    (((g : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F)) h
  rw [linRootHom_val, linRootHom_val] at h2
  have h3 := congrArg (fun m : Matrix (Fin d) (Fin d) F => m i j) h2
  simp [Matrix.transvection, Matrix.single_apply, hij] at h3
  exact Multiplicative.ofAdd.injective (by simpa using h3)

private theorem card_linRootHom_range (d : ℕ) (F : Type) [Field F] [Finite F]
    (i j : Fin d) (hij : i ≠ j) :
    Nat.card (linRootHom d F i j hij).range = Nat.card F := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (linRootHom_injective d F i j hij),
    Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

private theorem isPGroup_linRootHom_range {n d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (i j : Fin d) (hij : i ≠ j) :
    IsPGroup 2 (linRootHom d F i j hij).range := by
  apply IsPGroup.of_card (n := n)
  rw [card_linRootHom_range, hF]

private theorem conj_linRootHom (p d : ℕ) (F : Type) [Field F]
    (v : Fin d → rootsOfUnity p F) (i j : Fin d) (hij : i ≠ j) (c : Multiplicative F) :
    (linDiagHom p d F v : GL (Fin d) F) * (linRootHom d F i j hij c : GL (Fin d) F) *
        (linDiagHom p d F v : GL (Fin d) F)⁻¹ =
      (linRootHom d F i j hij (Multiplicative.ofAdd
        (((v i : Fˣ) : F) * Multiplicative.toAdd c * (((v j : Fˣ) : F))⁻¹)) :
        GL (Fin d) F) := by
  apply Units.ext
  rw [show ((linDiagHom p d F v : GL (Fin d) F)⁻¹ : GL (Fin d) F) =
      linDiagHom p d F v⁻¹ from (map_inv (linDiagHom p d F) v).symm]
  rw [Units.val_mul, Units.val_mul, linDiagHom_val, linDiagHom_inv_val,
    linRootHom_val, linRootHom_val]
  simp only [toAdd_ofAdd]
  have hab : ∀ k, ((v k : Fˣ) : F) * (((v k : Fˣ)⁻¹ : Fˣ) : F) = 1 := by
    intro k
    have h := congrArg (fun u : Fˣ => (u : F)) (mul_inv_cancel (v k : Fˣ))
    simpa using h
  have hmain := diagonal_conj_transvection
    (a := fun k => ((v k : Fˣ) : F)) (b := fun k => (((v k : Fˣ)⁻¹ : Fˣ) : F)) hab i j
    (Multiplicative.toAdd c)
  simpa using hmain

private theorem conj_rootHom_mem (p d : ℕ) (F : Type) [Field F]
    (i j : Fin d) (hij : i ≠ j) (v : ↥(linProdHom p d F).ker) (c : Multiplicative F) :
    linDiagHomSL p d F v * linRootHom d F i j hij c * (linDiagHomSL p d F v)⁻¹ ∈
      (linRootHom d F i j hij).range := by
  refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd
    ((((v : Fin d → rootsOfUnity p F) i : Fˣ) : F) * Multiplicative.toAdd c *
      ((((v : Fin d → rootsOfUnity p F) j : Fˣ) : F))⁻¹), Subtype.ext ?_⟩
  exact (conj_linRootHom p d F (v : Fin d → rootsOfUnity p F) i j hij c).symm

private theorem linDiagHomSL_mem_normalizer_root (p d : ℕ) (F : Type) [Field F] [Finite F]
    (i j : Fin d) (hij : i ≠ j) (v : ↥(linProdHom p d F).ker) :
    linDiagHomSL p d F v ∈ Subgroup.normalizer
      ((linRootHom d F i j hij).range : Set ↥(LargeEvenSLGroup (Fin d) F)) := by
  haveI : Finite ↥(linRootHom d F i j hij).range := Subtype.finite
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro k hk
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hk
    rw [← hc]
    show MulAut.conj (linDiagHomSL p d F v) (linRootHom d F i j hij c) ∈
      (linRootHom d F i j hij).range
    exact conj_rootHom_mem p d F i j hij v c
  · rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj (linDiagHomSL p d F v) :
        ↥(LargeEvenSLGroup (Fin d) F) →* ↥(LargeEvenSLGroup (Fin d) F)))
      (MulAut.conj (linDiagHomSL p d F v)).injective]

theorem lin_rank_bmax {p n d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω}
    {x : Ω} (hcfg : Cfg173 p S B N D K x) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : p ∣ d) (hpF : p ∣ 2 ^ n - 1)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S) (hψ : GLifts θ ψ) :
    p ^ (d - 1) ≤ Nat.card B := by
  classical
  have hp : p.Prime := hcfg.prime
  have hpdvd : p ∣ d := hpd
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hμ : Nat.card (rootsOfUnity p F) = p := by
    have hdvd : p ∣ Nat.card F - 1 := by rw [hF]; exact hpF
    haveI : HasEnoughRootsOfUnity F p := hasEnoughRootsOfUnity_of_dvd_card_sub_one hdvd
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity F p
  let SL := LargeEvenSLGroup (Fin d) F
  let D := (linProdHom p d F).ker
  let g : D →* ↥SL := linDiagHomSL p d F
  let Ψ : D →* ↥S := ψ.comp g
  let E : Subgroup ↥S := Ψ.range
  let EΩ : Subgroup Ω := E.map S.subtype
  have hDcard : Nat.card D = p ^ (d - 1) := card_ker_linProdHom hp hd1 hμ
  have hEcard' : Nat.card Ψ.ker * Nat.card E = p ^ (d - 1) := by
    have h := Subgroup.card_ker_mul_card_range Ψ
    rw [hDcard] at h
    exact h
  have hEΩ_card : Nat.card EΩ = Nat.card E :=
    Subgroup.card_map_of_injective (f := S.subtype) Subtype.coe_injective
  have hEel : IsElemAbelian p E := by
    have h1 : IsElemAbelian p ((⊤ : Subgroup D).map Ψ) :=
      isElemAbelian_map Ψ (isElemAbelian_top_ker p d F)
    simpa [E, MonoidHom.range_eq_map] using h1
  have hEΩ_el : IsElemAbelian p EΩ := isElemAbelian_map S.subtype hEel
  let X : Subgroup Ω := Subgroup.zpowers x ⊔ EΩ
  let Y : Subgroup Ω := Subgroup.zpowers x ⊓ EΩ
  have hker_le : Nat.card Ψ.ker ≤ p := by
    have hinj : Function.Injective (fun v : Ψ.ker =>
        (((v : D) : Fin d → rootsOfUnity p F) ⟨0, by omega⟩)) := by
      intro v w hvw
      have hsc : ∀ u : Ψ.ker, linDiagHom p d F ((u : D) : Fin d → rootsOfUnity p F) ∈
          LargeEvenScalars (Fin d) F := by
        intro u
        have h2 : ψ (g (u : D)) = 1 := u.2
        have h3 : (g (u : D) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
          psi_eq_one_scalar hψ (g (u : D)) h2
        exact h3
      obtain ⟨cv, hvc⟩ := linDiagHom_scalar_const (p := p) hd1 (hsc v)
      obtain ⟨cw, hwc⟩ := linDiagHom_scalar_const (p := p) hd1 (hsc w)
      have hvw' : cv = cw := by
        have h := hvw
        change ((v : D) : Fin d → rootsOfUnity p F) ⟨0, by omega⟩ =
          ((w : D) : Fin d → rootsOfUnity p F) ⟨0, by omega⟩ at h
        rw [hvc, hwc] at h
        simpa using h
      apply Subtype.ext
      apply Subtype.ext
      rw [hvc, hwc, hvw']
    calc Nat.card Ψ.ker ≤ Nat.card (rootsOfUnity p F) :=
          Nat.card_le_card_of_injective _ hinj
      _ = p := hμ
  have hEge : p ^ (d - 2) ≤ Nat.card E := by
    have h2 : p ^ (d - 1) ≤ p * Nat.card E := by
      rw [← hEcard']
      exact Nat.mul_le_mul_right _ hker_le
    have h1 : p ^ (d - 1) = p * p ^ (d - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [h1] at h2
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have hxcentS : ∀ s ∈ S, x * s = s * x := by
    have hxcent : x ∈ Subgroup.centralizer (S : Set Ω) :=
      (hcfg.cent x hcfg.mem).mpr (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp hxcent s hs).symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
  have hx_el : IsElemAbelian p (Subgroup.zpowers x) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hcfg.elem.2 x hcfg.mem
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ EΩ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨e, he, hbe⟩ := Subgroup.mem_map.mp hb
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp he
    subst hv
    have hbS : (ψ (g v) : Ω) ∈ S := (ψ (g v)).2
    have hcv : Commute x (ψ (g v) : Ω) := hxcentS _ hbS
    have hthis := hcv.zpow_left m
    rw [← hbe]
    exact hthis
  have hsup_el : IsElemAbelian p X := by
    have h := IsElemAbelian.sup_of_commute hx_el hEΩ_el hcomm
    simpa [X] using h
  let i0 : Fin d := ⟨0, by omega⟩
  let j0 : Fin d := ⟨1, by omega⟩
  have hij0 : i0 ≠ j0 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, j0] at this
  let R : Subgroup ↥SL := (linRootHom d F i0 j0 hij0).range
  have hR2 : IsPGroup 2 R := isPGroup_linRootHom_range (n := n) hF i0 j0 hij0
  let U0 : Subgroup ↥S := R.map ψ
  let U0Ω : Subgroup Ω := U0.map S.subtype
  have hU0Ω_2 : IsPGroup 2 U0Ω := by
    have h := (hR2.map ψ).map S.subtype
    simpa [U0Ω, U0] using h
  have hU0Ω_ne : U0Ω ≠ ⊥ := by
    intro hbot
    have h1 : ψ (linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F))) ∈ U0 :=
      Subgroup.mem_map_of_mem ψ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    have h2 : (ψ (linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F))) : Ω) ∈ U0Ω :=
      Subgroup.mem_map_of_mem S.subtype h1
    rw [hbot] at h2
    have h3' : (ψ (linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F))) : Ω) = 1 :=
      Subgroup.mem_bot.mp h2
    have h3 : ψ (linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F))) = 1 :=
      Subtype.ext (by simpa using h3')
    have hsc : (linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F)) : GL (Fin d) F) ∈
        LargeEvenScalars (Fin d) F :=
      psi_eq_one_scalar hψ _ h3
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hsc
    have hoff : ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) i0 j0 = 0 := by
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        hij0]
    have hon : (((linRootHom d F i0 j0 hij0 (Multiplicative.ofAdd (1 : F)) : ↥SL) :
        GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i0 j0 = 1 := by
      rw [linRootHom_val]
      simp [Matrix.transvection, Matrix.single_apply, hij0]
    have h1' := congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F) i0 j0) hc
    rw [hoff, hon] at h1'
    exact zero_ne_one h1'
  have hEΩ_norm : EΩ ≤ Subgroup.normalizer (U0Ω : Set Ω) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp he
    have h1 : ψ (g v) ∈ Subgroup.normalizer (U0 : Set ↥S) :=
      Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ
        (linDiagHomSL_mem_normalizer_root p d F i0 j0 hij0 v))
    exact Subgroup.le_normalizer_map S.subtype (Subgroup.mem_map_of_mem S.subtype h1)
  have hx_norm : Subgroup.zpowers x ≤ Subgroup.normalizer (U0Ω : Set Ω) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
      have hxs : x * (s : Ω) * x⁻¹ = (s : Ω) := by
        rw [hxcentS s s.2, mul_assoc, mul_inv_cancel, mul_one]
      change x * (s : Ω) * x⁻¹ ∈ U0Ω
      rw [hxs]
      exact Subgroup.mem_map_of_mem S.subtype hs
    · intro hk
      have hyS : x * k * x⁻¹ ∈ S := by
        obtain ⟨s, hs, hflip⟩ := Subgroup.mem_map.mp hk
        rw [← hflip]
        exact s.2
      have hc := hxcentS (x * k * x⁻¹) hyS
      have hcomm_y : x⁻¹ * (x * k * x⁻¹) * x = x * k * x⁻¹ := by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      have hk_eq : k = x * k * x⁻¹ := by
        calc k = x⁻¹ * (x * k * x⁻¹) * x := by group
          _ = x * k * x⁻¹ := hcomm_y
      rw [hk_eq]
      exact hk
  have hsup_norm : X ≤ Subgroup.normalizer (U0Ω : Set Ω) := by
    have h := sup_le hx_norm hEΩ_norm
    simpa [X] using h
  have hupper : Nat.card X ≤ Nat.card B := by
    rw [show Nat.card B = p ^ GLATwoLocalRank p Ω from hcfg.bmax.2.1]
    exact card_le_pow_glaTwoLocalRank hp hsup_el hU0Ω_ne hU0Ω_2 hsup_norm
  have hlower : p ^ (d - 1) ≤ Nat.card X := by
    by_cases hxE : x ∈ EΩ
    · have hsup_eq : X = EΩ := by
        have h := sup_eq_right.mpr (Subgroup.zpowers_le.mpr hxE)
        simpa [X] using h
      have hker_le_D0 : Ψ.ker ≤ (linConstHom p d F hpd).range := by
        intro v hv
        have hsc : linDiagHom p d F ((v : D) : Fin d → rootsOfUnity p F) ∈
            LargeEvenScalars (Fin d) F := by
          have h2 : ψ (g (v : D)) = 1 := hv
          have h3 : (g (v : D) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F :=
            psi_eq_one_scalar hψ (g (v : D)) h2
          exact h3
        obtain ⟨c, hc⟩ := linDiagHom_scalar_const (p := p) hd1 hsc
        exact MonoidHom.mem_range.mpr ⟨c, Subtype.ext hc.symm⟩
      have hk1 : Nat.card Ψ.ker = 1 := by
        have hk_dvd : Nat.card Ψ.ker ∣ p ^ (d - 1) := ⟨Nat.card E, hEcard'.symm⟩
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).mp hk_dvd
        have hle : p ^ j ≤ p ^ 1 := by
          rw [← hj']
          simpa using hker_le
        have hj1 : j ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
        interval_cases j
        · simpa using hj'
        · exfalso
          have hkp : Nat.card Ψ.ker = p := by simpa using hj'
          have hD0_le : (linConstHom p d F hpd).range ≤ Ψ.ker := by
            have heq : Ψ.ker = (linConstHom p d F hpd).range :=
              Subgroup.eq_of_le_of_card_ge hker_le_D0
                (by rw [card_linConst_range hpd hd1 hμ, hkp])
            rw [heq]
          obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hxE
          obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp he
          have hxt : (ψ (g t) : Ω) = x := by
            change (Ψ t : Ω) = x
            rw [ht]
            exact hex
          have hcentral : ∀ y : ↥S, ψ (g t) * y = y * ψ (g t) := by
            intro y
            apply Subtype.ext
            rw [show ((ψ (g t) * y : ↥S) : Ω) = (ψ (g t) : Ω) * (y : Ω) from rfl,
                show ((y * ψ (g t) : ↥S) : Ω) = (y : Ω) * (ψ (g t) : Ω) from rfl, hxt]
            exact hxcentS (y : Ω) y.2
          have hmk : QuotientGroup.mk (ψ (g t)) ∈
              Subgroup.center (↥S ⧸ Subgroup.center ↥S) := by
            rw [Subgroup.mem_center_iff]
            intro y
            obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) y
            change QuotientGroup.mk' (Subgroup.center ↥S) y' *
                QuotientGroup.mk' (Subgroup.center ↥S) (ψ (g t)) =
              QuotientGroup.mk' (Subgroup.center ↥S) (ψ (g t)) *
                QuotientGroup.mk' (Subgroup.center ↥S) y'
            rw [← map_mul, ← map_mul]
            congr 1
            exact (hcentral y').symm
          have hπ : LargeEvenProjMk SL (g t) ∈ Subgroup.center (LargeEvenProj SL) := by
            have hθ : θ (QuotientGroup.mk (ψ (g t))) = LargeEvenProjMk SL (g t) := hψ (g t)
            rw [← hθ]
            rw [Subgroup.mem_center_iff]
            intro y
            obtain ⟨y', rfl⟩ := θ.surjective y
            rw [← map_mul, ← map_mul]
            congr 1
            exact Subgroup.mem_center_iff.mp hmk y'
          have hsc := linDiag_sl_scalar_of_central (p := p) hd2
            (v := (t : Fin d → rootsOfUnity p F)) ((g t).2) hπ
          have ht_const : (t : D) ∈ (linConstHom p d F hpd).range := by
            obtain ⟨c, hc⟩ := linDiagHom_scalar_const (p := p) hd1 hsc
            exact MonoidHom.mem_range.mpr ⟨c, Subtype.ext hc.symm⟩
          have ht_mem : t ∈ Ψ.ker := hD0_le ht_const
          have hx1 : x = 1 := by
            rw [← hex, ← ht]
            exact congrArg (fun z : ↥S => (z : Ω)) ht_mem
          exact hcfg.ne_one hx1
      have hE_eq : Nat.card E = p ^ (d - 1) := by
        rw [← hEcard', hk1, one_mul]
      rw [hsup_eq, hEΩ_card, hE_eq]
    · have hdisj : Y = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        have hdvd : Nat.card Y ∣ p := by
          rw [← hxcard]
          exact Subgroup.card_dvd_of_le (H := Y) (K := Subgroup.zpowers x) inf_le_left
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h2
        · exact h1
        · exfalso
          have heq : Y = Subgroup.zpowers x :=
            Subgroup.eq_of_le_of_card_ge (H := Y) (K := Subgroup.zpowers x)
              inf_le_left (le_of_eq (by rw [hxcard, h2]))
          have hle : Subgroup.zpowers x ≤ EΩ := by
            have h : Y ≤ EΩ := inf_le_right
            rw [heq] at h
            exact h
          exact hxE (hle (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
      have hprod : Nat.card (Subgroup.zpowers x) * Nat.card EΩ ≤ Nat.card X := by
        let f : Subgroup.zpowers x × EΩ → ↥X :=
          fun q => ⟨(q.1 : Ω) * (q.2 : Ω), by
            have h1 : (q.1 : Ω) ∈ X :=
              Subgroup.mem_sup_left (S := Subgroup.zpowers x) (T := EΩ) q.1.2
            have h2 : (q.2 : Ω) ∈ X :=
              Subgroup.mem_sup_right (S := Subgroup.zpowers x) (T := EΩ) q.2.2
            exact X.mul_mem h1 h2⟩
        have hinj : Function.Injective f := by
          rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ heq
          have heq' : (a1 : Ω) * (b1 : Ω) = (a2 : Ω) * (b2 : Ω) := by
            simpa [f] using congrArg Subtype.val heq
          have habs : (a2⁻¹ * a1 : Ω) = b2 * b1⁻¹ := by
            calc (a2⁻¹ * a1 : Ω) = a2⁻¹ * (a1 * b1) * b1⁻¹ := by group
              _ = a2⁻¹ * (a2 * b2) * b1⁻¹ := by rw [heq']
              _ = b2 * b1⁻¹ := by group
          have hmem : (a2⁻¹ * a1 : Ω) ∈ Y := by
            refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · show (a2⁻¹ * a1 : Ω) ∈ Subgroup.zpowers x
              exact (Subgroup.zpowers x).mul_mem ((Subgroup.zpowers x).inv_mem ha2) ha1
            · rw [habs]
              exact EΩ.mul_mem hb2 (EΩ.inv_mem hb1)
          rw [hdisj] at hmem
          have haa : a2⁻¹ * a1 = 1 := Subgroup.mem_bot.mp hmem
          have hbb : b2 * b1⁻¹ = 1 := by rw [← habs]; exact haa
          exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp haa).symm)
            (Subtype.ext (mul_inv_eq_one.mp hbb).symm)
        have hc := Nat.card_le_card_of_injective f hinj
        rwa [Nat.card_prod] at hc
      calc p ^ (d - 1) = p * p ^ (d - 2) := by rw [← pow_succ']; congr 1; omega
        _ ≤ p * Nat.card EΩ := Nat.mul_le_mul_left p (by rw [hEΩ_card]; exact hEge)
        _ = Nat.card (Subgroup.zpowers x) * Nat.card EΩ := by rw [hxcard]
        _ ≤ Nat.card X := hprod
  exact hlower.trans hupper

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

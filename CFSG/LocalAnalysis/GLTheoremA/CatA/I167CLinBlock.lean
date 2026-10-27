module

import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped commutatorElement

structure LinBlock (K : Type) [Field K] [Finite K] {n : ℕ} (g : GL (Fin n) K) where
  r : ℕ
  D : Fin r → Type
  d : Fin r → ℕ
  [fld : ∀ i, Field (D i)]
  [fin : ∀ i, Finite (D i)]
  [alg : ∀ i, Algebra K (D i)]
  Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[K] Matrix (Fin n) (Fin n) K
  θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) K
  pos : ∀ i, 1 ≤ d i
  Φinj : Function.Injective Φ
  θinj : Function.Injective θ
  θrange : θ.range = Subgroup.centralizer ({g} : Set (GL (Fin n) K))
  θapply : ∀ w, ((θ w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)))
  Φrange : ∀ X : Matrix (Fin n) (Fin n) K,
    X * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * X → X ∈ Set.range Φ

attribute [instance] LinBlock.fld LinBlock.fin LinBlock.alg

private theorem i167CLin_block_exists_aux1 {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup (GL (Fin n) K)) :
      Set (GL (Fin n) K)) = Subgroup.centralizer ({g} : Set (GL (Fin n) K)) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hx _ (Subgroup.mem_zpowers _)
  · intro hx h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute g x := hx g (Set.mem_singleton g)
    exact (hc.zpow_left k).eq

private theorem i167CLin_block_exists_aux2 {K : Type} [Field K] [Finite K] {n : ℕ}
    (g : GL (Fin n) K) (hord : ((orderOf g : ℕ) : K) ≠ 0) : Nonempty (LinBlock K g) := by
  classical
  have hA : (Nat.card (Subgroup.zpowers g) : K) ≠ 0 := by
    rw [Nat.card_zpowers]
    exact hord
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hNZ, hΦinj, hΦrange, hθinj, hθrange, hθapply⟩ :=
    CFSG.StandardType.LinNonsplit.exists_piMat_commutant (Subgroup.zpowers g) hA
  letI : ∀ i, Field (D i) := hFld
  haveI : ∀ i, Finite (D i) := hFin
  have hΦrange' : ∀ X : Matrix (Fin n) (Fin n) K,
      X * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * X →
        X ∈ Set.range Φ := by
    intro X hX
    rw [hΦrange X]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.units_zpow_right hX k).eq
  let B : LinBlock K g :=
    { r := r
      D := D
      d := d
      fld := hFld
      fin := hFin
      alg := hAlg
      Φ := Φ
      θ := θ
      pos := fun i => Nat.succ_le_of_lt (Nat.pos_of_ne_zero (hNZ i).out)
      Φinj := hΦinj
      θinj := hθinj
      θrange := hθrange.trans (i167CLin_block_exists_aux1 g)
      θapply := hθapply
      Φrange := hΦrange' }
  exact ⟨B⟩

private theorem i167CLin_block_exists_aux3 {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) :
    Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ StatedSL n K =
      ((StatedSL n K).comap B.θ).map B.θ := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxr : x ∈ B.θ.range := by
      rw [B.θrange]
      exact hx1
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hxr
    exact Subgroup.mem_map.mpr ⟨w, hx2, rfl⟩
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨?_, hw⟩
    rw [← B.θrange]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩

private theorem i167CLin_block_exists_aux4 {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (M : Subgroup (GL (Fin n) K))
    (hM : IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ StatedSL n K)) :
    ∃ i : Fin B.r, IsComponentOf (M.comap B.θ) ⊤ ∧
      M.comap B.θ ≤ (StatedSL (B.d i) (B.D i)).map
        (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i) := by
  have hMle : M ≤ B.θ.range := by
    intro x hx
    have hx1 := (hM.1 hx).1
    rw [B.θrange]
    exact hx1
  have hMmap : (M.comap B.θ).map B.θ = M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hMle
  have hM'comp : IsComponentOf (M.comap B.θ) ((StatedSL n K).comap B.θ) := by
    refine CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_of_map_injective B.θ B.θinj ?_
    rw [hMmap, ← i167CLin_block_exists_aux3 B]
    exact hM
  have hM'top : IsComponentOf (M.comap B.θ) ⊤ := CFSG.LieType.SemisimpleCentralizers.Held.isComponentOf_top_of_normal' hM'comp
  obtain ⟨i, hi⟩ := CFSG.LieType.SemisimpleCentralizers.Held.exists_factor_of_isComponentOf_top (H := fun k => GL (Fin (B.d k)) (B.D k)) hM'top
  have hcommS : ∀ a b : GL (Fin (B.d i)) (B.D i), ⁅a, b⁆ ∈ StatedSL (B.d i) (B.D i) :=
    fun a b => CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL a b
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  refine ⟨i, hM'top, ?_⟩
  have h1 := CFSG.LieType.SemisimpleCentralizers.Held.commutator_eq_self_of_isComponentOf_top hM'top
  have h2 := Subgroup.commutator_mono hi hi
  rw [h1] at h2
  exact h2.trans (CFSG.LieType.SemisimpleCentralizers.Held.commutator_factorSub_le (H := fun k => GL (Fin (B.d k)) (B.D k))
    (StatedSL (B.d i) (B.D i)) hcommS)

private theorem i167CLin_block_exists_aux5 {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (M : Subgroup (GL (Fin n) K)) (i : Fin B.r)
    (hM'top : IsComponentOf (M.comap B.θ) ⊤)
    (hM'T : M.comap B.θ ≤ (StatedSL (B.d i) (B.D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i)) :
    M.comap B.θ = (StatedSL (B.d i) (B.D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i) := by
  have hSL' : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ :=
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds
  have hms : Function.Injective (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have hX : IsComponentOf ((M.comap B.θ).subgroupOf _) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hM'top hM'T
  let e : ↥((StatedSL (B.d i) (B.D i)).map
      (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i)) ≃*
      ↥(StatedSL (B.d i) (B.D i)) :=
    (Subgroup.equivMapOfInjective (StatedSL (B.d i) (B.D i))
      (MonoidHom.mulSingle (fun k => GL (Fin (B.d k)) (B.D k)) i) hms).symm
  have hXe := (CFSG.ComponentClassification.LocalComponents.equiv_iff e _).2 hX
  have htop := hSL' (B.d i) (B.D i) _ hXe
  have hXtop : (M.comap B.θ).subgroupOf _ = ⊤ := CFSG.LieType.SemisimpleCentralizers.Held.eq_top_of_map_equiv_eq_top e _ htop
  exact le_antisymm hM'T (Subgroup.subgroupOf_eq_top.mp hXtop)

private theorem i167CLin_block_exists_aux6 {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (M : Subgroup (GL (Fin n) K))
    (hM : IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ StatedSL n K)) :
    ∃ i : Fin B.r, 2 ≤ B.d i ∧
      M = ((StatedSL (B.d i) (B.D i)).map
        (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i)).map B.θ := by
  obtain ⟨i, hM'top, hM'T⟩ := i167CLin_block_exists_aux4 B M hM
  have hTeq := i167CLin_block_exists_aux5 B M i hM'top hM'T
  have hMle : M ≤ B.θ.range := by
    intro x hx
    have hx1 := (hM.1 hx).1
    rw [B.θrange]
    exact hx1
  have hMmap : (M.comap B.θ).map B.θ = M := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hMle
  have hMeq : M = ((StatedSL (B.d i) (B.D i)).map
      (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i)).map B.θ := by
    rw [← hTeq, hMmap]
  have hd2 : 2 ≤ B.d i := by
    by_contra hlt
    have hlt' : B.d i < 2 := not_le.mp hlt
    have hall : ∀ a ∈ M, a = 1 := by
      intro a ha
      rw [hMeq] at ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy1 := CFSG.LieType.SemisimpleCentralizers.Held.eq_one_of_mem_statedSL_of_le_one (by omega) hy
      rw [hy1, map_one, map_one]
    exact CFSG.LieType.SemisimpleCentralizers.Held.not_isQuasisimple_of_comm
      (fun a b => Subtype.ext (by simp [hall a a.2, hall b b.2])) hM.2.2
  exact ⟨i, hd2, hMeq⟩

theorem i167CLin_block_exists {K : Type} [Field K] [Finite K] {n : ℕ} (g : GL (Fin n) K)
    (hord : ((orderOf g : ℕ) : K) ≠ 0) (M : Subgroup (GL (Fin n) K))
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ StatedSL n K)) :
    ∃ (B : LinBlock K g) (i : Fin B.r), 2 ≤ B.d i ∧
      M = ((StatedSL (B.d i) (B.D i)).map
        (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i)).map B.θ := by
  obtain ⟨B⟩ := i167CLin_block_exists_aux2 g hord
  obtain ⟨i, hd2, hMeq⟩ := i167CLin_block_exists_aux6 B M hM
  exact ⟨B, i, hd2, hMeq⟩

private lemma i167CLin_block_coord_aux1 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (w : ∀ i, GL (Fin (B.d i)) (B.D i)) (hw : B.θ w = g) :
    ∀ i, w i ∈ Subgroup.center (GL (Fin (B.d i)) (B.D i)) := by
  intro i
  rw [Subgroup.mem_center_iff]
  intro y
  have hzmem : B.θ (Pi.mulSingle i y) ∈ Subgroup.centralizer ({g} : Set (GL (Fin n) K)) := by
    rw [← B.θrange]
    exact ⟨Pi.mulSingle i y, rfl⟩
  have hcomm : g * B.θ (Pi.mulSingle i y) = B.θ (Pi.mulSingle i y) * g :=
    (Subgroup.mem_centralizer_iff.mp hzmem) g (Set.mem_singleton g)
  have heq : w * Pi.mulSingle i y = Pi.mulSingle i y * w := by
    apply B.θinj
    rw [map_mul, map_mul, hw]
    exact hcomm
  have hxy := congrFun heq i
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same] at hxy
  exact hxy.symm

private lemma i167CLin_block_coord_aux2 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {p : ℕ} (w : ∀ i, GL (Fin (B.d i)) (B.D i)) (hw : B.θ w = g) (hg : g ^ p = 1)
    (c : ∀ i, B.D i)
    (hc : ∀ i, Matrix.scalar (Fin (B.d i)) (c i) =
      ((w i : GL (Fin (B.d i)) (B.D i)) : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) :
    (∀ i, c i ≠ 0) ∧
      (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)) ∧
        ∀ i, c i ^ p = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    haveI : Nonempty (Fin (B.d i)) := ⟨0, B.pos i⟩
    have hunit : IsUnit (((w i : GL (Fin (B.d i)) (B.D i)) :
        Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) := ⟨w i, rfl⟩
    exact hunit.ne_zero (by rw [← hc i, h, map_zero])
  · calc (g : Matrix (Fin n) (Fin n) K)
        = B.Φ (fun i => ((w i : GL (Fin (B.d i)) (B.D i)) :
            Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) :=
            (congrArg (fun t : GL (Fin n) K => (t : Matrix (Fin n) (Fin n) K)) hw).symm.trans
              (B.θapply w)
      _ = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)) := by
            congr 1
            funext i
            exact (hc i).symm
  · intro i
    have hwp : w ^ p = 1 := by
      apply B.θinj
      rw [map_pow, hw, hg, map_one]
    have hwi : (w i) ^ p = 1 := by
      have := congrFun hwp i
      simpa [Pi.pow_apply] using this
    haveI : Nonempty (Fin (B.d i)) := ⟨0, B.pos i⟩
    apply (Matrix.scalar_inj (n := Fin (B.d i))).mp
    rw [map_pow, hc i, ← Units.val_pow_eq_pow_val, hwi, Units.val_one, map_one]

theorem i167CLin_block_coord {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K} (B : LinBlock K g) {p : ℕ}
    (hg : g ^ p = 1) :
    ∃ c : ∀ i, B.D i, (∀ i, c i ≠ 0) ∧
      (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)) ∧ ∀ i, c i ^ p = 1 := by
  classical
  have hmem : g ∈ Subgroup.centralizer ({g} : Set (GL (Fin n) K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rfl
  rw [← B.θrange] at hmem
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem
  choose c hc using fun i => Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    (i167CLin_block_coord_aux1 B w hw i)
  exact ⟨c, i167CLin_block_coord_aux2 B w hw hg c hc⟩

private def i167CLin_block_fixed_aux1 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) : Fin B.r → Matrix (Fin n) (Fin n) K :=
  fun j => B.Φ (Pi.single j 1)

private theorem i167CLin_block_fixed_aux2 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (j : Fin B.r) :
    i167CLin_block_fixed_aux1 B j * i167CLin_block_fixed_aux1 B j =
      i167CLin_block_fixed_aux1 B j := by
  rw [i167CLin_block_fixed_aux1, ← map_mul]
  congr 1
  funext l
  by_cases h : l = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

private theorem i167CLin_block_fixed_aux4 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) :
    ∑ j, i167CLin_block_fixed_aux1 B j = 1 := by
  have hsum1 : (∑ j : Fin B.r,
      (Pi.single j 1 : ∀ l, Matrix (Fin (B.d l)) (Fin (B.d l)) (B.D l))) = 1 := by
    funext l
    simp [Pi.single_apply]
  change ∑ j, B.Φ (Pi.single j 1) = 1
  have : B.Φ (∑ j : Fin B.r,
      (Pi.single j 1 : ∀ l, Matrix (Fin (B.d l)) (Fin (B.d l)) (B.D l))) =
      ∑ j, B.Φ (Pi.single j 1) := map_sum B.Φ _ _
  rw [← this, hsum1, map_one]

private theorem i167CLin_block_fixed_aux5 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    (j : Fin B.r) :
    (g : Matrix (Fin n) (Fin n) K) * i167CLin_block_fixed_aux1 B j =
      B.Φ (Pi.single j (Matrix.scalar (Fin (B.d j)) (c j))) := by
  rw [hc, i167CLin_block_fixed_aux1, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux6 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    (j : Fin B.r) :
    ((g : Matrix (Fin n) (Fin n) K) - 1) * i167CLin_block_fixed_aux1 B j =
      B.Φ (Pi.single j (Matrix.scalar (Fin (B.d j)) (c j) - 1)) := by
  rw [hc, show (1 : Matrix (Fin n) (Fin n) K) = B.Φ 1 from (map_one B.Φ).symm,
    ← map_sub, i167CLin_block_fixed_aux1, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux7 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    (j : Fin B.r) :
    i167CLin_block_fixed_aux1 B j * ((g : Matrix (Fin n) (Fin n) K) - 1) =
      B.Φ (Pi.single j (Matrix.scalar (Fin (B.d j)) (c j) - 1)) := by
  rw [hc, show (1 : Matrix (Fin n) (Fin n) K) = B.Φ 1 from (map_one B.Φ).symm,
    ← map_sub, i167CLin_block_fixed_aux1, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux8 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hj : ∀ j, c j = 1 → j = i) {j : Fin B.r} (hji : j ≠ i) :
    B.Φ (Pi.single j (Matrix.scalar (Fin (B.d j)) ((c j - 1)⁻¹))) *
      (((g : Matrix (Fin n) (Fin n) K) - 1) * i167CLin_block_fixed_aux1 B j) =
      i167CLin_block_fixed_aux1 B j := by
  have hne : c j - 1 ≠ 0 := sub_ne_zero.mpr fun h => hji (hj j h)
  rw [i167CLin_block_fixed_aux6 B hc j, i167CLin_block_fixed_aux1, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = j
  · rw [hl]
    simp only [Pi.mul_apply, Pi.single_eq_same]
    have hsc : Matrix.scalar (Fin (B.d j)) (c j) - 1 =
        Matrix.scalar (Fin (B.d j)) (c j - 1) := by rw [map_sub, map_one]
    rw [hsc, ← map_mul, inv_mul_cancel₀ hne, map_one]
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux9 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (hj : ∀ j, c j = 1 → j = i) :
    LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin n) (Fin n) K) - 1)) =
      LinearMap.range (Matrix.toLin' (i167CLin_block_fixed_aux1 B i)) := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
    rw [LinearMap.mem_range]
    refine ⟨v, ?_⟩
    rw [Matrix.toLin'_apply]
    have hzero : ∀ j, j ≠ i → i167CLin_block_fixed_aux1 B j *ᵥ v = 0 := by
      intro j hji
      set U := B.Φ (Pi.single j (Matrix.scalar (Fin (B.d j)) ((c j - 1)⁻¹))) with hU
      set E := i167CLin_block_fixed_aux1 B j with hEdef
      set G := ((g : Matrix (Fin n) (Fin n) K) - 1) with hG
      have hE : E = U * (G * E) := (i167CLin_block_fixed_aux8 B hc hj hji).symm
      have hcomm : G * E = E * G := by
        rw [i167CLin_block_fixed_aux6 B hc j, i167CLin_block_fixed_aux7 B hc j]
      have hGE : G *ᵥ (E *ᵥ v) = E *ᵥ (G *ᵥ v) := by
        have h : Matrix.toLin' (G * E) = Matrix.toLin' (E * G) := by rw [hcomm]
        have h2 := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f v) h
        simpa only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply] using h2
      have hcomp : Matrix.toLin' E = Matrix.toLin' U ∘ₗ (Matrix.toLin' G ∘ₗ Matrix.toLin' E) := by
        conv_lhs => rw [hE]
        rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
      have hEv : E *ᵥ v = U *ᵥ (G *ᵥ (E *ᵥ v)) := by
        have := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f v) hcomp
        simpa only [LinearMap.comp_apply, Matrix.toLin'_apply] using this
      have hGv : G *ᵥ (E *ᵥ v) = 0 := by rw [hGE, hv]; simp
      calc E *ᵥ v = U *ᵥ (G *ᵥ (E *ᵥ v)) := hEv
        _ = 0 := by rw [hGv]; simp
    have hvsum : v = ∑ j, i167CLin_block_fixed_aux1 B j *ᵥ v := by
      rw [← Matrix.sum_mulVec, i167CLin_block_fixed_aux4, Matrix.one_mulVec]
    exact (hvsum.trans (Fintype.sum_eq_single i hzero)).symm
  · rintro v ⟨u, rfl⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      i167CLin_block_fixed_aux6 B hc i, hi]
    simp

private def i167CLin_block_fixed_aux10 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  Matrix.toLin' (i167CLin_block_fixed_aux1 B i)

private def i167CLin_block_fixed_aux11 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) : Submodule K (Fin n → K) :=
  LinearMap.range (i167CLin_block_fixed_aux10 B i)

private theorem i167CLin_block_fixed_aux12 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) {Y : Matrix (Fin n) (Fin n) K}
    (hY : Y = i167CLin_block_fixed_aux1 B i * Y * i167CLin_block_fixed_aux1 B i) :
    ∀ v ∈ i167CLin_block_fixed_aux11 B i, Matrix.toLin' Y v ∈ i167CLin_block_fixed_aux11 B i := by
  intro v _
  have h : Matrix.toLin' Y = (i167CLin_block_fixed_aux10 B i) ∘ₗ
      ((Matrix.toLin' Y) ∘ₗ (i167CLin_block_fixed_aux10 B i)) := by
    rw [i167CLin_block_fixed_aux10]
    conv_lhs => rw [hY]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_assoc]
  rw [h]
  exact ⟨(Matrix.toLin' Y) ((i167CLin_block_fixed_aux10 B i) v), rfl⟩

private noncomputable def i167CLin_block_fixed_aux13 {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (i : Fin B.r) (Y : Matrix (Fin n) (Fin n) K)
    (hY : Y = i167CLin_block_fixed_aux1 B i * Y * i167CLin_block_fixed_aux1 B i) :
    (i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i) :=
  (Matrix.toLin' Y).restrict (i167CLin_block_fixed_aux12 B i hY)

private theorem i167CLin_block_fixed_aux14 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r)
    (x : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) :
    B.Φ (Pi.single i x) =
      i167CLin_block_fixed_aux1 B i * B.Φ (Pi.single i x) *
        i167CLin_block_fixed_aux1 B i := by
  change B.Φ (Pi.single i x) =
    B.Φ (Pi.single i 1) * B.Φ (Pi.single i x) * B.Φ (Pi.single i 1)
  rw [← map_mul, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = i
  · subst hl; simp
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux15a {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) (y : B.D i) {w : Matrix (Fin n) (Fin n) K}
    (hw : w ∈ Set.range B.Φ) :
    B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)) * w =
      w * B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)) := by
  obtain ⟨w', rfl⟩ := hw
  rw [← map_mul, ← map_mul]
  congr 1
  funext l
  by_cases hl : l = i
  · rw [hl]
    simp only [Pi.mul_apply, Pi.single_eq_same]
    exact Matrix.scalar_comm y (fun r' => Commute.all y r') (w' i)
  · simp [Pi.single_eq_of_ne hl]

private theorem i167CLin_block_fixed_aux16 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) :
    (g : Matrix (Fin n) (Fin n) K) * i167CLin_block_fixed_aux1 B i = i167CLin_block_fixed_aux1 B i ∧
    i167CLin_block_fixed_aux1 B i * (g : Matrix (Fin n) (Fin n) K) = i167CLin_block_fixed_aux1 B i := by
  constructor
  · rw [i167CLin_block_fixed_aux5 B hc i, hi]
    simp [i167CLin_block_fixed_aux1]
  · rw [i167CLin_block_fixed_aux1]
    have h : B.Φ (Pi.single i 1) * (g : Matrix (Fin n) (Fin n) K) =
        B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) (c i))) := by
      rw [hc, ← map_mul]
      congr 1
      funext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [h, hi]
    simp [i167CLin_block_fixed_aux1]

private theorem i167CLin_block_fixed_aux_e_idem {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) :
    i167CLin_block_fixed_aux10 B i ∘ₗ i167CLin_block_fixed_aux10 B i =
      i167CLin_block_fixed_aux10 B i := by
  change Matrix.toLin' (i167CLin_block_fixed_aux1 B i) ∘ₗ
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i) =
    Matrix.toLin' (i167CLin_block_fixed_aux1 B i)
  rw [← Matrix.toLin'_mul, i167CLin_block_fixed_aux2]

private theorem i167CLin_block_fixed_aux_e_id {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) :
    ∀ x : (Fin n → K), x ∈ i167CLin_block_fixed_aux11 B i →
      i167CLin_block_fixed_aux10 B i x = x := by
  rintro x ⟨u, rfl⟩
  exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f u)
    (i167CLin_block_fixed_aux_e_idem B i)

private theorem i167CLin_block_fixed_aux15buildg {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {e : (Fin n → K) →ₗ[K] (Fin n → K)}
    {htilde : (Fin n → K) →ₗ[K] (Fin n → K)} {w : Matrix (Fin n) (Fin n) K}
    (hw : Matrix.toLin' w = htilde)
    (htilde_corner : htilde = e ∘ₗ (htilde ∘ₗ e))
    (he_g : e ∘ₗ Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) = e)
    (hg_e : Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) ∘ₗ e = e) :
    w ∈ Set.range B.Φ := by
  have htilde_comm_g : htilde ∘ₗ Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) ∘ₗ htilde := by
    have h1 : htilde ∘ₗ Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) = htilde := by
      conv_lhs => rw [htilde_corner]
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, he_g]
      exact htilde_corner.symm
    have h2 : Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) ∘ₗ htilde = htilde := by
      conv_lhs => rw [htilde_corner]
      rw [← LinearMap.comp_assoc, hg_e]
      exact htilde_corner.symm
    rw [h1, h2]
  apply B.Φrange w
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hw, htilde_comm_g]

private theorem i167CLin_block_fixed_aux15buildcorner {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (i : Fin B.r)
    {h : (i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)}
    {eW : (Fin n → K) →ₗ[K] (i167CLin_block_fixed_aux11 B i)}
    {htilde : (Fin n → K) →ₗ[K] (Fin n → K)}
    (heW_def : ∀ v : (Fin n → K), eW v = ⟨i167CLin_block_fixed_aux10 B i v, ⟨v, rfl⟩⟩)
    (htilde_def : ∀ v : (Fin n → K), htilde v = (h (eW v) : (Fin n → K))) :
    htilde = i167CLin_block_fixed_aux10 B i ∘ₗ
      (htilde ∘ₗ i167CLin_block_fixed_aux10 B i) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, htilde_def v,
    htilde_def (i167CLin_block_fixed_aux10 B i v)]
  have h2 : eW (i167CLin_block_fixed_aux10 B i v) = eW v := by
    rw [heW_def (i167CLin_block_fixed_aux10 B i v), heW_def v]
    congr 1
    exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f v)
      (i167CLin_block_fixed_aux_e_idem B i)
  rw [h2]
  exact (i167CLin_block_fixed_aux_e_id B i (h (eW v)) (h (eW v)).2).symm

private theorem i167CLin_block_fixed_aux15buildA {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1)
    (h : (i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :
    ∃ (htilde : (Fin n → K) →ₗ[K] (Fin n → K)) (w : Matrix (Fin n) (Fin n) K),
      Matrix.toLin' w = htilde ∧ w ∈ Set.range B.Φ ∧
      (∀ x : i167CLin_block_fixed_aux11 B i,
        htilde (x : (Fin n → K)) = (h x : (Fin n → K))) ∧
      htilde = i167CLin_block_fixed_aux10 B i ∘ₗ
        (htilde ∘ₗ i167CLin_block_fixed_aux10 B i) := by
  let e : (Fin n → K) →ₗ[K] (Fin n → K) := i167CLin_block_fixed_aux10 B i
  let W : Submodule K (Fin n → K) := LinearMap.range e
  let eW : (Fin n → K) →ₗ[K] W :=
    e.codRestrict W (fun v => by change e v ∈ LinearMap.range e; exact ⟨v, rfl⟩)
  let htilde : (Fin n → K) →ₗ[K] (Fin n → K) := W.subtype.comp (h.comp eW)
  have heW_apply : ∀ x : W, eW (x : (Fin n → K)) = x := by
    intro x
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply]
    exact i167CLin_block_fixed_aux_e_id B i x x.2
  have htilde_apply : ∀ x : W, htilde (x : (Fin n → K)) = (h x : (Fin n → K)) := by
    intro x
    change (h (eW (x : (Fin n → K))) : (Fin n → K)) = (h x : (Fin n → K))
    rw [heW_apply x]
  let w : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' htilde
  have hw : Matrix.toLin' w = htilde := by
    change Matrix.toLin' (LinearMap.toMatrix' htilde) = htilde
    rw [Matrix.toLin'_toMatrix']
  have he_g : e ∘ₗ Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) = e := by
    change Matrix.toLin' (i167CLin_block_fixed_aux1 B i) ∘ₗ
        Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i)
    rw [← Matrix.toLin'_mul, (i167CLin_block_fixed_aux16 B hc hi).2]
  have hg_e : Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) ∘ₗ e = e := by
    change Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) ∘ₗ
        Matrix.toLin' (i167CLin_block_fixed_aux1 B i) =
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i)
    rw [← Matrix.toLin'_mul, (i167CLin_block_fixed_aux16 B hc hi).1]
  have htilde_corner : htilde = e ∘ₗ (htilde ∘ₗ e) :=
    i167CLin_block_fixed_aux15buildcorner B i (fun v => rfl) (fun v => rfl)
  have hw_mem : w ∈ Set.range B.Φ :=
    i167CLin_block_fixed_aux15buildg B hw htilde_corner he_g hg_e
  exact ⟨htilde, w, hw, hw_mem, htilde_apply, htilde_corner⟩

private theorem i167CLin_block_fixed_aux15 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (y : B.D i) :
    i167CLin_block_fixed_aux13 B i (B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)))
      (i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y)) ∈
      Set.center ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) := by
  let e : (Fin n → K) →ₗ[K] (Fin n → K) := i167CLin_block_fixed_aux10 B i
  let W : Submodule K (Fin n → K) := LinearMap.range e
  let Y : Matrix (Fin n) (Fin n) K := B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y))
  let Y' : W →ₗ[K] W := (Matrix.toLin' Y).restrict
    (i167CLin_block_fixed_aux12 B i (i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y)))
  change Y' ∈ Set.center (W →ₗ[K] W)
  rw [Semigroup.mem_center_iff]
  intro h
  obtain ⟨htilde, w, hw, hw_mem, htilde_apply, htilde_corner⟩ :=
    i167CLin_block_fixed_aux15buildA B hc hi h
  have hYw : Y * w = w * Y := i167CLin_block_fixed_aux15a B i y hw_mem
  have hYh : Matrix.toLin' Y ∘ₗ htilde = htilde ∘ₗ Matrix.toLin' Y := by
    rw [← hw, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hYw]
  have hY'_apply : ∀ x : W, (Y' x : (Fin n → K)) = Matrix.toLin' Y (x : (Fin n → K)) := by
    intro x
    rfl
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  apply Subtype.ext
  calc (h (Y' x) : (Fin n → K)) = htilde (Y' x : (Fin n → K)) := (htilde_apply (Y' x)).symm
    _ = htilde (Matrix.toLin' Y (x : (Fin n → K))) := by rw [hY'_apply x]
    _ = Matrix.toLin' Y (htilde (x : (Fin n → K))) := by
          rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hYh]
    _ = Matrix.toLin' Y (h x : (Fin n → K)) := congrArg (Matrix.toLin' Y) (htilde_apply x)
    _ = (Y' (h x) : (Fin n → K)) := (hY'_apply (h x)).symm

private theorem i167CLin_block_fixed_aux18mem {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r)
    (x : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) (v : (Fin n → K)) :
    Matrix.toLin' (B.Φ (Pi.single i x)) v ∈ i167CLin_block_fixed_aux11 B i := by
  have h2 : Matrix.toLin' (B.Φ (Pi.single i x)) = i167CLin_block_fixed_aux10 B i ∘ₗ
      (Matrix.toLin' (B.Φ (Pi.single i x)) ∘ₗ i167CLin_block_fixed_aux10 B i) := by
    change Matrix.toLin' (B.Φ (Pi.single i x)) =
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i) ∘ₗ
      (Matrix.toLin' (B.Φ (Pi.single i x)) ∘ₗ Matrix.toLin' (i167CLin_block_fixed_aux1 B i))
    conv_lhs => rw [i167CLin_block_fixed_aux14 B i x]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_assoc]
  rw [h2]
  exact ⟨(Matrix.toLin' (B.Φ (Pi.single i x))) ((i167CLin_block_fixed_aux10 B i) v), rfl⟩

private noncomputable def i167CLin_block_fixed_aux18fun {K : Type} [Field K] [Finite K] {n : ℕ}
    {g : GL (Fin n) K} (B : LinBlock K g) (i : Fin B.r) :
    Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i) →
      ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
  fun x => (Matrix.toLin' (B.Φ (Pi.single i x))).restrict
    (fun v _ => i167CLin_block_fixed_aux18mem B i x v)

private theorem i167CLin_block_fixed_aux18inj {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) :
    Function.Injective (i167CLin_block_fixed_aux18fun B i) := by
  intro x y hxy
  have he_idem : (i167CLin_block_fixed_aux10 B i) ∘ₗ (i167CLin_block_fixed_aux10 B i) =
      i167CLin_block_fixed_aux10 B i := by
    change Matrix.toLin' (i167CLin_block_fixed_aux1 B i) ∘ₗ
        Matrix.toLin' (i167CLin_block_fixed_aux1 B i) =
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i)
    rw [← Matrix.toLin'_mul, i167CLin_block_fixed_aux2]
  have he_id' : ∀ y : (Fin n → K), y ∈ i167CLin_block_fixed_aux11 B i →
      (i167CLin_block_fixed_aux10 B i) y = y := by
    rintro y ⟨u, rfl⟩
    exact congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f u) he_idem
  have hcorner : ∀ x, Matrix.toLin' (B.Φ (Pi.single i x)) =
      (i167CLin_block_fixed_aux10 B i) ∘ₗ
      (Matrix.toLin' (B.Φ (Pi.single i x)) ∘ₗ i167CLin_block_fixed_aux10 B i) := by
    intro x
    change Matrix.toLin' (B.Φ (Pi.single i x)) =
      Matrix.toLin' (i167CLin_block_fixed_aux1 B i) ∘ₗ
      (Matrix.toLin' (B.Φ (Pi.single i x)) ∘ₗ Matrix.toLin' (i167CLin_block_fixed_aux1 B i))
    conv_lhs => rw [i167CLin_block_fixed_aux14 B i x]
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_assoc]
  have h1 : Matrix.toLin' (B.Φ (Pi.single i x)) = Matrix.toLin' (B.Φ (Pi.single i y)) := by
    apply LinearMap.ext
    intro v
    have hmem : Matrix.toLin' (B.Φ (Pi.single i x)) ((i167CLin_block_fixed_aux10 B i) v) ∈
        i167CLin_block_fixed_aux11 B i :=
      i167CLin_block_fixed_aux18mem B i x ((i167CLin_block_fixed_aux10 B i) v)
    have hx : Matrix.toLin' (B.Φ (Pi.single i x)) ((i167CLin_block_fixed_aux10 B i) v) =
        Matrix.toLin' (B.Φ (Pi.single i y)) ((i167CLin_block_fixed_aux10 B i) v) :=
      congrArg (fun f : (i167CLin_block_fixed_aux11 B i) →ₗ[K]
          (i167CLin_block_fixed_aux11 B i) =>
          (f ⟨(i167CLin_block_fixed_aux10 B i) v, ⟨v, rfl⟩⟩ : (Fin n → K))) hxy
    have hxv : Matrix.toLin' (B.Φ (Pi.single i x)) v =
        Matrix.toLin' (B.Φ (Pi.single i x)) ((i167CLin_block_fixed_aux10 B i) v) := by
      conv_lhs => rw [hcorner x, LinearMap.comp_apply, LinearMap.comp_apply]
      exact he_id' _ hmem
    have hyv : Matrix.toLin' (B.Φ (Pi.single i y)) v =
        Matrix.toLin' (B.Φ (Pi.single i y)) ((i167CLin_block_fixed_aux10 B i) v) := by
      conv_lhs => rw [hcorner y, LinearMap.comp_apply, LinearMap.comp_apply]
      exact he_id' _ (i167CLin_block_fixed_aux18mem B i y ((i167CLin_block_fixed_aux10 B i) v))
    rw [hxv, hyv, hx]
  have h2 : B.Φ (Pi.single i x) = B.Φ (Pi.single i y) := Matrix.toLin'.injective h1
  have h3 : Pi.single i x = Pi.single i y := B.Φinj h2
  have := congrFun h3 i
  simpa [Pi.single_eq_same] using this

private theorem i167CLin_block_fixed_aux15buildB {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {i : Fin B.r} {htilde : (Fin n → K) →ₗ[K] (Fin n → K)}
    {w : Matrix (Fin n) (Fin n) K}
    (hw : Matrix.toLin' w = htilde) (hw_mem : w ∈ Set.range B.Φ)
    (htilde_corner : htilde = i167CLin_block_fixed_aux10 B i ∘ₗ
      (htilde ∘ₗ i167CLin_block_fixed_aux10 B i)) :
    ∃ x : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i),
      Matrix.toLin' (B.Φ (Pi.single i x)) = htilde := by
  obtain ⟨w', hw'⟩ := hw_mem
  have hw_corner : w = i167CLin_block_fixed_aux1 B i * w * i167CLin_block_fixed_aux1 B i := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hw]
    exact htilde_corner
  have hw_eq : w = B.Φ (Pi.single i (w' i)) := by
    rw [hw_corner, ← hw']
    change B.Φ (Pi.single i 1) * B.Φ w' * B.Φ (Pi.single i 1) = B.Φ (Pi.single i (w' i))
    rw [← map_mul, ← map_mul]
    congr 1
    funext l
    by_cases hl : l = i
    · rw [hl]; simp [Pi.single_eq_same]
    · simp [Pi.single_eq_of_ne hl]
  have hw'_eq : w' = Pi.single i (w' i) := by
    apply B.Φinj
    rw [hw', hw_eq]
  exact ⟨w' i, by rw [← hw_eq, hw]⟩

private theorem i167CLin_block_fixed_aux18surj {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) :
    Function.Surjective (i167CLin_block_fixed_aux18fun B i) := by
  intro h
  obtain ⟨htilde, w, hw, hw_mem, htilde_apply, htilde_corner⟩ :=
    i167CLin_block_fixed_aux15buildA B hc hi h
  obtain ⟨x, hx⟩ := i167CLin_block_fixed_aux15buildB B hw hw_mem htilde_corner
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  change Matrix.toLin' (B.Φ (Pi.single i x)) (y : (Fin n → K)) = (h y : (Fin n → K))
  rw [hx, htilde_apply y]

private theorem i167CLin_block_fixed_aux17a {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (y : B.D i) {α : K}
    (hα' : i167CLin_block_fixed_aux13 B i (B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)))
      (i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y)) = α • LinearMap.id) :
    B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)) = α • i167CLin_block_fixed_aux1 B i := by
  let e : (Fin n → K) →ₗ[K] (Fin n → K) := i167CLin_block_fixed_aux10 B i
  let W : Submodule K (Fin n → K) := LinearMap.range e
  let Y : Matrix (Fin n) (Fin n) K := B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y))
  let Y' : W →ₗ[K] W := i167CLin_block_fixed_aux13 B i Y
    (i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y))
  have hY'apply : ∀ w : W, Matrix.toLin' Y (w : (Fin n → K)) = α • (w : (Fin n → K)) := by
    intro w
    have h := congrArg (fun f : W →ₗ[K] W => (f w : (Fin n → K))) hα'
    rw [show (Y' w : (Fin n → K)) = Matrix.toLin' Y (w : (Fin n → K)) from rfl] at h
    change Matrix.toLin' Y (w : (Fin n → K)) = α • (w : (Fin n → K)) at h
    exact h
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  have hYeq : Y = i167CLin_block_fixed_aux1 B i * Y * i167CLin_block_fixed_aux1 B i :=
    i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y)
  have hYmul : Y * i167CLin_block_fixed_aux1 B i = Y := by
    conv_lhs => rw [hYeq]
    rw [mul_assoc, i167CLin_block_fixed_aux2]
    exact hYeq.symm
  have hYcompose : Matrix.toLin' Y = Matrix.toLin' Y ∘ₗ e := by
    change Matrix.toLin' Y = Matrix.toLin' Y ∘ₗ Matrix.toLin' (i167CLin_block_fixed_aux1 B i)
    rw [← Matrix.toLin'_mul, hYmul]
  calc Matrix.toLin' Y v = Matrix.toLin' Y (e v) := by
        conv_lhs => rw [hYcompose]
        rw [LinearMap.comp_apply]
    _ = α • e v := hY'apply ⟨e v, ⟨v, rfl⟩⟩
    _ = (Matrix.toLin' (α • i167CLin_block_fixed_aux1 B i)) v := by
        rw [map_smul]
        rfl

private theorem i167CLin_block_fixed_aux17 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) :
    Function.Surjective (algebraMap K (B.D i)) := by
  intro y
  let e : (Fin n → K) →ₗ[K] (Fin n → K) := i167CLin_block_fixed_aux10 B i
  let W : Submodule K (Fin n → K) := LinearMap.range e
  let Y : Matrix (Fin n) (Fin n) K := B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y))
  let Y' : W →ₗ[K] W := i167CLin_block_fixed_aux13 B i Y
    (i167CLin_block_fixed_aux14 B i (Matrix.scalar (Fin (B.d i)) y))
  have hcenter : Y' ∈ Set.center (W →ₗ[K] W) := i167CLin_block_fixed_aux15 B hc hi y
  obtain ⟨α, _, hα⟩ := Module.End.mem_center_iff.mp hcenter
  have hα' : Y' = α • LinearMap.id := by rw [hα, Module.End.smulLeft_eq]
  have hY := i167CLin_block_fixed_aux17a B hc hi y hα'
  have hsingle_smul : (α • Pi.single i (1 : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) :
      ∀ j, Matrix (Fin (B.d j)) (Fin (B.d j)) (B.D j)) =
      Pi.single i (α • (1 : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) := by
    funext l
    by_cases hl : l = i
    · rw [hl]; simp [Pi.single_eq_same, Pi.smul_apply]
    · simp [Pi.single_eq_of_ne hl, Pi.smul_apply]
  have hsmul1 : (α • (1 : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) =
      Matrix.scalar (Fin (B.d i)) (algebraMap K (B.D i) α) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  have hΦeq : B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)) =
      B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) (algebraMap K (B.D i) α))) := by
    have h1 : B.Φ (Pi.single i (Matrix.scalar (Fin (B.d i)) y)) =
        α • B.Φ (Pi.single i (1 : Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i))) := by
      rw [← i167CLin_block_fixed_aux1]
      exact hY
    rw [h1, ← map_smul, hsingle_smul, hsmul1]
  have hsingle : Pi.single i (Matrix.scalar (Fin (B.d i)) y) =
      Pi.single i (Matrix.scalar (Fin (B.d i)) (algebraMap K (B.D i) α)) := B.Φinj hΦeq
  have hscalar : Matrix.scalar (Fin (B.d i)) y =
      Matrix.scalar (Fin (B.d i)) (algebraMap K (B.D i) α) := by
    have := congrFun hsingle i
    simpa [Pi.single_eq_same] using this
  haveI : Nonempty (Fin (B.d i)) :=
    Fin.pos_iff_nonempty.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one (B.pos i))
  exact ⟨α, (Matrix.scalar_inj).mp hscalar.symm⟩

private theorem i167CLin_block_fixed_aux18fr {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) (i : Fin B.r) (hcard : Nat.card (B.D i) = Nat.card K) :
    Module.finrank K (B.D i) = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (B.D i) := Fintype.ofFinite (B.D i)
  have hK2 : 2 ≤ Nat.card K := by
    have h := Fintype.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card]
    exact h
  have h1 : Nat.card (B.D i) = Nat.card K ^ Module.finrank K (B.D i) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have h2 : Nat.card K ^ Module.finrank K (B.D i) = Nat.card K ^ 1 := by
    rw [pow_one, ← h1, hcard]
  exact Nat.pow_right_injective hK2 h2

private theorem i167CLin_block_fixed_aux18a {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {i : Fin B.r}
    (hcard : Nat.card (B.D i) = Nat.card K)
    (hcardMat : Nat.card (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) =
      Nat.card ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i))) :
    B.d i = Module.finrank K (i167CLin_block_fixed_aux11 B i) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (B.D i) := Fintype.ofFinite (B.D i)
  haveI : Fintype (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) := Fintype.ofFinite _
  haveI : Finite ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
    Finite.of_injective (fun f => (f : _ → _)) (fun _ _ h => LinearMap.ext (congrFun h))
  haveI : Fintype ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
    Fintype.ofFinite _
  have hK2 : 2 ≤ Nat.card K := by
    have h := Fintype.one_lt_card (α := K)
    rw [Nat.card_eq_fintype_card]
    exact h
  have hfr : Module.finrank K (B.D i) = 1 := i167CLin_block_fixed_aux18fr B i hcard
  have hfinMat : Module.finrank K (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) =
      B.d i * B.d i := by
    rw [Module.finrank_matrix, Fintype.card_fin, hfr, mul_one]
  have hfinEnd : Module.finrank K ((i167CLin_block_fixed_aux11 B i) →ₗ[K]
      (i167CLin_block_fixed_aux11 B i)) =
      Module.finrank K (i167CLin_block_fixed_aux11 B i) *
        Module.finrank K (i167CLin_block_fixed_aux11 B i) := by
    rw [Module.finrank_linearMap]
  have hcard2 : Nat.card K ^ (B.d i * B.d i) =
      Nat.card K ^ (Module.finrank K (i167CLin_block_fixed_aux11 B i) *
        Module.finrank K (i167CLin_block_fixed_aux11 B i)) := by
    have h1 : Nat.card (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) =
        Nat.card K ^ Module.finrank K (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    have h2 : Nat.card ((i167CLin_block_fixed_aux11 B i) →ₗ[K]
        (i167CLin_block_fixed_aux11 B i)) =
        Nat.card K ^ Module.finrank K ((i167CLin_block_fixed_aux11 B i) →ₗ[K]
          (i167CLin_block_fixed_aux11 B i)) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank (K := K)
        (V := (i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i))
    rw [← hfinMat, ← hfinEnd, ← h1, hcardMat, h2]
  have hsq : B.d i * B.d i = Module.finrank K (i167CLin_block_fixed_aux11 B i) *
      Module.finrank K (i167CLin_block_fixed_aux11 B i) :=
    Nat.pow_right_injective hK2 hcard2
  rw [← pow_two, ← pow_two] at hsq
  exact Nat.pow_left_injective (n := 2) (by norm_num) hsq

private theorem i167CLin_block_fixed_aux18 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (hj : ∀ j, c j = 1 → j = i) :
    B.d i = Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin n) (Fin n) K) - 1))) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (B.D i) := Fintype.ofFinite (B.D i)
  haveI : Fintype (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) := Fintype.ofFinite _
  haveI : Finite ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
    Finite.of_injective (fun f => (f : _ → _)) (fun _ _ h => LinearMap.ext (congrFun h))
  haveI : Fintype ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
    Fintype.ofFinite _
  have hsurj := i167CLin_block_fixed_aux17 B hc hi
  have hcard : Nat.card (B.D i) = Nat.card K :=
    (Nat.card_congr (Equiv.ofBijective (algebraMap K (B.D i))
      ⟨FaithfulSMul.algebraMap_injective K (B.D i), hsurj⟩)).symm
  have hker := i167CLin_block_fixed_aux9 B hc hi hj
  rw [hker]
  have hbij : Function.Bijective (i167CLin_block_fixed_aux18fun B i) :=
    ⟨i167CLin_block_fixed_aux18inj B i, i167CLin_block_fixed_aux18surj B hc hi⟩
  have hcardMat : Nat.card (Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) =
      Nat.card ((i167CLin_block_fixed_aux11 B i) →ₗ[K] (i167CLin_block_fixed_aux11 B i)) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  exact i167CLin_block_fixed_aux18a B hcard hcardMat

theorem i167CLin_block_fixed {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K} (B : LinBlock K g)
    {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (hj : ∀ j, c j = 1 → j = i) :
    Nat.card (B.D i) = Nat.card K ∧
      B.d i = Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin n) (Fin n) K) - 1))) := by
  have hsurj := i167CLin_block_fixed_aux17 B hc hi
  refine ⟨?_, i167CLin_block_fixed_aux18 B hc hi hj⟩
  exact (Nat.card_congr (Equiv.ofBijective (algebraMap K (B.D i))
    ⟨FaithfulSMul.algebraMap_injective K (B.D i), hsurj⟩)).symm

private lemma i167CLin_block_fixed_triv_aux1 {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) (x : GL (Fin (B.d i)) (B.D i)) :
    (((B.θ (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i x) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  have hsub : (((B.θ (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i x) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1)
      = B.Φ (Pi.single i (((x : GL (Fin (B.d i)) (B.D i)) :
          Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) - 1)) := by
    rw [B.θapply (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i x)]
    rw [← map_one B.Φ, ← map_sub]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Pi.mulSingle_eq_same]
    · simp [Pi.mulSingle, Function.update_of_ne hj, Pi.single_eq_of_ne hj, Pi.one_apply]
  have hsubg : (g : Matrix (Fin n) (Fin n) K) - 1
      = B.Φ (fun j => Matrix.scalar (Fin (B.d j)) (c j) - 1) := by
    rw [hc, ← map_one B.Φ, ← map_sub]
    congr 1
  rw [hsub, hsubg, ← map_mul]
  have hzero : (Pi.single i (((x : GL (Fin (B.d i)) (B.D i)) :
        Matrix (Fin (B.d i)) (Fin (B.d i)) (B.D i)) - 1))
      * (fun j => Matrix.scalar (Fin (B.d j)) (c j) - 1) = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Pi.mul_apply, Pi.single_eq_same, Pi.zero_apply, hi]
    · simp [Pi.mul_apply, Pi.single_eq_of_ne hj, Pi.zero_apply]
  rw [hzero, map_zero]

theorem i167CLin_block_fixed_triv {K : Type} [Field K] [Finite K] {n : ℕ} {g : GL (Fin n) K} (B : LinBlock K g)
    {c : ∀ i, B.D i}
    (hc : (g : Matrix (Fin n) (Fin n) K) = B.Φ (fun i => Matrix.scalar (Fin (B.d i)) (c i)))
    {i : Fin B.r} (hi : c i = 1) :
    ∀ m ∈ ((StatedSL (B.d i) (B.D i)).map (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i)).map B.θ,
      ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin n) (Fin n) K) - 1)),
        (m : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by
  classical
  intro m hm v hv
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
  rw [Matrix.toLin'_apply]
  have hv0 : (((B.θ (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i x) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1) *ᵥ (((g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ u) = 0 := by
    rw [Matrix.mulVec_mulVec, i167CLin_block_fixed_triv_aux1 B hc hi x, Matrix.zero_mulVec]
  have hsub2 := hv0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hsub2
  exact sub_eq_zero.mp hsub2

theorem i167CLin_block_model {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {n : ℕ} {g : GL (Fin n) K}
    (B : LinBlock K g) {i : Fin B.r} (hi2 : 2 ≤ B.d i) {M : Subgroup (GL (Fin n) K)}
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin n) K)) ⊓ StatedSL n K))
    (hMeq : M = ((StatedSL (B.d i) (B.D i)).map
      (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i)).map B.θ) :
    ∃ e : ℕ, Nat.card (B.D i) = 2 ^ e ∧ StatedClassicalModel (M ⧸ Subgroup.center M) .PSL (B.d i) 2 e := by
  classical
  haveI : Fintype (B.D i) := Fintype.ofFinite (B.D i)
  have h2D : (2 : B.D i) = 0 := by
    rw [← map_ofNat (algebraMap K (B.D i)) 2, h2, map_zero]
  obtain ⟨q, hqchar, m, hqprime, hcard⟩ := FiniteField.card' (B.D i)
  haveI := hqchar
  have hq2 : q = 2 :=
    (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff (B.D i) q 2).mp h2D)
  have hE : Nat.card (B.D i) = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard, hq2]
  have hms : Function.Injective (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i) := by
    intro a b hab
    have := congrFun hab i
    simpa [MonoidHom.mulSingle_apply] using this
  have eM : ↥M ≃* ↥(StatedSL (B.d i) (B.D i)) :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((Subgroup.equivMapOfInjective _ B.θ B.θinj).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (B.d i) (B.D i))
          (MonoidHom.mulSingle (fun j => GL (Fin (B.d j)) (B.D j)) i) hms).symm)
  obtain ⟨e'⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eM
  haveI : IsSimpleGroup (M ⧸ Subgroup.center M) := hM.2.2.2
  exact ⟨(m : ℕ), hE,
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup
      hi2 hE e'⟩

private theorem i167CLin_block_dichotomy_aux1 {K : Type} [Field K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G] (g : G) (hg : g ^ p = 1) :
    ((orderOf g : ℕ) : K) ≠ 0 := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hg) with h1 | hp'
  · simp [h1]
  · rw [hp']
    exact CharP.cast_ne_zero_of_ne_of_prime (R := K) (p := 2) hp hp2.symm

private theorem i167CLin_block_dichotomy_aux2 {E : Type} [Field E] {e p : ℕ}
    (hE : Nat.card E = 2 ^ e) (hp : p.Prime) {c : E} (hc0 : c ≠ 0) (hcp : c ^ p = 1)
    (hc1 : c ≠ 1) : p ∣ 2 ^ e - 1 := by
  let u : Eˣ := Units.mk0 c hc0
  have hup : u ^ p = 1 := by ext; simp [u, hcp]
  have hu1 : u ≠ 1 := by
    intro h
    exact hc1 (by simpa [u] using congrArg (fun v : Eˣ => (v : E)) h)
  haveI : Fact p.Prime := ⟨hp⟩
  have horder : orderOf u = p := orderOf_eq_prime hup hu1
  have h := orderOf_dvd_natCard u
  rw [horder, Nat.card_units, hE] at h
  exact h

theorem i167CLin_block_dichotomy {K : Type} [Field K] [Finite K] {a : ℕ} (hKa : Nat.card K = 2 ^ a) (h2 : (2 : K) = 0)
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g : GL (Fin d) K) (hg : g ^ p = 1) (M : Subgroup (GL (Fin d) K))
    (hM : CFSG.Open.IsComponentOf M (Subgroup.centralizer ({g} : Set (GL (Fin d) K)) ⊓ StatedSL d K)) :
    ∃ b e : ℕ, StatedClassicalModel (M ⧸ Subgroup.center M) .PSL b 2 e ∧
      (p ∣ 2 ^ e - 1 ∨
        (e = a ∧ b = Module.finrank K (LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1))) ∧
          ∀ m ∈ M, ∀ v ∈ LinearMap.range (Matrix.toLin' ((g : Matrix (Fin d) (Fin d) K) - 1)),
            (m : Matrix (Fin d) (Fin d) K) *ᵥ v = v)) := by
  classical
  haveI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  have hord : ((orderOf g : ℕ) : K) ≠ 0 := i167CLin_block_dichotomy_aux1 hp hp2 g hg
  obtain ⟨B, i, hi2, hMeq⟩ := i167CLin_block_exists g hord M hM
  obtain ⟨c, hcne, hc, hcp⟩ := i167CLin_block_coord B hg
  obtain ⟨e, hDe, hmodel⟩ := i167CLin_block_model h2 B hi2 hM hMeq
  refine ⟨B.d i, e, hmodel, ?_⟩
  by_cases hci : c i = 1
  · right
    have hd : ∀ j, NeZero (B.d j) := fun j => ⟨by have := B.pos j; omega⟩
    have hw : B.Φ (fun j => Matrix.scalar (Fin (B.d j)) (c j)) =
        (g : Matrix (Fin d) (Fin d) K) := hc.symm
    have hj : ∀ j, c j = 1 → j = i := fun j hj1 =>
      CFSG.StandardType.LinNonsplit.eq_of_coord_eq_one hd B.Φ B.Φinj B.Φrange hw
        (by rw [hj1, map_one]) (by rw [hci, map_one])
    obtain ⟨hDcard, hdker⟩ := i167CLin_block_fixed B hc hci hj
    have hea : e = a := by
      apply Nat.pow_right_injective (le_refl 2)
      change 2 ^ e = 2 ^ a
      rw [← hDe, hDcard, hKa]
    exact ⟨hea, hdker, by simpa [hMeq] using i167CLin_block_fixed_triv B hc hci⟩
  · left
    exact i167CLin_block_dichotomy_aux2 hDe hp (hcne i) (hcp i) hci

end CFSG.LocalAnalysis.GLTheoremA.I167

end

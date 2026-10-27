module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniFin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniAux
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Lin
public import CFSG.GH74.L5U5.Models

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open scoped commutatorElement

theorem l154_projMk_eq_iff {I : Type} [Fintype I] [DecidableEq I] {K : Type} [Field K]
    (H : Subgroup (GL I K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar I c = (x : GL I K)⁻¹ * (y : GL I K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

theorem l154_ker_projMk_le_center {I : Type} [Fintype I] [DecidableEq I] {K : Type} [Field K]
    (H : Subgroup (GL I K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l154_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL I K) = Matrix.GeneralLinearGroup.scalar I c⁻¹ := by
    have : (x : GL I K)⁻¹ = Matrix.GeneralLinearGroup.scalar I c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hxG]
  exact (scalar_mul_comm c⁻¹ (y : GL I K)).symm

theorem l154_J_matrix_equiv {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {y : Ω}
    {X J : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hJ : GLAPComponent p X J) (hJS : J ≤ S)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) {I : Type} [Fintype I] [DecidableEq I] {K : Type} [Field K] {H : Subgroup (GL I K)}
    (θ : PSimple p S ≃* LargeEvenProj H) (ψ : MulAut (LargeEvenProj H))
    (hindy : LargeEvenInduces θ (indRel p S y) ψ) (B : GL I K) (σ : K ≃+* K)
    (hψB : ∀ g g' : ↥H, (g' : GL I K) = B * glMap σ (g : GL I K) * B⁻¹ →
      ψ (LargeEvenProjMk H g) = LargeEvenProjMk H g')
    (hBmem : ∀ g ∈ H, B * glMap σ g * B⁻¹ ∈ H)
    {G₁ R₁ : Type} [Group G₁] [Group R₁] (q₁ : G₁ →* R₁) (hq₁s : Function.Surjective q₁)
    (hq₁k : q₁.ker ≤ Subgroup.center G₁) (hR₁ : IsSimpleGroup R₁)
    (ι' : G₁ →* GL I K) (hι'H : ∀ m, ι' m ∈ H)
    (hscal : ∀ (m : G₁) (z : Kˣ), ι' m = Matrix.GeneralLinearGroup.scalar I z → q₁ m = 1)
    (hJP : ∀ z : LargeEvenProj H, z ∈ (chevTransfer p S J).map θ.toMonoidHom ↔
      ∃ m : G₁, LargeEvenProjMk H ⟨ι' m, hι'H m⟩ = z) :
    ∃ e₀ : PSimple p J ≃* R₁, ∀ m : G₁, ∃ (m' : G₁) (z : Kˣ),
      MulAut.congr e₀ (MI.indAut p J y hJy) (q₁ m) = q₁ m' ∧
        ι' m' = Matrix.GeneralLinearGroup.scalar I z * (B * glMap σ (ι' m) * B⁻¹) := by
  classical
  let Ψ : G₁ →* LargeEvenProj H :=
    (LargeEvenProjMk H).comp (ι'.codRestrict H hι'H)
  have hΨ : ∀ m, Ψ m = LargeEvenProjMk H ⟨ι' m, hι'H m⟩ := fun m => rfl
  have hker : ∀ m, Ψ m = 1 → q₁ m = 1 := by
    intro m hm
    have h1 : LargeEvenProjMk H ⟨ι' m, hι'H m⟩ =
        LargeEvenProjMk H 1 := by rw [← hΨ, hm, map_one]
    obtain ⟨c, hc⟩ := (l154_projMk_eq_iff _ _ _).1 h1
    refine hscal m c⁻¹ ?_
    have h2 : ι' m = (Matrix.GeneralLinearGroup.scalar I c)⁻¹ := by
      rw [hc]
      simp
    rw [h2, map_inv]
  obtain ⟨e₀, he₀⟩ := l154_J_equiv_abstract hp hSp hJ hJS hJy θ ψ hindy Ψ q₁ hq₁s hq₁k hR₁ hker hJP
  refine ⟨e₀, fun m => ?_⟩
  obtain ⟨m', hm'1, hm'2⟩ := he₀ m
  have hgm : B * glMap σ (ι' m) * B⁻¹ ∈ H := hBmem _ (hι'H m)
  have hψm : ψ (Ψ m) = LargeEvenProjMk H ⟨B * glMap σ (ι' m) * B⁻¹, hgm⟩ :=
    hψB ⟨ι' m, hι'H m⟩ ⟨_, hgm⟩ rfl
  rw [hψm] at hm'2
  obtain ⟨c, hc⟩ := (l154_projMk_eq_iff _ _ _).1 hm'2
  refine ⟨m', c⁻¹, hm'1, ?_⟩
  have h1 : ι' m' * Matrix.GeneralLinearGroup.scalar I c = B * glMap σ (ι' m) * B⁻¹ := by
    have hc' : Matrix.GeneralLinearGroup.scalar I c =
        (ι' m')⁻¹ * (B * glMap σ (ι' m) * B⁻¹) := hc
    rw [hc']
    group
  rw [← h1, ← mul_assoc, scalar_mul_comm c⁻¹ (ι' m'), mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    mul_one]

theorem l154_notInner_of_line {X : Type} [Group X] {F D : Type} [Field F] [Field D] {I : Type} [Fintype I]
    [DecidableEq I] {n₁ : ℕ} {M : Subgroup (GL (Fin n₁) D)} (ι : GL (Fin n₁) D →* GL I F) (hperf : commutator ↥M = ⊤)
    (σ : F ≃+* F) (B : GL I F) (S₀ : Set (GL (Fin n₁) D))
    (hnorm : ∀ P ∈ S₀, ∀ m ∈ M, P * m * P⁻¹ ∈ M) (e₀ : X ≃* LargeEvenProj M) (α : MulAut X)
    (hequi : ∀ m : ↥M, ∃ (m' : ↥M) (z : Fˣ),
      MulAut.congr e₀ α (LargeEvenProjMk M m) = LargeEvenProjMk M m' ∧
        ι (m' : GL (Fin n₁) D) = Matrix.GeneralLinearGroup.scalar I z *
          (B * glMap σ (ι (m : GL (Fin n₁) D)) * B⁻¹))
    (N : Matrix I I F) (hN : N ≠ 0) (C₀ : Set F) (h1 : (1 : F) ∈ C₀) {c₁ : F} (hc₁ : c₁ ∈ C₀)
    (hσc : σ c₁ ≠ c₁)
    (hT : ∀ c ∈ C₀, ∃ t ∈ M, ((ι t : GL I F) : Matrix I I F) = 1 + c • N) :
    MulAut.congr e₀ α ∉ LargeEvenMatConjImage (LargeEvenProjMk M) S₀ := by
  rintro ⟨P, hP, hgr⟩
  refine l154_no_inner_of_line ι hperf σ B P N hN C₀ h1 hc₁ hσc hT ?_
  intro m hm
  obtain ⟨m', z, hm1, hm2⟩ := hequi ⟨m, hm⟩
  have hPm : P * m * P⁻¹ ∈ M := hnorm P hP m hm
  have h3 := hgr ⟨m, hm⟩ ⟨P * m * P⁻¹, hPm⟩ rfl
  have h4 : LargeEvenProjMk M m' = LargeEvenProjMk M ⟨P * m * P⁻¹, hPm⟩ := by rw [← hm1, h3]
  obtain ⟨c, hc⟩ := (projMk_eq_iff_uni M m' ⟨P * m * P⁻¹, hPm⟩).1 h4
  refine ⟨z, c⁻¹, ?_⟩
  have h5 : (m' : GL (Fin n₁) D) = Matrix.GeneralLinearGroup.scalar (Fin n₁) c⁻¹ * (P * m * P⁻¹) := by
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin n₁) c = (m' : GL (Fin n₁) D)⁻¹ * (P * m * P⁻¹) := hc
    have : (m' : GL (Fin n₁) D) = (P * m * P⁻¹) * (Matrix.GeneralLinearGroup.scalar (Fin n₁) c)⁻¹ := by
      rw [hc']
      group
    rw [this, ← map_inv]
    exact (scalar_mul_comm c⁻¹ _).symm
  rw [← hm2, h5]

theorem l154_sq_eq_one_char_two {F : Type} [Field F] (h2 : (2 : F) = 0) {c : F} (hc : c ^ 2 = 1) : c = 1 := by
  have h : (c - 1) ^ 2 = 0 := by linear_combination hc + (1 - c) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)

theorem l154_notInner_sl2 {X : Type} [Group X] {F : Type} [Field F] [Finite F] (hF2 : (2 : F) = 0) {K : Type}
    [Field K] {I : Type} [Fintype I] [DecidableEq I] (ι : ↥(StatedSL 2 F) →* GL I K) (hperf : commutator ↥(StatedSL 2 F) = ⊤)
    (σ : K ≃+* K) (B : GL I K) (e₀ : X ≃* LargeEvenProj (StatedSL 2 F)) (α : MulAut X)
    (hequi : ∀ m : ↥(StatedSL 2 F), ∃ (m' : ↥(StatedSL 2 F)) (z : Kˣ),
      MulAut.congr e₀ α (LargeEvenProjMk (StatedSL 2 F) m) = LargeEvenProjMk (StatedSL 2 F) m' ∧
        ι m' = Matrix.GeneralLinearGroup.scalar I z * (B * glMap σ (ι m) * B⁻¹))
    (N : Matrix I I K) (hN : N ≠ 0) (C₀ : Set K) (h1 : (1 : K) ∈ C₀) {c₁ : K} (hc₁ : c₁ ∈ C₀)
    (hσc : σ c₁ ≠ c₁)
    (hT : ∀ c ∈ C₀, ∃ t : ↥(StatedSL 2 F), ((ι t : GL I K) : Matrix I I K) = 1 + c • N) :
    MulAut.congr e₀ α ∉ LargeEvenMatConjImage (LargeEvenProjMk (StatedSL 2 F)) Set.univ := by
  classical
  rintro ⟨P, -, hgr⟩
  haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hF2
  have hring : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two hring (((P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply (Matrix.GeneralLinearGroup.det P).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simpa using hc
  let cu : Fˣ := Units.mk0 c hc0
  let s : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) cu⁻¹
  let P' : GL (Fin 2) F := s * P
  have hP' : P' ∈ StatedSL 2 F := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    have e1 : ((P' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        c⁻¹ • ((P : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      simp only [P', s, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      ext i j
      simp [Matrix.mul_apply, Matrix.diagonal_apply, cu]
    rw [e1, Matrix.det_smul, hc]
    simp [cu]
    field_simp
  let t : ↥(StatedSL 2 F) := ⟨P', hP'⟩
  have hconj : ∀ m : GL (Fin 2) F, P * m * P⁻¹ = (t : GL (Fin 2) F) * m * (t : GL (Fin 2) F)⁻¹ := by
    intro m
    have hs := scalar_mul_comm cu⁻¹ (P * m * P⁻¹)
    calc P * m * P⁻¹ = (P * m * P⁻¹) * s * s⁻¹ := by group
      _ = s * (P * m * P⁻¹) * s⁻¹ := by rw [← hs]
      _ = (t : GL (Fin 2) F) * m * (t : GL (Fin 2) F)⁻¹ := by
        show _ = (s * P) * m * (s * P)⁻¹
        group
  have hconjSL : ∀ m : ↥(StatedSL 2 F), P * (m : GL (Fin 2) F) * P⁻¹ ∈ StatedSL 2 F := by
    intro m
    rw [hconj]
    exact (t * m * t⁻¹).2
  have hPeq : ∀ m : ↥(StatedSL 2 F),
      (⟨P * (m : GL (Fin 2) F) * P⁻¹, hconjSL m⟩ : ↥(StatedSL 2 F)) = t * m * t⁻¹ :=
    fun m => Subtype.ext (hconj m)
  refine l154_false_of_displacement ι hperf σ B (ι t)
    (fun v => ∃ z : Kˣ, v = Matrix.GeneralLinearGroup.scalar I z) ?_ ?_ ?_ N hN C₀ h1 hc₁ hσc hT
  · rintro v v' ⟨z, rfl⟩ ⟨z', rfl⟩
    exact scalar_mul_comm z _
  · rintro v ⟨z, rfl⟩ g
    exact scalar_mul_comm z _
  · intro g
    obtain ⟨m', z, hm1, hm2⟩ := hequi g
    have h3 := hgr g ⟨P * (g : GL (Fin 2) F) * P⁻¹, hconjSL g⟩ rfl
    have h4 : LargeEvenProjMk (StatedSL 2 F) m' = LargeEvenProjMk (StatedSL 2 F) (t * g * t⁻¹) := by
      rw [← hm1, h3, hPeq]
    obtain ⟨c', hc'⟩ := (projMk_eq_iff_uni _ m' (t * g * t⁻¹)).1 h4
    have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c' : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [hc']
      exact CFSG.Open.StatedAPI.mem_statedSL_iff.1 (m'⁻¹ * (t * g * t⁻¹)).2
    have hc1 : (c' : F) = 1 := by
      apply l154_sq_eq_one_char_two hF2
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using hdet
    have hc1' : c' = 1 := Units.ext hc1
    have hm'eq : m' = t * g * t⁻¹ := by
      rw [hc1', map_one] at hc'
      have h5 : (m' : GL (Fin 2) F) = ((t * g * t⁻¹ : ↥(StatedSL 2 F)) : GL (Fin 2) F) := by
        have := congrArg (fun w : GL (Fin 2) F => (m' : GL (Fin 2) F) * w) hc'
        simpa using this
      exact Subtype.ext h5
    refine ⟨z⁻¹, ?_⟩
    have hY : ι t * ι g * (ι t)⁻¹ =
        Matrix.GeneralLinearGroup.scalar I z * (B * glMap σ (ι g) * B⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      have : ι (t * g * t⁻¹) = ι m' := by rw [hm'eq]
      rw [← hm2]
      exact this
    rw [hY, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, map_inv]

theorem l154_marking_J_uni {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G] {X J : Subgroup G} {y : G}
    (hJ : GLAPComponent p X J) (hy : y ∈ Subgroup.normalizer (J : Set G)) {r k : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hrk : r = 2 → 2 ≤ k) {D₁ : Type} [Field D₁] [Finite D₁] (hD : Nat.card D₁ = (2 ^ k) ^ 2)
    (e : PSimple p J ≃* LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) D₁ (2 ^ k)))
    (hnot : MulAut.congr e (MI.indAut p J y hy) ∉
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (r + 1)) D₁ (2 ^ k)))
        (LargeEvenGUSet (Fin (r + 1)) D₁ (2 ^ k))) :
    CFSG.Assembly.LargeEvenMarking (PQuot p J) fun lab R _ I _ θ =>
      (lab.tag ≠ .triD4 ∨ p ≠ 3) ∧ ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) ∧
        MulAut.congr θ (MI.indAut p J y hy) ∉ I := by
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hJ
  refine ⟨(isQuasisimple_pQuot_of_glaPComponent hp hJ).1, ⟨.twA, r, k⟩, ⟨hk, hr, hrk⟩, ?_⟩
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeUnitary]
  refine ⟨D₁, inferInstance, inferInstance, hD, e.symm.isSimpleGroup, ?_, e, ?_⟩
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  · exact ⟨Or.inl (by decide), by simp, hnot⟩

end CFSG.LocalAnalysis.GLTheoremA.K155X

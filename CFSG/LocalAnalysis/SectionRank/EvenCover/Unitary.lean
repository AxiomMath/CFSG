module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.LieType.Steinberg CFSG.LieType.CentralExt CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary

section Split

variable {F : Type} [Field F] [Finite F] {f : ℕ} [Fact (Nat.Prime 2)] [CharP F 2]

local notation "σ₀" => unitaryInvolution F 2 f

theorem even_exists_rankOne_section_SU
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup σ₀ (unitaryInvolution_involutive hF) n) k) →* E, ∀ g, π (φ g) = g := by
  have hC := not_two_dvd_of_odd hodd
  by_cases hk : k.val + 1 < n / 2
  · set e := rankOneShortEquiv (hσ := unitaryInvolution_involutive hF) hk
    obtain ⟨ρ, hρ, -⟩ := sl2_existsUnique_lift hπ hcen hC
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h
  · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he hn hk
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    set e' := e.trans (hypEquiv hζ0 hζ).symm
    obtain ⟨ρ, hρ, -⟩ := sl2_existsUnique_lift hπ hcen hC
      ((Subgroup.subtype _).comp e'.symm.toMonoidHom)
    refine ⟨ρ.comp e'.toMonoidHom, fun g => ?_⟩
    have h := DFunLike.congr_fun hρ (e' g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h

theorem even_su_central_odd_extension_splitting
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) {E : Type*} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ s : SU σ₀ n →* E, (∀ x, π (s x) = x) ∧ (∀ τ : SU σ₀ n →* E, (∀ x, π (τ x) = x) → τ = s) ∧
      ∃ e : π.ker × s.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hC := not_two_dvd_of_odd hodd
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact exists_section_mulEquiv_of_existsUnique hcen (existsUnique_section_of_rankOne_lift
    (D := rootDatum hF n) (isCTGroupDatum hF n hn ζ hζ) (steinbergExtras hF n hn ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC
    (even_exists_rankOne_section_SU hF hn he hπ hcen hodd))

theorem even_su_existsUnique_lift
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    (he : Even n) {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (α : SU σ₀ n →* G) :
    ∃! α' : SU σ₀ n →* E, π.comp α' = α := by
  have : Finite (SU σ₀ n) := inferInstance
  obtain ⟨σ, hσ, huniq, -⟩ := even_su_central_odd_extension_splitting hF hn he
    (pullbackFst_surjective hπ α) (pullbackFst_ker_le_center hcen α)
    (Odd.of_dvd_nat hodd (card_pullbackFst_ker_dvd π α))
  refine ⟨_, comp_snd_section σ hσ, fun τ hτ => ?_⟩
  let τ' : SU σ₀ n →* pullback π α :=
    { toFun := fun g => ⟨(g, τ g), by
        change α g = π (τ g)
        rw [← hτ, MonoidHom.comp_apply]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have h1 := huniq τ' fun g => rfl
  ext g
  exact congrArg (fun f : SU σ₀ n →* pullback π α =>
    ((f g : pullback π α) : SU σ₀ n × E).2) h1

end Split

section Block

open Matrix

variable {K : Type} [Field K] {a m : ℕ}

@[expose] def blockMat (A : Matrix (Fin a) (Fin a) K) : Matrix (Fin (a + m)) (Fin (a + m)) K :=
  reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 1)

theorem blockMat_mul (A B : Matrix (Fin a) (Fin a) K) :
    blockMat (m := m) (A * B) = blockMat A * blockMat B := by
  simp only [blockMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blockMat_one : blockMat (m := m) (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  simp [blockMat, fromBlocks_one]

theorem det_blockMat (A : Matrix (Fin a) (Fin a) K) : (blockMat (m := m) A).det = A.det := by
  simp [blockMat]

theorem blockMat_apply_castAdd (A : Matrix (Fin a) (Fin a) K) (i j : Fin a) :
    blockMat (m := m) A (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by
  simp [blockMat]

theorem conjTr_blockMat (σ : K ≃+* K) (A : Matrix (Fin a) (Fin a) K) :
    conjTr σ (blockMat (m := m) A) = blockMat (conjTr σ A) := by
  rw [conjTr, conjTr, blockMat, blockMat, reindex_apply, reindex_apply, ← submatrix_map,
    transpose_submatrix, fromBlocks_map, fromBlocks_transpose, Matrix.map_zero _ (map_zero σ),
    Matrix.map_zero _ (map_zero σ), Matrix.map_one _ (map_zero σ) (map_one σ), transpose_zero,
    transpose_zero, transpose_one]

@[expose] def blockMatHom : Matrix (Fin a) (Fin a) K →* Matrix (Fin (a + m)) (Fin (a + m)) K where
  toFun := blockMat
  map_one' := blockMat_one
  map_mul' := blockMat_mul

@[expose] def blockGL : GL (Fin a) K →* GL (Fin (a + m)) K :=
  Units.map blockMatHom

theorem coe_blockGL (g : GL (Fin a) K) :
    ((blockGL (m := m) g : GL (Fin (a + m)) K) : Matrix (Fin (a + m)) (Fin (a + m)) K) =
      blockMat (g : Matrix (Fin a) (Fin a) K) :=
  rfl

theorem blockGL_mem_SUid (σ : K ≃+* K) {g : GL (Fin a) K} (hg : g ∈ SUid σ a) :
    blockGL (m := m) g ∈ SUid σ (a + m) := by
  obtain ⟨hdet, hiso⟩ := hg
  refine ⟨by rw [coe_blockGL, det_blockMat, hdet], ?_⟩
  rw [coe_blockGL, conjTr_blockMat, ← blockMat_mul, hiso, blockMat_one]

@[expose] def blockSUid (σ : K ≃+* K) : SUid σ a →* SUid σ (a + m) :=
  (blockGL.comp (SUid σ a).subtype).codRestrict _ fun g => blockGL_mem_SUid σ g.2

theorem coe_blockSUid (σ : K ≃+* K) (g : SUid σ a) :
    ((blockSUid (m := m) σ g : SUid σ (a + m)) : GL (Fin (a + m)) K) = blockGL (g : GL _ K) :=
  rfl

theorem eq_one_of_det_scalar_four [CharP K 2] {c : K} (h : c ^ 4 = 1) : c = 1 := by
  have h2 : (c ^ 2) ^ 2 = 1 ^ 2 := by rw [← pow_mul, one_pow]; exact h
  have h1 : c ^ 2 = 1 ^ 2 := by rw [CharTwo.sq_inj.1 h2, one_pow]
  exact CharTwo.sq_inj.1 h1

theorem eq_one_of_blockGL_mem_statedScalars [CharP K 2] {g : GL (Fin 4) K}
    (hdet : (g : Matrix (Fin 4) (Fin 4) K).det = 1)
    (h : blockGL (m := m) g ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin (4 + m)) K) :
    g = 1 := by
  obtain ⟨c, hc⟩ := h
  have hg : (g : Matrix (Fin 4) (Fin 4) K) = Matrix.scalar (Fin 4) (c : K) := by
    ext i j
    have := congrArg (fun M : GL (Fin (4 + m)) K =>
      (M : Matrix (Fin (4 + m)) (Fin (4 + m)) K) (Fin.castAdd m i) (Fin.castAdd m j)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_blockGL, blockMat_apply_castAdd,
      scalar_apply, diagonal_apply, Fin.castAdd_inj] at this
    rw [← this, scalar_apply, diagonal_apply]
  rw [hg, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    at hdet
  have hc1 := eq_one_of_det_scalar_four hdet
  apply Units.ext
  rw [hg, hc1, Units.val_one, map_one]

end Block

open CFSG.Assembly.LowTwoRank CFSG.Open

theorem statedScalars_subgroupOf_statedSU_four_eq_bot {K : Type} [Field K] [CharP K 2] (q : ℕ) :
    (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 q K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hdet := det_eq_one_of_mem_statedSU g.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc1 := eq_one_of_det_scalar_four hdet
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, hc1, map_one]
  rfl

theorem even_unitary_SQT_degree_three_bound
    {L : Type} [Group L] [Finite L]
    (_hL : IsQuasisimple L) (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {n f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) : n = 3 := by
  obtain ⟨⟨-, hf, hn3, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card (f := f * 2) (by rw [hK, pow_mul])
  set σ := unitaryInvolution K 2 f
  let ι : SU σ 4 →* StatedSU (4 + m) (2 ^ f) K :=
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK (4 + m))).toMonoidHom.comp
      ((blockSUid σ).comp ((MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)).symm.toMonoidHom.comp
        (equivStatedSU hK 4).toMonoidHom))
  let α : SU σ 4 →* L ⧸ Subgroup.center L :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ι)
  have hα : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    set y := equivStatedSU hK 4 x with hy
    have hιx : ((ι x : StatedSU (4 + m) (2 ^ f) K) : GL (Fin (4 + m)) K) =
        blockGL ((y : StatedSU 4 (2 ^ f) K) : GL (Fin 4) K) := rfl
    rw [hιx] at hx
    have hy1 : y = 1 := Subtype.ext (eq_one_of_blockGL_mem_statedScalars
      (det_eq_one_of_mem_statedSU y.2) hx)
    rw [Subgroup.mem_bot]
    exact (equivStatedSU hK 4).injective (hy1.trans (map_one _).symm)
  have hker : (QuotientGroup.mk' (Subgroup.center L)).ker = Subgroup.center L :=
    QuotientGroup.ker_mk' _
  obtain ⟨α', hα', -⟩ := even_su_existsUnique_lift hK (by norm_num) (by decide : Even 4)
    (QuotientGroup.mk'_surjective (Subgroup.center L)) hker.le (by rw [hker]; exact hodd) α
  have hα'inj : Function.Injective α' := by
    intro x y hxy
    apply hα
    rw [← hα', MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]
  obtain ⟨r, hr, hr2, hrank⟩ := ClassicalEven.psu_torus_three_le_pRank hK hf le_rfl
  have hD := statedScalars_subgroupOf_statedSU_four_eq_bot (K := K) (2 ^ f)
  let ε : StatedProj (StatedSU 4 (2 ^ f) K) ≃* StatedSU 4 (2 ^ f) K :=
    (QuotientGroup.quotientMulEquivOfEq hD).trans QuotientGroup.quotientBot
  let β : StatedProj (StatedSU 4 (2 ^ f) K) →* L :=
    α'.comp ((equivStatedSU hK 4).symm.toMonoidHom.comp ε.toMonoidHom)
  have hβ : Function.Injective β :=
    hα'inj.comp ((equivStatedSU hK 4).symm.injective.comp ε.injective)
  have h1 := pRank_top_le_of_injective hr.one_lt β hβ
  have h2 := (isStronglyQuasithin_iff.1 hSQT) r hr hr2
  omega

end CFSG.SectionRank.EvenCover

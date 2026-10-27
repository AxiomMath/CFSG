module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om5
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem cast_prime_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : F) ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

section Count

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem blockEnd_commute_of_ne (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane A p} (hDE : D ≠ E) :
    Commute (blockEnd A hp hpF hA t ht D) (blockEnd A hp hpF hA t ht E) := by
  have hD : blockEndOf A hp hpF hA (t D) D = blockEnd A hp hpF hA t ht D := by
    have h := blockEndOf_eq_zpow_blockEnd A hp hpF hA t ht (D := D) (d := 1)
      (Subgroup.one_mem D.1) 1 (by rw [one_mul, pow_one])
    simpa using h
  have hE : blockEndOf A hp hpF hA (t E) E = blockEnd A hp hpF hA t ht E := by
    have h := blockEndOf_eq_zpow_blockEnd A hp hpF hA t ht (D := E) (d := 1)
      (Subgroup.one_mem E.1) 1 (by rw [one_mul, pow_one])
    simpa using h
  rw [← hD, ← hE]
  exact blockEndOf_commute A hp hpF hA (t D) (t E) (Ne.symm hDE)

theorem pRank_le_card_ne_bot_blockSpace (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) :
    CFSG.Open.pRank p A ≤ (nonBotBlocks A p).card := by
  classical
  set S := nonBotBlocks A p with hS
  have hgen : (A : Set (V ≃ₗ[F] V)) ⊆ Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) :=
    le_closure_blockEnd A hp hpF hA t ht
  have hclosure : Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht)) =
      Subgroup.closure ((fun D => blockEnd A hp hpF hA t ht D) '' (S : Set (Hyperplane A p))) := by
    refine le_antisymm ?_ (Subgroup.closure_mono (Set.image_subset_range _ _))
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨D, rfl⟩
    by_cases hD : D ∈ S
    · exact Subgroup.subset_closure ⟨D, hD, rfl⟩
    · have hzero : blockSpace A D.1 = ⊥ := by
        by_contra hne
        exact hD ((mem_nonBotBlocks A p).mpr hne)
      have h1 : blockEnd A hp hpF hA t ht D = 1 := by
        refine LinearEquiv.ext fun v => ?_
        obtain ⟨u, r, hcu, rfl⟩ :=
          CFSG.RankThree.PartOne.KCOrthogonal.exists_coe_add_of_isCompl
            (isCompl_blockSpace_ker A hp hpF hA D) v
        have hu : (u : V) = 0 := by
          have h : (u : V) ∈ (⊥ : Submodule F V) := by rw [← hzero]; exact u.2
          simpa using h
        have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
          rw [LinearMap.mem_ker]; exact r.2
        rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
          blockEnd_apply_of_ker A hp hpF hA t ht D hr, hu]
        simp
      rw [h1]
      exact Subgroup.one_mem _
  set T := S.image (fun D => blockEnd A hp hpF hA t ht D) with hT
  have hTclosure : Subgroup.closure ((fun D => blockEnd A hp hpF hA t ht D) '' (S : Set _)) =
      Subgroup.closure (↑T : Set (V ≃ₗ[F] V)) := by
    rw [hT]
    simp
  have hpow : ∀ x ∈ T, x ^ p = 1 := by
    intro x hx
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp hx
    exact blockEnd_pow A hp hpF hA t ht D
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hy
    by_cases hDE : D = E
    · subst hDE; rfl
    · exact (blockEnd_commute_of_ne A hp hpF hA t ht hDE).eq
  have hcardT : Nat.card ↥(Subgroup.closure (↑T : Set (V ≃ₗ[F] V))) ≤ p ^ T.card :=
    HypBlocks.card_closure_finset_le_pow T hp hpow hcomm
  have hTS : T.card ≤ S.card := Finset.card_image_le
  have hbound :
      Nat.card ↥(Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht))) ≤ p ^ S.card := by
    rw [hclosure, hTclosure]
    exact le_trans hcardT (Nat.pow_le_pow_right hp.pos hTS)
  have hmono : CFSG.Open.pRank p A ≤
      CFSG.Open.pRank p (Subgroup.closure (Set.range (blockEnd A hp hpF hA t ht))) :=
    CFSG.SectionRank.pRank_mono hp.one_lt hgen
  exact hmono.trans (CFSG.SectionRank.pRank_le hp.one_lt
    (fun E hE _ => (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hE)).trans hbound))

end Count

section Image

variable {p : ℕ} {Ã : Subgroup ↥(orthDerived Q)}

@[expose] def orthImage (Ã : Subgroup ↥(orthDerived Q)) : Subgroup (V ≃ₗ[F] V) :=
  Ã.map (orthDerived Q).subtype

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem isElemAbelian_orthImage (hÃe : IsElemAbelian p Ã) :
    IsElemAbelian p (orthImage Ã) :=
  CFSG.SectionRank.isElemAbelian_map hÃe _

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem orthImage_le (Ã : Subgroup ↥(orthDerived Q)) : orthImage Ã ≤ orthDerived Q := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem pRank_orthImage (hp : p.Prime) :
    CFSG.Open.pRank p (orthImage Ã) = CFSG.Open.pRank p Ã :=
  CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt _
    (orthDerived Q).subtype_injective Ã

theorem quadratic_orthImage (a : ↥(orthImage Ã)) (v : V) :
    Q ((a : V ≃ₗ[F] V) v) = Q v :=
  (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (orthDerived_le_orthogonalGroup_of_commutator Q (orthImage_le Ã a.2))) v

theorem polar_orthImage (a : ↥(orthImage Ã)) (u v : V) :
    polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v := by
  rw [polarBilin_apply_apply, polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.polar,
    ← (a : V ≃ₗ[F] V).map_add u v, quadratic_orthImage a (u + v),
    quadratic_orthImage a u, quadratic_orthImage a v]

end Image

section Regime

variable {n p q : ℕ} {Ã : Subgroup ↥(orthDerived Q)}

theorem exists_isTotallyIsotropic_of_regime
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hÃe : IsElemAbelian p Ã)
    (hÃ3 : 3 ≤ CFSG.Open.pRank p Ã)
    (hreg : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      (CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 2 ∧ ∃ ℓ : ℕ,
        Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        ℓ - 1 ≤ CFSG.Open.pRank p Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1) :
    ∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0 := by
  letI : Fintype ↥(orthImage Ã) := Fintype.ofFinite ↥(orthImage Ã)
  have hpF : (p : F) ≠ 0 := cast_prime_ne_zero hp hp2
  have hA : IsElemAbelian p (orthImage Ã) := isElemAbelian_orthImage hÃe
  have hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Ã) a
  have hcard : 3 ≤ (nonBotBlocks (orthImage Ã) p).card := by
    have h1 : 3 ≤ CFSG.Open.pRank p (orthImage Ã) := by
      rw [pRank_orthImage (Ã := Ã) hp]; exact hÃ3
    exact le_trans h1 (pRank_le_card_ne_bot_blockSpace (orthImage Ã) hp hpF hA t ht)
  rcases hreg with hm0 | ⟨-, ℓ, hdim, -, h5, -⟩
  · obtain ⟨D, E, -, -, -, h8, -⟩ :=
      OmEngine.exists_blocks_regimeI (orthImage Ã) hQ hp hpF hp2 hA hB t ht hn hm0 hcard
    have hdimD := OmEngine.finrank_fixedSpace_blockEnd (orthImage Ã) hp hpF hA t ht D
    have hV : 8 ≤ Module.finrank F V := by
      rw [hdimD] at h8
      omega
    exact OmEngine.exists_threeSingular_of_eight_le hQ hV
  · exact OmEngine.exists_threeSingular_of_eight_le hQ (by omega)

end Regime

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F

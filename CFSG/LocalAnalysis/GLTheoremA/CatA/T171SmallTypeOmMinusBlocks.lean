module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusSiegel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om4
public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_invariant_totallyIsotropic_of_twoLocal
    (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank (ZMod 2) V = 2 * 5)
    {Bb P : Subgroup ↥(orthDerived Q)} (hP2 : IsPGroup 2 P) (hPne : P ≠ ⊥)
    (hBN : Bb ≤ Subgroup.normalizer (P : Set ↥(orthDerived Q))) :
    ∃ R : Submodule (ZMod 2) V, R ≠ ⊥ ∧
      (∀ b ∈ Bb, ∀ v ∈ R, ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v ∈ R) ∧
      R ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) R := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  let φ : P →* (V ≃ₗ[ZMod 2] V) := (orthDerived Q).subtype.comp P.subtype
  let C : Submodule (ZMod 2) V := CFSG.LargeExtraspecial.fixSpaceOf (P.map (orthDerived Q).subtype)
  have hCmem : ∀ v : V, v ∈ C ↔ ∀ p ∈ P, ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v = v := by
    intro v
    rw [CFSG.LargeExtraspecial.mem_fixSpaceOf]
    constructor
    · intro h p hp
      exact h _ (Subgroup.mem_map_of_mem (orthDerived Q).subtype hp)
    · intro h a ha
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 ha
      exact h p hp
  have hCne : C ≠ ⊥ := by
    obtain ⟨u, -, hu0, hufix⟩ := CFSG.LargeExtraspecial.S4.exists_fixed_ne_zero hP2 φ
      (U := (⊤ : Submodule (ZMod 2) V)) (fun _ _ _ => Submodule.mem_top) (by simp)
    refine (Submodule.ne_bot_iff C).2 ⟨u, ?_, hu0⟩
    rw [hCmem]
    intro p hp
    exact hufix ⟨p, hp⟩
  have hCtop : C ≠ ⊤ := by
    intro htop
    obtain ⟨p, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hPne
    have hpV : ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ≠ 1 := by
      intro h
      apply hp1
      exact Subtype.ext (Subtype.ext h)
    have hex : ∃ v : V, ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v ≠ v := by
      by_contra h
      push Not at h
      exact hpV (LinearEquiv.ext h)
    obtain ⟨v, hv⟩ := hex
    have hmem : v ∈ C := by rw [htop]; exact Submodule.mem_top
    exact hv ((hCmem v).1 hmem p p.2)
  let Corth : Submodule (ZMod 2) V := LinearMap.BilinForm.orthogonal (polarBilin Q) C
  have hCorthne : Corth ≠ ⊥ := by
    intro hbot
    apply hCtop
    have h := congrArg (LinearMap.BilinForm.orthogonal (polarBilin Q)) hbot
    rw [LinearMap.BilinForm.orthogonal_bot,
      LinearMap.BilinForm.orthogonal_orthogonal hQ
        (CFSG.LargeExtraspecial.OrthoF2.isRefl_polarBilin Q)] at h
    exact h
  have hCinv : ∀ b ∈ Bb, ∀ v ∈ C, ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v ∈ C := by
    intro b hb v hv
    rw [hCmem] at hv ⊢
    intro p hp
    have hbN : (b : ↥(orthDerived Q))⁻¹ ∈
        Subgroup.normalizer (P : Set ↥(orthDerived Q)) :=
      Subgroup.inv_mem _ (hBN hb)
    have hconj : ((b : ↥(orthDerived Q))⁻¹ * p * b : ↥(orthDerived Q)) ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hbN p).1 hp
    have hcoe : ((((b : ↥(orthDerived Q))⁻¹ * p * b : ↥(orthDerived Q)) :
        V ≃ₗ[ZMod 2] V)) =
        ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)⁻¹ *
          ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
            ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)
          (((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v)
        = (((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
            ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)) v :=
          (LinearEquiv.mul_apply ..).symm
      _ = (((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
            ((((b : ↥(orthDerived Q))⁻¹ * p * b : ↥(orthDerived Q)) :
              V ≃ₗ[ZMod 2] V))) v := by
          rw [hcoe]
          group
      _ = ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)
            ((((b : ↥(orthDerived Q))⁻¹ * p * b : ↥(orthDerived Q)) :
              V ≃ₗ[ZMod 2] V) v) := LinearEquiv.mul_apply ..
      _ = ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v := by rw [hv _ hconj]
  have hCorthinv : ∀ b ∈ Bb, ∀ v ∈ Corth,
      ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v ∈ Corth := by
    intro b hb v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro c hc
    have hbinv : (b : ↥(orthDerived Q))⁻¹ ∈ Bb := Subgroup.inv_mem _ hb
    have hcinv : ((b : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c ∈ C :=
      hCinv _ hbinv c hc
    have h0 : polar Q (((b : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c) v = 0 := by
      have := hv _ hcinv
      simpa [polarBilin_apply_apply] using this
    have hbO : ((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup b.2
    have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hbO
      (((b : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c) v
    have hiso' : polar Q c (((b : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v) =
        polar Q (((b : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c) v := by
      simpa using hiso
    rw [polarBilin_apply_apply, hiso']
    exact h0
  have hCorthP : ∀ p ∈ P, ∀ v ∈ Corth,
      ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v ∈ Corth := by
    intro p hp v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro c hc
    have h0 : polar Q c v = 0 := by
      have := hv _ hc
      simpa [polarBilin_apply_apply] using this
    have hcp : ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) c = c := (hCmem c).1 hc p hp
    have hcinv : ((p : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c = c := by
      nth_rewrite 1 [← hcp]
      exact LinearEquiv.symm_apply_apply _ c
    have hpO : ((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup p.2
    have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hpO
      (((p : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c) v
    have hiso' : polar Q c (((p : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) v) =
        polar Q (((p : ↥(orthDerived Q))⁻¹ : V ≃ₗ[ZMod 2] V) c) v := by
      simpa using hiso
    rw [polarBilin_apply_apply, hiso', hcinv]
    exact h0
  have hCorthP' : ∀ x : P, ∀ u ∈ Corth, φ x u ∈ Corth := fun x => hCorthP x x.2
  obtain ⟨u, huCorth, hu0, hufix⟩ :=
    CFSG.LargeExtraspecial.S4.exists_fixed_ne_zero hP2 φ (U := Corth) hCorthP' hCorthne
  have huC : u ∈ C := by
    rw [hCmem]
    intro p hp
    exact hufix ⟨p, hp⟩
  let R : Submodule (ZMod 2) V := C ⊓ Corth
  have hRne : R ≠ ⊥ := by
    refine (Submodule.ne_bot_iff R).2 ⟨u, ?_, hu0⟩
    exact Submodule.mem_inf.2 ⟨huC, huCorth⟩
  refine ⟨R, hRne, ?_, ?_⟩
  · intro b hb v hv
    exact Submodule.mem_inf.2 ⟨hCinv b hb v hv.1, hCorthinv b hb v hv.2⟩
  · intro r hr
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro s hs
    have hrCorth : r ∈ Corth := (Submodule.mem_inf.1 hr).2
    have hsC : s ∈ C := (Submodule.mem_inf.1 hs).1
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.1 hrCorth) s hsC
    simpa [polarBilin_apply_apply, polar_comm] using h

open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

noncomputable abbrev blockSet (A : Subgroup (V ≃ₗ[ZMod 2] V)) [Fintype A] :
    Finset (Hyperplane A 3) :=
  nonBotBlocks A 3

theorem card_blockSet_le_five (hQ : (polarBilin Q).Nondegenerate)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A] (hA : IsElemAbelian 3 A)
    (hAcard : Nat.card A = 3 ^ 4) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hB : ∀ a : ↥A, ∀ u v : V, polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u)
      ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v) :
    (blockSet A).card ≤ 5 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hsum : (∑ D ∈ blockSet A, finrank (ZMod 2) ↥(blockSpace A D.1)) =
      ∑ D : Hyperplane A 3, finrank (ZMod 2) ↥(blockSpace A D.1) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro D _ hDnot
    have hzero : blockSpace A D.1 = ⊥ := by
      by_contra hne
      exact hDnot (by simpa only [blockSet] using
        (mem_nonBotBlocks (A := A) (p := 3)).2 hne)
    simp [hzero]
  have htwo : ∀ D ∈ blockSet A, 2 ≤ finrank (ZMod 2) ↥(blockSpace A D.1) := by
    intro D hD
    exact two_le_finrank_blockSpace A h2 hQ hp hpF hA hB D
      (by simpa only [blockSet] using
        (mem_nonBotBlocks (A := A) (p := 3)).1 (by simpa only [blockSet] using hD))
  have hlower : (blockSet A).card * 2 ≤
      ∑ D ∈ blockSet A, finrank (ZMod 2) ↥(blockSpace A D.1) := by
    calc (blockSet A).card * 2 = ∑ _D ∈ blockSet A, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ D ∈ blockSet A, finrank (ZMod 2) ↥(blockSpace A D.1) :=
          Finset.sum_le_sum htwo
  have hdimsum := finrank_eq_finrank_fixedSpaceOf_add_sum_blockSpace A hp hpF hA
  rw [← hsum, hdim] at hdimsum
  have hCs : finrank (ZMod 2) (fixedSpaceOf A) ≤ 10 := by omega
  have h2c : (blockSet A).card * 2 ≤ 10 := by omega
  omega

theorem four_le_card_blockSet (hQ : (polarBilin Q).Nondegenerate)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} [Fintype A] (hA : IsElemAbelian 3 A)
    (hAcard : Nat.card A = 3 ^ 4) (hdim : finrank (ZMod 2) V = 2 * 5)
    (hfaith : ∀ a : ↥A, (∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v) → a = 1) :
    4 ≤ (blockSet A).card := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF : (3 : ZMod 2) ≠ 0 := by decide
  by_contra hlt
  push Not at hlt
  have hb3 : (blockSet A).card ≤ 3 := by omega
  let f : blockSet A → Subgroup ↥A := fun D => D.1
  have hindex : (⨅ D : blockSet A, f D).index ≤ 3 ^ (blockSet A).card := by
    refine (Subgroup.index_iInf_le f).trans ?_
    have hprod : (∏ D : blockSet A, (f D).index) = 3 ^ (blockSet A).card := by
      rw [show (∏ D : blockSet A, (f D).index) = ∏ _D : blockSet A, 3 from
        Finset.prod_congr rfl fun D _ => D.1.2]
      simp [Finset.prod_const, Finset.card_univ]
    rw [hprod]
  have hne : (⨅ D : blockSet A, f D) ≠ ⊥ := by
    intro hbot
    have hcard : (⨅ D : blockSet A, f D).index = 3 ^ 4 := by
      have h := (⨅ D : blockSet A, f D).card_mul_index
      rw [hbot, Subgroup.card_bot, one_mul, hAcard] at h
      simpa [hbot] using h
    have hle : 3 ^ 4 ≤ 3 ^ (blockSet A).card := by
      rw [← hcard]
      exact hindex
    have hle' : 3 ^ (blockSet A).card ≤ 3 ^ 3 :=
      Nat.pow_le_pow_right (by norm_num) hb3
    have : (3 : ℕ) ^ 4 ≤ 3 ^ 3 := hle.trans hle'
    norm_num at this
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have haD : ∀ D ∈ blockSet A, (a : ↥A) ∈ D.1 := by
    intro D hD
    exact (Subgroup.mem_iInf.mp a.2) ⟨D, hD⟩
  have hker : ∀ a : ↥A, (∀ D ∈ blockSet A, a ∈ D.1) →
      (∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v) := by
    intro a ha v
    have hdecomp : v ∈ fixedSpaceOf A ⊔
        (⨆ D : Hyperplane A 3, blockSpace A D.1) := by
      rw [sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA]
      exact Submodule.mem_top
    obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hdecomp
    rw [map_add]
    have hc' : (a : V ≃ₗ[ZMod 2] V) c = c := (mem_fixedSpaceOf A).1 hc a
    have hw' : (a : V ≃ₗ[ZMod 2] V) w = w := by
      have hle : (⨆ D : Hyperplane A 3, blockSpace A D.1) ≤
          CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (a : V ≃ₗ[ZMod 2] V) := by
        refine iSup_le fun D => ?_
        intro x hx
        rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace]
        by_cases hD : D ∈ blockSet A
        · exact (mem_blockSpace A).1 hx |>.1 a (ha D hD)
        · have hzero : blockSpace A D.1 = ⊥ := by
            by_contra hne
            exact hD (by simpa only [blockSet] using
              (mem_nonBotBlocks (A := A) (p := 3)).2 hne)
          rw [hzero, Submodule.mem_bot] at hx
          rw [hx]
          exact map_zero _
      exact (CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace).1 (hle hw)
    rw [hc', hw']
  exact ha1 (Subtype.ext (hfaith (a : ↥A) (hker (a : ↥A) haD)))

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

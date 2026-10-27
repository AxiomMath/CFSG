module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin11
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

noncomputable def statedSLEquivSpecialLinearGroup (d : ℕ) (F : Type) [Field F] :
    ↥(StatedSL d F) ≃* SpecialLinearGroup F (Fin d → F) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F).symm.trans
    (Matrix.SpecialLinearGroup.toLin_equiv (Pi.basisFun F (Fin d)))

namespace LinEngine

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {p : ℕ}

private theorem exists_three_ne_bot_blockSpace_sorted (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    [Finite (V ≃ₗ[F] V)] {k : ℕ} (hk : Nat.card ↥A = p ^ k)
    {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H) (hHH : CFSG.Open.pRank p H ≤ k)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) (hk3 : 3 ≤ k) :
    ∃ D₁ D₂ D₃ : Hyperplane A p, D₁ ≠ D₂ ∧ D₁ ≠ D₃ ∧ D₂ ≠ D₃ ∧
      blockSpace A D₁.1 ≠ ⊥ ∧ blockSpace A D₂.1 ≠ ⊥ ∧ blockSpace A D₃.1 ≠ ⊥ ∧
      Module.finrank F ↥(blockSpace A D₁.1) ≤ Module.finrank F ↥(blockSpace A D₂.1) ∧
      Module.finrank F ↥(blockSpace A D₁.1) ≤ Module.finrank F ↥(blockSpace A D₃.1) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ :=
    exists_three_ne_bot_blockSpace A hp hpF hA t ht hk hAH hHH htH hk3
  have hs : ({a, b, c} : Finset (Hyperplane A p)).Nonempty := ⟨a, by simp⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image ({a, b, c} : Finset (Hyperplane A p))
    (fun D => Module.finrank F ↥(blockSpace A D.1)) hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hma | hmb | hmc
  · subst m
    exact ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hmin b (by simp), hmin c (by simp)⟩
  · subst m
    exact ⟨b, a, c, hab.symm, hbc, hac, hb, ha, hc, hmin a (by simp), hmin c (by simp)⟩
  · subst m
    exact ⟨c, a, b, hac.symm, hbc.symm, hab, hc, ha, hb, hmin a (by simp), hmin b (by simp)⟩

end LinEngine

open LinEngine

theorem concl165Avoid_specialLinear (F : Type) [Field F] [Fintype F] (n d p q : ℕ)
    (hcard : Fintype.card F = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hm0 : 2 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (hd : 3 * CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≤ d)
    (hsmall : 2 ≤ n ∨ 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : Module.finrank F V = d)
    (A : Subgroup (SpecialLinearGroup F V)) (hAe : IsElemAbelian p A)
    (hmax : CFSG.Open.pRank p (⊤ : Subgroup (SpecialLinearGroup F V)) ≤ CFSG.Open.pRank p A)
    (h3 : 3 ≤ CFSG.Open.pRank p A) :
    Concl165Avoid (SpecialLinearGroup F V) p q A (Subgroup.center (SpecialLinearGroup F V)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (SpecialLinearGroup F V) := by
    haveI : Finite (V ≃ₗ[F] V) := finite_linearEquiv_self
    exact Subtype.finite
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0] at hm0
      simp [CFSG.LocalAnalysis.GLTheoremA.rk2Ord] at hm0
    · exact h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := by
    have h2 : ringChar F = 2 := by
      rw [FiniteField.even_card_iff_char_two, hcard]
      exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn1))
    exact ringChar.of_eq h2
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hpd : ¬ p ∣ Fintype.card F - 1 := by
    rw [hcard]
    intro hdvd
    have h1 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.rk2Ord_eq_one_iff.mpr hdvd
    omega
  set Agl : Subgroup (V ≃ₗ[F] V) := A.map SpecialLinearGroup.toLinearEquiv with hAgldef
  have hAgl : IsElemAbelian p Agl := by
    rw [hAgldef]
    exact IsElemAbelian.map hAe SpecialLinearGroup.toLinearEquiv
  have hAdet : Agl ≤ LinearEquiv.det.ker := by
    rintro x ⟨a, -, rfl⟩
    exact MonoidHom.mem_ker.mpr a.2
  haveI : Finite ↥Agl := Subtype.finite
  haveI : Fintype ↥Agl := Fintype.ofFinite ↥Agl
  obtain ⟨t, ht⟩ := exists_blockRep (A := Agl) (p := p) hp
  set SLgl : Subgroup (V ≃ₗ[F] V) :=
    (⊤ : Subgroup (SpecialLinearGroup F V)).map SpecialLinearGroup.toLinearEquiv with hSLgldef
  have hAsub : Agl ≤ SLgl := by
    rintro x ⟨a, -, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top a, rfl⟩
  have htoSL : ∀ D, blockEnd Agl hp hpF hAgl t ht D ∈ SLgl := by
    intro D
    refine Subgroup.mem_map.mpr
      ⟨⟨blockEnd Agl hp hpF hAgl t ht D,
        blockEnd_mem_specialLinear Agl hp hpF hAgl t ht hpd D⟩, Subgroup.mem_top _, rfl⟩
  have hkAgl : Nat.card ↥Agl = p ^ CFSG.Open.pRank p A := by
    have h1 : Nat.card ↥Agl = Nat.card ↥A := by
      rw [hAgldef]
      exact Subgroup.card_map_of_injective (fun _ _ h => Subtype.ext h)
    rw [h1]
    exact CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hAe
  have hmaxSL : CFSG.Open.pRank p SLgl ≤ CFSG.Open.pRank p A := by
    have h1 : CFSG.Open.pRank p SLgl =
        CFSG.Open.pRank p (⊤ : Subgroup (SpecialLinearGroup F V)) := by
      rw [hSLgldef]
      exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt
        SpecialLinearGroup.toLinearEquiv (fun _ _ h => Subtype.ext h) ⊤
    rw [h1]
    exact hmax
  have hAglEq := eq_closure_blockEnd_of_pRank_le (A := Agl) hp hpF hAgl t ht
    (k := CFSG.Open.pRank p A) hkAgl hAsub hmaxSL htoSL
  have hmemAgl : ∀ D, blockEnd Agl hp hpF hAgl t ht D ∈ Agl := fun D =>
    hAglEq.ge (Subgroup.subset_closure ⟨D, rfl⟩)
  obtain ⟨D₁, D₂, D₃, hD₁₂, hD₁₃, hD₂₃, hD₁, hD₂, hD₃, hle₁₂, hle₁₃⟩ :=
    exists_three_ne_bot_blockSpace_sorted Agl hp hpF hAgl t ht hkAgl hAsub hmaxSL htoSL h3
  have hthree : 3 * Module.finrank F ↥(blockSpace Agl D₁.1) ≤ Module.finrank F V :=
    three_mul_finrank_blockSpace_le (A := Agl) hp hpF hAgl hD₁₂ hD₁₃ hD₂₃ hle₁₂ hle₁₃
  have hfixed : Module.finrank F ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) =
      Module.finrank F V - Module.finrank F ↥(blockSpace Agl D₁.1) :=
    finrank_fixedByEnd_blockEnd (A := Agl) hp hpF hAgl t ht D₁
  have hd6 : 6 ≤ d := by
    have := hm0
    omega
  have hfixed4 : 4 ≤ Module.finrank F
      ↥(fixedByEnd (blockEnd Agl hp hpF hAgl t ht D₁)) := by
    rw [hfixed, hV]
    omega
  obtain ⟨t₁, t₂, ht₁coe, ht₂coe, hqJ, hqL, ht₁A, ht₂A⟩ :=
    exists_blockElements_quasisimple (A := A) (Agl := Agl) (D₁ := D₁) (D₂ := D₂)
      (D₃ := D₃) (n := n) hp hp2 hpF hAgl t ht hpd hAgldef hmemAgl hD₁₃ hD₂₃ hD₃ hfixed4
      hcard hn1 hm0 hsmall
  exact concl165Avoid_of_blockData (A := A) (Agl := Agl) (p := p) (q := q) (n := n) (d := d)
    hp hpF hAgl hAdet hpd hkAgl t ht hD₁ hD₂ hD₁₂ hfixed hthree hfixed4 hV hcard hsmall hm0
    hd h3 hq hqdiv hAe ht₁coe ht₂coe ht₁A ht₂A hqJ hqL

theorem sl165EngineFamA_holds : SL165EngineFamA := by
  intro F _ _ n d p q hcard hp hp2 hq hq2 hqp hm0 hd hsmall hqdiv Ã hÃe hÃmax hÃ3
  classical
  let e : ↥(StatedSL d F) ≃* SpecialLinearGroup F (Fin d → F) :=
    statedSLEquivSpecialLinearGroup d F
  haveI : Finite ((Fin d → F) ≃ₗ[F] (Fin d → F)) := by
    infer_instance
  have hmodel : Concl165Avoid (SpecialLinearGroup F (Fin d → F)) p q
      (Ã.map e.toMonoidHom) (Subgroup.center (SpecialLinearGroup F (Fin d → F))) := by
    refine concl165Avoid_specialLinear F n d p q hcard hp hp2 hq hq2 hqp hm0 hd hsmall
      hqdiv (V := Fin d → F) (by simp [Module.finrank_fin_fun]) (Ã.map e.toMonoidHom) ?_ ?_ ?_
    · exact hÃe.map e.toMonoidHom
    · rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
        CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt e.toMonoidHom
          e.injective Ã]
      exact hÃmax
    · rw [CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective hp.one_lt e.toMonoidHom
        e.injective Ã]
      exact hÃ3
  have hZ : ((StatedScalars (Fin d) F).subgroupOf (StatedSL d F)).map e.toMonoidHom =
      Subgroup.center (SpecialLinearGroup F (Fin d → F)) := by
    have h1 : (StatedScalars (Fin d) F).subgroupOf (StatedSL d F) =
        Subgroup.center (↥(StatedSL d F)) := by
      rw [← CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars d F,
        Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F)]
    rw [h1]
    simpa using (Subgroup.map_center_eq e)
  have hmodel' : Concl165Avoid (SpecialLinearGroup F (Fin d → F)) p q
      (Ã.map e.toMonoidHom)
      (((StatedScalars (Fin d) F).subgroupOf (StatedSL d F)).map e.toMonoidHom) := by
    rw [hZ]
    exact hmodel
  exact concl165Avoid_of_mulEquiv hp hq e hmodel'

end CFSG.LocalAnalysis.GLTheoremA.Y10F

module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmAltPerm
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

section Alternating

variable {X : Type} [Group X]

theorem oPPrimeHull_three_top_eq_of_alternating {L : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) = ⊥) {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : ↥L ≃* alternatingGroup (Fin n)) :
    oPPrimeHull 3 (⊤ : Subgroup X) = L := by
  classical
  obtain ⟨ι, hιinj, hι⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Alt.exists_perm_embedding
      hn hn6 e hC
  apply le_antisymm
  · rw [oPPrimeHull, Subgroup.closure_le]
    rintro x ⟨-, k, hk⟩
    have hodd : Odd (orderOf (ι x)) :=
      Odd.of_dvd_nat (Odd.pow (n := k) (show Odd 3 by norm_num))
        (hk ▸ orderOf_map_dvd ι x)
    have hsign : Equiv.Perm.sign (ι x) = 1 := by
      have h1 : (Equiv.Perm.sign (ι x)) ^ orderOf (ι x) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ι x)) with h2 | h2
      · exact h2
      · rw [h2, hodd.neg_one_pow] at h1; exact absurd h1 (by decide)
    have hmemA : ι x ∈ alternatingGroup (Fin n) :=
      Equiv.Perm.mem_alternatingGroup.mpr hsign
    obtain ⟨l, hl⟩ := e.surjective ⟨ι x, hmemA⟩
    have hlx : (l : X) = x := by
      apply hιinj
      rw [hι l, hl]
    rw [← hlx]
    exact l.2
  · intro l hl
    have h3 : ∀ c : Equiv.Perm (Fin n), c.IsThreeCycle →
        c ∈ (oPPrimeHull 3 (⊤ : Subgroup X)).map ι := by
      intro c hc
      let l : ↥L := e.symm ⟨c, hc.mem_alternatingGroup⟩
      have hlc : e l = ⟨c, hc.mem_alternatingGroup⟩ := e.apply_symm_apply _
      have hordl : orderOf l = 3 := by
        have h1 : orderOf (e l) = 3 := by
          rw [hlc, ← Subgroup.orderOf_coe (⟨c, hc.mem_alternatingGroup⟩)]
          exact hc.orderOf
        rw [← orderOf_injective e.toMonoidHom e.injective l]
        exact h1
      refine Subgroup.mem_map.mpr ⟨(l : X), ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨trivial, 1, by simpa using hordl⟩
      · rw [hι l, hlc]
    have hA : alternatingGroup (Fin n) ≤
        (oPPrimeHull 3 (⊤ : Subgroup X)).map ι := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
      exact (Subgroup.closure_le _).mpr h3
    have hmem := hA (e ⟨l, hl⟩).2
    obtain ⟨y, hy, hyl⟩ := Subgroup.mem_map.mp hmem
    have : y = l := hιinj (hyl.trans ((hι ⟨l, hl⟩).symm))
    rwa [← this]

end Alternating

section Surjective

open CFSG.ComponentClassification.CatalogueBPrimeJoin

private theorem oPPrimeHull_top_eq_primeResidual {A : Type*} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] : oPPrimeHull p (⊤ : Subgroup A) = primeResidual p A := by
  rw [primeResidual_eq_closure p, oPPrimeHull]
  congr 1
  ext x
  simp

variable {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}

theorem map_oPPrimeHull_top_of_surjective (hp : p.Prime) (φ : A →* B)
    (hφ : Function.Surjective φ) :
    (oPPrimeHull p (⊤ : Subgroup A)).map φ =
      oPPrimeHull p (⊤ : Subgroup B) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite B := Finite.of_surjective φ hφ
  rw [oPPrimeHull_top_eq_primeResidual (A := A),
    oPPrimeHull_top_eq_primeResidual (A := B)]
  exact primeResidual_map_surjective p φ hφ

end Surjective

section ThreeStar

variable {G : Type} [Group G] [Finite G]

private theorem nonempty_quot_oPPrimeHull_pPrimeCore (M : Subgroup G) :
    Nonempty (↥(oPPrimeHull 3 (⊤ : Subgroup ↥M)) ⧸
        CFSG.pPrimeCore 3 ↥(oPPrimeHull 3 (⊤ : Subgroup ↥M)) ≃*
      ↥(oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let N : Subgroup ↥M := oPPrimeHull 3 (⊤ : Subgroup ↥M)
  let O : Subgroup (↥M ⧸ C) := oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ C))
  haveI hCnorm : C.Normal := CFSG.pPrimeCore_normal
  haveI hNnorm : N.Normal := oPPrimeHull_top_normal 3
  let π : ↥M →* ↥M ⧸ C := QuotientGroup.mk' C
  have hO : N.map π = O :=
    map_oPPrimeHull_top_of_surjective Nat.prime_three π (QuotientGroup.mk'_surjective C)
  let f : ↥N →* ↥M ⧸ C := π.comp N.subtype
  let g : ↥N →* ↥O := f.codRestrict O (fun x => by
    rw [← hO]
    exact Subgroup.mem_map_of_mem π x.2)
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : ↥M ⧸ C) ∈ N.map π := by rw [hO]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker_g : g.ker = CFSG.pPrimeCore 3 ↥N := by
    have hgf : g.ker = f.ker := by
      ext x
      simp [g, f, MonoidHom.mem_ker]
    rw [hgf]
    ext x
    constructor
    · intro hx
      have hxC : (x : ↥M) ∈ C := by
        have h1 : QuotientGroup.mk' C (x : ↥M) = 1 := MonoidHom.mem_ker.mp hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hxmap : (x : ↥M) ∈ (CFSG.pPrimeCore 3 ↥N).map N.subtype := by
        rw [CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 3) hNnorm]
        exact Subgroup.mem_inf.mpr ⟨x.2, hxC⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      have hxmap : (x : ↥M) ∈ (CFSG.pPrimeCore 3 ↥N).map N.subtype :=
        Subgroup.mem_map_of_mem N.subtype hx
      rw [CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 3) hNnorm] at hxmap
      have h1 : QuotientGroup.mk' C (x : ↥M) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hxmap.2
      show f x = 1
      exact h1
  let eKer : ↥N ⧸ CFSG.pPrimeCore 3 ↥N ≃* ↥N ⧸ g.ker :=
    QuotientGroup.quotientMulEquivOfEq hker_g.symm
  exact ⟨eKer.trans (QuotientGroup.quotientKerEquivOfSurjective g hgsurj)⟩

theorem nonempty_threeStar_oPPrimeHull_mulEquiv (M : Subgroup G) :
    Nonempty (threeStar (oPPrimeHull 3 M) ≃*
      ↥(oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M)))) := by
  classical
  let J : Subgroup G := oPPrimeHull 3 M
  let N : Subgroup ↥M := oPPrimeHull 3 (⊤ : Subgroup ↥M)
  haveI hNnorm : N.Normal := oPPrimeHull_top_normal 3
  have hNmap : N.map M.subtype = J := map_subtype_oPPrimeHull_top M 3
  let eNJ : ↥N ≃* ↥J :=
    (Subgroup.equivMapOfInjective N M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hNmap)
  let eCongr : (↥N ⧸ CFSG.pPrimeCore 3 ↥N) ≃* (↥J ⧸ CFSG.pPrimeCore 3 ↥J) :=
    QuotientGroup.congr _ _ eNJ (CFSG.pPrimeCore_map_iso 3 eNJ)
  obtain ⟨eQuot⟩ := nonempty_quot_oPPrimeHull_pPrimeCore M
  exact ⟨eCongr.symm.trans eQuot⟩

end ThreeStar

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

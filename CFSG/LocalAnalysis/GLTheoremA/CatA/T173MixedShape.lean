module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrbit

import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LieType.SeitzGeneration.OrthBlocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open scoped IsMulCommutative

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {A : Subgroup ↥(orthDerived Q)}

structure IsAdaptedSystem (Q : QuadraticForm F V) (A : Subgroup ↥(orthDerived Q)) {l : ℕ}
    (U : Fin l → Submodule F V) : Prop extends IsPlaneSystem Q U where
  iSup_eq_top : ⨆ k, U k = ⊤
  maps_to : ∀ a ∈ A, ∀ k, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x ∈ U k
  gen : ∀ k, (∀ a ∈ A, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = x) ∨
    ∃ g ∈ A, (∀ x ∈ U k, (g : V ≃ₗ[F] V) x = x → x = 0) ∧
      ∀ a ∈ A, ∃ m : ℕ, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = ((g : V ≃ₗ[F] V) ^ m) x

private theorem exists_adaptedSystem_aux1 {r : ℕ} {U' : Fin r → Submodule F V} {P : Submodule F V}
    (h2 : Module.finrank F P = 2)
    (hnd : (QuadraticMap.polarBilin (Q.comp P.subtype)).Nondegenerate)
    (hm : ¬ IsPlusType (Q.comp P.subtype))
    (horth : ∀ j, ∀ x ∈ P, ∀ y ∈ U' j, polar Q x y = 0)
    (hU'sys : IsPlaneSystem Q U') :
    IsPlaneSystem Q (Fin.cons P U' : Fin (r + 1) → Submodule F V) :=
  { finrank_eq := fun j => by
      induction j using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact h2
      | succ i => rw [Fin.cons_succ]; exact hU'sys.finrank_eq i
    nondeg := fun j => by
      induction j using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact hnd
      | succ i => rw [Fin.cons_succ]; exact hU'sys.nondeg i
    not_isPlusType := fun j => by
      induction j using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact hm
      | succ i => rw [Fin.cons_succ]; exact hU'sys.not_isPlusType i
    perp := fun i j hij x hx y hy => by
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ l' =>
          simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
          exact horth l' x hx y hy
      | succ k =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
          exact (QuadraticMap.polar_comm Q x y).trans (horth k y hy x hx)
        | succ l' =>
          simp only [Fin.cons_succ] at hx hy
          exact hU'sys.perp k l' (fun h => hij (by rw [h])) x hx y hy }

private theorem exists_adaptedSystem_aux2 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r : ℕ}
    (hr : 1 ≤ r) (hdim : Module.finrank F V = 2 * (r + 1))
    {U' : Fin r → Submodule F V} (hU' : IsPlaneDecomp Q A ⊤ U') :
    IsPlusType Q ↔ (Even r ↔ IsPlusType (Q.comp (polarPerp Q (⨆ j, U' j)).subtype)) := by
  set W : Submodule F V := ⨆ j, U' j with hWdef
  set P : Submodule F V := polarPerp Q W with hPdef
  have hFs : (⨆ j, U' j) = (⨆ j ∈ (Finset.univ : Finset (Fin r)), U' j) := by simp
  have hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate := by
    rw [hWdef, hFs]
    exact hU'.toIsPlaneSystem.nondeg_biSup (Finset.univ : Finset (Fin r))
  have hWtype : IsPlusType (Q.comp W.subtype) ↔ Even r := by
    rw [hWdef, hFs]
    simpa using hU'.toIsPlaneSystem.isPlusType_biSup_iff (Finset.univ : Finset (Fin r))
  have hWdim : Module.finrank F W = 2 * r := by
    rw [hWdef, hFs]
    simpa using hU'.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin r))
  have hP2 : Module.finrank F P = 2 := by
    rw [hPdef, finrank_polarPerp hQ W, hWdim, hdim]; omega
  have hPnd : (QuadraticMap.polarBilin (Q.comp P.subtype)).Nondegenerate := by
    rw [hPdef]; exact nondeg_comp_polarPerp hQ hWnd
  have hcompl : IsCompl W P := by
    have h := hU'.toIsPlaneSystem.isCompl_iSup
    rwa [← hWdef, ← hPdef] at h
  have horth : ∀ a ∈ W, ∀ b ∈ P, polar Q a b = 0 := by
    intro a ha b hb
    rw [hPdef] at hb
    exact (mem_polarPerp_iff.1 hb) a ha
  have hiso := CFSG.RankThree.PartOne.K159.isometryEquivSup Q W P hcompl.disjoint horth
  have htop' : IsPlusType (Q.comp (W ⊔ P).subtype) ↔ IsPlusType Q := by
    rw [hcompl.sup_eq_top]; exact isPlusType_comp_top_iff
  have hprod : IsPlusType ((Q.comp W.subtype).prod (Q.comp P.subtype)) ↔
      (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp P.subtype)) :=
    CFSG.RankThree.PartOne.K159.isPlusType_prod_iff hWnd hPnd (d₁ := r) (d₂ := 1)
      (by omega) le_rfl hWdim (by rw [hP2])
  calc IsPlusType Q ↔ IsPlusType ((Q.comp W.subtype).prod (Q.comp P.subtype)) :=
        htop'.symm.trans (isPlusType_congr hiso)
    _ ↔ (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp P.subtype)) := hprod
    _ ↔ (Even r ↔ IsPlusType (Q.comp P.subtype)) := by rw [hWtype]

private theorem exists_adaptedSystem_aux3 {r : ℕ} {P : Submodule F V}
    (htype : IsPlusType Q ↔ Even (r + 1))
    (hiff : IsPlusType Q ↔ (Even r ↔ IsPlusType (Q.comp P.subtype))) :
    ¬ IsPlusType (Q.comp P.subtype) := by
  rintro hPplus
  have hQEr : IsPlusType Q ↔ Even r := by rw [hiff]; simp [hPplus]
  have hEr : Even (r + 1) ↔ Even r := htype.symm.trans hQEr
  have hodd : Even (r + 1) ↔ ¬ Even r := Nat.even_add_one (n := r)
  have hcontra : Even r ↔ ¬ Even r := hEr.symm.trans hodd
  by_cases he : Even r
  · exact (hcontra.mp he) he
  · exact he (hcontra.mpr he)

private theorem exists_adaptedSystem_aux4 {r : ℕ} {U' : Fin r → Submodule F V} {P : Submodule F V}
    (hPsys : IsPlaneSystem Q (Fin.cons P U' : Fin (r + 1) → Submodule F V))
    (hU' : IsPlaneDecomp Q A ⊤ U') (hdim : Module.finrank F V = 2 * (r + 1))
    (htriv : ∀ a ∈ A, ∀ x ∈ P, (a : V ≃ₗ[F] V) x = x) :
    ∃ U : Fin (r + 1) → Submodule F V, IsAdaptedSystem Q A U := by
  have htop : (⨆ j, (Fin.cons P U' : Fin (r + 1) → Submodule F V) j) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [show (⨆ j, (Fin.cons P U' : Fin (r + 1) → Submodule F V) j) =
        (⨆ j ∈ (Finset.univ : Finset (Fin (r + 1))),
          (Fin.cons P U' : Fin (r + 1) → Submodule F V) j) by simp,
      hPsys.finrank_biSup Finset.univ, Finset.card_univ, Fintype.card_fin, hdim]
  refine ⟨Fin.cons P U', ?_⟩
  refine
    { toIsPlaneSystem := hPsys
      iSup_eq_top := htop
      maps_to := ?_
      gen := ?_ }
  · intro a ha k x hx
    induction k using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero] at hx ⊢
      rw [htriv a ha x hx]
      exact hx
    | succ i =>
      simp only [Fin.cons_succ] at hx ⊢
      exact hU'.maps_to a ha i x hx
  · intro k
    induction k using Fin.cases with
    | zero => left; simpa using htriv
    | succ i => right; simpa using hU'.exists_gen i

private theorem exists_adaptedSystem_aux5 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r : ℕ}
    (hr : 1 ≤ r) (hdim : Module.finrank F V = 2 * (r + 1))
    (htype : IsPlusType Q ↔ Even (r + 1))
    {U' : Fin r → Submodule F V} (hU' : IsPlaneDecomp Q A ⊤ U') :
    ∃ U : Fin (r + 1) → Submodule F V, IsAdaptedSystem Q A U := by
  have hPm := exists_adaptedSystem_aux3 htype (exists_adaptedSystem_aux2 hQ hr hdim hU')
  have hFsu : (⨆ j, U' j) = (⨆ j ∈ (Finset.univ : Finset (Fin r)), U' j) := by simp
  have hPnd : (QuadraticMap.polarBilin (Q.comp (polarPerp Q (⨆ j, U' j)).subtype)).Nondegenerate :=
    nondeg_comp_polarPerp hQ (by
      rw [hFsu]
      exact hU'.toIsPlaneSystem.nondeg_biSup (Finset.univ : Finset (Fin r)))
  have hP2 : Module.finrank F (polarPerp Q (⨆ j, U' j)) = 2 := by
    have hWdim : Module.finrank F ↥(⨆ j, U' j) = 2 * r := by
      rw [hFsu]
      simpa using hU'.toIsPlaneSystem.finrank_biSup (Finset.univ : Finset (Fin r))
    rw [finrank_polarPerp hQ (⨆ j, U' j), hWdim, hdim]; omega
  have horth : ∀ j, ∀ x ∈ polarPerp Q (⨆ j, U' j), ∀ y ∈ U' j, polar Q x y = 0 := by
    intro j x hx y hy
    rw [QuadraticMap.polar_comm]
    exact (mem_polarPerp_iff.1 hx) y (le_iSup U' j hy)
  have hPsys := exists_adaptedSystem_aux1 (P := polarPerp Q (⨆ j, U' j))
    hP2 hPnd hPm horth hU'.toIsPlaneSystem
  have htriv : ∀ a ∈ A, ∀ x ∈ polarPerp Q (⨆ j, U' j), (a : V ≃ₗ[F] V) x = x := by
    intro a ha x hx
    exact hU'.apply_of_perp a ha x Submodule.mem_top hx
  exact exists_adaptedSystem_aux4 (P := polarPerp Q (⨆ j, U' j)) hPsys hU' hdim htriv

theorem exists_adaptedSystem (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (htype : IsPlusType Q ↔ Even l) (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ (l - 1)) :
    ∃ U : Fin l → Submodule F V, IsAdaptedSystem Q A U := by
  have hreg : CFSG.RankThree.PartOne.K159.RegOn Q ⊤ := fun u _ h =>
    hQ.1 u fun w => by
      simpa [QuadraticMap.polarBilin_apply_apply] using h w Submodule.mem_top
  obtain ⟨r, U', hU'⟩ :=
    exists_planeDecomp hQ hp hp2 hpq hA ⊤ hreg fun _ _ _ _ => Submodule.mem_top
  have hle : p ^ (l - 1) ≤ p ^ r := hcard ▸ hU'.card_le_pow hA hp
  have hl1 : l - 1 ≤ r := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
  have hrn : r ≤ l := by
    have h1 := hU'.toIsPlaneSystem.finrank_biSup Finset.univ
    have h2 := Submodule.finrank_le (⨆ j ∈ (Finset.univ : Finset (Fin r)), U' j)
    rw [h1, Finset.card_univ, Fintype.card_fin, hdim] at h2
    omega
  by_cases hrl : r = l
  · subst r
    refine ⟨U', ?_⟩
    refine
      { toIsPlaneSystem := hU'.toIsPlaneSystem
        iSup_eq_top := ?_
        maps_to := hU'.maps_to
        gen := fun j => Or.inr (hU'.exists_gen j) }
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [show (⨆ j, U' j) = (⨆ j ∈ (Finset.univ : Finset (Fin l)), U' j) by simp,
      hU'.toIsPlaneSystem.finrank_biSup Finset.univ, Finset.card_univ, Fintype.card_fin, hdim]
  · have hrlt : r < l := lt_of_le_of_ne hrn hrl
    have hlr : l = r + 1 := by omega
    subst l
    exact exists_adaptedSystem_aux5 hQ (by omega) hdim htype hU'

private theorem exists_rotation_extending_aux1 {P : Submodule F V}
    (hS : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P) {a : V ≃ₗ[F] V}
    (hO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h1 : ∀ s ∈ P, a s ∈ P) (h2 : ∀ s ∈ P, a.symm s ∈ P) :
    CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1
    ((CFSG.LieType.SeitzGeneration.OrthBlk.isCompl_perp hS).sup_eq_top ▸
      Submodule.mem_top (x := v))
  rw [show CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 (u + r) = a u + r by
      simpa using CFSG.LieType.SeitzGeneration.OrthBlk.extendId_apply hS h1 h2 hu hr,
    QuadraticMap.map_add Q (a u) r, QuadraticMap.map_add Q u r,
    CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hr (a u) (h1 u hu),
    CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp.mp hr u hu,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hO u]

theorem exists_rotation_extending (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) {P : Submodule F V} (hP : IsCompl P (polarPerp Q P))
    {g : ↥(orthDerived Q)} (hgP : ∀ x ∈ P, (g : V ≃ₗ[F] V) x ∈ P) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) :
    ∃ r : ↥(orthDerived Q), (∀ x ∈ P, (r : V ≃ₗ[F] V) x = (g : V ≃ₗ[F] V) x) ∧
      ∀ x ∈ polarPerp Q P, (r : V ≃ₗ[F] V) x = x := by
  classical
  have hS : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P := fun x hx hperp => by
    have hxperp : x ∈ polarPerp Q P := mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]; exact hperp y hy
    have hxbot : x ∈ P ⊓ polarPerp Q P := ⟨hx, hxperp⟩
    rwa [hP.inf_eq_bot, Submodule.mem_bot] at hxbot
  set a : V ≃ₗ[F] V := (g : V ≃ₗ[F] V) with ha
  have hgn' : a ^ n = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hgn
    simpa [ha] using h
  have h1 : ∀ s ∈ P, a s ∈ P := hgP
  have h2 : ∀ s ∈ P, a.symm s ∈ P := by
    have hn0 : 0 < n := by obtain ⟨k, rfl⟩ := hn; omega
    have hmul : a * a ^ (n - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hn0, hgn']
    have hinv : a.symm = a ^ (n - 1) := inv_eq_of_mul_eq_one_right hmul
    intro s hs
    rw [hinv]
    exact CFSG.LieType.SeitzGeneration.OrthBlk.pow_apply_mem h1 (n - 1) s hs
  have hrO : CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    exists_rotation_extending_aux1 hS (ha ▸ CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup g.2) h1 h2
  have hrpow : CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 ^ n = 1 := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1
      (hP.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.extendId_pow hS h1 h2 hu hr n, hgn']
    rfl
  have hrΩ : CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 ∈ orthDerived Q :=
    CFSG.RankThree.PartOne.mem_orthDerived_of_pow_eq_one hQ
      (CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hl hdim) hn hrO hrpow
  refine ⟨⟨CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2, hrΩ⟩, ?_, ?_⟩
  · intro x hx
    show CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 x = (g : V ≃ₗ[F] V) x
    rw [← ha]
    simpa using CFSG.LieType.SeitzGeneration.OrthBlk.extendId_apply hS h1 h2 hx
      (zero_mem (polarPerp Q P))
  · intro x hx
    show CFSG.LieType.SeitzGeneration.OrthBlk.extendId hS a h1 h2 x = x
    simpa using CFSG.LieType.SeitzGeneration.OrthBlk.extendId_apply hS h1 h2 (zero_mem P) hx

private theorem exists_torusFrame_aux1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hA : IsElemAbelian p A) (hU : IsAdaptedSystem Q A U) (k : Fin l) :
    ∃ r : ↥(orthDerived Q), orderOf r = p ∧ (∀ x ∈ U k, (r : V ≃ₗ[F] V) x ∈ U k) ∧
      (∀ x ∈ U k, (r : V ≃ₗ[F] V) x = x → x = 0) ∧
      (∀ x ∈ polarPerp Q (U k), (r : V ≃ₗ[F] V) x = x) ∧
      ∀ a ∈ A, ∃ m : ℕ, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = ((r : V ≃ₗ[F] V) ^ m) x := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases hU.gen k with htriv | ⟨g, hgA, hgfree, hgpow⟩
  · obtain ⟨r, hord, hmap, hfree, hperp⟩ :=
      exists_rotation_of_mem_plane hQ hdim hl hp hp2 hpq hU.toIsPlaneSystem k
    exact ⟨r, hord, hmap, hfree, hperp, fun a ha => ⟨0, fun x hx => by rw [htriv a ha x hx]; rfl⟩⟩
  · have hgp : g ^ p = 1 := hA.2 g hgA
    have hP : IsCompl (U k) (polarPerp Q (U k)) := isCompl_polarPerp (hU.nondeg k)
    obtain ⟨r, hragree, hrfix⟩ :=
      exists_rotation_extending hQ hdim hl hP (hU.maps_to g hgA k) hpodd hgp
    have hgcoe_p : (g : V ≃ₗ[F] V) ^ p = 1 := by
      have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hgp
      simpa using h
    have hrp : (r : V ≃ₗ[F] V) ^ p = 1 := by
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hP.sup_eq_top ▸ Submodule.mem_top (x := v))
      rw [map_add, pow_apply_eq_of_apply_eq (hU.maps_to g hgA k) hragree p u hu, hgcoe_p,
        pow_apply_eq_self (hrfix w hw) p]
      simp
    have hr1 : r ≠ 1 := by
      intro h1
      obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U k) (hU.finrank_eq k)
      exact hx0 (hgfree x hx (by rw [← hragree x hx, h1]; rfl))
    haveI : Fact p.Prime := ⟨hp⟩
    refine ⟨r, ?_, ?_, ?_, hrfix, ?_⟩
    · rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hrp (fun h => hr1 (Subtype.ext h))
    · intro x hx; rw [hragree x hx]; exact hU.maps_to g hgA k x hx
    · intro x hx hfix
      exact hgfree x hx (by rw [← hragree x hx]; exact hfix)
    · intro a ha
      obtain ⟨m, hm⟩ := hgpow a ha
      exact ⟨m, fun x hx => by
        rw [hm x hx]
        exact (pow_apply_eq_of_apply_eq (hU.maps_to g hgA k) hragree m x hx).symm⟩

private theorem exists_torusFrame_aux2 {m : ℕ} {U : Fin m → Submodule F V} {σ : Fin m → V ≃ₗ[F] V}
    (comm : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).Pairwise (Function.onFun Commute σ))
    (hfix : ∀ i j, i ≠ j → ∀ x ∈ U j, σ i x = x)
    (hmap : ∀ j, ∀ x ∈ U j, σ j x ∈ U j) (j : Fin m) {x : V} (hx : x ∈ U j) :
    (Finset.univ.noncommProd σ comm) x = σ j x := by
  have hcomm' : ((Finset.univ.erase j : Finset (Fin m)) : Set (Fin m)).Pairwise
      (Function.onFun Commute σ) :=
    fun _ hx _ hy hxy => comm (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
  rw [← Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ j) σ comm hcomm',
    LinearEquiv.mul_apply]
  have herase : ∀ y ∈ U j, (Finset.univ.erase j).noncommProd σ hcomm' y = y := by
    intro y hy
    refine Finset.noncommProd_induction (Finset.univ.erase j) σ hcomm' (fun g => g y = y)
      (fun a b ha hb => by rw [LinearEquiv.mul_apply, hb, ha]) rfl (fun i hi => ?_)
    exact hfix i j (Finset.mem_erase.mp hi).1 y hy
  exact herase (σ j x) (hmap j x hx)

private theorem exists_torusFrame_aux3 (hU : IsAdaptedSystem Q A U)
    {e : Fin l → ↥(orthDerived Q)} (hcomm : ∀ i j, Commute (e i : V ≃ₗ[F] V) (e j : V ≃ₗ[F] V))
    (hmap : ∀ k, ∀ x ∈ U k, (e k : V ≃ₗ[F] V) x ∈ U k)
    (hperp : ∀ k, ∀ x ∈ polarPerp Q (U k), (e k : V ≃ₗ[F] V) x = x)
    (hpow : ∀ a ∈ A, ∀ k, ∃ m : ℕ, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = ((e k : V ≃ₗ[F] V) ^ m) x) :
    A ≤ Subgroup.closure (Set.range e) := by
  intro a ha
  choose m hm using fun k => hpow a ha k
  set σ : Fin l → V ≃ₗ[F] V := fun k => (e k : V ≃ₗ[F] V) ^ (m k) with hσ
  have hσcomm : ∀ i j, Commute (σ i) (σ j) := fun i j => (hcomm i j).pow_pow (m i) (m j)
  have hcommσ : ((Finset.univ : Finset (Fin l)) : Set (Fin l)).Pairwise (Function.onFun Commute σ) := by
    rw [Finset.coe_univ]; exact Set.pairwise_univ.2 (fun i j _ => hσcomm i j)
  have hfixσ : ∀ i j, i ≠ j → ∀ x ∈ U j, σ i x = x := by
    intro i j hij x hx
    have hxperp : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun z hz => hU.perp i j hij z hz x hx
    exact pow_apply_eq_self (hperp i x hxperp) (m i)
  have hmapσ : ∀ j, ∀ x ∈ U j, σ j x ∈ U j := fun j x hx =>
    CFSG.LieType.SeitzGeneration.OrthBlk.pow_apply_mem (hmap j) (m j) x hx
  let bV : V ≃ₗ[F] V := Finset.univ.noncommProd σ hcommσ
  have hbVΩ : bV ∈ orthDerived Q :=
    Subgroup.noncommProd_mem (orthDerived Q) hcommσ (fun k _ => pow_mem (e k).2 (m k))
  let b : ↥(orthDerived Q) := ⟨bV, hbVΩ⟩
  have hbVeq : (b : V ≃ₗ[F] V) = bV := rfl
  have hab : a = b := by
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have hx : x ∈ ⨆ k, U k := by rw [hU.iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction U (motive := fun y => (a : V ≃ₗ[F] V) y = (b : V ≃ₗ[F] V) y)
      hx ?_ ?_ ?_
    · intro k y hy
      rw [hbVeq, hm k y hy]
      exact (exists_torusFrame_aux2 hcommσ hfixσ hmapσ k hy).symm
    · rw [map_zero, map_zero]
    · intro y z hy hz; rw [map_add, map_add, hy, hz]
  have hbT : b ∈ Subgroup.closure (Set.range e) := by
    have hbVmap : bV ∈ (Subgroup.closure (Set.range e)).map (orthDerived Q).subtype := by
      refine Subgroup.noncommProd_mem ((Subgroup.closure (Set.range e)).map (orthDerived Q).subtype)
        hcommσ (fun k _ => ?_)
      have hmem : e k ^ m k ∈ Subgroup.closure (Set.range e) :=
        pow_mem (Subgroup.subset_closure (show e k ∈ Set.range e from ⟨k, rfl⟩)) (m k)
      exact Subgroup.mem_map_of_mem (orthDerived Q).subtype hmem
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.1 hbVmap
    have hyb : y = b := Subtype.ext (hyeq.trans hbVeq.symm)
    rwa [hyb] at hyT
  rw [hab]; exact hbT

theorem exists_torusFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hA : IsElemAbelian p A) (hU : IsAdaptedSystem Q A U) :
    ∃ ρ : Fin l → ↥(orthDerived Q), IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)) ∧
      A ≤ Subgroup.closure (Set.range ρ) := by
  classical
  have hchoice : ∀ k : Fin l, ∃ r : ↥(orthDerived Q), orderOf r = p ∧
      (∀ x ∈ U k, (r : V ≃ₗ[F] V) x ∈ U k) ∧
      (∀ x ∈ U k, (r : V ≃ₗ[F] V) x = x → x = 0) ∧
      (∀ x ∈ polarPerp Q (U k), (r : V ≃ₗ[F] V) x = x) ∧
      ∀ a ∈ A, ∃ m : ℕ, ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = ((r : V ≃ₗ[F] V) ^ m) x :=
    fun k => exists_torusFrame_aux1 hQ hdim hl hp hp2 hpq hA hU k
  choose e he using hchoice
  have hcomm : ∀ i j : Fin l, Commute (e i : V ≃ₗ[F] V) (e j : V ≃ₗ[F] V) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · have hgU : ∀ x ∈ U i, (e j : V ≃ₗ[F] V) x = x := fun x hx =>
        (he j).2.2.2.1 x (mem_polarPerp_iff.2 fun z hz => hU.perp j i (Ne.symm hij) z hz x hx)
      have h := commute_of_apply_eq (Q := Q) (U := U i) (hU.nondeg i)
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (e j).2)
        hgU (he i).2.1 (he i).2.2.2.1
      exact (commute_iff_eq (e i : V ≃ₗ[F] V) (e j : V ≃ₗ[F] V)).2 h.symm
  have hcommS : ∀ i j : Fin l, Commute (e i) (e j) := fun i j =>
    (commute_iff_eq (e i) (e j)).2 (Subtype.ext
      ((commute_iff_eq (e i : V ≃ₗ[F] V) (e j : V ≃ₗ[F] V)).1 (hcomm i j)))
  have hframe : IsPlaneFrame Q p U e (Subgroup.closure (Set.range e)) :=
    { toIsPlaneSystem := hU.toIsPlaneSystem
      orderOf_eq := fun k => (he k).1
      apply_of_perp := fun k => (he k).2.2.2.1
      maps_to := fun k => (he k).2.1
      eq_zero_of_apply_eq := fun k => (he k).2.2.1
      isElemAbelian := CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.isElemAbelian_closure_range e hcommS
        (fun k => (he k).1 ▸ pow_orderOf_eq_one (e k))
      closure_eq := rfl }
  exact ⟨e, hframe, exists_torusFrame_aux3 hU hcomm (fun k => (he k).2.1)
    (fun k => (he k).2.2.2.1) (fun a ha k => (he k).2.2.2.2 a ha)⟩

private theorem isPlaneFrame_update_pow_aux1 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} (hc : ¬ p ∣ c) :
    Subgroup.closure (Set.range (Function.update ρ j (ρ j ^ c))) =
      Subgroup.closure (Set.range ρ) := by
  have hcop : Nat.Coprime c (orderOf (ρ j)) := by
    rw [hF.orderOf_eq j]
    exact (hp.coprime_iff_not_dvd.mpr hc).symm
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact pow_mem (Subgroup.subset_closure (show ρ j ∈ Set.range ρ from ⟨j, rfl⟩)) c
    · rw [Function.update_of_ne hk]
      exact Subgroup.subset_closure ⟨k, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j
    · rw [hk]
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := ρ j) hcop
      have hmem : (ρ j ^ c) ^ m ∈ Subgroup.closure (Set.range (Function.update ρ j (ρ j ^ c))) :=
        pow_mem (Subgroup.subset_closure (show ρ j ^ c ∈
          Set.range (Function.update ρ j (ρ j ^ c)) from ⟨j, by rw [Function.update_self]⟩)) m
      rw [hm] at hmem
      exact hmem
    · exact Subgroup.subset_closure ⟨k, by rw [Function.update_of_ne (f := ρ) hk (ρ j ^ c)]⟩

private theorem isPlaneFrame_update_pow_aux2 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} (hc : ¬ p ∣ c) :
    orderOf (ρ j ^ c) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · have hpj : (ρ j : ↥(orthDerived Q)) ^ p = 1 := hF.orderOf_eq j ▸ pow_orderOf_eq_one (ρ j)
    rw [← pow_mul, mul_comm, pow_mul, hpj, one_pow]
  · intro h1
    have hdvd : orderOf (ρ j) ∣ c := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hF.orderOf_eq j] at hdvd
    exact hc hdvd

private theorem isPlaneFrame_update_pow_aux3
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} :
    ∀ x ∈ polarPerp Q (U j), ((ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  intro x hx
  have hpow : ∀ n : ℕ, (((ρ j : V ≃ₗ[F] V) ^ n) x) = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hF.apply_of_perp j x hx]
  simpa only [Subgroup.coe_pow] using hpow c

private theorem isPlaneFrame_update_pow_aux4
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} :
    ∀ x ∈ U j, ((ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U j := by
  intro x hx
  have hpow : ∀ n : ℕ, (((ρ j : V ≃ₗ[F] V) ^ n) x) ∈ U j := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hF.maps_to j _ ih
  simpa only [Subgroup.coe_pow] using hpow c

private theorem isPlaneFrame_update_pow_aux5 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} (hc : ¬ p ∣ c) :
    ∀ x ∈ U j, ((ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x → x = 0 := by
  intro x hx hfix
  have hcop : Nat.Coprime c (orderOf (ρ j)) := by
    rw [hF.orderOf_eq j]
    exact (hp.coprime_iff_not_dvd.mpr hc).symm
  have hfixc : (((ρ j : V ≃ₗ[F] V) ^ c) x) = x := by
    simpa only [Subgroup.coe_pow] using hfix
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := ρ j) hcop
  have hm' : ((ρ j : V ≃ₗ[F] V) ^ c) ^ m = (ρ j : V ≃ₗ[F] V) := by
    simpa only [Subgroup.coe_pow] using
      congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hm
  have hpowfix : ∀ n : ℕ, ((((ρ j : V ≃ₗ[F] V) ^ c) ^ n) x) = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hfixc]
  exact hF.eq_zero_of_apply_eq j x hx (by rw [← hm']; exact hpowfix m)

theorem isPlaneFrame_update_pow (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (j : Fin l) {c : ℕ} (hc : ¬ p ∣ c) :
    IsPlaneFrame Q p U (Function.update ρ j (ρ j ^ c))
      (Subgroup.closure (Set.range (Function.update ρ j (ρ j ^ c)))) := by
  have hT := isPlaneFrame_update_pow_aux1 hp hF j hc
  have hord := isPlaneFrame_update_pow_aux2 hp hF j hc
  have hpp := isPlaneFrame_update_pow_aux3 hF j (c := c)
  have hmt := isPlaneFrame_update_pow_aux4 hF j (c := c)
  have hez := isPlaneFrame_update_pow_aux5 hp hF j hc
  refine
    { toIsPlaneSystem := hF.toIsPlaneSystem
      orderOf_eq := ?_
      apply_of_perp := ?_
      maps_to := ?_
      eq_zero_of_apply_eq := ?_
      isElemAbelian := ?_
      closure_eq := rfl }
  · intro k
    by_cases hk : k = j
    · rw [hk, Function.update_self]; exact hord
    · rw [Function.update_of_ne hk]; exact hF.orderOf_eq k
  · intro k x hx
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self]; exact hpp x hx
    · rw [Function.update_of_ne hk]; exact hF.apply_of_perp k x hx
  · intro k x hx
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self]; exact hmt x hx
    · rw [Function.update_of_ne hk]; exact hF.maps_to k x hx
  · intro k x hx hfix
    by_cases hk : k = j
    · rw [hk] at hx; rw [hk, Function.update_self] at hfix; exact hez x hx hfix
    · rw [Function.update_of_ne hk] at hfix; exact hF.eq_zero_of_apply_eq k x hx hfix
  · rw [hT]; exact hF.isElemAbelian


private theorem separated_or_pair_aux1 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    (k : Fin l) {d : ↥(orthDerived Q)} (hd : d ∈ Subgroup.closure (ρ '' {j | j ≠ k})) :
    ∀ x ∈ U k, (d : V ≃ₗ[F] V) x = x := by
  induction hd using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := hg
    intro x hx
    exact hF.apply_of_perp j x (mem_polarPerp_iff.2 fun y hy => hF.perp j k hj y hy x hx)
  | one => intro x _; rfl
  | mul a b _ _ iha ihb =>
    intro x hx
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ihb x hx, iha x hx]
  | inv a _ iha =>
    intro x hx
    rw [Subgroup.coe_inv]
    exact (LinearEquiv.symm_apply_eq _).2 (iha x hx).symm

private theorem separated_or_pair_aux2 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    (k : Fin l) : ¬ ∀ x ∈ U k, (ρ k : V ≃ₗ[F] V) x = x := by
  intro h
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U k) (hF.finrank_eq k)
  exact hv0 (hF.eq_zero_of_apply_eq k v hv (h v hv))

private theorem separated_or_pair_aux3 {k : Fin l} {a b : ↥(orthDerived Q)}
    (ha : ¬ ∀ x ∈ U k, (a : V ≃ₗ[F] V) x = x)
    (hb : ∀ x ∈ U k, (b : V ≃ₗ[F] V) x = x) :
    ¬ ∀ x ∈ U k, ((a * b : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
  intro h
  refine ha fun x hx => ?_
  have h1 := h x hx
  rwa [Subgroup.coe_mul, LinearEquiv.mul_apply, hb x hx] at h1

private theorem separated_or_pair_aux4 (hp : p.Prime) (hl : l ≠ 0)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    (hAρ : A ≤ Subgroup.closure (Set.range ρ)) (hcard : Nat.card A = p ^ (l - 1)) :
    ∃ χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p,
      ∀ t : Subgroup.closure (Set.range ρ),
        χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcomm : IsMulCommutative (Subgroup.closure (Set.range ρ)) := hF.isElemAbelian.1
  have hcardT : Nat.card (Additive (Subgroup.closure (Set.range ρ))) = p ^ l :=
    card_torus_eq hp hF
  have hcardD : Nat.card (Subgroup.toAddSubgroup (A.subgroupOf (Subgroup.closure (Set.range ρ))))
      = p ^ (l - 1) := by
    rw [show Nat.card (Subgroup.toAddSubgroup (A.subgroupOf (Subgroup.closure (Set.range ρ))))
        = Nat.card (A.subgroupOf (Subgroup.closure (Set.range ρ))) from rfl]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAρ).toEquiv, hcard]
  have hidx : (Subgroup.toAddSubgroup (A.subgroupOf (Subgroup.closure (Set.range ρ)))).index = p := by
    have h := AddSubgroup.index_mul_card
      (Subgroup.toAddSubgroup (A.subgroupOf (Subgroup.closure (Set.range ρ))))
    rw [hcardD, hcardT] at h
    have hpow : p ^ l = p * p ^ (l - 1) := by
      rcases Nat.exists_eq_succ_of_ne_zero hl with ⟨l', rfl⟩
      rw [pow_succ, mul_comm, Nat.succ_sub_one]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h
  obtain ⟨χ, hχ⟩ := exists_hom_of_index_eq_prime
    (Subgroup.toAddSubgroup (A.subgroupOf (Subgroup.closure (Set.range ρ)))) hidx
  refine ⟨χ, fun t => ?_⟩
  rw [hχ]
  simp [Subgroup.mem_subgroupOf]

private theorem separated_or_pair_aux5 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {a b : Fin l} (hab : a ≠ b) (ha : ρ a ∈ A) :
    ∃ g ∈ A, ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔
      ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x) := by
  have hna : ¬ ∀ x ∈ U a, (ρ a : V ≃ₗ[F] V) x = x := separated_or_pair_aux2 hF a
  have htb : ∀ x ∈ U b, (ρ a : V ≃ₗ[F] V) x = x :=
    separated_or_pair_aux1 hF b (Subgroup.subset_closure ⟨a, hab, rfl⟩)
  exact ⟨ρ a, ha, ⟨fun h => (hna h).elim, fun h => (h htb).elim⟩⟩

private theorem separated_or_pair_aux6 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {a b : Fin l} (hab : a ≠ b) (hb : ρ b ∈ A) :
    ∃ g ∈ A, ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔
      ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x) := by
  have hnb : ¬ ∀ x ∈ U b, (ρ b : V ≃ₗ[F] V) x = x := separated_or_pair_aux2 hF b
  have hta : ∀ x ∈ U a, (ρ b : V ≃ₗ[F] V) x = x :=
    separated_or_pair_aux1 hF a (Subgroup.subset_closure ⟨b, Ne.symm hab, rfl⟩)
  exact ⟨ρ b, hb, ⟨fun _ => hnb, fun _ => hta⟩⟩

private theorem separated_or_pair_aux7 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {a c : Fin l}
    (hc : χ (Additive.ofMul ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩) ≠ 0)
    {u : ℕ}
    (hu : (u : ZMod p) = χ (Additive.ofMul ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩)
      * (χ (Additive.ofMul ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩))⁻¹) :
    ρ a * (ρ c ^ u)⁻¹ ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  let ga : Subgroup.closure (Set.range ρ) := ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩
  let gc : Subgroup.closure (Set.range ρ) := ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩
  have hc' : χ (Additive.ofMul gc) ≠ 0 := hc
  have hu' : (u : ZMod p) = χ (Additive.ofMul ga) * (χ (Additive.ofMul gc))⁻¹ := hu
  have hamem : ρ a ∈ Set.range ρ := ⟨a, rfl⟩
  have hcmem : ρ c ∈ Set.range ρ := ⟨c, rfl⟩
  have hgT : ρ a * (ρ c ^ u)⁻¹ ∈ Subgroup.closure (Set.range ρ) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure hamem)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure hcmem) u))
  rw [← hχ ⟨ρ a * (ρ c ^ u)⁻¹, hgT⟩]
  rw [show (⟨ρ a * (ρ c ^ u)⁻¹, hgT⟩ : Subgroup.closure (Set.range ρ)) = ga * (gc ^ u)⁻¹ from
    Subtype.ext rfl]
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, map_add, AddMonoidHom.map_nsmul, nsmul_eq_mul]
  have hneg : χ (-(u • Additive.ofMul gc)) = -χ (u • Additive.ofMul gc) := by
    have h : χ (-(u • Additive.ofMul gc)) + χ (u • Additive.ofMul gc) = 0 := by
      rw [← map_add, neg_add_cancel, map_zero]
    exact eq_neg_of_add_eq_zero_left h
  rw [hneg, AddMonoidHom.map_nsmul, nsmul_eq_mul, hu', mul_assoc, inv_mul_cancel₀ hc', mul_one]
  abel

private theorem separated_or_pair_aux8 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {a b c : Fin l} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : χ (Additive.ofMul ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩) ≠ 0)
    (hc : χ (Additive.ofMul ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩) ≠ 0) :
    ∃ g ∈ A, ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔
      ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let d : ZMod p := χ (Additive.ofMul ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩)
    * (χ (Additive.ofMul ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩))⁻¹
  let u : ℕ := d.val
  let g : ↥(orthDerived Q) := ρ a * (ρ c ^ u)⁻¹
  have hgA : g ∈ A := by
    refine separated_or_pair_aux7 hp hF hχ hc ?_
    rw [show u = d.val from rfl]
    exact ZMod.natCast_zmod_val d
  have hb_a : ρ a ∈ Subgroup.closure (ρ '' {j | j ≠ b}) :=
    Subgroup.subset_closure ⟨a, hab, rfl⟩
  have hb_c : ρ c ∈ Subgroup.closure (ρ '' {j | j ≠ b}) :=
    Subgroup.subset_closure ⟨c, hcb, rfl⟩
  have htb : ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x :=
    separated_or_pair_aux1 hF b
      (Subgroup.mul_mem _ hb_a (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb_c u)))
  have ha_c : ρ c ∈ Subgroup.closure (ρ '' {j | j ≠ a}) :=
    Subgroup.subset_closure ⟨c, hca, rfl⟩
  have hna : ¬ ∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x := by
    have h1 : ¬ ∀ x ∈ U a, (ρ a : V ≃ₗ[F] V) x = x := separated_or_pair_aux2 hF a
    have h2 : ∀ x ∈ U a, (((ρ c ^ u)⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x :=
      separated_or_pair_aux1 hF a (Subgroup.inv_mem _ (Subgroup.pow_mem _ ha_c u))
    exact separated_or_pair_aux3 h1 h2
  exact ⟨g, hgA, ⟨fun h => (hna h).elim, fun h => (h htb).elim⟩⟩

private theorem separated_or_pair_aux9 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {i j : Fin l}
    (hj : χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩) ≠ 0)
    {c : ℕ}
    (hc : (c : ZMod p) = -(χ (Additive.ofMul ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩))
      * (χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩))⁻¹) :
    ρ i * ρ j ^ c ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  let gi : Subgroup.closure (Set.range ρ) := ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  let gj : Subgroup.closure (Set.range ρ) := ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩
  have hj' : χ (Additive.ofMul gj) ≠ 0 := hj
  have hc' : (c : ZMod p) = -(χ (Additive.ofMul gi)) * (χ (Additive.ofMul gj))⁻¹ := hc
  have hgT : ρ i * ρ j ^ c ∈ Subgroup.closure (Set.range ρ) :=
    Subgroup.mul_mem _ gi.2 (Subgroup.pow_mem _ gj.2 c)
  rw [← hχ ⟨ρ i * ρ j ^ c, hgT⟩]
  rw [show (⟨ρ i * ρ j ^ c, hgT⟩ : Subgroup.closure (Set.range ρ)) = gi * gj ^ c from
    Subtype.ext rfl]
  simp only [ofMul_mul, ofMul_pow, map_add, AddMonoidHom.map_nsmul, nsmul_eq_mul]
  rw [hc', mul_assoc, inv_mul_cancel₀ hj', mul_one]
  abel

private theorem separated_or_pair_aux10 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {i j : Fin l} (hij : i ≠ j) {c : ℕ} (hc : ¬ p ∣ c)
    (hcard : Nat.card A = p ^ (l - 1)) (hgen : ρ i * ρ j ^ c ∈ A)
    (hother : ∀ k, k ≠ i → k ≠ j → ρ k ∈ A) :
    A = Subgroup.closure (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j})) := by
  have hF' := isPlaneFrame_update_pow hp hF j hc
  have himg : Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j} =
      ρ '' {k | k ≠ i ∧ k ≠ j} := by
    refine Set.image_congr fun k hk => ?_
    exact Function.update_of_ne hk.2 _ _
  have hgen' : Function.update ρ j (ρ j ^ c) i * Function.update ρ j (ρ j ^ c) j =
      ρ i * ρ j ^ c := by
    rw [Function.update_of_ne hij, Function.update_self]
  have hcardRHS : Nat.card
      (Subgroup.closure (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j}))) = p ^ (l - 1) := by
    have h := card_closure_pair_eq hp hF' hij
    rwa [hgen', himg] at h
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [Subgroup.closure_le]
    rintro x (rfl | ⟨k, hk, rfl⟩)
    · exact hgen
    · exact hother k hk.1 hk.2
  · rw [hcardRHS, hcard]

private theorem separated_or_pair_aux11 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {i j : Fin l} (hij : i ≠ j)
    (hi : χ (Additive.ofMul ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩) ≠ 0)
    (hj : χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩) ≠ 0)
    (hother : ∀ k, k ≠ i → k ≠ j → ρ k ∈ A) (hcard : Nat.card A = p ^ (l - 1)) :
    ∃ c : ℕ, ¬ p ∣ c ∧
      A = Subgroup.closure (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j})) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let d : ZMod p := -(χ (Additive.ofMul ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩))
    * (χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩))⁻¹
  let c : ℕ := d.val
  have hdne : d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hi) (inv_ne_zero hj)
  have hc : ¬ p ∣ c := by
    intro hdiv
    have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdiv (ZMod.val_lt d)
    refine hdne ?_
    rw [← ZMod.natCast_zmod_val d, show d.val = 0 from hc0]
    simp
  have hgen : ρ i * ρ j ^ c ∈ A := by
    refine separated_or_pair_aux9 hp hF hχ hj ?_
    have hcd : (c : ZMod p) = -(χ (Additive.ofMul ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩))
        * (χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩))⁻¹ := by
      rw [show c = d.val from rfl]
      exact ZMod.natCast_zmod_val d
    exact hcd
  exact ⟨c, hc, separated_or_pair_aux10 hp hF hij hc hcard hgen hother⟩

private theorem separated_or_pair_aux12 {S : Finset (Fin l)} {a b : Fin l} (hab : a ≠ b)
    (ha : a ∈ S) (hb : b ∈ S) (h2 : S.card ≠ 2) :
    ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
  have h2le : 2 ≤ S.card := by
    have hsub : ({a, b} : Finset (Fin l)) ⊆ S := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({a, b} : Finset (Fin l)).card := by rw [Finset.card_pair hab]
      _ ≤ S.card := Finset.card_le_card hsub
  by_contra h
  have hsub : S ⊆ {a, b} := by
    intro x hx
    by_contra hx'
    rw [Finset.mem_insert, Finset.mem_singleton] at hx'
    push Not at hx'
    exact h ⟨x, hx, hx'.1, hx'.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at this
  omega

private theorem separated_or_pair_aux13 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {S : Finset (Fin l)} (hS : ∀ k, k ∈ S ↔ ρ k ∉ A) (h2 : S.card ≠ 2) :
    ∀ a b : Fin l, a ≠ b → ∃ g ∈ A,
      ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔ ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x) := by
  intro a b hab
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · obtain ⟨c, hcS, hca, hcb⟩ := separated_or_pair_aux12 hab ha hb h2
      have hcaχ : χ (Additive.ofMul ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩) ≠ 0 :=
        fun h0 => (hS a).mp ha ((hχ ⟨ρ a, Subgroup.subset_closure ⟨a, rfl⟩⟩).mp h0)
      have hccχ : χ (Additive.ofMul ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩) ≠ 0 :=
        fun h0 => (hS c).mp hcS ((hχ ⟨ρ c, Subgroup.subset_closure ⟨c, rfl⟩⟩).mp h0)
      exact separated_or_pair_aux8 hp hF hχ hab hca hcb hcaχ hccχ
    · have hbA : ρ b ∈ A := by
        by_contra h
        exact hb ((hS b).mpr h)
      exact separated_or_pair_aux6 hF hab hbA
  · have haA : ρ a ∈ A := by
      by_contra h
      exact ha ((hS a).mpr h)
    exact separated_or_pair_aux5 hF hab haA

private theorem separated_or_pair_aux14 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {χ : Additive (Subgroup.closure (Set.range ρ)) →+ ZMod p}
    (hχ : ∀ t : Subgroup.closure (Set.range ρ),
      χ (Additive.ofMul t) = 0 ↔ (t : ↥(orthDerived Q)) ∈ A)
    {S : Finset (Fin l)} (hS : ∀ k, k ∈ S ↔ ρ k ∉ A) (h2 : S.card = 2)
    (hcard : Nat.card A = p ^ (l - 1)) :
    ∃ (i j : Fin l) (c : ℕ), i ≠ j ∧ ¬ p ∣ c ∧
      A = Subgroup.closure (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j})) := by
  obtain ⟨i, j, hij, hSij⟩ := Finset.card_eq_two.mp h2
  have hiA : ρ i ∉ A := by
    have : i ∈ S := by rw [hSij]; exact Finset.mem_insert_self i {j}
    exact (hS i).mp this
  have hjA : ρ j ∉ A := by
    have : j ∈ S := by rw [hSij]; simp
    exact (hS j).mp this
  have hi : χ (Additive.ofMul ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩) ≠ 0 := fun h0 =>
    hiA ((hχ ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩⟩).mp h0)
  have hj : χ (Additive.ofMul ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩) ≠ 0 := fun h0 =>
    hjA ((hχ ⟨ρ j, Subgroup.subset_closure ⟨j, rfl⟩⟩).mp h0)
  have hother : ∀ k, k ≠ i → k ≠ j → ρ k ∈ A := by
    intro k hki hkj
    by_contra hkA
    have hkS : k ∈ S := (hS k).mpr hkA
    rw [hSij, Finset.mem_insert, Finset.mem_singleton] at hkS
    rcases hkS with h | h
    · exact hki h
    · exact hkj h
  obtain ⟨c, hc, heq⟩ := separated_or_pair_aux11 hp hF hχ hij hi hj hother hcard
  exact ⟨i, j, c, hij, hc, heq⟩

theorem separated_or_pair (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (hAρ : A ≤ Subgroup.closure (Set.range ρ))
    (hcard : Nat.card A = p ^ (l - 1)) :
    (∀ a b : Fin l, a ≠ b → ∃ g ∈ A,
      ((∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x) ↔ ¬ ∀ x ∈ U b, (g : V ≃ₗ[F] V) x = x)) ∨
    ∃ (i j : Fin l) (c : ℕ), i ≠ j ∧ ¬ p ∣ c ∧
      A = Subgroup.closure (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j})) := by
  classical
  by_cases hl0 : l = 0
  · left
    intro a
    exact Fin.elim0 (hl0 ▸ a)
  · obtain ⟨χ, hχ⟩ := separated_or_pair_aux4 hp hl0 hF hAρ hcard
    set S : Finset (Fin l) := Finset.univ.filter (fun k => ρ k ∉ A) with hS
    have hS_mem : ∀ k, k ∈ S ↔ ρ k ∉ A := by intro k; rw [hS]; simp
    by_cases h2 : S.card = 2
    · right
      exact separated_or_pair_aux14 hp hF hχ hS_mem h2 hcard
    · left
      exact separated_or_pair_aux13 hp hF hχ hS_mem h2

private theorem le_sup_of_invariant_totallySingular_aux1 (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ T) {i j : Fin l}
    (hA : ∀ k, k ≠ i → k ≠ j → ρ k ∈ A) {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0)
    (hinv : ∀ a ∈ A, ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j) :
    W ≤ polarPerp Q (U k) := by
  have hpk : (ρ k : V ≃ₗ[F] V) ^ p = 1 := by
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq k ▸ pow_orderOf_eq_one (ρ k))
    simpa using h
  exact le_polarPerp_of_invariant_of_free (g := (ρ k : V ≃ₗ[F] V)) (n := p)
    (hp.odd_of_ne_two hp2) hpk
    (isCompl_polarPerp (hF.toIsPlaneSystem.nondeg k))
    (fun x hx hQx => eq_zero_of_map_eq_zero_of_mem_plane hF.toIsPlaneSystem k hx hQx)
    (hF.maps_to k) (hF.eq_zero_of_apply_eq k) (hF.apply_of_perp k)
    hTS (hinv (ρ k) (hA k hki hkj))

private theorem le_sup_of_invariant_totallySingular_aux2 {i j : Fin l} (htop : ⨆ k, U k = ⊤) :
    (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) ⊔ (U i ⊔ U j) = ⊤ := by
  let s : Finset (Fin l) := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)
  change (⨆ k ∈ s, U k) ⊔ (U i ⊔ U j) = ⊤
  refine le_antisymm le_top ?_
  rw [← htop]
  refine iSup_le fun k => ?_
  by_cases hki : k = i
  · rw [hki]; exact le_sup_of_le_right (le_sup_left : U i ≤ U i ⊔ U j)
  · by_cases hkj : k = j
    · rw [hkj]; exact le_sup_of_le_right (le_sup_right : U j ≤ U i ⊔ U j)
    · have hks : k ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hki, hkj⟩
      exact le_trans (le_iSup₂ (f := fun k (_ : k ∈ s) => U k) k hks) le_sup_left

private theorem le_sup_of_invariant_totallySingular_aux3 {i j : Fin l} {W : Submodule F V}
    (hWk : ∀ k, k ≠ i → k ≠ j → W ≤ polarPerp Q (U k)) :
    W ≤ polarPerp Q (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) := by
  have hXle : (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) ≤
      polarPerp Q W := by
    refine iSup₂_le fun k hk y hy => ?_
    have hk' : k ≠ i ∧ k ≠ j := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
    rw [mem_polarPerp_iff]
    intro w hw
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 (hWk k hk'.1 hk'.2 hw) y hy
  intro w hw
  rw [mem_polarPerp_iff]
  intro y hy
  rw [QuadraticMap.polar_comm]
  exact mem_polarPerp_iff.1 (hXle hy) w hw

private theorem le_sup_of_invariant_totallySingular_aux4 {T : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U ρ T) {i j : Fin l} :
    U i ⊔ U j ≤
      polarPerp Q (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) := by
  have hUi_perp : U i ≤ polarPerp Q
      (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) := by
    have hXi : (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) ≤
        polarPerp Q (U i) := hF.toIsPlaneSystem.biSup_le_polarPerp (a := i) (s := _) (by simp)
    intro z hz
    rw [mem_polarPerp_iff]
    intro y hy
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 (hXi hy) z hz
  have hUj_perp : U j ≤ polarPerp Q
      (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) := by
    have hXj : (⨆ k ∈ (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)), U k) ≤
        polarPerp Q (U j) := hF.toIsPlaneSystem.biSup_le_polarPerp (a := j) (s := _) (by simp)
    intro z hz
    rw [mem_polarPerp_iff]
    intro y hy
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 (hXj hy) z hz
  exact sup_le hUi_perp hUj_perp

theorem le_sup_of_invariant_totallySingular (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U ρ T) (htop : ⨆ k, U k = ⊤) {i j : Fin l}
    (hA : ∀ k, k ≠ i → k ≠ j → ρ k ∈ A) {W : Submodule F V} (hTS : ∀ x ∈ W, Q x = 0)
    (hinv : ∀ a ∈ A, ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W) : W ≤ U i ⊔ U j := by
  let s : Finset (Fin l) := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)
  have hWk : ∀ k, k ≠ i → k ≠ j → W ≤ polarPerp Q (U k) :=
    fun k hki hkj => le_sup_of_invariant_totallySingular_aux1 hp hp2 hF hA hTS hinv hki hkj
  have hsup : (⨆ k ∈ s, U k) ⊔ (U i ⊔ U j) = ⊤ :=
    le_sup_of_invariant_totallySingular_aux2 (i := i) (j := j) (U := U) htop
  have hWX : W ≤ polarPerp Q (⨆ k ∈ s, U k) :=
    le_sup_of_invariant_totallySingular_aux3 (i := i) (j := j) (U := U) hWk
  have hUiUj : U i ⊔ U j ≤ polarPerp Q (⨆ k ∈ s, U k) :=
    le_sup_of_invariant_totallySingular_aux4 (i := i) (j := j) (U := U) hF
  have hdisj : (⨆ k ∈ s, U k) ⊓ polarPerp Q (⨆ k ∈ s, U k) = ⊥ :=
    disjoint_iff.mp (isCompl_polarPerp (hF.toIsPlaneSystem.nondeg_biSup s)).disjoint
  intro w hw
  have hwtop : w ∈ (⨆ k ∈ s, U k) ⊔ (U i ⊔ U j) := by rw [hsup]; trivial
  obtain ⟨x, hxX, y, hy, hxy⟩ := Submodule.mem_sup.1 hwtop
  have hx_eq : x = w - y := by rw [← hxy]; abel
  have hx_perp : x ∈ polarPerp Q (⨆ k ∈ s, U k) := by
    rw [hx_eq]
    exact sub_mem (hWX hw) (hUiUj hy)
  have hx0 : x = 0 := by
    have hx_in : x ∈ (⨆ k ∈ s, U k) ⊓ polarPerp Q (⨆ k ∈ s, U k) := ⟨hxX, hx_perp⟩
    rw [hdisj] at hx_in
    simpa using hx_in
  rw [← hxy, hx0, zero_add]
  exact hy

theorem exists_mixedFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (htype : IsPlusType Q ↔ Even l) (hA : GLAIsBmax p A) :
    ∃ (U : Fin l → Submodule F V) (ρ : Fin l → ↥(orthDerived Q)) (i j : Fin l), IsMixedFrame Q p U ρ i j A := by
  obtain ⟨hAe, hcard, T, hT0, hT2, hAT⟩ := (glaIsBmax_iff hQ hdim hl hp hp2 hpq htype).1 hA
  obtain ⟨U, hU⟩ := exists_adaptedSystem hQ hdim hl hp hp2 hpq htype hAe hcard
  obtain ⟨ρ, hF, hAρ⟩ := exists_torusFrame hQ hdim hl hp hp2 hpq hAe hU
  obtain ⟨W, hW0, hWTS, hWinv⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T173S.exists_invariant_totallySingular_of_normalizes hQ hdim hl hT2 hT0 hAT
  rcases separated_or_pair hp hF hAρ hcard with hsep | ⟨i, j, c, hij, hc, hAeq⟩
  · exact absurd (eq_bot_of_separated hF hp hp2 hU.iSup_eq_top hAρ hsep hWTS hWinv) hW0
  · have hF' := isPlaneFrame_update_pow hp hF j hc
    have hAeq' : A = Subgroup.closure (insert (Function.update ρ j (ρ j ^ c) i * Function.update ρ j (ρ j ^ c) j)
        (Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j})) := by
      have himg : Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j} = ρ '' {k | k ≠ i ∧ k ≠ j} := by
        refine Set.image_congr fun k hk => ?_
        exact Function.update_of_ne hk.2 _ _
      rw [himg, Function.update_self, Function.update_of_ne hij]
      exact hAeq
    have hρA : ∀ k, k ≠ i → k ≠ j → Function.update ρ j (ρ j ^ c) k ∈ A := fun k hki hkj => by
      rw [hAeq']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨k, ⟨hki, hkj⟩, rfl⟩)
    have hWle := le_sup_of_invariant_totallySingular hp hp2 hF' hU.iSup_eq_top hρA hWTS hWinv
    exact ⟨U, Function.update ρ j (ρ j ^ c), i, j, hF', hU.iSup_eq_top, hij, hAeq', W, hW0, hWle, hWTS, hWinv⟩

end CFSG.LocalAnalysis.GLTheoremA.T173M

end

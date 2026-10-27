module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentAdapt
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentDecomp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I164
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.K159 CFSG.Open CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem i167COrth_adapted_plane_aux1 {U : Submodule F V}
    (h : (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate) : RegOn Q U := by
  intro u hu hpol
  refine Subtype.ext_iff.1 (h.1 ⟨u, hu⟩ fun w => ?_)
  have := hpol (w : V) w.2
  simpa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] using this

private theorem i167COrth_adapted_plane_aux2 (hp : p.Prime) {A : Subgroup ↥(orthDerived Q)}
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p) {W N : Submodule F V}
    (hW : W = fixedSpace (g : V ≃ₗ[F] V)) (hN : N = polarPerp Q W)
    (hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) :
    ∃ b ∈ A, ∃ y ∈ N, (b : V ≃ₗ[F] V) y ≠ y := by
  by_contra hcon
  push Not at hcon
  subst hW
  subst hN
  have hgN : ∀ y ∈ polarPerp Q (fixedSpace (g : V ≃ₗ[F] V)),
      (g : V ≃ₗ[F] V) y = y := fun y hy => hcon g hgA y hy
  have hg1 : (g : V ≃ₗ[F] V) = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ fixedSpace (g : V ≃ₗ[F] V) ⊔
        polarPerp Q (fixedSpace (g : V ≃ₗ[F] V)) := by
      rw [(isCompl_polarPerp hWnd).sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, n, hn, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hgN n hn, mem_fixedSpace.1 hw]
    simp
  have hgone : g = 1 := Subtype.ext hg1
  rw [hgone, orderOf_one] at hg
  exact hp.ne_one hg.symm

theorem i167COrth_adapted_plane (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {A : Subgroup ↥(orthDerived Q)}
    (hA : IsElemAbelian p A) {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p) :
    ∃ P : Submodule F V, Module.finrank F P = 2 ∧ RegOn Q P ∧ ¬ IsPlusType (Q.comp P.subtype) ∧
      (∀ b ∈ A, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P) ∧
      ∀ y ∈ P, (g : V ≃ₗ[F] V) y = y → y = 0 := by
  classical
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ g hg
  set W : Submodule F V := fixedSpace (g : V ≃ₗ[F] V) with hWdef
  have hWnd : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  set N : Submodule F V := polarPerp Q W with hNdef
  have hNnd : (QuadraticMap.polarBilin (Q.comp N.subtype)).Nondegenerate :=
    nondeg_comp_polarPerp hQ hWnd
  have hNreg : RegOn Q N := i167COrth_adapted_plane_aux1 hNnd
  have hWinv : ∀ b ∈ A, ∀ y ∈ W, (b : V ≃ₗ[F] V) y ∈ W := by
    intro b hb y hy
    rw [hWdef, mem_fixedSpace] at hy ⊢
    rw [← apply_comm_of_isElemAbelian hA hb hgA y, hy]
  have hNinv : ∀ b ∈ A, ∀ y ∈ N, (b : V ≃ₗ[F] V) y ∈ N :=
    fun b hb y hy => apply_mem_polarPerp (Bb := A) hWinv hb hy
  have hmov : ∃ b ∈ A, ∃ y ∈ N, (b : V ≃ₗ[F] V) y ≠ y :=
    i167COrth_adapted_plane_aux2 hp hgA hg hWdef hNdef hWnd
  obtain ⟨P, -, -, hPN, hP2, hPreg, hPm, hPinv, -, -⟩ :=
    exists_adapted_plane hQ hp hp2 hpq hA hNreg hNinv hmov
  refine ⟨P, hP2, hPreg, hPm, hPinv, ?_⟩
  intro y hy hyfix
  have hyW : y ∈ W := by rw [hWdef, mem_fixedSpace]; exact hyfix
  have hyN : y ∈ N := hPN hy
  have hbot : y ∈ (⊥ : Submodule F V) := by
    rw [← (isCompl_polarPerp hWnd).inf_eq_bot]
    exact ⟨hyW, hyN⟩
  exact (Submodule.mem_bot F).1 hbot

private theorem i167COrth_partial_rotation_aux1 {W : Submodule F V} {E : V ≃ₗ[F] V}
    (h1 : ∀ x ∈ W, E x ∈ W) (h2 : ∀ x ∈ W, E.symm x ∈ W) (n : ℕ) (u : W) :
    ((restrictEquiv W E h1 h2 ^ n) u : V) = (E ^ n) (u : V) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ (restrictEquiv W E h1 h2) n, LinearEquiv.mul_apply, ih, pow_succ E n,
      LinearEquiv.mul_apply]
    rfl

private theorem i167COrth_partial_rotation_aux2 {W : Submodule F V} {E : V ≃ₗ[F] V}
    (hE : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : ∀ x ∈ W, E x ∈ W)
    (h2 : ∀ x ∈ W, E.symm x ∈ W) :
    restrictEquiv W E h1 h2 ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  change Q ((restrictEquiv W E h1 h2 u : W) : V) = Q (u : V)
  rw [coe_restrictEquiv]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hE (u : V)

private theorem i167COrth_partial_rotation_aux3 {A : Subgroup ↥(orthDerived Q)}
    {g : ↥(orthDerived Q)} (hA : IsElemAbelian p A) (hgA : g ∈ A) {P : Submodule F V}
    (hP : RegOn Q P) (hPinv : ∀ b ∈ A, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P)
    (hPinv' : ∀ y ∈ P, (g : V ≃ₗ[F] V).symm y ∈ P) :
    ∃ (g' : P ≃ₗ[F] P) (hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp P.subtype)),
      (∀ r : P, (g' r : V) = (g : V ≃ₗ[F] V) (r : V)) ∧
      (extendHom (isCompl_polarPerp (nondegenerate_of_regOn hP)) ⟨g', hg'⟩) ^ p = 1 := by
  classical
  let g' : P ≃ₗ[F] P := restrictEquiv P (g : V ≃ₗ[F] V) (hPinv g hgA) hPinv'
  have hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp P.subtype) :=
    i167COrth_partial_rotation_aux2 (orthDerived_le_orthogonalGroup g.2) (hPinv g hgA) hPinv'
  have hg'def : ∀ r : P, (g' r : V) = (g : V ≃ₗ[F] V) (r : V) := fun r => by
    rw [show (g' : P ≃ₗ[F] P) =
      restrictEquiv P (g : V ≃ₗ[F] V) (hPinv g hgA) hPinv' from rfl]
    exact coe_restrictEquiv _ _ _ _ _
  have hgVp : (g : V ≃ₗ[F] V) ^ p = 1 := by
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hA.2 g hgA)
  have hg'p : g' ^ p = 1 := by
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [i167COrth_partial_rotation_aux1 (hPinv g hgA) hPinv' p u, hgVp]
    rfl
  have hsub : (⟨g', hg'⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp P.subtype))) ^ p = 1 :=
    Subtype.ext hg'p
  refine ⟨g', hg', hg'def, ?_⟩
  calc (extendHom (isCompl_polarPerp (nondegenerate_of_regOn hP)) ⟨g', hg'⟩) ^ p =
      (extendHom (isCompl_polarPerp (nondegenerate_of_regOn hP)))
        ((⟨g', hg'⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp P.subtype))) ^ p) :=
        (map_pow _ _ p).symm
    _ = 1 := by rw [hsub, map_one]

private theorem i167COrth_partial_rotation_aux4 {A : Subgroup ↥(orthDerived Q)}
    {g : ↥(orthDerived Q)} (hA : IsElemAbelian p A) (hgA : g ∈ A) {P : Submodule F V}
    (hPinv : ∀ b ∈ A, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P) {g' : P ≃ₗ[F] P}
    (hg'def : ∀ r : P, (g' r : V) = (g : V ≃ₗ[F] V) (r : V))
    (a : ↥(orthDerived Q)) (ha : a ∈ A) :
    ∀ r : P, (g' ⟨(a : V ≃ₗ[F] V) (r : V), hPinv a ha (r : V) r.2⟩ : V) =
      (a : V ≃ₗ[F] V) (g' r : V) := by
  intro r
  rw [hg'def, hg'def]
  exact (apply_comm_of_isElemAbelian hA ha hgA (r : V)).symm

theorem i167COrth_partial_rotation (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ u ∈ T, Q u = 0)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A) {g : ↥(orthDerived Q)} (hgA : g ∈ A)
    {P : Submodule F V} (hP : RegOn Q P) (hPinv : ∀ b ∈ A, ∀ y ∈ P, (b : V ≃ₗ[F] V) y ∈ P) :
    ∃ h : ↥(orthDerived Q), h ^ p = 1 ∧ (∀ y ∈ P, (h : V ≃ₗ[F] V) y = (g : V ≃ₗ[F] V) y) ∧
      (∀ w ∈ polarPerp Q P, (h : V ≃ₗ[F] V) w = w) ∧ ∀ a ∈ A, h * a = a * h := by
  classical
  have hc : IsCompl P (orthPerp Q P) :=
    isCompl_polarPerp (nondegenerate_of_regOn hP)
  have hPinv' : ∀ y ∈ P, (g : V ≃ₗ[F] V).symm y ∈ P := by
    intro y hy
    simpa using hPinv g⁻¹ (A.inv_mem hgA) y hy
  obtain ⟨g', hg', hg'def, h0pow⟩ :=
    i167COrth_partial_rotation_aux3 hA hgA hP hPinv hPinv'
  let h₀ : V ≃ₗ[F] V := extendHom hc ⟨g', hg'⟩
  have h0mem : h₀ ∈ orthDerived Q :=
    CFSG.RankThree.PartOne.mem_orthDerived_of_pow_eq_one hQ hT (hp.odd_of_ne_two hp2)
      (extendHom_mem hc ⟨g', hg'⟩) h0pow
  refine ⟨⟨h₀, h0mem⟩, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    simpa using h0pow
  · intro y hy
    simpa [h₀, hg'def] using extendHom_apply_mem hc ⟨g', hg'⟩ ⟨y, hy⟩
  · intro w hw
    exact extendHom_fix hc ⟨g', hg'⟩ hw
  · intro a ha
    refine Subtype.ext ?_
    simpa [h₀] using extendHom_commute hc (hPinv a ha)
      (fun w hw => apply_mem_polarPerp (Bb := A) hPinv ha hw) ⟨g', hg'⟩
      (i167COrth_partial_rotation_aux4 hA hgA hPinv hg'def a ha)

private theorem fixedSpace_le_polarPerp_aux1 {g : V ≃ₗ[F] V} {P : Submodule F V} (hP : RegOn Q P)
    (hgP : ∀ y ∈ P, g y ∈ P) (hgP' : ∀ y ∈ polarPerp Q P, g y ∈ polarPerp Q P)
    (hfix : ∀ y ∈ P, g y = y → y = 0) : fixedSpace g ≤ polarPerp Q P := by
  intro w hw
  have hc := isCompl_polarPerp (nondegenerate_of_regOn hP)
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := w))
  rw [mem_fixedSpace, map_add] at hw
  have h1 : g u - u ∈ P := Submodule.sub_mem _ (hgP u hu) hu
  have h2 : g u - u ∈ polarPerp Q P := by
    have : g u - u = z - g z := by
      rw [← sub_eq_zero, show g u - u - (z - g z) = g u + g z - (u + z) by abel]
      exact sub_eq_zero.2 hw
    rw [this]
    exact Submodule.sub_mem _ hz (hgP' z hz)
  have h3 : g u - u = 0 := by
    have := (disjoint_iff.1 hc.disjoint) ▸ (show g u - u ∈ P ⊓ polarPerp Q P from ⟨h1, h2⟩)
    exact (Submodule.mem_bot F).1 this
  have hu0 : u = 0 := hfix u hu (sub_eq_zero.1 h3)
  rw [hu0, zero_add]
  exact hz

private theorem commute_supportedFixedDerived_aux1 {x : V ≃ₗ[F] V} {t : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q p x) (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (htW : ∀ w ∈ fixedSpace x, t w = w) {j : V ≃ₗ[F] V} (hj : j ∈ supportedFixedDerived Q x) :
    t * j = j * t := by
  have hj' : j ∈ supportedOrthDerived Q (fixedSpace x) :=
    (CFSG.RankThree.PartOne.KCOrthogonalD4.supportedOrthDerived_fixedSpace hx).symm ▸ hj
  obtain ⟨j', -, hjW, hjP⟩ := mem_supportedOrthDerived.1 hj'
  exact commute_of_apply_eq hx.polarBilin_fixed_nondegenerate ht htW
    (fun y hy => by rw [hjW ⟨y, hy⟩]; exact (j' ⟨y, hy⟩).2) hjP

private theorem i167COrth_eq_of_mem_zpowers_aux1 {P : Submodule F V} {T : V ≃ₗ[F] V}
    (hT : ∀ y ∈ P, T y = y) (c : ℤ) : ∀ y ∈ P, (T ^ c) y = y := by
  have hTP : ∀ y ∈ P, T y ∈ P := fun y hy => by rw [hT y hy]; exact hy
  have hTinv : ∀ y ∈ P, T⁻¹ y = y := by
    intro y hy
    apply T.injective
    change T (T.symm y) = T y
    rw [T.apply_symm_apply, hT y hy]
  have hTinvP : ∀ y ∈ P, T⁻¹ y ∈ P := fun y hy => by rw [hTinv y hy]; exact hy
  intro y hy
  rcases Int.eq_nat_or_neg c with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    induction n generalizing y with
    | zero => simp
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, ih (T y) (hTP y hy), hT y hy]
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih (T⁻¹ y) (hTinvP y hy), hTinv y hy]

private theorem i167COrth_eq_of_mem_zpowers_aux2 (hp : p.Prime) {G : V ≃ₗ[F] V}
    (hGord : orderOf G = p) {P : Submodule F V} (hP : P ≠ ⊥)
    (hfix : ∀ y ∈ P, G y = y → y = 0) {k : ℤ}
    (hGkfix : ∀ y ∈ P, (G ^ k) y = y) : G ^ k = 1 := by
  by_contra hne
  have hdvd : orderOf (G ^ k) ∣ p := by
    simpa [hGord] using
      orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers G k)
  have hGkord : orderOf (G ^ k) = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf (G ^ k)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  have hle : Subgroup.zpowers (G ^ k) ≤ Subgroup.zpowers G :=
    (Subgroup.zpowers_le).2 (Subgroup.zpow_mem_zpowers G k)
  have hcard : Nat.card (Subgroup.zpowers G) ≤ Nat.card (Subgroup.zpowers (G ^ k)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hGkord, hGord]
  have heq : Subgroup.zpowers (G ^ k) = Subgroup.zpowers G :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hGmem : G ∈ Subgroup.zpowers (G ^ k) := by
    rw [heq]; exact Subgroup.mem_zpowers G
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 hGmem
  have hGfixP : ∀ y ∈ P, G y = y := by
    intro y hy
    rw [← hc]
    exact i167COrth_eq_of_mem_zpowers_aux1 hGkfix c y hy
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  exact hy0 (hfix y hyP (hGfixP y hyP))

theorem i167COrth_eq_of_mem_zpowers (hp : p.Prime) {g h : ↥(orthDerived Q)} (hg : orderOf g = p)
    {P : Submodule F V} (hP : P ≠ ⊥) (hPinv : ∀ y ∈ P, (g : V ≃ₗ[F] V) y ∈ P)
    (hfix : ∀ y ∈ P, (g : V ≃ₗ[F] V) y = y → y = 0) (hh : h ∈ Subgroup.zpowers g)
    (hhP : ∀ y ∈ P, (h : V ≃ₗ[F] V) y = (g : V ≃ₗ[F] V) y) : h = g := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  set G : V ≃ₗ[F] V := (g : V ≃ₗ[F] V) with hG
  set k : ℤ := i - 1 with hk
  have hi : i = k + 1 := by omega
  have hGord : orderOf G = p := by
    rw [hG, Subgroup.orderOf_coe, hg]
  have hstep : ∀ y ∈ P, (G ^ k) (G y) = G y := by
    intro y hy
    calc (G ^ k) (G y) = (G ^ (k + 1)) y := by
          rw [zpow_add_one G k, LinearEquiv.mul_apply]
      _ = (G ^ i) y := by rw [hi]
      _ = ((g ^ i : ↥(orthDerived Q)) : V ≃ₗ[F] V) y := by rw [Subgroup.coe_zpow]
      _ = G y := hhP y hy
  have hmap : Submodule.map (G : V →ₗ[F] V) P = P := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      exact hPinv y hy
    · rw [LinearEquiv.finrank_map_eq]
  have hGkfix : ∀ y ∈ P, (G ^ k) y = y := by
    intro z hz
    have hzmap : z ∈ Submodule.map (G : V →ₗ[F] V) P := by rw [hmap]; exact hz
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hzmap
    have hzy : z = G y := by simpa using hyz.symm
    subst hzy
    exact hstep y hy
  have hGk1 : G ^ k = 1 := i167COrth_eq_of_mem_zpowers_aux2 hp hGord hP hfix hGkfix
  have hGi : G ^ i = G := by
    rw [hi, zpow_add_one, hGk1, one_mul]
  refine Subtype.ext ?_
  simpa [hG] using hGi

theorem i167COrth_r_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {m : ℕ} (hdim : Module.finrank F V = 2 * m) (hm : 4 ≤ m)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hmax : ∀ E : Subgroup ↥(orthDerived Q), IsElemAbelian p E → A ≤ E → E = A)
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p)
    (hCA : ∀ a ∈ A, (∀ j ∈ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
      a * j = j * a) → a ∈ Subgroup.zpowers g) :
    ∃ P : Submodule F V, Module.finrank F P = 2 ∧ RegOn Q P ∧ ¬ IsPlusType (Q.comp P.subtype) ∧
      fixedSpace (g : V ≃ₗ[F] V) = polarPerp Q P := by
  classical
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hx : OddOrderIsometry Q p (g : V ≃ₗ[F] V) := oddOrderIsometry_of_orthDerived hp hpl hQ g hg
  have hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ u ∈ T, Q u = 0 := by
    by_cases hplus : IsPlusType Q
    · exact exists_threeSingular hQ hdim (Or.inl ⟨hplus, by omega⟩)
    · exact exists_threeSingular hQ hdim (Or.inr ⟨hplus, hm⟩)
  obtain ⟨P, hP2, hPreg, hPm, hPinv, hPfix⟩ := i167COrth_adapted_plane hQ hp hp2 hpq hA hgA hg
  obtain ⟨h, hhp, hhP, hhperp, hhcomm⟩ :=
    i167COrth_partial_rotation hQ hp hp2 hT hA hgA hPreg hPinv
  have hWperp : fixedSpace (g : V ≃ₗ[F] V) ≤ polarPerp Q P :=
    fixedSpace_le_polarPerp_aux1 hPreg (hPinv g hgA)
      (fun y hy => apply_mem_polarPerp hPinv hgA hy) hPfix
  have hhA : h ∈ A := by
    have hE := rk2_isElemAbelian_sup_zpowers hA hhp (fun a ha => (hhcomm a ha).symm)
    rw [← hmax _ hE le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  have hcent : ∀ j ∈ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
      h * j = j * h := fun j hj =>
    Subtype.ext (commute_supportedFixedDerived_aux1 hx (orthDerived_le_orthogonalGroup h.2)
      (fun w hw => hhperp w (hWperp hw)) (Subgroup.mem_subgroupOf.1 hj))
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    simp at hP2
  have hhg : h = g :=
    i167COrth_eq_of_mem_zpowers hp hg hP0 (hPinv g hgA) hPfix (hCA h hhA hcent) hhP
  refine ⟨P, hP2, hPreg, hPm, le_antisymm hWperp fun w hw => ?_⟩
  rw [mem_fixedSpace, ← hhg]
  exact hhperp w hw

theorem i167COrth_witt (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {m : ℕ} (hdim : Module.finrank F V = 2 * m) (hm : 4 ≤ m)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A)
    (hmax : ∀ E : Subgroup ↥(orthDerived Q), IsElemAbelian p E → A ≤ E → E = A)
    {g : ↥(orthDerived Q)} (hgA : g ∈ A) (hg : orderOf g = p)
    (hCA : ∀ a ∈ A, (∀ j ∈ (supportedFixedDerived Q (g : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
      a * j = j * a) → a ∈ Subgroup.zpowers g) :
    Module.finrank F V = Module.finrank F (fixedSpace (g : V ≃ₗ[F] V)) + 2 ∧
      (IsPlusType Q ↔ ¬ IsPlusType (Q.comp (fixedSpace (g : V ≃ₗ[F] V)).subtype)) := by
  obtain ⟨P, hP2, hPreg, hPm, hW⟩ := i167COrth_r_one hQ hp hp2 hpq hdim hm hA hmax hgA hg hCA
  have hfin : Module.finrank F (polarPerp Q P) = Module.finrank F V - Module.finrank F P :=
    finrank_polarPerp hQ P
  have hle : Module.finrank F P ≤ Module.finrank F V := Submodule.finrank_le P
  refine ⟨?_, ?_⟩
  · rw [hW, hfin]
    omega
  · rw [hW, isPlusType_comp_polarPerp_iff hQ hdim (by omega) (nondegenerate_of_regOn hPreg) hP2 hPm]
    exact not_not.symm

end CFSG.LocalAnalysis.GLTheoremA.I167

end

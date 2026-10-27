module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentPrim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {m : ℕ} {U : Fin m → Submodule F V}
  {e : Fin m → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}

private theorem IsPlaneFrame.primary_of_apply_eq_aux1 {h : F[X]} (hirr : Irreducible h)
    (hmon : h.Monic) (hne : h ≠ X - 1) : h.eval 1 ≠ 0 := by
  intro h0
  have h3 : (X - C 1 : F[X]) ∣ h := Polynomial.dvd_iff_isRoot.2 h0
  have h4 := (irreducible_X_sub_C (1 : F)).associated_of_dvd hirr h3
  exact hne (by simpa using
    (Polynomial.eq_of_monic_of_associated (monic_X_sub_C (1 : F)) hmon h4).symm)

private theorem IsPlaneFrame.primary_of_apply_eq_aux2 {W' : Submodule F V} {f g : V ≃ₗ[F] V}
    (hg : ∀ v ∈ W', g v ∈ W') (heq : ∀ v ∈ W', f v = g v) (q : F[X]) :
    ∀ v ∈ W', aeval f.toLinearMap q v = aeval g.toLinearMap q v := by
  have hgpow : ∀ n, ∀ v ∈ W', (g.toLinearMap ^ n) v ∈ W' := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ', Module.End.mul_apply]; exact hg _ (ih v hv)
  have hpow : ∀ n, ∀ v ∈ W', (f.toLinearMap ^ n) v = (g.toLinearMap ^ n) v := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
        intro v hv
        rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih v hv]
        exact heq _ (hgpow n v hv)
  intro v hv
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
      rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
        hpow n v hv]

private theorem IsPlaneFrame.primary_of_apply_eq_aux3 (hF : IsPlaneFrame Q p U e Bb) (i : Fin m)
    (k : ℕ) : ∀ v ∈ U i, ((e i : V ≃ₗ[F] V) ^ k) v ∈ U i := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih => intro v hv; rw [pow_succ', LinearEquiv.mul_apply]; exact hF.maps_to i _ (ih v hv)

private theorem IsPlaneFrame.primary_of_apply_eq_aux4 (hF : IsPlaneFrame Q p U e Bb)
    {b : ↥(orthDerived Q)} (hb : b ∈ Bb) :
    ∀ i, ∀ v ∈ U i, (b : V ≃ₗ[F] V) v ∈ U i := by
  intro i v hv
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq hb i
  rw [hk v hv]
  exact IsPlaneFrame.primary_of_apply_eq_aux3 hF i k v hv

private theorem IsPlaneFrame.primary_of_apply_eq_aux5 (hF : IsPlaneFrame Q p U e Bb) {h : F[X]}
    (hheval : h.eval 1 ≠ 0) {b : ↥(orthDerived Q)} (j : Fin m)
    (hj : U j ≤ primaryComponent (b : V ≃ₗ[F] V).toLinearMap h) : b ≠ 1 := by
  intro h1
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j) (hF.finrank_eq j)
  have hv' : aeval (b : V ≃ₗ[F] V).toLinearMap h v = 0 := mem_primaryComponent.mp (hj hv)
  have hfix : (b : V ≃ₗ[F] V).toLinearMap v = (1 : F) • v := by
    rw [show (b : V ≃ₗ[F] V).toLinearMap = 1 from
      congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V).toLinearMap) h1]
    simp
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (μ := (1 : F)) hfix] at hv'
  exact hv0 ((smul_eq_zero.mp hv').resolve_left hheval)

private theorem IsPlaneFrame.primary_of_apply_eq_aux6 (hF : IsPlaneFrame Q p U e Bb)
    {d d₁ : ↥(orthDerived Q)} (hd : d ∈ Bb) (j₀ : Fin m)
    (hdd₁ : ∀ i, i ≠ j₀ → ∀ v ∈ U i, (d₁ : V ≃ₗ[F] V) v = (d : V ≃ₗ[F] V) v) {h : F[X]}
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) :
    (⨆ i ∈ Finset.univ.erase j₀, U i) ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h := by
  refine iSup₂_le fun i hi => ?_
  intro v hv
  rw [mem_primaryComponent]
  have hi' : i ≠ j₀ := (Finset.mem_erase.mp hi).1
  rw [IsPlaneFrame.primary_of_apply_eq_aux2 (W' := U i) (f := d₁) (g := d)
    (IsPlaneFrame.primary_of_apply_eq_aux4 hF hd i) (fun v hv => hdd₁ i hi' v hv) h v hv]
  exact mem_primaryComponent.mp (hU i hv)

private theorem IsPlaneFrame.primary_of_apply_eq_aux7 (hF : IsPlaneFrame Q p U e Bb) (hm : 2 ≤ m)
    (j₀ : Fin m) : (⨆ i ∈ Finset.univ.erase j₀, U i) ≠ ⊥ := by
  intro hbot
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin m, i₀ ≠ j₀ := by
    by_cases h0 : j₀.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff, h0] at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h0 (by simp [Fin.ext_iff] at h'; omega)⟩
  have hle : U i₀ ≤ ⨆ i ∈ Finset.univ.erase j₀, U i :=
    le_iSup₂ (f := fun i (_ : i ∈ Finset.univ.erase j₀) => U i) i₀
      (Finset.mem_erase.mpr ⟨hi₀, Finset.mem_univ i₀⟩)
  have h0 : Module.finrank F (U i₀) = 0 := by
    rw [le_bot_iff.mp (hle.trans (le_of_eq hbot)), finrank_bot]
  rw [hF.finrank_eq i₀] at h0
  omega

private theorem IsPlaneFrame.primary_of_apply_eq_aux8 {h : F[X]} (hheval : h.eval 1 ≠ 0)
    {d₁ : ↥(orthDerived Q)}
    (hVhne : primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h ≠ ⊥) : d₁ ≠ 1 := by
  intro h1
  apply hVhne
  rw [show (d₁ : V ≃ₗ[F] V).toLinearMap = 1 from
    congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V).toLinearMap) h1]
  rw [eq_bot_iff]
  intro v hv
  have hv' := mem_primaryComponent.mp hv
  have hfix : (1 : Module.End F V) v = (1 : F) • v := by simp
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (μ := (1 : F)) hfix] at hv'
  exact (smul_eq_zero.mp hv').resolve_left hheval

private theorem IsPlaneFrame.primary_of_apply_eq_aux9 (hF : IsPlaneFrame Q p U e Bb) :
    finrank F V = 2 * m + finrank F ↑(polarPerp Q (⨆ j, U j)) := by
  have hUuniv : (⨆ j : Fin m, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin m)), U j := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
    · refine iSup₂_le fun j _ => le_iSup U j
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (⨆ j : Fin m, U j)
    (polarPerp Q (⨆ j, U j))
  rw [hF.isCompl_iSup.inf_eq_bot, hF.isCompl_iSup.sup_eq_top] at hkey
  simp at hkey
  have hUfin : finrank F ↑(⨆ j : Fin m, U j) = 2 * m := by
    rw [hUuniv, hF.finrank_biSup, Finset.card_univ, Fintype.card_fin]
  rw [hUfin] at hkey
  exact hkey

private theorem IsPlaneFrame.primary_of_apply_eq_aux10 (hF : IsPlaneFrame Q p U e Bb)
    (j₀ : Fin m) :
    finrank F ↑(U j₀ ⊔ polarPerp Q (⨆ j, U j)) =
      2 + finrank F ↑(polarPerp Q (⨆ j, U j)) := by
  have hBdisj : Disjoint (U j₀) (polarPerp Q (⨆ j, U j)) :=
    (isCompl_polarPerp (hF.nondeg j₀)).disjoint.mono_right fun x hx =>
      mem_polarPerp_iff.mpr fun y hy => mem_polarPerp_iff.mp hx y (le_iSup U j₀ hy)
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (U j₀) (polarPerp Q (⨆ j, U j))
  rw [disjoint_iff.mp hBdisj, hF.finrank_eq j₀] at hkey
  simp at hkey
  omega

private theorem IsPlaneFrame.primary_of_apply_eq_aux11 (hF : IsPlaneFrame Q p U e Bb)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) :
    U j₀ ⊔ polarPerp Q (⨆ j, U j) ≤ fixedSpace (d₁ : V ≃ₗ[F] V) := by
  refine sup_le (fun v hv => mem_fixedSpace.mpr (hj₀ v hv)) (fun v hv => ?_)
  exact mem_fixedSpace.mpr (hF.apply_eq_of_mem_polarPerp_iSup hd₁ hv)

private theorem IsPlaneFrame.primary_of_apply_eq_aux12 (hF : IsPlaneFrame Q p U e Bb)
    {d₁ : ↥(orthDerived Q)} (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v)
    (hx₁ : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V)) {h : F[X]} (hh1 : h ≠ X - 1)
    (hmem : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) :
    Disjoint (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
      (fixedSpace (d₁ : V ≃ₗ[F] V)) := by
  have hXm : (X - 1 : F[X]) ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap := by
    refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one
      monic_X_sub_one ?_
    rw [← fixedSpace_eq_primaryComponent]
    intro hbot
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j₀) (hF.finrank_eq j₀)
    exact hv0 (by simpa using
      (hbot ▸ (mem_fixedSpace.mpr (hj₀ v hv)) : v ∈ (⊥ : Submodule F V)))
  rw [fixedSpace_eq_primaryComponent]
  exact disjoint_primaryComponent_of_ne hx₁ hmem hXm hh1

private theorem IsPlaneFrame.primary_of_apply_eq_aux13 (hF : IsPlaneFrame Q p U e Bb)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]} (hh1 : h ≠ X - 1)
    (hx₁ : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V))
    (hmem : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) :
    finrank F ↑(primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) ≤ 2 * (m - 1) := by
  have hV0 := IsPlaneFrame.primary_of_apply_eq_aux9 hF
  have hBfin := IsPlaneFrame.primary_of_apply_eq_aux10 hF j₀
  have hBfix := IsPlaneFrame.primary_of_apply_eq_aux11 hF hd₁ j₀ hj₀
  have hdisj := IsPlaneFrame.primary_of_apply_eq_aux12 hF j₀ hj₀ hx₁ hh1 hmem
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq
    (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) (fixedSpace (d₁ : V ≃ₗ[F] V))
  rw [disjoint_iff.mp hdisj] at hkey
  simp at hkey
  have hle : finrank F ↑(primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) +
      finrank F ↑(fixedSpace (d₁ : V ≃ₗ[F] V)) ≤ finrank F V := by
    rw [← hkey]
    simpa using Submodule.finrank_mono
      (le_top : (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h ⊔
        fixedSpace (d₁ : V ≃ₗ[F] V)) ≤ ⊤)
  have h2 : 2 + finrank F ↑(polarPerp Q (⨆ j, U j)) ≤
      finrank F ↑(fixedSpace (d₁ : V ≃ₗ[F] V)) := by
    rw [← hBfin]; exact Submodule.finrank_mono hBfix
  rw [hV0] at hle
  omega

private theorem IsPlaneFrame.primary_of_apply_eq_aux14 {d₁ : ↥(orthDerived Q)} {h : F[X]}
    [Fact (Irreducible h)]
    (hfrP : finrank F ↑(primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) = 2 * (m - 1))
    (hdeg : h.natDegree = 2) :
    primaryMultiplicity (d₁ : V ≃ₗ[F] V).toLinearMap h = m - 1 := by
  have hfr := finrank_primaryComponent (x := (d₁ : V ≃ₗ[F] V).toLinearMap) (a := h)
  rw [hfrP, hdeg] at hfr
  exact (Nat.mul_left_cancel (by norm_num : 0 < 2) hfr).symm

theorem IsPlaneFrame.primary_of_apply_eq (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d d₁ : ↥(orthDerived Q)} (hd : d ∈ Bb)
    (hd₁ : d₁ ∈ Bb) (j₀ : Fin m) (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v)
    (hdd₁ : ∀ i, i ≠ j₀ → ∀ v ∈ U i, (d₁ : V ≃ₗ[F] V) v = (d : V ≃ₗ[F] V) v) {h : F[X]}
    (hh1 : h ≠ X - 1) (hhd : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) (hm : 2 ≤ m) :
    h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap ∧
      primaryMultiplicity (d₁ : V ≃ₗ[F] V).toLinearMap h = m - 1 ∧
      ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hirr := irreducible_of_mem_primaryFactors hhd
  have hmon := monic_of_mem_primaryFactors hhd
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have hheval : h.eval 1 ≠ 0 := IsPlaneFrame.primary_of_apply_eq_aux1 hirr hmon hh1
  have hWle := IsPlaneFrame.primary_of_apply_eq_aux6 hF hd j₀ hdd₁ hU
  have hWbot := IsPlaneFrame.primary_of_apply_eq_aux7 hF hm j₀
  have hVhne : primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h ≠ ⊥ := fun hbot =>
    hWbot (le_bot_iff.mp (hWle.trans (le_of_eq hbot)))
  have hmem : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap :=
    mem_primaryFactors_of_primaryComponent_ne_bot hirr hmon hVhne
  have hd₁1 : d₁ ≠ 1 := IsPlaneFrame.primary_of_apply_eq_aux8 hheval hVhne
  have hd1_ne1 : d ≠ 1 := IsPlaneFrame.primary_of_apply_eq_aux5 hF hheval j₀ (hU j₀)
  have hx₁ : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d₁
      (orderOf_eq_prime (hF.isElemAbelian.2 d₁ hd₁) hd₁1)
  have hx_d : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d
      (orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1_ne1)
  have hdeg : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx_d hp hp2 hpq hhd hh1
  have hfrP_le := IsPlaneFrame.primary_of_apply_eq_aux13 hF hd₁ j₀ hj₀ hh1 hx₁ hmem
  have hWfin : finrank F ↑(⨆ i ∈ Finset.univ.erase j₀, U i) = 2 * (m - 1) := by
    rw [hF.finrank_biSup, Finset.card_erase_of_mem (Finset.mem_univ j₀),
      Finset.card_univ, Fintype.card_fin]
  have hfrP : finrank F ↑(primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) = 2 * (m - 1) :=
    le_antisymm hfrP_le (hWfin ▸ Submodule.finrank_mono hWle)
  have hmult := IsPlaneFrame.primary_of_apply_eq_aux14 hfrP hdeg
  refine ⟨hmem, hmult, fun i hi => ?_⟩
  exact (le_iSup₂ (f := fun i (_ : i ∈ Finset.univ.erase j₀) => U i) i
    (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)).trans hWle


private theorem exists_solvable_ker_centralizer_pair_aux2 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {b : ↥(orthDerived Q)} (hb : b ∈ Bb) :
    OddOrderIsometry Q p (b : V ≃ₗ[F] V) := by
  refine ⟨orthDerived_le_orthogonalGroup b.2, ?_, ?_, ?_⟩
  · have hbp : b ^ p = 1 := hF.isElemAbelian.2 b hb
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hbp
  · intro h0
    have h1 : ringChar F ∣ p := (ringChar.spec F p).mp h0
    rw [ringChar.eq F 2] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h1).symm
  · intro v hv
    exact hQ.1 v fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]; exact hv w

private theorem exists_solvable_ker_centralizer_pair_aux3 (j₀ : Fin m) :
    (⨆ j : Fin m, U j) = U j₀ ⊔ ⨆ i ∈ Finset.univ.erase j₀, U i := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hj : j = j₀
    · subst hj; exact le_sup_left
    · exact (le_iSup₂ (f := fun i (_ : i ∈ Finset.univ.erase j₀) => U i) j
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)).trans le_sup_right
  · refine sup_le (le_iSup U j₀) ?_
    refine iSup₂_le fun i _ => le_iSup U i

private theorem exists_solvable_ker_centralizer_pair_aux4 (hF : IsPlaneFrame Q p U e Bb) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb)
    (j₀ : Fin m) (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) :
    U j₀ ⊔ polarPerp Q (⨆ j, U j) ≤ fixedSpace (d₁ : V ≃ₗ[F] V) := by
  refine sup_le (fun v hv => mem_fixedSpace.mpr (hj₀ v hv)) (fun v hv => ?_)
  exact mem_fixedSpace.mpr (hF.apply_eq_of_mem_polarPerp_iSup hd₁ hv)

private theorem exists_solvable_ker_centralizer_pair_aux5 (hF : IsPlaneFrame Q p U e Bb) {d₁ : ↥(orthDerived Q)} (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) :
    (X - 1 : F[X]) ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap := by
  refine mem_primaryFactors_of_primaryComponent_ne_bot irreducible_X_sub_one monic_X_sub_one ?_
  rw [← fixedSpace_eq_primaryComponent]
  intro hbot
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j₀) (hF.finrank_eq j₀)
  exact hv0 (by simpa using
    (hbot ▸ (mem_fixedSpace.mpr (hj₀ v hv)) : v ∈ (⊥ : Submodule F V)))

private theorem exists_solvable_ker_centralizer_pair_aux6 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    fixedSpace (d₁ : V ≃ₗ[F] V) = U j₀ ⊔ polarPerp Q (⨆ j, U j) := by
  have hx : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V) := exists_solvable_ker_centralizer_pair_aux2 hF hQ hp hp2 hd₁
  have hXm := exists_solvable_ker_centralizer_pair_aux5 hF j₀ hj₀
  have hdisj : Disjoint (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
      (fixedSpace (d₁ : V ≃ₗ[F] V)) := by
    rw [fixedSpace_eq_primaryComponent]
    exact disjoint_primaryComponent_of_ne hx hh hXm hh1
  have hWle : (⨆ i ∈ Finset.univ.erase j₀, U i) ≤
      primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h :=
    iSup₂_le fun i hi => hU i (Finset.mem_erase.mp hi).1
  refine le_antisymm ?_ (exists_solvable_ker_centralizer_pair_aux4 hF hd₁ j₀ hj₀)
  intro v hv
  have hmem : v ∈ (⨆ j : Fin m, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hF.isCompl_iSup.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
  have hzfix : (d₁ : V ≃ₗ[F] V) z = z := hF.apply_eq_of_mem_polarPerp_iSup hd₁ hz
  have hafix : (d₁ : V ≃ₗ[F] V) a = a := by
    have hv' : (d₁ : V ≃ₗ[F] V) (a + z) = a + z := mem_fixedSpace.mp hv
    rw [map_add, hzfix] at hv'
    exact add_right_cancel hv'
  have ha' : a ∈ U j₀ ⊔ ⨆ i ∈ Finset.univ.erase j₀, U i := by
    rw [← exists_solvable_ker_centralizer_pair_aux3 j₀]
    exact ha
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 ha'
  have hufix : (d₁ : V ≃ₗ[F] V) u = u := hj₀ u hu
  have hwfix : (d₁ : V ≃ₗ[F] V) w = w := by
    have hv' : (d₁ : V ≃ₗ[F] V) (u + w) = u + w := hafix
    rw [map_add, hufix] at hv'
    exact add_left_cancel hv'
  have hwP : w ∈ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h := hWle hw
  have hwF1 : w ∈ fixedSpace (d₁ : V ≃ₗ[F] V) := mem_fixedSpace.mpr hwfix
  have hwbot : w ∈ (⊥ : Submodule F V) := by
    have := Submodule.mem_inf.mpr ⟨hwP, hwF1⟩
    rwa [disjoint_iff.mp hdisj] at this
  have hw0 : w = 0 := by simpa using hwbot
  rw [hw0, add_zero]
  exact Submodule.mem_sup.mpr ⟨u, hu, z, hz, rfl⟩


private theorem exists_solvable_ker_centralizer_pair_aux7 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    othersSpace (d₁ : V ≃ₗ[F] V).toLinearMap h = fixedSpace (d₁ : V ≃ₗ[F] V) := by
  have hx : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V) := exists_solvable_ker_centralizer_pair_aux2 hF hQ hp hp2 hd₁
  have hXm := exists_solvable_ker_centralizer_pair_aux5 hF j₀ hj₀
  have hself : reciprocalPolynomial h = h :=
    hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hh1
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun k hk => ?_
    by_cases hk1 : k = X - 1
    · rw [hk1, ← fixedSpace_eq_primaryComponent]
    · exfalso
      obtain ⟨i, hi⟩ := hF.exists_le_primaryComponent_of_mem hp hp2 hpq hd₁ hk.1 hk1
      by_cases hij : i = j₀
      · subst hij
        have hle : U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap (X - 1) := by
          rw [← fixedSpace_eq_primaryComponent]
          exact fun v hv => mem_fixedSpace.mpr (hj₀ v hv)
        have hdisj := disjoint_primaryComponent_of_ne hx hk.1 hXm hk1
        have hbot : U i = ⊥ := le_bot_iff.mp (le_inf hi hle |>.trans hdisj.le_bot)
        have h0 : Module.finrank F (U i) = 0 := by rw [hbot, finrank_bot]
        rw [hF.finrank_eq i] at h0
        omega
      · have hdisj := disjoint_primaryComponent_of_ne hx hk.1 hh hk.2.1
        have hbot : U i = ⊥ := le_bot_iff.mp (le_inf hi (hU i hij) |>.trans hdisj.le_bot)
        have h0 : Module.finrank F (U i) = 0 := by rw [hbot, finrank_bot]
        rw [hF.finrank_eq i] at h0
        omega
  · rw [fixedSpace_eq_primaryComponent]
    exact le_iSup₂_of_le (X - 1)
      ⟨hXm, Ne.symm hh1, by rw [hself]; exact Ne.symm hh1⟩ le_rfl


private theorem exists_solvable_ker_centralizer_pair_aux8 (hF : IsPlaneFrame Q p U e Bb) (j : Fin m) :
    Submodule.map ((e j : V ≃ₗ[F] V).toLinearMap - 1) (U j) = U j := by
  have him : ∀ x ∈ U j, ((e j : V ≃ₗ[F] V).toLinearMap - 1) x ∈ U j := fun x hx =>
    sub_mem (hF.maps_to j x hx) hx
  refine Submodule.eq_of_le_of_finrank_eq (fun _ h => ?_) ?_
  · rcases h with ⟨x, hx, rfl⟩
    exact him x hx
  · rw [← finrank_range_restrict ((e j : V ≃ₗ[F] V).toLinearMap - 1) him]
    exact LinearMap.finrank_range_of_inj (by
      intro a b hab
      have h0 : ((e j : V ≃ₗ[F] V).toLinearMap - 1) ((a : V) - b) = 0 := by
        have hab' : ((e j : V ≃ₗ[F] V).toLinearMap - 1) (a : V) =
            ((e j : V ≃ₗ[F] V).toLinearMap - 1) (b : V) := congrArg Subtype.val hab
        rw [map_sub, hab', sub_self]
      have h1 : (e j : V ≃ₗ[F] V) ((a : V) - b) = (a : V) - b := sub_eq_zero.mp h0
      have h2 : (a : V) - b = 0 := hF.eq_zero_of_apply_eq j _ (sub_mem a.2 b.2) h1
      exact Subtype.ext (sub_eq_zero.mp h2))

private theorem exists_solvable_ker_centralizer_pair_aux9 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    Submodule.map ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) (fixedSpace (d₁ : V ≃ₗ[F] V)) =
      U j₀ := by
  have hF1 := exists_solvable_ker_centralizer_pair_aux6 hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [hF1] at hv
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have hzperp : z ∈ polarPerp Q (U j₀) := fun w hw =>
      mem_polarPerp_iff.mp hz w (le_iSup U j₀ hw)
    have hzu : (e j₀ : V ≃ₗ[F] V).toLinearMap z = z := by
      simpa using hF.apply_of_perp j₀ z hzperp
    have h1 : ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) (u + z) =
        ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) u := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, map_add, map_add, hzu]
      simp only [Module.End.one_apply]
      abel
    rw [h1]
    exact sub_mem (hF.maps_to j₀ u hu) hu
  · calc U j₀ = Submodule.map ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) (U j₀) :=
        (exists_solvable_ker_centralizer_pair_aux8 hF j₀).symm
      _ ≤ Submodule.map ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1)
            (fixedSpace (d₁ : V ≃ₗ[F] V)) :=
          Submodule.map_mono (by rw [hF1]; exact le_sup_left)

private theorem exists_solvable_ker_centralizer_pair_aux10 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    {z : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q)))} :
    ∀ w ∈ U j₀, (z : V ≃ₗ[F] V) w ∈ U j₀ := by
  have hmap := exists_solvable_ker_centralizer_pair_aux9 hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  intro w hw
  have hw' : w ∈ Submodule.map ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1)
      (fixedSpace (d₁ : V ≃ₗ[F] V)) := hmap ▸ hw
  obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.1 hw'
  have hc : (e j₀ : V ≃ₗ[F] V) * (z : V ≃ₗ[F] V) = (z : V ≃ₗ[F] V) * (e j₀ : V ≃ₗ[F] V) :=
    congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
      (Subgroup.mem_centralizer_iff.1 z.2 (e j₀) (by simp))
  have hcd : (d₁ : V ≃ₗ[F] V) * (z : V ≃ₗ[F] V) = (z : V ≃ₗ[F] V) * (d₁ : V ≃ₗ[F] V) :=
    congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
      (Subgroup.mem_centralizer_iff.1 z.2 d₁ (by simp))
  have hzv : (z : V ≃ₗ[F] V) v ∈ fixedSpace (d₁ : V ≃ₗ[F] V) := by
    rw [mem_fixedSpace]
    show (d₁ : V ≃ₗ[F] V) ((z : V ≃ₗ[F] V) v) = (z : V ≃ₗ[F] V) v
    rw [← LinearEquiv.mul_apply, hcd, LinearEquiv.mul_apply, mem_fixedSpace.mp hv]
  have hzy : (z : V ≃ₗ[F] V) * (e j₀ : V ≃ₗ[F] V) = (e j₀ : V ≃ₗ[F] V) * (z : V ≃ₗ[F] V) := hc.symm
  have hcomm : (z : V ≃ₗ[F] V).toLinearMap * ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1)
      = ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) * (z : V ≃ₗ[F] V).toLinearMap := by
    rw [mul_sub, sub_mul, mul_one, one_mul, ← LinearEquiv.coe_toLinearMap_mul,
      ← LinearEquiv.coe_toLinearMap_mul, hzy]
  have hzw : (z : V ≃ₗ[F] V) w = ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) ((z : V ≃ₗ[F] V) v) := by
    rw [← hvw]
    change ((z : V ≃ₗ[F] V).toLinearMap * ((e j₀ : V ≃ₗ[F] V).toLinearMap - 1)) v =
      (((e j₀ : V ≃ₗ[F] V).toLinearMap - 1) * (z : V ≃ₗ[F] V).toLinearMap) v
    rw [hcomm]
  rw [hzw, ← hmap]
  exact Submodule.mem_map.mpr ⟨(z : V ≃ₗ[F] V) v, hzv, rfl⟩


private theorem exists_solvable_ker_centralizer_pair_aux11 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    polarPerp Q (⨆ j, U j) = fixedSpace (e j₀ : V ≃ₗ[F] V) ⊓ fixedSpace (d₁ : V ≃ₗ[F] V) := by
  have hF1 := exists_solvable_ker_centralizer_pair_aux6 hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  rw [hF.fixedSpace_eq_polarPerp j₀]
  refine le_antisymm ?_ ?_
  · intro v hv
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact fun w hw => mem_polarPerp_iff.mp hv w (le_iSup U j₀ hw)
    · exact mem_fixedSpace.mpr (hF.apply_eq_of_mem_polarPerp_iSup hd₁ hv)
  · intro v hv
    have hperp : v ∈ polarPerp Q (U j₀) := (Submodule.mem_inf.mp hv).1
    have hfix : v ∈ fixedSpace (d₁ : V ≃ₗ[F] V) := (Submodule.mem_inf.mp hv).2
    have hfix' : v ∈ U j₀ ⊔ polarPerp Q (⨆ j, U j) := hF1 ▸ hfix
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hfix'
    have hzu : u ∈ polarPerp Q (U j₀) := by
      simpa using sub_mem hperp (fun w hw => mem_polarPerp_iff.mp hz w (le_iSup U j₀ hw))
    have hu0 : u = 0 := by
      have hmem : u ∈ (⊥ : Submodule F V) := by
        have := Submodule.mem_inf.mpr ⟨hu, hzu⟩
        rwa [(isCompl_polarPerp (hF.nondeg j₀)).inf_eq_bot] at this
      simpa using hmem
    rw [hu0, zero_add]
    exact hz

private theorem exists_solvable_ker_centralizer_pair_aux12 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    {z : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q)))} :
    ∀ w ∈ polarPerp Q (⨆ j, U j), (z : V ≃ₗ[F] V) w ∈ polarPerp Q (⨆ j, U j) := by
  have hV0 := exists_solvable_ker_centralizer_pair_aux11 hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  intro w hw
  rw [hV0] at hw ⊢
  have hcy : (e j₀ : V ≃ₗ[F] V) * (z : V ≃ₗ[F] V) = (z : V ≃ₗ[F] V) * (e j₀ : V ≃ₗ[F] V) :=
    congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
      (Subgroup.mem_centralizer_iff.1 z.2 (e j₀) (by simp))
  have hcd : (d₁ : V ≃ₗ[F] V) * (z : V ≃ₗ[F] V) = (z : V ≃ₗ[F] V) * (d₁ : V ≃ₗ[F] V) :=
    congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
      (Subgroup.mem_centralizer_iff.1 z.2 d₁ (by simp))
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · have hwy : (e j₀ : V ≃ₗ[F] V) w = w := mem_fixedSpace.mp (Submodule.mem_inf.mp hw).1
    rw [mem_fixedSpace]
    rw [← LinearEquiv.mul_apply, hcy, LinearEquiv.mul_apply, hwy]
  · have hwx : (d₁ : V ≃ₗ[F] V) w = w := mem_fixedSpace.mp (Submodule.mem_inf.mp hw).2
    rw [mem_fixedSpace]
    rw [← LinearEquiv.mul_apply, hcd, LinearEquiv.mul_apply, hwx]



private theorem exists_solvable_ker_centralizer_pair_aux1 {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) (h2 : finrank K W = 2) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  set δ := CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ with hδ
  haveI : Group.IsSolvable δ.ker :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subtype.ext (commute_of_dicksonHom_eq_one hQ h2 a.1.2 b.1.2 a.2 b.2))
  haveI : Group.IsSolvable (Multiplicative (ZMod 2)) :=
    Group.isSolvable_of_comm fun a b => mul_comm a b
  exact Group.isSolvable_of_ker_le_range δ.ker.subtype δ (by rw [Subgroup.range_subtype])

private noncomputable def exists_solvable_ker_centralizer_pair_aux13
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →* (U j₀ ≃ₗ[F] U j₀) :=
  restrictHom _ (U j₀) (fun z w hw =>
    exists_solvable_ker_centralizer_pair_aux10 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
      (z := z) w hw)

private noncomputable def exists_solvable_ker_centralizer_pair_aux14
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →*
      (polarPerp Q (⨆ j, U j) ≃ₗ[F] polarPerp Q (⨆ j, U j)) :=
  restrictHom _ (polarPerp Q (⨆ j, U j)) (fun z w hw =>
    exists_solvable_ker_centralizer_pair_aux12 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
      (z := z) w hw)

private noncomputable def exists_solvable_ker_centralizer_pair_aux15
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j₀).subtype)) :=
  let ψ₁ := exists_solvable_ker_centralizer_pair_aux13 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  ψ₁.codRestrict _ fun z => by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    have hcoe : ((ψ₁ z w : U j₀) : V) = (z : V ≃ₗ[F] V) (w : V) := rfl
    change Q ((ψ₁ z w : U j₀) : V) = Q (w : V)
    rw [hcoe]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (orthDerived_le_orthogonalGroup z.1.2) (w : V)

private noncomputable def exists_solvable_ker_centralizer_pair_aux16
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (polarPerp Q (⨆ j, U j)).subtype)) :=
  let ψ₂ := exists_solvable_ker_centralizer_pair_aux14 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
  ψ₂.codRestrict _ fun z => by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    have hcoe : ((ψ₂ z w : polarPerp Q (⨆ j, U j)) : V) = (z : V ≃ₗ[F] V) (w : V) := rfl
    change Q ((ψ₂ z w : polarPerp Q (⨆ j, U j)) : V) = Q (w : V)
    rw [hcoe]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (orthDerived_le_orthogonalGroup z.1.2) (w : V)

private noncomputable def exists_solvable_ker_centralizer_pair_aux17
    {d₁ : ↥(orthDerived Q)} (j₀ : Fin m) :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →*
      ↥(Subgroup.centralizer ({(d₁ : V ≃ₗ[F] V)} : Set (V ≃ₗ[F] V))) :=
  { toFun := fun z => ⟨(z : V ≃ₗ[F] V), by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
        (Subgroup.mem_centralizer_iff.1 z.2 d₁ (by simp))⟩
    map_one' := Subtype.ext rfl
    map_mul' := fun _ _ => Subtype.ext rfl }

private noncomputable def exists_solvable_ker_centralizer_pair_aux18
    {d₁ : ↥(orthDerived Q)} (j₀ : Fin m) {h : F[X]} :
    ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →* (AdjoinRoot h)ˣ :=
  (Units.map (LinearMap.det : Module.End (AdjoinRoot h)
    (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) →* AdjoinRoot h)).comp
    ((centralizerGL (d₁ : V ≃ₗ[F] V) h).comp
      (exists_solvable_ker_centralizer_pair_aux17 (Q := Q) (d₁ := d₁) j₀))

private theorem exists_solvable_ker_centralizer_pair_aux19
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    (z : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))))
    (h1 : (exists_solvable_ker_centralizer_pair_aux15 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1)
    (h2 : (exists_solvable_ker_centralizer_pair_aux16 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1) :
    ∀ w ∈ U j₀ ⊔ polarPerp Q (⨆ j, U j), (z : V ≃ₗ[F] V) w = w := by
  have h1' : (exists_solvable_ker_centralizer_pair_aux13 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 :=
    Subtype.ext_iff.mp h1
  have h2' : (exists_solvable_ker_centralizer_pair_aux14 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 :=
    Subtype.ext_iff.mp h2
  have hfixU : ∀ w : U j₀, (z : V ≃ₗ[F] V) (w : V) = (w : V) := by
    intro w
    have h1'' : (exists_solvable_ker_centralizer_pair_aux13 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w = w :=
      congrArg (fun e : U j₀ ≃ₗ[F] U j₀ => e w) h1'
    have h1v : (((exists_solvable_ker_centralizer_pair_aux13 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w : U j₀) : V) = (w : V) :=
      congrArg Subtype.val h1''
    have hcoe : (((exists_solvable_ker_centralizer_pair_aux13 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w : U j₀) : V) = (z : V ≃ₗ[F] V) (w : V) := rfl
    rw [hcoe] at h1v
    exact h1v
  have hfixV : ∀ w : polarPerp Q (⨆ j, U j), (z : V ≃ₗ[F] V) (w : V) = (w : V) := by
    intro w
    have h2'' : (exists_solvable_ker_centralizer_pair_aux14 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w = w :=
      congrArg (fun e : polarPerp Q (⨆ j, U j) ≃ₗ[F] polarPerp Q (⨆ j, U j) => e w) h2'
    have h2v : (((exists_solvable_ker_centralizer_pair_aux14 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w : polarPerp Q (⨆ j, U j)) : V) = (w : V) :=
      congrArg Subtype.val h2''
    have hcoe : (((exists_solvable_ker_centralizer_pair_aux14 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z w : polarPerp Q (⨆ j, U j)) : V) = (z : V ≃ₗ[F] V) (w : V) := rfl
    rw [hcoe] at h2v
    exact h2v
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add, hfixU ⟨a, ha⟩, hfixV ⟨b, hb⟩]

private theorem exists_solvable_ker_centralizer_pair_aux22
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    (z : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))))
    (hfixB : ∀ w ∈ U j₀ ⊔ polarPerp Q (⨆ j, U j), (z : V ≃ₗ[F] V) w = w)
    (h3 : (exists_solvable_ker_centralizer_pair_aux18 (Q := Q) (d₁ := d₁) j₀ (h := h)) z = 1) :
    (z : V ≃ₗ[F] V) ∈ specialBlock Q (d₁ : V ≃ₗ[F] V) h := by
  have hzIso : (z : V ≃ₗ[F] V) ∈ isometryCentralizer Q (d₁ : V ≃ₗ[F] V) := by
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup z.1.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun a : ↥(orthDerived Q) => (a : V ≃ₗ[F] V))
      (Subgroup.mem_centralizer_iff.1 z.2 d₁ (by simp))
  have hzS : (z : V ≃ₗ[F] V) ∈ supportedBlock Q (d₁ : V ≃ₗ[F] V) h := by
    refine mem_supportedBlock.mpr ⟨hzIso, ?_⟩
    rw [exists_solvable_ker_centralizer_pair_aux7 hF hQ hp hp2 hpq hd₁ j₀ hj₀ hh hh1 hU,
      exists_solvable_ker_centralizer_pair_aux6 hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU]
    exact hfixB
  have h3' : blockDet Q (d₁ : V ≃ₗ[F] V) h ⟨(z : V ≃ₗ[F] V), hzS⟩ = 1 := by
    have hval : ((Units.map (LinearMap.det : Module.End (AdjoinRoot h)
        (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) →* AdjoinRoot h))
        (centralizerGL (d₁ : V ≃ₗ[F] V) h
          (exists_solvable_ker_centralizer_pair_aux17 (Q := Q) (d₁ := d₁) j₀ z)) : AdjoinRoot h) = 1 := by
      have := congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) h3
      simpa only [exists_solvable_ker_centralizer_pair_aux18, MonoidHom.comp_apply,
        Units.coe_map, Units.val_one] using this
    have hgl : (blockGL Q (d₁ : V ≃ₗ[F] V) h ⟨(z : V ≃ₗ[F] V), hzS⟩ :
          BlockGL (d₁ : V ≃ₗ[F] V) h) = centralizerGL (d₁ : V ≃ₗ[F] V) h
            (exists_solvable_ker_centralizer_pair_aux17 (Q := Q) (d₁ := d₁) j₀ z) := by
      rw [blockGL]
      exact congrArg (centralizerGL (d₁ : V ≃ₗ[F] V) h) (Subtype.ext rfl)
    rw [blockDet_apply, hgl]
    exact hval
  exact Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_subgroupOf.mpr (mem_specialBlock.mpr ⟨hzS, h3'⟩))


private theorem exists_solvable_ker_centralizer_pair_aux20
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    (z : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))))
    (hz : (z : V ≃ₗ[F] V) ∈ specialBlock Q (d₁ : V ≃ₗ[F] V) h) :
    (exists_solvable_ker_centralizer_pair_aux15 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 ∧
      (exists_solvable_ker_centralizer_pair_aux16 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 ∧
      (exists_solvable_ker_centralizer_pair_aux18 (Q := Q) (d₁ := d₁) j₀ (h := h)) z = 1 := by
  have hzS := specialBlock_le_supportedBlock h hz
  have hfixO : ∀ v ∈ othersSpace (d₁ : V ≃ₗ[F] V).toLinearMap h,
      (z : V ≃ₗ[F] V) v = v := (mem_supportedBlock.mp hzS).2
  have hfixF1 : ∀ v ∈ fixedSpace (d₁ : V ≃ₗ[F] V), (z : V ≃ₗ[F] V) v = v := by
    rw [exists_solvable_ker_centralizer_pair_aux7 (Q := Q) hF hQ hp hp2 hpq hd₁ j₀ hj₀ hh hh1 hU] at hfixO
    exact hfixO
  have hfixB : ∀ v ∈ U j₀ ⊔ polarPerp Q (⨆ j, U j), (z : V ≃ₗ[F] V) v = v := by
    rw [← exists_solvable_ker_centralizer_pair_aux6 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU]
    exact hfixF1
  have h1 : (exists_solvable_ker_centralizer_pair_aux15 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    change (z : V ≃ₗ[F] V) (w : V) = (w : V)
    exact hfixB (w : V) (Submodule.mem_sup_left w.2)
  have h2 : (exists_solvable_ker_centralizer_pair_aux16 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU) z = 1 := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => ?_
    apply Subtype.ext
    change (z : V ≃ₗ[F] V) (w : V) = (w : V)
    exact hfixB (w : V) (Submodule.mem_sup_right w.2)
  have h3 : (exists_solvable_ker_centralizer_pair_aux18 (Q := Q) (d₁ := d₁) j₀ (h := h)) z = 1 := by
    rw [Units.ext_iff]
    change ((Units.map (LinearMap.det : Module.End (AdjoinRoot h)
      (primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) →* AdjoinRoot h))
      (centralizerGL (d₁ : V ≃ₗ[F] V) h
        (exists_solvable_ker_centralizer_pair_aux17 (Q := Q) (d₁ := d₁) j₀ z)) : AdjoinRoot h) = 1
    rw [Units.coe_map]
    have hgl : (blockGL Q (d₁ : V ≃ₗ[F] V) h ⟨(z : V ≃ₗ[F] V), hzS⟩ :
          BlockGL (d₁ : V ≃ₗ[F] V) h) = centralizerGL (d₁ : V ≃ₗ[F] V) h
            (exists_solvable_ker_centralizer_pair_aux17 (Q := Q) (d₁ := d₁) j₀ z) := by
      rw [blockGL]
      exact congrArg (centralizerGL (d₁ : V ≃ₗ[F] V) h) (Subtype.ext rfl)
    rw [← hgl, ← blockDet_apply]
    exact blockDet_eq_one_of_mem_specialBlock hz
  exact ⟨h1, h2, h3⟩

private theorem exists_solvable_ker_centralizer_pair_aux23 {U : Fin m → Submodule F V} :
    (⨆ j : Fin m, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin m)), U j := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
  · refine iSup₂_le fun j _ => le_iSup U j

private theorem exists_solvable_ker_centralizer_pair_aux21
    (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin m)
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h)
    (hV0fin : finrank F ↑(polarPerp Q (⨆ j, U j)) = 2) :
    ∃ (A : Type) (_ : Group A), Group.IsSolvable A ∧
      ∃ φ : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →* A,
        φ.ker = ((specialBlock Q (d₁ : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)).subgroupOf
          (Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) := by
  let A := ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j₀).subtype)) ×
    (↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (polarPerp Q (⨆ j, U j)).subtype)) × (AdjoinRoot h)ˣ)
  have hUuniv : (⨆ j : Fin m, U j) = ⨆ j ∈ (Finset.univ : Finset (Fin m)), U j :=
    exists_solvable_ker_centralizer_pair_aux23
  haveI hsolv₁ : Group.IsSolvable
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U j₀).subtype)) :=
    exists_solvable_ker_centralizer_pair_aux1 (hF.nondeg j₀) (by rw [hF.finrank_eq j₀])
  haveI hsolv₂ : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (polarPerp Q (⨆ j, U j)).subtype)) := by
    refine exists_solvable_ker_centralizer_pair_aux1 ?_ ?_
    · have hW : (QuadraticMap.polarBilin (Q.comp (⨆ j, U j).subtype)).Nondegenerate := by
        rw [hUuniv]
        exact hF.nondeg_biSup Finset.univ
      exact nondeg_comp_polarPerp hQ hW
    · rw [hV0fin]
  haveI hsolv₃ : Group.IsSolvable (AdjoinRoot h)ˣ :=
    Group.isSolvable_of_comm fun a b => mul_comm a b
  refine ⟨A, inferInstance, inferInstance, (exists_solvable_ker_centralizer_pair_aux15 (Q := Q)
    hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU).prod
    ((exists_solvable_ker_centralizer_pair_aux16 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU).prod
      (exists_solvable_ker_centralizer_pair_aux18 (Q := Q) (d₁ := d₁) j₀ (h := h))), ?_⟩
  ext z
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz
    have hfixB := exists_solvable_ker_centralizer_pair_aux19 (Q := Q) hF hQ hp hp2 hd₁ j₀ hj₀ hh hh1 hU
      z (congrArg Prod.fst hz) (congrArg (fun w => w.2.1) hz)
    exact exists_solvable_ker_centralizer_pair_aux22 (Q := Q) hF hQ hp hp2 hpq hd₁ j₀ hj₀ hh hh1 hU
      z hfixB (congrArg (fun w => w.2.2) hz)
  · intro hz
    have hzN : (z : V ≃ₗ[F] V) ∈ specialBlock Q (d₁ : V ≃ₗ[F] V) h :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hz)
    obtain ⟨h1, h2, h3⟩ := exists_solvable_ker_centralizer_pair_aux20 (Q := Q) hF hQ hp hp2 hpq
      hd₁ j₀ hj₀ hh hh1 hU z hzN
    exact Prod.ext h1 (Prod.ext h2 h3)


theorem exists_solvable_ker_centralizer_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (j₀ : Fin (n - 1))
    (hj₀ : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h) :
    ∃ (A : Type) (_ : Group A), Group.IsSolvable A ∧
      ∃ φ : ↥(Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) →* A,
        φ.ker = ((specialBlock Q (d₁ : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)).subgroupOf
          (Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q))) := by
  have hn : 1 ≤ n := by have h := j₀.isLt; omega
  have hUuniv : (⨆ j : Fin (n - 1), U j) = ⨆ j ∈ (Finset.univ : Finset (Fin (n - 1))), U j := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_univ j) le_rfl)
    · refine iSup₂_le fun j _ => le_iSup U j
  have hV0fin : finrank F ↑(polarPerp Q (⨆ j, U j)) = 2 := by
    rw [finrank_polarPerp hQ (⨆ j, U j), hdim, hUuniv, hF.finrank_biSup,
      Finset.card_univ, Fintype.card_fin]
    omega
  exact exists_solvable_ker_centralizer_pair_aux21 hF hQ hp hp2 hpq hd₁ j₀ hj₀ hh hh1 hU hV0fin


private theorem layerIs_centralizer_pair_aux1 {n : ℕ} (hn : 4 ≤ n)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d d₁ : ↥(orthDerived Q)}
    {h : F[X]} (hhd : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) (j₀ : Fin (n - 1))
    (hk1 : ∀ i, i ≠ j₀ → ∀ v ∈ U i, (d₁ : V ≃ₗ[F] V) v = (d : V ≃ₗ[F] V) v) :
    d₁ ≠ 1 := by
  intro h1
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin (n - 1), i₀ ≠ j₀ := by
    by_cases h0 : j₀.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff, h0] at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h0 (by simp [Fin.ext_iff] at h'; omega)⟩
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i₀) (hF.finrank_eq i₀)
  refine hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hhd hh1 (hU i₀ hv) ?_)
  rw [← hk1 i₀ hi₀ v hv, h1]
  rfl

private theorem layerIs_centralizer_pair_aux2 (hF : IsPlaneFrame Q p U e Bb)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb) (hd₁1 : d₁ ≠ 1) :
    orderOf d₁ = p ∧ OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d₁ = p := orderOf_eq_prime (hF.isElemAbelian.2 d₁ hd₁) hd₁1
  exact ⟨hord, oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d₁ hord⟩

private theorem layerIs_centralizer_pair_aux3 {n : ℕ} (hn : 4 ≤ n)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {h : F[X]}
    (hhd : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) (j₀ : Fin (n - 1))
    {d₁ : ↥(orthDerived Q)} (hd₁ : d₁ ∈ Bb)
    (hk0 : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v)
    (hk1 : ∀ i, i ≠ j₀ → ∀ v ∈ U i, (d₁ : V ≃ₗ[F] V) v = (d : V ≃ₗ[F] V) v) :
    h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap ∧
      primaryMultiplicity (d₁ : V ≃ₗ[F] V).toLinearMap h = n - 2 ∧
      ∀ i, i ≠ j₀ → U i ≤ primaryComponent (d₁ : V ≃ₗ[F] V).toLinearMap h := by
  obtain ⟨hh₁, hmult, hUd₁⟩ :=
    hF.primary_of_apply_eq hQ hp hp2 hpq hd hd₁ j₀ hk0 hk1 hh1 hhd hU (by omega)
  exact ⟨hh₁, by rw [hmult]; omega, hUd₁⟩

private theorem layerIs_centralizer_pair_aux4 (hF : IsPlaneFrame Q p U e Bb)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {d₁ : ↥(orthDerived Q)}
    (hd₁ : d₁ ∈ Bb) (j₀ : Fin m) (hx₁ : OddOrderIsometry Q p (d₁ : V ≃ₗ[F] V))
    (hk0 : ∀ v ∈ U j₀, (d₁ : V ≃ₗ[F] V) v = v) {h : F[X]}
    (hh₁ : h ∈ primaryFactors (d₁ : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1) :
    (specialBlock Q (d₁ : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) ≤
      Subgroup.centralizer ({d₁, e j₀} : Set ↥(orthDerived Q)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hself := hx₁.reciprocal_eq_of_dvd_card_succ hp hpq hh₁ hh1
  obtain ⟨kk, hkk, hUkk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd₁ j₀
  have hkkh : kk ≠ h := by
    rintro rfl
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U j₀) (hF.finrank_eq j₀)
    exact hv0 (eq_zero_of_mem_primaryComponent_of_apply_eq hh₁ hh1 (hUkk hv) (hk0 v hv))
  have hfix : ∀ g ∈ specialBlock Q (d₁ : V ≃ₗ[F] V) h, ∀ v ∈ U j₀, g v = v := fun g hg v hv =>
    apply_eq_of_mem_specialBlock hkk hkkh (by rw [hself]; exact hkkh) hg (hUkk hv)
  intro g hg
  have hgs := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases hz with rfl | hz
  · exact Subtype.ext (LinearEquiv.ext fun v =>
      ((mem_isometryCentralizer.1 (specialBlock_le_isometryCentralizer h hgs)).2 v).symm)
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subtype.ext (commute_of_apply_eq (hF.nondeg j₀)
      (orthDerived_le_orthogonalGroup g.2) (hfix _ hgs) (hF.maps_to j₀) (hF.apply_of_perp j₀)).symm

theorem layerIs_centralizer_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) {h : F[X]}
    (hhd : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hU : ∀ j, U j ≤ primaryComponent (d : V ≃ₗ[F] V).toLinearMap h) (j₀ : Fin (n - 1))
    (hm4 : 4 ≤ n - 2 ∨ ((n - 2 = 2 ∨ n - 2 = 3) ∧ 4 ≤ Nat.card F)) :
    LayerIs p (Subgroup.centralizer {d, e j₀}) (isUnA (n - 2) (Nat.card F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨k, hk0, hk1⟩ := hF.exists_mul_zpow_apply hd j₀
  have hd₁B : d * e j₀ ^ k ∈ Bb := mul_mem hd (zpow_mem (hF.mem j₀) k)
  rw [← centralizer_pair_eq_of_mul_zpow_cent d (e j₀) k]
  generalize hd₁ : d * e j₀ ^ k = d₁ at hd₁B hk0 hk1 ⊢
  have hd₁1 : d₁ ≠ 1 := layerIs_centralizer_pair_aux1 hn hF hhd hh1 hU j₀ hk1
  obtain ⟨hord, hx₁⟩ := layerIs_centralizer_pair_aux2 hF hQ hp hp2 hd₁B hd₁1
  obtain ⟨hh₁, hmult', hUd₁⟩ :=
    layerIs_centralizer_pair_aux3 hn hQ hp hp2 hpq hF hd hhd hh1 hU j₀ hd₁B hk0 hk1
  have hHq : CFSG.IsQuasisimple ↥(specialBlock Q (d₁ : V ≃ₗ[F] V) h) :=
    isQuasisimple_specialBlock_of_multiplicity hp hp2 hpq hx₁ hh₁ hh1 hmult' hm4
  have hHle : specialBlock Q (d₁ : V ≃ₗ[F] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hHq.1
      ((specialBlock_le_isometryCentralizer h).trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  have hNq : CFSG.IsQuasisimple
      ↥((specialBlock Q (d₁ : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHle).symm hHq
  have hcat := catalogIs_pSimple_specialBlock hp hp2 hpq hQ hord hh₁ hh1 hmult' hm4
  have hNZ := layerIs_centralizer_pair_aux4 hF hp hp2 hpq hd₁B j₀ hx₁ hk0 hh₁ hh1
  obtain ⟨A, _, hA, φ, hker⟩ := exists_solvable_ker_centralizer_pair hQ hdim hp hp2 hpq hF hd₁B j₀
    hk0 hh₁ hh1 hUd₁
  exact (layerIs_of_ker_solvable hNZ hNq φ hker hcat).1

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end

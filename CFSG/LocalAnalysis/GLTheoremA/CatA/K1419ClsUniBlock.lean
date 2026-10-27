module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDMain
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix
open Polynomial
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LieType.SemisimpleCentralizers.HeldUCD
open CFSG.LocalAnalysis.ComponentInitial

private theorem isComponentOf_subgroupOf_top' {G : Type*} [Group G] {L K : Subgroup G}
    (hL : IsComponentOf L K) : IsComponentOf (L.subgroupOf K) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.of_mathlib
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hL.1).mp hL.2.1)
  · exact (CFSG.Open.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hL.1)).2 hL.2.2

private theorem natDegree_eq_finrank_adjoinRoot {L : Type} [Field L] {f : L[X]} (hf : f ≠ 0) :
    f.natDegree = Module.finrank L (AdjoinRoot f) := by
  have h := PowerBasis.finrank (AdjoinRoot.powerBasis (K := L) hf)
  rw [AdjoinRoot.powerBasis_dim hf] at h
  exact h.symm

private theorem component_heldGU_eq_heldSU (hSU : SUComponentsTrivial)
    {a Q : ℕ} {E : Type} [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hcard : Nat.card E = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    {J : Subgroup (GL (Fin a) E)} (hJ : IsComponentOf J (heldGU a E τ hτ)) :
    J = heldSU a E τ hτ := by
  have hle : J ≤ heldSU a E τ hτ := by
    have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
    have hcomm : ⁅J, J⁆ ≤ ⁅heldGU a E τ hτ, heldGU a E τ hτ⁆ :=
      Subgroup.commutator_mono hJ.1 hJ.1
    have hGU : ⁅heldGU a E τ hτ, heldGU a E τ hτ⁆ ≤ heldSU a E τ hτ :=
      Subgroup.commutator_le.mpr fun x hx y hy => commutatorElement_mem_heldSU hx hy
    rw [Subgroup.isPerfect_iff.mp hperf] at hcomm
    exact hcomm.trans hGU
  have hsub : CFSG.Open.IsSubnormal J (heldSU a E τ hτ) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1
      (inf_le_left : heldSU a E τ hτ ≤ heldGU a E τ hτ)
    change CFSG.Open.IsSubnormal (J ⊓ heldSU a E τ hτ) (heldSU a E τ hτ) at h
    rwa [inf_eq_left.mpr hle] at h
  have hcomp : IsComponentOf J (heldSU a E τ hτ) := ⟨hle, hsub, hJ.2.2⟩
  have htop : (J.subgroupOf (heldSU a E τ hτ)) = ⊤ :=
    hSU a Q E τ hτ hcard hτQ _ (isComponentOf_subgroupOf_top' hcomp)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

private theorem component_GL_eq_statedSL (hSL : SLComponentsTrivial)
    {b : ℕ} {E : Type} [Field E] [Finite E]
    {J : Subgroup (GL (Fin b) E)} (hJ : IsComponentOf J ⊤) :
    J = StatedSL b E := by
  have hle : J ≤ StatedSL b E := by
    have hperf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ.2.2.1
    have hcomm : ⁅J, J⁆ ≤ ⁅(⊤ : Subgroup (GL (Fin b) E)), ⊤⁆ :=
      Subgroup.commutator_mono hJ.1 hJ.1
    have hGL : ⁅(⊤ : Subgroup (GL (Fin b) E)), ⊤⁆ ≤ StatedSL b E :=
      Subgroup.commutator_le.mpr fun x _ y _ => commutatorElement_mem_statedSL x y
    rw [Subgroup.isPerfect_iff.mp hperf] at hcomm
    exact hcomm.trans hGL
  have hsub : CFSG.Open.IsSubnormal J (StatedSL b E) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hJ.2.1
      (le_top : StatedSL b E ≤ ⊤)
    rwa [inf_eq_left.mpr hle] at h
  have hcomp : IsComponentOf J (StatedSL b E) := ⟨hle, hsub, hJ.2.2⟩
  have htop : (J.subgroupOf (StatedSL b E)) = ⊤ :=
    hSL b E _ (isComponentOf_subgroupOf_top' hcomp)
  exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

private theorem component_heldGU_subtype_mulEquiv_heldSU (hSU : SUComponentsTrivial)
    {a Q : ℕ} {E : Type} [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x}
    (hcard : Nat.card E = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    {J : Subgroup ↥(heldGU a E τ hτ)} (hJ : IsComponentOf J ⊤) :
    Nonempty (↥J ≃* ↥(heldSU a E τ hτ)) := by
  let g : ↥(heldGU a E τ hτ) →* GL (Fin a) E := (heldGU a E τ hτ).subtype
  have hginj : Function.Injective g := (heldGU a E τ hτ).subtype_injective
  have hJ' : IsComponentOf (J.map g) (heldGU a E τ hτ) := by
    have h := isComponentOf_map_of_injective g hginj hJ
    rw [← MonoidHom.range_eq_map] at h
    simpa [g] using h
  have hEq : J.map g = heldSU a E τ hτ :=
    component_heldGU_eq_heldSU hSU hcard hτQ hJ'
  exact ⟨(Subgroup.equivMapOfInjective J g hginj).trans (MulEquiv.subgroupCongr hEq)⟩

private theorem Vf_ne_bot
    {L : Type} [Field L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F))
    (hPf : Pmat (s : Matrix (Fin n) (Fin n) L) b F f.1 ≠ 0) : Vf s b F f.1 ≠ ⊥ := by
  intro hbot
  apply hPf
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx := Pmat_mem_Vf H f x
  rw [hbot] at hx
  have h0 : Pmat (s : Matrix (Fin n) (Fin n) L) b F f.1 *ᵥ x = 0 := by simpa using hx
  simpa [Matrix.toLin'_apply] using h0

private theorem fullW_eq_one_of_ne
    {L : Type} [Field L] [Finite L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]
    (H : PrimaryHyp τ s m F a b) (fam : (f : Activ H) → ↥(Bl H f.1)) (f0 : Activ H)
    (hfam : ∀ gA : Activ H, gA ≠ f0 → fam gA = 1)
    (h : ↥(Fset s b F)) (hh : h ≠ f0.1) (hh' : h ≠ piI H f0.1) :
    fullW H fam h = 1 := by
  by_cases hA : IsAct H h
  · rw [fullW_act H fam hA]
    have hne : (⟨h, hA⟩ : Activ H) ≠ f0 := fun he => hh (congrArg Subtype.val he)
    rw [hfam _ hne]
    rfl
  · rw [fullW_nact H fam hA]
    have hnePi : piI H h ≠ f0.1 := by
      intro he
      apply hh'
      calc h = piI H (piI H h) := (piI_piI H h).symm
        _ = piI H f0.1 := by rw [he]
    have hne : (⟨piI H h, isAct_piI H hA⟩ : Activ H) ≠ f0 :=
      fun he => hnePi (congrArg Subtype.val he)
    rw [hfam _ hne]
    simp only [Subgroup.coe_one]
    rw [natUnit_one]

private theorem fullW_apply_eq_self
    {L : Type} [Field L] [Finite L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]
    (H : PrimaryHyp τ s m F a b) (fam : (f : Activ H) → ↥(Bl H f.1)) (f0 : Activ H)
    (hfam : ∀ gA : Activ H, gA ≠ f0 → fam gA = 1)
    (h : ↥(Fset s b F)) (hh : h ≠ f0.1) (hh' : h ≠ piI H f0.1)
    (v : Vf s b F h.1) :
    ((fullW H fam h).1 v : Fin n → L) = (v : Fin n → L) := by
  rw [fullW_eq_one_of_ne H fam f0 hfam h hh hh']
  simp

private noncomputable def centralizerEquivGlin'
    {L : Type} [Field L] {n : ℕ} {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x)
    (s : GL (Fin n) L) :
    ↥(Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ) ≃*
      ↥(Glin τ (s : Matrix (Fin n) (Fin n) L)) where
  toFun g := ⟨Matrix.GeneralLinearGroup.toLin g.1,
    (mem_centralizer_heldGU_iff hτ s g.1).mp g.2⟩
  invFun h := ⟨Matrix.GeneralLinearGroup.toLin.symm h.1,
    (mem_centralizer_heldGU_iff hτ s _).mpr (by
      rw [MulEquiv.apply_symm_apply]
      exact h.2)⟩
  left_inv g := Subtype.ext (Matrix.GeneralLinearGroup.toLin.symm_apply_apply g.1)
  right_inv h := Subtype.ext (Matrix.GeneralLinearGroup.toLin.apply_symm_apply h.1)
  map_mul' g h := Subtype.ext (map_mul Matrix.GeneralLinearGroup.toLin g.1 h.1)

private theorem selfDual_unitaryBlock_mulEquiv
    {L : Type} [Field L] [Finite L] {n : ℕ} {τ : L ≃+* L} {m : ℕ}
    {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}
    (H : PrimaryHyp τ s m F a b) {f : L[X]} [Fact (Irreducible f)]
    [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hf : f ∈ F) (hPf : Pmat (s : Matrix (Fin n) (Fin n) L) b F f ≠ 0)
    (hself : adjM τ (Pmat (s : Matrix (Fin n) (Fin n) L) b F f) =
      Pmat (s : Matrix (Fin n) (Fin n) L) b F f) (Q : ℕ) (hQ : Nat.card L = Q ^ 2)
    (hτQ : ∀ x, τ x = x ^ Q) :
    ∃ (a' : ℕ) (ρE : AdjoinRoot f ≃+* AdjoinRoot f) (hρE : ∀ x, ρE (ρE x) = x),
      (∀ x : AdjoinRoot f, ρE x = x ^ (Q ^ Module.finrank L (AdjoinRoot f))) ∧
      Nat.card (AdjoinRoot f) = (Q ^ Module.finrank L (AdjoinRoot f)) ^ 2 ∧
      Nonempty (↥(unitaryBlock τ s b F f) ≃* heldGU a' (AdjoinRoot f) ρE hρE) := by
  classical
  have hdiv : f ∣ starP τ m f := dvd_starP_of_self_dual H hf hPf hself
  have hdvd : f ∣ (X ^ m - 1 : L[X]) := by
    rw [← H.hprod]
    exact Finset.dvd_prod_of_mem _ hf
  have hσσ : ∀ x, sigmaK τ m hdiv (sigmaK τ m hdiv x) = x :=
    sigmaK_sigmaK τ H.hτ H.hm hdiv hdvd
  have hσL : ∀ l : L, sigmaK τ m hdiv (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => sigmaK_of τ m hdiv l
  have hf0 : f ≠ 0 := (H.hirr f hf).ne_zero
  haveI : Module.Finite L (AdjoinRoot f) := (H.hmon f hf).finite_adjoinRoot
  haveI : Finite (AdjoinRoot f) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f)) → L)
      (Module.finBasis L (AdjoinRoot f)).equivFun.toEquiv.symm
  let σE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv (sigmaK τ m hdiv) hσσ
  obtain ⟨p, e, hp, he1, hQe, hodd, hcard, hsig⟩ :=
    sigma_eq_frobenius_pow hQ τ hτQ σE hσL hσσ
  set k := Module.finrank L (AdjoinRoot f) with hk
  have hbar_card : Nat.card (AdjoinRoot f) = p ^ (2 * (e * k)) := by
    rw [hcard, hQe, ← pow_mul]
    congr 1
    ring
  have hUFD : UnitaryFieldData p (e * k) (AdjoinRoot f) :=
    ⟨hp, Nat.mul_pos he1 hodd.pos, hbar_card⟩
  have hbar : ∀ x, hUFD.bar x = sigmaK τ m hdiv x := by
    intro x
    rw [UnitaryFieldData.bar_apply]
    have h1 := hsig x
    rw [hQe, ← pow_mul] at h1
    exact h1.symm
  have hρE : ∀ x, hUFD.bar (hUFD.bar x) = x := hUFD.bar_bar
  have hρL : ∀ l : L, hUFD.bar (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => by
    rw [hbar]
    exact hσL l
  have hherm : ∀ x y : Vf s b F f, τ (hW τ s b F f x y) = hW τ s b F f y x := by
    intro x y
    rw [hW_apply, hW_apply]
    exact hfm_symm τ H.hτ _ _
  have hadj : ∀ (c : AdjoinRoot f) (x y : Vf s b F f),
      hW τ s b F f (c • x) y = hW τ s b F f x (hUFD.bar c • y) := by
    intro c x y
    rw [hbar]
    exact hW_smul_adj H hdiv c x y
  obtain ⟨B, hsymm, hsep, hrep⟩ :=
    exists_trace_form hUFD.bar (τ : L →+* L) hρE hρL (hW τ s b F f) hherm hadj
      (hW_nondeg H hf hself)
  haveI : Module.Finite L (Vf s b F f) := inferInstance
  haveI : FiniteDimensional (AdjoinRoot f) (Vf s b F f) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f) (Vf s b F f)
  obtain ⟨e0, he0⟩ :=
    UnitaryFieldData.exists_orthonormal_basis hUFD (B := B) (LinearMap.isSymm_def.mpr hsymm) hsep
  let ρE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv hUFD.bar hρE
  obtain ⟨φ⟩ := nonempty_mulEquiv_heldGU ρE hρE B e0 he0
  have hsub : unitaryBlock τ s b F f = sesqUnitaryGroup B := by
    ext g
    rw [mem_sesqUnitaryGroup]
    exact unitary_trace_iff (hW τ s b F f) B hrep g.1
  refine ⟨Module.finrank (AdjoinRoot f) (Vf s b F f), ρE, hρE, ?_, ?_,
    ⟨(MulEquiv.subgroupCongr hsub).trans φ⟩⟩
  · intro x
    show hUFD.bar x = _
    rw [UnitaryFieldData.bar_apply, hQe, ← pow_mul]
  · rw [hcard, ← pow_mul, mul_comm]

theorem k1419ClsUniBlockPair {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (s : GL (Fin n) L) (hs : s ∈ heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0)
    (M : Subgroup (GL (Fin n) L))
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    ∃ W U : Submodule L (Fin n → L), IsCompl W U ∧ W ≠ ⊥ ∧
      (∀ g ∈ M, ∀ v ∈ U, (g : Matrix (Fin n) (Fin n) L) *ᵥ v = v) ∧
      ((∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
          (hτ' : ∀ x, τ' (τ' x) = x) (P : Polynomial L),
          2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
          Nonempty (M ≃* heldSU a E τ' hτ') ∧ Irreducible P ∧ P.natDegree = dd ∧
          (∀ w ∈ W, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P) *ᵥ w = 0)) ∨
       (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (X Y : Submodule L (Fin n → L))
          (P P' : Polynomial L),
          2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧ Nonempty (M ≃* StatedSL b E) ∧
          W = X ⊔ Y ∧ X ≠ ⊥ ∧ Y ≠ ⊥ ∧
          (∀ x ∈ X, ∀ x' ∈ X, hfm τ x x' = 0) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, hfm τ y y' = 0) ∧
          Irreducible P ∧ P.natDegree = e ∧ Irreducible P' ∧
          (∀ x ∈ X, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P) *ᵥ x = 0) ∧
          (∀ y ∈ Y, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P') *ᵥ y = 0) ∧
          P.Monic ∧ P'.Monic ∧ P ≠ P' ∧ (∃ x ∈ X, ∃ y ∈ Y, hfm τ x y ≠ 0) ∧
          Module.finrank L ↥X = e * b)) := by
  classical
  have hSU0 : SUComponentsTrivial := SUComponentsTrivial_holds
  have hSL0 : SLComponentsTrivial := SLComponentsTrivial_holds
  have hm0 : 0 < orderOf s := orderOf_pos s
  have hsm : (s : Matrix (Fin n) (Fin n) L) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hs' : adjM τ (s : Matrix (Fin n) (Fin n) L) * (s : Matrix (Fin n) (Fin n) L) = 1 :=
    mem_heldGU.mp hs
  set F : Finset L[X] := factorsOf (L := L) (orderOf s) with hF
  have hirr : ∀ f ∈ F, Irreducible f := fun f hf => factorsOf_irreducible hf
  have hmon : ∀ f ∈ F, Monic f := fun f hf => factorsOf_monic hf
  have hprod : ∏ f ∈ F, f = X ^ orderOf s - 1 := prod_factorsOf hord hm0
  have hcop : ∀ f ∈ F, ∃ u v : L[X], u * f + v * gcF F f = 1 :=
    fun f hf => isCoprime_gcF hirr hmon hf
  choose! a b hab using hcop
  let H : PrimaryHyp τ (s : Matrix (Fin n) (Fin n) L) (orderOf s) F a b :=
    ⟨hτ, hm0, hirr, hmon, hprod, hsm, hs', hab⟩
  haveI hK : ∀ f : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F),
      Fact (∀ x ∈ Vf (s : Matrix (Fin n) (Fin n) L) b F f.1,
        aeval (s : Matrix (Fin n) (Fin n) L) f.1 *ᵥ x = 0) :=
    fun f => ⟨fun x hx => aeval_factor_mulVec_eq_zero H (mem_Fset.mp f.2).1 hx⟩
  let C : Subgroup (GL (Fin n) L) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ
  let Hact : Activ H → Type := fun f => ↥(Bl H f.1)
  haveI hFinH : ∀ f : Activ H, Finite (Hact f) := fun f => finite_Bl H f.1
  let ε : ↥C ≃* (∀ f : Activ H, Hact f) :=
    (centralizerEquivGlin' hτ s).trans (glinEquivBlocks H)
  let ψ : (∀ f : Activ H, Hact f) →* GL (Fin n) L :=
    C.subtype.comp ε.symm.toMonoidHom
  have hψinj : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hrange : ψ.range = C := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      refine ⟨ε ⟨x, hx⟩, ?_⟩
      simp [ψ]
  have hMle : M ≤ ψ.range := by
    rw [hrange]
    exact hM.1
  have hMmap : (M.comap ψ).map ψ = M := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hMle]
  have hM'top : IsComponentOf (M.comap ψ) ⊤ := by
    apply isComponentOf_of_map_injective ψ hψinj
    rw [hMmap, ← MonoidHom.range_eq_map, hrange]
    exact hM
  obtain ⟨f0, hf0⟩ := exists_factor_of_isComponentOf_top (H := Hact) hM'top
  set f : L[X] := f0.1.1 with hfdef
  have hfF : f ∈ F := (mem_Fset.mp f0.1.2).1
  have hPf : Pmat (s : Matrix (Fin n) (Fin n) L) b F f ≠ 0 := (mem_Fset.mp f0.1.2).2
  have hfix_block : ∀ (m : GL (Fin n) L), m ∈ M →
      ∀ (h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F)),
      h ≠ f0.1 → h ≠ piI H f0.1 →
      ∀ v : Vf (s : Matrix (Fin n) (Fin n) L) b F h.1,
      (m : Matrix (Fin n) (Fin n) L) *ᵥ (v : Fin n → L) = (v : Fin n → L) := by
    intro m hm h hh hh' v
    have hmC : m ∈ C := hM.1 hm
    obtain ⟨w, hwm⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hmC)
    let c : ↥C := ⟨m, hmC⟩
    have hc_eq : c = ε.symm w := Subtype.ext hwm.symm
    have hec : ε c = w := by rw [hc_eq, MulEquiv.apply_symm_apply]
    have hwmem : w ∈ M.comap ψ := by
      rw [Subgroup.mem_comap, hwm]
      exact hm
    have hwfac : w ∈ factorSub f0 := hf0 hwmem
    have hfam : ∀ gA : Activ H, gA ≠ f0 →
        (theta H (centralizerEquivGlin' hτ s c)) gA = 1 := by
      intro gA hgA
      have hfam_eq : theta H (centralizerEquivGlin' hτ s c) = ε c := rfl
      rw [hfam_eq, hec]
      exact mem_factorSub.mp hwfac gA hgA
    have hFW : ((fullW H (theta H (centralizerEquivGlin' hτ s c)) h).1 v : Fin n → L) =
        (v : Fin n → L) :=
      fullW_apply_eq_self H (theta H (centralizerEquivGlin' hτ s c)) f0 hfam h hh hh' v
    have hval : (m : Matrix (Fin n) (Fin n) L) *ᵥ (v : Fin n → L) =
        ((fullW H (theta H (centralizerEquivGlin' hτ s c)) h).1 v : Fin n → L) := by
      rw [← toLin_val_apply m (v : Fin n → L)]
      have hgl : centralizerEquivGlin' hτ s c =
          rhoG H (theta H (centralizerEquivGlin' hτ s c)) := by
        rw [rhoG_theta]
      calc (Matrix.GeneralLinearGroup.toLin m).val (v : Fin n → L)
          = (centralizerEquivGlin' hτ s c).1.val (v : Fin n → L) := by
              with_unfolding_all rfl
        _ = (rhoG H (theta H (centralizerEquivGlin' hτ s c))).1.val (v : Fin n → L) :=
            congrArg (fun x => x.1.val (v : Fin n → L)) hgl
        _ = rhoU H (fullW H (theta H (centralizerEquivGlin' hτ s c))) (v : Fin n → L) := rfl
        _ = ((fullW H (theta H (centralizerEquivGlin' hτ s c)) h).1 v : Fin n → L) :=
            rhoU_apply_block H (fullW H (theta H (centralizerEquivGlin' hτ s c))) h v
    rw [hval, hFW]
  let Fsub : Subgroup (∀ g : Activ H, Hact g) := factorSub f0
  let ρF : ↥Fsub ≃* Hact f0 :=
    { toFun := fun w => w.1 f0
      invFun := fun x => ⟨MonoidHom.mulSingle Hact f0 x, by
        dsimp only [Fsub]
        rw [mem_factorSub]
        intro j hj
        rw [MonoidHom.mulSingle_apply]
        simp [Pi.mulSingle_apply, hj]⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext j
        by_cases hj : j = f0
        · subst hj
          simp [MonoidHom.mulSingle_apply]
        · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, hj,
            mem_factorSub.mp w.2 j hj]
      right_inv := by
        intro x
        simp [MonoidHom.mulSingle_apply]
      map_mul' := fun x y => rfl }
  let Psub : Subgroup (∀ g : Activ H, Hact g) := M.comap ψ
  have hPsubcomp : IsComponentOf Psub ⊤ := by simpa [Psub] using hM'top
  have hPsubF : IsComponentOf (Psub.subgroupOf Fsub) ⊤ := by
    apply CFSG.ComponentClassification.LocalComponents.of_overgroup hPsubcomp
    simpa [Fsub, Psub] using hf0
  let M'' : Subgroup (Hact f0) := (Psub.subgroupOf Fsub).map ρF.toMonoidHom
  have hM''comp : IsComponentOf M'' ⊤ := by
    have h := isComponentOf_map_of_injective ρF.toMonoidHom ρF.injective hPsubF
    have htop : (⊤ : Subgroup ↥Fsub).map ρF.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact ρF.surjective
    rw [htop] at h
    exact h
  let eM1 : ↥M ≃* ↥Psub :=
    (MulEquiv.subgroupCongr hMmap).symm.trans
      (Subgroup.equivMapOfInjective Psub ψ hψinj).symm
  let eM2 : ↥Psub ≃* ↥(Psub.subgroupOf Fsub) :=
    (Subgroup.subgroupOfEquivOfLe hf0).symm
  let eM3 : ↥(Psub.subgroupOf Fsub) ≃* ↥M'' :=
    Subgroup.equivMapOfInjective (Psub.subgroupOf Fsub) ρF.toMonoidHom ρF.injective
  let eM : ↥M ≃* ↥M'' := eM1.trans (eM2.trans eM3)
  by_cases hself : piI H f0.1 = f0.1
  ·
    have hselfA : adjM τ (Pmat (s : Matrix (Fin n) (Fin n) L) b F f) =
        Pmat (s : Matrix (Fin n) (Fin n) L) b F f := by
      have h := adjM_piI H f0.1
      rw [hself] at h
      simpa [hfdef] using h
    haveI : Fact (Irreducible f) := ⟨hirr f hfF⟩
    haveI : Fact (∀ x ∈ Vf (s : Matrix (Fin n) (Fin n) L) b F f,
        aeval (s : Matrix (Fin n) (Fin n) L) f *ᵥ x = 0) :=
      ⟨fun x hx => aeval_factor_mulVec_eq_zero H hfF hx⟩
    obtain ⟨a', ρE, hρE, hτ'Q, hcardE, ⟨φ0⟩⟩ :=
      selfDual_unitaryBlock_mulEquiv H hfF hPf hselfA Q hL hτQ
    have hBl : Bl H f0.1 = unitaryBlock τ (s : Matrix (Fin n) (Fin n) L) b F f :=
      Bl_of_selfDual H hself
    let φGU : ↥(Bl H f0.1) ≃* heldGU a' (AdjoinRoot f) ρE hρE :=
      (MulEquiv.subgroupCongr hBl).trans φ0
    let J : Subgroup ↥(heldGU a' (AdjoinRoot f) ρE hρE) := M''.map φGU.toMonoidHom
    have hJcomp : IsComponentOf J ⊤ := by
      have h := isComponentOf_map_of_injective φGU.toMonoidHom φGU.injective hM''comp
      have htop : (⊤ : Subgroup (Hact f0)).map φGU.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        exact φGU.surjective
      simpa [J, htop] using h
    obtain ⟨eJ⟩ := component_heldGU_subtype_mulEquiv_heldSU hSU0
      (Q := Q ^ Module.finrank L (AdjoinRoot f)) hcardE hτ'Q hJcomp
    have eSU : ↥M ≃* ↥(heldSU a' (AdjoinRoot f) ρE hρE) :=
      (eM.trans (Subgroup.equivMapOfInjective M'' φGU.toMonoidHom φGU.injective)).trans eJ
    have ha2 : 2 ≤ a' := by
      by_contra hlt
      have hle1 : a' ≤ 1 := by omega
      exact absurd hM.2.2 (not_isQuasisimple_of_mulEquiv eSU fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one hle1 (x : GL (Fin a') (AdjoinRoot f))
          (y : GL (Fin a') (AdjoinRoot f))))
    have hdeg : f.natDegree = Module.finrank L (AdjoinRoot f) :=
      natDegree_eq_finrank_adjoinRoot (H.hirr f hfF).ne_zero
    let Qlin : (Fin n → L) →ₗ[L] (Fin n → L) :=
      Matrix.toLin' (Pmat (s : Matrix (Fin n) (Fin n) L) b F f)
    have hQidem : IsIdempotentElem Qlin := by
      show Qlin * Qlin = Qlin
      simp only [Qlin]
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, H.Pmat_idem hfF]
    let W : Submodule L (Fin n → L) := LinearMap.range Qlin
    let U : Submodule L (Fin n → L) := LinearMap.ker Qlin
    have hW : W = Vf (s : Matrix (Fin n) (Fin n) L) b F f := by
      ext x
      rw [show x ∈ W ↔ Qlin x = x from LinearMap.IsIdempotentElem.mem_range_iff hQidem,
        show Qlin x = Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ x from rfl,
        mem_Vf]
    have hXne : Vf (s : Matrix (Fin n) (Fin n) L) b F f ≠ ⊥ := Vf_ne_bot H f0.1 hPf
    have hWne : W ≠ ⊥ := by rw [hW]; exact hXne
    have hfixU : ∀ g ∈ M, ∀ v ∈ U,
        (g : Matrix (Fin n) (Fin n) L) *ᵥ v = v := by
      intro m hm v hv
      have hv0 : Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ v = 0 := by
        have hq : Qlin v = 0 := hv
        simpa [Qlin, Matrix.toLin'_apply] using hq
      have hsum : v = ∑ h ∈ (Finset.univ.erase f0.1),
          Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := by
        conv_lhs => rw [sum_Pmat_index H v]
        exact (Finset.sum_erase (s := Finset.univ)
          (f := fun h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F) =>
            Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v) hv0).symm
      rw [hsum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      have hh1 : h ≠ f0.1 := Finset.ne_of_mem_erase hh
      have hh2 : h ≠ piI H f0.1 := by rw [hself]; exact hh1
      exact hfix_block m hm h hh1 hh2
        ⟨Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v, Pmat_mem_Vf H h v⟩
    refine ⟨W, U, LinearMap.IsIdempotentElem.isCompl hQidem, hWne, hfixU, Or.inl ?_⟩
    refine ⟨a', Module.finrank L (AdjoinRoot f), AdjoinRoot f, inferInstance, inferInstance,
      ρE, hρE, f, ha2, hτ'Q, hcardE, ⟨eSU⟩, hirr f hfF, hdeg, ?_⟩
    intro w hw
    rw [hW] at hw
    exact aeval_factor_mulVec_eq_zero H hfF hw
  ·
    have hrep : IsRep H f0.1 := f0.2.resolve_left hself
    have hBl : Bl H f0.1 = ⊤ := Bl_of_isRep H hrep
    haveI : Fact (Irreducible f) := ⟨hirr f hfF⟩
    haveI : Module.Finite L (AdjoinRoot f) := (hmon f hfF).finite_adjoinRoot
    haveI : Finite (AdjoinRoot f) :=
      Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f)) → L)
        (Module.finBasis L (AdjoinRoot f)).equivFun.toEquiv.symm
    haveI : Module.Finite (AdjoinRoot f)
        (Vf (s : Matrix (Fin n) (Fin n) L) b F f) :=
      Module.Finite.of_restrictScalars_finite L (AdjoinRoot f)
        (Vf (s : Matrix (Fin n) (Fin n) L) b F f)
    let bdim : ℕ := Module.finrank (AdjoinRoot f)
      (Vf (s : Matrix (Fin n) (Fin n) L) b F f)
    let φGL : Hact f0 ≃* GL (Fin bdim) (AdjoinRoot f) :=
      (MulEquiv.subgroupCongr hBl).trans (Subgroup.topEquiv.trans
        (Matrix.GeneralLinearGroup.toLin'
          (Module.finBasis (AdjoinRoot f)
            (Vf (s : Matrix (Fin n) (Fin n) L) b F f))).symm)
    let J : Subgroup (GL (Fin bdim) (AdjoinRoot f)) := M''.map φGL.toMonoidHom
    have hJcomp : IsComponentOf J ⊤ := by
      have h := isComponentOf_map_of_injective φGL.toMonoidHom φGL.injective hM''comp
      have htop : (⊤ : Subgroup (Hact f0)).map φGL.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        exact φGL.surjective
      simpa [J, htop] using h
    have hJeq : J = StatedSL bdim (AdjoinRoot f) :=
      component_GL_eq_statedSL hSL0 hJcomp
    have eSL : ↥M ≃* ↥(StatedSL bdim (AdjoinRoot f)) :=
      (eM.trans (Subgroup.equivMapOfInjective M'' φGL.toMonoidHom φGL.injective)).trans
        (MulEquiv.subgroupCongr hJeq)
    have hb2 : 2 ≤ bdim := by
      by_contra hlt
      have hle1 : bdim ≤ 1 := by omega
      exact absurd hM.2.2 (not_isQuasisimple_of_mulEquiv eSL fun x y =>
        Subtype.ext (by
          have hx1 := eq_one_of_mem_statedSL_of_le_one hle1 x.2
          have hy1 := eq_one_of_mem_statedSL_of_le_one hle1 y.2
          simp only [Subgroup.coe_mul, hx1, hy1, one_mul, mul_one]))
    have hcardE : Nat.card (AdjoinRoot f) = Q ^ (2 * f.natDegree) := by
      let pb := AdjoinRoot.powerBasis (K := L) (H.hirr f hfF).ne_zero
      have hdim : pb.dim = f.natDegree :=
        AdjoinRoot.powerBasis_dim (H.hirr f hfF).ne_zero
      have hfin : Nat.card (Fin pb.dim) = pb.dim := by simp
      rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, hfin, hdim, hL,
        ← pow_mul]
    let Qlin : (Fin n → L) →ₗ[L] (Fin n → L) :=
      Matrix.toLin' (Pmat (s : Matrix (Fin n) (Fin n) L) b F f +
        Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1)
    have hne : f ≠ (piI H f0.1).1 := fun h => hself (Subtype.ext h).symm
    have hfF' : (piI H f0.1).1 ∈ F := (mem_Fset.mp (piI H f0.1).2).1
    have hPf' : Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 ≠ 0 :=
      (mem_Fset.mp (piI H f0.1).2).2
    have hQmat : (Pmat (s : Matrix (Fin n) (Fin n) L) b F f +
        Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1) *
        (Pmat (s : Matrix (Fin n) (Fin n) L) b F f +
          Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1) =
        Pmat (s : Matrix (Fin n) (Fin n) L) b F f +
          Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 := by
      rw [add_mul, mul_add, mul_add, H.Pmat_idem hfF, H.Pmat_idem hfF',
        H.Pmat_orth hfF hfF' hne, H.Pmat_orth hfF' hfF (Ne.symm hne)]
      abel
    have hQidem : IsIdempotentElem Qlin := by
      show Qlin * Qlin = Qlin
      simp only [Qlin]
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQmat]
    let W : Submodule L (Fin n → L) := LinearMap.range Qlin
    let U : Submodule L (Fin n → L) := LinearMap.ker Qlin
    have hW : W = Vf (s : Matrix (Fin n) (Fin n) L) b F f ⊔
        Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 := by
      ext x
      rw [show x ∈ W ↔ Qlin x = x from LinearMap.IsIdempotentElem.mem_range_iff hQidem]
      constructor
      · intro hx
        have hx' : x = Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ x +
            Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ x := by
          calc x = Qlin x := hx.symm
            _ = Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ x +
                Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ x := by
                simp [Qlin, Matrix.toLin'_apply, Matrix.add_mulVec]
        rw [hx']
        exact Submodule.add_mem_sup (Pmat_mem_Vf H f0.1 x)
          (Pmat_mem_Vf H (piI H f0.1) x)
      · intro hx
        let T : Submodule L (Fin n → L) :=
          LinearMap.ker (Qlin - (LinearMap.id : (Fin n → L) →ₗ[L] (Fin n → L)))
        have hT : Vf (s : Matrix (Fin n) (Fin n) L) b F f ⊔
            Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 ≤ T := by
          refine sup_le ?_ ?_
          · intro y hy
            have hy' : Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ y = y :=
              mem_Vf.mp hy
            have hz : Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ y = 0 :=
              Pmat_mulVec_of_mem_ne H (f := (piI H f0.1).1) (g := f0.1.1) hfF' hfF (Ne.symm hne) hy
            show (Qlin - (LinearMap.id : (Fin n → L) →ₗ[L] (Fin n → L))) y = 0
            simp only [Qlin, Matrix.toLin'_apply, Matrix.add_mulVec, hy', hz, add_zero,
              LinearMap.sub_apply, LinearMap.id_apply, sub_self]
          · intro y hy
            have hy' : Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ y = y :=
              mem_Vf.mp hy
            have hz : Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ y = 0 :=
              Pmat_mulVec_of_mem_ne H (f := f0.1.1) (g := (piI H f0.1).1) hfF hfF' hne hy
            show (Qlin - (LinearMap.id : (Fin n → L) →ₗ[L] (Fin n → L))) y = 0
            simp only [Qlin, Matrix.toLin'_apply, Matrix.add_mulVec, hy', hz, zero_add,
              LinearMap.sub_apply, LinearMap.id_apply, sub_self]
        have hxT := hT hx
        have hxeq : (Qlin - (LinearMap.id : (Fin n → L) →ₗ[L] (Fin n → L))) x = 0 := hxT
        simpa [LinearMap.sub_apply, sub_eq_zero] using hxeq
    have hXne : Vf (s : Matrix (Fin n) (Fin n) L) b F f ≠ ⊥ := Vf_ne_bot H f0.1 hPf
    have hYne : Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 ≠ ⊥ :=
      Vf_ne_bot H (piI H f0.1) hPf'
    have hWne : W ≠ ⊥ := by
      intro hbot
      have hle : Vf (s : Matrix (Fin n) (Fin n) L) b F f ⊔
          Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 ≤ ⊥ := by
        rw [← hW, hbot]
      exact hXne (le_bot_iff.mp (le_trans le_sup_left hle))
    have hfixU : ∀ g ∈ M, ∀ v ∈ U,
        (g : Matrix (Fin n) (Fin n) L) *ᵥ v = v := by
      intro m hm v hv
      have hv0 : Pmat (s : Matrix (Fin n) (Fin n) L) b F f *ᵥ v +
          Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ v = 0 := by
        have hq : Qlin v = 0 := hv
        simpa [Qlin, Matrix.toLin'_apply, Matrix.add_mulVec] using hq
      have hmem_pi : piI H f0.1 ∈ Finset.univ.erase f0.1 :=
        Finset.mem_erase.mpr ⟨hself, Finset.mem_univ _⟩
      have hsum : v = ∑ h ∈ (Finset.univ.erase f0.1).erase (piI H f0.1),
          Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := by
        have h1 := Finset.add_sum_erase (s := Finset.univ)
          (f := fun h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F) =>
            Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v)
          (a := f0.1) (Finset.mem_univ _)
        have h2 := Finset.add_sum_erase (s := Finset.univ.erase f0.1)
          (f := fun h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F) =>
            Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v)
          (a := piI H f0.1) hmem_pi
        have htotal : (∑ h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F),
            Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v) =
            ∑ h ∈ (Finset.univ.erase f0.1).erase (piI H f0.1),
              Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := by
          calc (∑ h : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F),
                Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v)
              = Pmat (s : Matrix (Fin n) (Fin n) L) b F f0.1.1 *ᵥ v +
                  ∑ h ∈ Finset.univ.erase f0.1,
                    Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := h1.symm
            _ = Pmat (s : Matrix (Fin n) (Fin n) L) b F f0.1.1 *ᵥ v +
                  (Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ v +
                    ∑ h ∈ (Finset.univ.erase f0.1).erase (piI H f0.1),
                      Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v) := by rw [h2]
            _ = (Pmat (s : Matrix (Fin n) (Fin n) L) b F f0.1.1 *ᵥ v +
                  Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ v) +
                    ∑ h ∈ (Finset.univ.erase f0.1).erase (piI H f0.1),
                      Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := by abel
            _ = ∑ h ∈ (Finset.univ.erase f0.1).erase (piI H f0.1),
                  Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v := by
                rw [show Pmat (s : Matrix (Fin n) (Fin n) L) b F f0.1.1 *ᵥ v +
                    Pmat (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1 *ᵥ v = 0
                      from hv0, zero_add]
        exact (sum_Pmat_index H v).trans htotal
      rw [hsum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun h hh => ?_
      have hh1 : h ≠ f0.1 := by
        have hmem : h ∈ Finset.univ.erase f0.1 := Finset.mem_of_mem_erase hh
        exact Finset.ne_of_mem_erase hmem
      have hh2 : h ≠ piI H f0.1 := Finset.ne_of_mem_erase hh
      exact hfix_block m hm h hh1 hh2
        ⟨Pmat (s : Matrix (Fin n) (Fin n) L) b F h.1 *ᵥ v, Pmat_mem_Vf H h v⟩
    have hpair : ∃ x ∈ Vf (s : Matrix (Fin n) (Fin n) L) b F f,
        ∃ y ∈ Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1, hfm τ x y ≠ 0 := by
      obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
      obtain ⟨y', hxy'⟩ : ∃ y', hfm τ x y' ≠ 0 := by
        by_contra h
        push Not at h
        exact hx0 (hfm_nondeg τ x h)
      have hsplit : hfm τ x y' = ∑ g : ↥(Fset (s : Matrix (Fin n) (Fin n) L) b F),
          hfm τ x (Pmat (s : Matrix (Fin n) (Fin n) L) b F g.1 *ᵥ y') := by
        rw [← hfm_sum_right]
        exact congrArg (hfm τ x) (sum_Pmat_index H y')
      by_contra hno
      push Not at hno
      apply hxy'
      rw [hsplit]
      refine Finset.sum_eq_zero fun g _ => ?_
      by_cases hg : g = piI H f0.1
      · subst hg
        exact hno x hxX _ (Pmat_mem_Vf H (piI H f0.1) y')
      · exact hfm_block_zero H f0.1 g hg hxX (Pmat_mem_Vf H g y')
    have hfin : Module.finrank L ↥(Vf (s : Matrix (Fin n) (Fin n) L) b F f) =
        f.natDegree * bdim := by
      rw [← Module.finrank_mul_finrank L (AdjoinRoot f) ↥(Vf (s : Matrix (Fin n) (Fin n) L) b F f),
        natDegree_eq_finrank_adjoinRoot (H.hirr f hfF).ne_zero]
    refine ⟨W, U, LinearMap.IsIdempotentElem.isCompl hQidem, hWne, hfixU, Or.inr ?_⟩
    refine ⟨bdim, f.natDegree, AdjoinRoot f, inferInstance, inferInstance,
      Vf (s : Matrix (Fin n) (Fin n) L) b F f,
      Vf (s : Matrix (Fin n) (Fin n) L) b F (piI H f0.1).1,
      f, (piI H f0.1).1, hb2, hcardE, ⟨eSL⟩, hW, hXne, hYne, ?_, ?_,
      hirr f hfF, rfl, hirr _ hfF', ?_, ?_, hmon f hfF, hmon _ hfF', hne, hpair, hfin⟩
    · intro x hx x' hx'
      exact hfm_block_zero H f0.1 f0.1 (fun h => hself h.symm) hx hx'
    · intro y hy y' hy'
      exact hfm_block_zero H (piI H f0.1) (piI H f0.1)
        (fun h => hself (by rw [piI_piI] at h; exact h)) hy hy'
    · intro x hx
      exact aeval_factor_mulVec_eq_zero H hfF hx
    · intro y hy
      exact aeval_factor_mulVec_eq_zero H hfF' hy

theorem k1419ClsUniBlock {L : Type} [Field L] [Finite L] {n Q : ℕ} {τ : L ≃+* L}
    (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hL : Nat.card L = Q ^ 2)
    (s : GL (Fin n) L) (hs : s ∈ heldGU n L τ hτ) (hord : (orderOf s : L) ≠ 0)
    (M : Subgroup (GL (Fin n) L))
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    ∃ W U : Submodule L (Fin n → L), IsCompl W U ∧ W ≠ ⊥ ∧
      (∀ g ∈ M, ∀ v ∈ U, (g : Matrix (Fin n) (Fin n) L) *ᵥ v = v) ∧
      ((∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
          (hτ' : ∀ x, τ' (τ' x) = x) (P : Polynomial L),
          2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
          Nonempty (M ≃* heldSU a E τ' hτ') ∧ Irreducible P ∧ P.natDegree = dd ∧
          (∀ w ∈ W, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P) *ᵥ w = 0)) ∨
       (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (X Y : Submodule L (Fin n → L))
          (P P' : Polynomial L),
          2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧ Nonempty (M ≃* StatedSL b E) ∧
          W = X ⊔ Y ∧ X ≠ ⊥ ∧ Y ≠ ⊥ ∧
          (∀ x ∈ X, ∀ x' ∈ X, hfm τ x x' = 0) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, hfm τ y y' = 0) ∧
          Irreducible P ∧ P.natDegree = e ∧ Irreducible P' ∧
          (∀ x ∈ X, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P) *ᵥ x = 0) ∧
          (∀ y ∈ Y, (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) P') *ᵥ y = 0))) := by
  obtain ⟨W, U, hWU, hW, hfix, hbr⟩ := k1419ClsUniBlockPair hτ hτQ hL s hs hord M hM
  refine ⟨W, U, hWU, hW, hfix, ?_⟩
  rcases hbr with hsd | ⟨b, e, E, hE, hEf, X, Y, P, P', hb, hcard, hMe, hWXY, hX, hY, hXi, hYi,
    hP, hPe, hP', hPX, hPY, -⟩
  · exact Or.inl hsd
  · exact Or.inr ⟨b, e, E, hE, hEf, X, Y, P, P', hb, hcard, hMe, hWXY, hX, hY, hXi, hYi,
      hP, hPe, hP', hPX, hPY⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419

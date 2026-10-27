module

public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.Adapters.CatalogueFieldBridges.Linear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial

private theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux1 {X : Type*} [Group X]
    (h : CFSG.IsQuasisimple X) : CFSG.Open.IsQuasisimple X :=
  ⟨@Group.IsPerfect.commutator_eq_top _ _ h.1, h.2.1⟩

private theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux2 {ℓ f : ℕ} {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ f E) {M : Type} [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] {B : M →ₛₗ[hE.bar] M →ₗ[E] E} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) {k p : ℕ} (hdim : finrank E M = k) (hk2 : 2 ≤ k)
    (hpq : p ∣ ℓ ^ f + 1) : p ∣ Nat.card ↥(sesqSpecialUnitaryGroup B) := by
  have hord := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hdim (by omega)).2.1
  have hpZ : (p : ℤ) ∣ ((ℓ ^ f : ℤ) + 1) := by exact_mod_cast hpq
  have hfac : (p : ℤ) ∣ ((ℓ ^ f : ℤ) ^ 2 - (-1 : ℤ) ^ 2) := by
    have h : ((ℓ ^ f : ℤ) ^ 2 - (-1 : ℤ) ^ 2) =
        ((ℓ ^ f : ℤ) + 1) * ((ℓ ^ f : ℤ) - 1) := by ring
    rw [h]
    exact dvd_mul_of_dvd_left hpZ _
  have hprod : (p : ℤ) ∣ ∏ i ∈ Finset.Icc 2 k,
      (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i) := by
    have hmem : 2 ∈ Finset.Icc 2 k := Finset.mem_Icc.2 ⟨le_rfl, hk2⟩
    have hdvd2 := Finset.dvd_prod_of_mem
      (fun i : ℕ => (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1 : ℤ) ^ i)) hmem
    have hfac' : (p : ℤ) ∣ (((ℓ ^ f : ℕ) : ℤ) ^ 2 - (-1 : ℤ) ^ 2) := by
      simpa only [Nat.cast_pow] using hfac
    exact dvd_trans hfac' hdvd2
  have hZ : (p : ℤ) ∣ (Nat.card ↥(sesqSpecialUnitaryGroup B) : ℤ) := by
    rw [hord]
    exact Dvd.dvd.mul_left hprod _
  exact_mod_cast hZ

private theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux3 {ℓ f : ℕ} {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ f E) {M : Type} [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] {B : M →ₛₗ[hE.bar] M →ₗ[E] E} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) {k : ℕ} (hdim : finrank E M = k)
    (hk : 4 ≤ k ∨ ((k = 2 ∨ k = 3) ∧ 4 ≤ ℓ ^ f)) (hk3 : 3 ≤ k) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) : catalogIs (PSimple p (sesqSpecialUnitaryGroup B)) (isUnA k (ℓ ^ f)) := by
  classical
  haveI : Finite E := hE.finite
  haveI : Finite M := Module.finite_of_finite E
  have hne : (k, ℓ ^ f) ≠ (3, 2) := by
    intro h
    rw [Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩
    rcases hk with hk4 | ⟨hk23, hq4⟩
    · omega
    · rcases hk23 with hk2 | hk3' <;> omega
  have hq : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hE hBs
      hBl (by rw [hdim]; exact hk3) (by rw [hdim]; exact hne)
  have hdvd := catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux2 hE hBs hBl hdim
    (by omega) hpq
  have hJ := H81Orth.centerQuotEquivPSimple_of_dvd_card hp
    (catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux1 hq) hdvd
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hBs hBl
  let e' : Module.Basis (Fin k) E M := e.reindex (finCongr hdim)
  have he' : ∀ i j, B (e' i) (e' j) = ((1 : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j := by
    intro i j
    simp only [e', Module.Basis.reindex_apply, he, Units.val_one, Matrix.one_apply,
      (finCongr hdim).symm.injective.eq_iff]
  obtain ⟨φ₁⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e' he'
  have hS := CFSG.ComponentClassification.Burgoyne.U.statedSU_eq_gramSU hE (n := k)
  let ψ : ↥(StatedSU k (ℓ ^ f) E) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MulEquiv.subgroupCongr hS).trans φ₁.symm
  let ψq : ↥(StatedSU k (ℓ ^ f) E) ⧸ Subgroup.center ↥(StatedSU k (ℓ ^ f) E) ≃*
      ↥(sesqSpecialUnitaryGroup B) ⧸ Subgroup.center ↥(sesqSpecialUnitaryGroup B) :=
    QuotientGroup.congr _ _ ψ (Subgroup.map_center_eq ψ)
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = (ℓ ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hE.card, ← pow_mul, mul_comm]
  obtain ⟨q', hv, -, hq'c, ⟨χ⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      (K := E) (m := k) (q := ℓ ^ f) hcardE hk3 hne
  let i : TauCeti.CFSGIndex := .lie ⟨.twistedA (k - 1) q', hv⟩
  have hi : isUnA k (ℓ ^ f) i := Or.inl ⟨by omega, hq'c⟩
  exact ⟨i, hi, ⟨hJ.symm.trans (ψq.symm.trans χ)⟩⟩

private theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux4 {F : Type} [Field F]
    [Finite F] (hF : 4 ≤ Nat.card F) :
    catalogIs (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (isLnA 2 (Nat.card F)) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rcases eq_or_ne (Nat.card F) 4 with h4 | h4
  · obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_mulEquiv_alternating_five
      (k := F) (Or.inl h4)
    let i : TauCeti.CFSGIndex := .alternating 5 (by norm_num)
    have hi : isLnA 2 (Nat.card F) i := Or.inr (Or.inl ⟨rfl, Or.inl h4, rfl⟩)
    exact ⟨i, hi, ⟨e⟩⟩
  rcases eq_or_ne (Nat.card F) 5 with h5 | h5
  · obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_mulEquiv_alternating_five
      (k := F) (Or.inr h5)
    let i : TauCeti.CFSGIndex := .alternating 5 (by norm_num)
    have hi : isLnA 2 (Nat.card F) i := Or.inr (Or.inl ⟨rfl, Or.inr h5, rfl⟩)
    exact ⟨i, hi, ⟨e⟩⟩
  rcases eq_or_ne (Nat.card F) 9 with h9 | h9
  · obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_psl2_nine_mulEquiv_alternating_six
      (k := F) h9
    let i : TauCeti.CFSGIndex := .alternating 6 (by norm_num)
    have hi : isLnA 2 (Nat.card F) i := Or.inr (Or.inr (Or.inl ⟨rfl, h9, rfl⟩))
    exact ⟨i, hi, ⟨e⟩⟩
  · haveI : CharP F (ringChar F) := ringChar.charP F
    obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
    let q : TauCeti.PrimePower := ⟨ringChar F, (n : ℕ), hp, n.pos⟩
    have hqc : q.card = Nat.card F := by
      simp only [q, TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card]
      rw [← hcard]
    have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff]
      refine ⟨?_, ?_⟩
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        exact ⟨le_rfl, fun _ => by rw [hqc]; exact hF⟩
      · rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        rintro (⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h4 (hqc.symm.trans h)
        · exact h5 (hqc.symm.trans h)
        · exact h9 (hqc.symm.trans h)
        · omega
        · omega
    obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
      (n := 1) q hv hqc.symm
    let i : TauCeti.CFSGIndex := .lie ⟨.A 1 q, hv⟩
    have hi : isLnA 2 (Nat.card F) i := Or.inl ⟨rfl, hqc⟩
    exact ⟨i, hi,
      ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 F).trans e⟩⟩

private theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux5 {ℓ f : ℕ} {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ f E) {M : Type} [AddCommGroup M] [Module E M]
    [FiniteDimensional E M] {B : M →ₛₗ[hE.bar] M →ₗ[E] E} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) (hdim : finrank E M = 2) (hq4 : 4 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) :
    catalogIs (PSimple p (sesqSpecialUnitaryGroup B)) (isUnA 2 (ℓ ^ f)) := by
  classical
  haveI : Finite E := hE.finite
  haveI : Finite M := Module.finite_of_finite E
  have hq : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
    CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hE hBs hBl hdim hq4
  have hdvd := catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux2 hE hBs hBl hdim
    (by omega) hpq
  have hJ := H81Orth.centerQuotEquivPSimple_of_dvd_card hp
    (catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux1 hq) hdvd
  obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hBs hBl hdim
  let ψq : ↥(sesqSpecialUnitaryGroup B) ⧸ Subgroup.center ↥(sesqSpecialUnitaryGroup B) ≃*
      Matrix.SpecialLinearGroup (Fin 2) hE.fixedField ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) hE.fixedField) :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  have hFcard : Nat.card hE.fixedField = ℓ ^ f := hE.card_fixedField
  have hcat := catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux4 (F := hE.fixedField)
    (by rw [hFcard]; exact hq4)
  rw [hFcard] at hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  exact ⟨i, Or.inr ⟨rfl, hi⟩, ⟨hJ.symm.trans (ψq.trans e)⟩⟩

theorem catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {M : Type} [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    {B : M →ₛₗ[hE.bar] M →ₗ[E] E} (hBs : B.IsSymm) (hBl : B.SeparatingLeft) {k : ℕ}
    (hdim : finrank E M = k) (hk : 4 ≤ k ∨ ((k = 2 ∨ k = 3) ∧ 4 ≤ ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) :
    catalogIs (PSimple p (sesqSpecialUnitaryGroup B)) (isUnA k (ℓ ^ f)) := by
  classical
  haveI : Finite E := hE.finite
  haveI : Finite M := Module.finite_of_finite E
  by_cases hk3 : 3 ≤ k
  · exact catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux3 hE hBs hBl hdim hk hk3 hp hpq
  · have hk2 : k = 2 := by
      rcases hk with hk4 | ⟨hk23, -⟩
      · omega
      · rcases hk23 with h2 | h3 <;> omega
    subst hk2
    have hq4 : 4 ≤ ℓ ^ f := by
      rcases hk with h4 | ⟨h23, hq4⟩
      · omega
      · exact hq4
    exact catalogIs_pSimple_sesqSpecialUnitaryGroup_isUnA_gen_aux5 hE hBs hBl hdim hq4 hp hpq

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end

module

public import CFSG.LinearAlgebra.LinearGroups.SLConjugationKer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm
import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofL3

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LocalAnalysis.GLTheoremA.FQ

private lemma frobenius_sq {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q) : σ * σ = 1 := by
  ext c
  change σ (σ c) = c
  haveI : Fintype F := Fintype.ofFinite F
  have hqq : q * q = Nat.card F := by rw [← pow_two, hF]
  rw [hσ, hσ, ← pow_mul, hqq, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

private lemma frobenius_ne_one {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (hF : Nat.card F = q ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q) : σ ≠ 1 := by
  intro h1
  have hfix : ∀ c : F, c ^ q = c := fun c => by rw [← hσ c, h1]; rfl
  haveI : Fintype F := Fintype.ofFinite F
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial F).natDegree = q := by
    have hlt : (Polynomial.X : Polynomial F).natDegree <
        (Polynomial.X ^ q : Polynomial F).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      omega
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hp0 : (Polynomial.X ^ q - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ q - Polynomial.X : Polynomial F).roots := by
    intro c _
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    exact hfix c
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hdeg, ← Nat.card_eq_fintype_card, hF] at hle
  nlinarith [hq]

private lemma natCard_fixF_eq {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (hF : Nat.card F = q ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q) :
    Nat.card (fixF σ) = q := by
  have hσ2 : σ * σ = 1 := frobenius_sq hF σ hσ
  have hσne : σ ≠ 1 := frobenius_ne_one hq hF σ hσ
  have hσU : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang.isUnitaryInvolution_of_involution
      hσne hσ2
  rw [card_fixF]
  exact CFSG.ClassicalInvolution.Phan.card_fixed_eq (σ := σ) hσU hF

private lemma isPGroup_of_isElemAbelian {p : ℕ} {X : Type*} [Group X]
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian p E) : IsPGroup p E := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro x
  exact ⟨1, by
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using hE.2 x.1 x.2)⟩

private lemma isElemAbelian_range {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {E : Subgroup X} (f : X →* Y) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  constructor
  · refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hfx, ← hfy, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · intro a ha
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp ha
    rw [← hfx, ← map_pow, hE.2 x hx, map_one]

private lemma isElemAbelian_range_of_subgroup {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {E : Subgroup X} (f : ↥E →* Y) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p f.range := by
  constructor
  · refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨x, hfx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hfy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hfx, ← hfy, ← map_mul, ← map_mul]
    exact congrArg f (hE.1.is_comm.comm x y)
  · intro a ha
    obtain ⟨x, hfx⟩ := MonoidHom.mem_range.mp ha
    rw [← hfx, ← map_pow]
    have hx : x ^ p = 1 := Subtype.ext (by simpa using hE.2 x.1 x.2)
    rw [hx, map_one]

private lemma isElemAbelian_of_injective {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {S : Subgroup X} (f : X →* Y) (hinj : Function.Injective (f.comp S.subtype))
    (h : CFSG.Open.IsElemAbelian p (S.map f)) : CFSG.Open.IsElemAbelian p S := by
  constructor
  · refine IsMulCommutative.of_comm fun s t => ?_
    apply hinj
    show f ((s : X) * (t : X)) = f ((t : X) * (s : X))
    rw [map_mul, map_mul]
    have ha : f (s : X) ∈ S.map f := Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩
    have hb : f (t : X) ∈ S.map f := Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩
    exact congrArg Subtype.val (h.1.is_comm.comm ⟨f (s : X), ha⟩ ⟨f (t : X), hb⟩)
  · intro s hs
    have h1 : (f s) ^ p = 1 := h.2 (f s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
    have h2 : f (s ^ p) = 1 := by rw [map_pow, h1]
    have h3 : (⟨s ^ p, S.pow_mem hs p⟩ : ↥S) = 1 := by
      apply hinj
      simpa using h2
    exact Subtype.ext_iff.mp h3

private lemma slFieldAut_mul_slConjugation (n : ℕ) (K : Type) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (σ : K ≃+* K) :
    slFieldAut (Fin n) K σ * slConjugation n K A =
      slConjugation n K (glFieldAut (Fin n) K σ A) * slFieldAut (Fin n) K σ := by
  have h := CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction_mul
    (n := n) (K := K) (A := 1) (B := A) σ 1
  simpa [CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction] using h

private lemma range_le_slConjugation_frob_range {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q)
    {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (θ : ↥E →* MulAut (Matrix.SpecialLinearGroup (Fin 3) F))
    (hθ : θ.range ≤ (slConjugation 3 F).range)
    (hθσ : ∀ x, θ x * slFieldAut (Fin 3) F σ = slFieldAut (Fin 3) F σ * θ x) :
    θ.range ≤ ((slConjugation 3 F).comp
      (Matrix.GeneralLinearGroup.map (fixF σ).subtype)).range := by
  rintro y ⟨x, rfl⟩
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp (hθ ⟨x, rfl⟩)
  have hrel := slFieldAut_mul_slConjugation 3 F A σ
  have hcomm : slFieldAut (Fin 3) F σ * θ x = θ x * slFieldAut (Fin 3) F σ := (hθσ x).symm
  have hZ : slConjugation 3 F (glFieldAut (Fin 3) F σ A) = θ x := by
    apply mul_right_cancel
      (b := slFieldAut (Fin 3) F σ)
    rw [← hrel, hA, hcomm]
  have hcenter : glFieldAut (Fin 3) F σ A * A⁻¹ ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F) := by
    rw [← ker_slConjugation 3 F, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hZ, hA, mul_inv_cancel]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hcenter
  have hscalar : glFieldAut (Fin 3) F σ A =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * A := by
    rw [hc]
    group
  have hmat : ((Matrix.GeneralLinearGroup.map σ.toRingHom A :
      Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • (A : Matrix (Fin 3) (Fin 3) F) := by
    change ((glFieldAut (Fin 3) F σ A : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = _
    rw [hscalar, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  obtain ⟨μ, B, hdesc⟩ :=
    CFSG.StandardType.LinearFieldFix.exists_descend_of_map_eq_smul σ A c hmat
  refine MonoidHom.mem_range.mpr ⟨B, ?_⟩
  have hB : Matrix.GeneralLinearGroup.map (fixF σ).subtype B =
      Matrix.GeneralLinearGroup.scalar (Fin 3) μ * A := by
    apply Units.ext
    rw [hdesc, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  change slConjugation 3 F (Matrix.GeneralLinearGroup.map (fixF σ).subtype B) = θ x
  rw [hB, map_mul, slConjugation_scalar, one_mul, hA]

private lemma frob_psi_ker_dvd {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (hF : Nat.card F = q ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ q) :
    Nat.card ((slConjugation 3 F).comp
      (Matrix.GeneralLinearGroup.map (fixF σ).subtype)).ker ∣ q - 1 := by
  set scal : (fixF σ)ˣ →* Matrix.GeneralLinearGroup (Fin 3) (fixF σ) :=
    Matrix.GeneralLinearGroup.scalar (Fin 3) with hscaldef
  have hscalinj : Function.Injective scal := by
    intro u v huv
    have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) (fixF σ) =>
      (A : Matrix (Fin 3) (Fin 3) (fixF σ)) 0 0) huv
    exact Units.ext (by
      simpa [hscaldef, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h)
  have hkerle : ((slConjugation 3 F).comp
      (Matrix.GeneralLinearGroup.map (fixF σ).subtype)).ker ≤ scal.range := by
    rintro A hA
    have hcenter : Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F) := by
      rw [← ker_slConjugation 3 F, MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp hA
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hcenter
    obtain ⟨b, hb⟩ := subfieldGLMap_scalar_reflect (Fin 3) F (fixF σ) A c hc.symm
    exact ⟨b, hb.symm⟩
  calc Nat.card ((slConjugation 3 F).comp
        (Matrix.GeneralLinearGroup.map (fixF σ).subtype)).ker ∣ Nat.card scal.range :=
      Subgroup.card_dvd_of_le hkerle
    _ = Nat.card (fixF σ)ˣ := by
        rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hscalinj, Subgroup.card_top]
    _ = q - 1 := by rw [Nat.card_units, natCard_fixF_eq hq hF σ hσ]

private lemma not_dvd_card_ker_comp {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {H : Subgroup X} (f : X →* Y) (hker : ¬ p ∣ Nat.card f.ker) :
    ¬ p ∣ Nat.card (f.comp H.subtype).ker := by
  intro h
  apply hker
  have h1 : Nat.card (f.comp H.subtype).ker =
      Nat.card (((f.comp H.subtype).ker).map H.subtype) :=
    (Subgroup.card_map_of_injective H.subtype_injective).symm
  rw [h1] at h
  exact h.trans (Subgroup.card_dvd_of_le (by
    rintro y ⟨x, hx, rfl⟩
    exact MonoidHom.mem_ker.mp hx))

private lemma exists_isElemAbelian_card_of_hom {X Y : Type*} [Group X] [Finite X] [Group Y]
    [Finite Y] {p : ℕ} (hp : p.Prime) (f : X →* Y) {R : Subgroup Y}
    (hR : CFSG.Open.IsElemAbelian p R) (hRle : R ≤ f.range) (hker : ¬ p ∣ Nat.card f.ker) :
    ∃ S : Subgroup X, CFSG.Open.IsElemAbelian p S ∧ Nat.card S = Nat.card R := by
  haveI : Fact p.Prime := ⟨hp⟩
  let H : Subgroup X := R.comap f
  let φH : ↥H →* Y := f.comp H.subtype
  have hφHrange : φH.range = R := by
    have hmap : φH.range = H.map f := by
      ext z
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨h.1, h.2, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, rfl⟩
    rw [hmap, show H = R.comap f from rfl, Subgroup.map_comap_eq, inf_eq_right.mpr hRle]
  have hNindex : φH.ker.index = Nat.card R := by rw [Subgroup.index_ker φH, hφHrange]
  have hNker : ¬ p ∣ Nat.card φH.ker := not_dvd_card_ker_comp f hker
  obtain ⟨k, hk⟩ := (isPGroup_iff_card_dvd_pow).1 (isPGroup_of_isElemAbelian hR)
  have hcp3 : Nat.Coprime (Nat.card φH.ker) p :=
    Nat.coprime_comm.mpr ((hp.coprime_iff_not_dvd).mpr hNker)
  have hcp : Nat.Coprime (Nat.card φH.ker) φH.ker.index := by
    rw [hNindex]
    exact ((Nat.coprime_pow_right_iff (Nat.succ_pos k) (Nat.card φH.ker) p).mpr hcp3)
      |>.coprime_dvd_right (hk.trans (pow_dvd_pow p (Nat.le_succ k)))
  obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime (N := φH.ker) hcp
  have hScard : Nat.card S = Nat.card R := by
    rw [← hNindex]; exact (hS.symm.index_eq_card).symm
  have hinj : Function.Injective (φH.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (x : ↥H) ∈ S ⊓ φH.ker :=
      ⟨x.2, MonoidHom.mem_ker.mpr (by simpa using MonoidHom.mem_ker.mp hx)⟩
    rw [show S ⊓ φH.ker = ⊥ from by rw [inf_comm]; exact hS.disjoint.eq_bot] at hx'
    simpa using hx'
  have hSmap : S.map φH = R := by
    rw [← hφHrange]
    apply le_antisymm
    · rintro z ⟨s, hs, rfl⟩
      exact ⟨s, rfl⟩
    · intro z hz
      obtain ⟨h, rfl⟩ := hz
      obtain ⟨⟨⟨u, hu⟩, ⟨s, hs⟩⟩, hus⟩ := hS.2 h
      refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
      rw [← hus, map_mul, MonoidHom.mem_ker.mp hu, one_mul]
  exact ⟨S.map H.subtype,
    isElemAbelian_range H.subtype (isElemAbelian_of_injective φH hinj (by rw [hSmap]; exact hR)),
    by rw [Subgroup.card_map_of_injective H.subtype_injective, hScard]⟩

theorem card_le_three_mul_card_ker_of_range_le_slConjugation_frob {F : Type} [Field F]
    [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 3 = 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ q) {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : CFSG.Open.IsElemAbelian 3 E) (θ : ↥E →* MulAut (Matrix.SpecialLinearGroup (Fin 3) F))
    (hθ : θ.range ≤ (slConjugation 3 F).range)
    (hθσ : ∀ x, θ x * slFieldAut (Fin 3) F σ = slFieldAut (Fin 3) F σ * θ x) :
    Nat.card E ≤ 3 * Nat.card θ.ker := by
  have hq2 : 2 ≤ q := by omega
  have hq1 : ¬ 3 ∣ q - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hfix3 : Nat.card (fixF σ) % 3 = 2 := by
    rw [natCard_fixF_eq hq2 hF σ hσ]; exact hq
  let ψ : Matrix.GeneralLinearGroup (Fin 3) (fixF σ) →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (slConjugation 3 F).comp (Matrix.GeneralLinearGroup.map (fixF σ).subtype)
  have hψker : ¬ 3 ∣ Nat.card ψ.ker := by
    change ¬ 3 ∣ Nat.card ((slConjugation 3 F).comp
      (Matrix.GeneralLinearGroup.map (fixF σ).subtype)).ker
    intro h3
    exact hq1 (h3.trans (frob_psi_ker_dvd hq2 hF σ hσ))
  have hRle : θ.range ≤ ψ.range := range_le_slConjugation_frob_range hF σ hσ hE θ hθ hθσ
  have hRelem : CFSG.Open.IsElemAbelian 3 θ.range := isElemAbelian_range_of_subgroup θ hE
  obtain ⟨S, hSelem, hScard⟩ :=
    exists_isElemAbelian_card_of_hom Nat.prime_three ψ hRelem hRle hψker
  have hbound : Nat.card S ≤ 3 :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.card_le_three_of_isElemAbelian_SL3
      hfix3 hSelem
  have hRbound : Nat.card θ.range ≤ 3 := by rw [← hScard]; exact hbound
  calc Nat.card E = Nat.card θ.ker * Nat.card θ.range :=
        (Subgroup.card_ker_mul_card_range θ).symm
    _ ≤ Nat.card θ.ker * 3 := Nat.mul_le_mul_left _ hRbound
    _ = 3 * Nat.card θ.ker := Nat.mul_comm _ _

end CFSG.LinearGroups

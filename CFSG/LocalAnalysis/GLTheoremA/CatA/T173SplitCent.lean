module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173S

open Polynomial Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.StandardType.TableBOrth

section Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem exists_eq_X_sub_C_of_mem_primaryFactors {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F - 1)
    {d : V ≃ₗ[F] V} (hd : d ^ p = 1) {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap) :
    ∃ u : Fˣ, u ^ p = 1 ∧ h = X - C (u : F) := by
  classical
  obtain ⟨hirr, hmonic, hdvd⟩ := mem_primaryFactors.mp hh
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp : d.toLinearMap ^ p = 1 := by
    have h := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) d p
    rw [hd, map_one] at h
    exact h.symm
  have hdvd1 : minpoly F d.toLinearMap ∣ X ^ p - 1 := by
    rw [minpoly.dvd_iff]
    simp [hdp]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have hζp : IsPrimitiveRoot (ζ : F) p := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
    exact hζ
  have hprod : (X : F[X]) ^ p - 1 = ∏ ζ' ∈ nthRootsFinset p (1 : F), (X - C ζ') :=
    X_pow_sub_one_eq_prod hp.pos hζp
  have hdiv : h ∣ ∏ ζ' ∈ nthRootsFinset p (1 : F), (X - C ζ') := by
    rw [← hprod]
    exact dvd_trans hdvd hdvd1
  obtain ⟨ζ', hζ'mem, hdvdζ'⟩ :=
    (Prime.dvd_finsetProd_iff hirr.prime (fun ζ' : F => X - C ζ')).1 hdiv
  have hζ'1 : ζ' ^ p = 1 := (mem_nthRootsFinset hp.pos (1 : F)).1 hζ'mem
  have hζ'0 : ζ' ≠ 0 := ne_zero_of_mem_nthRootsFinset (show (1 : F) ≠ 0 from one_ne_zero) hζ'mem
  have hassoc : Associated h (X - C ζ') :=
    hirr.associated_of_dvd (irreducible_X_sub_C ζ') hdvdζ'
  have heq : h = X - C ζ' := eq_of_monic_of_associated hmonic (monic_X_sub_C ζ') hassoc
  refine ⟨Units.mk0 ζ' hζ'0, ?_, ?_⟩
  · ext
    simpa using hζ'1
  · rw [heq]
    simp

private theorem exists_weight_of_mem_primaryFactors_aux1 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    (v : V) (j : Fin m) :
    QuadraticMap.polar Q (d v) (f j) = QuadraticMap.polar Q v (f j) * (c j : F) := by
  obtain ⟨w, hw1, hw2, hv⟩ := exists_decomp_of_isHypFamily hef v
  have hdw : d w = w := hd.2.2 w hw1 hw2
  have hdv : d v = (∑ i, ((QuadraticMap.polar Q v (f i) * (c i : F)) • e i +
      (QuadraticMap.polar Q v (e i) * (((c i)⁻¹ : Fˣ) : F)) • f i)) + w := by
    conv_lhs => rw [hv]
    rw [map_add, map_sum, hdw]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_add, map_smul, map_smul, hd.1 i, hd.2.1 i]
    simp only [smul_smul]
  rw [hdv]
  have hwj : QuadraticMap.polar Q w (f j) = 0 := by
    rw [QuadraticMap.polar_comm Q w (f j)]
    exact hw2 j
  rw [QuadraticMap.polar_add_left, hwj, add_zero]
  conv_lhs => rw [QuadraticMap.polar_comm]
  rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
  simp only [QuadraticMap.polarBilin_apply_apply]
  refine (Fintype.sum_eq_single j (fun i hij => ?_)).trans ?_
  · simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul]
    have h1 : QuadraticMap.polar Q (f j) (e i) = 0 := by
      rw [QuadraticMap.polar_comm Q (f j) (e i), hef.polar_ef i j, if_neg hij]
    have h2 : QuadraticMap.polar Q (f j) (f i) = 0 := hef.polar_ff j i
    rw [h1, h2, mul_zero, mul_zero, add_zero]
  · simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul]
    have h1 : QuadraticMap.polar Q (f j) (e j) = 1 := by
      rw [QuadraticMap.polar_comm Q (f j) (e j), hef.polar_ef j j, if_pos rfl]
    have h2 : QuadraticMap.polar Q (f j) (f j) = 0 := hef.polar_ff j j
    rw [h1, h2, mul_one, mul_zero, add_zero]

private theorem exists_weight_of_mem_primaryFactors_aux2 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    (v : V) (j : Fin m) :
    QuadraticMap.polar Q (d v) (e j) = QuadraticMap.polar Q v (e j) * (((c j)⁻¹ : Fˣ) : F) := by
  obtain ⟨w, hw1, hw2, hv⟩ := exists_decomp_of_isHypFamily hef v
  have hdw : d w = w := hd.2.2 w hw1 hw2
  have hdv : d v = (∑ i, ((QuadraticMap.polar Q v (f i) * (c i : F)) • e i +
      (QuadraticMap.polar Q v (e i) * (((c i)⁻¹ : Fˣ) : F)) • f i)) + w := by
    conv_lhs => rw [hv]
    rw [map_add, map_sum, hdw]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_add, map_smul, map_smul, hd.1 i, hd.2.1 i]
    simp only [smul_smul]
  rw [hdv]
  have hwj : QuadraticMap.polar Q w (e j) = 0 := by
    rw [QuadraticMap.polar_comm Q w (e j)]
    exact hw1 j
  rw [QuadraticMap.polar_add_left, hwj, add_zero]
  conv_lhs => rw [QuadraticMap.polar_comm]
  rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
  simp only [QuadraticMap.polarBilin_apply_apply]
  refine (Fintype.sum_eq_single j (fun i hij => ?_)).trans ?_
  · simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul]
    have h1 : QuadraticMap.polar Q (e j) (e i) = 0 := hef.polar_ee j i
    have h2 : QuadraticMap.polar Q (e j) (f i) = 0 := by
      rw [hef.polar_ef j i, if_neg (Ne.symm hij)]
    rw [h1, h2, mul_zero, mul_zero, add_zero]
  · simp only [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul]
    have h1 : QuadraticMap.polar Q (e j) (e j) = 0 := hef.polar_ee j j
    have h2 : QuadraticMap.polar Q (e j) (f j) = 1 := by
      rw [hef.polar_ef j j, if_pos rfl]
    rw [h1, h2, mul_zero, mul_one, zero_add]

theorem exists_weight_of_mem_primaryFactors (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {u : Fˣ} (hu : u ≠ 1)
    (hh : X - C (u : F) ∈ primaryFactors d.toLinearMap) : ∃ i, c i = u ∨ c i = u⁻¹ := by
  classical
  have hroot : (minpoly F d.toLinearMap).IsRoot (u : F) :=
    (Polynomial.dvd_iff_isRoot).mp (mem_primaryFactors.mp hh).2.2
  have heig : Module.End.HasEigenvalue d.toLinearMap (u : F) :=
    Module.End.hasEigenvalue_of_isRoot hroot
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 heig
  rw [Module.End.mem_eigenspace_iff] at hv
  have hv' : d v = (u : F) • v := hv
  obtain ⟨w, hw1, hw2, hvdecomp⟩ := exists_decomp_of_isHypFamily hef v
  by_contra hcon
  push Not at hcon
  have hα : ∀ i, QuadraticMap.polar Q v (f i) = 0 := by
    intro i
    have h := exists_weight_of_mem_primaryFactors_aux1 hef hd v i
    rw [hv', QuadraticMap.polar_smul_left, smul_eq_mul] at h
    have hne : ((c i : Fˣ) : F) ≠ (u : F) := fun hci => (hcon i).1 (Units.ext hci)
    have h2 : QuadraticMap.polar Q v (f i) * ((u : F) - (c i : F)) = 0 := by
      rw [mul_sub, mul_comm (QuadraticMap.polar Q v (f i)) (u : F), h, sub_self]
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr (Ne.symm hne))
  have hβ : ∀ i, QuadraticMap.polar Q v (e i) = 0 := by
    intro i
    have h := exists_weight_of_mem_primaryFactors_aux2 hef hd v i
    rw [hv', QuadraticMap.polar_smul_left, smul_eq_mul] at h
    have hne : (((c i)⁻¹ : Fˣ) : F) ≠ (u : F) := fun hci => (hcon i).2 (by
      have h1 : (c i)⁻¹ = u := Units.ext hci
      rw [← inv_inv (c i), h1])
    have h2 : QuadraticMap.polar Q v (e i) * ((u : F) - (((c i)⁻¹ : Fˣ) : F)) = 0 := by
      rw [mul_sub, mul_comm (QuadraticMap.polar Q v (e i)) (u : F), h, sub_self]
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr (Ne.symm hne))
  have hs0 : (∑ i, (QuadraticMap.polar Q v (f i) • e i +
      QuadraticMap.polar Q v (e i) • f i)) = 0 := by
    simp [hα, hβ]
  have hvw : v = w := by
    rw [hvdecomp, hs0, zero_add]
  have hdv : d v = v := by
    rw [hvw, hd.2.2 w hw1 hw2]
  have huv : v = u • v := hdv.symm.trans hv
  have hzero : (1 - (u : F)) • v = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr huv
  rcases smul_eq_zero.mp hzero with h1 | h2
  · exact hu (Units.ext (sub_eq_zero.mp h1).symm)
  · exact hv0 h2

private theorem finrank_fixedSpace_of_weightOne_aux1 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    (v : V) (j : Fin m) :
    QuadraticMap.polar Q (d v) (f j) = QuadraticMap.polar Q v (f j) * (c j : F) :=
  exists_weight_of_mem_primaryFactors_aux1 hef hd v j

private theorem finrank_fixedSpace_of_weightOne_aux2 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    (v : V) (j : Fin m) :
    QuadraticMap.polar Q (d v) (e j) = QuadraticMap.polar Q v (e j) * (((c j)⁻¹ : Fˣ) : F) :=
  exists_weight_of_mem_primaryFactors_aux2 hef hd v j

private theorem finrank_fixedSpace_of_weightOne_aux3 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    {j : Fin m} (hcj : c j ≠ 1) (hc1 : ∀ i, i ≠ j → c i = 1) :
    fixedSpace d ≤ LinearMap.ker ((QuadraticMap.polarBilin Q (e j)).prod
      (QuadraticMap.polarBilin Q (f j))) := by
  intro v hv
  rw [mem_fixedSpace] at hv
  rw [LinearMap.mem_ker, LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero]
  constructor
  · have h1 : QuadraticMap.polar Q (e j) v = 0 := by
      rw [QuadraticMap.polar_comm Q (e j) v]
      have h := finrank_fixedSpace_of_weightOne_aux2 hef hd v j
      rw [hv] at h
      have hne : (((c j)⁻¹ : Fˣ) : F) ≠ 1 := fun hc => hcj (by
        have h1 : (c j)⁻¹ = 1 := Units.ext hc
        rw [← inv_inv (c j), h1, inv_one])
      have h2 : QuadraticMap.polar Q v (e j) * ((((c j)⁻¹ : Fˣ) : F) - 1) = 0 := by
        rw [mul_sub, mul_one, ← h, sub_self]
      exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)
    exact h1
  · have h3 : QuadraticMap.polar Q (f j) v = 0 := by
      rw [QuadraticMap.polar_comm Q (f j) v]
      have h := finrank_fixedSpace_of_weightOne_aux1 hef hd v j
      rw [hv] at h
      have hne : ((c j : Fˣ) : F) ≠ 1 := fun hc => hcj (Units.ext hc)
      have h2 : QuadraticMap.polar Q v (f j) * ((c j : F) - 1) = 0 := by
        rw [mul_sub, mul_one, ← h, sub_self]
      exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)
    exact h3

private theorem finrank_fixedSpace_of_weightOne_aux4 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c d)
    {j : Fin m} (hc1 : ∀ i, i ≠ j → c i = 1) :
    LinearMap.ker ((QuadraticMap.polarBilin Q (e j)).prod
      (QuadraticMap.polarBilin Q (f j))) ≤ fixedSpace d := by
  intro v hv
  rw [LinearMap.mem_ker, LinearMap.prod_apply, Function.prod_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2⟩ := hv
  rw [mem_fixedSpace]
  obtain ⟨w, hw1, hw2, hvdecomp⟩ := exists_decomp_of_isHypFamily hef v
  have hdw : d w = w := hd.2.2 w hw1 hw2
  have hβj : QuadraticMap.polar Q v (e j) = 0 := by
    rw [← QuadraticMap.polar_comm Q (e j) v]; exact h1
  have hαj : QuadraticMap.polar Q v (f j) = 0 := by
    rw [← QuadraticMap.polar_comm Q (f j) v]; exact h2
  have hs : d (∑ i, (QuadraticMap.polar Q v (f i) • e i +
      QuadraticMap.polar Q v (e i) • f i)) =
      ∑ i, (QuadraticMap.polar Q v (f i) • e i +
      QuadraticMap.polar Q v (e i) • f i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [hαj, hβj]
      simp
    · rw [map_add, map_smul, map_smul, hd.1 i, hd.2.1 i, hc1 i hij]
      simp
  rw [hvdecomp, map_add, hs, hdw]

private theorem finrank_fixedSpace_of_weightOne_aux5 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) (j : Fin m) :
    LinearMap.range ((QuadraticMap.polarBilin Q (e j)).prod
      (QuadraticMap.polarBilin Q (f j))) = ⊤ := by
  let φ : V →ₗ[F] F × F :=
    (QuadraticMap.polarBilin Q (e j)).prod (QuadraticMap.polarBilin Q (f j))
  change LinearMap.range φ = ⊤
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have h1 : φ (e j) = (0, 1) := by
    rw [LinearMap.prod_apply]
    refine Prod.ext ?_ ?_
    · show QuadraticMap.polarBilin Q (e j) (e j) = 0
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hef.polar_ee j j
    · show QuadraticMap.polarBilin Q (f j) (e j) = 1
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (f j) (e j),
        hef.polar_ef j j, if_pos rfl]
  have h2 : φ (f j) = (1, 0) := by
    rw [LinearMap.prod_apply]
    refine Prod.ext ?_ ?_
    · show QuadraticMap.polarBilin Q (e j) (f j) = 1
      rw [QuadraticMap.polarBilin_apply_apply, hef.polar_ef j j, if_pos rfl]
    · show QuadraticMap.polarBilin Q (f j) (f j) = 0
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hef.polar_ff j j
  have h3 : (a, b) = φ (a • f j + b • e j) := by
    rw [map_add, map_smul, map_smul, h2, h1]
    ext <;> simp
  rw [h3]
  exact LinearMap.mem_range_self φ _

theorem finrank_fixedSpace_of_weightOne (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {j : Fin m} (hcj : c j ≠ 1) (hc1 : ∀ i, i ≠ j → c i = 1) :
    finrank F (fixedSpace d) + 2 = finrank F V := by
  classical
  let φ : V →ₗ[F] F × F :=
    (QuadraticMap.polarBilin Q (e j)).prod (QuadraticMap.polarBilin Q (f j))
  have hker : fixedSpace d = LinearMap.ker φ :=
    le_antisymm (finrank_fixedSpace_of_weightOne_aux3 hef hd hcj hc1)
      (finrank_fixedSpace_of_weightOne_aux4 hef hd hc1)
  have hrange : LinearMap.range φ = ⊤ := finrank_fixedSpace_of_weightOne_aux5 hef j
  have hrank : finrank F (LinearMap.range φ) = 2 := by
    rw [hrange, finrank_top, Module.finrank_prod, Module.finrank_self]
  have h := LinearMap.finrank_range_add_finrank_ker (f := φ)
  rw [hrank, ← hker] at h
  omega

theorem eq_one_of_isHypDiag_one {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {d : V ≃ₗ[F] V} (hd : IsHypDiag Q e f (fun _ => 1) d) : d = 1 :=
  IsHypDiag.eq_of_isHypDiag hef hd ⟨fun i => by simp, fun i => by simp, fun v _ _ => rfl⟩

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux1 {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hef : QuadraticMap.polar Q e f = 1) :
    (QuadraticMap.polarBilin (Q.comp (Submodule.span F {e, f}).subtype)).Nondegenerate := by
  refine ((CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isRefl_polarBilin
    (Q.comp (Submodule.span F {e, f}).subtype)).nondegenerate_iff_separatingLeft).2 ?_
  intro x hx
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.2
  have hxe : QuadraticMap.polar Q (a • e + b • f) e = 0 := by
    have h := hx ⟨e, Submodule.subset_span (by simp)⟩
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polar_comp_subtype_cent, ← hab] at h
    exact h
  have hxf : QuadraticMap.polar Q (a • e + b • f) f = 0 := by
    have h := hx ⟨f, Submodule.subset_span (by simp)⟩
    rw [QuadraticMap.polarBilin_apply_apply,
      CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polar_comp_subtype_cent, ← hab] at h
    exact h
  have hb : b = 0 := by
    have h := hxe
    rw [QuadraticMap.polar_add_left,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero he,
        QuadraticMap.polar_comm Q f e, hef] at h
    simpa using h
  have ha : a = 0 := by
    have h := hxf
    rw [QuadraticMap.polar_add_left,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
        hef,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hf] at h
    simpa using h
  refine Subtype.ext ?_
  rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]
  rfl

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux2 {p m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {c : Fin m → Fˣ} {g : V ≃ₗ[F] V} (hd : IsHypDiag Q e f c g)
    (hcp : ∀ i, c i ^ p = 1) : g ^ p = 1 := by
  have hpow_e : ∀ (n : ℕ) (i : Fin m), (g ^ n) (e i) = (((c i) ^ n : Fˣ) : F) • e i := by
    intro n i
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hd.1 i, map_smul, ih, smul_smul,
          ← Units.val_mul, mul_comm, ← pow_succ]
  have hpow_f : ∀ (n : ℕ) (i : Fin m),
      (g ^ n) (f i) = ((((c i)⁻¹) ^ n : Fˣ) : F) • f i := by
    intro n i
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hd.2.1 i, map_smul, ih, smul_smul,
          ← Units.val_mul, mul_comm, ← pow_succ]
  have hdiag : IsHypDiag Q e f (fun _ => 1) (g ^ p) := by
    refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
    · rw [hpow_e p i, hcp i]
    · rw [hpow_f p i, show ((c i)⁻¹) ^ p = 1 from by rw [inv_pow, hcp i, inv_one]]
      simp
    · have hfix : ∀ n, (g ^ n) v = v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hd.2.2 v hv1 hv2, ih]
      exact hfix p
  exact eq_one_of_isHypDiag_one hef hdiag

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux3 (u : Fˣ) :
    reciprocalPolynomial (X - C (u : F)) = X - C (((u⁻¹ : Fˣ) : F)) := by
  have h0 : (X - C (u : F) : F[X]).coeff 0 = -(u : F) := by simp
  have hX : (X : F[X]).reverse = 1 := by
    have h := Polynomial.reverse_mul_X (1 : F[X])
    rw [one_mul] at h
    rw [h, show (1 : F[X]) = C 1 from Polynomial.C_1.symm, Polynomial.reverse_C]
  have h1 : (X - C (u : F) : F[X]).reverse = 1 - C (u : F) * X := by
    rw [show (X - C (u : F) : F[X]) = X + C (-(u : F)) by rw [sub_eq_add_neg, map_neg],
      Polynomial.reverse_add_C, hX, Polynomial.natDegree_X, pow_one]
    rw [map_neg, neg_mul, sub_eq_add_neg]
  have hCmul : (C ((u : Fˣ) : F) : F[X]) * C (((u⁻¹ : Fˣ) : F)) = 1 := by
    rw [← Polynomial.C_mul, Units.mul_inv, Polynomial.C_1]
  unfold reciprocalPolynomial
  rw [h0, h1, inv_neg, map_neg, ← Units.val_inv_eq_inv_val u]
  calc
    -C (((u⁻¹ : Fˣ) : F)) * (1 - C ((u : Fˣ) : F) * X)
        = -C (((u⁻¹ : Fˣ) : F)) + (C (((u⁻¹ : Fˣ) : F)) * C ((u : Fˣ) : F)) * X := by ring
    _ = -C (((u⁻¹ : Fˣ) : F)) + 1 * X := by
      rw [mul_comm (C (((u⁻¹ : Fˣ) : F))) (C ((u : Fˣ) : F)), hCmul]
    _ = X - C (((u⁻¹ : Fˣ) : F)) := by ring

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux4 {x : V ≃ₗ[F] V} {μ : F}
    {v : V} (hv : v ≠ 0) (hxv : x v = μ • v) :
    (X - C μ : F[X]) ∈ primaryFactors x.toLinearMap := by
  have hev : Module.End.HasEigenvalue x.toLinearMap μ := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    exact ⟨(Module.End.mem_eigenspace_iff).2 hxv, hv⟩
  exact mem_primaryFactors.mpr ⟨irreducible_X_sub_C μ, monic_X_sub_C μ,
    dvd_iff_isRoot.mpr (Module.End.hasEigenvalue_iff_isRoot.mp hev)⟩

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) (i : Fin m) : e i ≠ 0 ∧ f i ≠ 0 := by
  have h1 : QuadraticMap.polar Q (e i) (f i) = 1 := by simpa using hef.polar_ef i i
  constructor
  · intro h0
    rw [h0, QuadraticMap.polar_zero_left] at h1
    exact zero_ne_one h1
  · intro h0
    rw [h0, QuadraticMap.polar_zero_right] at h1
    exact zero_ne_one h1

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux6 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {g : V ≃ₗ[F] V}
    (hg : IsHypDiag Q e f c g) {i : Fin m} (hci : c i ≠ 1) : g ≠ 1 := by
  intro h1
  have h2 : g (e i) = ((c i : Fˣ) : F) • e i := hg.1 i
  rw [h1] at h2
  have h3 : (e i) = ((c i : Fˣ) : F) • e i := by simpa using h2
  have h4 : ((c i : Fˣ) : F) = 1 := by
    have h5 : (((c i : Fˣ) : F) - 1) • e i = 0 := by
      rw [sub_smul, one_smul, ← h3, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef i).1)
  exact hci (Units.ext h4)

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux7 {p m : ℕ}
    (hp : p.Prime) {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ}
    (hcp : ∀ i, c i ^ p = 1) {g : ↥(orthDerived Q)} (hg : IsHypDiag Q e f c (g : V ≃ₗ[F] V))
    (hne : ∃ i, c i ≠ 1) : orderOf g = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hgp : (g : V ≃ₗ[F] V) ^ p = 1 := exists_mem_centralizer_specialBlock_not_mem_zpowers_aux2 hef hg hcp
  have hgp' : g ^ p = 1 := Subtype.ext (by simpa using hgp)
  have hg1 : g ≠ 1 := by
    intro h1
    exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux6 hef hg hne.choose_spec
      (by simpa using congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) h1)
  exact orderOf_eq_prime hgp' hg1

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux8 {T : V ≃ₗ[F] V} {v : V}
    (h : T v = v) (n : ℤ) : (T ^ n) v = v := by
  have hinv : T⁻¹ v = v := by
    have h' := T.symm_apply_apply v
    rwa [h] at h'
  have hnat : ∀ k : ℕ, (T ^ k) v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, h, ih]
  have hneg : ∀ k : ℕ, ((T⁻¹) ^ k) v = v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, hinv, ih]
  rcases n with k | k
  · simpa using hnat k
  · rw [zpow_negSucc, ← inv_pow]
    simpa using hneg (k + 1)

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux16 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {u : Fˣ} {j : Fin m} (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹)
    {g : V ≃ₗ[F] V} (hg : g ∈ specialBlock Q d (X - C (u : F))) : g (e j) = e j := by
  have hmem : (X - C (c j : F) : F[X]) ∈ primaryFactors d.toLinearMap :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux4
      (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef j).1 (hd.1 j)
  have hne : (X - C (c j : F) : F[X]) ≠ X - C (u : F) := by
    intro h
    have hc : (c j : F) = (u : F) := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    exact hj1 (Units.ext hc)
  have hne' : (X - C (c j : F) : F[X]) ≠ reciprocalPolynomial (X - C (u : F)) := by
    rw [exists_mem_centralizer_specialBlock_not_mem_zpowers_aux3]
    intro h
    have hc : (c j : F) = (((u⁻¹ : Fˣ) : F)) := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    exact hj2 (Units.ext hc)
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.apply_eq_of_mem_specialBlock hmem hne hne' hg
    ((CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).2 (hd.1 j))

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux17 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {u : Fˣ} {j : Fin m} (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹)
    {g : V ≃ₗ[F] V} (hg : g ∈ specialBlock Q d (X - C (u : F))) : g (f j) = f j := by
  have hmem : (X - C (((c j)⁻¹ : Fˣ) : F) : F[X]) ∈ primaryFactors d.toLinearMap :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux4
      (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef j).2 (hd.2.1 j)
  have hne : (X - C (((c j)⁻¹ : Fˣ) : F) : F[X]) ≠ X - C (u : F) := by
    intro h
    have hc : (((c j)⁻¹ : Fˣ) : F) = (u : F) := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    have hu1 : (c j)⁻¹ = u := Units.ext hc
    exact hj2 (by rw [← inv_inv (c j), hu1])
  have hne' : (X - C (((c j)⁻¹ : Fˣ) : F) : F[X]) ≠
      reciprocalPolynomial (X - C (u : F)) := by
    rw [exists_mem_centralizer_specialBlock_not_mem_zpowers_aux3]
    intro h
    have hc : (((c j)⁻¹ : Fˣ) : F) = (((u⁻¹ : Fˣ) : F)) := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    have hu1 : (c j)⁻¹ = u⁻¹ := Units.ext hc
    exact hj1 (by rw [← inv_inv (c j), hu1, inv_inv])
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.apply_eq_of_mem_specialBlock hmem hne hne' hg
    ((CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).2 (hd.2.1 j))

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux9 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {u : Fˣ} {j : Fin m} (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹)
    {g : V ≃ₗ[F] V} (hg : g ∈ specialBlock Q d (X - C (u : F))) :
    g (e j) = e j ∧ g (f j) = f j :=
  ⟨exists_mem_centralizer_specialBlock_not_mem_zpowers_aux16 hef hd hj1 hj2 hg,
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux17 hef hd hj1 hj2 hg⟩

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux10 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} {d : V ≃ₗ[F] V}
    (hd : IsHypDiag Q e f c d) {j : Fin m} (hj : c j ≠ 1)
    {g : V ≃ₗ[F] V} (hg : g ∈ supportedFixedDerived Q d) :
    g (e j) = e j ∧ g (f j) = f j := by
  have hmem_e : (X - C (c j : F) : F[X]) ∈ primaryFactors d.toLinearMap :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux4 (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef j).1 (hd.1 j)
  have hne_e : (X - C (c j : F) : F[X]) ≠ X - 1 := by
    intro h
    have hc : (c j : F) = 1 := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    exact hj (Units.ext hc)
  have hfix_e : g (e j) = e j :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.apply_eq_of_mem_supportedFixedDerived hmem_e hne_e hg
      ((CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).2 (hd.1 j))
  have hmem_f : (X - C (((c j)⁻¹ : Fˣ) : F) : F[X]) ∈ primaryFactors d.toLinearMap :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux4 (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef j).2 (hd.2.1 j)
  have hne_f : (X - C (((c j)⁻¹ : Fˣ) : F) : F[X]) ≠ X - 1 := by
    intro h
    have hc : (((c j)⁻¹ : Fˣ) : F) = 1 := by
      have hco := congrArg (fun p : F[X] => p.coeff 0) h
      simpa using hco
    exact (inv_ne_one.mpr hj) (Units.ext hc)
  have hfix_f : g (f j) = f j :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.apply_eq_of_mem_supportedFixedDerived hmem_f hne_f hg
      ((CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).2 (hd.2.1 j))
  exact ⟨hfix_e, hfix_f⟩

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux11 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c' : Fin m → Fˣ} {a : V ≃ₗ[F] V}
    (ha : IsHypDiag Q e f c' a) {j : Fin m} (hc' : ∀ i, i ≠ j → c' i = 1) :
    ∀ x ∈ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (Submodule.span F {e j, f j}),
      a x = x := by
  intro x hx
  have hBj : QuadraticMap.polar Q x (f j) = 0 := by
    have h := (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff).1 hx (f j)
      (Submodule.subset_span (by simp))
    exact (QuadraticMap.polar_comm Q (f j) x).symm.trans h
  have hBe : QuadraticMap.polar Q x (e j) = 0 := by
    have h := (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff).1 hx (e j)
      (Submodule.subset_span (by simp))
    exact (QuadraticMap.polar_comm Q (e j) x).symm.trans h
  obtain ⟨w, hw1, hw2, hxv⟩ := exists_decomp_of_isHypFamily hef x
  have hterm : ∀ i : Fin m,
      a (QuadraticMap.polar Q x (f i) • e i + QuadraticMap.polar Q x (e i) • f i) =
      QuadraticMap.polar Q x (f i) • e i + QuadraticMap.polar Q x (e i) • f i := by
    intro i
    by_cases hi : i = j
    · subst hi
      rw [hBj, hBe]
      simp
    · have hci : c' i = 1 := hc' i hi
      rw [map_add, map_smul, map_smul, ha.1 i, ha.2.1 i, hci]
      simp
  have hs : a (∑ i, (QuadraticMap.polar Q x (f i) • e i + QuadraticMap.polar Q x (e i) • f i)) =
      ∑ i, (QuadraticMap.polar Q x (f i) • e i + QuadraticMap.polar Q x (e i) • f i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  rw [hxv, map_add, hs, ha.2.2 w hw1 hw2]

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux12 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c' : Fin m → Fˣ} {a b : V ≃ₗ[F] V}
    (ha : IsHypDiag Q e f c' a) {j : Fin m} (hc' : ∀ i, i ≠ j → c' i = 1)
    (hb_orth : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hb_e : b (e j) = e j)
    (hb_f : b (f j) = f j) : b * a = a * b := by
  let U : Submodule F V := Submodule.span F {e j, f j}
  have hU : (QuadraticMap.polarBilin (Q.comp U.subtype)).Nondegenerate :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux1 (hef.map_e j) (hef.map_f j) (by simpa using hef.polar_ef j j)
  have hgU : ∀ x ∈ U, b x = x := by
    intro x hx
    obtain ⟨r, s, hx'⟩ := Submodule.mem_span_pair.mp hx
    rw [← hx']
    simp [map_add, map_smul, hb_e, hb_f]
  have heU : ∀ x ∈ U, a x ∈ U := by
    intro x hx
    obtain ⟨r, s, hx'⟩ := Submodule.mem_span_pair.mp hx
    rw [← hx']
    refine Submodule.mem_span_pair.mpr ⟨r * ((c' j : Fˣ) : F), s * (((c' j)⁻¹ : Fˣ) : F), ?_⟩
    rw [map_add, map_smul, map_smul, ha.1 j, ha.2.1 j, smul_smul, smul_smul]
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq (Q := Q) (U := U) hU
    hb_orth hgU heU (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux11 hef ha hc')

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux13 {p : ℕ}
    {a d : ↥(orthDerived Q)} (horda : orderOf a = p) (hordd : orderOf d = p) {v : V} {μ : F}
    (hav : (a : V ≃ₗ[F] V) v = v) (hdv : (d : V ≃ₗ[F] V) v = μ • v) (hμ : μ ≠ 1)
    (hv : v ≠ 0) : a ∉ Subgroup.zpowers d := by
  intro hmem
  obtain ⟨k0, hk0⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hsub : Subgroup.zpowers a ≤ Subgroup.zpowers d := by
    rintro x ⟨k, rfl⟩
    refine ⟨k0 * k, ?_⟩
    show d ^ (k0 * k) = a ^ k
    rw [zpow_mul, hk0]
  have hcarda : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, horda]
  have hcardd : Nat.card (Subgroup.zpowers d) = p := by rw [Nat.card_zpowers, hordd]
  have heq : Subgroup.zpowers a = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hcarda, hcardd])
  have hdmem : d ∈ Subgroup.zpowers a := by
    rw [heq]
    exact Subgroup.mem_zpowers d
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hdmem
  have hm' : (a : V ≃ₗ[F] V) ^ m = (d : V ≃ₗ[F] V) := by
    simpa using congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) hm
  have hd_e : (d : V ≃ₗ[F] V) v = v := by
    rw [← hm']
    exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux8 hav m
  have h5 : (μ - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← hdv, hd_e, sub_self]
  exact hμ (sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv))

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux14 {p m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c c' : Fin m → Fˣ}
    {d a : ↥(orthDerived Q)} (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V))
    (ha : IsHypDiag Q e f c' (a : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hI : ∃ i, c i = u ∨ c i = u⁻¹) {j : Fin m} (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹)
    (horda : orderOf a = p) (hordd : orderOf d = p)
    (hc' : ∀ i, i ≠ j → c' i = 1) : a ∉ Subgroup.zpowers d := by
  obtain ⟨i, hi⟩ := hI
  have hci_ne1 : c i ≠ 1 := by
    rcases hi with h | h
    · rw [h]; exact hu
    · rw [h]; exact inv_ne_one.mpr hu
  have hij : i ≠ j := by
    rintro rfl
    rcases hi with h | h
    · exact hj1 h
    · exact hj2 h
  have ha_fix : (a : V ≃ₗ[F] V) (e i) = e i := by
    rw [ha.1 i, show ((c' i : Fˣ) : F) = 1 from by simp [hc' i hij]]
    simp
  exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux13 horda hordd ha_fix
    (hd.1 i) (fun h => hci_ne1 (Units.ext h))
    (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef i).1

private lemma exists_mem_centralizer_specialBlock_not_mem_zpowers_aux15 {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c c' : Fin m → Fˣ}
    {d a : ↥(orthDerived Q)} (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V))
    (ha : IsHypDiag Q e f c' (a : V ≃ₗ[F] V)) {u : Fˣ} {j : Fin m}
    (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹) (hc' : ∀ i, i ≠ j → c' i = 1) :
    a ∈ Subgroup.centralizer
      (((specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))).subgroupOf (orthDerived Q) :
        Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbs : (b : V ≃ₗ[F] V) ∈ specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F)) :=
    Subgroup.mem_subgroupOf.mp hb
  obtain ⟨hb_e, hb_f⟩ :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux9 hef hd hj1 hj2 hbs
  exact Subtype.ext (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux12 hef ha hc'
    (orthDerived_le_orthogonalGroup b.2) hb_e hb_f)

theorem exists_mem_centralizer_specialBlock_not_mem_zpowers
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {u : Fˣ} (hu : u ≠ 1)
    (hI : ∃ i, c i = u ∨ c i = u⁻¹) {j : Fin m} (hj1 : c j ≠ u) (hj2 : c j ≠ u⁻¹) :
    ∃ a ∈ A, a ∈ Subgroup.centralizer
        (((specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))).subgroupOf (orthDerived Q) :
          Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) ∧ a ∉ Subgroup.zpowers d := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    exact hp.ne_one hζ.symm
  let c' : Fin m → Fˣ := fun i => if i = j then ζ else 1
  have hc'p : ∀ i, c' i ^ p = 1 := by
    intro i
    by_cases hi : i = j
    · subst hi
      simpa [c'] using hζp
    · simp [c', if_neg hi]
  obtain ⟨a, ha⟩ := exists_isHypDiag_mem_orthDerived hp hp2 hef hc'p
  have haA : a ∈ A := (hAeq a).2 ⟨c', hc'p, ha⟩
  have horda : orderOf a = p :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux7 hp hef hc'p ha
      ⟨j, by simp [c', hζ1]⟩
  have hI' := hI
  obtain ⟨i, hi⟩ := hI
  have hci_ne1 : c i ≠ 1 := by
    rcases hi with h | h
    · rw [h]; exact hu
    · rw [h]; exact inv_ne_one.mpr hu
  have hordd : orderOf d = p :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux7 hp hef hcp hd ⟨i, hci_ne1⟩
  refine ⟨a, haA, ?_, ?_⟩
  · exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux15 hef hd ha hj1 hj2
      (fun i hi => by simp [c', if_neg hi])
  · exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux14 hef hd ha hu hI' hj1 hj2
      horda hordd (fun i hi => by simp [c', if_neg hi])


theorem exists_mem_centralizer_supportedFixedDerived_not_mem_zpowers
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) {j₁ j₂ : Fin m} (hj : j₁ ≠ j₂) (h₁ : c j₁ ≠ 1)
    (h₂ : c j₂ ≠ 1) {G : Subgroup (V ≃ₗ[F] V)} (hG : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V)) :
    ∃ a ∈ A, a ∈ Subgroup.centralizer ((G.subgroupOf (orthDerived Q) : Subgroup ↥(orthDerived Q)) :
        Set ↥(orthDerived Q)) ∧ a ∉ Subgroup.zpowers d := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let c' : Fin m → Fˣ := fun i => if i = j₁ then c j₁ else 1
  have hc'p : ∀ i, c' i ^ p = 1 := by
    intro i
    by_cases hi : i = j₁
    · subst hi
      simpa [c'] using hcp i
    · simp [c', if_neg hi]
  obtain ⟨a, ha⟩ := exists_isHypDiag_mem_orthDerived hp hp2 hef hc'p
  have haA : a ∈ A := (hAeq a).2 ⟨c', hc'p, ha⟩
  have horda : orderOf a = p :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux7 hp hef hc'p ha
      ⟨j₁, by simp [c', h₁]⟩
  have hordd : orderOf d = p :=
    exists_mem_centralizer_specialBlock_not_mem_zpowers_aux7 hp hef hcp hd ⟨j₂, h₂⟩
  have hcentral : a ∈ Subgroup.centralizer ((G.subgroupOf (orthDerived Q) :
      Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbs : (b : V ≃ₗ[F] V) ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
      hG (Subgroup.mem_subgroupOf.mp hb)
    obtain ⟨hb_e, hb_f⟩ :=
      exists_mem_centralizer_specialBlock_not_mem_zpowers_aux10 hef hd h₁ hbs
    exact Subtype.ext (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux12 hef ha
      (fun i hi => by simp [c', if_neg hi]) (orthDerived_le_orthogonalGroup b.2) hb_e hb_f)
  refine ⟨a, haA, hcentral, ?_⟩
  have ha_fix : (a : V ≃ₗ[F] V) (e j₂) = e j₂ := by
    rw [ha.1 j₂, show ((c' j₂ : Fˣ) : F) = 1 from by simp [c', if_neg (Ne.symm hj)]]
    simp
  exact exists_mem_centralizer_specialBlock_not_mem_zpowers_aux13 horda hordd ha_fix
    (hd.1 j₂) (fun h => h₂ (Units.ext h))
    (exists_mem_centralizer_specialBlock_not_mem_zpowers_aux5 hef j₂).1


theorem glaLayer_top_eq_top (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) :
    GLALayer (⊤ : Subgroup ↥(orthDerived Q)) = ⊤ := by
  obtain ⟨T3, hT3, hTs⟩ := exists_finrank_three_singular hQ hdim hl
  have hq : CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(orthDerived Q)) :=
    CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv (isQuasisimple_orthDerived hQ ⟨T3, hT3, hTs⟩)
  have hc : IsComponentOf (⊤ : Subgroup ↥(orthDerived Q)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _, hq.1.commutator_eq_top, hq.2.1⟩
  exact eq_top_iff.2 (le_sSup (show (⊤ : Subgroup ↥(orthDerived Q)) ∈
    {K : Subgroup ↥(orthDerived Q) | IsComponentOf K ⊤} from hc))

private theorem standard_classification_part1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {d : ↥(orthDerived Q)} (hd1 : d = 1) :
    GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) = ⊤ := by
  have htop : Subgroup.centralizer ({d} : Set ↥(orthDerived Q)) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.2 (by simp [hd1])
  rw [htop]
  exact glaLayer_top_eq_top hQ hdim hl

private theorem standard_classification_part2 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) (hdp' : (d : V ≃ₗ[F] V) ^ p = 1) {h : F[X]}
    (hh : h ∈ primaryFactors (d : V ≃ₗ[F] V).toLinearMap) (hh1 : h ≠ X - 1)
    (hL : GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
      (specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hcent : ∀ a ∈ A, a ∈ Subgroup.centralizer
      (((specialBlock Q (d : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) :
        Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) → a ∈ Subgroup.zpowers d) :
    ∃ u : Fˣ, u ≠ 1 ∧ (∀ i, c i = u ∨ c i = u⁻¹) ∧
      GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
        (specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))).subgroupOf (orthDerived Q) := by
  obtain ⟨u, -, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp hpq hdp' hh
  have hu : u ≠ 1 := fun h1 => hh1 (by simp [h1])
  obtain ⟨i, hi⟩ := exists_weight_of_mem_primaryFactors hQ hef hd hu hh
  refine ⟨u, hu, fun j => ?_, hL⟩
  by_contra hj
  push Not at hj
  obtain ⟨a, haA, haC, hna⟩ := exists_mem_centralizer_specialBlock_not_mem_zpowers hQ hp hp2 hpq
    hef hAeq hcp hd hu ⟨i, hi⟩ hj.1 hj.2
  exact hna (hcent a haA haC)

private theorem standard_classification_part3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {A : Subgroup ↥(orthDerived Q)}
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) {d : ↥(orthDerived Q)}
    (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V)) (hd1 : d ≠ 1) {G : Subgroup (V ≃ₗ[F] V)}
    (hG : G ≤ supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hfix : finrank F (fixedSpace (d : V ≃ₗ[F] V)) ≤ 4 ∨
      G = supportedFixedDerived Q (d : V ≃ₗ[F] V))
    (hL : GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
      G.subgroupOf (orthDerived Q))
    (hcent : ∀ a ∈ A, a ∈ Subgroup.centralizer ((G.subgroupOf (orthDerived Q) :
      Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) → a ∈ Subgroup.zpowers d) :
    ∃ j, c j ≠ 1 ∧ (∀ i, i ≠ j → c i = 1) ∧
      GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
        (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  have hc1 : ∃ j, c j ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hd1 (Subtype.ext (eq_one_of_isHypDiag_one hef (by
      rwa [show c = fun _ => 1 from funext hall] at hd)))
  obtain ⟨j, hcj⟩ := hc1
  have hone : ∀ i, i ≠ j → c i = 1 := by
    intro i hij
    by_contra hci
    obtain ⟨a, haA, haC, hna⟩ := exists_mem_centralizer_supportedFixedDerived_not_mem_zpowers hQ hp
      hp2 hpq hef hAeq hcp hd (Ne.symm hij) hcj hci hG
    exact hna (hcent a haA haC)
  have hfin := finrank_fixedSpace_of_weightOne hQ hef hd hcj hone
  have hG' : G = supportedFixedDerived Q (d : V ≃ₗ[F] V) := hfix.resolve_left (by omega)
  exact ⟨j, hcj, hone, by rw [hL, hG']⟩

private theorem standard_classification_part4 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A : Subgroup ↥(orthDerived Q)} (hA : GLAIsBmax p A)
    {d : ↥(orthDerived Q)} (hdA : d ∈ A)
    (hK : IsComponentOf (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
      (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    (hCA : A ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
        Subgroup.zpowers d)
    {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    (hAeq : ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V))
    {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) (hd : IsHypDiag Q e f c (d : V ≃ₗ[F] V))
    (hd1 : d ≠ 1) :
    (∃ j, c j ≠ 1 ∧ (∀ i, i ≠ j → c i = 1) ∧
      GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
        (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
    (∃ u : Fˣ, u ≠ 1 ∧ (∀ i, c i = u ∨ c i = u⁻¹) ∧
      GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
        (specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))).subgroupOf (orthDerived Q)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp : d ^ p = 1 := hA.1.2 d hdA
  have hdp' : (d : V ≃ₗ[F] V) ^ p = 1 := by
    simpa using congrArg (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V)) hdp
  have hx : orderOf d = p := orderOf_eq_prime hdp hd1
  have hcent : ∀ {M : Subgroup ↥(orthDerived Q)},
      GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) = M →
      ∀ a ∈ A, a ∈ Subgroup.centralizer (M : Set ↥(orthDerived Q)) → a ∈ Subgroup.zpowers d :=
    fun {M} hM a haA haC => by
      rw [← hCA]
      exact ⟨haA, by rw [hM]; exact haC⟩
  rcases S172C.Cent.comp_cases_orthDerived_of_prime hQ hp hp2 hx hK with
    ⟨h, hh, hh1, -, hL⟩ | ⟨G, -, hG, -, hfix, hL⟩
  · exact Or.inr (standard_classification_part2 hQ hp hp2 hpq hef hAeq hcp hd hdp' hh hh1 hL
      fun a haA haC => hcent hL a haA haC)
  · exact Or.inl (standard_classification_part3 hQ hdim hl hp hp2 hpq hef hAeq hcp hd hd1 hG hfix hL
      fun a haA haC => hcent hL a haA haC)

theorem standard_classification (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A : Subgroup ↥(orthDerived Q)} (hA : GLAIsBmax p A)
    {d : ↥(orthDerived Q)} (hdA : d ∈ A)
    (hK : IsComponentOf (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
      (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    (hCA : A ⊓ Subgroup.centralizer
      (GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) : Set ↥(orthDerived Q)) =
        Subgroup.zpowers d) :
    ∃ (e f : Fin (wittRank Q l) → V) (c : Fin (wittRank Q l) → Fˣ), IsHypFamily Q e f ∧
      (∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V)) ∧
      (∀ i, c i ^ p = 1) ∧ IsHypDiag Q e f c (d : V ≃ₗ[F] V) ∧
      ((d = 1 ∧ GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) = ⊤) ∨
        (∃ j, c j ≠ 1 ∧ (∀ i, i ≠ j → c i = 1) ∧
          GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
            (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ∨
        (∃ u : Fˣ, u ≠ 1 ∧ (∀ i, c i = u ∨ c i = u⁻¹) ∧
          GLALayer (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))) =
            (specialBlock Q (d : V ≃ₗ[F] V) (X - C (u : F))).subgroupOf (orthDerived Q))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, f, hef, hAeq⟩ := exists_hypFamily_of_isBmax hQ hdim hl hp hp2 hpq hA
  obtain ⟨c, hcp, hd⟩ := (hAeq d).1 hdA
  refine ⟨e, f, c, hef, hAeq, hcp, hd, ?_⟩
  by_cases hd1 : d = 1
  · exact Or.inl ⟨hd1, standard_classification_part1 hQ hdim hl hd1⟩
  · exact Or.inr (standard_classification_part4 hQ hdim hl hp hp2 hpq hA hdA hK hCA hef hAeq hcp hd hd1)

end Cent

end CFSG.LocalAnalysis.GLTheoremA.T173S

end

module

public import CFSG.LieType.SeitzGeneration.OrthDfourProp
public import CFSG.LieType.SeitzGeneration.OrthHyperRoot
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical
  CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Two

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_apply_of_isotropic {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hw : Q w = 0) (v : V) : eichler Q u w v = v + polar Q v u • w - polar Q v w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero]

theorem eichler_wedge_expand (b₀ b₁ v : V) (α β γ δ : K) :
    polar Q v (α • b₀ + β • b₁) • (γ • b₀ + δ • b₁) -
        polar Q v (γ • b₀ + δ • b₁) • (α • b₀ + β • b₁) =
      (α * δ - β * γ) • (polar Q v b₀ • b₁ - polar Q v b₁ • b₀) := by
  simp only [polar_add_right, polar_smul_right_eq]
  module

theorem commute_eichler_of_det_one {x : V ≃ₗ[K] V}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {T : Submodule K V}
    (hT2 : Module.finrank K T = 2) (hTQ : ∀ t ∈ T, Q t = 0)
    (hTp : ∀ t ∈ T, ∀ t' ∈ T, polar Q t t' = 0) (hTx : ∀ t ∈ T, x t ∈ T)
    (hdet : LinearMap.det ((x : V →ₗ[K] V).restrict hTx) = 1) {e w : V} (he : e ∈ T)
    (hw : w ∈ T) : Commute (eichler Q e w) x := by
  classical
  haveI : Module.Finite K T := Module.finite_of_finrank_pos (by rw [hT2]; norm_num)
  obtain ⟨f, hf⟩ : ∃ f : T →ₗ[K] T, ∀ u : T, (f u : V) = x u :=
    ⟨(x : V →ₗ[K] V).restrict hTx, fun u => rfl⟩
  have hfeq : f = (x : V →ₗ[K] V).restrict hTx := LinearMap.ext fun u => Subtype.ext (hf u)
  obtain ⟨b, -⟩ : ∃ b : Basis (Fin 2) K T, True :=
    ⟨Module.finBasisOfFinrankEq K T hT2, trivial⟩
  have hdetN : (LinearMap.toMatrix b b f).det = 1 := by
    rw [LinearMap.det_toMatrix, hfeq]
    exact hdet
  rw [Matrix.det_fin_two] at hdetN
  have hfrepr : ∀ u : T, ∀ i : Fin 2, b.repr (f u) i = LinearMap.toMatrix b b f i 0 * b.repr u 0
      + LinearMap.toMatrix b b f i 1 * b.repr u 1 := by
    intro u i
    have h := congrFun (LinearMap.toMatrix_mulVec_repr b b f u) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm
  have hcoord : ∀ u : T, (u : V) = b.repr u 0 • (b 0 : V) + b.repr u 1 • (b 1 : V) := by
    intro u
    conv_lhs => rw [← b.sum_repr u]
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  obtain ⟨e', he'⟩ : ∃ e' : T, (e' : V) = e := ⟨⟨e, he⟩, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : T, (w' : V) = w := ⟨⟨w, hw⟩, rfl⟩
  have hdet' : b.repr (f e') 0 * b.repr (f w') 1 - b.repr (f e') 1 * b.repr (f w') 0 =
      b.repr e' 0 * b.repr w' 1 - b.repr e' 1 * b.repr w' 0 := by
    simp only [hfrepr]
    linear_combination (b.repr e' 0 * b.repr w' 1 - b.repr e' 1 * b.repr w' 0) * hdetN
  have hfe : ((f e' : T) : V) = x e := by rw [hf, he']
  have hfw : ((f w' : T) : V) = x w := by rw [hf, hw']
  have hEE : eichler Q (x e) (x w) = eichler Q e w := by
    refine LinearEquiv.ext fun v => ?_
    rw [eichler_apply_of_isotropic (hTQ _ (hTx e he)) (hTp _ (hTx e he) _ (hTx w hw))
        (hTQ _ (hTx w hw)) v, eichler_apply_of_isotropic (hTQ e he) (hTp e he w hw) (hTQ w hw) v]
    have h1 := eichler_wedge_expand (Q := Q) (b 0 : V) (b 1 : V) v (b.repr e' 0) (b.repr e' 1)
      (b.repr w' 0) (b.repr w' 1)
    have h2 := eichler_wedge_expand (Q := Q) (b 0 : V) (b 1 : V) v (b.repr (f e') 0)
      (b.repr (f e') 1) (b.repr (f w') 0) (b.repr (f w') 1)
    rw [← hcoord e', ← hcoord w', he', hw'] at h1
    rw [← hcoord (f e'), ← hcoord (f w'), hfe, hfw] at h2
    rw [add_sub_assoc, add_sub_assoc, h2, hdet', h1]
  have hconj := eichler_conj hx e w
  rw [hEE] at hconj
  show eichler Q e w * x = x * eichler Q e w
  calc eichler Q e w * x = (x * eichler Q e w * x⁻¹) * x := by rw [hconj]
    _ = x * eichler Q e w := by group

end Two

section Three

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_nonsingular_perp_of_hyp {A : Submodule K V} (hA : PolarNondegOn Q A)
    (h3 : 3 ≤ finrank K A) {e f : V} (heA : e ∈ A) (hfA : f ∈ A) (hee : Q e = 0)
    (hff : Q f = 0) (hef : polar Q e f = 1) :
    ∃ w ∈ A, polar Q e w = 0 ∧ polar Q f w = 0 ∧ Q w ≠ 0 := by
  obtain ⟨z₀, z₁, hz₀, hz₁, he₀, hf₀, he₁, hf₁, hpol⟩ :=
    OrthBlk.exists_orth_pair hA h3 heA hfA hee hff hef
  by_cases h0 : Q z₀ = 0
  · by_cases h1 : Q z₁ = 0
    · refine ⟨z₀ + z₁, A.add_mem hz₀ hz₁, ?_, ?_, ?_⟩
      · rw [polar_add_right, he₀, he₁, add_zero]
      · rw [polar_add_right, hf₀, hf₁, add_zero]
      · rw [QuadraticMap.map_add Q, h0, h1, zero_add, zero_add]
        exact hpol
    · exact ⟨z₁, hz₁, he₁, hf₁, h1⟩
  · exact ⟨z₀, hz₀, he₀, hf₀, h0⟩

theorem exists_singular_mem_three (h2 : (2 : K) ≠ 0) {A : Submodule K V}
    (hA : PolarNondegOn Q A) (h3 : finrank K A = 3) (M : AddSubgroup V)
    (hinv : ∀ x ∈ A, ∀ z ∈ A, Q x = 0 → polar Q x z = 0 → ∀ m ∈ M, m ∈ A →
      eichler Q x z m ∈ M)
    {y : V} (hyM : y ∈ M) (hyA : y ∈ A) (hy0 : y ≠ 0) :
    ∃ e ∈ M, e ∈ A ∧ e ≠ 0 ∧ Q e = 0 := by
  by_cases hyQ : Q y = 0
  · exact ⟨y, hyM, hyA, hy0, hyQ⟩
  obtain ⟨e, heA, he0, heQ⟩ := OrthBlk.exists_singular_of_three_le_any (S := A) h3.ge
  by_cases hc : polar Q y e = 0
  ·
    have hind : ∀ c : K, y ≠ c • e := by
      intro c hc'
      apply hyQ
      rw [hc', map_smul_eq_sq, heQ, mul_zero]
    obtain ⟨t, htA, hte, hty⟩ := OrthBlk.exists_perp_not_perp hA hyA heA hind
    have het : polar Q e t = 0 := by rw [polar_comm, hte]
    have hyt : polar Q y t ≠ 0 := by rwa [polar_comm]
    have hperp : polar Q e (-(polar Q y t)⁻¹ • t) = 0 := by
      rw [polar_smul_right_eq, het, mul_zero]
    have hEy := hinv e heA _ (A.smul_mem _ htA) heQ hperp y hyM hyA
    have hform : eichler Q e (-(polar Q y t)⁻¹ • t) y = y + e := by
      rw [eichler_apply heQ hperp]
      simp only [hc, zero_smul, add_zero, mul_zero, polar_smul_right_eq, neg_mul,
        inv_mul_cancel₀ hyt, neg_one_smul, sub_neg_eq_add]
    rw [hform] at hEy
    exact ⟨e, by simpa using M.sub_mem hEy hyM, heA, he0, heQ⟩
  ·
    obtain ⟨f, hfA, hfQ, hef⟩ := exists_partner_of_polarNondegOn hA heA he0 heQ
    obtain ⟨w, hwA, hew, hfw, hwQ⟩ := exists_nonsingular_perp_of_hyp hA h3.ge heA hfA heQ hfQ hef
    have hperp : ∀ t : K, polar Q e (t • w) = 0 := fun t => by
      rw [polar_smul_right_eq, hew, mul_zero]
    have hD : ∀ t : K, (polar Q y e * t) • w -
        (t * polar Q y w + t ^ 2 * Q w * polar Q y e) • e ∈ M := by
      intro t
      have h := hinv e heA (t • w) (A.smul_mem t hwA) heQ (hperp t) y hyM hyA
      have hform : eichler Q e (t • w) y = y + (polar Q y e * t) • w -
          (t * polar Q y w + t ^ 2 * Q w * polar Q y e) • e := by
        rw [eichler_apply heQ (hperp t), polar_smul_right_eq, map_smul_eq_sq]
        module
      rw [hform] at h
      convert M.sub_mem h hyM using 1
      abel
    have hkey : ∀ a : K, (-(2 * a * Q w * polar Q y e)) • e ∈ M := by
      intro a
      have h := M.sub_mem (M.sub_mem (hD (a + 1)) (hD a)) (hD 1)
      convert h using 1
      module
    have e2 : -(2 * (-(2 * Q w * polar Q y e)⁻¹) * Q w * polar Q y e) = 1 := by
      field_simp
    have h1 := hkey (-(2 * Q w * polar Q y e)⁻¹)
    rw [e2, one_smul] at h1
    exact ⟨e, h1, heA, he0, heQ⟩

theorem mem_of_invariant_of_singular_three (h2 : (2 : K) ≠ 0) {A : Submodule K V}
    (hA : PolarNondegOn Q A) (h3 : finrank K A = 3) (M : AddSubgroup V)
    (hinv : ∀ x ∈ A, ∀ z ∈ A, Q x = 0 → polar Q x z = 0 → ∀ m ∈ M, m ∈ A →
      eichler Q x z m ∈ M)
    {e : V} (heM : e ∈ M) (heA : e ∈ A) (he0 : e ≠ 0) (heQ : Q e = 0) : ∀ a ∈ A, a ∈ M := by
  obtain ⟨f, hfA, hfQ, hef⟩ := exists_partner_of_polarNondegOn hA heA he0 heQ
  obtain ⟨w, hwA, hew, hfw, hwQ⟩ := exists_nonsingular_perp_of_hyp hA h3.ge heA hfA heQ hfQ hef
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hfγ : ∀ t : K, polar Q f (t • w) = 0 := fun t => by
    rw [polar_smul_right_eq, hfw, mul_zero]
  have hγ : ∀ t : K, polar Q e (t • w) = 0 := fun t => by
    rw [polar_smul_right_eq, hew, mul_zero]
  have hd : (2 : K) * Q w ≠ 0 := mul_ne_zero h2 hwQ
  have hEf : ∀ t : K, e + t • w - (t ^ 2 * Q w) • f ∈ M := by
    intro t
    have h := hinv f hfA (t • w) (A.smul_mem t hwA) hfQ (hfγ t) e heM heA
    have hform : eichler Q f (t • w) e = e + t • w - (t ^ 2 * Q w) • f := by
      rw [eichler_apply hfQ (hfγ t), hef, polar_smul_right_eq, hew, mul_zero, zero_add,
        map_smul_eq_sq]
      module
    rwa [hform] at h
  have hgw : ∀ t : K, t • w - (t ^ 2 * Q w) • f ∈ M := by
    intro t
    convert M.sub_mem (hEf t) heM using 1
    abel
  have hsf : ∀ t : K, (-(2 * t * Q w)) • f ∈ M := by
    intro t
    have h := M.sub_mem (M.sub_mem (hgw (t + 1)) (hgw t)) (hgw 1)
    convert h using 1
    module
  have hKf : ∀ s : K, s • f ∈ M := by
    intro s
    convert hsf (-(s / (2 * Q w))) using 2
    field_simp
  have hfM : f ∈ M := by simpa using hKf 1
  have hwM : ∀ t : K, t • w ∈ M := by
    intro t
    have h := M.add_mem (hgw t) (hKf (t ^ 2 * Q w))
    rwa [sub_add_cancel] at h
  have hsq : ∀ t : K, (t ^ 2 * Q w) • e ∈ M := by
    intro t
    have h := hinv e heA (t • w) (A.smul_mem t hwA) heQ (hγ t) f hfM hfA
    have hform : eichler Q e (t • w) f = f + t • w - (t ^ 2 * Q w) • e := by
      rw [eichler_apply heQ (hγ t), hfe, hfγ t, zero_add, map_smul_eq_sq]
      module
    rw [hform] at h
    have h' := M.sub_mem (M.add_mem hfM (hwM t)) h
    rwa [sub_sub_cancel] at h'
  have hKe : ∀ s : K, (s * Q w) • e ∈ M := by
    intro s
    have h := M.sub_mem (hsq ((s + 1) / 2)) (hsq ((s - 1) / 2))
    have e4 : ((s + 1) / 2) ^ 2 * Q w - ((s - 1) / 2) ^ 2 * Q w = s * Q w := by
      field_simp
      ring
    rw [← sub_smul, e4] at h
    exact h
  have heM' : ∀ t : K, t • e ∈ M := by
    intro t
    have h := hKe (t / Q w)
    rwa [div_mul_cancel₀ t hwQ] at h
  intro a haA
  have hwf : polar Q w f = 0 := by rw [polar_comm, hfw]
  have hwe : polar Q w e = 0 := by rw [polar_comm, hew]
  have hww : polar Q w w = 2 * Q w := polar_self_eq_two_mul Q w
  have hli : LinearIndependent K ![e, f, w] := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    simp [Fin.sum_univ_three] at hg
    have hg0 : g 0 = 0 := by
      have h0 : polar Q (g 0 • e + g 1 • f + g 2 • w) f = polar Q 0 f := by rw [hg]
      rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, hef, polar_self_eq_zero hfQ, hwf, polar_zero_left] at h0
      simpa using h0
    have hg1 : g 1 = 0 := by
      have h1 : polar Q (g 0 • e + g 1 • f + g 2 • w) e = polar Q 0 e := by rw [hg]
      rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, polar_self_eq_zero heQ, hfe, hwe, polar_zero_left] at h1
      simpa using h1
    have hg2 : g 2 = 0 := by
      have h3' : polar Q (g 0 • e + g 1 • f + g 2 • w) w = polar Q 0 w := by rw [hg]
      rw [polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        polar_smul_left_eq, hew, hfw, hww, polar_zero_left] at h3'
      have h22 : g 2 * (2 * Q w) = 0 := by linear_combination h3'
      exact (mul_eq_zero.mp h22).resolve_right hd
    intro i
    fin_cases i
    · simpa using hg0
    · simpa using hg1
    · simpa using hg2
  have hspan : Submodule.span K (Set.range ![e, f, w]) = A := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heA
      · exact hfA
      · exact hwA
    · rw [finrank_span_eq_card hli, h3]
      simp
  have haS : a ∈ Submodule.span K (Set.range ![e, f, w]) := by
    rw [hspan]
    exact haA
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp haS
  have hc' : c 0 • e + c 1 • f + c 2 • w = a := by simpa [Fin.sum_univ_three] using hc
  rw [← hc']
  exact M.add_mem (M.add_mem (heM' _) (hKf _)) (hwM _)

theorem mem_of_invariant_three (h2 : (2 : K) ≠ 0) {A : Submodule K V} (hA : PolarNondegOn Q A)
    (h3 : finrank K A = 3) (M : AddSubgroup V)
    (hinv : ∀ x ∈ A, ∀ z ∈ A, Q x = 0 → polar Q x z = 0 → ∀ m ∈ M, m ∈ A →
      eichler Q x z m ∈ M)
    {y : V} (hyM : y ∈ M) (hyA : y ∈ A) (hy0 : y ≠ 0) : ∀ a ∈ A, a ∈ M := by
  obtain ⟨e, heM, heA, he0, heQ⟩ := exists_singular_mem_three h2 hA h3 M hinv hyM hyA hy0
  exact mem_of_invariant_of_singular_three h2 hA h3 M hinv heM heA he0 heQ

theorem exists_eichler_of_polar_ne_zero {Y : Submodule K V} (hY : PolarNondegOn Q Y)
    (hY3 : 3 ≤ Module.finrank K Y) {y e : V} (heY : e ∈ Y) (heQ : Q e = 0) (he0 : e ≠ 0)
    (hye : polar Q y e ≠ 0) : ∃ f ∈ Y, ∃ g ∈ Y, eichler Q f g y ≠ y := by
  obtain ⟨f, hfY, hfQ, hef⟩ := exists_partner_of_polarNondegOn hY heY he0 heQ
  obtain ⟨w, hwY, hew, -, hwQ⟩ := exists_nonsingular_perp_of_hyp hY hY3 heY hfY heQ hfQ hef
  refine ⟨e, heY, w, hwY, fun h => ?_⟩
  rw [eichler_apply heQ hew] at h
  have h' : polar Q y e • w = (polar Q y w + Q w * polar Q y e) • e := by
    linear_combination (norm := module) h
  have hq := congrArg (⇑Q) h'
  rw [map_smul_eq_sq, map_smul_eq_sq, heQ, mul_zero] at hq
  exact mul_ne_zero (pow_ne_zero 2 hye) hwQ hq

theorem exists_eichler_apply_ne {Y : Submodule K V} (hY : PolarNondegOn Q Y)
    (hY3 : 3 ≤ Module.finrank K Y) {y : V} (hyY : y ∈ Y) (hy0 : y ≠ 0) :
    ∃ e ∈ Y, ∃ f ∈ Y, eichler Q e f y ≠ y := by
  by_cases hyQ : Q y = 0
  · obtain ⟨e, heY, heQ, hye⟩ := exists_partner_of_polarNondegOn hY hyY hy0 hyQ
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [polar_zero_right] at hye
      exact zero_ne_one hye
    exact exists_eichler_of_polar_ne_zero hY hY3 heY heQ he0 (by rw [hye]; exact one_ne_zero)
  · obtain ⟨e, heY, he0, heQ⟩ := OrthBlk.exists_singular_of_three_le_any (S := Y) hY3
    by_cases hc : polar Q y e = 0
    · have hind : ∀ c : K, y ≠ c • e := by
        intro c hc'
        apply hyQ
        rw [hc', map_smul_eq_sq, heQ, mul_zero]
      obtain ⟨t, htY, hte, hty⟩ := OrthBlk.exists_perp_not_perp hY hyY heY hind
      have het : polar Q e t = 0 := by rw [polar_comm, hte]
      have hyt : polar Q y t ≠ 0 := by rwa [polar_comm]
      refine ⟨e, heY, t, htY, fun h => ?_⟩
      rw [eichler_apply heQ het] at h
      simp only [hc, zero_smul, add_zero, mul_zero] at h
      rw [sub_eq_self, smul_eq_zero] at h
      rcases h with h | h
      · exact hyt h
      · exact he0 h
    · exact exists_eichler_of_polar_ne_zero hY hY3 heY heQ he0 hc

theorem subset_rootSet_of_mixed_three (h2 : (2 : K) ≠ 0) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {Y : Submodule K V}
    (hY : PolarNondegOn Q Y) (hY3 : Module.finrank K Y = 3)
    (hYH : ∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ H) {s : V} (hs : ∀ y ∈ Y, polar Q s y = 0)
    (hmix : ∃ w ∈ rootSet Q H s, ∃ y ∈ Y, ∃ r : V, w = y + r ∧ (∀ z ∈ Y, polar Q z r = 0) ∧
      y ≠ 0) :
    ∀ y ∈ Y, y ∈ rootSet Q H s := by
  obtain ⟨w, hw, y, hyY, r, rfl, hr, hy0⟩ := hmix
  obtain ⟨e, heY, f, hfY, hne⟩ := exists_eichler_apply_ne hY hY3.ge hyY hy0
  have hg := hYH e heY f hfY
  have hgs : eichler Q e f s = s :=
    eichler_apply_of_polar_eq_zero (hs e heY) (hs f hfY)
  have hgr : eichler Q e f r = r :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hr e heY)
      (by rw [polar_comm]; exact hr f hfY)
  have h1 := rootSet_map hH hg hw
  rw [hgs, map_add, hgr] at h1
  have h2' := AddSubgroup.sub_mem _ h1 hw
  have h3 : eichler Q e f y + r - (y + r) = eichler Q e f y - y := by abel
  rw [h3] at h2'
  have hdY : eichler Q e f y - y ∈ Y := by
    by_cases h : Q e = 0 ∧ polar Q e f = 0
    · rw [eichler_apply h.1 h.2]
      have : y + polar Q y e • f - (polar Q y f + Q f * polar Q y e) • e - y =
          polar Q y e • f - (polar Q y f + Q f * polar Q y e) • e := by abel
      rw [this]
      exact Y.sub_mem (Y.smul_mem _ hfY) (Y.smul_mem _ heY)
    · exact absurd (by rw [eichler_of_not h]; rfl) hne
  have hd0 : eichler Q e f y - y ≠ 0 := sub_ne_zero.mpr hne
  intro y' hy'
  refine mem_of_invariant_three h2 hY hY3 (rootSet Q H s) ?_ h2' hdY hd0 y' hy'
  intro x hx z hz _ _ m hm _
  have hgx := hYH x hx z hz
  have hfix : eichler Q x z s = s := eichler_apply_of_polar_eq_zero (hs x hx) (hs z hz)
  have := rootSet_map hH hgx hm
  rwa [hfix] at this

end Three

end CFSG.LieType.SeitzGeneration

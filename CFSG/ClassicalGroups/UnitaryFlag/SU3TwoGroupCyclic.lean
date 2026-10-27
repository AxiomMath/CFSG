module

public import CFSG.ClassicalGroups.UnitaryFlag.InvolutionCenters
import CFSG.ClassicalGroups.UnitaryFlag.HomologyEigen

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K]

private theorem smul_eq_self_of_commute_of_pow_four (h : UnitaryFieldData 2 m K)
    {g z : unitarySU 2 m K 3} (hg4 : g ^ 4 = 1) (hcomm : g * z = z * g)
    {y : Fin 3 → K} (hy0 : y ≠ 0)
    (hY : LinearMap.range (subOne z) = K ∙ y) : g • y = y := by
  have : CharP K 2 := h.charP
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hconj : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [hcomm]
      _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hfix : g • (K ∙ y) = K ∙ y := by
    rw [← hY, ← range_subOne_conj h g z, hconj]
  have hmem : g • y ∈ K ∙ y := by
    rw [← hfix]
    exact Submodule.smul_mem_pointwise_smul y g (K ∙ y)
      (Submodule.mem_span_singleton_self y)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem
  have hb4 : b ^ 4 = 1 := by
    have h := pow_smul_eq_smul_pow (a := g) (e := y) (c := b) hb.symm 4
    rw [hg4, one_smul] at h
    have h2 : (b ^ 4 - 1) • y = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr h.symm
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hy0
  have hb1 : b = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 2 1 b).mp (by simpa using hb4)
  rw [← hb, hb1, one_smul]

private theorem smul_mem_hermPerp_of_commute (h : UnitaryFieldData 2 m K)
    {g z : unitarySU 2 m K 3} (hcomm : g * z = z * g)
    {L : Submodule K (Fin 3 → K)}
    (hker : LinearMap.ker (subOne z) = hermPerp h L) {v : Fin 3 → K}
    (hv : v ∈ hermPerp h L) : g • v ∈ hermPerp h L := by
  rw [← hker, LinearMap.mem_ker] at hv ⊢
  rw [subOne_apply h] at hv ⊢
  have hzv : z • v = v := sub_eq_zero.mp hv
  rw [← mul_smul, ← hcomm, mul_smul, hzv]
  exact sub_self _

private theorem sub_smul_mem_hermPerp (h : UnitaryFieldData 2 m K)
    {g : unitarySU 2 m K 3} {y w : Fin 3 → K} (hgy : g • y = y) :
    g • w - w ∈ hermPerp h (K ∙ y) := by
  rw [mem_hermPerp]
  intro a ha
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hiso : stdHermForm h 3 y (g • w) = stdHermForm h 3 y w := by
    have h := stdHermForm_smul_smul h g y w
    rwa [hgy] at h
  rw [map_sub]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hiso, sub_self]

private theorem exists_smul_shape (h : UnitaryFieldData 2 m K)
    {g z : unitarySU 2 m K 3} (hg4 : g ^ 4 = 1) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hcomm : g * z = z * g) {y c w : Fin 3 → K} (hy0 : y ≠ 0)
    (hYmem : K ∙ y ∈ isotropicLines h 3)
    (hY : LinearMap.range (subOne z) = K ∙ y)
    (hker : LinearMap.ker (subOne z) = hermPerp h (K ∙ y))
    (hc : c ∈ hermPerp h (K ∙ y)) (hcY : c ∉ K ∙ y) :
    ∃ α β γ : K, g • c = c + α • y ∧ g • w = w + β • y + γ • c := by
  have : CharP K 2 := h.charP
  have hgy : g • y = y := smul_eq_self_of_commute_of_pow_four h hg4 hcomm hy0 hY
  have hli : LinearIndependent K ![y, c] :=
    (LinearIndependent.pair_iff' hy0).mpr fun a ha =>
      hcY (by rw [← ha]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  have hperp : hermPerp h (K ∙ y) = Submodule.span K {y, c} :=
    hermPerp_eq_span_pair h hYmem rfl hc hcY
  have hgcmem : g • c ∈ Submodule.span K {y, c} := by
    rw [← hperp]
    exact smul_mem_hermPerp_of_commute h hcomm hker hc
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hgcmem
  have hgc0 : g • c = b • c + a • y := by rw [← hab]; abel
  have hcomm2 : Commute (g ^ 2) z := ((commute_iff_eq g z).mpr hcomm).pow_left 2
  have hg2inv : (g ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, hg4]
  have hg2c : g ^ 2 • c = b ^ 2 • c + (b * a + a) • y := by
    calc g ^ 2 • c = g • (g • c) := by rw [pow_two, mul_smul]
      _ = g • (b • c + a • y) := by rw [hgc0]
      _ = b • (g • c) + a • (g • y) := by
            rw [smul_add]
            congr 1
            · exact smul_comm g b c
            · exact smul_comm g a y
      _ = b • (b • c + a • y) + a • y := by rw [hgc0, hgy]
      _ = b ^ 2 • c + (b * a + a) • y := by
            rw [smul_add, smul_smul, smul_smul]
            module
  have hb2 : b ^ 2 = 1 := by
    have hsub : g ^ 2 • c - c ∈ K ∙ y := by
      by_cases hg2one : g ^ 2 = 1
      · rw [hg2one, one_smul, sub_self]
        exact Submodule.zero_mem _
      · have hrange := range_subOne_eq_of_commute h hg2inv hg2one hz2 hz1 hcomm2.eq
        have hmem : subOne (g ^ 2) c ∈ K ∙ y := by
          have h := LinearMap.mem_range_self (subOne (g ^ 2)) c
          rwa [hrange, hY] at h
        rwa [subOne_apply h] at hmem
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hsub
    have hd' : d • y = b ^ 2 • c + (b * a + a) • y - c := by
      rw [hg2c] at hd
      exact hd
    have hzero : (b * a + a - d) • y + (b ^ 2 - 1) • c = 0 := by
      rw [sub_smul, sub_smul, hd']
      simp only [one_smul]
      abel
    have hcoef := (LinearIndependent.pair_iff.mp hli) (b * a + a - d) (b ^ 2 - 1) hzero
    exact sub_eq_zero.mp hcoef.2
  have hb1 : b = 1 := CharTwo.sq_inj.mp (by rw [hb2, one_pow])
  have hgcfinal : g • c = c + a • y := by rw [hgc0, hb1, one_smul]
  have hgwmem : g • w - w ∈ Submodule.span K {y, c} := by
    rw [← hperp]
    exact sub_smul_mem_hermPerp h hgy
  obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.mp hgwmem
  refine ⟨a, a', b', hgcfinal, ?_⟩
  have hgw : g • w = w + (a' • y + b' • c) := by
    have h := sub_eq_iff_eq_add.mp hab'.symm
    rw [h, add_comm]
  simpa [add_assoc] using hgw

private theorem pow_two_smul_of_shape (h : UnitaryFieldData 2 m K)
    {g : unitarySU 2 m K 3} {y c w : Fin 3 → K} {α β γ : K}
    (hgy : g • y = y) (hgc : g • c = c + α • y)
    (hgw : g • w = w + β • y + γ • c) :
    g ^ 2 • w = w + (γ * α) • y := by
  have : CharP K 2 := h.charP
  have hself : ∀ x : Fin 3 → K, x + x = 0 := by
    intro x
    rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
  have hsmul : ∀ x : Fin 3 → K, g • x = x + subOne g x := by
    intro x
    rw [subOne_apply h]
    abel
  have hNy : subOne g y = 0 := by
    have h' : y + subOne g y = y + 0 := by rw [add_zero]; exact (hsmul y).symm.trans hgy
    exact add_left_cancel h'
  have hNc : subOne g c = α • y := by
    have h' : c + subOne g c = c + α • y := by rw [← hsmul c]; exact hgc
    exact add_left_cancel h'
  have hNw : subOne g w = β • y + γ • c := by
    have h' : w + subOne g w = w + (β • y + γ • c) := by
      rw [← hsmul w, hgw, add_assoc]
    exact add_left_cancel h'
  have hNN : subOne g (subOne g w) = (γ * α) • y := by
    rw [hNw, map_add, map_smul, map_smul, hNy, hNc, smul_zero, zero_add, smul_smul]
  calc g ^ 2 • w = g • (g • w) := by rw [pow_two, mul_smul]
    _ = g • (w + subOne g w) := by rw [hsmul w]
    _ = g • w + g • subOne g w := by rw [smul_add]
    _ = (w + subOne g w) + (subOne g w + subOne g (subOne g w)) := by
          rw [hsmul w, hsmul]
    _ = w + subOne g (subOne g w) := by
          have h : subOne g w + subOne g w = 0 := hself _
          calc (w + subOne g w) + (subOne g w + subOne g (subOne g w))
              = (w + subOne g (subOne g w)) + (subOne g w + subOne g w) := by abel
            _ = (w + subOne g (subOne g w)) + 0 := by rw [h]
            _ = w + subOne g (subOne g w) := add_zero _
    _ = w + (γ * α) • y := by rw [hNN]

private theorem pow_two_smul_of_two_shapes (h : UnitaryFieldData 2 m K)
    {g g' : unitarySU 2 m K 3} {y c w : Fin 3 → K} {α β γ α' β' γ' : K}
    (hgy : g' • y = y) (hgc : g' • c = c + α' • y)
    (hgw : g' • w = w + β' • y + γ' • c)
    (hgy' : g • y = y) (hgc' : g • c = c + α • y)
    (hgw' : g • w = w + β • y + γ • c) :
    (g * g') ^ 2 • w = w + ((γ + γ') * (α + α')) • y := by
  have hpy : (g * g') • y = y := by rw [mul_smul, hgy, hgy']
  have hpc : (g * g') • c = c + (α + α') • y := by
    calc (g * g') • c = g • (g' • c) := by rw [mul_smul]
      _ = g • (c + α' • y) := by rw [hgc]
      _ = g • c + α' • (g • y) := by rw [smul_add, smul_comm]
      _ = (c + α • y) + α' • y := by rw [hgc', hgy']
      _ = c + (α + α') • y := by rw [add_assoc, ← add_smul]
  have hpw : (g * g') • w = w + (β + β' + γ' * α) • y + (γ + γ') • c := by
    calc (g * g') • w = g • (g' • w) := by rw [mul_smul]
      _ = g • (w + β' • y + γ' • c) := by rw [hgw]
      _ = g • w + β' • (g • y) + γ' • (g • c) := by
            rw [smul_add, smul_add]
            congr 1
            · congr 1
              exact smul_comm g β' y
            · exact smul_comm g γ' c
      _ = (w + β • y + γ • c) + β' • y + γ' • (c + α • y) := by rw [hgw', hgy', hgc']
      _ = w + (β + β' + γ' * α) • y + (γ + γ') • c := by
            rw [smul_add]
            module
  rw [pow_two_smul_of_shape h hpy hpc hpw]

private theorem bar_alpha_mul_hyw_eq_gamma_mul_hcc (h : UnitaryFieldData 2 m K)
    {g : unitarySU 2 m K 3} {y c w : Fin 3 → K} {α β γ : K}
    (hgc : g • c = c + α • y) (hgw : g • w = w + β • y + γ • c)
    (hyy : stdHermForm h 3 y y = 0)
    (hyc : stdHermForm h 3 y c = 0) (hcy : stdHermForm h 3 c y = 0) :
    h.bar α * stdHermForm h 3 y w = γ * stdHermForm h 3 c c := by
  have : CharP K 2 := h.charP
  have hexp : stdHermForm h 3 (c + α • y) (w + β • y + γ • c) =
      stdHermForm h 3 c w + γ * stdHermForm h 3 c c + h.bar α * stdHermForm h 3 y w := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      hyy, hyc, hcy, mul_zero, add_zero, RingHom.id_apply]
    ring
  have hiso := stdHermForm_smul_smul h g c w
  rw [hgc, hgw, hexp] at hiso
  have h0 : γ * stdHermForm h 3 c c + h.bar α * stdHermForm h 3 y w = 0 := by
    linear_combination hiso
  exact (CharTwo.add_eq_zero.mp h0).symm

theorem pow_four_eq_one_of_pow_two_pow_eq_one (h : UnitaryFieldData 2 m K)
    {u : unitarySU 2 m K 3} {k : ℕ} (hu : u ^ 2 ^ k = 1) : u ^ 4 = 1 := by
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Matrix (Fin 3) (Fin 3) K := ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hA : A ^ (2 ^ k) = 1 := by
    have hc := congrArg (fun g : unitarySU 2 m K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hu
    simpa [A, Subgroup.coe_pow] using hc
  let N : Matrix (Fin 3) (Fin 3) K := A - 1
  have hN : N ^ (2 ^ k) = 0 := by
    have hsp := sub_pow_char_pow_of_commute (x := A) (y := (1 : Matrix (Fin 3) (Fin 3) K)) 2 k
      (Commute.one_right A)
    rw [hA, one_pow, sub_self] at hsp
    simpa [N] using hsp
  have hNil : IsNilpotent N := ⟨2 ^ k, hN⟩
  let φ : Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv' N
  have hφnil : IsNilpotent φ := hNil.map Matrix.toLinAlgEquiv'
  have hφ3 : φ ^ 3 = 0 := by
    have hchar := IsNilpotent.charpoly_eq_X_pow_finrank hφnil
    have hfr : Module.finrank K (Fin 3 → K) = 3 := by rw [Module.finrank_fin_fun K]
    have haeval := LinearMap.aeval_self_charpoly φ
    rw [hchar, hfr] at haeval
    simpa only [map_pow, Polynomial.aeval_X] using haeval
  have hN3 : N ^ 3 = 0 := by
    have : Matrix.toLinAlgEquiv' (N ^ 3) = Matrix.toLinAlgEquiv' 0 := by
      rw [map_pow]
      simpa using hφ3
    simpa using Matrix.toLinAlgEquiv'.injective this
  have hN4 : N ^ 4 = 0 := by
    rw [show (4:ℕ) = 3 + 1 by norm_num, pow_add, hN3, zero_mul]
  have hA4 : A ^ 4 = 1 := by
    have hAeq : A = N + 1 := by
      show A = A - 1 + 1
      abel
    rw [hAeq]
    have hadd := add_pow_char_pow_of_commute (x := N) (y := (1 : Matrix (Fin 3) (Fin 3) K)) 2 2
      (Commute.one_right N)
    rw [show 2 ^ 2 = 4 by norm_num] at hadd
    rw [hadd, hN4, one_pow, zero_add]
  refine Subtype.ext (Units.ext ?_)
  simpa [A, Subgroup.coe_pow] using hA4

private theorem exists_geometry (h : UnitaryFieldData 2 m K) {u : unitarySU 2 m K 3}
    (h4 : u ^ 4 = 1) (hu : u ^ 2 ≠ 1) :
    ∃ (z : unitarySU 2 m K 3) (y c w : Fin 3 → K),
      z = u ^ 2 ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
      y ≠ 0 ∧ stdHermForm h 3 y y = 0 ∧
      LinearMap.range (subOne z) = K ∙ y ∧
      LinearMap.ker (subOne z) = hermPerp h (K ∙ y) ∧
      K ∙ y ∈ isotropicLines h 3 ∧
      c ∈ hermPerp h (K ∙ y) ∧ c ∉ K ∙ y ∧
      stdHermForm h 3 c c ≠ 0 ∧
      stdHermForm h 3 y c = 0 ∧ stdHermForm h 3 c y = 0 ∧
      stdHermForm h 3 y w ≠ 0 := by
  have hz2 : (u ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num]
    exact h4
  obtain ⟨hYiso, -, hker⟩ := involution_mem_isotropicTransvectionGroup h hz2 hu
  obtain ⟨y, hy0, hyiso, hYeq⟩ := exists_eq_span_of_mem_isotropicLines hYiso
  have hYmem : K ∙ y ∈ isotropicLines h 3 := hYeq ▸ hYiso
  have hker' : LinearMap.ker (subOne (u ^ 2)) = hermPerp h (K ∙ y) := by
    rw [hYeq] at hker
    exact hker
  have hle : K ∙ y ≤ hermPerp h (K ∙ y) := le_hermPerp_self hYmem
  have hne : K ∙ y ≠ hermPerp h (K ∙ y) := by
    intro heq
    have hfr := finrank_hermPerp hYmem
    rw [← heq, finrank_span_singleton hy0] at hfr
    omega
  have hlt : K ∙ y < hermPerp h (K ∙ y) := lt_of_le_of_ne hle hne
  obtain ⟨-, c, hc, hcY⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  have hcc : stdHermForm h 3 c c ≠ 0 :=
    stdHermForm_self_ne_zero_of_mem_hermPerp h hYmem hc hcY
  have hhyc : stdHermForm h 3 y c = 0 :=
    (mem_hermPerp.mp hc) y (Submodule.mem_span_singleton_self y)
  have hhcy : stdHermForm h 3 c y = 0 := by
    rw [← (stdHermForm_isSymm h 3).eq y c, hhyc, map_zero]
  obtain ⟨w, hyw⟩ : ∃ w, stdHermForm h 3 y w ≠ 0 := by
    by_contra hw
    push Not at hw
    exact hy0 (stdHermForm_separatingLeft h 3 y hw)
  exact ⟨u ^ 2, y, c, w, rfl, hz2, hu, hy0, hyiso, hYeq, hker', hYmem, hc, hcY,
    hcc, hhyc, hhcy, hyw⟩

private theorem square_relations (h : UnitaryFieldData 2 m K)
    {u₁ u₂ z : unitarySU 2 m K 3} {y c w : Fin 3 → K}
    {α₁ β₁ γ₁ α₂ β₂ γ₂ : K}
    (hy0 : y ≠ 0) (hz : z = u₁ ^ 2)
    (hu₁y : u₁ • y = y) (hu₁c : u₁ • c = c + α₁ • y)
    (hu₁w : u₁ • w = w + β₁ • y + γ₁ • c)
    (hu₂y : u₂ • y = y) (hu₂c : u₂ • c = c + α₂ • y)
    (hu₂w : u₂ • w = w + β₂ • y + γ₂ • c)
    (h12 : u₂ ^ 2 = u₁ ^ 2) (h3 : (u₁ * u₂) ^ 2 = u₁ ^ 2)
    (hker : LinearMap.ker (subOne z) = hermPerp h (K ∙ y))
    (hyw : stdHermForm h 3 y w ≠ 0) :
    γ₂ * α₂ = γ₁ * α₁ ∧ (γ₁ + γ₂) * (α₁ + α₂) = γ₁ * α₁ ∧ γ₁ * α₁ ≠ 0 := by
  have hu₁sqw : u₁ ^ 2 • w = w + (γ₁ * α₁) • y :=
    pow_two_smul_of_shape h hu₁y hu₁c hu₁w
  have hu₂sqw : u₂ ^ 2 • w = w + (γ₂ * α₂) • y :=
    pow_two_smul_of_shape h hu₂y hu₂c hu₂w
  have hprodw : (u₁ * u₂) ^ 2 • w = w + ((γ₁ + γ₂) * (α₁ + α₂)) • y :=
    pow_two_smul_of_two_shapes h hu₂y hu₂c hu₂w hu₁y hu₁c hu₁w
  have hzw : z • w = w + (γ₁ * α₁) • y := by
    rw [hz]
    exact hu₁sqw
  have hγα : γ₁ * α₁ ≠ 0 := by
    intro h0
    have hzw' : z • w = w := by rw [hzw, h0, zero_smul, add_zero]
    have hwker : w ∈ LinearMap.ker (subOne z) := by
      rw [LinearMap.mem_ker, subOne_apply h, hzw', sub_self]
    rw [hker] at hwker
    exact hyw ((mem_hermPerp.mp hwker) y (Submodule.mem_span_singleton_self y))
  have h12eq : γ₂ * α₂ = γ₁ * α₁ := by
    have h := congrArg (fun g : unitarySU 2 m K 3 => g • w) h12
    rw [hu₂sqw, hu₁sqw] at h
    have h2 : (γ₂ * α₂) • y = (γ₁ * α₁) • y := add_left_cancel h
    have h3' : (γ₂ * α₂ - γ₁ * α₁) • y = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3' with h4' | h4'
    · exact sub_eq_zero.mp h4'
    · exact absurd h4' hy0
  have h3eq : (γ₁ + γ₂) * (α₁ + α₂) = γ₁ * α₁ := by
    have h := congrArg (fun g : unitarySU 2 m K 3 => g • w) h3
    rw [hprodw, hu₁sqw] at h
    have h2 : ((γ₁ + γ₂) * (α₁ + α₂)) • y = (γ₁ * α₁) • y := add_left_cancel h
    have h3' : ((γ₁ + γ₂) * (α₁ + α₂) - γ₁ * α₁) • y = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3' with h4' | h4'
    · exact sub_eq_zero.mp h4'
    · exact absurd h4' hy0
  exact ⟨h12eq, h3eq, hγα⟩

private theorem alpha_eq_of_bar_mul_eq (h : UnitaryFieldData 2 m K) {α γ hcc hyw : K}
    (hyw0 : hyw ≠ 0) (hrel : h.bar α * hyw = γ * hcc) :
    α = h.bar γ * h.bar (hcc / hyw) := by
  have hbaryw0 : h.bar hyw ≠ 0 := fun h0 => hyw0 (h.bar_eq_zero_iff.mp h0)
  have hbar : α * h.bar hyw = h.bar γ * h.bar hcc := by
    have hh := congrArg h.bar hrel
    simpa only [map_mul, h.bar_bar] using hh
  calc α = (h.bar γ * h.bar hcc) / h.bar hyw := (eq_div_iff hbaryw0).mpr hbar
    _ = h.bar γ * (h.bar hcc / h.bar hyw) := by ring
    _ = h.bar γ * h.bar (hcc / hyw) := by rw [map_div₀]

private theorem exists_rho_norm_trace (h : UnitaryFieldData 2 m K)
    {γ₁ γ₂ α₁ α₂ hcc hyw : K}
    (hcc0 : hcc ≠ 0) (hyw0 : hyw ≠ 0) (hγα : γ₁ * α₁ ≠ 0)
    (h12eq : γ₂ * α₂ = γ₁ * α₁)
    (h3eq : (γ₁ + γ₂) * (α₁ + α₂) = γ₁ * α₁)
    (hrel₁ : h.bar α₁ * hyw = γ₁ * hcc)
    (hrel₂ : h.bar α₂ * hyw = γ₂ * hcc) :
    ∃ ρ : K, ρ * h.bar ρ = 1 ∧ ρ + h.bar ρ = 1 := by
  have : CharP K 2 := h.charP
  have hα₁ : α₁ = h.bar γ₁ * h.bar (hcc / hyw) := alpha_eq_of_bar_mul_eq h hyw0 hrel₁
  have hα₂ : α₂ = h.bar γ₂ * h.bar (hcc / hyw) := alpha_eq_of_bar_mul_eq h hyw0 hrel₂
  let κ : K := h.bar (hcc / hyw)
  have hα₁' : α₁ = h.bar γ₁ * κ := hα₁
  have hα₂' : α₂ = h.bar γ₂ * κ := hα₂
  have hκ0 : κ ≠ 0 := by
    dsimp only [κ]
    rw [map_div₀]
    exact div_ne_zero (fun h0 => hcc0 (h.bar_eq_zero_iff.mp h0))
      (fun h0 => hyw0 (h.bar_eq_zero_iff.mp h0))
  have hsα : α₁ + α₂ = h.bar (γ₁ + γ₂) * κ := by
    rw [hα₁', hα₂', map_add, add_mul]
  have h12norm : γ₂ * h.bar γ₂ = γ₁ * h.bar γ₁ := by
    have h : (γ₂ * h.bar γ₂) * κ = (γ₁ * h.bar γ₁) * κ := by
      calc (γ₂ * h.bar γ₂) * κ = γ₂ * (h.bar γ₂ * κ) := by rw [mul_assoc]
        _ = γ₂ * α₂ := by rw [← hα₂']
        _ = γ₁ * α₁ := h12eq
        _ = γ₁ * (h.bar γ₁ * κ) := by rw [hα₁']
        _ = (γ₁ * h.bar γ₁) * κ := by rw [mul_assoc]
    exact mul_right_cancel₀ hκ0 h
  have h3norm : (γ₁ + γ₂) * h.bar (γ₁ + γ₂) = γ₁ * h.bar γ₁ := by
    have h : ((γ₁ + γ₂) * h.bar (γ₁ + γ₂)) * κ = (γ₁ * h.bar γ₁) * κ := by
      calc ((γ₁ + γ₂) * h.bar (γ₁ + γ₂)) * κ
          = (γ₁ + γ₂) * (h.bar (γ₁ + γ₂) * κ) := by rw [mul_assoc]
        _ = (γ₁ + γ₂) * (α₁ + α₂) := by rw [← hsα]
        _ = γ₁ * α₁ := h3eq
        _ = γ₁ * (h.bar γ₁ * κ) := by rw [hα₁']
        _ = (γ₁ * h.bar γ₁) * κ := by rw [mul_assoc]
    exact mul_right_cancel₀ hκ0 h
  have hγ₁0 : γ₁ ≠ 0 := fun h0 => hγα (by rw [h0, zero_mul])
  have hbarγ₁0 : h.bar γ₁ ≠ 0 := fun h0 => hγ₁0 (h.bar_eq_zero_iff.mp h0)
  let ρ : K := γ₂ / γ₁
  have hρnorm : ρ * h.bar ρ = 1 := by
    dsimp only [ρ]
    rw [map_div₀]
    field_simp [hγ₁0, hbarγ₁0]
    linear_combination h12norm
  have hρtrace : ρ + h.bar ρ = 1 := by
    have hs : γ₁ + γ₂ = γ₁ * (1 + ρ) := by
      dsimp only [ρ]
      field_simp [hγ₁0]
    have h' : (γ₁ * (1 + ρ)) * (h.bar γ₁ * (1 + h.bar ρ)) = γ₁ * h.bar γ₁ := by
      simpa only [hs, map_mul, map_add, map_one] using h3norm
    have h2 : (1 + ρ) * (1 + h.bar ρ) = 1 := by
      have h0 : γ₁ * h.bar γ₁ ≠ 0 := mul_ne_zero hγ₁0 hbarγ₁0
      refine mul_left_cancel₀ h0 ?_
      calc (γ₁ * h.bar γ₁) * ((1 + ρ) * (1 + h.bar ρ))
          = (γ₁ * (1 + ρ)) * (h.bar γ₁ * (1 + h.bar ρ)) := by ring
        _ = γ₁ * h.bar γ₁ := h'
        _ = (γ₁ * h.bar γ₁) * 1 := by rw [mul_one]
    have hexp : (1 + ρ) * (1 + h.bar ρ) = 1 + (ρ + h.bar ρ) + ρ * h.bar ρ := by ring
    rw [hexp, hρnorm] at h2
    have h3 : 1 + (ρ + h.bar ρ) + 1 = (ρ + h.bar ρ) := by
      calc 1 + (ρ + h.bar ρ) + 1 = (ρ + h.bar ρ) + (1 + 1) := by abel
        _ = (ρ + h.bar ρ) + 0 := by rw [CharTwo.add_self_eq_zero]
        _ = ρ + h.bar ρ := add_zero _
    rwa [h3] at h2
  exact ⟨ρ, hρnorm, hρtrace⟩

private theorem false_of_rho (h : UnitaryFieldData 2 m K) (hm : Even m) {ρ : K}
    (hρnorm : ρ * h.bar ρ = 1) (hρtrace : ρ + h.bar ρ = 1) : False := by
  have : CharP K 2 := h.charP
  have hρ2 : ρ ^ 2 = ρ + 1 := by
    have h2 : ρ ^ 2 + 1 = ρ := by
      calc ρ ^ 2 + 1 = ρ ^ 2 + ρ * h.bar ρ := by rw [hρnorm]
        _ = (ρ + h.bar ρ) * ρ := by
              rw [add_mul, mul_comm (h.bar ρ) ρ]
              ring
        _ = 1 * ρ := by rw [hρtrace]
        _ = ρ := one_mul ρ
    have h' := congrArg (· + 1) h2
    rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h'
  have hρ3 : ρ ^ 3 = 1 := by
    calc ρ ^ 3 = ρ * ρ ^ 2 := by ring
      _ = ρ * (ρ + 1) := by rw [hρ2]
      _ = 1 := by
            rw [mul_add, mul_one, ← pow_two, hρ2]
            calc (ρ + 1) + ρ = (ρ + ρ) + 1 := by abel
              _ = 0 + 1 := by rw [CharTwo.add_self_eq_zero]
              _ = 1 := zero_add 1
  have h3dvd : 3 ∣ 2 ^ m - 1 := by
    obtain ⟨t, rfl⟩ := hm
    have h := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) t
    rw [← pow_mul, show 2 * t = t + t by omega] at h
    simpa using h
  obtain ⟨k, hk⟩ := h3dvd
  have h2m : 2 ^ m = 3 * k + 1 := by
    have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
    omega
  have hbarρ : h.bar ρ = ρ := by
    rw [h.bar_apply]
    calc ρ ^ 2 ^ m = ρ ^ (3 * k + 1) := by rw [h2m]
      _ = (ρ ^ 3) ^ k * ρ := by rw [pow_add, pow_mul, pow_one]
      _ = ρ := by rw [hρ3, one_pow, one_mul]
  have hcontra : ρ + h.bar ρ = 1 := hρtrace
  rw [hbarρ] at hcontra
  have hzero : ρ + ρ = 0 := CharTwo.add_self_eq_zero ρ
  rw [hzero] at hcontra
  exact zero_ne_one hcontra

theorem sq_eq_one_of_sq_eq_of_mul_sq_eq (h : UnitaryFieldData 2 m K) (hm : Even m)
    {u₁ u₂ : unitarySU 2 m K 3} (h4 : u₁ ^ 4 = 1) (h12 : u₂ ^ 2 = u₁ ^ 2)
    (h3 : (u₁ * u₂) ^ 2 = u₁ ^ 2) : u₁ ^ 2 = 1 := by
  have : CharP K 2 := h.charP
  by_contra hz1
  obtain ⟨z, y, c, w, hz_eq, hz2, hz1', hy0, hyiso, hYeq, hker, hYmem, hc, hcY,
    hcc, hhyc, hhcy, hyw⟩ := exists_geometry h h4 hz1
  have hu₂4 : u₂ ^ 4 = 1 := by
    have h : u₂ ^ 4 = (u₂ ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h, h12, ← hz_eq]
    exact hz2
  have hcomm1 : u₁ * z = z * u₁ := by
    rw [hz_eq]
    group
  have hcomm2 : u₂ * z = z * u₂ := by
    rw [hz_eq, ← h12]
    group
  have hu₁y : u₁ • y = y := smul_eq_self_of_commute_of_pow_four h h4 hcomm1 hy0 hYeq
  have hu₂y : u₂ • y = y := smul_eq_self_of_commute_of_pow_four h hu₂4 hcomm2 hy0 hYeq
  obtain ⟨α₁, β₁, γ₁, hu₁c, hu₁w⟩ :=
    exists_smul_shape h h4 hz2 hz1' hcomm1 hy0 hYmem hYeq hker hc hcY
  obtain ⟨α₂, β₂, γ₂, hu₂c, hu₂w⟩ :=
    exists_smul_shape h hu₂4 hz2 hz1' hcomm2 hy0 hYmem hYeq hker hc hcY
  obtain ⟨h12eq, h3eq, hγα⟩ :=
    square_relations h hy0 hz_eq hu₁y hu₁c hu₁w hu₂y hu₂c hu₂w h12 h3 hker hyw
  have hrel₁ : h.bar α₁ * stdHermForm h 3 y w = γ₁ * stdHermForm h 3 c c :=
    bar_alpha_mul_hyw_eq_gamma_mul_hcc h hu₁c hu₁w hyiso hhyc hhcy
  have hrel₂ : h.bar α₂ * stdHermForm h 3 y w = γ₂ * stdHermForm h 3 c c :=
    bar_alpha_mul_hyw_eq_gamma_mul_hcc h hu₂c hu₂w hyiso hhyc hhcy
  obtain ⟨ρ, hρnorm, hρtrace⟩ :=
    exists_rho_norm_trace h hcc hyw hγα h12eq h3eq hrel₁ hrel₂
  exact false_of_rho h hm hρnorm hρtrace

private theorem sq_eq_z_of_notMem_zpowers
    {S : Subgroup (unitarySU 2 m K 3)} {z w u : unitarySU 2 m K 3}
    (hz : ∀ t ∈ S, t ^ 2 = 1 → t = 1 ∨ t = z)
    (huz : u ∉ Subgroup.zpowers w) (hzw : z ∈ Subgroup.zpowers w)
    (huS : u ∈ S) (hupow : u ^ 4 = 1) :
    u ^ 2 = z ∧ u ^ 2 ≠ 1 := by
  have hu1 : u ≠ 1 := fun h1 => huz (h1.symm ▸ Subgroup.one_mem _)
  have huz' : u ≠ z := fun h1 => huz (h1.symm ▸ hzw)
  have hsq_ne : u ^ 2 ≠ 1 := by
    intro hsq
    rcases hz u huS hsq with h1 | h1
    · exact hu1 h1
    · exact huz' h1
  have hsq : u ^ 2 = z := by
    have hmem : u ^ 2 ∈ S := S.pow_mem huS 2
    have hpow : (u ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * 2 = 4 by norm_num]
      exact hupow
    rcases hz _ hmem hpow with h1 | h1
    · exact absurd h1 hsq_ne
    · exact h1
  exact ⟨hsq, hsq_ne⟩

theorem isCyclic_of_isPGroup_of_forall_sq_eq_one (h : UnitaryFieldData 2 m K) (hm : Even m)
    {S : Subgroup (unitarySU 2 m K 3)} (hS : IsPGroup 2 S) (z : unitarySU 2 m K 3)
    (hz : ∀ t ∈ S, t ^ 2 = 1 → t = 1 ∨ t = z) : IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hScyc
  have h4 : ∀ t ∈ S, t ^ 4 = 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := hS.exists_orderOf_eq_pow (⟨t, ht⟩ : S)
    rw [Subgroup.orderOf_mk] at hk
    exact pow_four_eq_one_of_pow_two_pow_eq_one h (by rw [← hk, pow_orderOf_eq_one])
  by_cases hle : S ≤ Subgroup.zpowers z
  · exact hScyc (Subgroup.isCyclic_of_le hle)
  obtain ⟨u₁, hu₁S, hu₁z⟩ := SetLike.not_le_iff_exists.mp hle
  obtain ⟨hu₁sq, hu₁sq_ne⟩ :=
    sq_eq_z_of_notMem_zpowers hz hu₁z (Subgroup.mem_zpowers z) hu₁S (h4 u₁ hu₁S)
  have hSne : ¬ S ≤ Subgroup.zpowers u₁ := fun hle' => hScyc (Subgroup.isCyclic_of_le hle')
  obtain ⟨u₂, hu₂S, hu₂pow⟩ := SetLike.not_le_iff_exists.mp hSne
  have hzmem : z ∈ Subgroup.zpowers u₁ := hu₁sq ▸ Subgroup.npow_mem_zpowers u₁ 2
  obtain ⟨hu₂sq, -⟩ :=
    sq_eq_z_of_notMem_zpowers hz hu₂pow hzmem hu₂S (h4 u₂ hu₂S)
  have hprodS : u₁ * u₂ ∈ S := S.mul_mem hu₁S hu₂S
  have hprod_pow : u₁ * u₂ ∉ Subgroup.zpowers u₁ := by
    intro hmem
    apply hu₂pow
    have h2 : u₂ = u₁⁻¹ * (u₁ * u₂) := by group
    rw [h2]
    exact (Subgroup.zpowers u₁).mul_mem
      ((Subgroup.zpowers u₁).inv_mem (Subgroup.mem_zpowers u₁)) hmem
  obtain ⟨hprodsq, -⟩ :=
    sq_eq_z_of_notMem_zpowers hz hprod_pow hzmem hprodS (h4 _ hprodS)
  exact hu₁sq_ne (sq_eq_one_of_sq_eq_of_mul_sq_eq h hm (h4 u₁ hu₁S)
    (hu₂sq.trans hu₁sq.symm) (hprodsq.trans hu₁sq.symm))

end CFSG.ClassicalGroups.UnitaryFlag

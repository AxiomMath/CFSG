module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodUnitary
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsY
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Polynomial Module Matrix CFSG.Open
open scoped commutatorElement
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitaryLines
  CFSG.RankThree.PartOne.KCUnitaryThree CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryPair
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryRegular

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_le_fixSubgroup_map_conj_eq {S : Type} [Group S]
    (hZ : Subgroup.center S = ⊥) {β : MulAut S} {J : Subgroup (MulAut S)}
    (hJ : J ≤ inner S ⊓ Subgroup.centralizer ({β} : Set (MulAut S))) :
    ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ P.map (MulAut.conj : S →* MulAut S) = J := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := chevToolsY_conj_injective hZ
  have hJinner : J ≤ (MulAut.conj : S →* MulAut S).range :=
    hJ.trans inf_le_left
  refine ⟨J.comap (MulAut.conj : S →* MulAut S), ?_, ?_⟩
  · intro x hx
    have hxJ : MulAut.conj x ∈ J := hx
    have hxmap : MulAut.conj x ∈ (fixSubgroup β).map (MulAut.conj : S →* MulAut S) := by
      rw [← chevToolsY_inner_inf_centralizer hZ β]
      exact hJ hxJ
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hxy : y = x := hinj hyx
    rwa [← hxy]
  · rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hJinner

theorem exists_perfect_fixSubgroup_of_onPair (hn : 3 ≤ n) (hne : ¬ (n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ p = 1)
    {u v : Fin n → K} {μ : K} (huv : IsONPair h u v)
    (hu : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) u = μ • u)
    (hv : ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = μ • v) :
    ∃ P : Subgroup (primeFormP h (idGram K n)),
      P ≤ fixSubgroup (primeFormConjHom h (idGram K n) x) ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  classical
  have := h.finite
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hpℓ : p ≠ ℓ := ne_char_of_dvd_add_one hp hpq h.one_le
  have hxgl : (x : GL (Fin n) K) ^ p =
      GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    have h := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hx
    simpa using h
  have H0 := primaryData_of_pow_eq_scalar hp hpℓ hxgl
  obtain ⟨hmem, hgood⟩ := isGoodBlock_of_eigenpair (h := h) hq3 huv hu hv
  have hμp : μ ^ p = 1 := eigenvalue_pow_eq_one hx huv.ne_zero_left hu
  have hμ : h.bar μ * μ = 1 := bar_eq_inv_of_pow_eq_one h hpq hμp
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp hpq
  have hJp : p ∣ Nat.card ((gBlock h x (X - C μ)).map
      (primeFormConjHom h (idGram K n))) :=
    dvd_card_map_gBlock_of_torus hp hp2 hn hne H0 hμ hmem huv hu hv hζ hζn
  have hJq : CFSG.IsQuasisimple ((gBlock h x (X - C μ)).map
      (primeFormConjHom h (idGram K n))) :=
    isQuasisimple_map_gBlock hn hne hq2 H0 ⟨X - C μ, hmem⟩ hgood
  have hJle : (gBlock h x (X - C μ)).map (primeFormConjHom h (idGram K n)) ≤
      inner (primeFormP h (idGram K n)) ⊓
        Subgroup.centralizer ({primeFormConjHom h (idGram K n) x} :
          Set (MulAut (primeFormP h (idGram K n)))) :=
    map_gBlock_le hq2 H0 ⟨X - C μ, hmem⟩ hgood le_rfl
  have hZ : Subgroup.center (primeFormP h (idGram K n)) = ⊥ :=
    center_primeFormP_eq_bot h isPrimeFormGram_idGram hn hne
  obtain ⟨P, hPle, hPmap⟩ := exists_le_fixSubgroup_map_conj_eq hZ hJle
  refine ⟨P, hPle, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥((gBlock h x (X - C μ)).map
        (primeFormConjHom h (idGram K n))) := hJq.1
    apply Subgroup.map_injective (chevToolsY_conj_injective hZ)
    rw [Subgroup.map_commutator, hPmap, Subgroup.commutator_eq_self]
  · rw [← Subgroup.card_map_of_injective (chevToolsY_conj_injective hZ), hPmap]
    exact hJp


private theorem exists_scalar_conj_eq_of_commute (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) {G X : primeFormUnitary h (idGram K n)}
    (hcomm : primeFormConjHom h (idGram K n) G * primeFormConjHom h (idGram K n) X =
      primeFormConjHom h (idGram K n) X * primeFormConjHom h (idGram K n) G) :
    ∃ α : Kˣ, (G : GL (Fin n) K) * (X : GL (Fin n) K) * (G : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) α * (X : GL (Fin n) K) := by
  have h1 : primeFormConjHom h (idGram K n) (((G * X * G⁻¹) * X⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, map_inv, hcomm]
    group
  obtain ⟨α, -, hα⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
  refine ⟨α, ?_⟩
  have h3 := congrArg (fun g : GL (Fin n) K => g * (X : GL (Fin n) K)) hα
  simpa [Subgroup.coe_mul, mul_assoc] using h3

private theorem exists_lift_pow_eq_one_of_plane (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    {A B : primeFormUnitary h (idGram K n)} {u v : MulAut (primeFormP h (idGram K n))}
    (hA : primeFormConjHom h (idGram K n) A = u)
    (hB : primeFormConjHom h (idGram K n) B = v)
    (huD : u ∈ D) (hvD : v ∈ D) (hu1 : u ≠ 1)
    (hvnot : v ∉ Subgroup.zpowers u)
    {a b : Kˣ} (han : h.norm (a : K) = 1) (hbn : h.norm (b : K) = 1)
    (hAp : (A : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a)
    (hBp : (B : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) b) :
    ∃ X : primeFormUnitary h (idGram K n), X ^ p = 1 ∧
      primeFormConjHom h (idGram K n) X ∈ D ∧
      primeFormConjHom h (idGram K n) X ≠ 1 := by
  classical
  have := h.finite
  have hn0 : 0 < n := by omega
  have hcomm_uv : u * v = v * u :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨u, huD⟩ ⟨v, hvD⟩)
  have hcommAB : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) A := by
    rw [hA, hB]
    exact hcomm_uv
  obtain ⟨d, hABconj⟩ := exists_scalar_conj_eq_of_commute hn hne hcommAB
  by_cases hap : ∃ u' : Kˣ, u' ^ p = a
  · obtain ⟨u', rfl⟩ := hap
    have hun : h.norm (u' : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using han)
    have hu'n : h.norm ((u'⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hun
    refine ⟨scalarU h n u'⁻¹ hu'n * A, rescale_pow_eq_one hn hne hu'n hAp, ?_, ?_⟩
    · rw [map_mul, conjHom_scalarU hn hne, one_mul, hA]
      exact huD
    · rw [map_mul, conjHom_scalarU hn hne, one_mul, hA]
      exact hu1
  · push Not at hap
    obtain ⟨k, d', hbk⟩ := exists_zpow_mul_pow_of_forall_pow_ne hp hap b
    have hd' : d' ^ p = b * a ^ (-k) := by
      rw [hbk, mul_comm (a ^ k) (d' ^ p), mul_assoc, _root_.zpow_neg, mul_inv_cancel, mul_one]
    have hd'n : h.norm (d' : K) = 1 := by
      have hdp1 : (d' ^ p) ^ (ℓ ^ f + 1) = 1 := by
        rw [hd', mul_pow, (pow_succ_eq_one_iff_norm h b).mpr hbn, one_mul, ← zpow_natCast,
          ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          (pow_succ_eq_one_iff_norm h a).mpr han, _root_.one_zpow]
      exact norm_eq_one_of_pow_norm hp hp2 hpq ((pow_succ_eq_one_iff_norm h (d' ^ p)).mp hdp1)
    have hd'inv_n : h.norm ((d'⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hd'n
    have hd_pow : d ^ p = 1 :=
      CFSG.LinearAlgebra.scalar_pow_eq_one_of_conj_eq_scalar (F := K) (n := n)
        (X := (B : GL (Fin n) K)) (Y := (A : GL (Fin n) K)) (z := d) (b := b) (k := p)
        hABconj hBp hn0
    refine ⟨scalarU h n d'⁻¹ hd'inv_n * B * A ^ (-k), ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact CFSG.LinearAlgebra.scalar_inv_mul_mul_zpow_neg_pow_eq_one (F := K) (n := n)
        (X := (B : GL (Fin n) K)) (Y := (A : GL (Fin n) K)) (a := a) (b := b) (d := d')
        (m := k) hp hp2 hABconj hd_pow hBp hAp hbk
    · rw [map_mul, map_mul, conjHom_scalarU hn hne, one_mul, hB, map_zpow, hA]
      exact Subgroup.mul_mem _ hvD (Subgroup.zpow_mem _ huD (-k))
    · rw [map_mul, map_mul, conjHom_scalarU hn hne, one_mul, hB, map_zpow, hA]
      intro h1
      apply hvnot
      have h2 : v = u ^ k := by
        have := congrArg (fun x => x * u ^ k) h1
        simpa [mul_assoc, ← _root_.zpow_add] using this
      rw [h2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) k


theorem exists_split_lifts_of_le_primeFormD (hn : 3 ≤ n) (hne : ¬ (n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hDl : D ≤ primeFormD h (idGram K n)) :
    ∃ X Y : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) X ∈ D ∧
      primeFormConjHom h (idGram K n) Y ∈ D ∧
      primeFormConjHom h (idGram K n) X ≠ 1 ∧
      primeFormConjHom h (idGram K n) Y ∉
        Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ∧
      X ^ p = 1 ∧
      (∃ b : Kˣ, h.norm (b : K) = 1 ∧
        (Y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) b) ∧
      ∃ z : Kˣ, z ^ p = 1 ∧
        (Y : GL (Fin n) K) * X * (Y : GL (Fin n) K)⁻¹ =
          GeneralLinearGroup.scalar (Fin n) z * X := by
  classical
  have := h.finite
  have hn0 : 0 < n := by omega
  have hDbot : D ≠ ⊥ := by
    intro h'
    rw [h', Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨⟨u, huD⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDbot
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨A, hA⟩ := hDl huD
  have hu_pow : u ^ p = 1 := hD.2 u huD
  obtain ⟨v, hvD, hvnot⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm53A.exists_mem_not_mem_zpowers
      hp hD hcard huD
  obtain ⟨B, hB⟩ := hDl hvD
  have hpow : ∀ {X : primeFormUnitary h (idGram K n)},
      primeFormConjHom h (idGram K n) X ^ p = 1 →
      ∃ a : Kˣ, h.norm (a : K) = 1 ∧
        (X : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) a := by
    intro X hX
    have h1 : primeFormConjHom h (idGram K n) (X ^ p) = 1 := by rw [map_pow, hX]
    obtain ⟨a, ha, hX'⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
    exact ⟨a, (pow_succ_eq_one_iff_norm h a).mp ha, by simpa using hX'⟩
  obtain ⟨a, han, hAp⟩ := hpow (by rw [hA]; exact hu_pow)
  obtain ⟨b, hbn, hBp⟩ := hpow (by rw [hB]; exact hD.2 v hvD)
  obtain ⟨X, hXp, hXD, hX1⟩ :=
    exists_lift_pow_eq_one_of_plane hn hne hp hp2 hpq hD hA hB huD hvD hu1' hvnot
      han hbn hAp hBp
  obtain ⟨v, hvD, hvnot⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm53A.exists_mem_not_mem_zpowers
      hp hD hcard hXD
  obtain ⟨Y, hY⟩ := hDl hvD
  obtain ⟨bY, hbYn, hYp⟩ := hpow (by rw [hY]; exact hD.2 v hvD)
  have hcommXY : primeFormConjHom h (idGram K n) Y * primeFormConjHom h (idGram K n) X =
      primeFormConjHom h (idGram K n) X * primeFormConjHom h (idGram K n) Y := by
    rw [hY]
    exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hvD⟩ ⟨_, hXD⟩)
  obtain ⟨z, hYX⟩ := exists_scalar_conj_eq_of_commute hn hne hcommXY
  have hzp : z ^ p = 1 :=
    CFSG.LinearAlgebra.scalar_pow_eq_one_of_conj_eq_scalar (F := K) (n := n)
      (X := (X : GL (Fin n) K)) (b := 1) hYX
      (by
        have hXpgl : (X : GL (Fin n) K) ^ p = 1 := by
          rw [← Subgroup.coe_pow, hXp, Subgroup.coe_one]
        rw [hXpgl, map_one]) hn0
  exact ⟨X, Y, hXD, hY ▸ hvD, hX1, hY ▸ hvnot, hXp, ⟨bY, hbYn, hYp⟩, z, hzp, hYX⟩

theorem exists_onPair_of_nonsplit (hn : 3 ≤ n) (hne : ¬ (n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {R S : primeFormUnitary h (idGram K n)} (hRS : R * S = S * R) {c : Kˣ}
    (hR : (R : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ d : Kˣ, d ^ p ≠ c) (hS : S ^ p = 1)
    (hS1 : primeFormConjHom h (idGram K n) S ≠ 1) :
    ∃ (u v : Fin n → K) (μ : K), IsONPair h u v ∧
      ((toLinU h n S : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) u = μ • u ∧
      ((toLinU h n S : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = μ • v := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hpℓ := ne_char_of_dvd_add_one hp hpq h.one_le
  have hn0 : 0 < n := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp h1).symm
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_of_dvd h hp hpq
  have hRSgl : (R : GL (Fin n) K) * (S : GL (Fin n) K) =
      (S : GL (Fin n) K) * (R : GL (Fin n) K) := congrArg Subtype.val hRS
  have hSgl : (S : GL (Fin n) K) ^ p = 1 := congrArg Subtype.val hS
  have hSs : (S : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    simpa using hSgl
  have H0S := primaryData_of_pow_eq_scalar hp hpℓ hSs
  have hSnsc : ∀ d : Kˣ, (S : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) d := by
    intro d hd
    apply hS1
    have hdp := scalar_pow_eq_one_of_eq hn0 hSgl hd
    have hdn : h.norm (d : K) = 1 := by
      change (d : K) * h.bar (d : K) = 1
      rw [mul_comm]
      exact bar_eq_inv_of_pow_eq_one h hpq (by
        rw [← Units.val_pow_eq_pow_val, hdp, Units.val_one])
    exact (primeFormConjHom_eq_one_iff_of_ne hn hne S).mpr
      ⟨d, (pow_succ_eq_one_iff_norm h d).mpr hdn, hd⟩
  obtain ⟨a, ha, a', ha', haa'⟩ :=
    exists_ne_mem_primaryFactors' hn0 hp0 hpK hω hSgl hSnsc
  obtain ⟨ν₀, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp0 hω hSgl ha
  have hirr : Irreducible (X ^ p - C (c : K)) :=
    CFSG.LinearAlgebra.X_pow_sub_C_irreducible_of_prime_of_units hp hc
  have hdim := le_finrank_primaryComponent hn0 hp0 hRSgl hirr hR H0S.squarefree ha
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨v₀, hv₀, hv₀0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot H0S.squarefree ha)
  have hv₀eig := mem_primaryComponent_X_sub_C.mp hv₀
  have hν₀p : ν₀ ^ p = 1 := eigenvalue_pow_eq_one hS hv₀0 hv₀eig
  have hν₀bar : h.bar ν₀ * ν₀ = 1 := bar_eq_inv_of_pow_eq_one h hpq hν₀p
  have hsep := separatingLeft_primaryComponent_selfDual H0S ha (dualPoly_X_sub_C_self hν₀bar)
  obtain ⟨e, he_mem, he_on⟩ := exists_orthonormal_triple hsep (le_trans hp3 hdim)
  have hSe : ∀ i, ((toLinU h n S : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (e i) = ν₀ • e i := fun i =>
    mem_primaryComponent_X_sub_C.mp (he_mem i)
  exact ⟨e 0, e 1, ν₀, he_on.pair (by decide), hSe 0, hSe 1⟩

theorem exists_onPair_of_lt (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    {x : primeFormUnitary h (idGram K n)} (hx : x ^ p = 1) (hpn : p < n) :
    ∃ (u v : Fin n → K) (μ : K), IsONPair h u v ∧
      ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) u = μ • u ∧
      ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v = μ • v := by
  classical
  have := h.finite
  obtain ⟨b, μA, μB, hbo, hAe, hBe⟩ :=
    exists_orthonormal_eigenbasis_pair (h := h) hp hpq (A := x) (B := x) rfl hx hx
  have hcard : (Polynomial.nthRootsFinset p (1 : K)).card ≤ p := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p 1)
  have hmem : ∀ i : Fin n, μA i ∈ Polynomial.nthRootsFinset p (1 : K) := by
    intro i
    rw [Polynomial.mem_nthRootsFinset hp.pos]
    exact eigenvalue_pow_eq_one hx (b.ne_zero i) (hAe i)
  have hlt : Fintype.card {y : K // y ∈ Polynomial.nthRootsFinset p (1 : K)} <
      Fintype.card (Fin n) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin n => (⟨μA i, hmem i⟩ :
      {y : K // y ∈ Polynomial.nthRootsFinset p (1 : K)})) hlt
  have hμij : μA i = μA j := congrArg Subtype.val heq
  refine ⟨b i, b j, μA i, hbo.pair hij, hAe i, ?_⟩
  rw [hμij]
  exact hAe j

theorem exists_good_of_commuting_lifts_unitary (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {X Y : primeFormUnitary h (idGram K n)}
    (hXY : X * Y = Y * X) (hX : X ^ p = 1) {b : Kˣ}
    (hbn : h.norm (b : K) = 1)
    (hY : (Y : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) b)
    (hX1 : primeFormConjHom h (idGram K n) X ≠ 1)
    (hYX : primeFormConjHom h (idGram K n) Y ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) X)) :
    ∃ β ∈ Subgroup.closure {primeFormConjHom h (idGram K n) X,
        primeFormConjHom h (idGram K n) Y}, β ≠ 1 ∧
      ∃ P : Subgroup (primeFormP h (idGram K n)),
        P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  classical
  have := h.finite
  by_cases hb : ∃ v : Kˣ, v ^ p = b
  · obtain ⟨v, rfl⟩ := hb
    have hvn : h.norm (v : K) = 1 := norm_eq_one_of_pow_norm hp hp2 hpq (by simpa using hbn)
    have hv'n : h.norm ((v⁻¹ : Kˣ) : K) = 1 := by
      simpa [Units.val_inv_eq_inv_val] using norm_inv_eq_one hvn
    let Y' : primeFormUnitary h (idGram K n) := scalarU h n v⁻¹ hv'n * Y
    have hY'p : Y' ^ p = 1 := rescale_pow_eq_one hn hne hv'n hY
    have hY'c : primeFormConjHom h (idGram K n) Y' = primeFormConjHom h (idGram K n) Y := by
      rw [show Y' = scalarU h n v⁻¹ hv'n * Y from rfl, map_mul, conjHom_scalarU hn hne, one_mul]
    have hcomm : X * Y' = Y' * X := by
      rw [show Y' = scalarU h n v⁻¹ hv'n * Y from rfl]
      have hs : Commute (scalarU h n v⁻¹ hv'n) X := commute_scalarU hn hne v⁻¹ hv'n X
      have hYc : Commute Y X := (commute_iff_eq Y X).mpr hXY.symm
      exact (hs.mul_left hYc).eq.symm
    have hcomm' : Y' * X = X * Y' := hcomm.symm
    obtain ⟨bs, μA, μB, hbo, hAe, hBe⟩ :=
      exists_orthonormal_eigenbasis_pair (h := h) hp hpq hcomm' hY'p hX
    have hbo0 : ∀ i, bs i ≠ 0 := fun i => bs.ne_zero i
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := fun h' => by simpa [i0, i1] using congrArg Fin.val h'
    have hYX' : primeFormConjHom h (idGram K n) Y' ∉
        Subgroup.zpowers (primeFormConjHom h (idGram K n) X) := by
      rw [hY'c]
      exact hYX
    obtain ⟨M, lam, hMp, hME, hM1, hMe, hMeq⟩ :=
      exists_split_pair_element (h := h) hp hcomm hX hY'p hX1 hYX' hbo0 hBe hAe i0 i1
    have hpair : IsONPair h (bs i0) (bs i1) := hbo.pair h01
    obtain ⟨P, hPle, hPperf, hPdvd⟩ :=
      exists_perfect_fixSubgroup_of_onPair hn hne hq3 hp hp2 hpq hMp hpair
        (hMe i0) (by rw [hMeq]; exact hMe i1)
    have hME' := hME
    rw [hY'c] at hME'
    exact ⟨primeFormConjHom h (idGram K n) M, hME', hM1, P, hPle, hPperf, hPdvd⟩
  · push Not at hb
    obtain ⟨u, v, μ, huv, hu, hv⟩ :=
      exists_onPair_of_nonsplit hn hne hp hp2 hpq hXY.symm hY hb hX hX1
    obtain ⟨P, hPle, hPperf, hPdvd⟩ :=
      exists_perfect_fixSubgroup_of_onPair hn hne hq3 hp hp2 hpq hX huv hu hv
    exact ⟨primeFormConjHom h (idGram K n) X, Subgroup.subset_closure (Set.mem_insert _ _),
      hX1, P, hPle, hPperf, hPdvd⟩


theorem mem_closure_of_mem_innAutDerived_of_commute (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hnp : n = p)
    {X Y : primeFormUnitary h (idGram K n)} (hX : X ^ p = 1) {z : Kˣ}
    (hz : IsPrimitiveRoot (z : K) p)
    (hYX : (Y : GL (Fin n) K) * X * (Y : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) z * X)
    {β : MulAut (primeFormP h (idGram K n))}
    (hβ : β ∈ innAutDerived (primeFormP h (idGram K n)))
    (hβX : β * primeFormConjHom h (idGram K n) X =
      primeFormConjHom h (idGram K n) X * β)
    (hβY : β * primeFormConjHom h (idGram K n) Y =
      primeFormConjHom h (idGram K n) Y * β) :
    β ∈ Subgroup.closure {primeFormConjHom h (idGram K n) X,
      primeFormConjHom h (idGram K n) Y} := by
  classical
  have := h.finite
  obtain ⟨G, hG⟩ :=
    exists_primeFormConjHom_of_mem_innAutDerived h isPrimeFormGram_idGram hn hne hβ
  have hcGX : primeFormConjHom h (idGram K n) G * primeFormConjHom h (idGram K n) X =
      primeFormConjHom h (idGram K n) X * primeFormConjHom h (idGram K n) G := by
    have := hβX
    rwa [hG] at this
  have hcGY : primeFormConjHom h (idGram K n) G * primeFormConjHom h (idGram K n) Y =
      primeFormConjHom h (idGram K n) Y * primeFormConjHom h (idGram K n) G := by
    have := hβY
    rwa [hG] at this
  obtain ⟨α, hGX⟩ := exists_scalar_conj_eq_of_commute hn hne hcGX
  obtain ⟨α', hGY⟩ := exists_scalar_conj_eq_of_commute hn hne hcGY
  have hXgl : (X : GL (Fin n) K) ^ p = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hX
    simpa using this
  obtain ⟨c, i, j, hGdec⟩ :=
    CFSG.LinearAlgebra.exists_eq_scalar_mul_pow_mul_pow (F := K) (n := n) (p := p)
      (X := (X : GL (Fin n) K)) (Y := (Y : GL (Fin n) K)) (z := z)
      hp hz hXgl hYX hnp hGX hGY
  have hmem_scalar : (GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) ∈
      primeFormUnitary h (idGram K n) := by
    have hXimem : (X : GL (Fin n) K) ^ i * (Y : GL (Fin n) K) ^ j ∈
        primeFormUnitary h (idGram K n) :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ X.2 i) (Subgroup.pow_mem _ Y.2 j)
    have h1 : (G : GL (Fin n) K) * ((X : GL (Fin n) K) ^ i * (Y : GL (Fin n) K) ^ j)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) c := by
      rw [hGdec]
      group
    rw [← h1]
    exact Subgroup.mul_mem _ G.2 (Subgroup.inv_mem _ hXimem)
  have hnorm : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) (1 : GL (Fin n) K) hmem_scalar
  have hGsub : G = (⟨GeneralLinearGroup.scalar (Fin n) c, hmem_scalar⟩ :
      primeFormUnitary h (idGram K n)) * X ^ i * Y ^ j := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    exact hGdec
  have hbeta : β = primeFormConjHom h (idGram K n) X ^ i *
      primeFormConjHom h (idGram K n) Y ^ j := by
    simp only [hG, hGsub, map_mul, map_pow,
      primeFormConjHom_scalar_eq_one h (idGram K n) hnorm, one_mul]
  have hmem : primeFormConjHom h (idGram K n) X ^ i *
      primeFormConjHom h (idGram K n) Y ^ j ∈
      Subgroup.closure {primeFormConjHom h (idGram K n) X,
        primeFormConjHom h (idGram K n) Y} := by
    apply Subgroup.mul_mem
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rwa [hbeta]

private theorem right_clause_of_extraspecial (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2)
    (hDle : D ≤ innAutDerived (primeFormP h (idGram K n)))
    {X Y : primeFormUnitary h (idGram K n)}
    (hXD : primeFormConjHom h (idGram K n) X ∈ D)
    (hYD : primeFormConjHom h (idGram K n) Y ∈ D)
    (hX1 : primeFormConjHom h (idGram K n) X ≠ 1)
    (hYXnm : primeFormConjHom h (idGram K n) Y ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) X))
    (hXp : X ^ p = 1) {z : Kˣ} (hzp : z ^ p = 1) (hz1 : z ≠ 1)
    (hYX : (Y : GL (Fin n) K) * X * (Y : GL (Fin n) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) z * X)
    (hnp : n = p) {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    (hpq : p ∣ ℓ ^ f + 1) :
    lpEpsIdx p (.twistedA (n - 1) q) ∧
      innAutDerived (primeFormP h (idGram K n)) ⊓
        Subgroup.centralizer (D : Set (MulAut (primeFormP h (idGram K n)))) = D := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  haveI : Finite (primeFormP h (idGram K n)) := inferInstance
  have hzprim : IsPrimitiveRoot (z : K) p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
    exact orderOf_eq_prime hzp hz1
  have hclD : Subgroup.closure {primeFormConjHom h (idGram K n) X,
      primeFormConjHom h (idGram K n) Y} = D :=
    CFSG.StandardType.ggClosure_pair_eq hp hDcard hXD hYD hX1 (hD.2 _ hXD) hYXnm
  refine ⟨?_, ?_⟩
  · refine ⟨q, Or.inr ⟨?_, ?_⟩⟩
    · rw [hnp]
    · rw [hq]; exact hpq
  · refine le_antisymm ?_ (le_inf hDle ?_)
    · intro β hβ
      have hβX : β * primeFormConjHom h (idGram K n) X =
          primeFormConjHom h (idGram K n) X * β :=
        (Subgroup.mem_centralizer_iff.mp hβ.2 _ hXD).symm
      have hβY : β * primeFormConjHom h (idGram K n) Y =
          primeFormConjHom h (idGram K n) Y * β :=
        (Subgroup.mem_centralizer_iff.mp hβ.2 _ hYD).symm
      have hcl := mem_closure_of_mem_innAutDerived_of_commute hn hne hp hnp hXp hzprim
        hYX hβ.1 hβX hβY
      rwa [hclD] at hcl
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem innGoodAt_primeFormP_of_dvd_gcd {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpg : p ∣ Nat.gcd n (ℓ ^ f + 1)) (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f) :
    InnGoodAt p (.twistedA (n - 1) q) (primeFormP h (idGram K n)) := by
  classical
  have := h.finite
  have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right n (ℓ ^ f + 1))
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n (ℓ ^ f + 1))
  have hq3 : 3 < ℓ ^ f := three_lt_of_dvd_add_one h hp hp2 h32 hpq
  intro D hDel hDcard hDle
  have hDsub : D ≤ primeFormD h (idGram K n) :=
    hDle.trans (innAutDerived_le_primeFormD h isPrimeFormGram_idGram hn hne)
  obtain ⟨X, Y, hXD, hYD, hX1, hYXnm, hXp, ⟨b, hbn, hYp⟩, ⟨z, hzp, hYX⟩⟩ :=
    exists_split_lifts_of_le_primeFormD hn hne hp hp2 hpq hDel hDcard hDsub
  haveI : Finite (primeFormP h (idGram K n)) := inferInstance
  have hclD : Subgroup.closure {primeFormConjHom h (idGram K n) X,
      primeFormConjHom h (idGram K n) Y} = D :=
    CFSG.StandardType.ggClosure_pair_eq hp hDcard hXD hYD hX1 (hDel.2 _ hXD) hYXnm
  by_cases hz1 : z = 1
  · have hXY : X * Y = Y * X := by
      apply Subtype.ext
      have h := hYX
      rw [hz1, map_one] at h
      have h2 := congrArg (fun g : GL (Fin n) K => g * (Y : GL (Fin n) K)) h
      simpa [mul_assoc] using h2.symm
    obtain ⟨β, hβ, hβ1, P, hPle, hPperf, hPdvd⟩ :=
      exists_good_of_commuting_lifts_unitary hn hne hq3 hp hp2 hpq hXY hXp hbn hYp hX1 hYXnm
    exact Or.inl ⟨β, hclD ▸ hβ, hβ1, P, hPle, hPperf, hPdvd⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hzprim : IsPrimitiveRoot (z : K) p := by
      rw [IsPrimitiveRoot.iff_orderOf, orderOf_units]
      exact orderOf_eq_prime hzp hz1
    by_cases hnp : n = p
    · exact Or.inr (right_clause_of_extraspecial hn hne hp hDel hDcard hDle hXD hYD hX1
        hYXnm hXp hzp hz1 hYX hnp hq hpq)
    · have hpn' : p < n :=
        lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpn) (fun h' => hnp h'.symm)
      obtain ⟨u, v, μ, huv, hu, hv⟩ := exists_onPair_of_lt hp hpq hXp hpn'
      obtain ⟨P, hPle, hPperf, hPdvd⟩ :=
        exists_perfect_fixSubgroup_of_onPair hn hne hq3 hp hp2 hpq hXp huv hu hv
      exact Or.inl ⟨primeFormConjHom h (idGram K n) X, hXD, hX1, P, hPle, hPperf, hPdvd⟩

theorem unitaryInnGoodDvd_holds : UnitaryInnGoodDvd := by
  rintro q n p K _ h hn hne hp hp2 hpℓ hgcd h32
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have h32' : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
    rwa [TauCeti.PrimePower.card_def q] at h32
  refine innGoodAt_primeFormP_of_dvd_gcd h hn ?_ hp hp2 ?_ h32' (q := q) hq
  · rwa [TauCeti.PrimePower.card_def q] at hne
  · rwa [TauCeti.PrimePower.card_def q] at hgcd

theorem lieInnGood_unitary : LieInnGood isUnitaryIdx :=
  lieInnGood_unitary_of_dvd unitaryInnGoodDvd_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

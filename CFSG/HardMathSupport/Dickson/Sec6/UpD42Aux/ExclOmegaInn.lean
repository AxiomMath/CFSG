module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Excl
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.ExclOmegaSix
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.ExclOmegaTen

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator

theorem commute_of_fixes_fixedSpace_of_mem_supportedBlock {K : Type} [Field K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x y g : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hyx : y * x = x * y)
    (hyW : ∀ w ∈ fixedSpace x, y w = w) (hg : g ∈ supportedBlock Q x (X - 1)) :
    y * g = g * y := by
  have hc := hx.fixed_others.1
  have hgy : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    (mem_supportedBlock.mp hg).1.2
  have hgW : ∀ w ∈ fixedSpace x, g w ∈ fixedSpace x := by
    intro w hw
    rw [mem_fixedSpace] at hw ⊢
    calc x (g w) = (x * g) w := rfl
      _ = (g * x) w := by rw [Subgroup.mem_centralizer_singleton_iff.mp hgy]
      _ = g (x w) := rfl
      _ = g w := by rw [hw]
  have hgR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g r = r := (mem_supportedBlock.mp hg).2
  have hyR : ∀ r ∈ othersSpace x.toLinearMap (X - 1),
      y r ∈ othersSpace x.toLinearMap (X - 1) :=
    fun r hr => mem_othersSpace_of_apply (Subgroup.mem_centralizer_singleton_iff.mpr hyx) hr
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hc v
  have h1 : y (g (w + r)) = g w + y r := by
    rw [map_add, map_add, hyW (g w) (hgW w hw), hgR r hr]
  have h2 : g (y (w + r)) = g w + y r := by
    rw [map_add, map_add, hyW w hw, hgR (y r) (hyR r hr)]
  exact h1.trans h2.symm

theorem mem_orthDerived_of_cube_eq_one_charTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 4 ≤ n)
    (hdim : Module.finrank K V = 2 * n) {y : V ≃ₗ[K] V}
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hy3 : y ^ 3 = 1) :
    y ∈ orthDerived Q :=
  CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ
    (CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hn hdim) (by norm_num) hyO hy3

theorem mem_centralizer_lift_of_fixes_fixedSpace {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {J : Subgroup S}
    (hJ : J.map e = fixedComponentImage Q x) {y : V ≃ₗ[K] V}
    (hyx : y * x = x * y) (hyW : ∀ w ∈ fixedSpace x, y w = w) (hyΩ : y ∈ orthDerived Q) :
    e.symm (piOrth Q ⟨y, hyΩ⟩) ∈ Subgroup.centralizer (J : Set S) := by
  let s := e.symm (piOrth Q ⟨y, hyΩ⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hej : e j ∈ fixedComponentImage Q x := by
    rw [← hJ]
    exact ⟨j, hj, rfl⟩
  rw [fixedComponentImage, Subgroup.mem_map] at hej
  obtain ⟨w, hw, hwj⟩ := hej
  have hwSD : ((w : orthDerived Q) : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x :=
    Subgroup.mem_subgroupOf.mp hw
  have hcomm : y * (w : V ≃ₗ[K] V) = (w : V ≃ₗ[K] V) * y :=
    commute_of_fixes_fixedSpace_of_mem_supportedBlock hx hyx hyW
      (supportedFixedDerived_le_supportedBlock hwSD)
  refine e.injective ?_
  calc e (j * s) = e j * e s := map_mul e j s
    _ = piOrth Q w * piOrth Q ⟨y, hyΩ⟩ := by
      rw [hwj, MulEquiv.apply_symm_apply]
    _ = piOrth Q (w * ⟨y, hyΩ⟩) := (map_mul _ _ _).symm
    _ = piOrth Q (⟨y, hyΩ⟩ * w) := by
      rw [show w * ⟨y, hyΩ⟩ = ⟨y, hyΩ⟩ * w from Subtype.ext hcomm.symm]
    _ = piOrth Q ⟨y, hyΩ⟩ * piOrth Q w := map_mul _ _ _
    _ = e s * e j := by rw [MulEquiv.apply_symm_apply, ← hwj]
    _ = e (s * j) := (map_mul e s j).symm

theorem mem_centralizer_lift_of_commute {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {b : S} {x y : orthDerived Q}
    (hxeb : piOrth Q x = e b)
    (hyx : (y : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)) :
    e.symm (piOrth Q y) ∈ Subgroup.centralizer ({b} : Set S) := by
  let s := e.symm (piOrth Q y)
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine e.injective ?_
  calc e (s * b) = e s * e b := map_mul e s b
    _ = piOrth Q y * piOrth Q x := by
      rw [MulEquiv.apply_symm_apply, ← hxeb]
    _ = piOrth Q (y * x) := (map_mul _ _ _).symm
    _ = piOrth Q (x * y) := by rw [show y * x = x * y from Subtype.ext hyx]
    _ = piOrth Q x * piOrth Q y := map_mul _ _ _
    _ = e b * e s := by rw [← hxeb, MulEquiv.apply_symm_apply]
    _ = e (b * s) := (map_mul e b s).symm

theorem false_of_omegaTwoBig_six_le {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 6 ≤ n)
    (hdim : Module.finrank K V = 2 * n) {x : orthDerived Q} (hx3 : orderOf x = 3)
    (hfix : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 8)
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {b : S} {J : Subgroup S}
    (hxeb : piOrth Q x = e b) (hJ : J.map e = fixedComponentImage Q (x : V ≃ₗ[K] V))
    (hC : ∀ y ∈ Subgroup.centralizer ({b} : Set S),
      y ∈ Subgroup.centralizer (J : Set S) → y ^ 3 = 1 → y ∈ Subgroup.zpowers b) : False := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hx3V : orderOf (x : V ≃ₗ[K] V) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  have hlin : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [hchar]; norm_num) hQ x hx3
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup x.2
  obtain ⟨y, hyO, hy3, hycomm, hyfix, hynot⟩ :=
    exists_isometry_of_fixedSpace_eight hQ hx3V hxO hfix (by omega)
  have hyΩ : y ∈ orthDerived Q :=
    mem_orthDerived_of_cube_eq_one_charTwo hQ (by omega) hdim hyO hy3
  let s := e.symm (piOrth Q ⟨y, hyΩ⟩)
  have hsb : s ∈ Subgroup.centralizer ({b} : Set S) :=
    mem_centralizer_lift_of_commute (y := ⟨y, hyΩ⟩) e hxeb hycomm
  have hsJ : s ∈ Subgroup.centralizer (J : Set S) :=
    mem_centralizer_lift_of_fixes_fixedSpace hlin e hJ hycomm hyfix hyΩ
  have hs3 : s ^ 3 = 1 := by
    refine e.injective ?_
    rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← map_pow,
      show (⟨y, hyΩ⟩ : orthDerived Q) ^ 3 = 1 from Subtype.ext (by simpa using hy3), map_one]
  have hsnot : s ∉ Subgroup.zpowers b := by
    intro hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hEq : (⟨y, hyΩ⟩ : orthDerived Q) = x ^ k := by
      refine piOrth_injective hQ ?_
      calc piOrth Q ⟨y, hyΩ⟩ = e s := (e.apply_symm_apply _).symm
        _ = e (b ^ k) := by rw [← hk]
        _ = (e b) ^ k := map_zpow e b k
        _ = (piOrth Q x) ^ k := by rw [← hxeb]
        _ = piOrth Q (x ^ k) := (map_zpow (piOrth Q) x k).symm
    exact hynot (Subgroup.mem_zpowers_iff.mpr ⟨k, (congrArg Subtype.val hEq).symm⟩)
  exact hsnot (hC s hsb hsJ hs3)

noncomputable def fixedLayerLift {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q)
    (A : Subgroup S) : Subgroup (orthDerived Q) :=
  (A.map (e : S →* ProjOrthDerived Q)).comap (piOrth Q)

theorem fixedLayerLift_isElemAbelian_and_card {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V]
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {A : Subgroup S}
    (hAel : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4) :
    IsElemAbelian 3 ((fixedLayerLift e A).map (orthDerived Q).subtype) ∧
      Nat.card ((fixedLayerLift e A).map (orthDerived Q).subtype) = 3 ^ 4 := by
  let π : orthDerived Q ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective (piOrth Q) ⟨piOrth_injective hQ, piOrth_surjective⟩
  have hcomap : fixedLayerLift e A = (A.map (e : S →* ProjOrthDerived Q)).map
      (π.symm : ProjOrthDerived Q →* orthDerived Q) := by
    rw [fixedLayerLift]
    exact Subgroup.comap_equiv_eq_map_symm π _
  have hB : IsElemAbelian 3 (A.map (e : S →* ProjOrthDerived Q)) := hAel.map _
  constructor
  · rw [hcomap]
    exact (hB.map (π.symm : ProjOrthDerived Q →* orthDerived Q)).map _
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcomap,
      Subgroup.card_map_of_injective π.symm.injective,
      Subgroup.card_map_of_injective e.injective, hA4]

theorem fixedLayerLift_fixes_orthPerp {K : Type} [Field K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nontrivial V] {p : ℕ} {x : orthDerived Q}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {S : Type} [Group S]
    (e : S ≃* ProjOrthDerived Q) {A J : Subgroup S}
    (hJ : J.map e = fixedComponentImage Q (x : V ≃ₗ[K] V)) (hAJ : A ≤ J)
    {z : orthDerived Q} (hz : z ∈ fixedLayerLift e A) :
    ∀ v ∈ orthPerp Q (fixedSpace (x : V ≃ₗ[K] V)), (z : V ≃ₗ[K] V) v = v := by
  have hzB : piOrth Q z ∈ A.map (e : S →* ProjOrthDerived Q) := hz
  obtain ⟨α, hαA, hα⟩ := Subgroup.mem_map.mp hzB
  have hmem : piOrth Q z ∈ fixedComponentImage Q (x : V ≃ₗ[K] V) := by
    rw [← hα, ← hJ]
    exact ⟨α, hAJ hαA, rfl⟩
  rw [fixedComponentImage, Subgroup.mem_map] at hmem
  obtain ⟨w, hw, hw_eq⟩ := hmem
  have hwz : (w : orthDerived Q) = z := piOrth_injective hQ hw_eq
  have hzSD : (z : V ≃ₗ[K] V) ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) := by
    rw [← hwz]
    exact Subgroup.mem_subgroupOf.mp hw
  intro v hv
  rw [CFSG.RankThree.PartOne.KCOrthogonalD4.orthPerp_fixedSpace hx] at hv
  exact (mem_supportedBlock.mp (supportedFixedDerived_le_supportedBlock hzSD)).2 v hv

theorem false_of_omegaTwoBig_finrank_ten {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 10)
    {x : orthDerived Q} {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {b : S}
    {A : Subgroup S} (hxeb : piOrth Q x = e b)
    (hσ : ∃ σ : V ≃ₗ[K] V, σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      σ ∈ orthDerived Q ∧
      σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∈ (fixedLayerLift e A).map (orthDerived Q).subtype ∧
      σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∉ Subgroup.zpowers (x : V ≃ₗ[K] V))
    (hwc : ∀ y : S, y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ A → y * b * y⁻¹ ∈ Subgroup.zpowers b) :
    False := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨σ, _, hσΩ, hσA, hσnot⟩ := hσ
  let s := e.symm (piOrth Q ⟨σ, hσΩ⟩)
  obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hσA
  obtain ⟨α, hαA, hα⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hz)
  have h1 : e (s * b * s⁻¹) = piOrth Q z := by
    calc e (s * b * s⁻¹) = e s * e b * (e s)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = piOrth Q ⟨σ, hσΩ⟩ * piOrth Q x * (piOrth Q ⟨σ, hσΩ⟩)⁻¹ := by
        rw [MulEquiv.apply_symm_apply, ← hxeb]
      _ = piOrth Q (⟨σ, hσΩ⟩ * x * ⟨σ, hσΩ⟩⁻¹) := by
        rw [← map_inv, ← map_mul, ← map_mul]
      _ = piOrth Q z := by
        rw [show (⟨σ, hσΩ⟩ : orthDerived Q) * x * ⟨σ, hσΩ⟩⁻¹ = z from
          Subtype.ext hzval.symm]
  have hconj : s * b * s⁻¹ = α := by
    refine e.injective ?_
    rw [h1]
    exact hα.symm
  have hconjA : s * b * s⁻¹ ∈ A := by
    rw [hconj]
    exact hαA
  have hnotin : s * b * s⁻¹ ∉ Subgroup.zpowers b := by
    intro hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hEq : (⟨σ, hσΩ⟩ : orthDerived Q) * x * ⟨σ, hσΩ⟩⁻¹ = x ^ k := by
      refine piOrth_injective hQ ?_
      calc
        piOrth Q (⟨σ, hσΩ⟩ * x * ⟨σ, hσΩ⟩⁻¹) = piOrth Q z := by
          rw [show (⟨σ, hσΩ⟩ : orthDerived Q) * x * ⟨σ, hσΩ⟩⁻¹ = z from
            Subtype.ext hzval.symm]
        _ = e (s * b * s⁻¹) := h1.symm
        _ = e (b ^ k) := by rw [← hk]
        _ = (e b) ^ k := map_zpow e b k
        _ = (piOrth Q x) ^ k := by rw [← hxeb]
        _ = piOrth Q (x ^ k) := (map_zpow (piOrth Q) x k).symm
    refine hσnot (Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩)
    exact (congrArg Subtype.val hEq).symm
  exact hnotin (hwc s (Subgroup.mem_sup_right hconjA))

theorem exists_conj_mem_fixedLayerLift {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V = 10) {x : orthDerived Q} (hx3 : orderOf x = 3)
    {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q) {J A : Subgroup S}
    (hJ : J.map e = fixedComponentImage Q (x : V ≃ₗ[K] V)) (hAJ : A ≤ J)
    (hAel : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4)
    (hTen : ∀ (A' : Subgroup (V ≃ₗ[K] V)), A' ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian 3 A' → Nat.card A' = 3 ^ 4 →
      (∀ a ∈ A', ∀ v ∈ orthPerp Q (fixedSpace (x : V ≃ₗ[K] V)), a v = v) →
      ∃ σ : V ≃ₗ[K] V, σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ σ ∈ orthDerived Q ∧
        σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∈ A' ∧
        σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∉ Subgroup.zpowers (x : V ≃ₗ[K] V)) :
    ∃ σ : V ≃ₗ[K] V, σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ σ ∈ orthDerived Q ∧
      σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∈ (fixedLayerLift e A).map (orthDerived Q).subtype ∧
      σ * (x : V ≃ₗ[K] V) * σ⁻¹ ∉ Subgroup.zpowers (x : V ≃ₗ[K] V) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hx3V : orderOf (x : V ≃ₗ[K] V) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  have hxodd : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [hchar]; norm_num) hQ x hx3
  obtain ⟨hA'el, hA'card⟩ := fixedLayerLift_isElemAbelian_and_card hQ e hAel hA4
  have hA'O : (fixedLayerLift e A).map (orthDerived Q).subtype ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro a ha
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp ha
    exact orthDerived_le_orthogonalGroup z.2
  have hA'U : ∀ a ∈ (fixedLayerLift e A).map (orthDerived Q).subtype,
      ∀ v ∈ orthPerp Q (fixedSpace (x : V ≃ₗ[K] V)), a v = v := by
    rintro a ⟨z, hz, rfl⟩ v hv
    exact fixedLayerLift_fixes_orthPerp hQ hxodd e hJ hAJ hz v hv
  exact hTen _ hA'O hA'el hA'card hA'U

theorem upD42ExclInnAt_omegaTwoBig : UpD42ExclInnAt IsOmegaTwoBigIndex := by
  rintro S _ _ _ hcat b J A hb1 hb3 hJ hJiso hAJ hAel hA4 hC hwc
  obtain ⟨t, n, ht, hn5, hG⟩ := statedClassicalModel_of_isOmegaTwoBig hcat
  obtain ⟨K, _, _, V, _, _, _, Q, e, x, hQ, hK, hxeb, hx3, hdim, hfix, hJmap⟩ :=
    exists_fixedLayer_of_isD42_component ht hG hb3 hb1 hJ hJiso
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl (hK.trans (pow_one 2).symm)
  by_cases hn6 : 6 ≤ n
  · exact false_of_omegaTwoBig_six_le hQ hn6 hdim hx3 hfix e hxeb hJmap hC
  · have hn5' : n = 5 := by omega
    subst hn5'
    have hdim10 : Module.finrank K V = 10 := by omega
    refine false_of_omegaTwoBig_finrank_ten hQ hdim10 e hxeb ?_ hwc
    refine exists_conj_mem_fixedLayerLift hQ hdim10 hx3 e hJmap hAJ hAel hA4 ?_
    intro A' hAO hA'el hA'4 hA'U
    exact exists_conj_mem_of_fixedSpace_eight_of_finrank_ten hQ hK hdim10
      (by rw [Subgroup.orderOf_coe, hx3]) (orthDerived_le_orthogonalGroup x.2) hfix hAO hA'el
      hA'4 hA'U

end CFSG.HardMathSupport.Dickson.Sec6

end

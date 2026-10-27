module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcE6ConnDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCentralizer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighGraph
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.LieType.AlgebraicGroups


private theorem rho_eq_smul_all {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {wρ : WeylGroup Tag.E6}
    (hwρ : S.D.n = canonicalRep (coxeterSystem Tag.E6) L wρ)
    (x : Fin Tag.E6.rank → ℤ) : S.ρ x = wρ • x := by
  have hbase : ∀ i : Fin Tag.E6.rank,
      S.ρ (Pi.single i 1) = wρ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) :=
    fun i => S.rho_eq_smul_of_frob hFr hΦ hwρ (isRoot_single Tag.E6 i)
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  have hsum : S.ρ (∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      ∑ i, x i • S.ρ (Pi.single i 1) := by
    change S.rhoHom (∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      ∑ i, x i • S.ρ (Pi.single i 1)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  rw [hsum]
  simp only [hbase]
  conv_rhs => rw [hx]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

theorem langSetup_rootChar_rho_apply {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (x : Fin τ.rank → ℤ) :
    rootChar a (S.ρ x) = rootChar a x ^ S.D.q := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hρx : S.ρ x = ∑ i, x i • S.ρ (Pi.single i 1) := by
    conv_lhs => rw [hx]
    change S.rhoHom (∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      ∑ i, x i • S.ρ (Pi.single i 1)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  conv_lhs => rw [hρx]
  rw [rootChar_sum]
  conv_rhs => rw [hx]
  rw [rootChar_sum, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul,
    S.frob.rootChar_eq a hT (Pi.single i 1) (isRoot_single τ i)]
  rw [← zpow_natCast (rootChar a (Pi.single i 1)) S.D.q, ← zpow_mul]
  rw [rootChar_zsmul]
  rw [← zpow_natCast (rootChar a (Pi.single i 1) ^ (x i : ℤ)) S.D.q, ← zpow_mul, mul_comm]

theorem langSetup_not_three_dvd_q {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) : ¬ 3 ∣ S.D.q := by
  rintro ⟨k, hk⟩
  obtain ⟨p, n, hp, hn, hq⟩ := S.hqpow.1
  have h3dvd : 3 ∣ p ^ n := by
    rw [hq]
    exact ⟨k, hk⟩
  have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
  have hp3 : p = 3 := by
    rcases (Nat.dvd_prime (Nat.prime_iff.2 hp)).1 h3p with h | h
    · omega
    · exact h.symm
  have h3L : ((3 : ℕ) : L) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, CharP.cast_eq_zero L 2, zero_add,
      Nat.cast_one]
  have hcast : ((p ^ n : ℕ) : L) = 0 := by
    rw [hq]
    exact S.hqpow.2
  rw [hp3, Nat.cast_pow, h3L, one_pow] at hcast
  exact one_ne_zero hcast

private theorem q_mod_three {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq3 : ¬ 3 ∣ S.D.q - 1) : S.D.q % 3 = 2 := by
  have hq0 : S.D.q % 3 ≠ 0 := fun h =>
    langSetup_not_three_dvd_q S (Nat.dvd_of_mod_eq_zero h)
  have hq1 : S.D.q % 3 ≠ 1 := by
    intro h
    apply hq3
    refine ⟨S.D.q / 3, ?_⟩
    have hmod := Nat.div_add_mod S.D.q 3
    omega
  have hlt := Nat.mod_lt S.D.q (by norm_num : 0 < 3)
  omega

private theorem pow_eq_inv_of_cube {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) {q : ℕ}
    (hq : q % 3 = 2) : x ^ q = x⁻¹ := by
  rw [pow_eq_pow_mod (n := 3) q hx, hq]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; simpa using hx)

private theorem rootChar_wρ_smul {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) {wρ : WeylGroup Tag.E6}
    (hwρ : S.D.n = canonicalRep (coxeterSystem Tag.E6) L wρ)
    (x : Fin Tag.E6.rank → ℤ) : rootChar a (wρ • x) = rootChar a x ^ S.D.q := by
  rw [← rho_eq_smul_all S hFr hΦ hwρ x]
  exact langSetup_rootChar_rho_apply S hT x

private theorem rootChar_wρ_inv_smul {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {wρ : WeylGroup Tag.E6} {q : ℕ}
    (hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (wρ • x) = rootChar a x ^ q)
    (x : Fin Tag.E6.rank → ℤ) : rootChar a (wρ⁻¹ • x) ^ q = rootChar a x := by
  have h := hχ (wρ⁻¹ • x)
  rw [smul_inv_smul] at h
  exact h.symm

private theorem mem_rootCharStabilizer_conj {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {wρ : WeylGroup Tag.E6} {q : ℕ}
    (hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (wρ • x) = rootChar a x ^ q)
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizerSubgroup a) :
    wρ * w * wρ⁻¹ ∈ rootCharStabilizerSubgroup a := by
  intro x
  rw [mul_smul, mul_smul, hχ, hw, rootChar_wρ_inv_smul hχ x]

private theorem rootChar_e6Shift_conj {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    {wρ : WeylGroup Tag.E6} {q : ℕ}
    (hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (wρ • x) = rootChar a x ^ q)
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizerSubgroup a) :
    rootChar a (e6Shift (wρ * w * wρ⁻¹)) = (rootChar a (e6Shift w)) ^ q := by
  have h0 : (0 : Fin Tag.E6.rank → ℤ) = wρ • e6Shift wρ⁻¹ + e6Shift wρ := by
    rw [← e6Shift_mul wρ wρ⁻¹, mul_inv_cancel, e6Shift_one]
  have h1 : e6Shift (wρ * w * wρ⁻¹) =
      (wρ * w) • e6Shift wρ⁻¹ + (wρ • e6Shift w + e6Shift wρ) := by
    rw [e6Shift_mul (wρ * w) wρ⁻¹, e6Shift_mul wρ w]
  have hprod : rootChar a (e6Shift wρ⁻¹) ^ q * rootChar a (e6Shift wρ) = 1 := by
    have hc := congrArg (rootChar a) h0
    rw [rootChar_zero, rootChar_add, hχ] at hc
    exact hc.symm
  rw [h1, rootChar_add, rootChar_add, mul_smul, hχ, hw, hχ]
  calc rootChar a (e6Shift wρ⁻¹) ^ q * (rootChar a (e6Shift w) ^ q * rootChar a (e6Shift wρ))
      = (rootChar a (e6Shift wρ⁻¹) ^ q * rootChar a (e6Shift wρ)) *
          rootChar a (e6Shift w) ^ q := by ac_rfl
    _ = 1 * rootChar a (e6Shift w) ^ q := by rw [hprod]
    _ = rootChar a (e6Shift w) ^ q := one_mul _

theorem rootChar_e6Shift_of_mem_kernelReflectionGroup {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelReflectionGroup a) : rootChar a (e6Shift u) = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, hα, rfl⟩ := hx
    have hxW : (w * simple Tag.E6 i * w⁻¹) ∈ rootCharStabilizerSubgroup a :=
      kernelReflectionGroup_le a (Subgroup.subset_closure ⟨w, i, hα, rfl⟩)
    have hx2 : (w * simple Tag.E6 i * w⁻¹) * (w * simple Tag.E6 i * w⁻¹) = 1 := by
      have hs : simple Tag.E6 i * simple Tag.E6 i = 1 :=
        (coxeterSystem Tag.E6).simple_mul_simple_self i
      calc (w * simple Tag.E6 i * w⁻¹) * (w * simple Tag.E6 i * w⁻¹)
          = w * (simple Tag.E6 i * simple Tag.E6 i) * w⁻¹ := by group
        _ = 1 := by rw [hs, mul_one, mul_inv_cancel]
    have h := e6Shift_mul (w * simple Tag.E6 i * w⁻¹) (w * simple Tag.E6 i * w⁻¹)
    rw [hx2, e6Shift_one] at h
    have hsq : rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹)) ^ 2 = 1 := by
      have hc := congrArg (rootChar a) h
      rw [rootChar_zero, rootChar_add, hxW] at hc
      rw [pow_two]
      exact hc.symm
    have h3 : rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹)) ^ 3 = 1 :=
      e6ShiftChar_pow_three a ⟨w * simple Tag.E6 i * w⁻¹, hxW⟩
    calc rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹))
        = rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹)) *
            rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹)) ^ 2 := by rw [hsq, mul_one]
      _ = rootChar a (e6Shift (w * simple Tag.E6 i * w⁻¹)) ^ 3 := by
          rw [← pow_succ']
      _ = 1 := h3
  | one => rw [e6Shift_one, rootChar_zero]
  | mul x y hx hy ihx ihy =>
    have hxW : x ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hx
    rw [e6Shift_mul, rootChar_add, hxW, ihx, ihy, one_mul]
  | inv x hx ihx =>
    have hxW : x ∈ rootCharStabilizerSubgroup a := kernelReflectionGroup_le a hx
    have h := e6Shift_mul x x⁻¹
    rw [mul_inv_cancel, e6Shift_one] at h
    have hc := congrArg (rootChar a) h
    rw [rootChar_zero, rootChar_add, hxW, ihx, mul_one] at hc
    exact hc.symm

private theorem map_step_torusGroup_le {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) :
    (torusGroup Tag.E6 L).map S.D.step ≤ torusGroup Tag.E6 L := by
  rw [Subgroup.map_le_iff_le_comap]
  intro t ht
  change S.D.step t ∈ torusGroup Tag.E6 L
  obtain ⟨wρ, hwρ⟩ := S.D.n_weyl
  have hnN : S.D.n ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) := by
    rw [hwρ]
    exact canonicalRep_mem_normalizer (R := L) wρ
  have hFt : Units.map (entrywiseHom Fr) t ∈ torusGroup Tag.E6 L := by
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hstep : S.D.step t = S.D.n * Units.map (entrywiseHom Fr) t * S.D.n⁻¹ := by
    change S.D.n * S.D.Φ t * S.D.n⁻¹ = S.D.n * Units.map (entrywiseHom Fr) t * S.D.n⁻¹
    rw [hΦ]
  rw [hstep]
  exact (Subgroup.mem_normalizer_iff.1 hnN _).1 hFt

private theorem map_step_rootSpan_le {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) :
    (rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map S.D.step ≤
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  simp only [rootSpan, Subgroup.map_iSup]
  refine iSup_le fun α => iSup_le fun hα => ?_
  rw [S.frob.map_rootSubgroup α hα.1]
  refine le_iSup₂_of_le (S.ρ α) ?_ le_rfl
  refine ⟨(S.frob.isRoot_iff α).2 hα.1, ?_⟩
  show rootChar a (S.ρ α) = 1
  rw [langSetup_rootChar_rho_apply S hT α]
  have h1 : rootChar a α = 1 := hα.2
  rw [h1, one_pow]

private theorem map_step_toralRootGroup_le {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) :
    (toralRootGroup Tag.E6 L a).map S.D.step ≤ toralRootGroup Tag.E6 L a := by
  rw [toralRootGroup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · exact (map_step_torusGroup_le S hFr hΦ).trans le_sup_left
  · exact (map_step_rootSpan_le S hT).trans le_sup_right

private theorem step_canonicalRep {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {wρ : WeylGroup Tag.E6}
    (hwρ : S.D.n = canonicalRep (coxeterSystem Tag.E6) L wρ) (w : WeylGroup Tag.E6) :
    ∃ t ∈ torusGroup Tag.E6 L,
      S.D.step (canonicalRep (coxeterSystem Tag.E6) L w) =
        t * canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) := by
  set nρ := canonicalRep (coxeterSystem Tag.E6) L wρ with hnρ
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nv := canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) with hnv
  obtain ⟨k, hk, hkconj⟩ := canonicalRep_inv_mul_conj_mem (L := L) wρ w
  have hnN : nρ ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer (R := L) wρ
  have hnt : nρ * k⁻¹ * nρ⁻¹ ∈ torusGroup Tag.E6 L :=
    (Subgroup.mem_normalizer_iff.1 hnN _).1 (inv_mem hk)
  have hnv_eq : nv = nρ * k * nw * nρ⁻¹ := by
    have h := congrArg (fun z => nρ * z * nρ⁻¹) hkconj
    have h' : nρ * k * nw * nρ⁻¹ = nv := by
      simpa [hnρ, hnw, hnv, mul_assoc] using h.symm
    exact h'.symm
  have hstep : S.D.step nw = nρ * nw * nρ⁻¹ := by
    change S.D.n * S.D.Φ nw * S.D.n⁻¹ = nρ * nw * nρ⁻¹
    rw [hΦ, hwρ, E8Lift.units_map_entrywiseHom_canonicalRep]
  refine ⟨nρ * k⁻¹ * nρ⁻¹, hnt, ?_⟩
  rw [hstep, hnv_eq]
  group

theorem e6CentralizerConnOdd_untw_holds :
    E6CentralizerConnOdd := by
  intro L _ _ _ p₀ S huntw hq3 a hT hap y hyC hyF
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := huntw
  obtain ⟨wρ, hwρ⟩ := S.D.n_weyl
  have hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (wρ • x) = rootChar a x ^ S.D.q :=
    fun x => rootChar_wρ_smul S hFr hΦ hT hwρ x
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L a).1 y hyC
  have hhM : h ∈ toralRootGroup Tag.E6 L a := Subgroup.mem_sup_left hh
  have huM : u ∈ toralRootGroup Tag.E6 L a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvM : v ∈ toralRootGroup Tag.E6 L a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  have hnwX : canonicalRep (coxeterSystem Tag.E6) L w ∈ toralCentralizer Tag.E6 L a :=
    canonicalRep_mem_toralCentralizer hw
  have hvW : wρ * w * wρ⁻¹ ∈ rootCharStabilizerSubgroup a :=
    mem_rootCharStabilizer_conj hχ hw
  have hnvX : canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) ∈
      toralCentralizer Tag.E6 L a := canonicalRep_mem_toralCentralizer hvW
  have hFM : ∀ m ∈ toralRootGroup Tag.E6 L a, S.D.step m ∈ toralRootGroup Tag.E6 L a :=
    fun m hm => map_step_toralRootGroup_le S hFr hΦ hT ⟨m, hm, rfl⟩
  obtain ⟨t, htT, htstep⟩ := step_canonicalRep S hFr hΦ hwρ w
  have htM : t ∈ toralRootGroup Tag.E6 L a := Subgroup.mem_sup_left htT
  have h1 : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
      (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v) ∈ toralRootGroup Tag.E6 L a := by
    have hm1 : h * u ∈ toralRootGroup Tag.E6 L a := mul_mem hhM huM
    have hN := toralCentralizer_le_normalizer a hnwX
    have hconj := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) (h * u)).1 hm1
    rw [show (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v)
        = ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * (h * u) *
            canonicalRep (coxeterSystem Tag.E6) L w) * v from by group]
    exact mul_mem hconj hvM
  have hstepy : S.D.step (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v) =
      (S.D.step h * S.D.step u * t) *
        canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) * S.D.step v := by
    simp only [map_mul, htstep]
    group
  have h2 : (canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹))⁻¹ *
      (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v) ∈ toralRootGroup Tag.E6 L a := by
    rw [← hyF, hstepy]
    have hm3 : S.D.step h * S.D.step u * t ∈ toralRootGroup Tag.E6 L a :=
      mul_mem (mul_mem (hFM h hhM) (hFM u huM)) htM
    have hm4 : S.D.step v ∈ toralRootGroup Tag.E6 L a := hFM v hvM
    have hN := toralCentralizer_le_normalizer a hnvX
    have hconj := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) _).1 hm3
    rw [show (canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹))⁻¹ *
          ((S.D.step h * S.D.step u * t) *
            canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) * S.D.step v)
        = ((canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹))⁻¹ *
            (S.D.step h * S.D.step u * t) *
            canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹)) * S.D.step v from by group]
    exact mul_mem hconj hm4
  have h3 : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
      canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) ∈ toralRootGroup Tag.E6 L a := by
    have hprod := mul_mem h1 (inv_mem h2)
    have e : ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v)) *
        ((canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹))⁻¹ *
          (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v))⁻¹ =
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹) := by group
    rwa [e] at hprod
  have h4 : canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * (wρ * w * wρ⁻¹)) ∈
      toralRootGroup Tag.E6 L a := by
    obtain ⟨k, hk, hkeq⟩ := canonicalRep_mul_mem (R := L) w (w⁻¹ * (wρ * w * wρ⁻¹))
    rw [show w * (w⁻¹ * (wρ * w * wρ⁻¹)) = wρ * w * wρ⁻¹ from by group] at hkeq
    have hkM : k ∈ toralRootGroup Tag.E6 L a := Subgroup.mem_sup_left hk
    have hN := toralCentralizer_le_normalizer a hnwX
    have hconjk : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
        canonicalRep (coxeterSystem Tag.E6) L w ∈ toralRootGroup Tag.E6 L a :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hN) k).1 hkM
    have hnv_eq : canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * (wρ * w * wρ⁻¹)) =
        ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
          canonicalRep (coxeterSystem Tag.E6) L w) *
          ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
            canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹)) := by
      have h := congrArg (fun z => (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * z) hkeq
      have h1 : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L w *
            canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * (wρ * w * wρ⁻¹))) =
          canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * (wρ * w * wρ⁻¹)) := by group
      rw [h1] at h
      calc canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * (wρ * w * wρ⁻¹))
          = (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * (k *
              canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹)) := h
        _ = ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
              canonicalRep (coxeterSystem Tag.E6) L w) *
              ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
                canonicalRep (coxeterSystem Tag.E6) L (wρ * w * wρ⁻¹)) := by group
    rw [hnv_eq]
    exact mul_mem hconjk h3
  have hwSigma : w⁻¹ * (wρ * w * wρ⁻¹) ∈ kernelReflectionGroup a :=
    mem_kernelReflectionGroup_of_canonicalRep_mem_gen h4
  set c := rootChar a (e6Shift w) with hc
  have hv_c : rootChar a (e6Shift (wρ * w * wρ⁻¹)) = c⁻¹ := by
    rw [rootChar_e6Shift_conj hχ hw]
    exact pow_eq_inv_of_cube
      (e6ShiftChar_pow_three a ⟨w, hw⟩) (q_mod_three S hq3)
  have hwinv_c : rootChar a (e6Shift w⁻¹) = c⁻¹ := by
    have h := e6Shift_mul w w⁻¹
    rw [mul_inv_cancel, e6Shift_one] at h
    have hc' := congrArg (rootChar a) h
    rw [rootChar_zero, rootChar_add, hw (e6Shift w⁻¹)] at hc'
    exact eq_inv_of_mul_eq_one_left hc'.symm
  have hw_invW : w⁻¹ ∈ rootCharStabilizerSubgroup a := (rootCharStabilizerSubgroup a).inv_mem hw
  have hone : rootChar a (e6Shift (w⁻¹ * (wρ * w * wρ⁻¹))) = 1 :=
    rootChar_e6Shift_of_mem_kernelReflectionGroup hwSigma
  rw [e6Shift_mul, rootChar_add, hw_invW, hv_c, hwinv_c] at hone
  have hc2 : c ^ 2 = 1 := by
    have h := congrArg Inv.inv hone
    simp only [inv_one, mul_inv_rev, inv_inv, ← pow_two] at h
    exact h
  have hc3 : c ^ 3 = 1 := by
    rw [hc]
    exact e6ShiftChar_pow_three a ⟨w, hw⟩
  have hc1 : c = 1 := by
    calc c = c * c ^ 2 := by rw [hc2, mul_one]
      _ = c ^ 3 := by rw [← pow_succ']
      _ = 1 := hc3
  have hwSigma' : w ∈ kernelReflectionGroup a := by
    refine mem_kernelReflectionGroup_of_e6Shift a hap hw ?_
    simpa [hc] using hc1
  obtain ⟨-, hMnormal, -⟩ := Chevalley_toral_centralizer_root_generated_quotient Tag.E6 L a
  haveI : ((toralRootGroup Tag.E6 L a).subgroupOf (toralCentralizer Tag.E6 L a)).Normal := hMnormal
  have hnwM : canonicalRep (coxeterSystem Tag.E6) L w ∈ toralRootGroup Tag.E6 L a := by
    have hker := kernelReflectionGroup_le_ker (K := L) a
    have hmem : (⟨w, hw⟩ : rootCharStabilizerSubgroup a) ∈
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) :=
      Subgroup.mem_subgroupOf.2 hwSigma'
    have hφ : weylToralQuotientHom L a ⟨w, hw⟩ = 1 := MonoidHom.mem_ker.1 (hker hmem)
    have hmem' : (⟨canonicalRep (coxeterSystem Tag.E6) L w, hnwX⟩ :
        toralCentralizer Tag.E6 L a) ∈
        (toralRootGroup Tag.E6 L a).subgroupOf (toralCentralizer Tag.E6 L a) :=
      (QuotientGroup.eq_one_iff _).1 hφ
    exact Subgroup.mem_subgroupOf.1 hmem'
  exact mul_mem (mul_mem (mul_mem hhM huM) hnwM) hvM

theorem e6CentralizerConnOddExcKernels_holds :
    E6CentralizerConnOddExcKernels := by
  intro L hL hA hC p₀ S huntw hq3 a hT hap hkern y hyC hyF
  exact e6CentralizerConnOdd_untw_holds (L := L) (p₀ := p₀) S huntw hq3 a hT hap y hyC hyF

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcE6Kern
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.GraphAux
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.GraphAux
  CFSG.LieType.AlgebraicGroups


private abbrev e6TwPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

private def twConj (wρ δ : WeylGroup Tag.E6) : WeylGroup Tag.E6 := wρ * δ * wρ⁻¹

private theorem rho_root_eq {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) {W : WeylGroup Tag.E6}
    (hW : S.D.n = canonicalRep (coxeterSystem Tag.E6) L W)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    S.ρ γ = W • permLattice e6TwPerm γ := by
  obtain ⟨D, ρ, frob, E, hp, hq5, hqpow, hpq, finite, E_le, E_exp, E_all⟩ := S
  obtain ⟨Φ, q, n, g0, steinberg, n_weyl, g0_mem, lang⟩ := D
  subst hΦ
  subst hW
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => by
    subst h
    have h0 := hFr 0
    rw [pow_zero, map_zero] at h0
    exact zero_ne_one h0
  exact frobRootMap_ofTwist_apply (t := TwistTag.E6) hq hFr g0_mem lang frob hγ


private theorem rho_eq_smul_all_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) {W : WeylGroup Tag.E6}
    (hW : S.D.n = canonicalRep (coxeterSystem Tag.E6) L W)
    (x : Fin Tag.E6.rank → ℤ) : S.ρ x = W • permLattice e6TwPerm x := by
  have hbase : ∀ i : Fin Tag.E6.rank,
      S.ρ (Pi.single i 1) = W • permLattice e6TwPerm (Pi.single i 1) :=
    fun i => rho_root_eq S hFr hΦ hW (isRoot_single Tag.E6 i)
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
  change ∑ i, x i • (W • permLattice e6TwPerm (Pi.single i 1)) =
    W • (permLatticeHom e6TwPerm (∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, smul_comm]
  rfl

private theorem q_mod_three_tw {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq3 : ¬ 3 ∣ S.D.q + 1) : S.D.q % 3 = 1 := by
  have hq0 : S.D.q % 3 ≠ 0 := fun h =>
    langSetup_not_three_dvd_q S (Nat.dvd_of_mod_eq_zero h)
  have hq2 : S.D.q % 3 ≠ 2 := by
    intro h
    apply hq3
    refine ⟨S.D.q / 3 + 1, ?_⟩
    have hmod := Nat.div_add_mod S.D.q 3
    omega
  have hlt := Nat.mod_lt S.D.q (by norm_num : 0 < 3)
  omega

private theorem rootChar_rho_eq_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ha : ∀ i, a i ^ 3 = 1)
    (hq : S.D.q % 3 = 1) (x : Fin Tag.E6.rank → ℤ) :
    rootChar a (S.ρ x) = rootChar a x := by
  rw [langSetup_rootChar_rho_apply S hT x]
  rw [pow_eq_pow_mod (n := 3) S.D.q (rootChar_pow_three ha x), hq, pow_one]



private theorem rootChar_e6Shift_eq_one_of_twisted {L : Type} [Field L]
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1)
    {σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ)}
    (l : Fin Tag.E6.rank → ℤ) (hσΩ : σ e6Omega3 + e6Omega3 = (3 : ℤ) • l)
    {w u : WeylGroup Tag.E6} (hw : ∀ v, rootChar a (w • v) = rootChar a v)
    (hu : u ∈ kernelReflectionGroup a)
    (hσw : ∀ v, σ (w • v) = w • (u • σ v))
    (hχσ : ∀ v, rootChar a (σ v) = rootChar a v) :
    rootChar a (e6Shift w) = 1 := by
  have hσΩ' : σ e6Omega3 = (3 : ℤ) • l - e6Omega3 := eq_sub_of_add_eq hσΩ
  have huΩ : u • e6Omega3 = (3 : ℤ) • e6Shift u + e6Omega3 := by
    rw [three_smul_e6Shift u]
    abel
  have h3 : (3 : ℤ) • (σ (e6Shift w) + e6Shift w) =
      (3 : ℤ) • (w • (u • l) - l - w • (e6Shift u)) := by
    have e1 : (3 : ℤ) • (σ (e6Shift w) + e6Shift w) =
        w • (u • σ e6Omega3) - σ e6Omega3 + (w • e6Omega3 - e6Omega3) := by
      rw [smul_add, ← map_zsmul, three_smul_e6Shift, map_sub, hσw]
    rw [e1, hσΩ']
    simp only [smul_sub, smul_add, smul_comm u (3 : ℤ) l, smul_comm w (3 : ℤ), huΩ]
    abel
  have h1 : σ (e6Shift w) + e6Shift w = w • (u • l) - l - w • (e6Shift u) :=
    smul_right_injective _ (by norm_num : (3 : ℤ) ≠ 0) h3
  have hsq : rootChar a (e6Shift w) * rootChar a (e6Shift w) = 1 := by
    have hul : rootChar a (u • l) = rootChar a l := (kernelReflectionGroup_le a hu) l
    have e := congrArg (rootChar a) h1
    rw [rootChar_add, hχσ (e6Shift w), rootChar_sub, rootChar_sub,
      hw (u • l), hw (e6Shift u),
      rootChar_e6Shift_of_mem_kernelReflectionGroup hu, hul] at e
    simpa using e
  calc rootChar a (e6Shift w) = rootChar a (e6Shift w) * 1 := by rw [mul_one]
    _ = rootChar a (e6Shift w) * (rootChar a (e6Shift w) * rootChar a (e6Shift w)) := by
        rw [hsq, mul_one]
    _ = rootChar a (e6Shift w) ^ 3 := by rw [pow_three]
    _ = 1 := rootChar_pow_three ha _


private theorem map_step_torusGroup_le_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) :
    (torusGroup Tag.E6 L).map S.D.step ≤ torusGroup Tag.E6 L := by
  obtain ⟨D, ρ, frob, E, hp, hq5, hqpow, hpq, finite, E_le, E_exp, E_all⟩ := S
  obtain ⟨Φ, q, n, g0, steinberg, n_weyl, g0_mem, lang⟩ := D
  subst hΦ
  rw [Subgroup.map_le_iff_le_comap]
  intro t ht
  let x : ModGL Tag.E6 L := twistHom TwistTag.E6 L Fr t
  change n * x * n⁻¹ ∈ torusGroup Tag.E6 L
  obtain ⟨wρ, hwρ⟩ := n_weyl
  have hnN : n ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) := by
    rw [hwρ]
    exact canonicalRep_mem_normalizer (R := L) wρ
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => by
    subst h
    have h0 := hFr 0
    rw [pow_zero, map_zero] at h0
    exact zero_ne_one h0
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨x, by rw [hFr, hx]⟩
  have hFt : x ∈ torusGroup Tag.E6 L := by
    change twistHom TwistTag.E6 L Fr t ∈ torusGroup Tag.E6 L
    exact twistHom_mem_torusGroup' (t := TwistTag.E6) (K := L) (σ := Fr) hsurj ht
  exact (Subgroup.mem_normalizer_iff.1 hnN x).1 hFt

private theorem map_step_rootSpan_le_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
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

private theorem map_step_toralRootGroup_le_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) :
    (toralRootGroup Tag.E6 L a).map S.D.step ≤ toralRootGroup Tag.E6 L a := by
  rw [toralRootGroup, Subgroup.map_sup]
  exact sup_le ((map_step_torusGroup_le_tw S hFr hΦ).trans le_sup_left)
    ((map_step_rootSpan_le_tw S hT).trans le_sup_right)

private theorem step_canonicalRep_tw {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr) {wρ : WeylGroup Tag.E6}
    (hwρ : S.D.n = canonicalRep (coxeterSystem Tag.E6) L wρ) (w : WeylGroup Tag.E6) :
    ∃ t ∈ torusGroup Tag.E6 L,
      S.D.step (canonicalRep (coxeterSystem Tag.E6) L w) =
        t * canonicalRep (coxeterSystem Tag.E6) L (twConj wρ (weylTwist TwistTag.E6 w)) := by
  obtain ⟨D, ρ, frob, E, hp, hq5, hqpow, hpq, finite, E_le, E_exp, E_all⟩ := S
  obtain ⟨Φ, q, n, g0, steinberg, n_weyl, g0_mem, lang⟩ := D
  subst hΦ
  let δ : WeylGroup Tag.E6 := weylTwist TwistTag.E6 w
  let nρ : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L wρ
  let nw : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L w
  let nδ : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L δ
  let nv : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L (twConj wρ δ)
  obtain ⟨k, hk, hkconj⟩ := canonicalRep_inv_mul_conj_mem (L := L) wρ δ
  have hnN : nρ ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) :=
    canonicalRep_mem_normalizer (R := L) wρ
  have hnt : nρ * k⁻¹ * nρ⁻¹ ∈ torusGroup Tag.E6 L :=
    (Subgroup.mem_normalizer_iff.1 hnN _).1 (inv_mem hk)
  have hwρ' : n = nρ := hwρ
  have hnv_eq : nv = nρ * k * nδ * nρ⁻¹ := by
    have h := congrArg (fun z => nρ * z * nρ⁻¹) hkconj
    have h' : nρ * k * nδ * nρ⁻¹ = nv := by
      simpa [nρ, nδ, nv, δ, twConj, mul_assoc] using h.symm
    exact h'.symm
  have htw : (twistHom TwistTag.E6 L Fr nw : ModGL Tag.E6 L) = nδ :=
    twistHom_canonicalRep (t := TwistTag.E6) (K := L) (σ := Fr) w
  have hstep : (MulAut.conj n).toMonoidHom (twistHom TwistTag.E6 L Fr nw) =
      nρ * nδ * nρ⁻¹ := by
    rw [hwρ', htw]
    rfl
  refine ⟨nρ * k⁻¹ * nρ⁻¹, hnt, ?_⟩
  change (MulAut.conj n).toMonoidHom (twistHom TwistTag.E6 L Fr nw) =
    (nρ * k⁻¹ * nρ⁻¹) * nv
  rw [hstep, hnv_eq]
  group


theorem twE6CentralizerConnOdd_holds :
    TwE6CentralizerConnOdd := by
  intro L _ _ _ p₀ S huntw hq3 a hT hap y hyC hyF
  classical
  obtain ⟨Fr, hFr, hΦ⟩ := huntw
  obtain ⟨wρ, hwρ⟩ := S.D.n_weyl
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors Tag.E6 L a).1 y hyC
  let δ : WeylGroup Tag.E6 := weylTwist TwistTag.E6 w
  let vW : WeylGroup Tag.E6 := twConj wρ δ
  have hhM : h ∈ toralRootGroup Tag.E6 L a := Subgroup.mem_sup_left hh
  have huM : u ∈ toralRootGroup Tag.E6 L a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvM : v ∈ toralRootGroup Tag.E6 L a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  have hnwX : canonicalRep (coxeterSystem Tag.E6) L w ∈ toralCentralizer Tag.E6 L a :=
    canonicalRep_mem_toralCentralizer hw
  have hχ : ∀ x : Fin Tag.E6.rank → ℤ, rootChar a (S.ρ x) = rootChar a x :=
    fun x => rootChar_rho_eq_tw S hT hap (q_mod_three_tw S hq3) x
  have hσw0 : ∀ y, S.ρ (w • y) = vW • S.ρ y := by
    intro y
    rw [rho_eq_smul_all_tw S hFr hΦ hwρ (w • y),
      rho_eq_smul_all_tw S hFr hΦ hwρ y]
    rw [show vW = wρ * δ * wρ⁻¹ from rfl, mul_smul, mul_smul, inv_smul_smul]
    congr 1
    rw [show δ • permLattice e6TwPerm y =
        permLattice e6TwPerm (w • y) by
        have h := weylTwist_smul (t := TwistTag.E6) w
          (permLattice e6TwPerm y : Fin TwistTag.E6.tag.rank → ℤ)
        have h2 : permLattice (Equiv.symm TwistTag.E6.perm)
            (permLattice e6TwPerm y : Fin TwistTag.E6.tag.rank → ℤ) = y :=
          CFSG.LieType.Chevalley.permLattice_symm_permLattice TwistTag.E6.perm y
        rw [h2] at h
        exact h]
  have hvW : vW ∈ rootCharStabilizerSubgroup a := by
    intro z
    have h1 : vW • z = S.ρ (w • S.ρ⁻¹ z) := by
      have h := hσw0 (S.ρ⁻¹ z)
      simpa using h.symm
    have h2 : rootChar a (S.ρ⁻¹ z) = rootChar a z := by
      have h := hχ (S.ρ⁻¹ z)
      simpa using h.symm
    rw [h1, hχ (w • S.ρ⁻¹ z), hw (S.ρ⁻¹ z), h2]
  have hnvX : canonicalRep (coxeterSystem Tag.E6) L vW ∈
      toralCentralizer Tag.E6 L a := canonicalRep_mem_toralCentralizer hvW
  have hFM : ∀ m ∈ toralRootGroup Tag.E6 L a, S.D.step m ∈ toralRootGroup Tag.E6 L a :=
    fun m hm => map_step_toralRootGroup_le_tw S hFr hΦ hT ⟨m, hm, rfl⟩
  obtain ⟨t, htT, htstep⟩ := step_canonicalRep_tw S hFr hΦ hwρ w
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
        canonicalRep (coxeterSystem Tag.E6) L vW * S.D.step v := by
    rw [map_mul, map_mul, map_mul, htstep]
    rfl
  have h2 : (canonicalRep (coxeterSystem Tag.E6) L vW)⁻¹ *
      (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v) ∈ toralRootGroup Tag.E6 L a := by
    rw [← hyF, hstepy]
    have hm3 : S.D.step h * S.D.step u * t ∈ toralRootGroup Tag.E6 L a :=
      mul_mem (mul_mem (hFM h hhM) (hFM u huM)) htM
    have hm4 : S.D.step v ∈ toralRootGroup Tag.E6 L a := hFM v hvM
    have hN := toralCentralizer_le_normalizer a hnvX
    have hconj := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) _).1 hm3
    rw [show (canonicalRep (coxeterSystem Tag.E6) L vW)⁻¹ *
          ((S.D.step h * S.D.step u * t) *
            canonicalRep (coxeterSystem Tag.E6) L vW * S.D.step v)
        = ((canonicalRep (coxeterSystem Tag.E6) L vW)⁻¹ *
            (S.D.step h * S.D.step u * t) *
            canonicalRep (coxeterSystem Tag.E6) L vW) * S.D.step v from by group]
    exact mul_mem hconj hm4
  have h3 : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
      canonicalRep (coxeterSystem Tag.E6) L vW ∈ toralRootGroup Tag.E6 L a := by
    have hprod := mul_mem h1 (inv_mem h2)
    have e : ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v)) *
        ((canonicalRep (coxeterSystem Tag.E6) L vW)⁻¹ *
          (h * u * canonicalRep (coxeterSystem Tag.E6) L w * v))⁻¹ =
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          canonicalRep (coxeterSystem Tag.E6) L vW := by group
    rwa [e] at hprod
  have h4 : canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * vW) ∈
      toralRootGroup Tag.E6 L a := by
    obtain ⟨k, hk, hkeq⟩ := canonicalRep_mul_mem (R := L) w (w⁻¹ * vW)
    rw [show w * (w⁻¹ * vW) = vW from by group] at hkeq
    have hkM : k ∈ toralRootGroup Tag.E6 L a := Subgroup.mem_sup_left hk
    have hN := toralCentralizer_le_normalizer a hnwX
    have hconjk : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
        canonicalRep (coxeterSystem Tag.E6) L w ∈ toralRootGroup Tag.E6 L a :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem hN) k).1 hkM
    have hnv_eq : canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * vW) =
        ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
          canonicalRep (coxeterSystem Tag.E6) L w) *
          ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
            canonicalRep (coxeterSystem Tag.E6) L vW) := by
      have h := congrArg (fun z => (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * z) hkeq
      have h1 : (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          (canonicalRep (coxeterSystem Tag.E6) L w *
            canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * vW)) =
          canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * vW) := by group
      rw [h1] at h
      calc canonicalRep (coxeterSystem Tag.E6) L (w⁻¹ * vW)
          = (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * (k *
              canonicalRep (coxeterSystem Tag.E6) L vW) := h
        _ = ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * k *
              canonicalRep (coxeterSystem Tag.E6) L w) *
              ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
                canonicalRep (coxeterSystem Tag.E6) L vW) := by group
    rw [hnv_eq]
    exact mul_mem hconjk h3
  have huSigma : w⁻¹ * vW ∈ kernelReflectionGroup a :=
    mem_kernelReflectionGroup_of_canonicalRep_mem_gen h4
  have hσw : ∀ x, S.ρ (w • x) = w • ((w⁻¹ * vW) • S.ρ x) := by
    intro x
    rw [hσw0 x, mul_smul, ← mul_smul, mul_inv_cancel, one_smul]
  have hσΩ : S.ρ e6Omega3 + e6Omega3 =
      (3 : ℤ) • (wρ • e6OmegaSum - e6Shift wρ) := by
    rw [rho_eq_smul_all_tw S hFr hΦ hwρ e6Omega3]
    have hP : permLattice e6TwPerm e6Omega3 + e6Omega3 = (3 : ℤ) • e6OmegaSum := by
      simpa [e6TwPerm] using
        (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.GraphAux.permLattice_e6Omega3_add)
    calc wρ • permLattice e6TwPerm e6Omega3 + e6Omega3
        = wρ • (permLattice e6TwPerm e6Omega3 + e6Omega3) - wρ • e6Omega3 + e6Omega3 := by
          rw [smul_add]; abel
      _ = wρ • ((3 : ℤ) • e6OmegaSum) - wρ • e6Omega3 + e6Omega3 := by rw [hP]
      _ = (3 : ℤ) • (wρ • e6OmegaSum) - (wρ • e6Omega3 - e6Omega3) := by
          rw [smul_comm wρ (3 : ℤ)]; abel
      _ = (3 : ℤ) • (wρ • e6OmegaSum - e6Shift wρ) := by
          rw [← three_smul_e6Shift wρ, smul_sub]
  have hshift : rootChar a (e6Shift w) = 1 :=
    rootChar_e6Shift_eq_one_of_twisted (σ := S.rhoHom) hap
      (wρ • e6OmegaSum - e6Shift wρ) hσΩ hw huSigma hσw hχ
  have hwSigma' : w ∈ kernelReflectionGroup a :=
    mem_kernelReflectionGroup_of_e6Shift a hap hw hshift
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

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

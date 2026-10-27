module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CentralLat
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjClass

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.SeitzGeneration.ExcHighThree (twPhi twPhi_map tw_torus_conj_fixed
  tw_class_trivial_of_mem exists_primCubeRoot_of_charP)

set_option linter.unusedSectionVars false

private theorem d4t2ct_equiv {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] {q : ℕ} (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) :
    ∃ (ε : L →+* AlgebraicClosure K) (Fr' : AlgebraicClosure K →+* AlgebraicClosure K),
      ε.comp (algebraMap K L) = algebraMap K (AlgebraicClosure K) ∧ (∀ c, Fr' c = c ^ q) ∧
        ε.comp Fr = Fr'.comp ε := by
  obtain ⟨e⟩ : Nonempty (L ≃ₐ[K] AlgebraicClosure K) := ⟨IsAlgClosure.equiv K L _⟩
  refine ⟨(e : L →+* AlgebraicClosure K),
    (e : L →+* AlgebraicClosure K).comp (Fr.comp (e.symm : AlgebraicClosure K →+* L)),
    RingHom.ext fun c => by simp, fun c => by simp [hFr], RingHom.ext fun c => by simp⟩

section Central


private theorem d4t2ct_transport {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (g0 : ModGL Tag.E6 L) (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    {ω : List (Fin Tag.E6.rank)} (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (hF : twistHom TwistTag.E6 L Fr g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω))
    (u z : Fin Tag.E6.rank → Lˣ) (hΦ : twPhi Fr ω u = u * z) (hz : e6RootParams z = 1)
    (hz1 : z ≠ 1) :
    twistHom TwistTag.E6 L Fr (rootDiagUnit Tag.E6 (e6RootParams u)) =
        (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω))⁻¹ *
          rootDiagUnit Tag.E6 (e6RootParams u) *
            canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) ∧
      g0 * rootDiagUnit Tag.E6 (e6RootParams u) * g0⁻¹ ∉
        (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨ε, Fr', he, hFr', hint⟩ := d4t2ct_equiv (K := K) Fr hFr
  have hεinj : Function.Injective (baseChangeGL (τ := Tag.E6) ε) := baseChangeGL_injective ε
  have hN : baseChangeGL ε (canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd ω)) = canonicalRep (coxeterSystem Tag.E6)
        (AlgebraicClosure K) ((coxeterSystem Tag.E6).wordProd ω) :=
    CFSG.LieType.Chevalley.baseChangeGL_canonicalRep ε _
  have ht : baseChangeGL ε (rootDiagUnit Tag.E6 (e6RootParams u)) =
      rootDiagUnit Tag.E6 (e6RootParams fun l => Units.map ε.toMonoidHom (u l)) := by
    rw [baseChangeGL_rootDiagUnit, e6RootParams_map']
  have hΦ' : twPhi Fr' ω (fun l => Units.map ε.toMonoidHom (u l)) =
      (fun l => Units.map ε.toMonoidHom (u l)) * fun l => Units.map ε.toMonoidHom (z l) := by
    rw [twPhi_map ε Fr Fr' hint ω u, hΦ]
    funext l
    exact map_mul (Units.map ε.toMonoidHom) (u l) (z l)
  have hz' : e6RootParams (fun l => Units.map ε.toMonoidHom (z l)) = 1 := by
    rw [e6RootParams_map', hz]
    funext j
    exact map_one (Units.map ε.toMonoidHom)
  have hz1' : (fun l => Units.map ε.toMonoidHom (z l)) ≠ 1 := fun h => hz1 (funext fun l =>
    Units.map_injective (f := ε.toMonoidHom) ε.injective
      ((congrFun h l).trans (map_one (Units.map ε.toMonoidHom)).symm))
  have hg0' : baseChangeGL ε g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ε hg0C
  have hF' : twistHom TwistTag.E6 (AlgebraicClosure K) Fr' (baseChangeGL ε g0) =
      baseChangeGL ε g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
        ((coxeterSystem Tag.E6).wordProd ω) := by
    have e2 : baseChangeGL ε (g0 * canonicalRep (coxeterSystem Tag.E6) L
        ((coxeterSystem Tag.E6).wordProd ω)) = baseChangeGL ε g0 *
          canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
            ((coxeterSystem Tag.E6).wordProd ω) := by
      rw [map_mul, hN]
    exact (twistHom_baseChangeGL (t := TwistTag.E6) ε hint g0).trans
      ((congrArg (baseChangeGL ε) hF).trans e2)
  refine ⟨hεinj ?_, fun hmem => ?_⟩
  ·
    have e3 := twistHom_baseChangeGL (t := TwistTag.E6) ε hint
      (rootDiagUnit Tag.E6 (e6RootParams u))
    have e4 : baseChangeGL ε ((canonicalRep (coxeterSystem Tag.E6) L
        ((coxeterSystem Tag.E6).wordProd ω))⁻¹ * rootDiagUnit Tag.E6 (e6RootParams u) *
          canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω)) =
        (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
          ((coxeterSystem Tag.E6).wordProd ω))⁻¹ *
          rootDiagUnit Tag.E6 (e6RootParams fun l => Units.map ε.toMonoidHom (u l)) *
            canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K)
              ((coxeterSystem Tag.E6).wordProd ω) := by
      rw [map_mul, map_mul, map_inv, hN, ht]
    exact e3.symm.trans ((congrArg (twistHom TwistTag.E6 (AlgebraicClosure K) Fr') ht).trans
      ((tw_torus_conj_fixed hp hK σ hσ Fr' hFr' hω _ _ hΦ' hz').trans e4.symm))
  ·
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hmem
    have e1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) y =
        baseChangeGL ε (baseChangeGL (algebraMap K L) y) := by
      rw [← he, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL]
    have e2 : baseChangeGL ε (g0 * rootDiagUnit Tag.E6 (e6RootParams u) * g0⁻¹) =
        baseChangeGL ε g0 * rootDiagUnit Tag.E6
          (e6RootParams fun l => Units.map ε.toMonoidHom (u l)) * (baseChangeGL ε g0)⁻¹ := by
      rw [map_mul, map_mul, map_inv, ht]
    have hyu : baseChangeGL (algebraMap K (AlgebraicClosure K)) y = baseChangeGL ε g0 *
        rootDiagUnit Tag.E6 (e6RootParams fun l => Units.map ε.toMonoidHom (u l)) *
          (baseChangeGL ε g0)⁻¹ :=
      e1.trans ((congrArg (baseChangeGL ε) hyeq).trans e2)
    have key := tw_class_trivial_of_mem hp hf hK σ hσ hq Fr' hFr' (baseChangeGL ε g0) hg0' hω
      hF' _ hy hyu
    have h1 : twPhi Fr' ω (fun l => Units.map ε.toMonoidHom (u l)) =
        fun l => Units.map ε.toMonoidHom (u l) := key
    rw [hΦ'] at h1
    exact hz1' (mul_left_cancel (h1.trans (mul_one _).symm))

theorem d4t2CentralTorus_holds : D4T2CentralTorus := by
  intro L _ _ p₀ S hS hAlg l f hl hf hq hl3 h3 h3q a hT hap hall m hm
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP L l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  obtain ⟨w, hn, hρw⟩ := KSNotAll24.d4t2out_rho_eq S hS
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : S.D.Φ = twistHom TwistTag.E6 L Fr := MonoidHom.ext fun g => (hΦ g).trans rfl
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hFr' : ∀ c, Fr c = c ^ (l ^ f) := fun c => by rw [hFr, hq]
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  have hq2 : 2 ≤ l ^ f := by
    rw [← hq]
    exact hq1
  have hq3 : (l ^ f) % 3 = 2 := by
    obtain ⟨k, hk⟩ := h3q
    omega
  obtain ⟨K, hKcard, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield (Ω := L) (ℓ := l) (f := f) hf
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ hl.ne_zero))
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, ← pow_mul])
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ (l ^ f) :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K l f) ⟨(iterateFrobenius K l f).injective,
      Finite.surjective_of_injective (iterateFrobenius K l f).injective⟩,
      fun c => iterateFrobenius_def l f c⟩
  haveI : IsAlgClosure K L := ⟨inferInstance, ⟨fun x => by
    obtain ⟨k, hk, hx⟩ := hAlg x
    refine ⟨Polynomial.X ^ (S.D.q ^ k) - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow hk.ne' hq1), ?_⟩
    simp [hx]⟩⟩
  have hΓ : S.D.Γ = ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    Γ_eq_map_twistedE6RootGroup hl hf hKcard hσ hFr' S.D hΦ'
  have hM : S.D.model = (twistedFixedGroup TwistTag.E6 L Fr).map
      (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    model_eq_map_twistedFixedGroup S.D hΦ'
  have hidx : (S.Γ.subgroupOf S.D.model).index ∣ 3 := by
    have h1 := CFSG.LieType.SeitzGeneration.twisted_E6_relIndex_dvd_three hl hf K hKcard
      σ.toRingHom hσ L Fr hFr' (le_refl (twistedFixedGroup TwistTag.E6 L Fr))
    have h2 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj S.D.g0⁻¹).toMonoidHom)
      ((twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)))
      (twistedFixedGroup TwistTag.E6 L Fr) (MulAut.conj S.D.g0⁻¹).injective
    have e : S.D.Γ.relIndex S.D.model = ((twistedE6RootGroup K σ).map
        (baseChangeGL (algebraMap K L))).relIndex (twistedFixedGroup TwistTag.E6 L Fr) := by
      rw [hΓ, hM]
      exact h2
    show S.D.Γ.relIndex S.D.model ∣ 3
    rw [e]
    exact h1
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hall]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap hall i
  have hsub : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
    fun γ hγ => hγ.1
  have hker : kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i :=
    (Set.eq_of_subset_of_ncard_le hsub (hall.trans hc.symm).le hfin).symm
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, hρC⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  have hbij : Set.BijOn S.ρ (componentRoots (rootCharHom a) i)
      (componentRoots (rootCharHom a) i) :=
    ((hfin.subset hsub).injOn_iff_bijOn_of_mapsTo fun γ hγ => hρC γ hγ).1 S.ρ.injective.injOn
  have hρ' : ∀ γ ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
      γ = (coxeterSystem Tag.E6).wordProd ω • permLattice e6RhoFour δ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hbij.surjOn hγ
    refine ⟨δ, hδ, ?_⟩
    rw [hρw δ (hsub hδ).1, e6RhoFour_eq_twistPerm]
    rfl
  obtain ⟨ζ, hζ⟩ := exists_primCubeRoot_of_charP (L := L) hl3
  obtain ⟨u, z, hu, hz, hz1, hcent⟩ := d4t2ct_exists_lang hq2 hFr' hζ ω v hv hρ'
  have hg0 : twistHom TwistTag.E6 L Fr S.D.g0 =
      S.D.g0 * canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) := by
    have h := S.D.lang
    rw [hΦ', hn] at h
    exact h
  obtain ⟨hfix, hnotC⟩ := d4t2ct_transport hl hf hKcard σ hσ hq3 Fr hFr' S.D.g0 S.D.g0_mem hω
    hg0 u z hu hz hz1
  have hΦt : S.D.Φ (rootDiagUnit Tag.E6 (e6RootParams u)) =
      (canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω))⁻¹ *
        rootDiagUnit Tag.E6 (e6RootParams u) *
          canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [hΦ']
    exact hfix
  have hT0 : rootDiagUnit Tag.E6 (e6RootParams u) ∈ S.D.torus := by
    refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [hΦt, hn]
    group
  have hT0M : rootDiagUnit Tag.E6 (e6RootParams u) ∈ S.D.model := S.D.torus_le_model hT0
  have hnot : rootDiagUnit Tag.E6 (e6RootParams u) ∉ S.Γ := by
    intro hmem
    have hmem' : rootDiagUnit Tag.E6 (e6RootParams u) ∈ S.D.Γ := hmem
    rw [hΓ] at hmem'
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 hmem'
    refine hnotC ?_
    have e : S.D.g0 * rootDiagUnit Tag.E6 (e6RootParams u) * S.D.g0⁻¹ = y := by
      rw [← hyt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  have hM0 : toralRootGroup Tag.E6 L a ≤
      Subgroup.centralizer {rootDiagUnit Tag.E6 (e6RootParams u)} := by
    show torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a) ≤ _
    refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (rootDiagUnit_mul_comm_of_mem_torusGroup (e6RootParams u) hx).symm)
      (iSup₂_le fun γ hγ => ?_)
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    have hγ' : γ ∈ kernelRoots (rootCharHom a) := hγ
    rw [hker] at hγ'
    have h1 := rootDiagUnit_conj_pinnedX (τ := Tag.E6) (e6RootParams u) hγ.1 c
    rw [hcent γ hγ', Units.val_one, one_mul] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1).symm
  haveI hnormal : (S.Γ.subgroupOf S.D.model).Normal := by
    have e : S.Γ.subgroupOf S.D.model = ⁅(⊤ : Subgroup S.D.model), ⊤⁆ := by
      have h1 : ⁅S.D.model, S.D.model⁆ =
          Subgroup.map S.D.model.subtype ⁅(⊤ : Subgroup S.D.model), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      show (⁅S.D.model, S.D.model⁆ : Subgroup (ModGL Tag.E6 L)).subgroupOf S.D.model = _
      rw [h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  have hidx3 : (S.Γ.subgroupOf S.D.model).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h | h
    · exfalso
      apply hnot
      have h2 : (⟨_, hT0M⟩ : S.D.model) ∈ S.Γ.subgroupOf S.D.model := by
        rw [Subgroup.index_eq_one.1 h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 h2
    · exact h
  have hcard : Nat.card (S.D.model ⧸ S.Γ.subgroupOf S.D.model) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : (QuotientGroup.mk ⟨_, hT0M⟩ : S.D.model ⧸ S.Γ.subgroupOf S.D.model) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hnot
  obtain ⟨n, hn'⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_of_prime_card hcard hne
    (g' := (QuotientGroup.mk ⟨m, hm⟩ : S.D.model ⧸ S.Γ.subgroupOf S.D.model)))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq] at hn'
  refine ⟨(rootDiagUnit Tag.E6 (e6RootParams u) ^ n)⁻¹, inv_mem (pow_mem hT0 n),
    fun x hx => ?_, ?_⟩
  · have hc : Commute x (rootDiagUnit Tag.E6 (e6RootParams u)) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hM0 hx)
    exact (hc.pow_right n).inv_right.symm.eq
  · simpa using Subgroup.mem_subgroupOf.1 hn'

end Central

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

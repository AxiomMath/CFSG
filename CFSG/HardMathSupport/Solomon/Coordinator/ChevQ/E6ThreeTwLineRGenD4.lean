module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineRGenConn
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2SpinPerfect
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgebraicZMod

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSLineR

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24 CFSG.LieType.Seitz
open CFSG.RankThree.PartOne.KE (d4Nodes)
open scoped Pointwise

set_option linter.unusedSectionVars false


theorem d4t2_rElem_mem_layer {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) (hAlg : S.IsAlgebraic)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    {x : ModGL Tag.E6 L} (hx : x ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a})
    {k : ℕ} (hxk : x ^ (l ^ k) = 1) :
    x ∈ sSup {J | CFSG.Open.IsComponentOf J
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a})} := by
  classical
  obtain ⟨hch, -⟩ := S.exists_charP_isAlgebraic_zmod hAlg hl hf hq
  haveI := hch
  haveI : Fact l.Prime := ⟨hl⟩
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one hall
  obtain ⟨i, v, hker, hv, hρ⟩ := d4t2tm_class S h3 hT hap hall
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (ModGL Tag.E6 L),
      U = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := ⟨_, rfl⟩
  have hUker : rootSpan Tag.E6 L (rootCharKernel a) = U := by
    rw [hUdef, ← hker]
    rfl
  have hPperf : ⁅U ⊓ S.D.model, U ⊓ S.D.model⁆ = U ⊓ S.D.model := by
    by_cases hin : twistInner (kernelRoots (rootCharHom a))
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    · have h := d4t2_fixedSpinPerfect S hS hAlg hl hf hq hl3 h3 h3q hT hap hall hin
      rw [hker, ← hUdef] at h
      exact h
    · have hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
          (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
        rwa [← hker]
      have hqs := d4t2out_rootSpan_model_quasisimple S hS (by omega) hq h3q hT hap i v hv
        hker.le hρ hnin
      rw [hUdef]
      exact Subgroup.isPerfect_iff.1 hqs.1.1
  have hPΓ : U ⊓ S.D.model ≤ S.Γ :=
    calc U ⊓ S.D.model = ⁅U ⊓ S.D.model, U ⊓ S.D.model⁆ := hPperf.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ := Subgroup.commutator_mono inf_le_right inf_le_right
  have hPC : U ⊓ S.D.model ≤ Subgroup.centralizer {rootDiagUnit .E6 a} := fun y hy => by
    have h : y ∈ toralCentralizer .E6 L a :=
      rootSpan_rootCharKernel_le_toralCentralizer a (by rw [hUker]; exact hy.1)
    exact (Subgroup.mem_inf.1 h).2
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3 (fun h => absurd h (by decide))
    hT hap hd1
  have hPcomp : U ⊓ S.D.model ≤
      sSup {J | CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a})} := by
    refine (perfect_le_iSup_rationalComponent_of_prime S Nat.prime_three hT hap hd1 hTame
      (U ⊓ S.D.model) (le_inf hPΓ hPC) hPperf).trans (iSup_le fun j => ?_)
    exact le_sSup (isComponentOf_rationalComponent S hT j.1 j.2)
  obtain ⟨hxΓ, hxa⟩ := Subgroup.mem_inf.1 hx
  have hxmodel : x ∈ S.D.model := S.Γ_le_model hxΓ
  have hxC : x ∈ toralCentralizer .E6 L a :=
    Subgroup.mem_inf.2 ⟨(S.D.mem_model.1 hxmodel).1, hxa⟩
  obtain ⟨n, -, hnN, hn3, hgen⟩ := d4t2_centralizer_generator a hap
  obtain ⟨m, hm, j, -, hxmj⟩ := hgen x hxC
  have hnjN : n ^ j ∈ Subgroup.normalizer (toralRootGroup .E6 L a : Set (ModGL .E6 L)) :=
    pow_mem hnN j
  have hnj : n ^ j ∈ toralRootGroup .E6 L a := by
    have h1 : (n ^ j) ^ (l ^ k) ∈ toralRootGroup .E6 L a := by
      refine pow_mem_of_mul_pow_eq_one hnjN (r₀ := (n ^ j)⁻¹ * m * n ^ j) ?_ ?_
      · have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hnjN) m).1 hm
        simpa only [inv_inv] using h
      · rw [show n ^ j * ((n ^ j)⁻¹ * m * n ^ j) = x by rw [hxmj]; group]
        exact hxk
    have h2 : (n ^ j) ^ 3 ∈ toralRootGroup .E6 L a := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_mem hn3 j
    exact mem_of_pow_mem_of_coprime
      (Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hl).2 (Ne.symm hl3))) h2 h1
  have hxM : x ∈ toralRootGroup .E6 L a := by
    rw [hxmj]
    exact mul_mem hm hnj
  have hHU : torusGroup Tag.E6 L ≤ Subgroup.normalizer (U : Set (ModGL Tag.E6 L)) := by
    rw [hUdef]
    exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (S := componentRoots (rootCharHom a) i) (fun γ hγ => hγ.1.1)
  have hxHU : x ∈ torusGroup Tag.E6 L ⊔ U := by
    rw [← hUker]
    exact hxM
  have hmul : x ∈ ((torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) * (U : Set (ModGL Tag.E6 L))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHU]
    exact hxHU
  obtain ⟨t₀, ht₀, u, hu, rfl⟩ := Set.mem_mul.1 hmul
  have ht₀U : t₀ ^ (l ^ k) ∈ U := pow_mem_of_mul_pow_eq_one (hHU ht₀) hu hxk
  have ht₀U' : t₀ ^ (l ^ k) ∈ rootSpan Tag.E6 L
      ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
    rw [← hv, ← hUdef]
    exact ht₀U
  obtain ⟨s, hs, hss⟩ := d4t2tl_div_torus_inf_rootSpan (L := L) v (N := l ^ k)
    (pow_pos hl.pos k) (t₀ ^ (l ^ k)) ⟨pow_mem ht₀ _, ht₀U'⟩
  have hts : t₀ = s := by
    have hcomm : Commute t₀ s := by
      obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
      exact rootDiagUnit_mul_comm_of_mem_torusGroup b hs.1
    have h1 : (t₀ * s⁻¹) ^ (l ^ k) = 1 := by
      rw [hcomm.inv_right.mul_pow, inv_pow, hss, mul_inv_cancel]
    exact mul_inv_eq_one.1 (eq_one_of_torus_pow_eq_one (mul_mem ht₀ (inv_mem hs.1)) h1)
  have ht₀Um : t₀ ∈ U := by
    rw [hts, hUdef, hv]
    exact hs.2
  exact hPcomp ⟨mul_mem ht₀Um hu, hxmodel⟩

theorem mem_layer_of_d4 {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hd : TwE6LineDim K σ f 30) {c : twistedE6RootGroup K σ} (hfc : f c = c) {m : ℕ}
    (hcm : c ^ (ringChar K ^ m) = 1) :
    c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} := by
  classical
  obtain ⟨h, rfl, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  have hker : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  have h3dvd : 3 ∣ ringChar K ^ D.e + 1 := by
    rw [← D.hqe]
    exact hE.three_dvd
  have hAlg : D.S.IsAlgebraic :=
    D.S.isAlgebraic_of_algebraic K 2 (by rw [D.hSq, ← D.hqe]; exact hE.card_field)
  have hmapfp := D.map_fixedPoints
  have hcfix : c ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) := by
    have hle : Subgroup.zpowers (twistedE6InndiagConj K σ h) ≤
        MulAction.stabilizer (MulAut (twistedE6RootGroup K σ)) c :=
      Subgroup.zpowers_le.2 hfc
    intro φ hφ
    exact hle hφ
  have hic : D.ι c ∈ D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} := by
    rw [← hmapfp]
    exact ⟨c, hcfix, rfl⟩
  have hicm : D.ι c ^ (ringChar K ^ m) = 1 := by rw [← map_pow, hcm, map_one]
  have key := d4t2_rElem_mem_layer D.S D.hS hAlg D.hℓ D.he D.hSq hE.char_ne_three D.hL3 h3dvd
    D.hT D.hap hker hic hicm
  have hCd : D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a} ≤ D.ι.range := fun x hx => by
    rw [D.hrange]
    exact (Subgroup.mem_inf.1 hx).1
  have hcomapfix : (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}).comap D.ι =
      fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) := by
    rw [← hmapfp]
    exact Subgroup.comap_map_eq_self_of_injective D.hinj _
  have hle : sSup {J | CFSG.Open.IsComponentOf J
        (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a})} ≤
      (sSup {J | CFSG.Open.IsComponentOf J
        (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))}).map D.ι := by
    refine sSup_le fun J hJ => ?_
    have hJ' : CFSG.Open.IsComponentOf J
        (D.S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 D.a}) := hJ
    have hJle : J ≤ D.ι.range := hJ'.1.trans hCd
    have hJc := isComponentOf_comap_of_injective D.ι D.hinj hJle hCd hJ'
    rw [hcomapfix] at hJc
    calc J = (J.comap D.ι).map D.ι := (Subgroup.map_comap_eq_self hJle).symm
      _ ≤ _ := Subgroup.map_mono (le_sSup hJc)
  obtain ⟨c', hc', hcc'⟩ := hle key
  rw [D.hinj hcc'] at hc'
  exact hc'

end KSLineR

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

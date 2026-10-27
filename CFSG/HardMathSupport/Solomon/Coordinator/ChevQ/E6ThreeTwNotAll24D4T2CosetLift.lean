module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetLat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CosetDefs
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

section CosetLift

set_option linter.unusedSectionVars false


theorem d4t2c_exists_torus_mul_mem_model {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {w : WeylGroup .E6} (hw : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w)
    {M : WeylGroup .E6}
    (hcomm : ∀ x : Fin Tag.E6.rank → ℤ, M • (w • permLattice (τ := .E6) TwistTag.E6.perm x) =
      w • permLattice (τ := .E6) TwistTag.E6.perm (M • x)) :
    ∃ h ∈ torusGroup .E6 L, h * canonicalRep (coxeterSystem Tag.E6) L M ∈ S.D.model := by
  classical
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  have ht' : t = TwistTag.E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  subst ht'
  have hΦF : ∀ y, S.D.Φ y = twistHom TwistTag.E6 L Fr y := fun y => (hΦ y).trans rfl
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.two_le
  obtain ⟨M', hM'⟩ : ∃ M' : WeylGroup Tag.E6, M' = weylTwist TwistTag.E6 M := ⟨_, rfl⟩
  have htw : ∀ v : Fin Tag.E6.rank → ℤ, M' • permLattice (τ := .E6) TwistTag.E6.perm v =
      permLattice (τ := .E6) TwistTag.E6.perm (M • v) := fun v => by
    rw [hM']
    exact weylTwist_smul_permLattice TwistTag.E6 M v
  have hMw : M * w = w * M' := by
    refine eq_of_smul_eq_smul fun x : Fin Tag.E6.rank → ℤ => ?_
    have h1 := hcomm (permLattice (τ := .E6) TwistTag.E6.perm.symm x)
    have h2 : permLattice (τ := .E6) TwistTag.E6.perm
        (permLattice (τ := .E6) TwistTag.E6.perm.symm x) = x := permLattice_permLattice_symm _ _
    rw [h2] at h1
    rw [mul_smul, mul_smul, h1, ← htw, h2]
  have hwM : w * M' * w⁻¹ = M := by
    rw [← hMw]
    group
  have hFM : S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L M) =
      canonicalRep (coxeterSystem Tag.E6) L M' := by
    rw [hΦF, hM']
    exact twistHom_canonicalRep TwistTag.E6 L Fr M
  obtain ⟨k₀, hk₀, hk₀e⟩ : ∃ k₀ ∈ torusGroup .E6 L,
      (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ *
          canonicalRep (coxeterSystem Tag.E6) L (w * M' * w⁻¹) *
        canonicalRep (coxeterSystem Tag.E6) L w = k₀ * canonicalRep (coxeterSystem Tag.E6) L M' :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.canonicalRep_inv_mul_conj_mem_tw (L := L) w w M'
  rw [hwM] at hk₀e
  obtain ⟨X, hXdef⟩ : ∃ X : ModGL Tag.E6 L, X = S.D.n * k₀⁻¹ * S.D.n⁻¹ := ⟨_, rfl⟩
  have hX : X ∈ torusGroup .E6 L := by
    rw [hXdef, hw]
    exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) w) _).1
      (inv_mem hk₀)
  have hstep : S.D.n * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L M) * S.D.n⁻¹ =
      X * canonicalRep (coxeterSystem Tag.E6) L M := by
    have e : canonicalRep (coxeterSystem Tag.E6) L M' = k₀⁻¹ *
        ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * canonicalRep (coxeterSystem Tag.E6) L M *
          canonicalRep (coxeterSystem Tag.E6) L w) := by
      rw [hk₀e]
      group
    rw [hFM, e, hXdef, hw]
    group
  obtain ⟨h, hh, hhX⟩ : ∃ h ∈ torusGroup .E6 L, h * (S.D.n * S.D.Φ h * S.D.n⁻¹)⁻¹ = X := by
    obtain ⟨h, hh, hhX⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_torus_lang_tw hq2 hFr w hX
    refine ⟨h, hh, ?_⟩
    rw [hw, hΦF h]
    exact hhX
  have hYH : S.D.n * S.D.Φ h * S.D.n⁻¹ ∈ torusGroup .E6 L := by
    have e : S.D.n * S.D.Φ h * S.D.n⁻¹ = X⁻¹ * h := by
      rw [← hhX]
      group
    rw [e]
    exact mul_mem (inv_mem hX) hh
  have hYh : S.D.n * S.D.Φ h * S.D.n⁻¹ * h = h * (S.D.n * S.D.Φ h * S.D.n⁻¹) := by
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hYH
    rw [hc]
    exact rootDiagUnit_mul_comm_of_mem_torusGroup c hh
  refine ⟨h, hh, S.D.mem_model.2 ⟨?_, ?_⟩⟩
  · exact mul_mem
      (mem_toralCentralizer.1 (torusGroup_le_toralCentralizer (1 : Fin Tag.E6.rank → Lˣ) hh)).1
      (canonicalRep_mem_adjointGroup _ L M)
  · rw [map_mul]
    calc S.D.n * (S.D.Φ h * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L M)) * S.D.n⁻¹
        = S.D.n * S.D.Φ h * S.D.n⁻¹ *
            (S.D.n * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L M) * S.D.n⁻¹) := by group
      _ = S.D.n * S.D.Φ h * S.D.n⁻¹ * (X * canonicalRep (coxeterSystem Tag.E6) L M) := by
          rw [hstep]
      _ = S.D.n * S.D.Φ h * S.D.n⁻¹ * h * (S.D.n * S.D.Φ h * S.D.n⁻¹)⁻¹ *
            canonicalRep (coxeterSystem Tag.E6) L M := by
          rw [← hhX]
          group
      _ = h * canonicalRep (coxeterSystem Tag.E6) L M := by
          rw [hYh]
          group

theorem d4t2c_toral (hC : D4T2CentralTorus) {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹) (hAlg : S.IsAlgebraic)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    {A : Subgroup (ModGL Tag.E6 L)} (hAT : A ≤ S.D.torus) (hab : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 3) (hdA : rootDiagUnit .E6 a ∈ A)
    (hroot : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ¬ ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ A → rootChar b γ = 1) :
    ∃ ε ∈ A, ε ∉ Subgroup.zpowers (rootDiagUnit .E6 a) ∧ ∃ y ∈ S.Γ,
      y * rootDiagUnit .E6 a = rootDiagUnit .E6 a * y ∧ y * ε = ε * y ∧
      y ∉ toralRootGroup .E6 L a := by
  obtain ⟨w, hw⟩ := S.D.n_weyl
  obtain ⟨ε, hεA, hεZ, M, hMd, hMε, hMM, hcomm⟩ :=
    d4t2c_toral_weyl S hS hq h3q hap hall hAT hab hcard hdA hroot hw
  obtain ⟨h, hh, hm⟩ := d4t2c_exists_torus_mul_mem_model S hS hw hcomm
  obtain ⟨n, hn⟩ : ∃ n, n = canonicalRep (coxeterSystem Tag.E6) L M := ⟨_, rfl⟩
  rw [← hn] at hMd hMε hMM hm
  obtain ⟨t, htT, htc, htΓ⟩ := hC S hS hAlg hl hf hq hl3 h3 h3q (hAT hdA) hap hall _ hm
  have hTM : ∀ {x : ModGL Tag.E6 L}, x ∈ torusGroup .E6 L → x ∈ toralRootGroup .E6 L a :=
    fun hx => Subgroup.mem_sup_left hx
  have hdT : rootDiagUnit .E6 a ∈ torusGroup .E6 L := (Subgroup.mem_inf.1 (hAT hdA)).1
  have hεT : ε ∈ torusGroup .E6 L := (Subgroup.mem_inf.1 (hAT hεA)).1
  have htH : t ∈ torusGroup .E6 L := (Subgroup.mem_inf.1 htT).1
  have hhd : h * rootDiagUnit .E6 a = rootDiagUnit .E6 a * h :=
    (rootDiagUnit_mul_comm_of_mem_torusGroup a hh).symm
  have hhε : h * ε = ε * h := by
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hεT
    exact (rootDiagUnit_mul_comm_of_mem_torusGroup c hh).symm
  have htd : t * rootDiagUnit .E6 a = rootDiagUnit .E6 a * t := htc _ (hTM hdT)
  have htε : t * ε = ε * t := htc _ (hTM hεT)
  refine ⟨ε, hεA, hεZ, t * (h * n), htΓ, ?_, ?_, ?_⟩
  · calc t * (h * n) * rootDiagUnit .E6 a = t * (h * (n * rootDiagUnit .E6 a)) := by group
      _ = t * (h * rootDiagUnit .E6 a) * n := by
          rw [hMd]
          group
      _ = t * rootDiagUnit .E6 a * (h * n) := by
          rw [hhd]
          group
      _ = rootDiagUnit .E6 a * (t * (h * n)) := by
          rw [htd]
          group
  · calc t * (h * n) * ε = t * (h * (n * ε)) := by group
      _ = t * (h * ε) * n := by
          rw [hMε]
          group
      _ = t * ε * (h * n) := by
          rw [hhε]
          group
      _ = ε * (t * (h * n)) := by
          rw [htε]
          group
  · intro hy
    apply hMM
    have e : n = h⁻¹ * (t⁻¹ * (t * (h * n))) := by group
    rw [e]
    exact mul_mem (inv_mem (hTM hh)) (mul_mem (inv_mem (hTM htH)) hy)

end CosetLift

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

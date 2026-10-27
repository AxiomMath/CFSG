module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Lattice
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.Q1327T

section Frobenius

theorem e6d4t2_frob_params
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) :
    ∃ e : ℕ, 1 ≤ e ∧ S.D.q = 2 ^ e := by
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have h2 : ℓ = 2 := CharP.eq L hchar ‹CharP L 2›
  subst h2
  exact ⟨f, hf, hq⟩

theorem e6d4t2_step_eq_frobTwist
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hS : E6ShapeSetup S) :
    ∃ (e : ℕ) (Q : ModGL Tag.E6 L), 1 ≤ e ∧ S.D.q = 2 ^ e ∧
      ∀ g, S.D.step g = frobTwistGL Tag.E6 L 2 e Q g := by
  obtain ⟨e, he, hq⟩ := e6d4t2_frob_params S
  obtain ⟨Fr, hFr, hcase⟩ := hS
  have hFr' : Fr = iterateFrobenius L 2 e := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  rcases hcase with ⟨hΦ, -⟩ | ⟨hΦ, -⟩
  · refine ⟨e, S.D.n, he, hq, fun g => ?_⟩
    change S.D.n * S.D.Φ g * S.D.n⁻¹ = S.D.n * entrywiseFrobGL Tag.E6 L 2 e g * S.D.n⁻¹
    rw [hΦ, hFr']
  · refine ⟨e, S.D.n * e6Diagram L, he, hq, fun g => ?_⟩
    have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ :=
      fun g => by rw [hΦ]; rfl
    change S.D.n * S.D.Φ g * S.D.n⁻¹ =
      (S.D.n * e6Diagram L) * entrywiseFrobGL Tag.E6 L 2 e g * (S.D.n * e6Diagram L)⁻¹
    rw [hΦ', hFr']
    group

end Frobenius

section Stability

theorem e6d4t2_rho_mem_kernel
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ kernelRoots (rootCharHom a)) : S.ρ α ∈ kernelRoots (rootCharHom a) := by
  refine ⟨(S.frob.isRoot_iff α).2 hα.1, ?_⟩
  show rootChar a (S.ρ α) = 1
  rw [S.frob.rootChar_eq a hT α hα.1]
  have h1 : rootChar a α = 1 := hα.2
  rw [h1, one_pow]

theorem e6d4t2_step_mem_torus
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hS : E6ShapeSetup S) {h : ModGL Tag.E6 L} (hh : h ∈ torusGroup Tag.E6 L) :
    S.D.step h ∈ torusGroup Tag.E6 L := by
  obtain ⟨Fr, hFr, hcase⟩ := hS
  obtain ⟨w, hwn⟩ := S.D.n_weyl
  have hnN : S.D.n ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)) := by
    rw [hwn]
    exact canonicalRep_mem_normalizer (R := L) w
  have hq0 : 0 < S.D.q := S.hqpow.1.pos
  have hsurj : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  have hΦ : S.D.Φ h ∈ torusGroup Tag.E6 L := by
    rcases hcase with ⟨hΦ, -⟩ | ⟨hΦ, -⟩
    · rw [hΦ]
      obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.units_map_entrywiseHom_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    · rw [hΦ]
      exact twistHom_mem_torusGroup' (t := TwistTag.E6) (K := L) (σ := Fr) hsurj hh
  exact (Subgroup.mem_normalizer_iff.1 hnN _).1 hΦ

theorem e6d4t2_step_mem_rootSpan
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    {x : ModGL Tag.E6 L} (hx : x ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))) :
    S.D.step x ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  have hle : (rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map S.D.step ≤
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup_le fun α => iSup_le fun hα => ?_
    rw [S.frob.map_rootSubgroup α hα.1]
    exact le_iSup₂_of_le (S.ρ α) (e6d4t2_rho_mem_kernel S hT hα) le_rfl
  exact hle ⟨x, hx, rfl⟩

theorem e6d4t2_step_mem_M
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hS : E6ShapeSetup S) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    {m : ModGL Tag.E6 L}
    (hm : m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))) :
    S.D.step m ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
  have hle : (torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a))).map S.D.step ≤
      torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact Subgroup.mem_sup_left (e6d4t2_step_mem_torus S hS hh)
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_right (e6d4t2_step_mem_rootSpan S hT hx)
  exact hle ⟨m, hm, rfl⟩

end Stability

section Weyl

theorem e6d4t2_canonicalRep_inv
    {L : Type} [Field L] [CharP L 2] {τ : Tag} (x : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) L x⁻¹ = (canonicalRep (coxeterSystem τ) L x)⁻¹ := by
  have h := canonicalRep_mul_charTwo (R := L) x x⁻¹
  rw [mul_inv_cancel, canonicalRep_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem e6d4t2_canonicalRep_conj
    {L : Type} [Field L] [CharP L 2] {τ : Tag} (w x : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) L (w * x * w⁻¹) =
      canonicalRep (coxeterSystem τ) L w * canonicalRep (coxeterSystem τ) L x *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
  rw [canonicalRep_mul_charTwo, canonicalRep_mul_charTwo, e6d4t2_canonicalRep_inv]

@[expose] noncomputable def e6d4t2W0 : WeylGroup Tag.E6 :=
  (coxeterSystem TwistTag.E6.tag).wordProd twD4T2W0Word

theorem e6d4t2_w0_smul (α : Fin Tag.E6.rank → ℤ) :
    e6d4t2W0 • α = -(permLattice e6Graph α) := twD4T2W0_smul α

theorem e6d4t2_graph_graph (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Graph (permLattice e6Graph x) = x := by
  rw [← permLattice_mul, e6Graph_mul_self]
  rfl

theorem e6d4t2_graph_neg (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Graph (-x) = -permLattice e6Graph x := by
  funext i
  simp [permLattice]

theorem e6d4t2_w0_mul_self
    : e6d4t2W0 * e6d4t2W0 = 1 := by
  refine CFSG.RankThree.E6.eq_of_smul_single_eq fun j => ?_
  rw [mul_smul, one_smul, e6d4t2_w0_smul, e6d4t2_w0_smul, e6d4t2_graph_neg, neg_neg,
    e6d4t2_graph_graph]

theorem e6d4t2_weylTwist_eq
    (x : WeylGroup Tag.E6) : e6WeylTwist x = e6d4t2W0 * x * e6d4t2W0⁻¹ := by
  have hinv : e6d4t2W0⁻¹ = e6d4t2W0 := inv_eq_of_mul_eq_one_right e6d4t2_w0_mul_self
  refine CFSG.RankThree.E6.eq_of_smul_single_eq fun j => ?_
  have h1 : e6WeylTwist x • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      permLattice e6Graph (x • permLattice e6Graph (Pi.single j 1)) := by
    have := e6WeylTwist_smul x (permLattice e6Graph (Pi.single j 1))
    rw [e6d4t2_graph_graph] at this
    exact this
  rw [h1, hinv, mul_smul, mul_smul, e6d4t2_w0_smul, e6d4t2_w0_smul, smul_neg, e6d4t2_graph_neg,
    neg_neg]

end Weyl

section ShapeWeyl

theorem e6d4t2_shape_weyl
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hS : E6ShapeSetup S) :
    ∃ (w' : WeylGroup Tag.E6) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = ε • (w' • γ)) ∧
      ∀ x : WeylGroup Tag.E6, S.D.step (canonicalRep (coxeterSystem Tag.E6) L x) =
        canonicalRep (coxeterSystem Tag.E6) L (w' * x * w'⁻¹) := by
  obtain ⟨Fr, hFr, hcase⟩ := hS
  rcases hcase with ⟨hΦ, -⟩ | ⟨hΦ, -⟩
  · obtain ⟨w, hwn⟩ := S.D.n_weyl
    refine ⟨w, 1, Or.inl rfl, fun γ hγ => ?_, fun x => ?_⟩
    · rw [one_smul]
      exact S.rho_eq_smul_of_frob hFr hΦ hwn hγ
    · change S.D.n * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L x) * S.D.n⁻¹ = _
      rw [hΦ, hwn, frobenius_canonicalRep Fr x, e6d4t2_canonicalRep_conj]
  · have hS' : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
          (diagramAt .E6 L t h)⁻¹ :=
      ⟨TwistTag.E6, rfl, Fr, hFr, fun g => by rw [hΦ]; rfl⟩
    obtain ⟨w, hwn, hρ⟩ := d4t2out_rho_eq S hS'
    refine ⟨w * e6d4t2W0, -1, Or.inr rfl, fun γ hγ => ?_, fun x => ?_⟩
    · rw [hρ γ hγ, mul_smul, e6d4t2_w0_smul, smul_neg, neg_one_zsmul, neg_neg]
    · have h1 : S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L x) =
          canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist x) := by
        rw [hΦ]
        exact twistHom_canonicalRep TwistTag.E6 L Fr x
      change S.D.n * S.D.Φ (canonicalRep (coxeterSystem Tag.E6) L x) * S.D.n⁻¹ = _
      rw [h1, hwn, ← e6d4t2_canonicalRep_conj, e6d4t2_weylTwist_eq]
      congr 1
      group

end ShapeWeyl

end CFSG.LocalAnalysis.GLTheoremA.T158

end

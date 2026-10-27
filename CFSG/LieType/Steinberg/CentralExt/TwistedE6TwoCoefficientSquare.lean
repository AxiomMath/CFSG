module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCompactPair
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalRecipeSourceSquare
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalFieldLangSquare
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7BaseChange
public noncomputable section

namespace CFSG.StandardType.GGFinModel


open CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement


open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.GroupTheory


open CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.StandardType.TableBExc.E6Three
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag

set_option backward.isDefEq.respectTransparency false in
theorem exists_qTwo_coefficient_transport
    {L : Type} [Field L] [Finite L] (_hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ι : L ≃+* actualQuadraticSubfield 1) :
    ∃ eBC : twistedE6RootGroup L σ ≃* stdGroup,
      ∀ s, stdLangEmbedding (eBC s) =
        baseChangeGL ((actualQuadraticSubfield 1).subtype.comp ι.toRingHom)
          (s : ModGL Tag.E6 L) := by
  obtain ⟨η, hη⟩ := exists_original_coefficient_square (n := 1) (by decide) ι
  let τ : L ≃+* CFSG.LieType.Chevalley.C2E6Overlap.K := η.symm.trans fieldEquiv
  have hbar : ∀ c : CFSG.LieType.Chevalley.C2E6Overlap.K,
      barEquivStd c = c ^ 2 := by
    intro c
    change barHom c = c ^ 2
    rw [barHom_apply, bar]
  have hτ : ∀ c, τ (σ c) = barEquivStd (τ c) := by
    intro c
    rw [hσ c, map_pow, hbar]
  have hC := TwE6KG7.graphFixedRootGroup_map_baseChangeGL_eq τ σ barEquivStd hτ
  let eBC : twistedE6RootGroup L σ ≃* stdGroup :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup L σ)
      (baseChangeGL (τ := Tag.E6) τ.toRingHom)
      (baseChangeGL_injective (τ := Tag.E6) τ.toRingHom)).trans
        (MulEquiv.subgroupCongr hC)
  have hcoe (s : twistedE6RootGroup L σ) :
      (eBC s : ModGL Tag.E6 CFSG.LieType.Chevalley.C2E6Overlap.K) =
        baseChangeGL τ.toRingHom (s : ModGL Tag.E6 L) := rfl
  have hcomp : ((ggRatEmb 2).comp fieldEquiv.symm.toRingHom).comp τ.toRingHom =
      (actualQuadraticSubfield 1).subtype.comp ι.toRingHom := by
    ext x
    change ggRatEmb 2 (fieldEquiv.symm (fieldEquiv (η.symm x))) = _
    rw [fieldEquiv.symm_apply_apply]
    have h := RingHom.congr_fun hη (η.symm x)
    change (actualQuadraticSubfield 1).subtype (ι (η (η.symm x))) =
      ggRatEmb 2 (η.symm x) at h
    rw [η.apply_symm_apply] at h
    exact h.symm
  refine ⟨eBC, ?_⟩
  intro s
  rw [stdLangEmbedding_eq_field_transport, hcoe,
    baseChangeGL_baseChangeGL, hcomp]

set_option backward.isDefEq.respectTransparency false in
theorem exists_qTwo_native_donor_square
    {L : Type} [Field L] [Finite L] (hL4 : Nat.card L = 4)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    (ι : L ≃+* actualQuadraticSubfield 1) :
    ∃ (β : MulAut (twistedE6Group 2 1))
      (j : stdGroup →* ModGL Tag.E6 GGL),
      Function.Injective j ∧
      (∀ s, j (nativeStdTransport hL4 σ hσ s) =
        baseChangeGL ((actualQuadraticSubfield 1).subtype.comp ι.toRingHom)
          (s : ModGL Tag.E6 L)) ∧
      ∀ u, j (isogenyStd (β u)) = ggIotaK .twistedE6 0 1 (by decide) u := by
  obtain ⟨eBC, hBC⟩ := exists_qTwo_coefficient_transport hL4 σ hσ ι
  let δ : MulAut stdGroup := eBC.symm.trans (nativeStdTransport hL4 σ hσ)
  let β : MulAut (twistedE6Group 2 1) := scAut δ
  let j : stdGroup →* ModGL Tag.E6 GGL :=
    stdLangEmbedding.comp δ.symm.toMonoidHom
  refine ⟨β, j, stdLangEmbedding_injective.comp δ.symm.injective, ?_, ?_⟩
  · intro s
    change stdLangEmbedding
      (eBC ((nativeStdTransport hL4 σ hσ).symm (nativeStdTransport hL4 σ hσ s))) = _
    rw [MulEquiv.symm_apply_apply]
    exact hBC s
  · intro u
    change stdLangEmbedding (δ.symm (isogenyStd (scAut δ u))) = _
    rw [scAut_spec, MulEquiv.symm_apply_apply, stdLangEmbedding_isogeny]

set_option backward.isDefEq.respectTransparency false in
theorem exists_original_qTwo_native_actor_square
    {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {L : Type} [Field L] [Finite L] {σ : L ≃+* L}
    {ψ : ↥X →* ↥(twistedE6RootGroup L σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords 1 hBN ψ κ) (hL4 : Nat.card L = 4)
    (hσ : ∀ c, σ c = c ^ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X) :
    ∃ (M : GGDatumModel .twistedE6 1 3
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (ζ0 : GGLˣ) (hζ0 : ζ0 ^ 3 = 1)
      (β : MulAut (twistedE6Group 2 1)) (mu : stdGroup →* ModGL Tag.E6 GGL),
      Function.Injective mu ∧ mu.range = M.D.Γ ∧ orderOf ζ0 = 3 ∧
      (∀ u, mu (isogenyStd (β u)) =
        (MulAut.conj M.D.g0).symm (ggIotaK .twistedE6 0 1 (by decide) u)) ∧
      ∀ (b : ↥Bs) (s : stdGroup),
        mu (originalStdAction hL4 σ hσ hBN ψ hψ hker b s) =
          rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
            (Multiplicative.toAdd (κ b))) * mu s *
          (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
            (Multiplicative.toAdd (κ b))))⁻¹ := by
  obtain ⟨ι, e, g, M, ζ0, hζ0, he, hMg, hMw, hζ0o, muX, hmuX, hΓ, hact⟩ :=
    hκ.exists_original_field_lang_model_square (by decide)
      (by simpa using hL4) (by decide) (fun c => by simpa using hσ c) hψ
  obtain ⟨β, j, hj, hnative, hsource⟩ := exists_qTwo_native_donor_square hL4 σ hσ ι
  let eN := nativeStdTransport hL4 σ hσ
  let mu : stdGroup →* ModGL Tag.E6 GGL :=
    (MulAut.conj M.D.g0).symm.toMonoidHom.comp j
  let q : ↥X →* stdGroup := eN.toMonoidHom.comp ψ
  have hq : Function.Surjective q := eN.surjective.comp hψ
  have hsq : mu.comp q = muX := by
    apply MonoidHom.ext
    intro l
    change (MulAut.conj M.D.g0).symm (j (eN (ψ l))) = muX l
    rw [hnative, hmuX, he]
    rfl
  have hμΓ : mu.range = M.D.Γ := by
    rw [← hΓ]
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨l, rfl⟩ := hq s
      exact ⟨l, (DFunLike.congr_fun hsq l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨q l, DFunLike.congr_fun hsq l⟩
  refine ⟨M, ζ0, hζ0, β, mu,
    (MulAut.conj M.D.g0).symm.injective.comp hj, hμΓ, hζ0o, ?_, ?_⟩
  · intro u
    change (MulAut.conj M.D.g0).symm (j (isogenyStd (β u))) = _
    rw [hsource]
  · intro b s
    obtain ⟨l, rfl⟩ := hq s
    have hα : originalStdAction hL4 σ hσ hBN ψ hψ hker b (q l) =
        q (ggGamma X hBN b l) := by
      exact originalStdAction_apply_mk hL4 σ hσ hBN ψ hψ hker b l
    rw [hα]
    change (mu.comp q) (ggGamma X hBN b l) =
      _ * (mu.comp q) l * _
    rw [hsq]
    exact hact b l

set_option backward.isDefEq.respectTransparency false in
theorem exists_original_qTwo_native_residual_square
    {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {L : Type} [Field L] [Finite L] {σ : L ≃+* L}
    {ψ : ↥X →* ↥(twistedE6RootGroup L σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords 1 hBN ψ κ) (hL4 : Nat.card L = 4)
    (hσ : ∀ c, σ c = c ^ 2) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center ↥X) :
    ∃ (M : GGDatumModel .twistedE6 1 3
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (ζ0 : GGLˣ) (hζ0 : ζ0 ^ 3 = 1)
      (β : MulAut (twistedE6Group 2 1)) (mu : stdGroup →* ModGL Tag.E6 GGL),
      Function.Injective mu ∧ mu.range = M.D.Γ ∧ orderOf ζ0 = 3 ∧
      (∀ u, mu (isogenyStd (β u)) =
        (MulAut.conj M.D.g0).symm (ggIotaK .twistedE6 0 1 (by decide) u)) ∧
      (∀ (b : ↥Bs) (s : stdGroup),
        mu (originalStdAction hL4 σ hσ hBN ψ hψ hker b s) =
          rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
            (Multiplicative.toAdd (κ b))) * mu s *
          (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
            (Multiplicative.toAdd (κ b))))⁻¹) ∧
      ∀ r : MulAut Bs,
        (ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
          ⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
            MonoidHom.eqLocus
              (originalStdAction hL4 σ hσ hBN ψ hψ hker (b : Bs)).toMonoidHom
              (MonoidHom.id stdGroup))).map mu =
        ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
          (Set.range fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
            rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ (b : Bs)))))) := by
  obtain ⟨M, ζ0, hζ0, β, mu, hmu, hΓ, hζ0o, hsource, hact⟩ :=
    exists_original_qTwo_native_actor_square hκ hL4 hσ hψ hker
  refine ⟨M, ζ0, hζ0, β, mu, hmu, hΓ, hζ0o, hsource, hact, ?_⟩
  intro r
  let : Finite stdGroup := finite_stdGroup
  have hk : mu.ker ≤ Subgroup.center stdGroup := by
    rw [(MonoidHom.ker_eq_bot_iff mu).mpr hmu]
    exact bot_le
  have ho : Odd (Nat.card mu.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff mu).mpr hmu]
    simp
  let I := ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs))
  let alpha : I → MulAut stdGroup := fun b =>
    originalStdAction hL4 σ hσ hBN ψ hψ hker (b : Bs)
  let a : I → Fin Tag.E6.rank → GGLˣ := fun b =>
    zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ (b : Bs)))
  let gamma : I → MulAut (ModGL Tag.E6 GGL) :=
    fun b => MulAut.conj (rootDiagUnit Tag.E6 (a b))
  have hcompat : ∀ b u, mu (alpha b u) = gamma b (mu u) := fun b u => hact (b : Bs) u
  have hfixed : (⨅ b, MonoidHom.eqLocus (gamma b).toMonoidHom
      (MonoidHom.id (ModGL Tag.E6 GGL))) =
      Subgroup.centralizer (Set.range fun b => rootDiagUnit Tag.E6 (a b)) := by
    ext x
    simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_iff, Set.forall_mem_range]
    change (∀ b, gamma b x = x) ↔ ∀ b,
      rootDiagUnit Tag.E6 (a b) * x = x * rootDiagUnit Tag.E6 (a b)
    constructor
    · intro h b
      have hb := h b
      change rootDiagUnit Tag.E6 (a b) * x * (rootDiagUnit Tag.E6 (a b))⁻¹ = x at hb
      have hm := congrArg (fun z => z * rootDiagUnit Tag.E6 (a b)) hb
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
    · intro h b
      change rootDiagUnit Tag.E6 (a b) * x * (rootDiagUnit Tag.E6 (a b))⁻¹ = x
      rw [h b]
      group
  have hm := ggOTwoPrime_map_fixedFamily_of_central_odd_kernel
    mu hk ho ⊤ alpha gamma hcompat
  rw [Subgroup.map_top, hΓ, hfixed] at hm
  exact hm

end CFSG.StandardType.GGFinModel

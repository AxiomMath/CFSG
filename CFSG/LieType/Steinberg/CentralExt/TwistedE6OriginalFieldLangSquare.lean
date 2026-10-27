module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoToralCoords
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6MinusculeFixedField
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.LocalAnalysis.StandardType.GGResidualA2Pair
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag
public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.KE8F
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag

set_option backward.isDefEq.respectTransparency false in
theorem TwE6ToralCoords.exists_original_field_actor_square
    {n : ℕ} {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ (ι : K ≃+* actualQuadraticSubfield n)
      (e : AlgebraicClosure K →+* GGL)
      (g : ModGL Tag.E6 (AlgebraicClosure K))
      (g0 : ModGL Tag.E6 GGL) (ζ0 : GGLˣ) (hζ0 : ζ0 ^ 3 = 1),
      e.comp (algebraMap K (AlgebraicClosure K)) =
        (actualQuadraticSubfield n).subtype.comp ι.toRingHom ∧
      g0 = baseChangeGL e g ∧ orderOf ζ0 = 3 ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ 2 ^ n) ∧
        g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
          g * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0) ∧
      ∃ mu : ↥X →* ModGL Tag.E6 GGL,
        mu = (MulAut.conj g0).symm.toMonoidHom.comp
          ((baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))).comp
            ((twistedE6RootGroup K σ).subtype.comp ψ)) ∧
        ∀ (b : ↥Bs) (l : ↥X),
          mu (ggGamma X hBN b l) =
            rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))) * mu l *
            (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))))⁻¹ := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨ι⟩ := CFSG.RankThree.PartOne.CTP.exists_ringEquiv_of_card_eq
    (hK.trans (card_actualQuadraticSubfield hn).symm)
  let fK : K →+* GGL := (actualQuadraticSubfield n).subtype.comp ι.toRingHom
  letI : Algebra K GGL := fK.toAlgebra
  let e : AlgebraicClosure K →+* GGL :=
    (IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := GGL)).toRingHom
  have he : e.comp (algebraMap K (AlgebraicClosure K)) = fK := by
    apply RingHom.ext
    intro c
    exact (IsAlgClosed.lift (R := K) (S := AlgebraicClosure K) (M := GGL)).commutes c
  obtain ⟨Fr, ζ, hζ, g, t, hFr, hζo, hg, hLang, ht, hact⟩ := hκ.actor
  let g0 : ModGL Tag.E6 GGL := baseChangeGL e g
  let ζ0 : GGLˣ := Units.map e.toMonoidHom ζ
  have hζ0 : ζ0 ^ 3 = 1 := by
    change (Units.map e.toMonoidHom ζ) ^ 3 = 1
    rw [← map_pow, hζ, map_one]
  have hζ0o : orderOf ζ0 = 3 :=
    (orderOf_injective (Units.map e.toMonoidHom) (Units.map_injective e.injective) ζ).trans hζo
  let j : ↥X →* ModGL Tag.E6 K := (twistedE6RootGroup K σ).subtype.comp ψ
  let jG : ↥X →* ModGL Tag.E6 GGL :=
    (baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))).comp j
  let mu : ↥X →* ModGL Tag.E6 GGL := (MulAut.conj g0).symm.toMonoidHom.comp jG
  have ht0 (v : Fin Tag.E6.rank → ZMod 3) :
      baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K))) (t v) =
        g0 * rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0 v) * g0⁻¹ := by
    calc
      _ = baseChangeGL e (baseChangeGL (algebraMap K (AlgebraicClosure K)) (t v)) :=
        (baseChangeGL_baseChangeGL (algebraMap K (AlgebraicClosure K)) e (t v)).symm
      _ = baseChangeGL e
          (g * rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ hζ v) * g⁻¹) :=
        congrArg (baseChangeGL e) (ht v)
      _ = _ := by
        rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit]
        have hv : (fun i => Units.map e.toMonoidHom (zetaVec (τ := Tag.E6) ζ hζ v i)) =
            zetaVec (τ := Tag.E6) ζ0 hζ0 v := by
          funext i
          simp only [zetaVec_apply, map_pow]
          rfl
        rw [hv]
  refine ⟨ι, e, g, g0, ζ0, hζ0, he, rfl, hζ0o,
    ⟨Fr, hFr, hg, hLang⟩, mu, rfl, ?_⟩
  intro b l
  have hj : j (ggGamma X hBN b l) =
      t (Multiplicative.toAdd (κ b)) * j l * (t (Multiplicative.toAdd (κ b)))⁻¹ := hact b l
  have hjG : jG (ggGamma X hBN b l) =
      baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))
        (t (Multiplicative.toAdd (κ b))) * jG l *
      (baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))
        (t (Multiplicative.toAdd (κ b))))⁻¹ := by
    change baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))
      (j (ggGamma X hBN b l)) = _
    rw [hj, map_mul, map_mul, map_inv]
    rfl
  change g0⁻¹ * jG (ggGamma X hBN b l) * g0 =
    rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ b))) *
      (g0⁻¹ * jG l * g0) *
      (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ b))))⁻¹
  rw [hjG, ht0]
  group
  rfl


set_option backward.isDefEq.respectTransparency false in
theorem TwE6ToralCoords.exists_original_field_lang_model_square
    {n : ℕ} {G : Type} [Group G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (hψ : Function.Surjective ψ) :
    ∃ (ι : K ≃+* actualQuadraticSubfield n)
      (e : AlgebraicClosure K →+* GGL)
      (g : ModGL Tag.E6 (AlgebraicClosure K))
      (M : GGDatumModel .twistedE6 n 3 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (ζ0 : GGLˣ) (hζ0 : ζ0 ^ 3 = 1),
      e.comp (algebraMap K (AlgebraicClosure K)) =
        (actualQuadraticSubfield n).subtype.comp ι.toRingHom ∧
      M.D.g0 = baseChangeGL e g ∧ M.w = twE6W0 ∧ orderOf ζ0 = 3 ∧
      ∃ mu : ↥X →* ModGL Tag.E6 GGL,
        mu = (MulAut.conj M.D.g0).symm.toMonoidHom.comp
          ((baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))).comp
            ((twistedE6RootGroup K σ).subtype.comp ψ)) ∧
        mu.range = M.D.Γ ∧
        ∀ (b : ↥Bs) (l : ↥X),
          mu (ggGamma X hBN b l) =
            rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))) * mu l *
            (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))))⁻¹ := by
  obtain ⟨ι, e, g, g0, ζ0, hζ0, he, hg0, hζ0o,
    ⟨Fr, hFr, hg, hLang⟩, mu, hmu, hact⟩ :=
      hκ.exists_original_field_actor_square hn hK
  have hFrcomm : e.comp Fr = (ggFrobT n).comp e := by
    ext c
    simp only [RingHom.comp_apply, hFr, ggFrobT_apply, map_pow]
  have hg0mem : g0 ∈ adjointGroup Tag.E6 GGL := by
    rw [hg0]
    exact map_baseChangeGL_adjointGroup_le e (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  have hLang0 : ggPhi .twistedE6 n g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) GGL twE6W0 := by
    change twistHom TwistTag.E6 GGL (ggFrobT n) g0 = _
    rw [hg0, twistHom_baseChangeGL (t := TwistTag.E6) e hFrcomm, hLang, map_mul,
      baseChangeGL_canonicalRep]
  let ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have heps : eps 3 n = -1 :=
    (eps_eq_neg_one_iff Nat.prime_three (by decide) n (Or.inr h3)).2 h3
  have hw : GGWeylLaw .twistedE6 3 n ht twE6W0 := by
    intro u
    change twE6W0 • permLattice (TwistTag.perm .E6) u = _
    rw [heps, piB_twistedE6_of_dvd n h3, neg_one_smul]
    have hpi : (finCongr (rank_eq_langTag n ht)).permCongr
        (1 : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 n).D.rank)) = 1 := by
      rfl
    rw [hpi]
    change twE6W0 • permLattice (TwistTag.perm .E6) u = -u
    rw [CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul]
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨M, hMw, hMg⟩ := G5.ggG5_datum_of_lang ht hw hg0mem hLang0
  let fK : K →+* GGL := e.comp (algebraMap K (AlgebraicClosure K))
  let j : ↥X →* ModGL Tag.E6 GGL :=
    (baseChangeGL fK).comp ((twistedE6RootGroup K σ).subtype.comp ψ)
  have hFrsurj : Function.Surjective (ggFrobT n) := by
    intro y
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (n := 2 ^ n) y
      (pow_pos (by norm_num : (0 : ℕ) < 2) n)
    exact ⟨x, by rw [ggFrobT_apply, hx]⟩
  have hjrange : j.range = graphFixedRootGroup TwistTag.E6 GGL (ggFrobT n) := by
    dsimp only [j]
    rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top, Subgroup.range_subtype]
    exact map_baseChangeGL_graphFixedRootGroup_eq TwistTag.E6 Nat.prime_two hn K hK
      σ.toRingHom hσ fK (ggFrobT_apply n) hFrsurj
  have hΓ : M.D.Γ.map (MulAut.conj M.D.g0).toMonoidHom = j.range := by
    rw [CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.map_conj_Γ M.D,
      (ggLangPkg_twE6_adjoint hn M.D M.hΦ).desc.derived,
      MonoidHom.range_comp, Subgroup.range_subtype, hjrange]
    exact map_baseChangeGL_graphFixedRootGroup_eq TwistTag.E6 Nat.prime_two hn
      (GaloisField 2 (2 * n)) (CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn)
      (CFSG.LieType.Steinberg.Exceptional.frobQ 2 n)
      (CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 n)
      (ggRatEmb (2 * n)) (ggFrobT_apply n) hFrsurj
  have hmuM : mu = (MulAut.conj M.D.g0).symm.toMonoidHom.comp j := by
    rw [hMg]
    exact hmu
  have hcomp : (MulAut.conj M.D.g0).symm.toMonoidHom.comp
      (MulAut.conj M.D.g0).toMonoidHom = MonoidHom.id (ModGL Tag.E6 GGL) := by
    apply MonoidHom.ext
    intro x
    exact (MulAut.conj M.D.g0).symm_apply_apply x
  have hmuRange : mu.range = M.D.Γ := by
    rw [hmuM, MonoidHom.range_comp, ← hΓ, Subgroup.map_map,
      hcomp, Subgroup.map_id]
  exact ⟨ι, e, g, M, ζ0, hζ0, he, hMg.trans hg0, hMw, hζ0o,
    mu, hmuM, hmuRange, hact⟩

set_option backward.isDefEq.respectTransparency false in
theorem TwE6ToralCoords.exists_original_field_lang_residual_square
    {n : ℕ} {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hBN : Bs ≤ Subgroup.normalizer (X : Set G)}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {ψ : ↥X →* ↥(twistedE6RootGroup K σ)}
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)}
    (hκ : TwE6ToralCoords n hBN ψ κ) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center ↥X) (hodd : Odd (Nat.card ψ.ker)) :
    ∃ (ι : K ≃+* actualQuadraticSubfield n)
      (e : AlgebraicClosure K →+* GGL)
      (g : ModGL Tag.E6 (AlgebraicClosure K))
      (M : GGDatumModel .twistedE6 n 3 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (ζ0 : GGLˣ) (hζ0 : ζ0 ^ 3 = 1),
      e.comp (algebraMap K (AlgebraicClosure K)) =
        (actualQuadraticSubfield n).subtype.comp ι.toRingHom ∧
      M.D.g0 = baseChangeGL e g ∧ M.w = twE6W0 ∧ orderOf ζ0 = 3 ∧
      ∃ mu : ↥X →* ModGL Tag.E6 GGL,
        mu = (MulAut.conj M.D.g0).symm.toMonoidHom.comp
          ((baseChangeGL (e.comp (algebraMap K (AlgebraicClosure K)))).comp
            ((twistedE6RootGroup K σ).subtype.comp ψ)) ∧
        mu.range = M.D.Γ ∧
        (∀ (b : ↥Bs) (l : ↥X),
          mu (ggGamma X hBN b l) =
            rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))) * mu l *
            (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
              (Multiplicative.toAdd (κ b))))⁻¹) ∧
        ∀ r : MulAut Bs, ((ggRankOneIn X Bs r).subgroupOf X).map mu =
          ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
            (Set.range fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
              rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
                (Multiplicative.toAdd (κ (b : Bs)))))) := by
  obtain ⟨ι, e, g, M, ζ0, hζ0, he, hMg, hMw, hζ0o, mu, hmu, hμΓ, hact⟩ :=
    hκ.exists_original_field_lang_model_square hn hK h3 hσ hψ
  have hμker : mu.ker = ψ.ker := by
    rw [hmu, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj M.D.g0).symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (baseChangeGL_injective _),
      MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
  have hμc : mu.ker ≤ Subgroup.center ↥X := hμker.symm ▸ hker
  have hμo : Odd (Nat.card mu.ker) := hμker.symm ▸ hodd
  let beta : ↥Bs →* MulAut (ModGL Tag.E6 GGL) :=
    MulAut.conj.comp ((rootDiagHom Tag.E6 GGL).comp
      ((NoOffE6Three.zetaHom ζ0 hζ0).comp κ))
  refine ⟨ι, e, g, M, ζ0, hζ0, he, hMg, hMw, hζ0o, mu, hmu, hμΓ, hact, ?_⟩
  intro r
  have hfixed : (⨅ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)),
      MonoidHom.eqLocus (beta (b : Bs)).toMonoidHom (MonoidHom.id (ModGL Tag.E6 GGL))) =
      Subgroup.centralizer
        (Set.range fun b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)) =>
          rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
            (Multiplicative.toAdd (κ (b : Bs))))) := by
    ext x
    simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_iff, Set.forall_mem_range]
    change (∀ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)), rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
        (Multiplicative.toAdd (κ (b : Bs)))) * x *
        (rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
          (Multiplicative.toAdd (κ (b : Bs)))))⁻¹ = x) ↔
      ∀ b : ↥(MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)), rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
        (Multiplicative.toAdd (κ (b : Bs)))) * x =
        x * rootDiagUnit Tag.E6 (zetaVec (τ := Tag.E6) ζ0 hζ0
          (Multiplicative.toAdd (κ (b : Bs))))
    exact forall_congr' fun b => mul_inv_eq_iff_eq_mul
  have hmap := ggRankOneIn_map_of_central_odd_kernel X Bs hBN mu hμc hμo beta
    (fun b l => hact b l) r
  rw [hμΓ, hfixed] at hmap
  exact hmap

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

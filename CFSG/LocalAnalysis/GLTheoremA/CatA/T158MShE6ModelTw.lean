module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComps
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GF2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_isTE6n_of_catalogIs_shape {X : Type} [Group X]
    (hcat : catalogIs X (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q)) :
    ∃ n : ℕ, 3 ∣ 2 ^ n + 1 ∧ catalogIs X (S10.isTE6n n) := by
  obtain ⟨i, hi, he⟩ := hcat
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating k hk => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie idx =>
    obtain ⟨q, hshape, hidx⟩ := hi
    rw [hidx] at hshape
    obtain ⟨-, hq2, h3q⟩ := hshape
    have hvalid : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by
      rw [← hidx]
      exact idx.2
    refine ⟨q.exponent, ?_, .lie idx, ?_, he⟩
    · rwa [TauCeti.PrimePower.card_def, hq2] at h3q
    · rw [show idx = ⟨.twistedE6 q, hvalid⟩ from Subtype.ext hidx]
      exact ⟨hq2, rfl⟩

theorem twE6Marking_of_innerDiagMarking_of_isTE6n
    {G : Type} [Group G] [Finite G] {L H : Subgroup G} {n : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hid : InnerDiagMarking H L) (hcat : catalogIs (PSimple 3 L) (S10.isTE6n n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ Nat.card K = (2 ^ n) ^ 2 ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.StandardType.TwE6Delta.RecipeR K n,
        ∀ a ∈ H, ∃ φ ∈ CFSG.StandardType.TwE6Delta.RecipeI K n,
          LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  obtain ⟨-, lab, hlab, hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel hid
  obtain ⟨R, _, I, F, -, -, θ, -, hM⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨idx, hvalid, hP, ⟨e0⟩⟩ := CatB.exists_lieIndex hcat
  cases idx with
  | twistedE6 q =>
    obtain ⟨-, hqn⟩ := hP
    haveI hsimpleCat : IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hvalid⟩) :=
      (finite_isSimpleGroup_cat_twistedE6 hvalid).2
    haveI : IsSimpleGroup (PSimple 3 L) := e0.isSimpleGroup
    have hn : 1 ≤ n := hqn ▸ q.exponent_pos
    obtain ⟨eP⟩ := HSubT.psimple_nonempty_equiv_quotCenter 3 L hqs inferInstance
    have hcatZ : catalogIs (↥L ⧸ Subgroup.center ↥L) (S10.isTE6n n) := (catalogIs_congr eP).mp hcat
    have hMZ : CFSG.StandardType.MarkedModel lab (↥L ⧸ Subgroup.center ↥L) :=
      CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hM
    have hLieZ : LieModel (↥L ⧸ Subgroup.center ↥L) .twistedE6 0 2 n := T263.lieModel_twE6_of_catalogIs hcatZ
    have hdeterm : lab.tag = .twE6 ∧ lab.n = n := by
      by_cases h2 : CFSG.StandardType.markChar lab = 2
      · exact CFSG.StandardType.NbrInnerMore.eq_of_markedModel_twE6 hn hLieZ hlab h2 hMZ
      · exfalso
        have hodd : OddLieType (↥L ⧸ Subgroup.center ↥L) := by
          obtain ⟨tag, rank, m⟩ := lab
          cases tag <;> simp [CFSG.StandardType.markChar] at h2
          all_goals first
            | exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
                CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
                  (show LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2 from hMZ),
                (show LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2 from hMZ)⟩
            | exact ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num,
                CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
                  (show LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1 from hMZ),
                (show LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1 from hMZ)⟩
        exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hLieZ
          (by decide) (by simp) (by simp) (by simp) hodd
    obtain ⟨tag_l, rank_l, n_l⟩ := lab
    obtain ⟨htag, hnlab⟩ := hdeterm
    subst htag
    subst hnlab
    have hrecipe := hraw
    dsimp only [LargeEvenRawDatum] at hrecipe
    dsimp only [LargeEvenRecipeTwisted] at hrecipe
    obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hrecipe
    obtain ⟨-, -, ⟨θ', hP', -⟩⟩ := hQ
    obtain ⟨-, hBI⟩ := hP'
    exact ⟨K, hKfield, hKfinite, hn, hKcard, θ', hBI⟩
  | _ => exact hP.elim

theorem twE6Marking_of_innerDiagMarking
    {G : Type} [Group G] [Finite G] {L H : Subgroup G} (hqs : CFSG.Open.IsQuasisimple ↥L)
    (hid : InnerDiagMarking H L)
    (hcat : catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q)) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ 3 ∣ 2 ^ n + 1 ∧
      Nat.card K = (2 ^ n) ^ 2 ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.StandardType.TwE6Delta.RecipeR K n,
        ∀ a ∈ H, ∃ φ ∈ CFSG.StandardType.TwE6Delta.RecipeI K n,
          LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ := by
  obtain ⟨n, h3, hcatn⟩ := exists_isTE6n_of_catalogIs_shape hcat
  obtain ⟨K, hKfield, hKfinite, hn, hK, θ, hθ⟩ := twE6Marking_of_innerDiagMarking_of_isTE6n hqs hid hcatn
  exact ⟨n, K, hKfield, hKfinite, hn, h3, hK, θ, hθ⟩

theorem t158E6ModelData_tw_of_marking
    {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} (hP : PreSetup 3 L J A d b)
    {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) (hK : Nat.card K = (2 ^ n) ^ 2)
    (θ' : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.StandardType.TwE6Delta.RecipeR K n)
    (hId : ∃ φ ∈ CFSG.StandardType.TwE6Delta.RecipeI K n,
      LargeEvenInduces θ' (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) φ)
    (hIb : ∃ φ ∈ CFSG.StandardType.TwE6Delta.RecipeI K n,
      LargeEvenInduces θ' (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C) (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) (β φ : MulAut C)
      (Lf : Type) (_ : Field Lf) (_ : IsAlgClosed Lf) (_ : CharP Lf 2) (S : LangSetup Tag.E6 Lf 5)
      (a : Fin Tag.E6.rank → Lfˣ) (ι : C →* ModGL Tag.E6 Lf) (y : ModGL Tag.E6 Lf),
      Subgroup.center C = ⊥ ∧
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β ∧
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ ∧
      E6ShapeSetup S ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c, ι (φ c) = y * ι c * y⁻¹) ∧
      y ∈ toralCentralizer Tag.E6 Lf a ∧ S.D.step y = y ∧
      (rootDiagUnit Tag.E6 a ∉ S.Γ → β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C) ∧
      S.D.q = 2 ^ n := by
  classical
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hP.norm hP.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hP.norm hP.b_mem
  obtain ⟨σ, hσ, ε, hε⟩ := CFSG.StandardType.TwE6Transport.exists_recipeConj (K := K) hn hK
  have hle := CFSG.StandardType.NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ
  set θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(twistedE6RootGroup K σ) := θ'.trans ε.symm with hθ
  have hind : ∀ (g : G) (φ : MulAut (CFSG.StandardType.TwE6Delta.RecipeR K n)),
      φ ∈ CFSG.StandardType.TwE6Delta.RecipeI K n →
      LargeEvenInduces θ' (fun l l' : ↥L => (l' : G) = g⁻¹ * (l : G) * g) φ →
      ∃ w : ↥(twistedE6InndiagGL K σ),
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = g⁻¹ * (l : G) * g)
          (twistedE6InndiagConj K σ w) := by
    intro g φ hφI hφ
    obtain ⟨w, rfl⟩ := (hε φ).2 hφI
    refine ⟨⟨w, hle w.2⟩, fun l l' hl => ?_⟩
    have h1 := hφ l l' hl
    rw [CFSG.StandardType.TwE6Transport.recipeConj_apply] at h1
    have h2 : twistedE6InndiagConj K σ ⟨w, hle w.2⟩ = CFSG.StandardType.RecipeExcLang.twConj K σ w :=
      MulEquiv.ext fun c => Subtype.ext (by
        rw [twistedE6InndiagConj_apply, CFSG.StandardType.RecipeExcLang.coe_twConj])
    rw [hθ, MulEquiv.trans_apply, MulEquiv.trans_apply, h2, ← h1, MulEquiv.symm_apply_apply]
  obtain ⟨φd, hφdI, hφd⟩ := hId
  obtain ⟨φb, hφbI, hφb⟩ := hIb
  obtain ⟨h, hβind⟩ := hind d φd hφdI hφd
  obtain ⟨h', hφind⟩ := hind b φb hφbI hφb
  have hinjc := twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ
  have hβ3 : (twistedE6InndiagConj K σ h) ^ 3 = 1 :=
    T171Sh.largeEvenInduces_pow_eq_one hdN hβind (hP.elem.2 d hP.d_mem)
  have hh3 : h ^ 3 = 1 := hinjc (by rw [map_pow, hβ3, map_one])
  have hh1 : h ≠ 1 := by
    intro h1
    have hβ1 : LargeEvenInduces θ (T171Sh.conjRel d) (1 : MulAut ↥(twistedE6RootGroup K σ)) := by
      have h2 := hβind
      rw [h1, map_one] at h2
      exact h2
    have hcent : d ∈ Subgroup.centralizer (L : Set G) :=
      T171Sh.centralizes_of_conjRel_center hdN
        (T171Sh.exists_center_of_largeEvenInduces_one hdN hβ1) ⟨hP.qs.1⟩
    have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hP.d_mem, hcent⟩
    rw [hP.faithful] at hmem
    exact hP.d_ne (Subgroup.mem_bot.mp hmem)
  have hdb : d * b = b * d := isElemAbelian_commute hP.elem hP.d_mem hP.b_mem
  have hhh' : h * h' = h' * h := by
    have e1 := T171Sh.largeEvenInduces_mul hdN hbN hdb hβind hφind
    have e2 := T171Sh.largeEvenInduces_mul hbN hdN hdb.symm hφind hβind
    rw [← hdb] at e2
    have huniq := T171Sh.largeEvenInduces_unique e1 e2
      (T171Sh.conjRel_total (Subgroup.mul_mem _ hdN hbN))
    exact hinjc (by rw [map_mul, map_mul]; exact huniq)
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
      (by norm_num)
  have hh3' : (h : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3]
    rfl
  have hh1' : (h : ModGL TwistTag.E6.tag K) ≠ 1 := fun h1 => hh1 (Subtype.ext h1)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr, hΦ⟩, hT, hap, h1, hinj, hrange, hβι, hga, hgι⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight.exists_langSetup_conj_of_inndiag_twE6_iota
      Nat.prime_two hn hK σ hσ Nat.prime_three (by norm_num) (p₀ := 5) (by norm_num) (by norm_num)
      (Or.inl le_rfl) hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (fun c => twistedE6InndiagConj_apply h c) hh3' hh1'
  obtain ⟨bc, hbc⟩ : ∃ bc : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 (AlgebraicClosure K),
      ∀ x, bc x = baseChangeGL (algebraMap K (AlgebraicClosure K)) x :=
    ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)), fun x => rfl⟩
  rw [← hbc] at hga
  have hda : rootDiagUnit Tag.E6 a = S.D.g0⁻¹ * bc (h : ModGL TwistTag.E6.tag K) * S.D.g0 := by
    rw [← hga]
    group
  have hιc : ∀ c : ↥(twistedE6RootGroup K σ),
      ι c = S.D.g0⁻¹ * bc (c : ModGL TwistTag.E6.tag K) * S.D.g0 := by
    intro c
    have h2 := hgι c
    rw [← hbc] at h2
    rw [← h2]
    group
  set y : ModGL Tag.E6 (AlgebraicClosure K) :=
    S.D.g0⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * S.D.g0 with hy
  have hφι : ∀ c, ι (twistedE6InndiagConj K σ h' c) = y * ι c * y⁻¹ := by
    intro c
    rw [hιc, hιc, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv, hy]
    group
  have hvF : bc (h' : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
    rw [hbc]
    exact map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ Fr hFr
      ⟨h', h'.2, rfl⟩
  have hΦv : S.D.Φ (bc (h' : ModGL TwistTag.E6.tag K)) = bc (h' : ModGL TwistTag.E6.tag K) := by
    rw [hΦ]
    exact hvF.2
  have hyF : S.D.step y = y := by
    rw [hy]
    change (MulAut.conj S.D.n) (S.D.Φ (S.D.g0⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * S.D.g0)) =
      S.D.g0⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * S.D.g0
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hΦv, S.D.lang]
    group
  have hyG : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    mul_mem (mul_mem (inv_mem S.D.g0_mem) hvF.1) S.D.g0_mem
  have hbcc : bc (h : ModGL TwistTag.E6.tag K) * bc (h' : ModGL TwistTag.E6.tag K) =
      bc (h' : ModGL TwistTag.E6.tag K) * bc (h : ModGL TwistTag.E6.tag K) := by
    rw [← map_mul, ← map_mul]
    exact congrArg bc (congrArg Subtype.val hhh')
  have hyd : rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹ = y := by
    rw [hy, hda]
    calc S.D.g0⁻¹ * bc (h : ModGL TwistTag.E6.tag K) * S.D.g0 *
          (S.D.g0⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * S.D.g0) *
          (S.D.g0⁻¹ * bc (h : ModGL TwistTag.E6.tag K) * S.D.g0)⁻¹ =
        S.D.g0⁻¹ * (bc (h : ModGL TwistTag.E6.tag K) * bc (h' : ModGL TwistTag.E6.tag K)) *
          (bc (h : ModGL TwistTag.E6.tag K))⁻¹ * S.D.g0 := by group
      _ = S.D.g0⁻¹ * (bc (h' : ModGL TwistTag.E6.tag K) * bc (h : ModGL TwistTag.E6.tag K)) *
          (bc (h : ModGL TwistTag.E6.tag K))⁻¹ * S.D.g0 := by rw [hbcc]
      _ = S.D.g0⁻¹ * bc (h' : ModGL TwistTag.E6.tag K) * S.D.g0 := by group
  have hyC : y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a :=
    mem_toralCentralizer.2 ⟨hyG, hyd⟩
  have hshape : E6ShapeSetup S :=
    ⟨Fr, fun c => by rw [hSq]; exact hFr c, Or.inr ⟨hΦ, by rw [hSq]; exact h3⟩⟩
  have hlast : rootDiagUnit Tag.E6 a ∉ S.Γ →
      twistedE6InndiagConj K σ h ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(twistedE6RootGroup K σ) := by
    intro hnot hinner
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hinner
    have hcmem : (c : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ := Subgroup.mem_sup_left c.2
    have hcc : twistedE6InndiagConj K σ ⟨c, hcmem⟩ = MulAut.conj c :=
      MulEquiv.ext fun x => Subtype.ext (by
        rw [twistedE6InndiagConj_apply, MulAut.conj_apply]
        rfl)
    have hceq : (⟨c, hcmem⟩ : ↥(twistedE6InndiagGL K σ)) = h := hinjc (hcc.trans hc)
    have hhc : (h : ModGL TwistTag.E6.tag K) = (c : ModGL TwistTag.E6.tag K) := by
      rw [← hceq]
    apply hnot
    rw [hda, hhc, ← hιc c, ← hrange]
    exact MonoidHom.mem_range.2 ⟨c, rfl⟩
  exact ⟨↥(twistedE6RootGroup K σ), inferInstance, inferInstance, θ, twistedE6InndiagConj K σ h,
    twistedE6InndiagConj K σ h', AlgebraicClosure K, inferInstance, inferInstance, inferInstance, S,
    a, ι, y, center_graphFixedRootGroup_eq_bot σ.surjective, hβind, hφind, hshape, hT, hap, h1,
    hinj, hrange, hβι, hφι, hyC, hyF, hlast, hSq⟩

theorem t158E6ModelData_tw_of_isTE6n
    {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {n : ℕ} (hP : PreSetup 3 L J A d b)
    (hcat : catalogIs (PSimple 3 L) (S10.isTE6n n)) (hodd : Odd n) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C) (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) (β φ : MulAut C)
      (Lf : Type) (_ : Field Lf) (_ : IsAlgClosed Lf) (_ : CharP Lf 2) (S : LangSetup Tag.E6 Lf 5)
      (a : Fin Tag.E6.rank → Lfˣ) (ι : C →* ModGL Tag.E6 Lf) (y : ModGL Tag.E6 Lf),
      Subgroup.center C = ⊥ ∧
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β ∧
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ ∧
      E6ShapeSetup S ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      (∀ c, ι (φ c) = y * ι c * y⁻¹) ∧
      y ∈ toralCentralizer Tag.E6 Lf a ∧ S.D.step y = y ∧
      (rootDiagUnit Tag.E6 a ∉ S.Γ → β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C) ∧
      S.D.q = 2 ^ n := by
  obtain ⟨K, _, _, hn, hK, θ', hI⟩ := twE6Marking_of_innerDiagMarking_of_isTE6n hP.qs hP.idiag₂ hcat
  have h3 : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨j, rfl⟩ := hodd
    rw [pow_succ, pow_mul]
    have h4 : (2 ^ 2) ^ j % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  exact t158E6ModelData_tw_of_marking hP hn h3 hK θ'
    (hI d (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)))
    (hI b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))

theorem t158E6ModelData_tw
    {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G}
    (hP : PreSetup 3 L J A d b)
    (hcat : catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q)) :
    T158E6ModelData L J A d b := by
  obtain ⟨n, K, _, _, hn, h3, hK, θ', hI⟩ := twE6Marking_of_innerDiagMarking hP.qs hP.idiag₂ hcat
  obtain ⟨C, i₁, i₂, θ, β, φ, Lf, i₃, i₄, i₅, S, a, ι, y, hZ, hβind, hφind, hshape, hT, hap, h1, hinj,
      hrange, hβι, hφι, hyC, hyF, hlast, -⟩ :=
    t158E6ModelData_tw_of_marking hP hn h3 hK θ' (hI d (Subgroup.mem_sup_left (Subgroup.mem_zpowers d)))
      (hI b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
  exact ⟨C, i₁, i₂, θ, β, φ, Lf, i₃, i₄, i₅, S, a, ι, y, hZ, hβind, hφind, hshape, hT, hap, h1, hinj,
    hrange, hβι, hφι, hyC, hyF, hlast⟩

end CFSG.LocalAnalysis.GLTheoremA.T158

end

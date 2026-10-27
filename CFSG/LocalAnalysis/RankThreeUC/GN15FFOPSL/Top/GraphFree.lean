module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.Select
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Dimension
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.LabelBounds
public import CFSG.LieType.SpecialLinear.Stage.ModelBounds
public import CFSG.LieType.SpecialLinear.TypeLabel.EndPeriod
public import CFSG.LieType.SpecialLinear.TypeLabel.Rotation
public import CFSG.LieType.SpecialLinear.TypeLabel.StagePeriod
public import CFSG.LieType.SpecialLinear.SLModel.Recognition
public import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoTauLinAlg
public import CFSG.LieType.SpecialLinear.TypeLabel.Scalar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Matrix Module Representation
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear.SLModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.Quasithin.SmithCurtis
open scoped MonoidAlgebra TensorProduct

theorem topActor_compat0 {n : ℕ} {F : Type} [Field F]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin n) F) W)
    (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hcompatW : ∀ d ∈ D, ∃ A : GL (Fin n) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g w, ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g w) =
        ρ (borelStd n F A τ 0 g) (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w))
    (d : ↥D) :
    ∃ A : GL (Fin n) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, topActor ρ D d (endFieldRep ρ g x) =
        endFieldRep ρ (borelStd n F A τ 0 g) (topActor ρ D d x) := by
  obtain ⟨A, hA, τ, h⟩ := hcompatW d d.2
  refine ⟨A, hA, τ, fun g x => ?_⟩
  change ρ.asModuleEquiv.symm
      (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g (ρ.asModuleEquiv x))) =
    ρ.asModuleEquiv.symm
      (ρ (borelStd n F A τ 0 g)
        (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ.asModuleEquiv x)))
  rw [h g (ρ.asModuleEquiv x)]

theorem graphPart_eq_one_of_compat0 {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (n + 1)) F) W)
    (hker : ∀ g, ρ g = 1 → g ∈ LinearFlag.scalars (n + 1) F)
    (hn : 3 ≤ n + 1)
    (D : Subgroup (W ≃ₗ[ZMod 2] W))
    (hD : D ≤ CFSG.LieType.SpecialLinear.rangeNormalizer (repUnits ρ))
    (hD2W : ∀ d ∈ D, d * d = 1)
    (hcompat : ∀ d ∈ D, ∃ B : GL (Fin (n + 1)) F, IsUpperGL B ∧ ∃ τ : F ≃+* F,
      ∀ g w, ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g w) =
        ρ (borelStd (n + 1) F B τ 0 g)
          (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w))
    (d : ↥D) :
    CFSG.LieType.SpecialLinear.graphPart (repUnits ρ)
      (repUnits_ker_le_scalars ρ hker) hn ⟨d, hD d.2⟩ = 1 := by
  classical
  obtain ⟨B, hB, τ, hτ⟩ := hcompat d d.2
  let hd : CFSG.LieType.SpecialLinear.rangeNormalizer (repUnits ρ) := ⟨d, hD d.2⟩
  have hd_inv : ((d : W ≃ₗ[ZMod 2] W))⁻¹ = (d : W ≃ₗ[ZMod 2] W) :=
    inv_eq_of_mul_eq_one_right (hD2W d d.2)
  have hlift : CFSG.LieType.SpecialLinear.liftAut (repUnits ρ)
      (repUnits_ker_le_scalars ρ hker) hn hd =
        CFSG.QuasithinUnique.K1.stdAut B τ 0 := by
    apply CFSG.LieType.SpecialLinear.eq_of_comp_proj_eq
      (π := repUnits ρ) (repUnits_ker_le_scalars ρ hker) hn
    intro g
    rw [CFSG.LieType.SpecialLinear.liftAut_spec]
    apply LinearEquiv.ext
    intro w
    rw [show (((hd : W ≃ₗ[ZMod 2] W)) * repUnits ρ g *
          ((hd : W ≃ₗ[ZMod 2] W))⁻¹) w =
        ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (ρ g
          (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w)) by
      simp [hd, repUnits_apply, hd_inv]]
    have hdd : ((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
        (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w) = w := by
      have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) (hD2W d d.2)
      simpa using h
    rw [hτ g (((d : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) w), hdd, repUnits_apply,
      borelStd_zero]
  have hstd : CFSG.QuasithinUnique.K1.stdAut
        (CFSG.LieType.SpecialLinear.stdData (repUnits ρ)
          (repUnits_ker_le_scalars ρ hker) hn hd).1
        (CFSG.LieType.SpecialLinear.stdData (repUnits ρ)
          (repUnits_ker_le_scalars ρ hker) hn hd).2.1
        (CFSG.LieType.SpecialLinear.stdData (repUnits ρ)
          (repUnits_ker_le_scalars ρ hker) hn hd).2.2 =
      CFSG.QuasithinUnique.K1.stdAut B τ 0 := by
    rw [← CFSG.LieType.SpecialLinear.liftAut_eq_stdAut, hlift]
  have heps := (CFSG.LieType.SpecialLinear.stdAut_field_graph_unique hn
    (CFSG.LieType.SpecialLinear.stdData_eps_le_one (repUnits ρ)
      (repUnits_ker_le_scalars ρ hker) hn hd) (by norm_num) hstd).2
  change Multiplicative.ofAdd
    ((CFSG.LieType.SpecialLinear.stdData (repUnits ρ)
      (repUnits_ker_le_scalars ρ hker) hn hd).2.2 : ZMod 2) = 1
  rw [heps]
  rfl

theorem odd_orderOf_of_mem_centralizer_repUnits {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin m) K) W)
    (hirr : ρ.IsIrreducible) {c : W ≃ₗ[ZMod 2] W}
    (hc : c ∈ Subgroup.centralizer ((repUnits ρ).range : Set (W ≃ₗ[ZMod 2] W))) :
    Odd (orderOf c) := by
  classical
  have htwo : ∀ x : W ≃ₗ[ZMod 2] W,
      x ∈ Subgroup.centralizer ((repUnits ρ).range : Set (W ≃ₗ[ZMod 2] W)) →
      x * x = 1 → x = 1 := by
    intro x hxmem hx2
    by_contra hxne
    let L : W →ₗ[ZMod 2] W := (x : W →ₗ[ZMod 2] W) - 1
    have hx_apply : ∀ v : W, x (x v) = v := by
      intro v
      have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e v) hx2
      simpa using h
    have hLne : L ≠ 0 := by
      intro h0
      apply hxne
      ext v
      have h := congrArg (fun f : W →ₗ[ZMod 2] W => f v) h0
      exact sub_eq_zero.mp (by simpa [L] using h)
    have hker_inv : ∀ g : Matrix.SpecialLinearGroup (Fin m) K,
        ∀ z ∈ LinearMap.ker L, ρ g z ∈ LinearMap.ker L := by
      intro g z hz
      have hz' : x z - z = 0 := by simpa [L] using hz
      have hcomm : x (ρ g z) = ρ g (x z) := by
        have hc' := (Subgroup.mem_centralizer_iff.mp hxmem) (repUnits ρ g)
          (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
        have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e z) hc'
        simpa [repUnits_apply] using h.symm
      rw [LinearMap.mem_ker]
      change x (ρ g z) - ρ g z = 0
      rw [hcomm, ← map_sub, hz', map_zero]
    have hL2 : ∀ v : W, L (L v) = 0 := by
      intro v
      change x (x v - v) - (x v - v) = 0
      exact CFSG.RankThree.GF2n.Tim79.QuadModel.sub_sub_eq_zero_of_invol
        (K := ZMod 2) hx_apply v
    obtain ⟨v, hv⟩ : ∃ v : W, L v ≠ 0 := by
      by_contra h
      apply hLne
      ext v
      simpa using not_exists.mp h v
    have hker_ne : LinearMap.ker L ≠ ⊥ := by
      intro hbot
      have hmem : L v ∈ LinearMap.ker L := by
        rw [LinearMap.mem_ker]
        exact hL2 v
      rw [hbot] at hmem
      exact hv (by simpa using hmem)
    let S : Subrepresentation ρ := ⟨LinearMap.ker L, hker_inv⟩
    rcases hirr.eq_bot_or_eq_top S with h | h
    · apply hker_ne
      exact congrArg Subrepresentation.toSubmodule h
    · apply hLne
      ext v
      have hvS : v ∈ S.toSubmodule := by
        rw [congrArg Subrepresentation.toSubmodule h]
        trivial
      have hvker : v ∈ LinearMap.ker L := hvS
      simpa [L] using hvker
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hdvd : 2 ∣ orderOf c := even_iff_two_dvd.mp hodd
  let x : W ≃ₗ[ZMod 2] W := c ^ (orderOf c / 2)
  have hxord : orderOf x = 2 := by
    dsimp only [x]
    exact orderOf_pow_orderOf_div (orderOf_pos c).ne' hdvd
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hxord] at h
    simpa [pow_two] using h
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    omega
  exact hx1 (htwo x ((Subgroup.centralizer _).pow_mem hc _) hx2)


private theorem card_active_eq_one_of_forall_eq_empty {f n : ℕ} {ε : Fin f → Finset (Fin n)}
    {i₀ : Fin f} (hne : ε i₀ ≠ ∅) (h : ∀ i, i ≠ i₀ → ε i = ∅) :
    (Finset.univ.filter fun i => ε i ≠ ∅).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨i₀, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    by_contra hne'
    exact hi (h i hne')
  · rintro rfl
    exact hne

theorem graph_free_false {n f r : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2 ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ n + 1)
    (hrq : r ∣ 2 ^ f - 1)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin (n + 1)) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1)
    (hker : ∀ g, ρ g = 1 → g ∈ LinearFlag.scalars (n + 1) K)
    (hscal : ∀ (c : Kˣ) (hc : c ^ (n + 1) = 1), c ^ r = 1 →
      ρ (LinearFlag.scalarElement c hc) = 1)
    (D : Subgroup (W ≃ₗ[ZMod 2] W)) (hD1 : D ≠ ⊥) (hDel : CFSG.IsElementaryAbelian 2 ↥D)
    (hquad : ∀ a ∈ D, ∀ b ∈ D, ∀ w, b (a w - w) = a w - w)
    (hcomm : ∀ d ∈ D, ∀ f : W →ₗ[ZMod 2] W, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) →
      (d : W →ₗ[ZMod 2] W) ∘ₗ f = f ∘ₗ (d : W →ₗ[ZMod 2] W))
    (hcompat : ∀ d ∈ D, ∃ B : GL (Fin (n + 1)) K, IsUpperGL B ∧ ∃ τ : K ≃+* K, ∀ g w,
      d (ρ g w) = ρ (borelStd (n + 1) K B τ 0 g) (d w))
    (hoff : Nat.card W ≤ Nat.card ↥D * Nat.card {w : W // ∀ d ∈ D, d w = w})
    (hbest : ∀ B : Subgroup (W ≃ₗ[ZMod 2] W), B ≤ D →
      Nat.card ↥B * Nat.card {w : W // ∀ b ∈ B, b w = w} ≤
        Nat.card ↥D * Nat.card {w : W // ∀ d ∈ D, d w = w})
    (hered : ∀ Z : Submodule (ZMod 2) W,
      (∀ d : ↥D, ∀ z ∈ Z, (d : W ≃ₗ[ZMod 2] W) z ∈ Z) → IsOffenderOn (tautRep D) ⊤ Z) :
    False := by
  classical
  let E := End (ZMod 2)[Matrix.SpecialLinearGroup (Fin (n + 1)) K] ρ.asModule
  let k := AlgebraicClosure E
  exact
    letI : Algebra K k :=
      (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
        (K := E) (F₀ := K) (p := 2)).some.toAlgebra
    letI : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
    (by
  obtain ⟨s, hs_pos, hE⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow
      (ρ := ρ)
  obtain ⟨y, χ, J, ht, s₀, hs₀⟩ := top_exists_type (n := n) ρ hne
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (endFieldRep ρ)) :=
    top_isSimpleRep (n := n) ρ
  obtain ⟨ε, hε0, hεχ, hεJ, β, hβ⟩ :=
    CFSG.LieType.SpecialLinear.SLModel.exists_iso_slModelRep (m := n) (f := f)
      (hF := hK)
      (ρ := CFSG.Theory.Representation.extendScalars k (endFieldRep ρ)) hsimp ht
  have htε : ∃ i, ε i ≠ ∅ := by
    by_contra h
    push Not at h
    exact hs₀ ((hεJ s₀).mpr fun r => by rw [h r]; simp)
  let d := Module.finrank E ρ.asModule
  have hdBeta : Module.finrank k (BModel k ε) = d := by
    rw [← β.finrank_eq]
    exact CFSG.HardMathSupport.GuralnickMalle.finrank_tensorProduct_asModule (ρ := ρ) k
  have hd_bound : (∏ i ∈ Finset.univ.filter (fun i => ε i ≠ ∅), orbitSize (ε i)) ≤ d := by
    have h := CFSG.LieType.SpecialLinear.ExteriorModel.prod_orbitSize_le_finrank
      (k := k) (n := n + 1) (τ := Fin f) ε
    rwa [hdBeta] at h
  have hextra_bound : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) →
      (ε i₀ = {⟨1, by omega⟩, ⟨2, by omega⟩} ∨
        ε i₀ = {⟨n - 1, by omega⟩, ⟨n, by omega⟩}) →
      (n + 1) * n + (n + 1).choose 3 ≤ d := by
    intro i₀ hε' hset
    rcases hset with hset | hset
    · have h := CFSG.LieType.SpecialLinear.ExteriorModel.add_choose_le_finrank_of_one_two
        (k := k) (n := n + 1) (by omega) ε i₀ hset hε'
      rwa [hdBeta] at h
    · have h := CFSG.LieType.SpecialLinear.ExteriorModel.add_choose_le_finrank_of_last_two
        (k := k) (n := n + 1) (by omega) ε i₀ hset hε'
      rwa [hdBeta] at h
  have hscal_bound : r ∣ ∑ i : Fin f, 2 ^ (i : ℕ) * ∑ j ∈ ε i, (j : ℕ) := by
    obtain ⟨c, hcord, hc1⟩ :=
      CFSG.LieType.SpecialLinear.exists_orderOf_eq_of_dvd (m := n) (F := K) (f := f) (r := r)
        (by rwa [Nat.card_eq_fintype_card]) hrn hrq
    have hcr : c ^ r = 1 := by rw [← hcord, pow_orderOf_eq_one]
    have hscal_ext : CFSG.Theory.Representation.extendScalars k (endFieldRep ρ)
        (LinearFlag.scalarElement c hc1) = 1 :=
      (CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
        (ρ := ρ) (k := k) (LinearFlag.scalarElement c hc1)).mpr (hscal c hc1 hcr)
    have hdvd := CFSG.LieType.SpecialLinear.orderOf_dvd_of_isCoverType_scalar
      (m := n) (F := K) (k := k) ht hεχ hc1 hscal_ext
    rwa [hcord] at hdvd
  have hs_bound : f ≤ s * (Finset.univ.filter fun i => ε i ≠ ∅).card :=
    CFSG.LieType.SpecialLinear.le_mul_card_active_of_isCoverType_endField (m := n) (f := f)
      (W := W) (ρ := ρ) (by rwa [Nat.card_eq_fintype_card]) hE k ht hε0 hεχ htε
  have hD2W : ∀ d ∈ D, d * d = 1 := by
    intro d hd
    have h := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := D) d hd
    simpa [pow_two] using h
  have hodd : ∀ c ∈ Subgroup.centralizer ((repUnits ρ).range :
      Set (W ≃ₗ[ZMod 2] W)), Odd (orderOf c) :=
    fun c hc => odd_orderOf_of_mem_centralizer_repUnits ρ hirr hc
  have hhint : ∀ a ∈ D, ∀ x : Matrix.SpecialLinearGroup (Fin (n + 1)) K,
      ∃ y, ∀ w, a (ρ x w) = ρ y (a w) := by
    intro a ha x
    obtain ⟨B, hB, τ, hτ⟩ := hcompat a ha
    exact ⟨borelStd (n + 1) K B τ 0 x, fun w => hτ x w⟩
  have hDN : D ≤ CFSG.LieType.SpecialLinear.rangeNormalizer (repUnits ρ) :=
    le_rangeNormalizer_repUnits ρ hhint
  have hgraph : ∀ d (hd : d ∈ D),
      CFSG.LieType.SpecialLinear.graphPart (repUnits ρ)
        (repUnits_ker_le_scalars ρ hker) (by omega : 3 ≤ n + 1) ⟨d, hDN hd⟩ = 1 :=
    fun d hd => graphPart_eq_one_of_compat0 ρ hker (by omega) D hDN hD2W hcompat ⟨d, hd⟩
  have h2 : Nat.card ↥D ≤ 2 * Nat.card ↥(D ⊓ (repUnits ρ).range) :=
    CFSG.LieType.SpecialLinear.card_le_two_mul_card_inf_of_graphPart_eq_one
      (π := repUnits ρ) (repUnits_ker_le_scalars ρ hker) (by omega) hodd D hDN hD2W hgraph
  have hR : ∀ g, ∃ r ∈ (repUnits ρ).range, ∀ w, r w = ρ g w := by
    intro g
    exact ⟨repUnits ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩,
      fun w => repUnits_apply ρ g w⟩
  have hR' : ∀ r ∈ (repUnits ρ).range, ∃ g, ∀ w, r w = ρ g w := by
    intro r hr
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hr
    exact ⟨g, fun w => by rw [← hg]; exact repUnits_apply ρ g w⟩
  have hdim_bound : s * d < f * (n + 1) ^ 2 :=
    mul_finrank_lt_of_best (m := n + 1) (by omega) (K := K) (f := f) hK ρ hirr
      ((repUnits ρ).range) hR hR' D hDN h2 hD1 hbest hoff hE
  have hne_top : ∃ g : Matrix.SpecialLinearGroup (Fin (n + 1)) K,
      endFieldRep ρ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hne
    refine ⟨g, fun h => hg ?_⟩
    have hext : CFSG.Theory.Representation.extendScalars k (endFieldRep ρ) g = 1 := by
      rw [CFSG.Theory.Representation.extendScalars_apply, h, LinearMap.baseChange_one]
    exact (CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
      (ρ := ρ) (k := k) g).mp hext
  have htop_one : ∀ d : ↥D, topActor ρ D d = 1 → d = 1 := by
    intro d h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h' : topActor ρ D d (ρ.asModuleEquiv.symm w) = ρ.asModuleEquiv.symm w := by
      rw [h]; rfl
    have := congrArg (fun x => ρ.asModuleEquiv x) h'
    simpa [topActor_apply, transportEnd_apply] using this
  have hD1top : ∃ d : ↥D, topActor ρ D d ≠ 1 := by
    obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    exact ⟨d, fun h => hd (htop_one d h)⟩
  have hδE : ∀ d (c : E) (x : ρ.asModule), topActor ρ D d (c • x) = c • topActor ρ D d x :=
    fun d c x => topActor_smul ρ D hcomm d c x
  have hD2top : ∀ d : ↥D, topActor ρ D d * topActor ρ D d = 1 :=
    topActor_mul_self ρ D hD2W
  have hquadtop : ∀ a b : ↥D, ∀ x : ρ.asModule,
      topActor ρ D b (topActor ρ D a x - x) = topActor ρ D a x - x :=
    topActor_quadratic ρ D hquad
  have hofftop : IsOffenderOn (topActor ρ D) ⊤ ⊤ :=
    topActor_isOffenderOn ρ D (tautRep D) (fun d w => rfl) hD2W hered ⊤
      (fun _ _ _ => Submodule.mem_top)
  have hcompatTop : ∀ d : ↥D, ∃ A : GL (Fin (n + 1)) K, IsUpperGL A ∧ ∃ τ : K ≃+* K,
      ∀ g x, topActor ρ D d (endFieldRep ρ g x) =
        endFieldRep ρ (borelStd (n + 1) K A τ 0 g) (topActor ρ D d x) :=
    fun d => topActor_compat0 ρ D hcompat d
  have hE' : Fintype.card E = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  have hnat_bound : (Finset.univ.filter fun i => ε i ≠ ∅).card = 2 →
      (∀ i, ε i ≠ ∅ → ε i = {⟨1, by omega⟩} ∨ ε i = {⟨n, by omega⟩}) → False := by
    intro hcard2 hnat2
    have hsf : s < f := by
      have hd2 : (n + 1) ^ 2 ≤ d := by
        obtain ⟨a, b, hab, hT⟩ := Finset.card_eq_two.mp hcard2
        have hact : ε a ≠ ∅ := by
          have hmem : a ∈ Finset.univ.filter (fun i => ε i ≠ ∅) := by
            rw [hT]
            exact Finset.mem_insert_self a {b}
          simpa using hmem
        have hbact : ε b ≠ ∅ := by
          have hmem : b ∈ Finset.univ.filter (fun i => ε i ≠ ∅) := by
            rw [hT]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
          simpa using hmem
        have hprod : (∏ i ∈ Finset.univ.filter (fun i => ε i ≠ ∅), orbitSize (ε i)) =
            orbitSize (ε a) * orbitSize (ε b) := by
          rw [hT, Finset.prod_pair hab]
        have hOa : orbitSize (ε a) = n + 1 := by
          rcases hnat2 a hact with h | h
          · rw [h]; exact orbitSize_natural_left (n := n + 1) (by omega)
          · rw [h]; exact orbitSize_natural_right (n := n + 1) (by omega)
        have hOb : orbitSize (ε b) = n + 1 := by
          rcases hnat2 b hbact with h | h
          · rw [h]; exact orbitSize_natural_left (n := n + 1) (by omega)
          · rw [h]; exact orbitSize_natural_right (n := n + 1) (by omega)
        have h := hd_bound
        rw [hprod, hOa, hOb] at h
        simpa [pow_two] using h
      have hmul : s * (n + 1) ^ 2 < f * (n + 1) ^ 2 :=
        lt_of_le_of_lt (Nat.mul_le_mul_left s hd2) hdim_bound
      exact (Nat.mul_lt_mul_right (by positivity)).mp hmul
    have hval : ∀ g ∈ (curtisDatum n K 2).H, ∃ c : E, χ g = algebraMap E k c :=
      CFSG.LieType.SpecialLinear.chi_mem_range_of_isCoverType_extendScalars
        (m := n) (F := K) (E := E) (k := k) (X := ρ.asModule) (endFieldRep ρ) hsimp ht
    have hrot_s : ∀ r : Fin f, ε ⟨(r + s) % f, Nat.mod_lt _ r.pos⟩ = ε r :=
      CFSG.LieType.SpecialLinear.rotate_eq_of_chi_mem_range (F := K) (E := E) (k := k)
        hK hE' ε hε0 hεχ hval
    obtain ⟨e, hfe, hrot_e⟩ :=
      CFSG.LieType.SpecialLinear.rotate_half_of_card_eq_two ε hs_pos hsf hrot_s hcard2
    have hes : e ≤ s := by
      have h2 : 2 * e ≤ 2 * s := by
        calc 2 * e = f := hfe.symm
          _ ≤ s * 2 := by simpa [hcard2] using hs_bound
          _ = 2 * s := by ring
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
    obtain ⟨r₁, hr₁⟩ := htε
    let r₂ : Fin f := ⟨(r₁ + e) % f, Nat.mod_lt _ r₁.pos⟩
    have hr₂ : (r₂ : ℕ) = (r₁ + e) % f := rfl
    have hεr₂ : ε r₂ = ε r₁ := hrot_e r₁
    have he0 : 0 < e := by omega
    have hef : e < f := by omega
    have hr₂ne : r₂ ≠ r₁ := by
      intro hEq
      have hval : (r₁ + e) % f = (r₁ : ℕ) := by
        have := congrArg Fin.val hEq
        simpa [r₂] using this
      have hmod : r₁ + e ≡ r₁ [MOD f] := by
        show (r₁ + e) % f = r₁ % f
        rw [Nat.mod_eq_of_lt r₁.isLt]
        exact hval
      exact (Nat.not_dvd_of_pos_of_lt he0 hef) (Nat.add_modEq_left_iff.mp hmod)
    let T := Finset.univ.filter fun i => ε i ≠ ∅
    have hTcard : T.card = 2 := by simpa [T] using hcard2
    have hmem₁ : r₁ ∈ T := by simpa [T] using hr₁
    have hmem₂ : r₂ ∈ T := by
      have hne₂ : ε r₂ ≠ ∅ := by rw [hεr₂]; exact hr₁
      simpa [T] using hne₂
    have hTpair : T = {r₁, r₂} := by
      have hsub : ({r₁, r₂} : Finset (Fin f)) ⊆ T := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hmem₁
        · rw [Finset.mem_singleton.mp hx]
          exact hmem₂
      have hcardpair : ({r₁, r₂} : Finset (Fin f)).card = 2 :=
        Finset.card_pair hr₂ne.symm
      have hle : T.card ≤ ({r₁, r₂} : Finset (Fin f)).card := by
        rw [hTcard, hcardpair]
      exact (Finset.eq_of_subset_of_card_le hsub hle).symm
    have hrest : ∀ r, r ≠ r₁ → r ≠ r₂ → ε r = ∅ := by
      intro r hr1 hr2
      by_contra hne
      have hmem : r ∈ T := by simpa [T] using hne
      rw [hTpair] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hr1 h
      · rw [Finset.mem_singleton.mp h] at hr2
        exact hr2 rfl
    rcases hnat2 r₁ hr₁ with h1 | h1
    · let j : Fin (n + 1) := ⟨1, by omega⟩
      have hj : (j : ℕ) = 1 ∨ (j : ℕ) = n := Or.inl rfl
      have hε₁ : ε r₁ = {j} := by simpa [j] using h1
      have hε₂ : ε r₂ = {j} := by rw [hεr₂, hε₁]
      exact CFSG.LieType.SpecialLinear.stage_pair_false (n := n) (f := f) (e := e)
        (hn := hn) (hF := hK) (hfe := hfe)
        (E := E) (k := k) (D := ↥D) (σ := endFieldRep ρ) (X := ρ.asModule)
        (hsimp := hsimp) (hne := hne_top) (δ := topActor ρ D)
        (hδE := hδE) (hD2 := hD2top) (hD1 := hD1top) (hquad := hquadtop)
        (hcompat := hcompatTop) (hoff := hofftop) (ε := ε) (β := β) (hβ := hβ)
        (hE := hE') (hes := hes) (r₁ := r₁) (r₂ := r₂) (hr₂ := hr₂)
        (j := j) (hj := hj) (h₁ := hε₁) (h₂ := hε₂) (hrest := hrest)
    · let j : Fin (n + 1) := ⟨n, by omega⟩
      have hj : (j : ℕ) = 1 ∨ (j : ℕ) = n := Or.inr rfl
      have hε₁ : ε r₁ = {j} := by simpa [j] using h1
      have hε₂ : ε r₂ = {j} := by rw [hεr₂, hε₁]
      exact CFSG.LieType.SpecialLinear.stage_pair_false (n := n) (f := f) (e := e)
        (hn := hn) (hF := hK) (hfe := hfe)
        (E := E) (k := k) (D := ↥D) (σ := endFieldRep ρ) (X := ρ.asModule)
        (hsimp := hsimp) (hne := hne_top) (δ := topActor ρ D)
        (hδE := hδE) (hD2 := hD2top) (hD1 := hD1top) (hquad := hquadtop)
        (hcompat := hcompatTop) (hoff := hofftop) (ε := ε) (β := β) (hβ := hβ)
        (hE := hE') (hes := hes) (r₁ := r₁) (r₂ := r₂) (hr₂ := hr₂)
        (j := j) (hj := hj) (h₁ := hε₁) (h₂ := hε₂) (hrest := hrest)
  have hadj_bound : ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) →
      ε i₀ = {⟨1, by omega⟩, ⟨n, by omega⟩} → False := by
    intro i₀ hε' hεset
    have hne₀ : ε i₀ ≠ ∅ := by rw [hεset]; simp
    have hcard1 := card_active_eq_one_of_forall_eq_empty hne₀ hε'
    have hfs : f ≤ s := by simpa [hcard1] using hs_bound
    exact CFSG.LieType.SpecialLinear.stage_adjoint_false (n := n) (f := f)
      (hn := hn) (hF := hK)
      (E := E) (k := k) (D := ↥D) (σ := endFieldRep ρ) (X := ρ.asModule)
      (hsimp := hsimp) (hne := hne_top) (δ := topActor ρ D)
      (hδE := hδE) (hD2 := hD2top) (hD1 := hD1top) (hquad := hquadtop)
      (hcompat := hcompatTop) (hoff := hofftop) (ε := ε) (β := β) (hβ := hβ)
      (hE := hE') (hfs := hfs) (r₀ := i₀) (hε' := hε') (hε := hεset)
  have hcube_bound : ∀ h6 : n + 1 = 6, ∀ i₀, (∀ i, i ≠ i₀ → ε i = ∅) →
      ε i₀ = {⟨3, by omega⟩} → False := by
    intro h6 i₀ hε' hεset
    have hn5 : n = 5 := by omega
    subst n
    have hne₀ : ε i₀ ≠ ∅ := by rw [hεset]; simp
    have hcard1 := card_active_eq_one_of_forall_eq_empty hne₀ hε'
    have hfs : f ≤ s := by simpa [hcard1] using hs_bound
    have hq : 2 < Fintype.card K := by
      have hfpos : 0 < f := by
        have h2 : 1 < 2 ^ f := by
          have h := Finite.one_lt_card (α := K)
          rw [Nat.card_eq_fintype_card, hK] at h
          exact h
        by_contra h
        have h0 : f = 0 := by omega
        rw [h0] at h2
        norm_num at h2
      have hr3 : 3 ≤ r := by
        have := hr.two_le
        omega
      have hpos : 0 < 2 ^ f - 1 := by
        have h2 : 2 ≤ 2 ^ f := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfpos
        omega
      have hle : r ≤ 2 ^ f - 1 := Nat.le_of_dvd hpos hrq
      have h3 : 3 ≤ 2 ^ f - 1 := le_trans hr3 hle
      rw [hK]
      omega
    exact CFSG.LieType.SpecialLinear.stage_cube_false (f := f)
      (hF := hK) (hq := hq)
      (E := E) (k := k) (D := ↥D) (σ := endFieldRep ρ) (X := ρ.asModule)
      (hsimp := hsimp) (hne := hne_top) (δ := topActor ρ D)
      (hδE := hδE) (hD2 := hD2top) (hD1 := hD1top) (hquad := hquadtop)
      (hcompat := hcompatTop) (hoff := hofftop) (ε := ε) (β := β) (hβ := hβ)
      (hE := hE') (hfs := hfs) (r₀ := i₀) (hε' := hε') (hε := hεset)
  exact psl_false_of_label_bounds (n := n + 1) (f := f) (r := r) (s := s) (d := d)
    (by omega) hr hr2 hrn ε hε0 htε hscal_bound hs_bound hdim_bound hd_bound
    hextra_bound hnat_bound hadj_bound hcube_bound)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

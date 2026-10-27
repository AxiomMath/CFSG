module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinAux
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
  CFSG.LocalAnalysis.GLTheoremA.T263.SD

variable {K : Type} [Field K] [Finite K] {n : ℕ}

local notation "𝒱" => (Fin n → K)

theorem lift_commutes (h2 : (2 : K) = 0) (hn0 : 0 < n) {A : GL (Fin n) K} {w : projectiveSL n K}
    (hw : w ∈ fixSubgroup (conjAut n K A)) {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hgw : proj n K g = w) {k : ℕ} (hgk : g ^ (2 ^ k) = 1) :
    slGL n K g ∈ gl_centralizer (glA A) := by
  have h1 : proj n K (CatalogueBHigherLinearAction.slConjugation n K A g) = proj n K g := by
    rw [← conjAut_proj, hgw]
    exact mem_fixSubgroup.1 hw
  have h2' : (CatalogueBHigherLinearAction.slConjugation n K A g) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hgk, map_one]
  have h3 := eq_of_proj_eq_of_two_pow h2 hn0 h2' hgk h1
  exact mem_fixSubgroup_slConjugation_iff.1 (mem_fixSubgroup.2 h3)

theorem gl_apply_inv_apply {V : Type*} [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) (v : V) :
    (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
  rfl

theorem gl_inv_apply_apply {V : Type*} [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) (v : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) ((g : Module.End K V) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
  rfl

theorem bad_block_trivial (h2 : (2 : K) = 0) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : p = 3 → 4 ≤ Nat.card K) {A B : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱)))
    (hB : conjAut n K B * conjAut n K A = conjAut n K A * conjAut n K B)
    (hBp : conjAut n K B ^ p = 1) {g zt : Matrix.SpecialLinearGroup (Fin n) K}
    (hgc : slGL n K g ∈ gl_centralizer (glA A))
    (hs : (CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹)⁻¹ * zt ∈ scalars n K)
    {h : K[X]} (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱))
    (hm2 : primaryMultiplicity (glA A : Module.End K 𝒱) h = 2) (hq : Nat.card (AdjoinRoot h) ≤ 3) :
    ∀ v ∈ primaryComponent (glA A : Module.End K 𝒱) h,
      ((slGL n K zt : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) v = v := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hn0 : 0 < n := by omega
  obtain ⟨hK2, hKu⟩ := units_eq_one_of_card_le_three h2 (E := AdjoinRoot h) hq
  have hp3 : 3 < p := by
    have hp3' : p ≠ 3 := fun h3 => by
      have := hK h3
      omega
    have := hp.two_le
    by_contra hle
    push Not at hle
    interval_cases p <;> simp_all
  have hzt : zt = CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹ :=
    (inv_mul_eq_one.1 (scalars_eq_one_of_units_subsingleton hKu hs)).symm
  obtain ⟨ζ, hζ⟩ := comm_scalar_of_conjAut_comm hn hB
  rw [hKu ζ, map_one] at hζ
  have hBA : B * A = A * B := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hζ)
  have hBc : glA B ∈ gl_centralizer (glA A) := by
    rw [mem_gl_centralizer]
    have h3 : (glA B) * (glA A) = (glA A) * (glA B) := by
      show Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A =
        Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B
      rw [← map_mul, ← map_mul, hBA]
    have h4 := congrArg (fun z : LinearMap.GeneralLinearGroup K 𝒱 => (z : Module.End K 𝒱)) h3
    simp only [Units.val_mul] at h4
    exact h4
  obtain ⟨c₁, hc₁⟩ := pow_scalar_of_conjAut_pow hn hBp
  rw [hKu c₁, map_one] at hc₁
  have hBpl : (glA B) ^ p = 1 := by
    show Matrix.GeneralLinearGroup.toLin B ^ p = 1
    rw [← map_pow, hc₁, map_one]
  have hfix := apply_eq_of_card_le_three hsq hh hm2 hq hp hp3 hBc hBpl
  intro v hv
  have hinvfix : ∀ t ∈ primaryComponent (glA A : Module.End K 𝒱) h,
      (((glA B)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t = t := by
    intro t ht
    have := gl_inv_apply_apply (glA B) t
    rwa [hfix t ht] at this
  have hw : (((slGL n K g)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) v ∈
      primaryComponent (glA A : Module.End K 𝒱) h :=
    apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hgc)) hv
  rw [hzt, map_mul, map_inv, slGL_slConjugation]
  simp only [Units.val_mul, Module.End.mul_apply]
  rw [hinvfix _ hw, gl_apply_inv_apply, hfix v hv]

variable {A : GL (Fin n) K}

local notation "𝒲[" h "]" => primaryComponent (glA A : Module.End K 𝒱) h

theorem not_scalar_on_block (h2 : (2 : K) = 0) {B : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱))
    {g zt s : Matrix.SpecialLinearGroup (Fin n) K} (hgc : slGL n K g ∈ gl_centralizer (glA A))
    (hBc : glA B ∈ gl_centralizer (glA A))
    (hzt : zt = CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹ * s) (hs : s ∈ scalars n K)
    {k : ℕ} (hzt2 : zt ^ (2 ^ k) = 1) {v : 𝒱} (hv : v ∈ 𝒲[h])
    (hne : ((slGL n K zt : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) v ≠ v) :
    ¬ ∃ c : AdjoinRoot h, ∀ w : 𝒲[h],
      (((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w : 𝒱)) =
        ((c • w : 𝒲[h]) : 𝒱) := by
  rintro ⟨c, hc⟩
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨l, hl⟩ := slGL_scalar_apply hs
  let γg := commutantRestrict h
    ⟨(slGL n K g : Module.End K 𝒱), mem_commutant_of_mem_gl_centralizer hgc⟩
  have hcomm : ∀ t ∈ 𝒲[h], ((glA B * slGL n K g * (glA B)⁻¹ * (slGL n K g)⁻¹ :
      LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t = t := by
    intro t ht
    have hw : (((slGL n K g)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t ∈ 𝒲[h] :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hgc)) ht
    let w : 𝒲[h] := ⟨(((slGL n K g)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t, hw⟩
    have hw₂ : (((glA B)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w : 𝒱) ∈ 𝒲[h] :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hBc)) w.2
    let w₂ : 𝒲[h] := ⟨(((glA B)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w : 𝒱), hw₂⟩
    have h1 : ((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱) =
        ((c • w₂ : 𝒲[h]) : 𝒱) := hc w₂
    have h2' : ((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱) = (w : 𝒱) :=
      gl_apply_inv_apply (glA B) (w : 𝒱)
    have hw₃ : ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱) ∈ 𝒲[h] :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp hgc) w₂.2
    let w₃ : 𝒲[h] := ⟨((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱), hw₃⟩
    have h3 : ((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₃ : 𝒱) =
        ((c • w₃ : 𝒲[h]) : 𝒱) := hc w₃
    have h4 : ((c • w₃ : 𝒲[h]) : 𝒱) =
        ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) ((c • w₂ : 𝒲[h]) : 𝒱) :=
      (congrArg Subtype.val (map_smul γg c w₂)).symm
    simp only [Units.val_mul, Module.End.mul_apply]
    calc ((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱)
          (((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱))
        = ((c • w₃ : 𝒲[h]) : 𝒱) := h3
      _ = ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) ((c • w₂ : 𝒲[h]) : 𝒱) := h4
      _ = ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱)
          (((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w₂ : 𝒱)) := by rw [h1]
      _ = ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w : 𝒱) := by rw [h2']
      _ = t := gl_apply_inv_apply (slGL n K g) t
  have hy : (slGL n K zt) ^ (2 ^ k) = 1 := by rw [← map_pow, hzt2, map_one]
  have hztl : ∀ w : 𝒲[h], ((slGL n K zt : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (w : 𝒱) =
      ((algebraMap K (AdjoinRoot h) l • w : 𝒲[h]) : 𝒱) := by
    intro w
    rw [coe_algebraMap_smul_primaryComponent _ _ l w, hzt, map_mul, map_mul, map_inv,
      slGL_slConjugation]
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [hl]
    simp only [map_smul]
    have := hcomm (w : 𝒱) w.2
    simp only [Units.val_mul, Module.End.mul_apply] at this
    rw [this]
  exact hne (eq_of_smul_of_two_pow h2 hh hy hztl ⟨v, hv⟩)

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end

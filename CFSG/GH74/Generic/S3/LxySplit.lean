module

public import CFSG.GH74.Generic.S3.Main19
public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.GH74.Generic.S3.L3ClassC2T2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.E2.CaseIINoComp
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS.TwoThin CFSG.GH74.E2 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

section Model

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_lieModel_K (hnd : NbrData G t p f x y Iw Iv) {K : Subgroup (CentralizerBar x)}
    (himg : imgBar x Iw = K) (hKc : center ↥K = ⊥) (hKn : Nontrivial ↥K) :
    LieModel ↥K t 3 p f := by
  have hIwle : Iw ≤ centralizer ({x} : Set G) := hnd.comp_w.1.1
  have hq : IsQuasisimple ↥Iw := hnd.comp_w.1.isQuasisimple
  have hmem : ∀ m : ↥Iw, proj x ⟨(m : G), hIwle m.2⟩ ∈ K := by
    intro m
    have h := mem_imgBar.2 (show ∃ g : ↥(centralizer ({x} : Set G)), (g : G) ∈ Iw ∧
      proj x g = proj x ⟨(m : G), hIwle m.2⟩ from ⟨⟨m, hIwle m.2⟩, m.2, rfl⟩)
    rwa [himg] at h
  let φ : ↥Iw →* ↥K := ((proj x).comp (Subgroup.inclusion hIwle)).codRestrict K hmem
  have hφ : Function.Surjective φ := by
    rintro ⟨k, hk⟩
    rw [← himg] at hk
    obtain ⟨g, hgM, rfl⟩ := mem_imgBar.1 hk
    exact ⟨⟨g, hgM⟩, rfl⟩
  have hker : φ.ker = center ↥Iw := by
    apply le_antisymm
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker φ) with h | h
      · exfalso
        obtain ⟨k, hk⟩ := exists_ne (1 : ↥K)
        obtain ⟨m, rfl⟩ := hφ k
        exact hk (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top m))
      · exact h
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzc : φ z ∈ center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro k
        obtain ⟨m, rfl⟩ := hφ k
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz m]
      rw [hKc, Subgroup.mem_bot] at hzc
      exact hzc
  let e : ↥Iw ⧸ center ↥Iw ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact CFSG.GH74.lieModel_of_mulEquiv e hnd.model_w

end Model

@[expose] def NontrivAt {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)) :
    Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K → ¬ IsComponent (S45.barSub (y * x) Iv)

@[expose] def LxyShapeAt {G : Type} [Group G] [Finite G] (x : G)
    (K : Subgroup (CentralizerBar x)) : Prop :=
  ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
    NbrData G t p f x y Iw Iv → imgBar x Iw = K →
    ∀ L : Subgroup (CentralizerBar (y * x)), IsComponent L → S45.barSub (y * x) Iv ≤ L →
      S45.barSub (y * x) Iv ≠ L →
        ∃ t' : StatedLieTag, (t' = .PSL ∨ t' = .PSU) ∧ LieModel ↥L t' 3 p f

@[expose] def B_S3_nontrivJNT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K → LyAt x K →
      NontrivAt x K

@[expose] def B_S3_LxyShapeJNT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K → LyAt x K →
      LxyShapeAt x K

@[expose] def L3FRank : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 →
    5 ≤ p ^ f → Gen4Comp X → LieModel X t 3 p f → FRank X = (p ^ f) ^ 4 * 6

theorem b_S3_LxyJNT_of_parts
    (hG : GenericKnownFacts) (hE : E2ComponentFacts)
    (hLy : B_S3_LyJNT) (hOnly : B_S3_onlyInvJNT)
    (hNontriv : B_S3_nontrivJNT) (hShape : B_S3_LxyShapeJNT) (hFR : L3FRank) :
    B_S3_LxyJNT := by
  intro G _ _ x K hset hmax hthin honly t p f y Iw Iv hnd himg L hLc hle
  have hLyAt : LyAt x K := hLy G x K hset hmax hthin honly
  have hnt := hNontriv G x K hset hmax hthin honly hLyAt t p f y Iw Iv hnd himg
  have hne : S45.barSub (y * x) Iv ≠ L := fun h => hnt (by rw [h]; exact hLc)
  obtain ⟨t', ht', hmodelL⟩ :=
    hShape G x K hset hmax hthin honly hLyAt t p f y Iw Iv hnd himg L hLc hle hne
  refine ⟨t', ht', hmodelL, ?_⟩
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hnd.y_inv, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hnd.x_inv, pow_two] at this
  have hyx2 : orderOf (y * x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (y * x) ^ 2 = (y * x) * (y * x) := by rw [pow_two]
        _ = y * (x * y) * x := by group
        _ = y * (y * x) * x := by rw [hnd.comm]
        _ = (y * y) * (x * x) := by group
        _ = 1 := by rw [hy2, hx2, one_mul]
    · intro h
      apply hnd.ne
      calc y = y * (x * x) := by rw [hx2, mul_one]
        _ = (y * x) * x := by rw [mul_assoc]
        _ = x := by rw [h, one_mul]
  obtain ⟨⟨p₀, f₀, -, -, -, hmodelK₀⟩, -⟩ := hset.shape
  have hKcen : center ↥K = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hset.comp.1 hmodelK₀
  have hKnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hset.comp.1
  have hmodelK : LieModel ↥K t 3 p f := hnd.lxy_lieModel_K himg hKcen hKnt
  have hmodelL' : LieModel ↥L .PSL 3 p f ∨ LieModel ↥L .PSU 3 p f := by
    rcases ht' with rfl | rfl
    · exact Or.inl hmodelL
    · exact Or.inr hmodelL
  have hLcen : center ↥L = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hLc.1 hmodelL'
  have hxbarL : xbar (y * x) ∉ L := xbar_not_mem_of_center_eq_bot hyx2 hLcen
  have hshapeL : ShapeS3 (y * x) L :=
    ⟨⟨p, f, hnd.prime.1, hnd.prime.2.1, hnd.prime.2.2, hmodelL'⟩, hxbarL⟩
  have hKP : GLS.IsKProperSimple G :=
    ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  have hgenK : Gen4Comp ↥K := gen4Comp_of_gen4Cen (gen4Cen_barQ hset.gen4 hset.inv) K
  have hgenL : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hset.gen4 hyx2) L
  have hFK := hFR ↥K t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenK hmodelK
  have hFL := hFR ↥L t' p f ht' hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenL hmodelL
  have hLcl := l3_not_inC2_not_inT2 hG hE ht' hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenL hmodelL
  have hG2L : GLS.InG2 ↥L :=
    ⟨GLS.inCalK2_of_isComponent hKP hyx2 hLc, hLcl.1, hLcl.2⟩
  have hsetL : S3Setup G (y * x) L :=
    ⟨hset.simple, hset.nonab, hset.rank, hset.gen4, hset.kgh, hset.sylow, hset.layerNe, hyx2, hLc,
      hG2L, hshapeL⟩
  have hd2K : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  have hd2L : d2 ↥L = 7 := d2_eq_seven_of_shapeS3 hLc hG2L hshapeL
  have hFeq : FRank ↥K = FRank ↥L := by rw [hFK, hFL]
  have hmaxL : IsJMax (y * x) L :=
    ⟨⟨hyx2, hLc, hG2L⟩, fun y' L' hp' => by
      obtain ⟨h1, h2⟩ := hmax.2 y' L' hp'
      refine ⟨by omega, fun hd => ?_⟩
      have h3 := h2 (by omega)
      omega⟩
  exact hOnly G (y * x) L hsetL hmaxL hthin

end CFSG.GH74.Generic.S3

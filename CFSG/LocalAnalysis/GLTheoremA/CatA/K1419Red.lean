module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G]

theorem glaPPrimeCoreOf_eq_map' (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X = (GLAPPrimeCore p ↥X).map X.subtype := rfl

theorem conjAut'_zpow_apply [Finite G] (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) (k : ℤ) (l : K) :
    (((conjAut' K y hy) ^ k) l : G) = y ^ k * (l : G) * (y ^ k)⁻¹ := by
  have hyk : y ^ k ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hy k
  have hpow : (conjAut' K y hy) ^ k = conjAut' K (y ^ k) hyk := by
    unfold conjAut'
    rw [← map_zpow]
    all_goals rfl
  rw [hpow, coe_conjAut']

theorem i1419Rel_conjAut'_zpow [Finite G] (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G)) (k : ℤ) :
    I1419Rel ((conjAut' K y hy) ^ k) = S10.indRel 3 K (y ^ (-k)) := by
  funext q q'
  apply propext
  unfold I1419Rel S10.indRel
  refine exists_congr fun l => exists_congr fun l' => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [← Subtype.coe_inj, conjAut'_zpow_apply, zpow_neg, inv_inv]
  exact eq_comm

theorem glaMarking_congr {L : Type} [Group L] {P P' : CFSG.Assembly.LargeEvenMarkProp L}
    (h : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : L ⧸ Subgroup.center L ≃* R), P lab R I F θ ↔ P' lab R I F θ) :
    GLAMarking L P → GLAMarking L P' := by
  have hP : P = P' := by
    funext lab R _ I F θ
    exact propext (h lab R I F θ)
  rw [hP]
  exact id

theorem i1419Inn_of_innDiagOn [Finite G] (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (h : GLAMarking (PQuot 3 K) fun _ _ _ I _ θ => ∀ a ∈ Subgroup.zpowers y, ∃ φ ∈ I, GLAInduces θ (S10.indRel 3 K a) φ) :
    I1419Inn (conjAut' K y hy) := by
  unfold I1419Inn
  apply glaMarking_congr _ h
  intro lab R _ I F θ
  constructor
  · intro h1 k
    have h2 := h1 (y ^ (-k)) (Subgroup.zpow_mem_zpowers y (-k))
    rw [i1419Rel_conjAut'_zpow]
    exact h2
  · intro h1 a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h2 := h1 (-n)
    rw [i1419Rel_conjAut'_zpow, neg_neg] at h2
    exact h2

theorem nontriv_of_not_centMod [Finite G] (K : Subgroup G) {y : G} (hy : y ∈ Subgroup.normalizer (K : Set G))
    (hC : ¬ CentMod 3 K y) : I1419Nontriv (conjAut' K y hy) := by
  by_contra hnt
  apply hC
  unfold CentMod
  refine ⟨hy, ?_⟩
  unfold I1419Nontriv at hnt
  push Not at hnt
  have key : ∀ k : ℤ, ∀ l : K,
      (QuotientGroup.mk ((conjAut' K y hy ^ k) l) : PQuot 3 K) = QuotientGroup.mk l := by
    intro k
    induction k using Int.induction_on with
    | zero => intro l; rfl
    | succ _i ih =>
      intro l
      rw [zpow_add_one, MulAut.mul_apply, ih (conjAut' K y hy l), hnt l]
    | pred _i ih =>
      intro l
      rw [zpow_sub_one, MulAut.mul_apply, ih]
      have h1 := hnt ((conjAut' K y hy)⁻¹ l)
      rw [MulAut.apply_inv_self] at h1
      exact h1.symm
  rw [Subgroup.commutator_le]
  intro g hg k' hk'
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk'
  have hmem := (QuotientGroup.eq).1 (key n ⟨g, hg⟩⁻¹)
  have hO : (K.subtype (((conjAut' K y hy ^ n) ⟨g, hg⟩⁻¹)⁻¹ * ⟨g, hg⟩⁻¹) : G) ∈ GLAPPrimeCoreOf 3 K := by
    rw [glaPPrimeCoreOf_eq_map']
    exact Subgroup.mem_map_of_mem _ hmem
  have hcomm : ⁅y ^ n, g⁆ ∈ GLAPPrimeCoreOf 3 K := by
    have hval : (K.subtype (((conjAut' K y hy ^ n) ⟨g, hg⟩⁻¹)⁻¹ * ⟨g, hg⟩⁻¹) : G) = ⁅y ^ n, g⁆ := by
      have h3 := conjAut'_zpow_apply K hy n ⟨g, hg⟩⁻¹
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at h3 ⊢
      rw [h3, commutatorElement_def]
      group
    rw [← hval]
    exact hO
  rw [← commutatorElement_inv]
  exact (GLAPPrimeCoreOf 3 K).inv_mem hcomm

theorem center_bot_subgroupOf [Finite G] {K L : Subgroup G} (hKL : K ≤ L) (hZ : Subgroup.center (PQuot 3 K) = ⊥) :
    Subgroup.center (PQuot 3 (K.subgroupOf L)) = ⊥ := by
  obtain ⟨e⟩ := K144.pQuot_subgroupOf_equiv (p := 3) hKL
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h2 : e x ∈ Subgroup.center (PQuot 3 K) := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map_of_mem _ hx
  rw [hZ, Subgroup.mem_bot] at h2
  exact e.injective (by rw [h2, map_one])

theorem i1419_of_facts [Finite G] (hA : I1419UpFact) (hC : I1419ClassFact) (hE : I1419ExcFact) :
    CFSG.LocalAnalysis.GLTheoremA.I1419FourAt G := by
  intro X L K y hX hL hNy hy3 hCent hK hcat hZ hInn
  have hp3 : Nat.Prime 3 := by norm_num
  have hQ : CFSG.Open.IsQuasisimple (PQ ↥L) := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  have hCat : IsCatalogGroup (PQ ↥L ⧸ Subgroup.center (PQ ↥L)) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
      ((hX.of_le hL.1).quotient (GLAPPrimeCore 3 ↥L)) hQ
  have hβ3 : (conjAut' L y hNy) ^ 3 = 1 := conjAut'_pow L hNy hy3
  obtain ⟨hKL, hJ⟩ := glaPComponent_fixSubgroup_conjAut' hp3 L hNy hK
  obtain ⟨eS⟩ := K144.pSimple_subgroupOf_equiv (p := 3) hKL
  have hcat' : catalogIs (PSimple 3 (K.subgroupOf L)) l3u3Index := (catalogIs_congr eS).2 hcat
  have hZ' : Subgroup.center (PQuot 3 (K.subgroupOf L)) = ⊥ := center_bot_subgroupOf hKL hZ
  have hNt : I1419Nontriv (conjAut' L y hNy) := nontriv_of_not_centMod L hNy hCent
  have hInn' := hInn
  unfold InnDiagOn at hInn'
  have hI : I1419Inn (conjAut' L y hNy) := i1419Inn_of_innDiagOn L hNy hInn'.2
  by_cases hcl : catalogIs (PSimple 3 L) I1419Classical2
  · exact hC ↥L (conjAut' L y hNy) (K.subgroupOf L) hQ hβ3 hNt hI hJ hcat' hZ' hcl
  · have hch := hA ↥L (conjAut' L y hNy) (K.subgroupOf L) hQ hCat hβ3 hNt hJ hcat'
    exact hE ↥L (conjAut' L y hNy) (K.subgroupOf L) hQ hβ3 hNt hI hJ hcat' hZ' hch hcl

theorem i1419Up_of_cases (hAlt : I1419UpAltFact) (hSpor : I1419UpSporFact) (hLie : I1419UpLieOddFact) :
    I1419UpFact := by
  intro Q _ _ β J hQ hCat hβ3 hNt hJ hcat
  by_contra hnot
  obtain ⟨i, ⟨eS⟩⟩ := hCat
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQ Q) hQ
    apply hab
    apply eS.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact hAlt Q β J hQ ⟨.alternating n hn, trivial, ⟨eS⟩⟩ hnot hβ3 hNt hJ hcat
  | sporadic s =>
    exact hSpor Q β J hQ ⟨.sporadic s, trivial, ⟨eS⟩⟩ hnot hβ3 hNt hJ hcat
  | lie dl =>
    by_cases hc : dl.1.characteristic = 2
    · exact hnot (Or.inl ⟨.lie dl, hc, ⟨eS⟩⟩)
    · exact hLie Q β J hQ ⟨.lie dl, hc, ⟨eS⟩⟩ hnot hβ3 hNt hJ hcat

theorem i1419_of_cases [Finite G] (hAlt : I1419UpAltFact) (hSpor : I1419UpSporFact)
    (hLie : I1419UpLieOddFact) (hC : I1419ClassFact) (hE : I1419ExcFact) :
    CFSG.LocalAnalysis.GLTheoremA.I1419FourAt G :=
  i1419_of_facts (i1419Up_of_cases hAlt hSpor hLie) hC hE

end CFSG.LocalAnalysis.GLTheoremA.K1419

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)
open scoped Pointwise

namespace P614K64b

variable {A : Type} [Group A]

theorem le_normalizer_of_le_of_le {D L N : Subgroup A} (hLD : L ≤ normalizer (D : Set A))
    (hDN : D ≤ N) (hNL : N ≤ L) : D ≤ normalizer (N : Set A) := by
  rw [Subgroup.le_normalizer_iff]
  intro d hd x hx
  have h1 : x * d⁻¹ * x⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hLD (hNL hx)) d⁻¹).mp (inv_mem hd)
  have h2 : d * x * d⁻¹ = d * (x * d⁻¹ * x⁻¹) * x := by group
  rw [h2]
  exact mul_mem (hDN (mul_mem hd h1)) hx

theorem commutator_mem_of_sup_eq {D L X : Subgroup A} (hXL : X ≤ L)
    (hLD : L ≤ normalizer (D : Set A)) (hsup : X ⊔ D = L) (hXX : ⁅X, X⁆ ≤ D) :
    ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ D := by
  have hcoe : ((X ⊔ D : Subgroup A) : Set A) = (X : Set A) * (D : Set A) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X D (hXL.trans hLD)
  have hconj : ∀ g ∈ L, ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun g hg d hd =>
    (Subgroup.mem_normalizer_iff.mp (hLD hg) d).mp hd
  intro a ha b hb
  have ha' : a ∈ ((X ⊔ D : Subgroup A) : Set A) := by rw [hsup]; exact ha
  have hb' : b ∈ ((X ⊔ D : Subgroup A) : Set A) := by rw [hsup]; exact hb
  rw [hcoe] at ha' hb'
  obtain ⟨x, hx, d, hd, rfl⟩ := Set.mem_mul.mp ha'
  obtain ⟨y, hy, e, he, rfl⟩ := Set.mem_mul.mp hb'
  have hxL : x ∈ L := hXL hx
  have hyL : y ∈ L := hXL hy
  have key : x * d * (y * e) * (x * d)⁻¹ * (y * e)⁻¹ =
      x * d * x⁻¹ * ((x * y) * (e * d⁻¹) * (x * y)⁻¹) *
        ((x * y * x⁻¹) * e⁻¹ * (x * y * x⁻¹)⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
  rw [key]
  refine mul_mem (mul_mem (mul_mem (hconj x hxL d hd) ?_) ?_) ?_
  · exact hconj _ (mul_mem hxL hyL) _ (mul_mem he (inv_mem hd))
  · exact hconj _ (mul_mem (mul_mem hxL hyL) (inv_mem hxL)) _ (inv_mem he)
  · have h := Subgroup.commutator_mem_commutator hx hy
    rw [commutatorElement_def] at h
    exact hXX h

theorem normalizer_le_normalizer_derivedSeriesOf (H : Subgroup A) (n : ℕ) :
    normalizer (H : Set A) ≤ normalizer (CFSG.Quasithin.derivedSeriesOf H n : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact CFSG.Quasithin.map_conj_derivedSeriesOf hg n

theorem derivedSeriesOf_sup_eq {L D : Subgroup A} (hs : S622IsSimpleSection L D) (n : ℕ) :
    CFSG.Quasithin.derivedSeriesOf L n ⊔ D = L := by
  obtain ⟨hDL, hDn, -, hmax, hnab⟩ := hs
  have hLD : L ≤ normalizer (D : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mp hDn
  induction n with
  | zero => exact sup_eq_left.mpr hDL
  | succ n ih =>
    have hXL : CFSG.Quasithin.derivedSeriesOf L n ≤ L := CFSG.Quasithin.derivedSeriesOf_le L n
    have hNL : CFSG.Quasithin.derivedSeriesOf L (n + 1) ⊔ D ≤ L :=
      sup_le (CFSG.Quasithin.derivedSeriesOf_le L (n + 1)) hDL
    have hnormal : ((CFSG.Quasithin.derivedSeriesOf L (n + 1) ⊔ D).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
      exact (le_inf (Subgroup.le_normalizer.trans
        (normalizer_le_normalizer_derivedSeriesOf L (n + 1))) hLD).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    rcases hmax _ le_sup_right hNL hnormal with h | h
    · exfalso
      apply hnab
      refine commutator_mem_of_sup_eq hXL hLD ih ?_
      rw [← CFSG.Quasithin.derivedSeriesOf_succ]
      exact le_sup_left.trans h.le
    · exact h

theorem perfectCore_sup_eq [Finite A] {L D : Subgroup A} (hs : S622IsSimpleSection L D) :
    CFSG.Quasithin.perfectCore L ⊔ D = L := by
  obtain ⟨n, hn⟩ := CFSG.Quasithin.exists_perfectCore_eq L
  rw [hn n le_rfl]
  exact derivedSeriesOf_sup_eq hs n

theorem mem_of_sup_eq [Finite A] {K D L : Subgroup A} (hKL : K ≤ L)
    (hLK : L ≤ normalizer (K : Set A)) (hLD : L ≤ normalizer (D : Set A)) (hsup : K ⊔ D = L)
    {p : ℕ} (hD : Nat.Coprime p (Nat.card D)) {z : A} (hzL : z ∈ L) (hz : z ^ p = 1) :
    z ∈ K := by
  have hKn : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hLK
  have hDL : D ≤ L := hsup ▸ le_sup_right
  have hz' : z ∈ ((K ⊔ D : Subgroup A) : Set A) := by rw [hsup]; exact hzL
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K D (hKL.trans hLD)] at hz'
  obtain ⟨k, hk, d, hd, hkd⟩ := Set.mem_mul.mp hz'
  set π : ↥L →* ↥L ⧸ K.subgroupOf L := QuotientGroup.mk' (K.subgroupOf L) with hπ
  have h1 : π ⟨z, hzL⟩ = π ⟨d, hDL hd⟩ := by
    have e : (⟨z, hzL⟩ : ↥L) = ⟨k, hKL hk⟩ * ⟨d, hDL hd⟩ := Subtype.ext hkd.symm
    have hk1 : π ⟨k, hKL hk⟩ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
    rw [e, map_mul, hk1, one_mul]
  have h2 : orderOf (π ⟨z, hzL⟩) ∣ p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have e : (⟨z, hzL⟩ : ↥L) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz)
    rw [e, map_one]
  have h3 : orderOf (π ⟨d, hDL hd⟩) ∣ Nat.card D :=
    (orderOf_map_dvd π _).trans (by rw [Subgroup.orderOf_mk]; exact D.orderOf_dvd_natCard hd)
  have h4 : orderOf (π ⟨z, hzL⟩) = 1 := Nat.eq_one_of_dvd_coprimes hD h2 (h1 ▸ h3)
  rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h4
  exact h4

end P614K64b

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

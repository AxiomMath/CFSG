module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.ClassicalInvolution.Basic
import CFSG.ClassicalInvolution.OrderForm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.Open CFSG.ComponentClassification.StandardRecognition

variable {G : Type} [Group G]

@[expose] def fzCClosure (z : G) (R : Subgroup G) : Subgroup G :=
  closure {x | ∃ g ∈ centralizer ({z} : Set G), ∃ a ∈ R, x = g * a * g⁻¹}

theorem le_fzCClosure (z : G) (R : Subgroup G) : R ≤ fzCClosure z R := fun a ha =>
  subset_closure ⟨1, one_mem _, a, ha, by simp⟩

theorem fzCClosure_le_centralizer {z : G} {R : Subgroup G} (hR : R ≤ centralizer ({z} : Set G)) :
    fzCClosure z R ≤ centralizer ({z} : Set G) := by
  rw [fzCClosure, closure_le]
  rintro x ⟨g, hg, a, ha, rfl⟩
  have hg' : g * z = z * g := mem_centralizer_singleton_iff.mp hg
  have ha' : a * z = z * a := mem_centralizer_singleton_iff.mp (hR ha)
  have hgi : g⁻¹ * z = z * g⁻¹ := by
    calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hg']
      _ = z * g⁻¹ := by group
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  calc g * a * g⁻¹ * z = g * a * (g⁻¹ * z) := by group
    _ = g * a * (z * g⁻¹) := by rw [hgi]
    _ = g * (a * z) * g⁻¹ := by group
    _ = g * (z * a) * g⁻¹ := by rw [ha']
    _ = (g * z) * a * g⁻¹ := by group
    _ = (z * g) * a * g⁻¹ := by rw [hg']
    _ = z * (g * a * g⁻¹) := by group

theorem centralizer_le_normalizer_fzCClosure (z : G) (R : Subgroup G) :
    centralizer ({z} : Set G) ≤ normalizer ((fzCClosure z R : Subgroup G) : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  have key : ∀ d ∈ centralizer ({z} : Set G), ∀ x ∈ fzCClosure z R,
      d * x * d⁻¹ ∈ fzCClosure z R := by
    intro d hd x hx
    induction hx using closure_induction with
    | mem y hy =>
      obtain ⟨g, hg, a, ha, rfl⟩ := hy
      exact subset_closure ⟨d * g, mul_mem hd hg, a, ha, by group⟩
    | one => simpa using one_mem _
    | mul y w _ _ hy hw =>
      have : d * (y * w) * d⁻¹ = (d * y * d⁻¹) * (d * w * d⁻¹) := by group
      rw [this]; exact mul_mem hy hw
    | inv y _ hy =>
      have : d * y⁻¹ * d⁻¹ = (d * y * d⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hy
  intro x
  constructor
  · exact key c hc x
  · intro hx
    have := key c⁻¹ (inv_mem hc) (c * x * c⁻¹) hx
    simpa [mul_assoc] using this

theorem fz_oddLie_or_mathieu_of_quaternion (hCIT : ClassicalInvolutionTheoremModels)
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2) {R : Subgroup G} (hzR : z ∈ R) (hRz : R ≤ centralizer ({z} : Set G))
    (hR : Nonempty (R ≃* QuaternionGroup 2)) (hsyl : ¬ 2 ∣ R.relIndex (fzCClosure z R)) :
    Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      Blueprint.NativeSporadic.IsSporadic G .M12 := by
  obtain ⟨e0⟩ := hR
  set J : Subgroup G := fzCClosure z R with hJ
  have hRJ : R ≤ J := le_fzCClosure z R
  have hzJ : z ∈ J := hRJ hzR
  have hJz : J ≤ centralizer ({z} : Set G) := fzCClosure_le_centralizer hRz
  have hnorm : (J.subgroupOf (centralizer ({z} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJz).2 (centralizer_le_normalizer_fzCClosure z R)
  have hsub : CFSG.Open.IsSubnormal J (centralizer ({z} : Set G)) :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hJz hnorm
  have hcard : Nat.card R = 2 ^ 3 := by
    rw [Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hR2 : IsPGroup 2 R := IsPGroup.of_card hcard
  have hle : R ≤ J := hRJ
  let eRJ : ↥(R.subgroupOf J) ≃* R := Subgroup.subgroupOfEquivOfLe hle
  have hRJ2 : IsPGroup 2 ↥(R.subgroupOf J) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr eRJ.toEquiv, hcard])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 J := hRJ2.toSylow (by simpa [Subgroup.relIndex] using hsyl)
  have hSeq : (S : Subgroup J) = R.subgroupOf J := IsPGroup.toSylow_coe _ _
  let eS : (S : Subgroup J) ≃* QuaternionGroup (2 ^ (3 - 2)) :=
    (MulEquiv.subgroupCongr hSeq).trans (eRJ.trans e0)
  have hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) :=
    ⟨3, le_rfl, ⟨eS⟩⟩
  have hTE : classicalInvolutionTightlyEmbedded J :=
    (CFSG.ClassicalInvolution.tightlyEmbedded_iff_centralizer_le_normalizer hzJ hz hJz S hS).2
      (centralizer_le_normalizer_fzCClosure z R)
  let eF : genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases (hCIT G hFnonab z hz J hzJ hsub S hS).2 hTE with h | h | h
  · exact .inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr (.inl ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))
  · exact .inr (.inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))

theorem catalog_of_oddLie_or_mathieu
    (h : Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      Blueprint.NativeSporadic.IsSporadic G .M12) : Blueprint.Catalog G := by
  rcases h with ⟨t, n, p, f, -, -, -, hm⟩ | h | h
  · exact Blueprint.lieModel_catalog G t n p f hm
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h⟩)))

theorem fz_catalog_of_quaternion (hCIT : ClassicalInvolutionTheoremModels)
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2) {R : Subgroup G} (hzR : z ∈ R) (hRz : R ≤ centralizer ({z} : Set G))
    (hR : Nonempty (R ≃* QuaternionGroup 2)) (hsyl : ¬ 2 ∣ R.relIndex (fzCClosure z R)) :
    Blueprint.Catalog G :=
  catalog_of_oddLie_or_mathieu (fz_oddLie_or_mathieu_of_quaternion hCIT hnonab hz hzR hRz hR hsyl)

end CFSG.OddStandard.SmallF3.FritzII

module

public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6Comm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher QuaternionGroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem eq_of_ne_one_of_card_dvd_two {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ∣ 2)
    {x y : Q} (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  by_contra hxy
  have hinj : Function.Injective (![1, x, y] : Fin 3 → Q) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have h3 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  have := Nat.le_of_dvd (by norm_num) hQ
  omega

variable {K : Type} [Field K] [Finite K]

theorem conj_mul_inv_mem_inner (h2 : (2 : K) ≠ 0) (x : MulAut (StatedProj (StatedSp 2 K)))
    {d : MulAut (StatedProj (StatedSp 2 K))} (hd : d ∈ spLinearAutGroup 2 K) :
    x * d * x⁻¹ * d⁻¹ ∈ inner (StatedProj (StatedSp 2 K)) := by
  classical
  obtain ⟨hE, -⟩ := RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2
  obtain ⟨hID, -, hDn, -, -, -⟩ := standard_outer_quotient (K := K) (r := 2) (by omega)
  set I := inner (StatedProj (StatedSp 2 K)) with hI
  set D := spLinearAutGroup 2 K with hD
  have hxD : x * d * x⁻¹ ∈ D := by
    have hx : x ∈ spSemilinearAutGroup 2 K := hE ▸ Subgroup.mem_top x
    have hd' : d ∈ spSemilinearAutGroup 2 K := hE ▸ Subgroup.mem_top d
    exact Subgroup.mem_subgroupOf.mp
      (hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨x, hx⟩)
  by_cases hdI : d ∈ I
  · exact I.mul_mem ((inferInstance : I.Normal).conj_mem d hdI x) (I.inv_mem hdI)
  have hxdI : x * d * x⁻¹ ∉ I := fun h => hdI (by
    have := (inferInstance : I.Normal).conj_mem _ h x⁻¹
    simpa [mul_assoc] using this)
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hcard⟩ := FiniteField.card K p
  have hK : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hdvd := relIndex_inner_spLinearAutGroup_dvd (r := 2) hp m.pos hK
  have hcard2 : Nat.card (D ⧸ I.subgroupOf D) ∣ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hdvd.trans (Nat.gcd_dvd_left 2 _)
  have key := eq_of_ne_one_of_card_dvd_two hcard2
    (x := QuotientGroup.mk (⟨x * d * x⁻¹, hxD⟩ : D)) (y := QuotientGroup.mk (⟨d, hd⟩ : D))
    (fun h => hxdI (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)))
    (fun h => hdI (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)))
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at key
  have hk : (x * d * x⁻¹)⁻¹ * d ∈ I := key
  have : x * d * x⁻¹ * d⁻¹ = d * ((x * d * x⁻¹)⁻¹ * d)⁻¹ * d⁻¹ := by group
  rw [this]
  exact (inferInstance : I.Normal).conj_mem _ (I.inv_mem hk) d

theorem commute_mul_of_central {Q : Type*} [Group Q] {A B D₁ D₂ : Q} (hAB : A * B = B * A)
    (h₁ : ∀ y, y * D₁ = D₁ * y) (h₂ : ∀ y, y * D₂ = D₂ * y) :
    A * D₁ * (B * D₂) = B * D₂ * (A * D₁) :=
  calc A * D₁ * (B * D₂) = A * (D₁ * B) * D₂ := by group
    _ = A * B * (D₁ * D₂) := by rw [← h₁ B]; group
    _ = B * A * (D₂ * D₁) := by rw [hAB, h₂ D₁]
    _ = B * (A * D₂) * D₁ := by group
    _ = B * D₂ * (A * D₁) := by rw [h₂ A]; group

theorem outer_comm (h2 : (2 : K) ≠ 0) (a b : Outer (StatedProj (StatedSp 2 K))) :
    a * b = b * a := by
  obtain ⟨hE, -⟩ := RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2
  obtain ⟨-, -, -, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := 2) (by omega)
  have hcen : ∀ {d : MulAut (StatedProj (StatedSp 2 K))}, d ∈ spLinearAutGroup 2 K →
      ∀ y : Outer (StatedProj (StatedSp 2 K)), y * (QuotientGroup.mk d : Outer _) =
        QuotientGroup.mk d * y := by
    intro d hd y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := (QuotientGroup.eq_one_iff (N := inner (StatedProj (StatedSp 2 K))) _).mpr
      (conj_mul_inv_mem_inner h2 x hd)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk x : Outer _) * QuotientGroup.mk d =
        (QuotientGroup.mk x * QuotientGroup.mk d * (QuotientGroup.mk x)⁻¹ *
          (QuotientGroup.mk d)⁻¹) * (QuotientGroup.mk d * QuotientGroup.mk x) := by group
      _ = QuotientGroup.mk d * QuotientGroup.mk x := by rw [h1, one_mul]
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨k, hk⟩ := hg α (hE ▸ Subgroup.mem_top α)
  obtain ⟨m, hm⟩ := hg β (hE ▸ Subgroup.mem_top β)
  have hα : (QuotientGroup.mk α : Outer (StatedProj (StatedSp 2 K))) =
      QuotientGroup.mk (g ^ (-k)) * QuotientGroup.mk (g ^ k * α) := by
    rw [← QuotientGroup.mk_mul, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  have hβ : (QuotientGroup.mk β : Outer (StatedProj (StatedSp 2 K))) =
      QuotientGroup.mk (g ^ (-m)) * QuotientGroup.mk (g ^ m * β) := by
    rw [← QuotientGroup.mk_mul, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
  rw [hα, hβ]
  refine commute_mul_of_central ?_ (hcen hk) (hcen hm)
  rw [QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
  exact (Commute.zpow_zpow_self _ _ _).eq

theorem not_injective_outer (h2 : (2 : K) ≠ 0) {N : Type} [Group N]
    (e : N ≃* StatedProj (StatedSp 2 K)) (φ : QuaternionGroup 2 →* Outer N) :
    ¬ Function.Injective φ := by
  intro hφ
  let ψ := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toMonoidHom.comp φ
  have hψ : Function.Injective ψ :=
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective.comp hφ
  have h := outer_comm h2 (ψ (a 1)) (ψ (xa 0))
  rw [← map_mul, ← map_mul] at h
  exact absurd (hψ h) (by decide)

end CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

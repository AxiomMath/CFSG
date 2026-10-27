module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCG28
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

variable {B : Type} [Group B] [Finite B] {K : Subgroup B} [K.Normal]

theorem eq_of_wclosedIn (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1)
    (hinnT : ∀ (T : Sylow 3 K) (φ : MulAut K), φ ^ 3 = 1 →
      (∀ t ∈ (T : Subgroup K), φ t = t) → ∃ g : K, ∀ x : K, φ x = g * x * g⁻¹)
    (hcent : ∀ (T : Sylow 3 K) (a b : K), a ∈ (T : Subgroup K) → b ∈ (T : Subgroup K) →
      orderOf a = 3 → orderOf b = 3 → (∀ t ∈ (T : Subgroup K), t * a * t⁻¹ = a) →
      (∀ t ∈ (T : Subgroup K), t * b * t⁻¹ = b) → b ∈ zpowers a)
    (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
    (A A' : Subgroup (MulAut.conjNormal (H := K)).range) (hA3 : Nat.card A = 3)
    (hA'3 : Nat.card A' = 3)
    (Y : Subgroup (MulAut.conjNormal (H := K)).range)
    (hSY : (S : Subgroup (MulAut.conjNormal (H := K)).range) ≤ Y)
    (hwc : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y)
    (hwc' : IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A' Y) : A' = A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hι := innHom_injective hZ
  obtain ⟨a, haT, ha3, hac, hAa⟩ := exists_inner_of_wclosedIn hZ hinnT S A hA3 Y hSY hwc
  obtain ⟨b, hbT, hb3, hbc, hAb⟩ := exists_inner_of_wclosedIn hZ hinnT S A' hA'3 Y hSY hwc'
  set T₀ := (S : Subgroup (MulAut.conjNormal (H := K)).range).comap (innHom K)
  have hmap : T₀.map (innHom K) = (innHom K).range ⊓ S := Subgroup.map_comap_eq _ _
  have hcardT₀ : Nat.card T₀ = 3 ^ (Nat.card K).factorization 3 := by
    have hN : ((innHom K).range).Normal := by
      constructor
      rintro _ ⟨k, rfl⟩ r
      refine ⟨(r : MulAut K) k, Subtype.ext (MulEquiv.ext fun x => ?_)⟩
      apply Subtype.ext
      obtain ⟨y, rfl⟩ := (r : MulAut K).surjective x
      simp [innHom_apply, MulAut.mul_apply]
    rw [← Subgroup.card_map_of_injective hι, hmap,
      CFSG.Quasithin.card_inf_normal_of_sylow (S : Subgroup _) (innHom K).range
        S.card_eq_multiplicity, ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
  let T : Sylow 3 K := Sylow.ofCard T₀ hcardT₀
  have hba := hcent T a b haT hbT ha3 hb3 hac hbc
  have hle : A' ≤ A := by
    rw [hAa, hAb, zpowers_le, ← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_of_mem _ hba
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA3, hA'3])

theorem kFactTenNineWCGammaG28Uniq_of
    (h : KFactG28SylowCenter) :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal], IsCaseIThreeG28 K →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        (S : Subgroup (MulAut.conjNormal (H := K)).range) ≤ Y →
        IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y →
        ∀ A' : Subgroup (MulAut.conjNormal (H := K)).range, Nat.card A' = 3 →
          IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A' Y → A' = A := by
  intro B _ _ K _ hK S A Y hA3 hSY hwc A' hA'3 hwc'
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨hZ, hinnT⟩ := g28_hZ_hinnT d hd e
  exact eq_of_wclosedIn hZ hinnT (h K ⟨d, hd, ⟨e⟩⟩) S A A' hA3 hA'3 Y hSY hwc hwc'

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC

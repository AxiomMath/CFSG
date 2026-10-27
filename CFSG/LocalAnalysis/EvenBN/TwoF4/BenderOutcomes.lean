module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesSp4
public import CFSG.LocalAnalysis.EvenBN.GMSK.StatementBender
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.SteinbergBV
open CFSG.ABGLocalTools (IsSylowOf)

variable {H : Type} [Group H]

theorem not_isSimpleGroup_of_equiv_prod {D A : Type*} [Group D] [Group A] [Nontrivial A]
    (ψ : D ≃* A × A) : ¬ IsSimpleGroup D := by
  intro hD
  have : IsSimpleGroup (A × A) := ψ.symm.isSimpleGroup
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  set N : Subgroup (A × A) := (⊤ : Subgroup A).prod (⊥ : Subgroup A) with hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have hm : ((a, 1) : A × A) ∈ N := mem_prod.mpr ⟨mem_top a, one_mem _⟩
    rw [h, mem_bot] at hm
    exact ha (congrArg Prod.fst hm)
  · have hm : ((1, a) : A × A) ∈ N := by
      rw [h]
      exact mem_top _
    exact ha (mem_bot.mp (mem_prod.mp hm).2)

theorem benderSylow_of_sharpOutcome_suzuki [Finite H] {A : Subgroup H} {t : H} {n : ℕ}
    (hS : GMSK.SharpOutcome (fun D _ => LieModel D .PSp 2 2 n) H A t) (htt : t * t = 1)
    (hodd : Odd n) (h3 : 3 ≤ n) (hAt : A ≤ centralizer ({t} : Set H)) {V : Subgroup H}
    (hV : IsSylowOf 2 V A) (hVcard : Nat.card V = 2 ^ (2 * n))
    (h1 : ∀ z ∈ zIn V, z * z = 1) (h2 : ∀ c ∈ V, c * c ∈ ⁅V, V⁆) (h3' : ⁅V, V⁆ ≤ zIn V)
    (h4 : ∀ v ∈ V, v * v = 1 → v ∈ zIn V) :
    ∃ W : Subgroup H, BenderSylow (CFSG.layer H) t V W := by
  have : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨⟨-, -, hAL, hDE, -, halt, -⟩, hsimple⟩ := hS
  rw [hDE] at halt
  have hVA : V ≤ A := hV.le
  rcases halt with ⟨⟨hDs, -, -, -⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hψ₁, hψ₂⟩, -⟩
  · obtain ⟨hn, hout⟩ := hsimple hDs
    exact benderSylow_of_symplectic htt hn hodd h3 hout (le_inf (hVA.trans hAL) (hVA.trans hAt))
      hV.isPGroup hVcard
  · have : Nontrivial A := by
      rw [nontrivial_iff_ne_bot]
      intro hA
      have hV1 : V = ⊥ := le_bot_iff.mp (hA ▸ hVA)
      rw [hV1, card_bot] at hVcard
      exact absurd hVcard.symm (Nat.one_lt_two_pow (by omega)).ne'
    refine ⟨_, benderSylow_of_two_factor htt hAL (fun d hd => ?_) ψ hψ₁ hψ₂ hV h1 h2 h3' h4⟩
    simpa using (inferInstance : (CFSG.layer H).Normal).conj_mem d hd t⁻¹

end CFSG.LocalAnalysis.EvenBN.TwoF4

end

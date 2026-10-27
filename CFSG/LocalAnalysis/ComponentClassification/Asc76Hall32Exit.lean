module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32CaseB
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

theorem exists_exit_step {p : ℕ} {S P : Subgroup G} {A : Set G} {c x : G}
    (h : CFSG.RankTwoShapes.AlperinDecomposition p S P c) (hx : x ∈ P) (hxA : x ∈ A)
    (hcx : c⁻¹ * x * c ∉ A) :
    ∃ Q : Subgroup G, CFSG.RankTwoShapes.IsAlperinSubgroup p S Q ∧ ∃ d : G,
      d⁻¹ * x * d ∈ Q ∧ d⁻¹ * x * d ∈ A ∧
      ∃ n ∈ normalizer (Q : Set G), n⁻¹ * (d⁻¹ * x * d) * n ∉ A := by
  induction h with
  | one => exact absurd (by simpa using hxA) hcx
  | @step c n Q _ hQ hPQ hn ih =>
    by_cases hc : c⁻¹ * x * c ∈ A
    · refine ⟨Q, hQ, c, hPQ ⟨x, hx, by simp⟩, hc, n, hn, ?_⟩
      have e : n⁻¹ * (c⁻¹ * x * c) * n = (c * n)⁻¹ * x * (c * n) := by group
      rw [e]
      exact hcx
    · exact ih hc

variable [Finite G]

theorem exists_conj_centralizer_le {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {z g : G}
    (hzS : ∀ s ∈ S, s * z = z * s) :
    ∃ k : G, k⁻¹ * z * k = g⁻¹ * z * g ∧
      S ⊓ centralizer ({g⁻¹ * z * g} : Set G) ≤ rightConjugate S k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  set u := g⁻¹ * z * g with hudef
  set C := centralizer ({u} : Set G) with hCdef
  have hSgC : rightConjugate S g ≤ C := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    rw [hCdef, mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := hzS _ hx
    calc u * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [hudef]; group
      _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [h1]
      _ = x * u := by rw [hudef]; group
  have htop : rightConjugate (⊤ : Subgroup G) g = ⊤ := by
    rw [rightConjugate_eq_self_iff, normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top g
  have hSg' : IsSylowOf 2 (rightConjugate S g) ⊤ := by
    have h := isSylowOf_rightConjugate hS g
    rwa [htop] at h
  have hSg : IsSylowOf 2 (rightConjugate S g) C := isSylowOf_of_le hSgC le_top hSg'
  have hCS2 : IsPGroup 2 ↥(S ⊓ C) := hS2.to_le inf_le_left
  obtain ⟨Q, hQ, hCSQ⟩ := exists_isSylowOf_le (inf_le_right : S ⊓ C ≤ C) hCS2
  obtain ⟨c, hc, hQc⟩ := exists_conj_of_isSylowOf hSg hQ
  refine ⟨g * c, ?_, ?_⟩
  · have hcu : c⁻¹ * u * c = u := by
      have h1 := mem_centralizer_iff.mp hc u (Set.mem_singleton u)
      rw [mul_assoc, h1, inv_mul_cancel_left]
    calc (g * c)⁻¹ * z * (g * c) = c⁻¹ * u * c := by rw [hudef]; group
      _ = u := hcu
  · rw [← rightConjugate_mul, ← hQc]
    exact hCSQ

theorem stronglyClosed_of_central {X : Type} [Group X] [Finite X] {S T : Subgroup X}
    (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hT4 : Nat.card T = 4) (hTsq : ∀ x ∈ T, x ^ 2 = 1)
    (hwc : ∀ g : X, rightConjugate T g ≤ S → rightConjugate T g = T) {z : X} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzc : ∀ g : X, g * z = z * g) :
    ∀ τ ∈ T, ∀ g : X, g⁻¹ * τ * g ∈ S → g⁻¹ * τ * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro τ hτ g hg
  obtain ⟨S', hS'⟩ := exists_sylow_eq_of_isSylowOf_top hS
  have hP : zpowers τ ≤ (S' : Subgroup X) := by rw [hS']; exact zpowers_le.mpr (hTS hτ)
  have hPg : (zpowers τ).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S' : Subgroup X) := by
    rw [MonoidHom.map_zpowers, hS']
    exact zpowers_le.mpr (by simpa [MulAut.conj_apply] using hg)
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S' hP hPg
  rw [← hcg τ (mem_zpowers τ)]
  rw [hS'] at hc
  clear hcg hPg hP hg
  induction hc with
  | one => simpa using hτ
  | @step c n Q _ hQ hPQ hn ih =>
    set y := c⁻¹ * τ * c with hydef
    have hyQ : y ∈ Q := hPQ ⟨τ, mem_zpowers τ, by simp [hydef]⟩
    have hzQ : z ∈ Q := hQ.2.2.1 ⟨mem_centralizer_iff.mpr fun q _ => hzc q, hTS hzT⟩
    have e : (c * n)⁻¹ * τ * (c * n) = n⁻¹ * y * n := by rw [hydef]; group
    rw [e]
    by_cases hy1 : y = 1
    · rw [hy1, mul_one, inv_mul_cancel]
      exact one_mem T
    by_cases hyz : y = z
    · rw [hyz, mul_assoc, ← hzc n, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hzT
    have hTQ : T ≤ Q := fun x hx => by
      rcases eq_or_of_card_four hT4 hTsq hzT ih hz1 hy1 hyz hx with rfl | rfl | rfl | rfl
      · exact one_mem Q
      · exact hzQ
      · exact hyQ
      · exact mul_mem hyQ hzQ
    have hnT := normalizer_le_of_weaklyClosed hTQ hQ.1 hwc hn
    have h1 := (mem_normalizer_iff.mp (inv_mem hnT) y).mp ih
    simpa using h1

theorem exists_conj_sdiff_centralizer {S T : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (hT4 : Nat.card T = 4) (hTel : IsElemAbelian 2 T)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hns : ∃ t ∈ T, ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ∉ T) {z : G} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzS : ∀ s ∈ S, s * z = z * s) :
    ∃ n : G, n⁻¹ * z * n ∈ S ∧ n⁻¹ * z * n ∉ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 : (⟨a, ha⟩ : ↥T) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := hTel.1.is_comm.comm _ _
    simpa using congrArg Subtype.val h1
  have hTsq : ∀ x ∈ T, x ^ 2 = 1 := hTel.2
  have hSN := le_normalizer_of_weaklyClosed hTS hwc
  obtain ⟨t₀, ht₀, g, hgS, hgT⟩ := hns
  obtain ⟨S', hS'⟩ := exists_sylow_eq_of_isSylowOf_top hS
  have hP : zpowers t₀ ≤ (S' : Subgroup G) := by rw [hS']; exact zpowers_le.mpr (hTS ht₀)
  have hPg : (zpowers t₀).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S' : Subgroup G) := by
    rw [MonoidHom.map_zpowers, hS']
    exact zpowers_le.mpr (by simpa [MulAut.conj_apply] using hgS)
  obtain ⟨c, hc, hcg⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S' hP hPg
  have hcT : c⁻¹ * t₀ * c ∉ (T : Set G) := by
    rw [hcg t₀ (mem_zpowers t₀)]
    exact hgT
  obtain ⟨Q, hQ, d, hyQ, hyT, n, hn, hwT⟩ := exists_exit_step hc (mem_zpowers t₀) ht₀ hcT
  rw [hS'] at hQ
  set y := d⁻¹ * t₀ * d with hydef
  set w := n⁻¹ * y * n with hwdef
  have hyT' : y ∈ T := hyT
  have hwT' : w ∉ T := hwT
  have hwQ : w ∈ Q := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) y).mp hyQ
    simpa [hwdef] using h1
  have hwS : w ∈ S := hQ.1 hwQ
  have hwC : w ∉ centralizer (T : Set G) := fun hw =>
    hwT' (conj_mem_of_mem_centralizer hS hTS hTab hwc hyT' hw)
  have hy1 : y ≠ 1 := by
    intro h1
    apply hwT'
    rw [hwdef, h1, mul_one, inv_mul_cancel]
    exact one_mem T
  have hTQ : ¬ T ≤ Q := by
    intro hTQ
    have hnT := normalizer_le_of_weaklyClosed hTQ hQ.1 hwc hn
    have h1 := (mem_normalizer_iff.mp (inv_mem hnT) y).mp hyT'
    exact hwT' (by simpa [hwdef] using h1)
  have hwy : w * y = y * w := by
    by_contra hne
    set a := w * y * w⁻¹ with hadef
    have haT : a ∈ T := (mem_normalizer_iff.mp (hSN hwS) y).mp hyT'
    have haQ : a ∈ Q := mul_mem (mul_mem hwQ hyQ) (inv_mem hwQ)
    have ha1 : a ≠ 1 := fun h1 => hy1 (by
      have e : y = w⁻¹ * a * w := by rw [hadef]; group
      rw [e, h1, mul_one, inv_mul_cancel])
    have hay : a ≠ y := fun h1 => hne (by
      calc w * y = a * w := by rw [hadef]; group
        _ = y * w := by rw [h1])
    apply hTQ
    intro x hx
    rcases eq_or_of_card_four hT4 hTsq hyT' haT hy1 ha1 hay hx with rfl | rfl | rfl | rfl
    · exact one_mem Q
    · exact hyQ
    · exact haQ
    · exact mul_mem haQ hyQ
  have hyz : y = z := by
    by_contra hyz
    exact hwC (mem_centralizer_of_comm hT4 hTsq hzT hyT' hz1 hy1 hyz (hzS w hwS).symm hwy.symm)
  refine ⟨n, ?_, ?_⟩
  · rw [← hyz]; exact hwS
  · rw [← hyz]; exact hwC

end CFSG.ComponentClassification.Asc76X.Hall32

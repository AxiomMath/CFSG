module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10_mem_tB_of_not_mem {t : G} {B L : Subgroup G} (hBL : B ≤ L) (ht2 : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {x : G} (hx : x ∈ B ⊔ zpowers t) (hxL : x ∉ L) :
    x ∈ cosetSet t B := by
  have hcomm : ∀ b ∈ B, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_iff.1 htC b (hBL hb)
  obtain ⟨b, hb, i, rfl⟩ := (mem_sup_zpowers_iff_of_commute hcomm).1 hx
  have hti : t ^ i = t ^ (i % 2) := by
    have h := zpow_mod_orderOf t i
    rw [ht2] at h
    exact_mod_cast h.symm
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · exfalso
    apply hxL
    rw [hti, h, zpow_zero, mul_one]
    exact hBL hb
  · refine ⟨b, hb, ?_⟩
    rw [hti, h, zpow_one]
    exact hcomm b hb

theorem sec10_B_normal {t z : G} {L S : Subgroup G} (hBD : Sec10BData t L S)
    (ht2 : orderOf t = 2) (htC : t ∈ centralizer (L : Set G)) (hz : IsI4PlusIn L z)
    (hzc : ∀ b ∈ secB S L, b * z = z * b) (h105 : ∃ g : G, g⁻¹ * t * g = t * z)
    (h108 : ∀ g : G, g⁻¹ * t * g ∉ L) :
    ∀ m ∈ secM t S L, ∀ b ∈ secB S L, m * b * m⁻¹ ∈ secB S L := by
  obtain ⟨hBL, -, hBC, -, hML, φ, ⟨hadd, hinj, himg, hact, hsurj⟩, -, h2, -⟩ := hBD
  have hcomm : ∀ b ∈ secB S L, b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_iff.1 htC b (hBL hb)
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have hφ1 : φ 0 = 1 := by
    have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have := hadd 0 0 h0 h0
    simpa using this
  have hzB : z ∈ secB S L := by
    have : z ∈ centralizer (secB S L : Set G) ⊓ L :=
      ⟨Subgroup.mem_centralizer_iff.2 fun b hb => hzc b hb, hz.mem⟩
    rwa [hBC] at this
  obtain ⟨v, hv, hφv⟩ := (himg z).1 hzB
  have hv4 : vecWeight v = 4 := by
    rcases even_weight_cases_five v hv with h0 | h02 | h04
    · exfalso
      have := hz.1
      rw [← hφv, h0, hφ1, orderOf_one] at this
      omega
    · exact absurd (hφv ▸ hz) (h2 v hv h02)
    · exact h04
  let T : Set G := {x | (∃ g : G, x = g⁻¹ * t * g) ∧ x ∈ secA t S L}
  let N : Subgroup G := Subgroup.closure {y | ∃ x ∈ T, ∃ x' ∈ T, y = x * x'}
  have hTM : ∀ m ∈ secM t S L, ∀ x ∈ T, m * x * m⁻¹ ∈ T := by
    rintro m hm x ⟨⟨g, rfl⟩, hxA⟩
    refine ⟨⟨g * m⁻¹, by group⟩, ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 hm _).1 hxA
  have htT : t ∈ T := ⟨⟨1, by simp⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
  have htzT : t * z ∈ T := by
    obtain ⟨g, hg⟩ := h105
    exact ⟨⟨g, hg.symm⟩, Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left hzB)⟩
  have hNB : N ≤ secB S L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, ⟨⟨g, rfl⟩, hxA⟩, x', ⟨⟨g', rfl⟩, hxA'⟩, rfl⟩
    obtain ⟨b, hb, hxb⟩ :=
      sec10_mem_tB_of_not_mem hBL ht2 htC hxA (h108 g)
    obtain ⟨b', hb', hxb'⟩ :=
      sec10_mem_tB_of_not_mem hBL ht2 htC hxA' (h108 g')
    rw [hxb, hxb']
    have : t * b * (t * b') = b * b' := by
      calc t * b * (t * b') = t * (b * t) * b' := by group
        _ = t * (t * b) * b' := by rw [hcomm b hb]
        _ = (t * t) * (b * b') := by group
        _ = b * b' := by rw [htt, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hb hb'
  have hφ4 : ∀ u, vecWeight u = 4 → φ u ∈ N := by
    intro u hu
    obtain ⟨σ, hσ, hσu⟩ := exists_alt_permVec_weight_four v u hv4 hu
    obtain ⟨h, hh, hspec⟩ := hsurj σ hσ
    have hhM : h ∈ secM t S L ⊓ L := by rw [hML]; exact hh
    have hht : h * t = t * h := Subgroup.mem_centralizer_iff.1 htC h hhM.2
    have hφu : φ u = t * (h * (t * z) * h⁻¹) := by
      rw [← hσu, ← hspec v hv, hφv]
      calc h * z * h⁻¹ = h * (t * (t * z)) * h⁻¹ := by rw [← mul_assoc t t z, htt, one_mul]
        _ = (h * t * h⁻¹) * (h * (t * z) * h⁻¹) := by group
        _ = t * (h * (t * z) * h⁻¹) := by rw [hht]; group
    rw [hφu]
    exact Subgroup.subset_closure ⟨t, htT, _, hTM h hhM.1 _ htzT, rfl⟩
  have hBN : secB S L ≤ N := by
    intro b hb
    obtain ⟨w, hw, rfl⟩ := (himg b).1 hb
    rcases even_weight_cases_five w hw with h0 | h02 | h04
    · rw [h0, hφ1]; exact N.one_mem
    · obtain ⟨x, y, hx, hy, rfl⟩ := weight_two_sum_five w h02
      rw [hadd x y (isEvenVec_of_weight_four x hx) (isEvenVec_of_weight_four y hy)]
      exact N.mul_mem (hφ4 x hx) (hφ4 y hy)
    · exact hφ4 w h04
  have hBeq : N = secB S L := le_antisymm hNB hBN
  intro m hm b hb
  rw [← hBeq] at hb ⊢
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨x, hx, x', hx', rfl⟩ := hy
      exact Subgroup.subset_closure
        ⟨m * x * m⁻¹, hTM m hm x hx, m * x' * m⁻¹, hTM m hm x' hx', by group⟩
  | one => simpa using N.one_mem
  | mul y y' _ _ ihy ihy' =>
      have : m * (y * y') * m⁻¹ = (m * y * m⁻¹) * (m * y' * m⁻¹) := by group
      rw [this]
      exact N.mul_mem ihy ihy'
  | inv y _ ihy =>
      have : m * y⁻¹ * m⁻¹ = (m * y * m⁻¹)⁻¹ := by group
      rw [this]
      exact N.inv_mem ihy

theorem asc82Lemma1010_of (h105 : Asc82Lemma105) (h108 : Asc82Lemma108) (hb : Asc82Basic10)
    (hf : Asc82Facts10) : Asc82Lemma1010 := by
  intro G _ _ t L S z K1 K2 hctx
  obtain ⟨-, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hBD := sec10BData_of hb hf.b5 hctx.toSec10Z
  have ht2 : orderOf t = 2 := hctx.involution
  have h108' := h108 G t L S z K1 K2 hctx
  refine ⟨sec10_B_normal hBD ht2 htC hctx.pocket
    (fun b hb => hctx.central b (secB_le_S S L hb)) (h105 G t L S z K1 K2 hctx) h108', ?_⟩
  intro g hg
  exact sec10_mem_tB_of_not_mem (secB_le_L S L) ht2 htC hg (h108' g)

end CFSG.OddStandard.SmallF3.Omega

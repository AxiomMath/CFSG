module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Central26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Beta26

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding
open CFSG.ComponentClassification.AschbacherToolkit

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}
  {R : Subgroup G}

theorem concl26_main (IH : Statement26 (Nat.card G - 1)) (h : Hyp26 S 𝒯 R) : Concl26 𝒯 R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hH : fusionGen (memberSet 𝒯) = ⊤
  · exact Or.inl hH
  by_cases hO : CFSG.Assembly.oddCore G = ⊥
  swap
  · exact concl26_of_oddCore_ne_bot IH h hO
  by_cases hZ : ∃ u ∈ center G, orderOf u = 2
  · obtain ⟨u, hu, hu2⟩ := hZ
    exact concl26_of_central IH h hO hu hu2
  push Not at hZ
  set Γ := memberSet 𝒯 with hΓdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h.toHypCore
  have hRS : R ≤ S := h.le R h.mem
  have hR2 : IsPGroup 2 R := h.sylow.isPGroup.to_le hRS
  obtain ⟨E, hER, hE4, -⟩ := exists_four_le h.big.1
  have hR1 : R ≠ ⊥ := by
    intro h'
    have h1 := Subgroup.card_le_of_le hER
    rw [h', Subgroup.card_bot] at h1
    omega
  have hZR := inf_center_ne_bot_of_le hR2 le_rfl le_normalizer hR1
  obtain ⟨a, haZR, ha2⟩ := BenderExt.ExtCore.exists_orderOf_eq_two
    (A := R ⊓ (R ⊓ centralizer (R : Set G))) hR2 inf_le_left hZR
  have haR : a ∈ R := (mem_inf.mp haZR).1
  have haZ : ∀ p ∈ R, p * a = a * p := fun p hp =>
    mem_centralizer_iff.mp (mem_inf.mp (mem_inf.mp haZR).2).2 p hp
  have ha1 : a ≠ 1 := fun h' => by rw [h', orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := mem_memberSet h.mem haR ha1
  by_cases hpuc : ProductUniqueContainment H a
  · exact Or.inr (alpha26 h hH hO hZ haR ha2 hpuc)
  exfalso
  simp only [ProductUniqueContainment, not_forall] at hpuc
  obtain ⟨t, ht, hat, hta, g, hg⟩ := hpuc
  have haH : a ∈ H := mem_fusionGen_of_mem haΓ
  have htH : t ∈ H := centralizer_le_fusionGen haΓ (mem_centralizer_singleton_iff.mpr hat.eq.symm)
  have hatH : a * t ∈ H := H.mul_mem haH htH
  have hgH : g ∉ H := fun hgH =>
    hg ⟨fun _ => hgH, fun _ => H.mul_mem (H.mul_mem (H.inv_mem hgH) hatH) hgH⟩
  have hgat : g⁻¹ * (a * t) * g ∈ H := by
    by_contra hn
    exact hg ⟨fun h' => absurd h' hn, fun h' => absurd h' hgH⟩
  obtain ⟨k₀, hk₀⟩ := ht
  have htk : t = k₀⁻¹ * a * k₀ := by rw [← hk₀]; rfl
  have haa : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have htt : t * t = 1 := by
    rw [htk]
    calc k₀⁻¹ * a * k₀ * (k₀⁻¹ * a * k₀) = k₀⁻¹ * (a * a) * k₀ := by group
      _ = 1 := by rw [haa]; group
  have hA2 : IsPGroup 2 (S ⊓ centralizer ({a} : Set G) : Subgroup G) :=
    h.sylow.isPGroup.to_le inf_le_left
  obtain ⟨Q, hQ, hAQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hA2 inf_le_right
  have ht1 : t ≠ 1 := fun h' => ha1 (by
    rw [htk] at h'
    have : a = k₀ * (k₀⁻¹ * a * k₀) * k₀⁻¹ := by group
    rw [this, h']; group)
  set V := commutingPairSubgroup a t haa htt hat with hVdef
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (commutingPairSubgroup_card ha1 ht1 (Ne.symm hta))
  have hVC : V ≤ centralizer ({a} : Set G) := by
    intro v hv
    rw [mem_centralizer_singleton_iff]
    rcases mem_commutingPairSubgroup.mp hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · rfl
    · exact hat.eq.symm
    · calc a * t * a = a * (t * a) := by group
        _ = a * (a * t) := by rw [hat.eq]
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hQ hV2 hVC
  have hca : c * a = a * c := mem_centralizer_singleton_iff.mp hc
  have hcH : c ∈ H := centralizer_le_fusionGen haΓ hc
  set t' := c⁻¹ * t * c with ht'def
  have ht'Q : t' ∈ Q := hcle (by
    rw [mem_rightConjugate_iff, ht'def]
    have : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
    rw [this]
    exact mem_commutingPairSubgroup.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hSH : S ≤ H := le_fusionGen h.closed hΓS ⟨a, haΓ⟩
  have haQ : a ∈ Q := hAQ (mem_inf.mpr ⟨hRS haR, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hQH : Q ≤ H := by
    obtain ⟨c', -, hc'⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf h.sylow
      hQ.isPGroup le_top
    have hle := rightConjugate_mono (hc'.trans hSH) c'⁻¹
    rw [rightConjugate_inv] at hle
    have hac : a ∈ rightConjugate H c'⁻¹ := hle haQ
    rw [mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS haΓ] at hac
    intro q hq
    have hq' := hle hq
    rw [mem_rightConjugate_iff] at hq'
    have hq'' := H.mul_mem (H.mul_mem (H.inv_mem hac) hq') hac
    simpa [mul_assoc] using hq''
  obtain ⟨h₀, hh₀, hQS⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
    (h.sylow.of_le hSH le_top) hQ.isPGroup hQH
  have hmemQ : ∀ y ∈ Q, h₀⁻¹ * y * h₀ ∈ S := fun y hy => hQS (by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hy)
  have hRQ : R ≤ Q := fun r hr => hAQ (mem_inf.mpr ⟨hRS hr, mem_centralizer_singleton_iff.mpr
    (haZ r hr)⟩)
  have hP₁S : rightConjugate R h₀ ≤ S := fun y hy => by
    rw [mem_rightConjugate_iff] at hy
    have := hmemQ _ (hRQ hy)
    simpa [mul_assoc] using this
  have hconj_comm : ∀ {u v : G}, u * v = v * u →
      (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by
    intro u v huv
    calc (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = h₀⁻¹ * (u * v) * h₀ := by group
      _ = h₀⁻¹ * (v * u) * h₀ := by rw [huv]
      _ = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by group
  have hac' : a * c⁻¹ = c⁻¹ * a := by
    calc a * c⁻¹ = c⁻¹ * (c * a) * c⁻¹ := by group
      _ = c⁻¹ * (a * c) * c⁻¹ := by rw [hca]
      _ = c⁻¹ * a := by group
  have hat'a : a * t' = c⁻¹ * (a * t) * c := by
    rw [ht'def]
    calc a * (c⁻¹ * t * c) = (a * c⁻¹) * t * c := by group
      _ = (c⁻¹ * a) * t * c := by rw [hac']
      _ = c⁻¹ * (a * t) * c := by group
  have hat' : a * t' = t' * a := by
    calc a * t' = c⁻¹ * (a * t) * c := hat'a
      _ = c⁻¹ * (t * a) * c := by rw [hat.eq]
      _ = c⁻¹ * t * (a * c) := by group
      _ = c⁻¹ * t * (c * a) := by rw [hca]
      _ = t' * a := by rw [ht'def]; group
  refine false_of_beta26 IH h.toHypCore hZ (P := rightConjugate R h₀) (h.conj h₀ hP₁S)
    (h.big.rightConjugate h₀)
    (fun g' hg' => by
      rw [rightConjugate_mul] at hg' ⊢
      exact h.conj _ hg')
    (a := h₀⁻¹ * a * h₀) (b := h₀⁻¹ * t' * h₀)
    (by rw [mem_rightConjugate_iff]; simpa [mul_assoc] using haR)
    (fun p hp => by
      rw [mem_rightConjugate_iff] at hp
      have := hconj_comm (haZ _ hp)
      simpa [mul_assoc] using this)
    (by rw [show h₀⁻¹ * a * h₀ = MulAut.conj h₀⁻¹ a by simp, MulEquiv.orderOf_eq]; exact ha2)
    (hmemQ _ ht'Q) (w := h₀⁻¹ * (k₀ * c) * h₀) (by rw [ht'def, htk]; group) (hconj_comm hat')
    (fun h' => hta (by
      have h2 : t' = a := by
        have := congrArg (fun y => h₀ * y * h₀⁻¹) h'
        simpa [mul_assoc] using this
      calc t = c * t' * c⁻¹ := by rw [ht'def]; group
        _ = c * a * c⁻¹ := by rw [h2]
        _ = a * c * c⁻¹ := by rw [hca]
        _ = a := by group))
    (k := g⁻¹ * c * h₀) (fun h' => hgH (by
      have h1 := H.mul_mem h' (H.mul_mem (H.inv_mem hh₀) (H.inv_mem hcH))
      have h2 : g⁻¹ * c * h₀ * (h₀⁻¹ * c⁻¹) = g⁻¹ := by group
      rw [h2] at h1
      exact H.inv_mem_iff.mp h1)) ?_
  have e : g⁻¹ * c * h₀ * (h₀⁻¹ * a * h₀ * (h₀⁻¹ * t' * h₀)) * (g⁻¹ * c * h₀)⁻¹ =
      g⁻¹ * (a * t) * g := by
    have : h₀⁻¹ * a * h₀ * (h₀⁻¹ * t' * h₀) = h₀⁻¹ * (a * t') * h₀ := by group
    rw [this, hat'a]
    group
  rw [e]
  exact hgat

omit [Finite G] in
theorem statement26_all : ∀ n, Statement26 n := by
  intro n
  induction n with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hX S' 𝒯' R' h
    by_cases hle : Nat.card X ≤ n
    · exact ih X hle S' 𝒯' R' h
    have IH : Statement26 (Nat.card X - 1) := fun Y _ _ hY => ih Y (by omega)
    exact concl26_main IH h

theorem asc76Lemma26 : Asc76Lemma26 := asc76Lemma26_of statement26_all

end CFSG.ComponentClassification.Asc76.L26

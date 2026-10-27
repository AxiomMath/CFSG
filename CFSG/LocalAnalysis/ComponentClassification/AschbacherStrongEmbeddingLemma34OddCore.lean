module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Minimal

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem exists_conj_mem_of_mem_sup {N : Subgroup G} [N.Normal] {x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hx : x ∈ (S : Subgroup G) ⊔ N) :
    ∃ n ∈ N, n⁻¹ * x * n ∈ (S : Subgroup G) := by
  obtain ⟨m, hm, hmS⟩ := exists_conj_le_sylow (S := S) (H := (S : Subgroup G) ⊔ N) le_sup_left
    (Subgroup.zpowers_le.mpr hx) hx2
  obtain ⟨s, hs, n', hn', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  refine ⟨s * n' * s⁻¹, (inferInstance : N.Normal).conj_mem n' hn' s, ?_⟩
  have h1 := hmS x (Subgroup.mem_zpowers x)
  have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h1) (Subgroup.inv_mem _ hs)
  rwa [show s * ((s * n')⁻¹ * x * (s * n')) * s⁻¹ = (s * n' * s⁻¹)⁻¹ * x * (s * n' * s⁻¹) by
    group] at h2

theorem isPGroup_zpowers_conj (h : Hyp S A₁ A₂) {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (g : G) :
    IsPGroup 2 (Subgroup.zpowers (g⁻¹ * a * g)) := by
  have haS : a ∈ (S : Subgroup G) := by
    rcases ha with ha | ha
    · exact h.le_one ha
    · exact h.le_two ha
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one S.isPGroup' haS
  have hord : orderOf (g⁻¹ * a * g) = orderOf a := by
    rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord, hk])

omit [Finite G] in
theorem inf_eq_bot_of_odd {P N : Subgroup G} (hP : IsPGroup 2 P) (hN : Odd (Nat.card N)) :
    P ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one hP hx.1
  have hdvd₁ : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hdvd₂ : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hx.2]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) (Nat.card N) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hN)
  have := Nat.eq_one_of_dvd_coprimes hcop hdvd₁ hdvd₂
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp this)

omit [Finite G] in
theorem oddCore_eq_bot_of_normal'
    {X : Type*} [Group X] [Finite X] (hO : CFSG.oddCore X = ⊥) (K : Subgroup X) [K.Normal] :
    CFSG.oddCore K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.oddCore_eq_piCore X).trans (CFSG.pPrimeCore_eq_piCore X 2).symm] at hO
  rw [(CFSG.oddCore_eq_piCore K).trans (CFSG.pPrimeCore_eq_piCore K 2).symm]
  have hN : ((CFSG.pPrimeCore 2 K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (CFSG.pPrimeCore 2 K).map K.subtype ≤ CFSG.pPrimeCore 2 X := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle

namespace Minimal

variable (m : Minimal S A₁ A₂)
include m

theorem eq_bot_of_normal_of_odd {N : Subgroup G} [N.Normal] (hNH : N ≤ overlapClosure A₁ A₂)
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hNbot
  have h := m.hyp
  set H := overlapClosure A₁ A₂ with hHdef
  set π := QuotientGroup.mk' N with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hπconj : ∀ g a : G, π (g⁻¹ * a * g) = (π g)⁻¹ * π a * π g := fun g a => by
    rw [map_mul, map_mul, map_inv]
  have hSN : (S : Subgroup G) ⊓ N = ⊥ := inf_eq_bot_of_odd S.isPGroup' hN
  have hinf : ∀ {A : Subgroup G}, A ≤ (S : Subgroup G) → A ⊓ π.ker = ⊥ := fun hA => by
    rw [hker]
    exact le_bot_iff.mp (hSN ▸ inf_le_inf_right N hA)
  have hlift : ∀ {a g : G}, a ∈ (A₁ : Set G) ∪ A₂ →
      π (g⁻¹ * a * g) ∈ (S : Subgroup G).map π →
        ∃ n ∈ N, (g * n)⁻¹ * a * (g * n) ∈ (S : Subgroup G) := by
    intro a g ha hmem
    obtain ⟨s, hs, hsx⟩ := hmem
    have hsn : s⁻¹ * (g⁻¹ * a * g) ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hsx, inv_mul_cancel]
    have hx : g⁻¹ * a * g ∈ (S : Subgroup G) ⊔ N := by
      have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hsn)
      rwa [mul_inv_cancel_left] at this
    obtain ⟨n, hn, hnS⟩ := exists_conj_mem_of_mem_sup (isPGroup_zpowers_conj h ha g) hx
    exact ⟨n, hn, by rwa [show (g * n)⁻¹ * a * (g * n) = n⁻¹ * (g⁻¹ * a * g) * n by group]⟩
  have hπn : ∀ {n : G}, n ∈ N → π n = 1 := fun hn => by
    rw [← MonoidHom.mem_ker, hker]; exact hn
  have hpush : ∀ {x : G}, x ∈ (A₁ : Set G) ∪ A₂ →
      π x ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪ (A₂.map π : Subgroup (G ⧸ N)) := by
    rintro x (hx | hx)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  have hliftU : ∀ {a' : G ⧸ N}, a' ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪
      (A₂.map π : Subgroup (G ⧸ N)) → ∃ a ∈ (A₁ : Set G) ∪ A₂, π a = a' := by
    rintro a' (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  have hclosed : ∀ a' ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪
      (A₂.map π : Subgroup (G ⧸ N)), ∀ g' : G ⧸ N,
        g'⁻¹ * a' * g' ∈ (S : Subgroup G).map π →
          g'⁻¹ * a' * g' ∈ ((A₁.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) ∪
            (A₂.map π : Subgroup (G ⧸ N)) := by
    intro a' ha' g' hmem
    obtain ⟨a, haU, rfl⟩ := hliftU ha'
    obtain ⟨g, rfl⟩ := hπ g'
    rw [← hπconj] at hmem ⊢
    obtain ⟨n, hn, hnS⟩ := hlift haU hmem
    have := hpush (m.conj_mem haU hnS)
    rwa [hπconj, map_mul, hπn hn, mul_one, ← hπconj] at this
  have hHle : overlapClosure (A₁.map π) (A₂.map π) ≤ H.map π := by
    rw [overlapClosure, Subgroup.closure_le]
    rintro _ ⟨X', hX', Y', hY', hne⟩
    obtain ⟨g, rfl⟩ := hπ ‹_›
    obtain ⟨X, hX, rfl⟩ : ∃ X : Subgroup G, (X = A₁ ∨ X = A₂) ∧ X.map π = X' := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX'
      rcases hX' with rfl | rfl
      · exact ⟨A₁, Or.inl rfl, rfl⟩
      · exact ⟨A₂, Or.inr rfl, rfl⟩
    obtain ⟨Y, hY, rfl⟩ : ∃ Y : Subgroup G, (Y = A₁ ∨ Y = A₂) ∧ Y.map π = Y' := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY'
      rcases hY' with rfl | rfl
      · exact ⟨A₁, Or.inl rfl, rfl⟩
      · exact ⟨A₂, Or.inr rfl, rfl⟩
    rw [rightConjugate_map_hom] at hne
    obtain ⟨w', hw', hw'1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
    obtain ⟨⟨w₁, hw₁, hw₁e⟩, ⟨b, hb, hbe⟩⟩ := Subgroup.mem_inf.mp hw'
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hw₁
    rw [SetLike.mem_coe] at hb
    have hxU : g * w₁ * g⁻¹ ∈ (A₁ : Set G) ∪ A₂ := by
      rcases hX with rfl | rfl
      · exact Or.inl hw₁
      · exact Or.inr hw₁
    have hbS : b ∈ (S : Subgroup G) := by
      rcases hY with rfl | rfl
      · exact h.le_one hb
      · exact h.le_two hb
    have hx1 : g * w₁ * g⁻¹ ≠ 1 := by
      intro h1
      apply hw'1
      rw [← hw₁e]
      have : w₁ = 1 := by
        calc w₁ = g⁻¹ * (g * w₁ * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [this, map_one]
    have hmem : π (g⁻¹ * (g * w₁ * g⁻¹) * g) ∈ (S : Subgroup G).map π := by
      rw [show g⁻¹ * (g * w₁ * g⁻¹) * g = w₁ by group, hw₁e, ← hbe]
      exact ⟨b, hbS, rfl⟩
    obtain ⟨n, hn, hnS⟩ := hlift hxU hmem
    refine ⟨g * n, m.mem_of_conj hxU hx1 hnS, ?_⟩
    rw [map_mul, hπn hn, mul_one]
  let S' : Sylow 2 (G ⧸ N) := S.mapSurjective hπ
  have hyp : Hyp S' (A₁.map π) (A₂.map π) :=
    { le_one := Subgroup.map_mono h.le_one
      le_two := Subgroup.map_mono h.le_two
      comm := by rw [← Subgroup.map_commutator, h.comm, Subgroup.map_bot]
      rank_one := h.rank_one.trans (pRank_le_map_of_inf_ker π A₁ (hinf h.le_one))
      rank_two := h.rank_two.trans (pRank_le_map_of_inf_ker π A₂ (hinf h.le_two))
      closed_overlap := fun a' ha' g' _ hmem => hclosed a' ha' g' hmem.2
      closed_one := fun a' ha' g' _ hmem => hclosed a' ha' g' hmem.1
      closed_two := fun a' ha' g' _ hmem => hclosed a' ha' g' hmem.1 }
  have hcard : Nat.card (G ⧸ N) ≤ Nat.card G - 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have : Nat.card (G ⧸ N) * 1 < Nat.card (G ⧸ N) * Nat.card N := by nlinarith
    omega
  have hnot : ∀ {A B : Subgroup G}, A ≤ (S : Subgroup G) → B ≤ (S : Subgroup G) → ¬ A ≤ B →
      ¬ A.map π ≤ B.map π := by
    intro A B hA hB hAB hle
    apply hAB
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hle ⟨x, hx, rfl⟩
    have hbn : b⁻¹ * x ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hbx, inv_mul_cancel]
    have hbS : b⁻¹ * x ∈ (S : Subgroup G) ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hB hb)) (hA hx), hbn⟩
    rw [hSN, Subgroup.mem_bot] at hbS
    have : x = b := by
      calc x = b * (b⁻¹ * x) := by group
        _ = b := by rw [hbS, mul_one]
    rw [this]
    exact hb
  rcases m.ih (G ⧸ N) hcard S' (A₁.map π) (A₂.map π) hyp with htop | hle | hle | hd
  · apply m.ne_top
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, hk, hkg⟩ := hHle (htop ▸ Subgroup.mem_top (π g))
    have hkn : k⁻¹ * g ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have := H.mul_mem hk (hNH hkn)
    rwa [mul_inv_cancel_left] at this
  · exact hnot h.le_one h.le_two m.not_le₁₂ hle
  · exact hnot h.le_two h.le_one m.not_le₂₁ hle
  · obtain ⟨⟨a', ha', g', hS, hconj⟩, -, -⟩ := hd
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨g, rfl⟩ := hπ g'
    rw [← hπconj] at hS hconj
    obtain ⟨n, hn, hnS⟩ := hlift (Or.inl ha) hS
    have hsU := m.conj_mem (Or.inl ha) hnS
    have hsN := mem_normalizer_one_of_mem_union h.comm hsU
    rw [← rightConjugate_eq_self_iff] at hsN
    have hπs : π ((g * n)⁻¹ * a * (g * n)) = π (g⁻¹ * a * g) := by
      rw [hπconj, hπconj, map_mul, hπn hn, mul_one]
    rw [← hπs, rightConjugate_map_hom, hsN] at hconj
    exact hnot h.le_one h.le_two m.not_le₁₂ (le_of_eq hconj)

theorem oddCore_le : CFSG.oddCore G ≤ overlapClosure A₁ A₂ := by
  obtain ⟨E, hEA, ⟨hEc, hEsq⟩, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) A₁
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 A₁ := Nat.pow_le_pow_right (by norm_num) m.hyp.rank_one
  obtain ⟨u, hu, v, hv, hu2, hv2, huv⟩ := exists_two_involutions hE4 hEsq
  have huu : u * u = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hu2).1
  have hvv : v * v = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hv2).1
  have hcomm : Commute u v := by
    have := hEc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  let V := commutingPairSubgroup u v huu hvv hcomm
  have hVA : V ≤ A₁ := by
    intro x hx
    rcases mem_commutingPairSubgroup.mp hx with rfl | rfl | rfl | rfl
    · exact A₁.one_mem
    · exact hEA hu
    · exact hEA hv
    · exact A₁.mul_mem (hEA hu) (hEA hv)
  have hVcard : Nat.card V = 2 ^ 2 := commutingPairSubgroup_card
    (orderOf_eq_prime_iff.mp hu2).2 (orderOf_eq_prime_iff.mp hv2).2 huv
  have hpower : ∀ member : V, member ^ 2 = 1 := fun member =>
    Subtype.ext (commutingPairSubgroup_sq member.property)
  have hodd : ¬ 2 ∣ Nat.card (CFSG.oddCore G) :=
    (CFSG.ComponentClassification.OddCore.odd_card G).not_two_dvd_nat
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two V (CFSG.oddCore G) hpower hVcard hodd
    (le_top.trans (Subgroup.normalizer_eq_top (H := CFSG.oddCore G)).ge)
  rw [hgen]
  refine iSup_le fun w => iSup_le fun hw1 => ?_
  exact inf_le_right.trans (m.centralizer_le (Or.inl (hVA w.property))
    (fun h1 => hw1 (Subtype.ext h1)))

theorem oddCore_eq_bot : CFSG.oddCore G = ⊥ :=
  m.eq_bot_of_normal_of_odd m.oddCore_le (CFSG.ComponentClassification.OddCore.odd_card G)

end Minimal

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding

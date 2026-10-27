module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSyl

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem false_of_goldschmidt_bound (hG : Goldschmidt74Cor4) {m : ℕ} {G : Type} [Group G] [Finite G]
    {C R : Subgroup G} (hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) (hC2 : ∀ c ∈ C, c * c = 1)
    (hCR : C ≤ R) (hR2 : IsPGroup 2 R) (hRN : R ≤ normalizer (C : Set G))
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ normalizer (C : Set G) → R ≤ Q → Q ≤ R)
    (hweak : ∀ D : Subgroup G, D ≤ R → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      (∀ x ∈ D, x * x = 1) → ¬ D ≤ C → Nat.card D = Nat.card C →
      ∃ d ∈ D, d ∉ C ∧ C.relIndex D < (centralizer ({d} : Set G)).relIndex C)
    (hrank : ∀ B : Subgroup G, B ≤ R → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → (centralizer (C : Set G)).relIndex B ≤ m)
    (t : G) (htR : t ∈ R) (htC : t ∉ C) (ht2 : orderOf t = 2) (htconj : ∃ g : G, g * t * g⁻¹ ∈ C)
    (hcomm : m < Nat.card (⁅C, zpowers t⁆ : Subgroup G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwc := weaklyClosed_of_relIndex_lt hCab hC2 hweak
  obtain ⟨T, hTR⟩ := exists_sylow_eq_of_weaklyClosed hR2 hRN hmax hwc hCR
  have hwcT : ∀ g : G, C.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      C.map (MulAut.conj g).toMonoidHom = C := by
    rw [hTR]
    exact hwc
  obtain ⟨g, hg⟩ := htconj
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  obtain ⟨ρ, ⟨B, hB, hBρ⟩, -, -, hII⟩ := hG G T C (hTR ▸ hCR) hCab hC2 hwcT
    ⟨g * t * g⁻¹, hg, g⁻¹, by rw [hTR, e]; exact htR, by rw [e]; exact htC⟩
  obtain ⟨hBT, hBC, g', hg'⟩ := hB
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hxy := hCab _ (hg' ⟨x, hx, rfl⟩) _ (hg' ⟨y, hy, rfl⟩)
    have : g' * (x * y) * g'⁻¹ = g' * (y * x) * g'⁻¹ := by
      calc g' * (x * y) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * y * g'⁻¹) := by group
        _ = (g' * y * g'⁻¹) * (g' * x * g'⁻¹) := hxy
        _ = g' * (y * x) * g'⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hB2 : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    have h1 := hC2 _ (hg' ⟨x, hx, rfl⟩)
    have : g' * (x * x) * g'⁻¹ = 1 := by
      calc g' * (x * x) * g'⁻¹ = (g' * x * g'⁻¹) * (g' * x * g'⁻¹) := by group
        _ = 1 := h1
    simpa using this
  have hρ : ρ ≤ m := hBρ ▸ hrank B (hTR ▸ hBT) hBab hB2
  have hle := hII t (hTR ▸ htR) ht2 ⟨g, hg⟩
  omega

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem false_of_sylow_bound
    (hG : Goldschmidt74Cor4) {m : ℕ} (hm : m < 64) (h : Setup L A C z) (hty : SextetType L A)
    (hSyl : ∀ n : egNL L A, n * n = 1 → (n : G) ∉ A →
      ∃ S₀ : Subgroup (egQD C), IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧ psi h n ∈ S₀ ∧
        (∀ D : Subgroup (egQD C), D ≤ S₀ → (∀ a ∈ D, a * a = 1) → Nat.card D ≤ m) ∧
        (∀ D : Subgroup (egQD C), D ≤ S₀ → (∀ a ∈ D, a * a = 1) → D ≠ ⊥ →
          ∃ d ∈ D, d ≠ 1 ∧ ∃ b : ℕ, (∀ (g : G) (hg : g ∈ normalizer (C : Set G)),
            qdMk C ⟨g, hg⟩ = d → Nat.card (fixSub C g) ≤ b) ∧ Nat.card D * b < 4096)) :
    False := by
  classical
  obtain ⟨hAL, e, hA⟩ := id hty
  have hCab := h.hC.comm
  have hC2 := h.hCe
  have hCcard : Nat.card C = 4096 := h.hC.card
  let σ := Sym6.tetE hA
  let H : Subgroup (egNL L A) := (alternatingGroup (Fin 6)).comap σ
  have hH : H.index = 2 := (Sym6.index_two_iff hA hAL H).2 rfl
  obtain ⟨t₀, ht₀2, ht₀A, ht₀H⟩ := Sym6.exists_involution_not_mem hA hAL
  obtain ⟨S₀, hS₀, hS₀odd, ht₀S, hrankY, hfusY⟩ := hSyl t₀ ht₀2 ht₀A
  let R : Subgroup G := liftSub C S₀
  have hCR : C ≤ R := le_liftSub
  have hRN : R ≤ normalizer (C : Set G) := liftSub_le_normalizer
  have hR2 : IsPGroup 2 R := liftSub_isPGroup hC2 hS₀
  have hmax := liftSub_maximal hS₀ hS₀odd
  have hmemR : ∀ (d : G) (hd : d ∈ normalizer (C : Set G)), d ∈ R →
      qdMk C ⟨d, hd⟩ ∈ S₀ := fun d hd hdR => (mem_liftSub.1 hdR).2
  have himg : ∀ B : Subgroup G, B ≤ R → (∀ x ∈ B, x * x = 1) →
      ∃ Bb : Subgroup (egQD C), Nat.card Bb = C.relIndex B ∧ Bb ≤ S₀ ∧ (∀ a ∈ Bb, a * a = 1) ∧
        (∀ a ∈ Bb, ∃ (b : G) (hb : b ∈ normalizer (C : Set G)), b ∈ B ∧ a = qdMk C ⟨b, hb⟩) ∧
        ∀ (b : G) (hb : b ∈ normalizer (C : Set G)), b ∈ B → qdMk C ⟨b, hb⟩ ∈ Bb := by
    intro B hBR hB2
    refine ⟨((qdMk C).comp ((B.subgroupOf (normalizer (C : Set G))).subtype)).range,
      card_range_eq_relIndex (hBR.trans hRN), ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨b, rfl⟩
      exact hmemR _ (b : normalizer (C : Set G)).2 (hBR (mem_subgroupOf.1 b.2))
    · rintro _ ⟨b, rfl⟩
      show qdMk C (b : normalizer (C : Set G)) * qdMk C (b : normalizer (C : Set G)) = 1
      rw [← map_mul]
      have : (b : normalizer (C : Set G)) * b = 1 := Subtype.ext (hB2 _ (mem_subgroupOf.1 b.2))
      rw [this, map_one]
    · rintro _ ⟨b, rfl⟩
      exact ⟨((b : normalizer (C : Set G)) : G), (b : normalizer (C : Set G)).2,
        mem_subgroupOf.1 b.2, rfl⟩
    · intro b hb hbB
      exact ⟨⟨⟨b, hb⟩, mem_subgroupOf.2 hbB⟩, rfl⟩
  have hrank : ∀ B : Subgroup G, B ≤ R → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → (centralizer (C : Set G)).relIndex B ≤ m := by
    intro B hBR _ hB2
    obtain ⟨Bb, hBb, hBbS, hBb2, -, -⟩ := himg B hBR hB2
    have hle : (centralizer (C : Set G)).relIndex B ≤ C.relIndex B := by
      apply Subgroup.relIndex_le_of_le_left
      · exact fun c hc => mem_centralizer_iff.2 fun c' hc' => hCab c' hc' c hc
      · exact Subgroup.index_ne_zero_of_finite
    calc (centralizer (C : Set G)).relIndex B ≤ C.relIndex B := hle
      _ = Nat.card Bb := hBb.symm
      _ ≤ m := hrankY Bb hBbS hBb2
  have hweak : ∀ D : Subgroup G, D ≤ R → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      (∀ x ∈ D, x * x = 1) → ¬ D ≤ C → Nat.card D = Nat.card C →
      ∃ d ∈ D, d ∉ C ∧ C.relIndex D < (centralizer ({d} : Set G)).relIndex C := by
    intro D hDR _ hD2 hDC _
    obtain ⟨Db, hDb, hDbS, hDb2, hDbmem, hDbin⟩ := himg D hDR hD2
    obtain ⟨d₀, hd₀D, hd₀C⟩ := Set.not_subset.1 hDC
    have hbot : Db ≠ ⊥ := by
      intro hbot
      have hd₀N : d₀ ∈ normalizer (C : Set G) := hRN (hDR hd₀D)
      have hmem : qdMk C ⟨d₀, hd₀N⟩ ∈ Db := hDbin d₀ hd₀N hd₀D
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hd₀C ((qdMk_eq_one hd₀N).1 hmem)
    obtain ⟨d, hdD, hd1, b, hb, hlt⟩ := hfusY Db hDbS hDb2 hbot
    obtain ⟨g, hgN, hgD, hgd⟩ := hDbmem d hdD
    refine ⟨g, hgD, fun hgC => hd1 (hgd ▸ (qdMk_eq_one hgN).2 hgC), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := centralizer ({g} : Set G)) (K := C)
    rw [← card_fixSub_eq_card_inf, hCcard] at h1
    by_contra hcon
    have hr : (centralizer ({g} : Set G)).relIndex C ≤ C.relIndex D := not_lt.1 hcon
    have hbg : Nat.card (fixSub C g) ≤ b := hb g hgN hgd.symm
    have h2 : (centralizer ({g} : Set G)).relIndex C * Nat.card (fixSub C g) ≤
        C.relIndex D * b := Nat.mul_le_mul hr hbg
    rw [← hDb] at h2
    omega
  have ht₀N : (t₀ : G) ∈ normalizer (C : Set G) := egNL_le_normalizer_C h t₀.2
  have ht₀R : (t₀ : G) ∈ R := mem_liftSub.2 ⟨ht₀N, ht₀S⟩
  have ht₀L : (t₀ : G) ∈ L := (mem_inf.1 t₀.2).2
  have ht₀C : (t₀ : G) ∉ C := fun hC => ht₀A (mem_A_of_mem_L h hC ht₀L)
  have ht₀tt : (t₀ : G) * t₀ = 1 := congrArg Subtype.val ht₀2
  have ht₀ord : orderOf (t₀ : G) = 2 := by
    apply orderOf_eq_prime
    · rw [sq]; exact ht₀tt
    · intro h1
      exact ht₀A (h1 ▸ A.one_mem)
  have htconj : ∃ g : G, g * (t₀ : G) * g⁻¹ ∈ C := by
    obtain ⟨l, -, hlA⟩ := exists_conj_mem_of_involution_of_type hty t₀ ht₀L ht₀tt
    exact ⟨l, h.hC.A_le hlA⟩
  have hcomm : m < Nat.card (⁅C, zpowers (t₀ : G)⁆ : Subgroup G) := by
    have hge := card_le_card_fixSub_mul_commutator hCab ht₀N
    obtain ⟨-, h8⟩ := card_fix_involution_of_type hty H hH t₀ ht₀2 ht₀A
    have h8' : Nat.card (fixSub A (t₀ : G)) = 8 := h8 (ht₀H H hH)
    have hfix : Nat.card (fixSub C (t₀ : G)) ≤ 64 :=
      (card_fixSub_le h t₀.2).trans (by rw [h8']; norm_num)
    by_contra hle
    have : Nat.card C ≤ 64 * m :=
      hge.trans (Nat.mul_le_mul hfix (not_lt.1 hle))
    omega
  exact false_of_goldschmidt_bound hG hCab hC2 hCR hR2 hRN hmax hweak hrank (t₀ : G) ht₀R ht₀C
    ht₀ord htconj hcomm

end CSide

end CFSG.EvenSporadicStandard.M24Std

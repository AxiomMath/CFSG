module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.Wreathed.FourPointThreePairs

open CFSG.TwoRankLowerBound.Helpers

open scoped BigOperators Classical

theorem end_commute_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hV : Module.finrank ℂ V = 1) (f₁ f₂ : Module.End ℂ V) : f₁ * f₂ = f₂ * f₁ := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp hV
  obtain ⟨c₁, hc₁⟩ := hv (f₁ v)
  obtain ⟨c₂, hc₂⟩ := hv (f₂ v)
  ext w
  obtain ⟨c, rfl⟩ := hv w
  simp only [Module.End.mul_apply, map_smul]
  rw [← hc₂, ← hc₁, map_smul, map_smul, ← hc₁, ← hc₂]
  simp only [smul_smul, mul_comm c₂ c₁]

theorem two_le_finrank_of_character_ne_one {G : Type} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (data : FiniteComplexRepresentation G)
    (hirr : data.IsIrreducible) (hne : data.character ≠ 1) :
    2 ≤ Module.finrank ℂ data.vector := by
  have h0 : Module.finrank ℂ data.vector ≠ 0 := by
    have h := irreducible_character_degree_ne_zero data hirr
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact_mod_cast h
  by_contra hlt
  have h1 : Module.finrank ℂ data.vector = 1 := by omega
  have hker := CFSG.Wreathed.FourPointGaussianColumns.ker_eq_bot_of_character_ne_one data hirr hne
  have hinj : Function.Injective data.representation := (MonoidHom.ker_eq_bot_iff _).mp hker
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (hinj (by rw [map_mul, map_mul, end_commute_of_finrank_eq_one h1]))

theorem eq_one_or_neg_one_of_odd_of_sq_le {L : ℤ} (hL : Odd L) (h : L ^ 2 ≤ 5) :
    L = 1 ∨ L = -1 := by
  have h1 : L ≤ 2 := by nlinarith
  have h2 : -2 ≤ L := by nlinarith
  obtain ⟨k, rfl⟩ := hL
  omega

theorem four_le_sq_of_even_of_ne_zero {L : ℤ} (hL : Even L) (h : L ≠ 0) : 4 ≤ L ^ 2 := by
  obtain ⟨k, rfl⟩ := hL
  have hk : k ≠ 0 := by
    rintro rfl
    exact h (by ring)
  rcases lt_or_gt_of_ne hk with hk' | hk' <;> nlinarith

theorem norm_eight_odd_column {ι : Type*} (B E : Finset ι) (hEB : E ⊆ B) (hE : E.card = 4)
    (L : ι → ℤ) (hL : ∑ χ ∈ B, L χ ^ 2 = 8) (hodd : ∀ χ ∈ E, Odd (L χ))
    (heven : ∀ χ ∈ B, χ ∉ E → Even (L χ)) :
    (∀ χ ∈ E, L χ = 1 ∨ L χ = -1) ∧
      ∃ η ∈ B, η ∉ E ∧ (L η = 2 ∨ L η = -2) ∧ ∀ χ ∈ B, χ ∉ E → χ ≠ η → L χ = 0 := by
  have hsplit : ∑ χ ∈ B \ E, L χ ^ 2 + ∑ χ ∈ E, L χ ^ 2 = 8 := by
    rw [Finset.sum_sdiff hEB]
    exact hL
  have hnn : 0 ≤ ∑ χ ∈ B \ E, L χ ^ 2 := Finset.sum_nonneg fun χ _ => sq_nonneg _
  have hE1 : ∀ χ ∈ E, 1 ≤ L χ ^ 2 := fun χ hχ => by
    obtain ⟨k, hk⟩ := hodd χ hχ
    rw [hk]
    rcases le_or_gt 0 k with h | h <;> nlinarith
  have hunit : ∀ χ ∈ E, L χ = 1 ∨ L χ = -1 := by
    intro χ hχ
    have h3 : 3 ≤ ∑ ψ ∈ E.erase χ, L ψ ^ 2 := by
      have h := Finset.card_nsmul_le_sum (E.erase χ) (fun ψ => L ψ ^ 2) 1
        (fun ψ hψ => hE1 ψ (Finset.mem_of_mem_erase hψ))
      rw [Finset.card_erase_of_mem hχ, hE] at h
      norm_num at h
      exact h
    have hsum := Finset.add_sum_erase E (fun ψ => L ψ ^ 2) hχ
    exact eq_one_or_neg_one_of_odd_of_sq_le (hodd χ hχ) (by linarith)
  have hE4 : ∑ χ ∈ E, L χ ^ 2 = 4 := by
    have h : ∀ χ ∈ E, L χ ^ 2 = 1 := fun χ hχ => by
      rcases hunit χ hχ with h | h <;> rw [h] <;> norm_num
    rw [Finset.sum_congr rfl h, Finset.sum_const, hE]
    norm_num
  have hrest : ∑ χ ∈ B \ E, L χ ^ 2 = 4 := by linarith
  obtain ⟨η, hη, hηne⟩ : ∃ η ∈ B \ E, L η ≠ 0 := by
    by_contra hcon
    have h0 : ∑ χ ∈ B \ E, L χ ^ 2 = 0 :=
      Finset.sum_eq_zero fun χ hχ => by
        have h : L χ = 0 := by
          by_contra h
          exact hcon ⟨χ, hχ, h⟩
        rw [h]
        ring
    linarith
  obtain ⟨hηB, hηE⟩ := Finset.mem_sdiff.mp hη
  have hη4 : 4 ≤ L η ^ 2 := four_le_sq_of_even_of_ne_zero (heven η hηB hηE) hηne
  have hηle : L η ^ 2 ≤ ∑ χ ∈ B \ E, L χ ^ 2 :=
    Finset.single_le_sum (f := fun χ => L χ ^ 2) (fun χ _ => sq_nonneg (L χ)) hη
  refine ⟨hunit, η, hηB, hηE, ?_, ?_⟩
  · have h : (L η - 2) * (L η + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · left
      linarith
    · right
      linarith
  · intro χ hχB hχE hχη
    have hχ : χ ∈ (B \ E).erase η :=
      Finset.mem_erase.mpr ⟨hχη, Finset.mem_sdiff.mpr ⟨hχB, hχE⟩⟩
    have hsum := Finset.add_sum_erase (B \ E) (fun ψ => L ψ ^ 2) hη
    have hle : L χ ^ 2 ≤ ∑ ψ ∈ (B \ E).erase η, L ψ ^ 2 :=
      Finset.single_le_sum (f := fun ψ => L ψ ^ 2) (fun ψ _ => sq_nonneg (L ψ)) hχ
    have h0 : L χ ^ 2 = 0 := by nlinarith [sq_nonneg (L χ)]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0

theorem sign_balance {ι : Type*} (E : Finset ι) (hE : E.card = 4) (s : ι → ℤ)
    (hs : ∀ χ ∈ E, s χ = 1 ∨ s χ = -1) (hsum : ∑ χ ∈ E, s χ = 0) :
    (E.filter (fun χ => s χ = 1)).card = 2 ∧ (E.filter (fun χ => s χ = -1)).card = 2 := by
  have h1 : ∑ χ ∈ E, s χ = ∑ χ ∈ E, (2 * (if s χ = 1 then (1 : ℤ) else 0) - 1) :=
    Finset.sum_congr rfl fun χ hχ => by rcases hs χ hχ with h | h <;> simp [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const, hE,
    hsum] at h1
  have hp : (E.filter (fun χ => s χ = 1)).card = 2 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] at h1
    omega
  refine ⟨hp, ?_⟩
  have hcongr : E.filter (fun χ => s χ = -1) = E.filter (fun χ => ¬ s χ = 1) :=
    Finset.filter_congr fun χ hχ => by
      rcases hs χ hχ with h | h <;> simp [h]
  have hc := Finset.card_filter_add_card_filter_not (s := E) (fun χ => s χ = 1)
  rw [hcongr]
  omega

theorem column_eight_analysis {ι : Type*} (B : Finset ι) (P L deg : ι → ℤ) (p₀ : ι)
    (hp₀ : p₀ ∈ B) (hE : (B.filter (fun χ => P χ ≠ 0)).card = 4)
    (hPunit : ∀ χ ∈ B, P χ ≠ 0 → P χ = 1 ∨ P χ = -1) (hLsq : ∑ χ ∈ B, L χ ^ 2 = 8)
    (hpar : ∀ χ ∈ B, ∃ k : ℤ, L χ = P χ + 2 * k) (hPL : ∑ χ ∈ B, P χ * L χ = 0)
    (hPd : ∑ χ ∈ B, P χ * deg χ = 0) (hLd : ∑ χ ∈ B, L χ * deg χ = 0) (hPp : P p₀ = 1)
    (hLp : L p₀ = -1) (hdp : deg p₀ = 1) (hdeg : ∀ χ ∈ B, χ ≠ p₀ → 2 ≤ deg χ) :
    let E := B.filter (fun χ => P χ ≠ 0)
    ∃ η ∈ B, η ∉ E ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ L η = 2 * ε ∧
      (∀ χ ∈ B, χ ∉ E → χ ≠ η → L χ = 0) ∧ (∀ χ ∈ E, L χ = 1 ∨ L χ = -1) ∧
      ∃ β ∈ E, β ≠ p₀ ∧
        (E.filter (fun χ => L χ = P χ)).card = 2 ∧ (E.filter (fun χ => L χ = -P χ)).card = 2 ∧
        E.filter (fun χ => L χ = -P χ) = {p₀, β} ∧
        deg η = |1 + P β * deg β| ∧ (deg η = deg β - 1 ∨ deg η = deg β + 1) ∧
        ∑ χ ∈ E.filter (fun χ => L χ = P χ), P χ * deg χ = -ε * deg η ∧
        ∑ χ ∈ E.filter (fun χ => L χ = -P χ), P χ * deg χ = ε * deg η := by
  intro E
  have hEB : E ⊆ B := Finset.filter_subset _ _
  have hmemE : ∀ χ, χ ∈ E ↔ χ ∈ B ∧ P χ ≠ 0 := fun χ => Finset.mem_filter
  have hP0 : ∀ χ ∈ B, χ ∉ E → P χ = 0 := fun χ hχB hχE => by
    by_contra h
    exact hχE ((hmemE χ).mpr ⟨hχB, h⟩)
  have hodd : ∀ χ ∈ E, Odd (L χ) := by
    intro χ hχ
    obtain ⟨hχB, hP⟩ := (hmemE χ).mp hχ
    obtain ⟨k, hk⟩ := hpar χ hχB
    rcases hPunit χ hχB hP with h | h
    · exact ⟨k, by rw [hk, h]; ring⟩
    · exact ⟨k - 1, by rw [hk, h]; ring⟩
  have heven : ∀ χ ∈ B, χ ∉ E → Even (L χ) := by
    intro χ hχB hχE
    obtain ⟨k, hk⟩ := hpar χ hχB
    exact ⟨k, by rw [hk, hP0 χ hχB hχE]; ring⟩
  obtain ⟨hunit, η, hηB, hηE, hη2, hzero⟩ := norm_eight_odd_column B E hEB hE L hLsq hodd heven
  obtain ⟨ε, hε, hLη⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ L η = 2 * ε := by
    rcases hη2 with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hsE : ∀ χ ∈ E, P χ * L χ = 1 ∨ P χ * L χ = -1 := by
    intro χ hχ
    obtain ⟨hχB, hP⟩ := (hmemE χ).mp hχ
    rcases hPunit χ hχB hP with h | h <;> rcases hunit χ hχ with h' | h' <;> rw [h, h'] <;>
      norm_num
  have hoffE : ∀ (F : ι → ℤ), (∀ χ ∈ B, χ ∉ E → F χ = 0) →
      ∑ χ ∈ B, F χ = ∑ χ ∈ E, F χ := by
    intro F hF
    rw [← Finset.sum_sdiff hEB, Finset.sum_eq_zero (s := B \ E) fun χ hχ =>
      hF χ (Finset.mem_sdiff.mp hχ).1 (Finset.mem_sdiff.mp hχ).2, zero_add]
  have hPLE : ∑ χ ∈ E, P χ * L χ = 0 := by
    rw [← hoffE _ fun χ hχB hχE => by rw [hP0 χ hχB hχE, zero_mul]]
    exact hPL
  obtain ⟨hcardp, hcardm⟩ := sign_balance E hE (fun χ => P χ * L χ) hsE hPLE
  have hplus : E.filter (fun χ => L χ = P χ) = E.filter (fun χ => P χ * L χ = 1) :=
    Finset.filter_congr fun χ hχ => by
      obtain ⟨hχB, hP⟩ := (hmemE χ).mp hχ
      rcases hPunit χ hχB hP with h | h <;> rcases hunit χ hχ with h' | h' <;> simp [h, h']
  have hminus : E.filter (fun χ => L χ = -P χ) = E.filter (fun χ => P χ * L χ = -1) :=
    Finset.filter_congr fun χ hχ => by
      obtain ⟨hχB, hP⟩ := (hmemE χ).mp hχ
      rcases hPunit χ hχB hP with h | h <;> rcases hunit χ hχ with h' | h' <;> simp [h, h']
  have hnot : E.filter (fun χ => ¬ L χ = P χ) = E.filter (fun χ => L χ = -P χ) :=
    Finset.filter_congr fun χ hχ => by
      obtain ⟨hχB, hP⟩ := (hmemE χ).mp hχ
      rcases hPunit χ hχB hP with h | h <;> rcases hunit χ hχ with h' | h' <;> simp [h, h']
  rw [← hplus] at hcardp
  rw [← hminus] at hcardm
  have hp₀E : p₀ ∈ E := (hmemE p₀).mpr ⟨hp₀, by rw [hPp]; norm_num⟩
  have hp₀m : p₀ ∈ E.filter (fun χ => L χ = -P χ) :=
    Finset.mem_filter.mpr ⟨hp₀E, by rw [hLp, hPp]⟩
  obtain ⟨β, hβE, hβp, hEm⟩ : ∃ β ∈ E, β ≠ p₀ ∧ E.filter (fun χ => L χ = -P χ) = {p₀, β} := by
    obtain ⟨u, t, hut, heq⟩ := Finset.card_eq_two.mp hcardm
    rw [heq] at hp₀m
    rcases Finset.mem_insert.mp hp₀m with h | h
    · subst h
      refine ⟨t, ?_, hut.symm, heq⟩
      exact (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t) :
        t ∈ E.filter (fun χ => L χ = -P χ))).1
    · rw [Finset.mem_singleton] at h
      subst h
      refine ⟨u, ?_, hut, by rw [heq, Finset.pair_comm]⟩
      exact (Finset.mem_filter.mp (heq ▸ Finset.mem_insert_self u {p₀} :
        u ∈ E.filter (fun χ => L χ = -P χ))).1
  set Sp := ∑ χ ∈ E.filter (fun χ => L χ = P χ), P χ * deg χ with hSp
  set Sm := ∑ χ ∈ E.filter (fun χ => L χ = -P χ), P χ * deg χ with hSm
  have hsum1 : Sp + Sm = 0 := by
    rw [hSp, hSm, ← hnot, Finset.sum_filter_add_sum_filter_not,
      ← hoffE _ fun χ hχB hχE => by rw [hP0 χ hχB hχE, zero_mul]]
    exact hPd
  have hLdE : ∑ χ ∈ E, L χ * deg χ = Sp - Sm := by
    rw [← Finset.sum_filter_add_sum_filter_not E (fun χ => L χ = P χ), hnot, hSp, hSm,
      sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.mp hχ).2]
    · exact Finset.sum_congr rfl fun χ hχ => by rw [(Finset.mem_filter.mp hχ).2]; ring
  have hηne : η ≠ p₀ := fun h => hηE (h ▸ hp₀E)
  have hLdB : ∑ χ ∈ B, L χ * deg χ = ∑ χ ∈ E, L χ * deg χ + L η * deg η := by
    rw [← Finset.sum_sdiff hEB, add_comm]
    congr 1
    refine Finset.sum_eq_single_of_mem η (Finset.mem_sdiff.mpr ⟨hηB, hηE⟩) fun χ hχ hχη => ?_
    rw [hzero χ (Finset.mem_sdiff.mp hχ).1 (Finset.mem_sdiff.mp hχ).2 hχη, zero_mul]
  have hsum2 : Sp - Sm + 2 * ε * deg η = 0 := by
    rw [← hLdE, ← hLη, ← hLdB]
    exact hLd
  have hSpv : Sp = -ε * deg η := by linarith
  have hSmv : Sm = ε * deg η := by linarith
  have hSm2 : Sm = 1 + P β * deg β := by
    rw [hSm, hEm, Finset.sum_pair hβp.symm, hPp, hdp]
    ring
  have hβB : β ∈ B := hEB hβE
  have hdη := hdeg η hηB hηne
  have hdβ := hdeg β hβB hβp
  have hPβ := hPunit β hβB ((hmemE β).mp hβE).2
  have hrel : 1 + P β * deg β = ε * deg η := hSm2.symm.trans hSmv
  have hdη' : deg η = |1 + P β * deg β| := by
    rw [hrel, abs_mul]
    rcases hε with rfl | rfl <;> simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ deg η)]
  refine ⟨η, hηB, hηE, ε, hε, hLη, hzero, hunit, β, hβE, hβp, hcardp, hcardm, hEm, hdη', ?_,
    hSpv, hSmv⟩
  rcases hPβ with h | h <;> rcases hε with h' | h' <;> rw [h, h'] at hrel <;> omega

theorem conj_column_analysis {ι : Type*} (B : Finset ι) (P L₁ L₃ : ι → ℤ) (σ : ι → ι)
    (hσσ : ∀ χ, σ (σ χ) = χ) (hσB : ∀ χ ∈ B, σ χ ∈ B) (hPσ : ∀ χ, P (σ χ) = P χ)
    (hLσ : ∀ χ ∈ B, L₃ (σ χ) = L₁ χ) (p₀ : ι) (hσp : σ p₀ = p₀) (η₁ η₃ β₁ β₃ : ι)
    (ε₁ ε₃ : ℤ) (hη₁ : η₁ ∈ B) (hη₁P : P η₁ = 0) (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hL₁ : L₁ η₁ = 2 * ε₁) (hL₃ : L₃ η₃ = 2 * ε₃)
    (hzero₃ : ∀ χ ∈ B, P χ = 0 → χ ≠ η₃ → L₃ χ = 0) (hβ₁ : β₁ ∈ B) (hβ₁P : P β₁ ≠ 0)
    (hβ₁L : L₁ β₁ = -P β₁) (hβ₁p : β₁ ≠ p₀)
    (hminus₃ : ∀ χ ∈ B, P χ ≠ 0 → L₃ χ = -P χ → χ = p₀ ∨ χ = β₃) :
    η₃ = σ η₁ ∧ ε₃ = ε₁ ∧ β₃ = σ β₁ := by
  have hη : σ η₁ = η₃ := by
    by_contra h
    have h0 := hzero₃ (σ η₁) (hσB η₁ hη₁) (by rw [hPσ, hη₁P]) h
    rw [hLσ η₁ hη₁, hL₁] at h0
    rcases hε₁ with rfl | rfl <;> norm_num at h0
  have hε : ε₃ = ε₁ := by
    have h := hLσ η₁ hη₁
    rw [hη, hL₃, hL₁] at h
    linarith
  have hβ : σ β₁ = β₃ := by
    rcases hminus₃ (σ β₁) (hσB β₁ hβ₁) (by rw [hPσ]; exact hβ₁P)
      (by rw [hLσ β₁ hβ₁, hβ₁L, hPσ]) with h | h
    · exact absurd (by rw [← hσσ β₁, h, hσp]) hβ₁p
    · exact h
  exact ⟨hη.symm, hε, hβ.symm⟩

theorem card_inter_two_pairs {ι : Type*} (E : Finset ι) (a b c d p₀ : ι) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hpab : a ∈ E ↔ b ∈ E) (hpcd : c ∈ E ↔ d ∈ E) (hcardE : E.card = 4) (hp₀E : p₀ ∈ E)
    (hp₀J : p₀ ∉ ({a, b, c, d} : Finset ι)) :
    (E ∩ {a, b, c, d}).card = 0 ∨ (E ∩ {a, b, c, d}).card = 2 := by
  have hcard4 : ({a, b, c, d} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  by_cases ha : a ∈ E <;> by_cases hc : c ∈ E
  · exfalso
    have hsub : ({a, b, c, d} : Finset ι) ⊆ E := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [ha, hpab.mp ha, hc, hpcd.mp hc]
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardE, hcard4])
    exact hp₀J (heq ▸ hp₀E)
  · right
    have hb := hpab.mp ha
    have hd : d ∉ E := fun h => hc (hpcd.mpr h)
    have heq : E ∩ {a, b, c, d} = {a, b} := by
      ext t
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, rfl | rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd ht hc
        · exact absurd ht hd
      · rintro (rfl | rfl)
        · exact ⟨ha, Or.inl rfl⟩
        · exact ⟨hb, Or.inr (Or.inl rfl)⟩
    rw [heq, Finset.card_pair hab]
  · right
    have hb : b ∉ E := fun h => ha (hpab.mpr h)
    have hd := hpcd.mp hc
    have heq : E ∩ {a, b, c, d} = {c, d} := by
      ext t
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, rfl | rfl | rfl | rfl⟩
        · exact absurd ht ha
        · exact absurd ht hb
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hc, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨hd, Or.inr (Or.inr (Or.inr rfl))⟩
    rw [heq, Finset.card_pair hcd]
  · left
    have hb : b ∉ E := fun h => ha (hpab.mpr h)
    have hd : d ∉ E := fun h => hc (hpcd.mpr h)
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at ht
    obtain ⟨ht, rfl | rfl | rfl | rfl⟩ := ht
    exacts [ha ht, hb ht, hc ht, hd ht]

theorem odd_filter_eq_symmDiff {ι : Type*} (B : Finset ι) (P Q : ι → ℤ) (deg : ι → ℕ)
    (hP : ∀ χ ∈ B, P χ = 0 ∨ P χ = 1 ∨ P χ = -1) (hQ : ∀ χ ∈ B, Q χ = 0 ∨ Q χ = 1 ∨ Q χ = -1)
    (hpar : ∀ χ ∈ B, ∃ k : ℤ, (deg χ : ℤ) = P χ + Q χ + 2 * k) :
    B.filter (fun χ => Odd (deg χ)) =
      symmDiff (B.filter (fun χ => P χ ≠ 0)) (B.filter (fun χ => Q χ ≠ 0)) := by
  ext χ
  rw [Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
  by_cases hχ : χ ∈ B
  · obtain ⟨k, hk⟩ := hpar χ hχ
    rw [Nat.odd_iff]
    rcases hP χ hχ with h | h | h <;> rcases hQ χ hχ with h' | h' | h' <;> rw [h, h'] at hk <;>
      simp only [h, h', hχ, true_and, ne_eq, not_true_eq_false, not_false_eq_true, and_true,
        and_false, or_false, false_or, one_ne_zero, neg_eq_zero, iff_true, iff_false] <;> omega
  · simp [hχ]

theorem card_symmDiff_add {ι : Type*} (E J : Finset ι) :
    (symmDiff E J).card + 2 * (E ∩ J).card = E.card + J.card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_sdiff_add_card_inter E J
  have h2 := Finset.card_sdiff_add_card_inter J E
  rw [Finset.inter_comm] at h2
  omega

end CFSG.Wreathed.FourPointThreePairs

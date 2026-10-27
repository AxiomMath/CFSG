module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB6

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def Sec3TenExceptional : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (T T₁ S : Subgroup G) (n : ℕ), Sec3 T T₁ → Odd n → 3 < n → Sec3Dih T T₁ n →
      Nat.card (normIn T T₁) = 4 → ∀ (a u : G), SecB6 T T₁ S a → u ∈ normIn T T₁ →
        (∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) → (∃ l ∈ normIn T T₁, a * l ≠ l * a) → False

theorem mem_normalizer_of_values {L : Subgroup G} {a : G} (haa : a * a = 1)
    (haL : ∀ t ∈ T, ⁅t, a⁆ ∈ L) (hLT : L ≤ T) : a ∈ Subgroup.normalizer (L : Set G) := by
  have key : ∀ y ∈ L, a * y * a⁻¹ ∈ L := by
    intro y hy
    have e1 : a * y * a⁻¹ = (⁅y, a⁆)⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    rw [e1]
    exact L.mul_mem (L.inv_mem (haL y (hLT hy))) hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key x
  · intro hx
    have := key _ hx
    have e2 : a * (a * x * a⁻¹) * a⁻¹ = x := by
      calc a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [haa]; group
    rwa [e2] at this

theorem exists_two_group_conj_le [Finite G] {N A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hAN : A ≤ N) (hBN : B ≤ N) :
    ∃ k ∈ N, ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ N ∧ A ≤ S ∧ conjSubgroup k B ≤ S := by
  obtain ⟨P, hP⟩ := (hA.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (hB.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSubgroup_eq_of_sylow Q P
  refine ⟨(g : G), g.2, (P : Subgroup N).map N.subtype, ?_, ?_, ?_, ?_⟩
  · exact (P.isPGroup').map N.subtype
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x hx
    refine ⟨⟨x, hAN hx⟩, hP (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
    have hbN : b ∈ N := hBN hb
    have h1 : (⟨b, hbN⟩ : ↥N) ∈ Q := hQ (Subgroup.mem_subgroupOf.2 hb)
    have h2 : g * ⟨b, hbN⟩ * g⁻¹ ∈ conjSubgroup g (Q : Subgroup N) := conj_mem_conjSubgroup g h1
    rw [hg] at h2
    exact ⟨g * ⟨b, hbN⟩ * g⁻¹, h2, rfl⟩

theorem Sec3.false_of_caseB_core [Finite G] [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput) (hExc : Sec3TenExceptional)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (hD : Sec3Dih T T₁ n) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (T : Set G))
    (hSL : S ≤ Subgroup.normalizer (normIn T T₁ : Set G)) (hL₁S : normIn T₁ T ≤ S) {g a u : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) (ha : a ∈ conjSubgroup g (normIn T₁ T)) (ha1 : a ≠ 1)
    (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) (haS : a ∈ S)
    (hnc : ∃ l ∈ normIn T T₁, a * l ≠ l * a) : False := by
  have hLa := hS.isLElt_conj hg ha ha1
  have haN : a ∈ Subgroup.normalizer (T : Set G) := hLa.transv.1
  have haa : a * a = 1 := hLa.transv.2.1
  have haL : ∀ t ∈ T, ⁅t, a⁆ ∈ normIn T T₁ := fun t ht => by
    rcases hvals t ht with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hu
  by_cases hTa : conjSubgroup a T₁ = T₁
  · exact hS.false_of_conj_eq hn hn3 hD haN hTa haL hvals hnc
  have haNL : a ∈ Subgroup.normalizer (normIn T T₁ : Set G) :=
    mem_normalizer_of_values haa haL (normIn_le T T₁)
  have h38 := section3Eight h214 hInv hSz hnab hS hS2 hSN hSL hL₁S
  have hcomm : ∀ e ∈ normIn T₁ T, ∀ f ∈ conjSubgroup a (normIn T₁ T), e * f = f * e := by
    intro e he f hf
    have heK : e ∈ ⨆ s : S, conjSubgroup (s : G) (normIn T₁ T) :=
      Subgroup.mem_iSup_of_mem (⟨1, S.one_mem⟩ : S) (by
        show e ∈ conjSubgroup 1 (normIn T₁ T)
        rw [conjSubgroup_one]
        exact he)
    have hfK : f ∈ ⨆ s : S, conjSubgroup (s : G) (normIn T₁ T) :=
      Subgroup.mem_iSup_of_mem (⟨a, haS⟩ : S) hf
    exact elemAbelian_mul_comm h38 heK hfK
  obtain ⟨hN, ⟨eiso⟩⟩ := hD
  have hcard : Nat.card T = Nat.card (normIn T T₁) * 2 := hS.card_eq_two_mul_dihedral hn eiso
  have hB6 : SecB6 T T₁ S a := ⟨hS, hS2, hL₁S, haS, haa, haN, haNL, hTa, hcomm, hcard⟩
  have hD' : Sec3Dih T T₁ n := ⟨hN, ⟨eiso⟩⟩
  obtain ⟨m, hm0, hLm, -, -⟩ := hS.card_normIn_eq_two_pow
  have h3 := hS.three_le_card_normIn hn hn3 hD'
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m ≤ 1 := by omega
    have h2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  rcases Nat.lt_or_ge m 3 with hm | hm
  · have hm' : m = 2 := by omega
    have hL4 : Nat.card (normIn T T₁) = 4 := by rw [hLm, hm']; norm_num
    exact hExc G hnab T T₁ S n hS hn hn3 hD' hL4 a u hB6 hu hvals hnc
  · have h8 : 8 ≤ Nat.card (normIn T T₁) := by
      rw [hLm]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    exact hB6.false_of_inputs h214 hInv hSz hnab hn hn3 hD' hu hvals h8 hnc

end CFSG.CGT.Timmesfeld75

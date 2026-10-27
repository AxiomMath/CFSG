module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3

theorem exists_zpowers_eq_of_card_eq_two {G : Type*} [Group G] {Z : Subgroup G}
    (h : Nat.card Z = 2) : ∃ z : G, Z = Subgroup.zpowers z := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial Z := (Finite.one_lt_card_iff_nontrivial).1 (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  have hz1 : (z : G) ≠ 1 := fun h' => hz (Subtype.ext h')
  have hle : Subgroup.zpowers (z : G) ≤ Z := (Subgroup.zpowers_le).2 z.2
  have hord : orderOf (z : G) ∣ 2 := by
    rw [← h]
    have := orderOf_dvd_natCard (z : ↥Z)
    simpa [Subgroup.orderOf_coe] using this
  have hord2 : orderOf (z : G) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h' | h'
    · exact absurd (orderOf_eq_one_iff.1 h') hz1
    · exact h'
  refine ⟨z, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [Nat.card_zpowers, hord2, h]

theorem lemma2_4_25_0_of (hC55 : Lemma245_C55) (hQ : Lemma2_4_25_Q) : Lemma2_4_25_0 := by
  intro G _ _ T M H S L cfg
  have hcs := cfg.cs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hnS⟩ :=
    exists_mem_inf_normalizer_of_ne (p := 2) hcs.setting.isPGroup hcs.le_T hcs.ne_T
  have hSM₀ : S ≤ T ⊓ Subgroup.normalizer (S : Set G) :=
    le_inf hcs.le_T Subgroup.le_normalizer
  have hne' : S ≠ T ⊓ Subgroup.normalizer (S : Set G) := fun h => by
    rw [← h] at hn
    exact hnS hn
  obtain ⟨y, hyM, hyU⟩ :=
    hC55 G T M H S L hcs (T ⊓ Subgroup.normalizer (S : Set G)) hSM₀ inf_le_left hne' inf_le_right
  by_cases hyQ : conjR (blockU L) y ≤ s2Q1 S L
  ·
    obtain ⟨t, htS, htL, -⟩ : ∃ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
        conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
          ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
      rcases hcs.blocks with h | h
      · exact absurd h cfg.double
      · exact h
    have hLt : conjR L t⁻¹ ≠ L := by
      change L.map (MulAut.conj t⁻¹⁻¹).toMonoidHom ≠ L
      rw [inv_inv]
      exact htL
    refine ⟨y * t, T.mul_mem hyM.1 (hcs.le_T htS),
      Subgroup.mul_mem _ hyM.2 (Subgroup.le_normalizer htS), fun hle => hyU ?_⟩
    refine (le_inf hyQ ?_).trans (hQ G T M H S L cfg t⁻¹ (S.inv_mem htS) hLt)
    intro z hz
    change z ∈ conjSubgroup (blockU L) y at hz
    change z ∈ conjSubgroup (s2Q1 S L) t⁻¹
    rw [mem_conjSubgroup_iff] at hz ⊢
    have hmem : t⁻¹ * z * t⁻¹⁻¹ ∈ conjR (blockU L) (y * t) := by
      change _ ∈ conjSubgroup (blockU L) (y * t)
      rw [mem_conjSubgroup_iff]
      have : y * t * (t⁻¹ * z * t⁻¹⁻¹) * (y * t)⁻¹ = y * z * y⁻¹ := by group
      rw [this]
      exact hz
    exact hle hmem
  · exact ⟨y, hyM.1, hyM.2, hyQ⟩

theorem lemma2_4_25_of_steps (h0 : Lemma2_4_25_0) (hA : Lemma2_4_25_A) (hB : Lemma2_4_25_B)
    (hC : Lemma2_4_25_C) (hD : Lemma2_4_25_D) : Lemma2_4_25 := by
  intro G _ _ T M H S L hcs h5
  by_contra hne
  have cfg : A5Cfg2 G T M H S L := ⟨hcs, h5, hne⟩
  obtain ⟨x, hxT, hxN, hxU⟩ := h0 G T M H S L cfg
  have hAx := hA G T M H S L cfg x hxT hxN hxU
  have hBx := hB G T M H S L cfg x hxT hxN hxU hAx
  obtain ⟨K, hK⟩ := hC G T M H S L cfg x hxT hxN hxU hBx
  exact hD G T M H S L cfg x K hK

theorem a5_false_of_steps (h1 : Lemma2_4_29_1) (h2 : Lemma2_4_29_2) (h3 : Lemma2_4_29_3)
    (h4 : Lemma2_4_29_4) (h5 : Lemma2_4_29_5) (h6 : Lemma2_4_29_6) (h7 : Lemma2_4_29_7)
    (h8 : Lemma2_4_29_8) (h9 : Lemma2_4_29_9) (h10 : Lemma2_4_29_10) (h11 : Lemma2_4_29_11)
    {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} (cfg : A5Cfg G T M H S L) :
    False := by
  have s1 := h1 G T M H S L cfg
  have s2 := h2 G T M H S L cfg s1
  have s3 := h3 G T M H S L cfg s2
  have tc := h4 G T M H S L cfg s3
  have s5 := h5 G T M H S L cfg s3 tc
  have s6 := h6 G T M H S L cfg s5
  obtain ⟨z, hz⟩ := exists_zpowers_eq_of_card_eq_two s1.Z_card
  obtain ⟨u, hu, hu'⟩ := s6.exists_u
  have s7 := h7 G T M H S L cfg s6 z u hz hu hu'
  have hnc := h8 G T M H S L cfg z u s7
  obtain ⟨K, s9⟩ := h9 G T M H S L cfg z u s7 hnc
  have s10 := h10 G T M H S L cfg z u K s9
  exact h11 G T M H S L cfg z u K s10

theorem a5BlockExcluded_of_steps (h25 : Lemma2_4_25) (h1 : Lemma2_4_29_1)
    (h2 : Lemma2_4_29_2) (h3 : Lemma2_4_29_3) (h4 : Lemma2_4_29_4) (h5 : Lemma2_4_29_5)
    (h6 : Lemma2_4_29_6) (h7 : Lemma2_4_29_7) (h8 : Lemma2_4_29_8) (h9 : Lemma2_4_29_9)
    (h10 : Lemma2_4_29_10) (h11 : Lemma2_4_29_11) : A5BlockExcluded := by
  intro G _ _ T M H S L hcs h5'
  exact a5_false_of_steps h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ⟨hcs, h5', h25 G T M H S L hcs h5'⟩

end CFSG.QuasithinUnique.A5

module

public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Filter
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

local instance factPrimeSevenW4P : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

@[expose] def lieTuplesW4P : List (StatedLieTag × ℕ × ℕ × ℕ) :=
  [(.PSL, 2, 2, 1), (.PSL, 3, 2, 1), (.PSL, 4, 2, 1), (.PSU, 3, 2, 1), (.PSU, 4, 2, 1),
    (.PSp, 2, 2, 1), (.G2, 0, 2, 1), (.PSL, 2, 2, 2), (.PSL, 3, 2, 2), (.PSL, 2, 2, 3),
    (.PSL, 2, 3, 1), (.PSU, 3, 3, 1), (.PSp, 2, 3, 1), (.PSL, 2, 3, 2), (.PSL, 2, 5, 1),
    (.PSL, 2, 7, 1)]

@[expose] def filterCheckW4P (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (o ≤ 30240 → (t, n, p, f) ∈ lieTuplesW4P)

theorem lieSearch_w4P : lieSearchV W4MinusC.orthPlus8Primes 348364800 filterCheckW4P = true := by
  decide +kernel

theorem filterW4P_lieTuple {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hord : lieOrd t n (p ^ f) ∣ 348364800)
    (hle : lieOrd t n (p ^ f) ≤ 30240) : (t, n, p, f) ∈ lieTuplesW4P := by
  have hC := lieSearchV_sound W4MinusC.primes_orthPlus8 lieSearch_w4P ht hp hf hn hn0 hnB hadm hord
  simp only [filterCheckW4P, decide_eq_true_eq] at hC
  exact hC hle

theorem filterW4P_alt {n : ℕ} (hn5 : 5 ≤ n) (hord : n.factorial / 2 ∣ 348364800)
    (hle : n.factorial / 2 ≤ 30240) : n ≤ 8 := by
  by_contra h
  have h9 : 9 ≤ n := by omega
  have hd : Nat.factorial 9 / 2 ≤ n.factorial / 2 :=
    Nat.div_le_div_right (Nat.factorial_le h9)
  have hnum : Nat.factorial 9 / 2 = 181440 := by decide +kernel
  omega

theorem filterW4P_false_of_sporadic : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M →
    sporadicCard s ∣ 348364800 → sporadicCard s ≤ 30240 → False := by
  decide +kernel

section FilterBinders


theorem filter_W4Plus {X : Type} [Group X] [IsSimpleGroup X] (hX : CFSG.Blueprint.Catalog X)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hord : Nat.card X ∣ 348364800)
    (hle : Nat.card X ≤ 30240) :
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      Nonempty (X ≃* CFSG.AGLEmbedding.PSL2GF 7 1) ∨
      Nonempty (X ≃* CFSG.AGLEmbedding.PSL2GF 2 3) ∨
      LieModel X .PSU 3 3 1 ∨ LieModel X .PSL 3 2 2 ∨ LieModel X .PSp 2 3 1 := by
  rcases catalog_model_cases hX hnonab with ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, p, f, ht, hp, hf, hn, hn0,
    hnB, hadm, hc, hm⟩ | ⟨p, f, h⟩ | ⟨p, f, h⟩ | ⟨s, ⟨e⟩⟩
  ·
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcard : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rw [hcard] at hord hle
    exact Or.inl ⟨n, hn5, filterW4P_alt hn5 hord hle, ⟨e⟩⟩
  ·
    rw [hc] at hord hle
    have hmem := filterW4P_lieTuple ht hp hf hn hn0 hnB hadm hord hle
    simp only [lieTuplesW4P, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
    ·
      have h := LieModel.admissible hm
      rw [CFSG.Open.StatedLieAdmissible] at h
      exact absurd rfl h.2.2.2.1
    ·
      have hsc : StatedClassicalModel X .PSL 3 2 1 :=
        LieModel.statedClassicalModel_of_ne_zero (by decide) hm
      have h27 := CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hsc
      exact Or.inr (Or.inl (CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated (F := GaloisField 7 1)
        7 1 (by norm_num) (GaloisField.card 7 1 (by norm_num)) h27))
    ·
      exact Or.inl ⟨8, by norm_num, by norm_num,
        CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hm⟩
    ·
      have h := LieModel.admissible hm
      rw [CFSG.Open.StatedLieAdmissible] at h
      exact absurd rfl h.2.2.2
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (CFSG.GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hm)))))
    ·
      have h := LieModel.admissible hm
      rw [CFSG.Open.StatedLieAdmissible] at h
      exact absurd rfl h.2.2.2
    ·
      have h := LieModel.admissible hm
      rw [CFSG.Open.StatedLieAdmissible] at h
      norm_num at h
    ·
      have h60 : Nat.card X = 60 := by
        rw [hc]
        decide +kernel
      haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [h60]; decide)
      exact Or.inl ⟨5, by norm_num, by norm_num,
        CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60⟩
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    ·
      exact Or.inr (Or.inr (Or.inl
        (CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel 2 3 (by norm_num)
          (GaloisField.card 2 3 (by norm_num)) hm)))
    ·
      have h := LieModel.admissible hm
      rw [CFSG.Open.StatedLieAdmissible] at h
      exact absurd rfl h.2.2.2.2
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))
    ·
      have hsc : StatedClassicalModel X .PSL 2 3 2 :=
        LieModel.statedClassicalModel_of_ne_zero (by decide) hm
      exact Or.inl ⟨6, by norm_num, by norm_num,
        CFSG.StandardType.nonempty_alternatingGroup_of_psl_two_nine hsc⟩
    ·
      have h60 : Nat.card X = 60 := by
        rw [hc]
        decide +kernel
      haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [h60]; decide)
      exact Or.inl ⟨5, by norm_num, by norm_num,
        CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60⟩
    ·
      exact Or.inr (Or.inl (CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel 7 1 (by norm_num)
        (GaloisField.card 7 1 (by norm_num)) hm))
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hord) (by decide +kernel)
  ·
    exact absurd ((thirteen_dvd_card_of_reeTitsModel_Tits h).trans hord) (by decide +kernel)
  ·
    obtain ⟨hTh, hM, hcard⟩ := sporadic_cases e hord (by decide +kernel) (by decide +kernel)
    rw [hcard] at hord hle
    exact (filterW4P_false_of_sporadic s hTh hM hord hle).elim

end FilterBinders

end CFSG.GF2Type.Smith1979.OmegaPlus

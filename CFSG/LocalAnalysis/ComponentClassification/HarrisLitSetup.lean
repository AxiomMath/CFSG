module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitReduction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem Config.three_le_twoRank [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}
    (h : Config t L p f) : 3 ≤ Open.twoRank X := by
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) := fun h2 =>
    absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := L)) h2)
      (by norm_num)
  have hL : 2 ≤ Open.pRank 2 (⊤ : Subgroup L) := by
    rw [← SectionRank.pRank_quotient_eq (pPrimeCore 2 L) hodd]
    exact h.two_le_pRank_bar
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup L)
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq, pow_orderOf_eq_one]
  have hcomm : ∀ (a : E) (b : zpowers t),
      Commute (L.subtype.comp E.subtype a) ((zpowers t).subtype b) := by
    rintro a ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact Commute.zpow_right (mem_centralizer_singleton_iff.mp (h.le_centralizer (a : L).2)) k
  let φ : E × zpowers t →* X :=
    MonoidHom.noncommCoprod (L.subtype.comp E.subtype) (zpowers t).subtype hcomm
  have hφ : ∀ x : E × zpowers t, φ x = ((x.1 : L) : X) * (x.2 : X) := fun _ => rfl
  have hzp : ∀ s ∈ zpowers t, s = 1 ∨ s = t := by
    intro s hs
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow, one_mul,
        zpow_one]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [hφ] at hab
    rcases hzp b b.2 with hb | hb
    · rw [hb, mul_one] at hab
      have ha : a = 1 := Subtype.ext (Subtype.ext hab)
      have hb' : b = 1 := Subtype.ext hb
      rw [ha, hb']
      rfl
    · exfalso
      rw [hb] at hab
      have : t = ((a : L) : X)⁻¹ := (eq_inv_of_mul_eq_one_right hab)
      exact h.not_mem (this ▸ L.inv_mem (a : L).2)
  have hcommA : ∀ a b : E × zpowers t, a * b = b * a := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    refine Prod.ext (hE.1.is_comm.comm a₁ a₂) (Subtype.ext ?_)
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp b₁.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b₂.2
    change (b₁ : X) * b₂ = b₂ * b₁
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self t i j).eq
  have hpow : ∀ a : E × zpowers t, a ^ 2 = 1 := by
    rintro ⟨a, b⟩
    refine Prod.ext (Subtype.ext (hE.2 _ a.2)) (Subtype.ext ?_)
    rcases hzp b b.2 with hb | hb
    · change (b : X) ^ 2 = 1
      rw [hb, one_pow]
    · change (b : X) ^ 2 = 1
      rw [hb, ht2]
  have hcardA : Nat.card (E × zpowers t) = 2 ^ (Open.pRank 2 (⊤ : Subgroup L) + 1) := by
    rw [Nat.card_prod, hcard, Nat.card_zpowers, h.orderOf_eq, pow_succ]
  have := SectionRank.le_pRank_of_injective one_lt_two hcommA hpow hcardA φ hinj
    (H := (⊤ : Subgroup X)) le_top
  change 3 ≤ Open.pRank 2 (⊤ : Subgroup X)
  omega

theorem exists_max_config [Finite X]
    (h : ∃ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f) :
    ∃ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f ∧
      ∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
        twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X)) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (t : X) (L : Subgroup X) (p f : ℕ), Config t L p f ∧
    twoPart (centralizer ({t} : Set X)) = n
  have hbound : ∀ n, P n → n ≤ Nat.card X := by
    rintro n ⟨t, L, p, f, -, rfl⟩
    exact (Nat.ordProj_le 2 Nat.card_pos.ne').trans (Subgroup.card_le_card_group _)
  obtain ⟨t, L, p, f, hc⟩ := h
  have hP : P (twoPart (centralizer ({t} : Set X))) := ⟨t, L, p, f, hc, rfl⟩
  obtain ⟨t₀, L₀, p₀, f₀, hc₀, hm₀⟩ := Nat.findGreatest_spec (hbound _ hP) hP
  refine ⟨t₀, L₀, p₀, f₀, hc₀, fun t' L' p' f' hc' => ?_⟩
  rw [hm₀]
  exact Nat.le_findGreatest (hbound _ ⟨t', L', p', f', hc', rfl⟩) ⟨t', L', p', f', hc', rfl⟩

theorem sq_mod_sixteen {p f : ℕ} (hp : Odd p) (hf : Even f) :
    p ^ f % 16 = 1 ∨ p ^ f % 16 = 9 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← two_mul, mul_comm, pow_mul, Nat.pow_mod]
  have h16 : (p ^ k) % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hodd : (p ^ k) % 2 = 1 := Nat.odd_iff.mp hp.pow
  have h2 : (p ^ k) % 16 % 2 = 1 := by omega
  interval_cases (p ^ k) % 16 <;> simp_all

theorem catalog_of_oddLieType {Y : Type} [Group Y] (h : Blueprint.OddLieType Y) :
    Blueprint.Catalog Y := by
  obtain ⟨t, n, p, f, -, -, -, hm⟩ := h
  exact Blueprint.lieModel_catalog Y t n p f hm

theorem catalog_of_HS {Y : Type} [Group Y] (e : Y ≃* Blueprint.NativeSporadic.HS) :
    Blueprint.Catalog Y :=
  .inr (.inr (.inr (.inr ⟨.HS, ⟨e⟩⟩)))

theorem theoremOne_of_inputs (hGH : UFrontier.GH74ModelsInput)
    (hHSF : GSLit.HarrisSolomonFritzInput) (hHS : HarrisSolomonDihedralInput)
    (h4 : SectionFour) : TheoremOne := by
  intro X _ _ _ hnonab hK t L p f hc
  by_contra hcat
  obtain ⟨t, L, p, f, hc, hmax⟩ := exists_max_config ⟨t, L, p, f, hc⟩
  have hsect : ¬ SectionalRankLeFour X := fun hs =>
    hcat (UFrontier.catalog_of_gh74 hGH hnonab hc.three_le_twoRank hs)
  have hD := hHS X hnonab hsect t L p f hc
  have h16 : 16 ∣ p ^ f - 1 := by
    rcases sq_mod_sixteen (hc.prime.odd_of_ne_two hc.ne_two)
        (hD.even p f hc.prime hc.ne_two hc.lieModel) with h1 | h9
    · have := hc.five_le
      omega
    · exfalso
      have h8 := hc.factorization_card_bar h9
      have hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L),
          IsCyclic (P : Subgroup ↥(coreActionKernel L)) := fun P =>
        isCyclic_of_prime_card (hD.card_sylow P)
      obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (Bar L)))
      have hS : Nat.card (S : Subgroup (Bar L)) = 8 := by
        rw [S.card_eq_multiplicity, h8]
        norm_num
      rcases hHSF X hnonab t hc.orderOf_eq L hc.le_centralizer hc.isPComponent
          hc.isSimpleGroup_bar (hc.pRank_bar_eq_two h8) ⟨S, hS⟩ hcyc with hodd | ⟨-, ⟨e⟩⟩
      · exact hcat (catalog_of_oddLieType hodd)
      · exact hcat (catalog_of_HS e)
  exact h4 X hnonab hK hcat hsect t L p f hc hmax hD h16

theorem harrisInput_of_sectionFour (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hGH : UFrontier.GH74ModelsInput) (hHSF : GSLit.HarrisSolomonFritzInput)
    (hHS : HarrisSolomonDihedralInput) (h4 : SectionFour) : GSLit.HarrisInput :=
  harrisInput_of_theoremOne hCU (theoremOne_of_inputs hGH hHSF hHS h4)

end CFSG.ComponentClassification.HarrisLit

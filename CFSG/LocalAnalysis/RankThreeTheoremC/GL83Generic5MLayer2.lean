module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5L54
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.RankThree.PartOne.D4RC.Burnside

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_mem_Z_of_mem_normalizer (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {Y : Subgroup G} (hY1 : Y ≠ ⊥)
    (hYZ : Y ≤ centralizer ((gen5L x : Subgroup G) : Set G))
    (hcase : IsSylowOf p (gen5U (P : Subgroup G) x) (normalizer (Y : Set G)) ∨
      x ∈ normalizer (Y : Set G)) {g : G}
    (hgU : g ∈ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G))
    (hgY : g ∈ normalizer (Y : Set G)) (hgp : Nat.Coprime p (orderOf g)) :
    g ∈ centralizer ((gen5L x : Subgroup G) : Set G) :=
  gen5_L54 hG K1 Sch hK hExcl hl hY1 hYZ hcase (W := zpowers g) (by rwa [Nat.card_zpowers])
    (zpowers_le.mpr hgY) (le_normalizer_zpowers_of_mem_centralizer hgU) (mem_zpowers g)

theorem gen5_not_coprime_card (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {J : Subgroup G} (hJperf : ⁅J, J⁆ = J)
    (hJU : J ≤ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G)) (hxJ : x ∈ J)
    (hJcyc : ∀ Q : Subgroup G, Q ≤ J → IsPGroup p Q → IsCyclic Q) :
    ¬ Nat.Coprime (Nat.card ↥(J ⊓ centralizer ((gen5L x : Subgroup G) : Set G))) (p - 1) := by
  intro hcop
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := gen5_five_le hG hl; omega
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := hl.generic
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxpg : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨S, hS, hxS⟩ := exists_isSylowOf_ge_of_le (zpowers_le.mpr hxJ) hxpg
  obtain ⟨hSJ, hSp, hSidx⟩ := isSylowOf_iff.mp hS
  have hSc : IsCyclic S := hJcyc S hSJ hSp
  have hxS' : x ∈ S := hxS (mem_zpowers x)
  have hS1 : S ≠ ⊥ := fun h => hx1 (by rw [h] at hxS'; exact (mem_bot).mp hxS')
  obtain ⟨g, hgJ, hgN, a, haS, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt hp2 hJperf hSJ hSp hSidx hSc hS1
  have ha1 : a ≠ 1 := fun h => hga (by rw [h, mul_one, mul_inv_cancel])
  have hax : a ∈ zpowers x := by
    rw [← zpowers_eq_of_orderOf_eq_of_isCyclic hSc haS hxS'
      (by rw [orderOf_eq_prime hap ha1, hxo])]
    exact mem_zpowers a
  have hgxS : g * x * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgN x).mp hxS'
  have hgx : g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact zpowers_eq_of_orderOf_eq_of_isCyclic hSc hgxS hxS'
      (MulEquiv.orderOf_eq (MulAut.conj g) x)
  have hgC : g ∉ centralizer ((zpowers x : Subgroup G) : Set G) := fun h => hga (by
    rw [← mem_centralizer_iff.mp h a hax, mul_inv_cancel_right])
  obtain ⟨c, m, hm, -, -, hmo⟩ := exists_orderOf_pow_eq p hp g
  have hxZ := (gen5_Z hG hl).1
  have hgZ : g ^ (p ^ c) ∈ centralizer ((gen5L x : Subgroup G) : Set G) :=
    gen5_mem_Z_of_mem_normalizer hG K1 Sch hK hExcl hl (Y := zpowers x)
      (fun h => hx1 (by simpa [h] using mem_zpowers x)) (zpowers_le.mpr hxZ)
      (Or.inr (le_normalizer (mem_zpowers x))) (pow_mem (hJU hgJ) _) (pow_mem hgx _)
      (hmo ▸ (Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hgR : g ^ (p ^ c) ∈ J ⊓ centralizer ((gen5L x : Subgroup G) : Set G) :=
    ⟨pow_mem hgJ _, hgZ⟩
  have hpow :
      g ^ (p ^ c * Nat.card ↥(J ⊓ centralizer ((gen5L x : Subgroup G) : Set G))) = 1 := by
    rw [pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    exact Subgroup.orderOf_dvd_natCard _ hgR
  have hp1 : Nat.Coprime p (p - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
    have := hp.two_le
    have := Nat.le_of_dvd (by omega) h
    omega
  refine hgC (mem_centralizer_of_pow_mem_of_coprime_totient inferInstance hgx
    (hpow ▸ one_mem _) ?_)
  rw [Nat.card_zpowers, hxo, Nat.totient_prime hp]
  exact Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.pow_left c hp1, hcop⟩

theorem gen5_exists_sylow_case (hG : Gen5Global G) (hl : Gen5Local G p P M x) {J : Subgroup G}
    (hJU : J ≤ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G))
    (hJconj : ∀ d ∈ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G), ∀ j ∈ J,
      d * j * d⁻¹ ∈ J) {f : ℕ} [Fact f.Prime] (hfp : f < p) {F₀ : Subgroup G}
    (hF₀ : IsSylowOf f F₀ (J ⊓ centralizer ((gen5L x : Subgroup G) : Set G)))
    (hF₀c : IsCyclic F₀) :
    ∃ F : Subgroup G, IsSylowOf f F (J ⊓ centralizer ((gen5L x : Subgroup G) : Set G)) ∧
      IsCyclic F ∧ (IsSylowOf p (gen5U (P : Subgroup G) x) (normalizer (F : Set G)) ∨
        x ∈ normalizer (F : Set G)) := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  have hF₀Z := hF₀.le.trans inf_le_right
  have hUN : gen5U (P : Subgroup G) x ≤ normalizer (F₀ : Set G) := fun u hu =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun z hz =>
      (mem_centralizer_iff.mp (hF₀Z hz) u hu.2).symm)
  rcases gen5_dichotomy_N hG hl hUN with hsyl | ⟨d, hd, hdx⟩
  · exact ⟨F₀, hF₀, hF₀c, Or.inl hsyl⟩
  set F := F₀.map (MulAut.conj d⁻¹).toMonoidHom with hF
  have hmemF : ∀ h, h ∈ F ↔ d * h * d⁻¹ ∈ F₀ := fun h => by
    rw [hF, mem_map_equiv]
    simp [MulAut.conj_apply]
  have hFJ : F ≤ J := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hJconj d⁻¹ (inv_mem hd) y (hF₀.le hy).1
  have hFp : IsPGroup f F := hF₀.isPGroup.map _
  have hFc : IsCyclic F :=
    (F₀.equivMapOfInjective _ (MulAut.conj d⁻¹).injective).isCyclic.mp hF₀c
  have hxN : x ∈ normalizer (F : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    rw [hmemF, hmemF]
    have he : d * (x * h * x⁻¹) * d⁻¹ = d * x * d⁻¹ * (d * h * d⁻¹) * (d * x * d⁻¹)⁻¹ := by
      group
    rw [he]
    exact mem_normalizer_iff.mp hdx (d * h * d⁻¹)
  have hxC : x ∈ centralizer (F : Set G) :=
    mem_centralizer_of_pow_mem_of_coprime_totient hFc hxN
      (by rw [hl.generic.2.1.2.2.1]; exact one_mem _)
      (coprime_totient_card_of_isPGroup Fact.out hFp fun q hq hqp =>
        ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp) ▸ hfp)
  obtain ⟨e⟩ := gen5_psl hG hl
  have hFZ : F ≤ centralizer ((gen5L x : Subgroup G) : Set G) := by
    refine le_centralizer_layer_of_coprime_of_isGenericPoint hl.generic le_rfl e
      (fun y hy => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC y hy)) ?_ ?_
    · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hFp
      rw [hn]
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp Fact.out).mp (hp.dvd_of_dvd_pow hdvd)
      omega
    · intro u hu
      exact centralizer_le_normalizer _
        (le_centralizer_iff.mp (hFJ.trans hJU) ⟨hu.1.1, hu.2⟩)
  refine ⟨F, isSylowOf_of_card (le_inf hFJ hFZ) ?_, hFc, Or.inr hxN⟩
  rw [card_map_of_injective (MulAut.conj _).injective]
  exact hF₀.card_eq

theorem gen5_false_of_perfect_lift (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {J : Subgroup G} (hJperf : ⁅J, J⁆ = J)
    (hJU : J ≤ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G)) (hxJ : x ∈ J)
    (hJconj : ∀ d ∈ centralizer ((gen5U (P : Subgroup G) x : Subgroup G) : Set G), ∀ j ∈ J,
      d * j * d⁻¹ ∈ J)
    (hJcyc : ∀ Q : Subgroup G, Q ≤ J → IsPGroup p Q → IsCyclic Q) : False := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hxZ, hZodd, -⟩ := gen5_Z hG hl
  obtain ⟨-, ⟨-, hx1, -, -, -⟩, -, -⟩ := hl.generic
  set Z := centralizer ((gen5L x : Subgroup G) : Set G) with hZ
  set U := gen5U (P : Subgroup G) x with hU
  set R := J ⊓ Z with hR
  have hR1 : Nat.card R ≠ 1 := fun h => hx1 (by
    have h1 : x ∈ R := ⟨hxJ, hxZ⟩
    rw [Subgroup.card_eq_one.mp h] at h1
    exact (mem_bot).mp h1)
  set f := (Nat.card R).minFac with hfdef
  have hf : f.Prime := Nat.minFac_prime hR1
  have : Fact f.Prime := ⟨hf⟩
  have hfR : f ∣ Nat.card R := Nat.minFac_dvd _
  have hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card R → f ≤ q := fun q hq hqR =>
    Nat.minFac_le_of_dvd hq.two_le hqR
  have hf2 : f ≠ 2 := fun h => hZodd ((h ▸ hfR).trans (card_dvd_of_le inf_le_right))
  have hfp : f < p := by
    obtain ⟨q, hq, hqR, hqp⟩ := Nat.Prime.not_coprime_iff_dvd.mp
      (gen5_not_coprime_card hG K1 Sch hK hExcl hl hJperf hJU hxJ hJcyc)
    have h1 := hmin q hq hqR
    have := hp.two_le
    have h2 := Nat.le_of_dvd (by omega) hqp
    omega
  obtain ⟨F₀, hF₀⟩ := exists_isSylowOf f R
  have hF₀c : IsCyclic F₀ := gen5_isCyclic_of_le_Z hG K1 Sch hK hExcl hl hf hf2 hfp.ne
    (hF₀.le.trans inf_le_right) hF₀.isPGroup
  obtain ⟨F, hFR, hFc, hcase⟩ := gen5_exists_sylow_case hG hl hJU hJconj hfp hF₀ hF₀c
  have hFp := hFR.isPGroup
  have hFJ : F ≤ J := hFR.le.trans inf_le_left
  have hFZ : F ≤ Z := hFR.le.trans inf_le_right
  have hF1 : F ≠ ⊥ := by
    intro h
    have := (isSylowOf_iff.mp hFR).2.2
    rw [h, relIndex_bot_left] at this
    exact this hfR
  have hNJ : ∀ g ∈ J, g ∈ normalizer (F : Set G) → g ∈ centralizer (F : Set G) := by
    intro g hgJ hgN
    obtain ⟨c, m, hm, -, -, hmo⟩ := exists_orderOf_pow_eq p hp g
    have hgZ : g ^ (p ^ c) ∈ Z := gen5_mem_Z_of_mem_normalizer hG K1 Sch hK hExcl hl hF1 hFZ
      hcase (pow_mem (hJU hgJ) _) (pow_mem hgN _)
      (hmo ▸ (Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    have hgC := mem_centralizer_of_mem_normalizer_of_minFac hFR hFc hmin
      ⟨pow_mem hgJ _, hgZ⟩ (pow_mem hgN _)
    refine mem_centralizer_of_pow_mem_of_coprime_totient hFc hgN hgC
      (coprime_totient_card_of_isPGroup hf hFp fun q hq hqp => ?_)
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp)]
    exact hfp
  have hFidx : ¬ f ∣ F.relIndex J := by
    obtain ⟨S, hS, hFS⟩ := exists_isSylowOf_ge_of_le hFJ hFp
    obtain ⟨hSJ, hSp, hSidx⟩ := isSylowOf_iff.mp hS
    by_cases hFeq : F = S
    · exact hFeq ▸ hSidx
    obtain ⟨s, hsS, hsN, hsF⟩ := exists_mem_normalizer_not_mem_of_isPGroup hFS hFeq hSp
    have hW : IsPGroup f ↥(zpowers s ⊔ F) := IsPGroup.to_sup_of_normal_right'
      (hSp.to_le (zpowers_le.mpr hsS)) hFp (zpowers_le.mpr hsN)
    have hWS : zpowers s ⊔ F ≤ S := sup_le (zpowers_le.mpr hsS) hFS
    have hWp : Nat.Coprime p (Nat.card ↥(zpowers s ⊔ F)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hf).mpr hfp.ne')
    have hWZ := gen5_L54 hG K1 Sch hK hExcl hl hF1 hFZ hcase hWp
      (sup_le (zpowers_le.mpr hsN) le_normalizer)
      ((le_centralizer_iff.mp ((hWS.trans hSJ).trans hJU)).trans (centralizer_le_normalizer _))
    have hWF := hFR.eq_of_le le_sup_right (le_inf (hWS.trans hSJ) hWZ) hW
    exact (hsF (hWF ▸ (le_sup_left : zpowers s ≤ zpowers s ⊔ F) (mem_zpowers s))).elim
  obtain ⟨g, hgJ, hgN, a, haF, -, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt hf2 hJperf hFJ hFp hFidx hFc hF1
  exact hga (by rw [← mem_centralizer_iff.mp (hNJ g hgJ hgN) a haF, mul_inv_cancel_right])

end CFSG.LocalAnalysis.RankThreeTheoremC

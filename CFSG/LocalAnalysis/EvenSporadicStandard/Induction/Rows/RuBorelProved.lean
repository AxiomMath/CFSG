module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuBorelGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocalProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLink

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.RuStd CFSG.EvenSporadicStandard.Induction.RuSz

section Borel


theorem exists_sylow_conj {R'' : Subgroup (Equiv.Perm (Fin 4060))} (hR'' : R'' ≤ K0)
    (hcard : Nat.card R'' = 64) :
    ∃ k ∈ K0, ∀ x, x ∈ R'' ↔ k⁻¹ * x * k ∈ R0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K0 := K0_finite
  have h64 : (2 : ℕ) ^ (Nat.card K0).factorization 2 = 64 := by
    rw [card_K0, show (29120 : ℕ) = 2 ^ 6 * 455 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hR0K : R0 ≤ K0 := inf_le_left
  have hA : Nat.card (R0.subgroupOf K0) = 2 ^ (Nat.card K0).factorization 2 := by
    rw [h64, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0K).toEquiv, card_R0]
  have hB : Nat.card (R''.subgroupOf K0) = 2 ^ (Nat.card K0).factorization 2 := by
    rw [h64, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'').toEquiv, hcard]
  let S₁ : Sylow 2 K0 := Sylow.ofCard (R0.subgroupOf K0) hA
  let S₂ : Sylow 2 K0 := Sylow.ofCard (R''.subgroupOf K0) hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K0 S₁ S₂
  refine ⟨(g : Equiv.Perm (Fin 4060)), g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxK : x ∈ K0 := hR'' hx
    have h1 : (⟨x, hxK⟩ : K0) ∈ S₂ := Subgroup.mem_subgroupOf.2 hx
    rw [← hg, CFSG.RankThree.mem_smul_sylow_iff] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hx
    have hxK : x ∈ K0 := by
      have : (g : Equiv.Perm (Fin 4060)) * ((g : Equiv.Perm (Fin 4060))⁻¹ * x * g) *
          (g : Equiv.Perm (Fin 4060))⁻¹ ∈ K0 :=
        K0.mul_mem (K0.mul_mem g.2 (hR0K hx)) (K0.inv_mem g.2)
      simpa [mul_assoc] using this
    have h1 : g⁻¹ * (⟨x, hxK⟩ : K0) * g ∈ S₁ := Subgroup.mem_subgroupOf.2 (by simpa using hx)
    rw [← CFSG.RankThree.mem_smul_sylow_iff, hg] at h1
    exact Subgroup.mem_subgroupOf.1 h1

theorem N'_le_K0 : N' ≤ K0 := by
  rw [N', closure_le]
  rintro _ ⟨w, -, rfl⟩
  exact kG_mem w

theorem card_centralizer_borel_le {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) {u : Y}
    (hu : orderOf u = 2) {Kl : Subgroup Y} (hKu : ∀ k ∈ Kl, k * u = u * k)
    (hKcard : Nat.card Kl = 29120) {Rl : Subgroup Y} (hRK : Rl ≤ Kl) (hRcard : Nat.card Rl = 64) :
    Nat.card (Subgroup.centralizer ((Subgroup.normalizer (Rl : Set Y) ⊓ Kl : Subgroup Y) :
      Set Y)) ≤ 4 := by
  obtain ⟨e, he⟩ := exists_std_equiv hY hu (card_centralizer_of_pair hY hu hKu hKcard)
  have hmapK := map_eq_K0 he hKu hKcard
  have hfinR : Finite Rl := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
  have hR''K : Rl.map (emb e) ≤ K0 := hmapK ▸ Subgroup.map_mono hRK
  have hR''card : Nat.card (Rl.map (emb e)) = 64 := by
    rw [Subgroup.card_map_of_injective (emb_injective e), hRcard]
  obtain ⟨k, hkK, hk⟩ := exists_sylow_conj hR''K hR''card
  have hkP : k ∈ ruP := ruL_le (K0_le_L hkK)
  let θ : Y → Equiv.Perm (Fin 4060) := fun c => k⁻¹ * emb e c * k
  have hθinj : Function.Injective θ := by
    intro c₁ c₂ h
    apply emb_injective e
    have h' := congrArg (fun z => k * z * k⁻¹) h
    simpa [θ, mul_assoc] using h'
  have hθmem : ∀ c ∈ Subgroup.centralizer
      ((Subgroup.normalizer (Rl : Set Y) ⊓ Kl : Subgroup Y) : Set Y), θ c ∈ DN := by
    intro c hc
    refine mem_DN.2 ⟨ruP.mul_mem (ruP.mul_mem (ruP.inv_mem hkP) (emb_mem e c)) hkP, ?_⟩
    intro n hn
    have hnK : n ∈ K0 := N'_le_K0 hn
    have hnN : n ∈ Subgroup.normalizer (R0 : Set (Equiv.Perm (Fin 4060))) := N'_le_normalizer hn
    have hnR := Subgroup.mem_normalizer_iff.1 hnN
    set n'' : Equiv.Perm (Fin 4060) := k * n * k⁻¹ with hn''
    have hn''K : n'' ∈ K0 := K0.mul_mem (K0.mul_mem hkK hnK) (K0.inv_mem hkK)
    obtain ⟨y, hy⟩ := emb_surj e (ruL_le (K0_le_L hn''K))
    have hyK : y ∈ Kl := by
      have : emb e y ∈ Kl.map (emb e) := hmapK ▸ (hy ▸ hn''K)
      obtain ⟨k', hk', hkk⟩ := this
      exact emb_injective e hkk ▸ hk'
    have hyN : y ∈ Subgroup.normalizer (Rl : Set Y) := by
      refine mem_normalizer_of_conj_mem (fun r hr => ?_)
      have hrR : emb e r ∈ Rl.map (emb e) := Subgroup.mem_map_of_mem _ hr
      have hr0 := (hk _).1 hrR
      have h1 := (hnR _).1 hr0
      have h2 : k * (n * (k⁻¹ * emb e r * k) * n⁻¹) * k⁻¹ ∈ Rl.map (emb e) := (hk _).2 (by
        simpa [mul_assoc] using h1)
      have h3 : k * (n * (k⁻¹ * emb e r * k) * n⁻¹) * k⁻¹ = emb e (y * r * y⁻¹) := by
        rw [map_mul, map_mul, map_inv, hy, hn'']
        group
      rw [h3] at h2
      obtain ⟨r', hr', hrr⟩ := h2
      exact emb_injective e hrr ▸ hr'
    have hyc : y * c = c * y :=
      (Subgroup.mem_centralizer_iff.1 hc y ⟨hyN, hyK⟩)
    have h4 : n'' * emb e c = emb e c * n'' := by
      rw [← hy, ← map_mul, ← map_mul, hyc]
    show n * (k⁻¹ * emb e c * k) = k⁻¹ * emb e c * k * n
    calc n * (k⁻¹ * emb e c * k) = k⁻¹ * (n'' * emb e c) * k := by rw [hn'']; group
      _ = k⁻¹ * (emb e c * n'') * k := by rw [h4]
      _ = k⁻¹ * emb e c * k * n := by rw [hn'']; group
  have : Finite DN := inferInstance
  calc Nat.card (Subgroup.centralizer ((Subgroup.normalizer (Rl : Set Y) ⊓ Kl : Subgroup Y) :
        Set Y))
      ≤ Nat.card DN := Nat.card_le_card_of_injective
        (fun c => ⟨θ c, hθmem c c.2⟩) (fun c₁ c₂ h => Subtype.ext (hθinj (congrArg Subtype.val h)))
    _ ≤ 4 := card_DN_le

theorem ruNormalizerFacts_proved : RuNormalizerFacts := by
  intro G _ L K u hL hQ R hRK hRcard
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  set N : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ K with hN
  have hNK : N ≤ K := inf_le_right
  have hNL : N ≤ L := hNK.trans hKL
  have hRL : R ≤ L := hRK.trans hKL
  haveI hfinL : Finite ↥L :=
    Nat.finite_of_card_ne_zero (by rw [(ruFacts_of_isSporadic hL).card_eq]; norm_num)
  haveI : Finite ↥(L ⊓ centralizer (N : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hup : Nat.card ↥(L ⊓ centralizer (N : Set G)) ≤ 4 := by
    set u' : ↥L := ⟨u, huL⟩ with hu'
    have hu2' : orderOf u' = 2 := by rw [hu', Subgroup.orderOf_mk]; exact hu2
    have hKu' : ∀ k ∈ K.subgroupOf L, k * u' = u' * k := fun k hk =>
      Subtype.ext (hKu (k : G) (Subgroup.mem_subgroupOf.1 hk))
    have hcardKl : Nat.card (K.subgroupOf L) = 29120 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
      exact hcard
    have hRl : R.subgroupOf L ≤ K.subgroupOf L := fun x hx => hRK hx
    have hRlcard : Nat.card (R.subgroupOf L) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, hRcard]
      norm_num
    have hfinR : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
    have hY := card_centralizer_borel_le hL hu2' hKu' hcardKl hRl hRlcard
    have hsub : (Subgroup.normalizer ((R.subgroupOf L : Subgroup ↥L) : Set ↥L) ⊓
        K.subgroupOf L : Subgroup ↥L) ≤ N.subgroupOf L := by
      intro y hy
      refine Subgroup.mem_subgroupOf.2 ⟨?_, Subgroup.mem_subgroupOf.1 hy.2⟩
      refine mem_normalizer_of_conj_mem (fun r hr => ?_)
      have hrL : r ∈ L := hRL hr
      have h1 := (Subgroup.mem_normalizer_iff.1 hy.1 ⟨r, hrL⟩).1 (Subgroup.mem_subgroupOf.2 hr)
      exact Subgroup.mem_subgroupOf.1 h1
    rw [← card_centralizer_subgroupOf hNL]
    exact (Subgroup.card_le_of_le (Subgroup.centralizer_le (fun x hx => hsub hx))).trans hY
  have hlow : 4 ≤ Nat.card ↥(L ⊓ centralizer (N : Set G)) := by
    have h4 := (ruPair_analysis hL hQ').2.2.2
    rw [← h4]
    exact Subgroup.card_le_of_le (inf_le_inf_left L (Subgroup.centralizer_le (fun x hx => hNK hx)))
  exact le_antisymm hup hlow

end Borel

end CFSG.EvenSporadicStandard.Induction

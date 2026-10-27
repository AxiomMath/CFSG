module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResCB2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResEA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSyl
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem not_two_dvd_index_of_odd_mul {Y : Type*} [Group Y] [Finite Y] (O P : Subgroup Y)
    [O.Normal] (hO : Odd (Nat.card O)) (h : ∀ y : Y, ∃ o ∈ O, ∃ p ∈ P, y = o * p) :
    ¬ 2 ∣ P.index := by
  let f : P →* Y ⧸ O := (QuotientGroup.mk' O).comp P.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, p, hp, rfl⟩ := h y
    refine ⟨⟨p, hp⟩, ?_⟩
    show QuotientGroup.mk p = QuotientGroup.mk (o * p)
    rw [QuotientGroup.eq]
    have := (inferInstance : O.Normal).conj_mem o ho p⁻¹
    simpa [mul_assoc] using this
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.2 hf, Subgroup.card_top] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have h3 := Subgroup.card_mul_index P
  have hq : 0 < Nat.card (Y ⧸ O) := Nat.card_pos
  have h4 : P.index * Nat.card f.ker = Nat.card O := by
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    calc Nat.card (Y ⧸ O) * (P.index * Nat.card f.ker)
        = P.index * (Nat.card f.ker * Nat.card (Y ⧸ O)) := by ring
      _ = P.index * Nat.card P := by rw [h1]
      _ = Nat.card Y := by rw [mul_comm]; exact h3
      _ = Nat.card (Y ⧸ O) * Nat.card O := h2
  intro hdvd
  have : 2 ∣ Nat.card O := h4 ▸ Dvd.dvd.mul_right hdvd _
  exact (Nat.not_even_iff_odd.2 hO) (even_iff_two_dvd.2 this)

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem false_of_stepA
    (hG : Goldschmidt74Cor4) (h : Setup L A C z) (hty : SextetType L A)
    (hStepA : ∀ y : egQD C, ∃ o ∈ fusionOddCore (egQD C),
      ∃ p ∈ centralizer ({zt h} : Set (egQD C)), y = o * p) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAL, e, hA⟩ := id hty
  let σ := Sym6.tetE hA
  have hσs : Function.Surjective σ := Sym6.tetE_surjective hA hAL
  have hσA : A.subgroupOf (egNL L A) ≤ σ.ker := Sym6.le_ker_tetE hA
  have hσk : Nat.card σ.ker = 192 := Sym6.card_ker_tetE hA hAL
  let H : Subgroup (egNL L A) := (alternatingGroup (Fin 6)).comap σ
  have hH : H.index = 2 := (Sym6.index_two_iff hA hAL H).2 rfl
  obtain ⟨σ', hσ'k, -, hσ'⟩ := exists_sigma_centralizer h σ hσs hσA hσk
  let P : Subgroup (egQD C) := centralizer ({zt h} : Set (egQD C))
  have hψP : ∀ n : egNL L A, psi h n ∈ P := fun n =>
    mem_centralizer_singleton_iff.2 (psi_comm h n)
  have hOodd : Odd (Nat.card (fusionOddCore (egQD C))) := odd_natCard_fusionOddCore _
  have hPodd : ¬ 2 ∣ P.index := not_two_dvd_index_of_odd_mul _ P hOodd hStepA
  have hbound : ∀ d : P, (d : egQD C) * d = 1 → (d : egQD C) ≠ 1 →
      ∀ (g : G) (hg : g ∈ normalizer (C : Set G)), qdMk C ⟨g, hg⟩ = d →
        Nat.card (fixSub C g) ≤ 256 ∧
          (σ' d ∉ alternatingGroup (Fin 6) → Nat.card (fixSub C g) ≤ 64) := by
    intro d hd2 hd1 g hg hgd
    obtain ⟨m, hdm⟩ := exists_decomp_centralizer h d.2
    have hdm' : qdMk C ⟨g, hg⟩ = psi h m ∨ qdMk C ⟨g, hg⟩ = psi h m * zt h := by
      rw [hgd]
      exact hdm
    obtain ⟨h256, h64⟩ := card_fixSub_le_of_involution h hty hH hg m hdm'
      (by rw [hgd]; exact hd2) (by rw [hgd]; exact hd1)
    refine ⟨h256, fun hodd => h64 fun hmH => hodd ?_⟩
    have hcomp : σ' d = σ m := by
      rcases hdm with h1 | h1
      · exact hσ' m 0 d (by rw [h1, pow_zero, mul_one])
      · exact hσ' m 1 d (by rw [h1, pow_one])
    rw [hcomp]
    exact hmH
  refine false_of_sylow hG h hty fun n hn2 hnA => ?_
  let p₀ : P := ⟨psi h n, hψP n⟩
  have hp₀2 : p₀ * p₀ = 1 := by
    apply Subtype.ext
    show psi h n * psi h n = 1
    rw [← map_mul, hn2, map_one]
  have hp₀1 : p₀ ≠ 1 := fun h1 => by
    have : psi h n = 1 := congrArg Subtype.val h1
    rw [← MonoidHom.mem_ker, ker_psi h] at this
    exact hnA (mem_subgroupOf.1 this)
  have hzp : IsPGroup 2 (zpowers p₀) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hp₀2) hp₀1]
    norm_num
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  let S₀ : Subgroup (egQD C) := (S : Subgroup P).map P.subtype
  have hS₀ : IsPGroup 2 S₀ := S.isPGroup'.map P.subtype
  have hS₀P : S₀ ≤ P := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hS₀odd : ¬ 2 ∣ S₀.index := by
    have h1 := Subgroup.relIndex_mul_index (H := S₀) (K := P) hS₀P
    have h2 : S₀.relIndex P = (S : Subgroup P).index := by
      show (S₀.subgroupOf P).index = _
      exact congrArg Subgroup.index
        (Subgroup.comap_map_eq_self_of_injective P.subtype_injective (S : Subgroup P))
    rw [← h1, h2]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h3 | h3
    · exact S.not_dvd_index h3
    · exact hPodd h3
  refine ⟨S₀, hS₀, hS₀odd, ⟨p₀, hS (mem_zpowers p₀), rfl⟩, ?_, ?_⟩
  ·
    intro D hDS hD2
    let D' : Subgroup P := D.subgroupOf P
    have hD'card : Nat.card D' = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDS.trans hS₀P)).toEquiv
    rw [← hD'card]
    exact (card_elemAb_le_of_ker_six σ' hσ'k D' fun a ha => Subtype.ext (hD2 _ ha)).1
  ·
    intro D hDS hD2 hDbot
    let D' : Subgroup P := D.subgroupOf P
    have hD'card : Nat.card D' = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDS.trans hS₀P)).toEquiv
    obtain ⟨hle16, hodd16⟩ :=
      card_elemAb_le_of_ker_six σ' hσ'k D' fun a ha => Subtype.ext (hD2 _ ha)
    by_cases h16 : Nat.card D' = 16
    · obtain ⟨d', hd', hnotA⟩ := hodd16 h16
      have hdD : (d' : egQD C) ∈ D := Subgroup.mem_subgroupOf.1 hd'
      have hd1 : (d' : egQD C) ≠ 1 := fun h1 => by
        apply hnotA
        have : d' = 1 := Subtype.ext h1
        rw [this, map_one]
        exact one_mem _
      refine ⟨d', hdD, hd1, 64, fun g hg hgd => ?_, ?_⟩
      · exact (hbound d' (hD2 _ hdD) hd1 g hg hgd).2 hnotA
      · rw [← hD'card, h16]
        norm_num
    · obtain ⟨⟨d, hdD⟩, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDbot
      have hd1 : d ≠ 1 := fun h1 => hd (Subtype.ext h1)
      refine ⟨d, hdD, hd1, 256, fun g hg hgd => ?_, ?_⟩
      · exact (hbound ⟨d, hS₀P (hDS hdD)⟩ (hD2 _ hdD) hd1 g hg hgd).1
      · have : Nat.card D ≤ 15 := by
          have h1 : Nat.card D ≤ 16 := hD'card ▸ hle16
          have h2 : Nat.card D ≠ 16 := fun e => h16 (by rw [hD'card]; exact e)
          omega
        calc Nat.card D * 256 ≤ 15 * 256 := Nat.mul_le_mul_right _ this
          _ < 4096 := by norm_num

end CSide

end CFSG.EvenSporadicStandard.M24Std

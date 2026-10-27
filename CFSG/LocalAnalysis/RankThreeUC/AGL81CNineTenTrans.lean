module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem starImg_map_conj (p : ℕ) (H J : Subgroup G) (y : ↥H) :
    starImg p H (J.map (MulAut.conj (y : G)).toMonoidHom) =
      (starImg p H J).map
        (MulAut.conj (QuotientGroup.mk' (primeComplementCore (G := ↥H) p) y)).toMonoidHom := by
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hsub : (J.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf H =
      (J.subgroupOf H).map (MulAut.conj y).toMonoidHom := by
    ext t
    constructor
    · intro ht
      rw [Subgroup.mem_subgroupOf] at ht
      obtain ⟨c, hcJ, hct⟩ := Subgroup.mem_map.mp ht
      have hcy : c = (y : G)⁻¹ * (t : G) * (y : G) := by
        have h2 : (MulAut.conj (y : G)) c = (t : G) := hct
        rw [← h2, MulAut.conj_apply]
        group
      refine Subgroup.mem_map.mpr ⟨⟨c, ?_⟩, ?_, ?_⟩
      · rw [hcy]
        exact H.mul_mem (H.mul_mem (H.inv_mem y.2) t.2) y.2
      · rwa [Subgroup.mem_subgroupOf]
      · exact Subtype.ext (show (MulAut.conj (y : G)) c = (t : G) from hct)
    · intro ht
      obtain ⟨a, ha, hat⟩ := Subgroup.mem_map.mp ht
      refine Subgroup.mem_map.mpr ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, ?_⟩
      simpa using congrArg Subtype.val hat
  show starImg p H (J.map (MulAut.conj (y : G)).toMonoidHom) =
    (starImg p H J).map (MulAut.conj (π y)).toMonoidHom
  unfold starImg
  rw [hsub, Subgroup.map_map]
  have hcomp : π.comp (MulAut.conj y).toMonoidHom =
      (MulAut.conj (π y)).toMonoidHom.comp π := by
    ext g
    show π ((MulAut.conj y) g) = (MulAut.conj (π y)) (π g)
    simp [MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map]

theorem card_starImg_eq (hp : p.Prime) {A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup p A) :
    Nat.card (starImg p H A) = Nat.card A := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let K : Subgroup ↥H := A.subgroupOf H
  have hKcard : ∃ n : ℕ, Nat.card K = p ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    exact ⟨n, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hn]⟩
  obtain ⟨n, hn⟩ := hKcard
  have hcop : Nat.Coprime (Nat.card K) (Nat.card O) := by
    rw [hn]
    exact (primeComplementCore_coprime (G := ↥H) p).pow_left n
  have hKinf : K ⊓ O = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hinj : Function.Injective
      ((QuotientGroup.mk' O).domRestrict K) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [← Subgroup.inf_subgroupOf_left O K, hKinf, Subgroup.bot_subgroupOf]
  have hrange : ((QuotientGroup.mk' O).domRestrict K).range = starImg p H A := by
    rw [MonoidHom.domRestrict_range]
    rfl
  calc Nat.card (starImg p H A)
      = Nat.card ((QuotientGroup.mk' O).domRestrict K).range := by rw [hrange]
    _ = Nat.card K := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    _ = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv

end CFSG.LocalAnalysis.RankThreeUC.AGL81C


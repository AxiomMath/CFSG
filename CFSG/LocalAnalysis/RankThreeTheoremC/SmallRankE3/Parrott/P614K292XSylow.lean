module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K292XTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
open P614K292

namespace P614K292X

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type}
  [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L} {y : GL (Fin 3) K} {v : Fin 3 → K}

@[expose] def FrameConj (π : Bool) (q : ℕ) (K : Type) [Field K] (y : GL (Fin 3) K)
    (v : Fin 3 → K) : Prop :=
  ∀ E : Subgroup (GL (Fin 3) K), E ≤ slPi π 3 q K → IsElemAbelian 3 E →
    Nat.card E = 9 → StatedScalars (Fin 3) K ⊓ slPi π 3 q K ≤ E →
    ∃ a ∈ slPi π 3 q K, E.map (MulAut.conj a).toMonoidHom = threeFrame y v

theorem exists_mul_mem_normalizer (M : LModel L π p f K ν) (hν : Function.Injective ν)
    [hLn : L.Normal] (hF : threeFrame y v ∈ frameCands π (p ^ f) y)
    (hconj : FrameConj π (p ^ f) K y v) (g : X) :
    ∃ l ∈ L, l * g ∈ normalizer (threeFrameIn ν y v : Set X) := by
  obtain ⟨hFSL, hFab, hF9, hFZ, -⟩ := hF
  set E := threeFrameIn ν y v
  set A := E.map (MulAut.conj g).toMonoidHom
  set φ : ↥(slPi π 3 (p ^ f) K) →* X := L.subtype.comp ν with hφ
  have hφinj : Function.Injective φ := comp_injective hν
  set E' := (A.comap φ).map (slPi π 3 (p ^ f) K).subtype
  have hAL : A ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact hLn.conj_mem k (threeFrameIn_le hk) g
  have hArange : A ≤ φ.range := fun a ha => by
    obtain ⟨s, hs⟩ := M.surj ⟨a, hAL ha⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  have h1 : E' ≤ slPi π 3 (p ^ f) K := Subgroup.map_subtype_le _
  have h2 : IsElemAbelian 3 E' :=
    (isElemAbelian_comap hφinj ((isElemAbelian_threeFrameIn hFab).map _)).map _
  have h3 : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective (slPi π 3 (p ^ f) K).subtype_injective,
      ← Subgroup.card_map_of_injective hφinj, Subgroup.map_comap_eq_self hArange,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, card_threeFrameIn hν hFSL, hF9]
  have h4 : StatedScalars (Fin 3) K ⊓ slPi π 3 (p ^ f) K ≤ E' := by
    intro z hz
    refine ⟨⟨z, hz.2⟩, ?_, rfl⟩
    have hzc : (⟨z, hz.2⟩ : ↥(slPi π 3 (p ^ f) K)) ∈ center ↥(slPi π 3 (p ^ f) K) := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq M.piField M.modThree,
        Subgroup.mem_subgroupOf]
      exact hz.1
    have hZ : φ ⟨z, hz.2⟩ ∈ (center ↥L).map L.subtype := ⟨_, M.map_mem_center hzc, rfl⟩
    have hZ' := (KFactProofs.T29.normal_map_center_subtype L).conj_mem _ hZ g⁻¹
    refine ⟨_, center_le_threeFrameIn M hFZ hZ', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨a, ha, hmap⟩ := hconj E' h1 h2 h3 h4
  set a' : ↥(slPi π 3 (p ^ f) K) := ⟨a, ha⟩
  refine ⟨((ν a' : ↥L) : X), (ν a').2, mem_normalizer_of_conj_mem fun k hk => ?_⟩
  have hk' : g * k * g⁻¹ ∈ A := ⟨k, hk, by simp only [MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]⟩
  obtain ⟨t, ht⟩ := M.surj ⟨_, hAL hk'⟩
  have htk : ((ν t : ↥L) : X) = g * k * g⁻¹ := congrArg Subtype.val ht
  have htE' : (t : GL (Fin 3) K) ∈ E' := ⟨t, by
    show φ t ∈ A
    rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, htk]
    exact hk', rfl⟩
  have hat : a * t * a⁻¹ ∈ threeFrame y v := by
    rw [← hmap]
    exact ⟨t, htE', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have heq : ((ν a' : ↥L) : X) * g * k * (((ν a' : ↥L) : X) * g)⁻¹ =
      ((ν (a' * t * a'⁻¹) : ↥L) : X) := by
    rw [coe_nu_conj, htk]
    group
  rw [heq, coe_mem_threeFrameIn_iff hν]
  exact hat

theorem not_three_dvd_index (M : LModel L π p f K ν) (hν : Function.Injective ν) [L.Normal]
    (hF : threeFrame y v ∈ frameCands π (p ^ f) y) (hconj : FrameConj π (p ^ f) K y v)
    (hind : ¬ 3 ∣ (normalizer (threeFrame y v : Set (GL (Fin 3) K))).relIndex
      (slPi π 3 (p ^ f) K)) :
    ¬ 3 ∣ (normalizer (threeFrameIn ν y v : Set X)).index := by
  set N := normalizer (threeFrameIn ν y v : Set X)
  have hsup : N ⊔ L = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨l, hl, hlg⟩ := exists_mul_mem_normalizer M hν hF hconj g
    have h := Subgroup.mul_mem_sup (inv_mem hl) hlg
    rwa [inv_mul_cancel_left, sup_comm] at h
  rw [index_eq_relIndex_of_sup_eq_top hsup]
  have hle : (normalizer (threeFrame y v : Set (GL (Fin 3) K))).subgroupOf (slPi π 3 (p ^ f) K) ≤
      (N.subgroupOf L).comap ν := by
    intro s hs
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact coe_mem_normalizer_threeFrameIn hν (Subgroup.mem_subgroupOf.1 hs)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_comap_of_surjective (N.subgroupOf L) M.surj] at hdvd
  exact fun h => hind (h.trans hdvd)

theorem exists_sylow_le_normalizer (M : LModel L π p f K ν) (hν : Function.Injective ν)
    [L.Normal] (hF : threeFrame y v ∈ frameCands π (p ^ f) y)
    (hconj : FrameConj π (p ^ f) K y v)
    (hind : ¬ 3 ∣ (normalizer (threeFrame y v : Set (GL (Fin 3) K))).relIndex
      (slPi π 3 (p ^ f) K)) :
    ∃ Q : Sylow 3 X, (Q : Subgroup X) ≤ normalizer (threeFrameIn ν y v : Set X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_sylow_le_of_not_dvd_index (not_three_dvd_index M hν hF hconj hind)

end P614K292X

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.RuStd

theorem card_centralizer_of_fixed
    (v : ruP) (hv : orderOf v = 2)
    (hfix : ∃ p, (v : Equiv.Perm (Fin 4060)) p = p) :
    Nat.card (centralizer ({v} : Set ruP)) = 245760 := by
  rcases FactsA.isConj_ruZ'_or_ruA0' hv with h | h
  · rw [← FactsA.card_centralizer_eq_of_isConj h]
    exact FactsA.card_centralizer_ruZ'
  · exfalso
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    obtain ⟨p, hp⟩ := hfix
    have h0 := conj_ruA0_ncard (g := (c : Equiv.Perm (Fin 4060)))
    have hempty : fixSet ((c : Equiv.Perm (Fin 4060)) * ruA0 * (c : Equiv.Perm (Fin 4060))⁻¹) =
        ∅ := (Set.ncard_eq_zero (Set.toFinite _)).1 h0
    have : p ∈ fixSet ((c : Equiv.Perm (Fin 4060)) * ruA0 * (c : Equiv.Perm (Fin 4060))⁻¹) := hp
    rw [hempty] at this
    exact this

theorem oddCore_of_quot {G : Type} [Group G] {r : G}
    (φ : ↥(centralizer ({r} : Set G)) →* M10) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (zpowers r).subgroupOf (centralizer ({r} : Set G))) (N : Subgroup G)
    (hN : N ≤ centralizer ({r} : Set G))
    (hnorm : ∀ x ∈ centralizer ({r} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ zpowers r := by
  have hN' : (N.subgroupOf (centralizer ({r} : Set G))).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.2
      (by simpa using hnorm g g.2 x (Subgroup.mem_subgroupOf.1 hx))⟩
  have hcard : Nat.card (N.subgroupOf (centralizer ({r} : Set G))) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hKn : ((N.subgroupOf (centralizer ({r} : Set G))).map φ).Normal := hN'.map φ hφs
  have hKodd : Odd (Nat.card ((N.subgroupOf (centralizer ({r} : Set G))).map φ)) :=
    Odd.of_dvd_nat (hcard ▸ hodd) (Subgroup.card_map_dvd _ φ)
  have hK := M10_no_odd_normal _ hKodd
  intro n hn
  have h1 : φ ⟨n, hN hn⟩ ∈ (N.subgroupOf (centralizer ({r} : Set G))).map φ :=
    ⟨⟨n, hN hn⟩, hn, rfl⟩
  rw [hK, Subgroup.mem_bot] at h1
  have h2 : (⟨n, hN hn⟩ : ↥(centralizer ({r} : Set G))) ∈ φ.ker := h1
  rw [hφk] at h2
  exact h2

section ThreeAt


theorem threeAt_ruThreeX0 : ThreeAt ruThreeX0 := by
  obtain ⟨φ, hφs, hφk⟩ := exists_ruThreeHom
  have hmem : ∀ x : ↥(centralizer ({ruThreeX0} : Set ruP)),
      ((x : ruP) : Equiv.Perm (Fin 4060)) ∈ ruThreeC0 := by
    intro x
    rw [ruThreeC0_spec.1]
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, x.1.2⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
  let ψ : ↥(centralizer ({ruThreeX0} : Set ruP)) →* ↥ruThreeC0 :=
    ((ruP.subtype).comp (centralizer ({ruThreeX0} : Set ruP)).subtype).codRestrict ruThreeC0 hmem
  have hψs : Function.Surjective ψ := by
    intro c
    have hiff : ∀ x, x ∈ ruThreeC0 ↔ x ∈ centralizer {ruThreeLine 0} ⊓ ruP := fun x => by
      rw [ruThreeC0_spec.1]
    obtain ⟨hc1, hc2⟩ := mem_inf.1 ((hiff _).1 c.2)
    exact ⟨⟨⟨c, hc2⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hc1))⟩, Subtype.ext rfl⟩
  have hker : (φ.comp ψ).ker =
      (zpowers ruThreeX0).subgroupOf (centralizer ({ruThreeX0} : Set ruP)) := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    have h1 : φ (ψ x) = 1 ↔ ψ x ∈ φ.ker := MonoidHom.mem_ker.symm
    rw [h1, hφk, Subgroup.mem_subgroupOf]
    show ((x : ruP) : Equiv.Perm (Fin 4060)) ∈ zpowers (ruThreeLine 0) ↔ (x : ruP) ∈ _
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [ruThreeX0] using hk)⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      exact mem_zpowers_iff.2 ⟨k, by simpa [ruThreeX0] using congrArg Subtype.val hk⟩
  obtain ⟨V, hVC, hV2, hVfix⟩ := ruThreeV_spec
  have hVP : V ∈ ruP := ruThreeC0_le_P hVC
  refine ⟨card_centralizer_ruThreeX0, ?_, ⟨φ.comp ψ, hφs.comp hψs, hker⟩,
    ⟨⟨V, hVP⟩, ?_, ?_, ?_⟩⟩
  · exact oddCore_of_quot (φ.comp ψ) (hφs.comp hψs) hker
  · exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_of_mem_ruThreeC0 hVC))
  · rw [← Subgroup.orderOf_coe]
    exact hV2
  · exact card_centralizer_of_fixed _ (by rw [← Subgroup.orderOf_coe]; exact hV2) hVfix

theorem ruThreeFacts_ruP : RuThreeFacts ruP :=
  ruThreeFacts_of_threeAt fun r hr => by
    obtain ⟨c, hc⟩ := exists_conj_ruThree r hr
    have h := threeAt_ruThreeX0.map (MulAut.conj c)
    rw [MulAut.conj_apply] at h
    exact ThreeAt.of_zpowers_eq hc h

end ThreeAt

theorem ruThreeFacts_of_isSporadic
    {Y : Type} [Group Y]
    (hY : IsSporadic Y .Ru) : RuThreeFacts Y := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  exact ruThreeFacts_ruP.of_mulEquiv e.symm

end CFSG.EvenSporadicStandard.RuStd.S2

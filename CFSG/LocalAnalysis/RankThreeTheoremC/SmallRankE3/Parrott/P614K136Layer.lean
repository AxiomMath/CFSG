module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open Subgroup

theorem exists_isPComponent_map_eq {X : Type*} [Group X] [Finite X] (p : ℕ)
    {K : Subgroup (X ⧸ CFSG.pPrimeCore p X)} (hK : CFSG.IsComponent K) :
    ∃ L : Subgroup X, CFSG.IsPComponent p L ∧
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) = K := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore p X)
  set S : Set (Subgroup X) := {L | L.IsSubnormal ∧ L.map π = K}
  have hS : S.Nonempty := ⟨K.comap π, hK.2.comap π,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K⟩
  obtain ⟨L, hL⟩ := (Set.toFinite S).exists_minimal hS
  refine ⟨L, ⟨K, hK, hL.1.1, hL.1.2, fun J hJL hJsub hJmap => ?_⟩, hL.1.2⟩
  exact not_le_of_gt hJL (hL.2 ⟨hJsub, hJmap⟩ hJL.le)

theorem card_dvd_card_pLayer {X : Type*} [Group X] [Finite X] (p : ℕ) [hp : Fact p.Prime]
    (Y : Subgroup X) [hY : Y.Normal] {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hSnc : ∃ a b : S, a * b ≠ b * a) (hpS : p ∣ Nat.card S) (ψ : Y →* S)
    (hψ : Function.Surjective ψ) (hker : ∀ y : Y, ψ y = 1 → (y : X) ∈ CFSG.pPrimeCore p X) :
    Nat.card S ∣ Nat.card (CFSG.pLayer X p) := by
  set N := CFSG.pPrimeCore p X with hN
  set π := QuotientGroup.mk' N with hπ
  have hkill : ∀ y : Y, (y : X) ∈ N → ψ y = 1 := by
    have hnorm : ((N.subgroupOf Y).map ψ).Normal :=
      ((inferInstance : N.Normal).subgroupOf Y).map ψ hψ
    have hcop : Nat.Coprime p (Nat.card ((N.subgroupOf Y).map ψ)) := by
      refine Nat.Coprime.coprime_dvd_right ?_ (CFSG.pPrimeCore_coprime_card (p := p) (G := X))
      refine (Subgroup.card_map_dvd _ _).trans ?_
      let ι : (N.subgroupOf Y) →* N :=
        { toFun := fun y => ⟨(y : Y), y.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Subgroup.card_dvd_of_injective ι fun a b hab => ?_
      have h := congrArg (fun z : N => (z : X)) hab
      exact Subtype.ext (Subtype.ext h)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf Y).map ψ) with h | h
    · intro y hy
      have hmem : ψ y ∈ (N.subgroupOf Y).map ψ := Subgroup.mem_map_of_mem ψ hy
      rwa [h, Subgroup.mem_bot] at hmem
    · exfalso
      rw [h, Subgroup.card_top] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop hpS
  set K' : Subgroup (X ⧸ N) := Y.map π with hK'
  let α : Y →* K' := (π.comp Y.subtype).codRestrict K' fun y => Subgroup.mem_map_of_mem π y.2
  have hα : Function.Surjective α := by
    rintro ⟨k, hk⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker_eq : α.ker = ψ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : α y = 1 ↔ (y : X) ∈ N := by
      rw [← Subtype.coe_inj]
      change π (y : X) = 1 ↔ _
      exact QuotientGroup.eq_one_iff _
    rw [h1]
    exact ⟨hkill y, hker y⟩
  let e : K' ≃* S := (QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))
  haveI : IsSimpleGroup K' := e.isSimpleGroup
  have hK'nc : ∃ a b : K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnc
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hK'comp : CFSG.IsComponent K' :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hK'nc).1,
      (hY.map π (QuotientGroup.mk'_surjective N)).isSubnormal⟩
  obtain ⟨L, hL, hLK⟩ := exists_isPComponent_map_eq p hK'comp
  have hLle : L ≤ CFSG.pLayer X p := le_sSup hL
  calc Nat.card S = Nat.card K' := (Nat.card_congr e.toEquiv).symm
    _ ∣ Nat.card L := by rw [← hLK]; exact Subgroup.card_map_dvd L π
    _ ∣ Nat.card (CFSG.pLayer X p) := Subgroup.card_dvd_of_le hLle

theorem eq_of_inf_normalizer_le {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {R S : Subgroup G}
    [Finite S] (hRS : R ≤ S) (hS : IsPGroup p S) (h : S ⊓ normalizer (R : Set G) ≤ R) :
    R = S := by
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := normalizerCondition_of_isNilpotent
  by_contra hne
  have hlt : R.subgroupOf S < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne ?_
    exact le_antisymm hRS fun s hs => by
      have : (⟨s, hs⟩ : S) ∈ R.subgroupOf S := htop ▸ Subgroup.mem_top _
      exact this
  have hgrow := hnc _ hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hRS] at hgrow
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt hgrow
  exact hxR (h ⟨x.2, hxN⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

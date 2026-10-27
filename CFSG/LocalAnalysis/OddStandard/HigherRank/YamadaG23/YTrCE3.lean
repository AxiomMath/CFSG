module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem centExt_split_of_sylow_split {G : Type} [Group G] [Finite G]
    {N Z P K₀ : Subgroup G} (hZN : Z ≤ N) (hZc : ∀ z ∈ Z, ∀ g ∈ N, z * g = g * z)
    (hZ3 : IsPGroup 3 ↥Z) (hPN : P ≤ N) (hP : IsPGroup 3 ↥P) (hPi : ¬ 3 ∣ P.relIndex N)
    (hZP : Z ≤ P) (hK₀P : K₀ ≤ P) (hZK : Z ⊓ K₀ = ⊥) (hZK₀ : Z ⊔ K₀ = P) :
    ∃ K : Subgroup G, K ≤ N ∧ Z ⊓ K = ⊥ ∧ Z ⊔ K = N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₀N : K₀ ≤ N := hK₀P.trans hPN
  haveI hVnorm : (Z.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hZN).mpr fun z n hz hn => by
      have h : n * z * n⁻¹ = z := by rw [← hZc z hz n hn]; group
      rwa [h]
  haveI hVcomm : IsMulCommutative ↥(Z.subgroupOf N) :=
    IsMulCommutative.of_comm fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      exact hZc a.1.1 a.2 b.1.1 (hZN b.2)
  have hVp : IsPGroup 3 ↥(Z.subgroupOf N) :=
    hZ3.of_equiv (Subgroup.subgroupOfEquivOfLe hZN).symm
  have hPp : IsPGroup 3 ↥(P.subgroupOf N) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hPi' : ¬ 3 ∣ (P.subgroupOf N).index := by
    simpa only [Subgroup.relIndex] using hPi
  have hK₀sub : K₀.subgroupOf N ≤ hPp.toSylow hPi' := by
    rw [IsPGroup.toSylow_coe hPp hPi']
    exact Subgroup.subgroupOf_mono N hK₀P
  have hVK₀ : Z.subgroupOf N ⊓ K₀.subgroupOf N = ⊥ := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    rw [Subgroup.map_inf (Z.subgroupOf N) (K₀.subgroupOf N) N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hZN, Subgroup.map_subgroupOf_eq_of_le hK₀N,
      Subgroup.map_bot, hZK]
  have hVK₀sup : Z.subgroupOf N ⊔ K₀.subgroupOf N = hPp.toSylow hPi' := by
    rw [IsPGroup.toSylow_coe hPp hPi', ← Subgroup.subgroupOf_sup hZN hK₀N, hZK₀]
  obtain ⟨K', hVK', hVtop'⟩ :=
    (CFSG.Quasithin.gaschutz (G := ↥N) (p := 3) (V := Z.subgroupOf N) hVp
        (hPp.toSylow hPi')).mpr
      ⟨K₀.subgroupOf N, hK₀sub, hVK₀, hVK₀sup⟩
  refine ⟨K'.map N.subtype, Subgroup.map_subtype_le K', ?_, ?_⟩
  · have hZmap : (Z.subgroupOf N).map N.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZN
    have h1 : Z ⊓ K'.map N.subtype = ((Z.subgroupOf N) ⊓ K').map N.subtype := by
      rw [Subgroup.map_inf (Z.subgroupOf N) K' N.subtype N.subtype_injective, hZmap]
    rw [h1, hVK', Subgroup.map_bot]
  · have hZmap : (Z.subgroupOf N).map N.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZN
    have htop : (⊤ : Subgroup ↥N).map N.subtype = N :=
      (MonoidHom.range_eq_map N.subtype).symm.trans (Subgroup.range_subtype N)
    have h1 : Z ⊔ K'.map N.subtype = ((Z.subgroupOf N) ⊔ K').map N.subtype := by
      rw [Subgroup.map_sup (Z.subgroupOf N) K' N.subtype, hZmap]
    rw [h1, hVtop', htop]

end CFSG.OddStandard.HigherRank.YamadaG23

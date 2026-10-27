module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.GroupTheory.ABGLocalTools.RelativeStability

public section

open Subgroup

namespace CFSG.ABGLocalTools

variable {G M : Type*} [Group G] [Group M]

theorem eq_one_of_pow_two_pow_eq_one_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {g : G}
    (hgN : g ∈ N) {k : ℕ} (hg : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg
  have h2 : orderOf g ∣ Nat.card N := by
    have h := orderOf_dvd_natCard (⟨g, hgN⟩ : N)
    rw [← orderOf_coe] at h
    exact h
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem twoSubgroupsCyclic_bot : TwoSubgroupsCyclic (⊥ : Subgroup M) := by
  intro T hT _
  rw [le_bot_iff] at hT
  subst hT
  infer_instance

theorem TwoSubgroupsCyclic.map_of_injective {B : Subgroup G} (hB : TwoSubgroupsCyclic B)
    (f : G →* M) (hf : Function.Injective f) : TwoSubgroupsCyclic (B.map f) := by
  intro T hTB hT
  have hT' : T.comap f ≤ B := by
    intro g hg
    obtain ⟨b, hb, hbg⟩ := hTB hg
    rw [← hf hbg]
    exact hb
  have hTr : T ≤ f.range := hTB.trans (map_le_range f B)
  have hc : IsCyclic (T.comap f) := hB _ hT' (hT.comap_of_injective f hf)
  have e := MulEquiv.subgroupCongr (map_comap_eq_self hTr)
  exact isCyclic_of_surjective (e.toMonoidHom.comp (f.subgroupMap (T.comap f)))
    (e.surjective.comp (f.subgroupMap_surjective _))

theorem pCore_map_eq_bot_of_injective {p : ℕ} {B : Subgroup G} (hB : pCore p B = ⊥)
    (f : G →* M) (hf : Function.Injective f) : pCore p (B.map f) = ⊥ := by
  rw [← pCore_map_iso p (B.equivMapOfInjective f hf), hB, Subgroup.map_bot]

variable [Finite G] {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V]

theorem mem_pCore_comap_of_twoSubgroupsCyclic (hp : p ≠ 2) (π : G →* M)
    (hker : Odd (Nat.card π.ker)) (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) {x : G} (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    {B : Subgroup M} (hB : TwoSubgroupsCyclic B) (hxB : π x ∈ B) :
    (⟨x, hxB⟩ : B.comap π) ∈ pCore p (B.comap π) := by
  have hsec : TwoSectionsCyclic (B.comap π) := twoSectionsCyclic_of_isCyclic fun D hD => by
    set f : D →* M := (π.comp (B.comap π).subtype).comp D.subtype with hfdef
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro d hd
      obtain ⟨k, hk⟩ := hD d
      have hk' : ((d : B.comap π) : G) ^ 2 ^ k = 1 := by
        have := congrArg (fun y : D => ((y : B.comap π) : G)) hk
        simpa using this
      have h1 := eq_one_of_pow_two_pow_eq_one_of_odd hker (g := ((d : B.comap π) : G)) hd hk'
      rw [mem_bot]
      exact Subtype.ext (Subtype.ext h1)
    have hrange : f.range ≤ B := by
      rintro _ ⟨d, rfl⟩
      exact (d : B.comap π).2
    have : IsCyclic f.range :=
      hB _ hrange (hD.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    exact isCyclic_of_injective f.rangeRestrict
      (MonoidHom.rangeRestrict_injective_iff.mpr hf)
  exact mem_pCore_of_twoSectionsCyclic hsec hp (ρ.comp (B.comap π).subtype)
    (hρ.comp (subtype_injective _)) ⟨x, hxB⟩ hx

theorem mem_pCore_of_twoSubgroupsCyclic (hp : p ≠ 2) (π : G →* M)
    (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker))
    (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V) (hρ : Function.Injective ρ) {x : G}
    (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) {B : Subgroup M} (hB : TwoSubgroupsCyclic B)
    (hxB : π x ∈ B) : (⟨π x, hxB⟩ : B) ∈ pCore p B := by
  have hmem := mem_pCore_comap_of_twoSubgroupsCyclic hp π hker ρ hρ hx hB hxB
  exact map_pCore_le_of_surjective (π.subgroupComap B)
    (π.subgroupComap_surjective B hπ) ⟨_, hmem, rfl⟩

theorem mem_pCore_of_map_eq_one (hp : p ≠ 2) (π : G →* M) (hker : Odd (Nat.card π.ker))
    (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V) (hρ : Function.Injective ρ) {x : G}
    (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) (hx1 : π x = 1) : x ∈ pCore p G := by
  have hxB : π x ∈ (⊥ : Subgroup M) := by rw [hx1]; exact one_mem _
  have hmem := mem_pCore_comap_of_twoSubgroupsCyclic hp π hker ρ hρ hx twoSubgroupsCyclic_bot
    hxB
  have hn : ((⊥ : Subgroup M).comap π).subtype.range.Normal := by
    rw [range_subtype]
    infer_instance
  exact map_pCore_le_of_injective_of_normal _ (subtype_injective _) hn ⟨_, hmem, rfl⟩

end CFSG.ABGLocalTools

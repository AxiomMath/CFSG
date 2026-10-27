module

public import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.GroupTheory.ConjClassCover

public section

namespace CFSG.GroupTheory

open Subgroup

theorem exists_mem_normalizer_not_mem_centralizer_of_isConj {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {z j : G} (hzj : IsConj z j) {T : Subgroup G}
    (hTK : T ≤ centralizer ({z} : Set G) ⊓ centralizer ({j} : Set G)) (hT : IsPGroup p T)
    (hTmax : ∀ T' : Subgroup G, T' ≤ centralizer ({z} : Set G) ⊓ centralizer ({j} : Set G) →
      IsPGroup p T' → T ≤ T' → T' = T)
    {P : Subgroup G} (hP : IsPGroup p P) (hPz : P ≤ centralizer ({z} : Set G))
    (hcard : Nat.card T < Nat.card P) :
    ∃ y ∈ centralizer ({j} : Set G), y ∈ Subgroup.normalizer (T : Set G) ∧
      y * z * y⁻¹ ≠ z := by
  classical
  let Cz : Subgroup G := centralizer ({z} : Set G)
  let Cj : Subgroup G := centralizer ({j} : Set G)
  have hCzCj : Nat.card Cz = Nat.card Cj := card_centralizer_eq_of_isConj hzj
  have hTCz : T ≤ Cz := hTK.trans inf_le_left
  have hTCj : T ≤ Cj := hTK.trans inf_le_right
  obtain ⟨S, hTS⟩ := (hT.comap_subtype (K := Cj)).exists_le_sylow
  let P₂ : Subgroup G := (S : Subgroup Cj).map Cj.subtype
  have hP₂le : P₂ ≤ Cj := Subgroup.map_subtype_le _
  have hTP₂ : T ≤ P₂ := by
    intro t ht
    have ht' : (⟨t, hTCj ht⟩ : Cj) ∈ T.subgroupOf Cj :=
      Subgroup.mem_subgroupOf.mpr ht
    exact Subgroup.mem_map_of_mem Cj.subtype (hTS ht')
  have hP₂P : IsPGroup p P₂ := S.isPGroup'.map Cj.subtype
  have hcardP₂ : Nat.card P₂ = p ^ (Nat.card Cj).factorization p := by
    rw [show Nat.card P₂ = Nat.card (S : Subgroup Cj) from
      Subgroup.card_map_of_injective Cj.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  obtain ⟨S', hPS'⟩ := (hP.comap_subtype (K := Cz)).exists_le_sylow
  let P₁ : Subgroup G := (S' : Subgroup Cz).map Cz.subtype
  have hcardP₁ : Nat.card P₁ = p ^ (Nat.card Cz).factorization p := by
    rw [show Nat.card P₁ = Nat.card (S' : Subgroup Cz) from
      Subgroup.card_map_of_injective Cz.subtype_injective]
    exact Sylow.card_eq_multiplicity S'
  have hPP₁ : P ≤ P₁ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPz]
    exact Subgroup.map_mono hPS'
  have hcardPP₁ : Nat.card P ≤ Nat.card P₁ := Subgroup.card_le_of_le hPP₁
  have hcardTP₂ : Nat.card T < Nat.card P₂ := by
    calc Nat.card T < Nat.card P := hcard
      _ ≤ Nat.card P₁ := hcardPP₁
      _ = p ^ (Nat.card Cz).factorization p := hcardP₁
      _ = p ^ (Nat.card Cj).factorization p := by rw [hCzCj]
      _ = Nat.card P₂ := hcardP₂.symm
  have hltTP₂ : T < P₂ := by
    refine lt_of_le_of_ne hTP₂ ?_
    intro heq
    rw [heq] at hcardTP₂
    exact lt_irrefl _ hcardTP₂
  obtain ⟨y, hy, hyT⟩ := SetLike.exists_of_lt (lt_inf_normalizer_of_isPGroup hP₂P hltTP₂)
  have hyP₂ : y ∈ P₂ := hy.1
  have hyNorm : y ∈ Subgroup.normalizer (T : Set G) := hy.2
  have hyCj : y ∈ Cj := hP₂le hyP₂
  refine ⟨y, hyCj, hyNorm, ?_⟩
  intro hyz
  have hyCz : y ∈ Cz := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hyz]
  have hZyP : IsPGroup p (Subgroup.zpowers y) :=
    hP₂P.to_le (Subgroup.zpowers_le.mpr hyP₂)
  have hZyNorm : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hyNorm
  have hsupP : IsPGroup p (T ⊔ Subgroup.zpowers y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hT hZyP hZyNorm
  have hsupLe : (T ⊔ Subgroup.zpowers y : Subgroup G) ≤ Cz ⊓ Cj :=
    sup_le (le_inf hTCz hTCj) (Subgroup.zpowers_le.mpr ⟨hyCz, hyCj⟩)
  have heq : (T ⊔ Subgroup.zpowers y : Subgroup G) = T :=
    hTmax _ hsupLe hsupP le_sup_left
  exact hyT (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))

end CFSG.GroupTheory

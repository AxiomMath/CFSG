module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29TwoNilp
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Main

namespace L29Pair

section Conj

variable {H : Type} [Group H]

theorem isComponent_map_conj {K : Subgroup H} (hK : IsComponent K) (e : H) :
    IsComponent (K.map (MulAut.conj e : H →* H)) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj e) hK

theorem mem_normalizer_of_mem_normalizer {A B : Subgroup H} (hne : A ≠ B) (hB : IsComponent B)
    (hAB : ∀ K : Subgroup H, IsComponent K → K = A ∨ K = B) {e : H}
    (he : e ∈ normalizer (A : Set H)) : e ∈ normalizer (B : Set H) := by
  rw [mem_normalizer_iff_map_conj_eq] at he ⊢
  rcases hAB _ (isComponent_map_conj hB e) with h | h
  · exact absurd (Subgroup.map_injective (MulAut.conj e).injective (h.trans he.symm)) hne.symm
  · exact h

theorem map_conj_eq_of_not_mem_normalizer {A B : Subgroup H} (hA : IsComponent A)
    (hAB : ∀ K : Subgroup H, IsComponent K → K = A ∨ K = B) {e : H}
    (he : e ∉ normalizer (A : Set H)) : A.map (MulAut.conj e : H →* H) = B := by
  rcases hAB _ (isComponent_map_conj hA e) with h | h
  · exact absurd (mem_normalizer_iff_map_conj_eq.mpr h) he
  · exact h

theorem map_conj_mul (A : Subgroup H) (a b : H) :
    A.map (MulAut.conj (b * a) : H →* H) =
      (A.map (MulAut.conj a : H →* H)).map (MulAut.conj b : H →* H) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem mul_mem_normalizer_of_not_mem {A B : Subgroup H} (hne : A ≠ B) (hA : IsComponent A)
    (hB : IsComponent B) (hAB : ∀ K : Subgroup H, IsComponent K → K = A ∨ K = B) {a b : H}
    (ha : a ∉ normalizer (A : Set H)) (hb : b ∉ normalizer (A : Set H)) :
    b * a ∈ normalizer (A : Set H) := by
  have hAB' : ∀ K : Subgroup H, IsComponent K → K = B ∨ K = A := fun K hK => (hAB K hK).symm
  have hb' : b ∉ normalizer (B : Set H) := fun h =>
    hb (mem_normalizer_of_mem_normalizer hne.symm hA hAB' h)
  have h1 := map_conj_eq_of_not_mem_normalizer hA hAB ha
  have h2 := map_conj_eq_of_not_mem_normalizer hB hAB' hb'
  rw [mem_normalizer_iff_map_conj_eq, map_conj_mul, h1, h2]

theorem index_dvd_two_of_components {A B : Subgroup H} (hne : A ≠ B) (hA : IsComponent A)
    (hB : IsComponent B) (hAB : ∀ K : Subgroup H, IsComponent K → K = A ∨ K = B)
    (E : Subgroup H) :
    ((E ⊓ normalizer (A : Set H) ⊓ normalizer (B : Set H)).subgroupOf E).index ∣ 2 := by
  rw [Subgroup.index_dvd_two_iff]
  by_cases hall : ∀ e ∈ E, e ∈ normalizer (A : Set H)
  · refine ⟨1, fun b => Or.inr ?_⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨b.2, hall b b.2⟩, mem_normalizer_of_mem_normalizer hne hB hAB (hall b b.2)⟩
  · push Not at hall
    obtain ⟨e, he, hen⟩ := hall
    refine ⟨⟨e, he⟩, fun b => ?_⟩
    by_cases hb : (b : H) ∈ normalizer (A : Set H)
    · refine Or.inr ?_
      rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨b.2, hb⟩, mem_normalizer_of_mem_normalizer hne hB hAB hb⟩
    · refine Or.inl ?_
      rw [Subgroup.mem_subgroupOf]
      have hba := mul_mem_normalizer_of_not_mem hne hA hB hAB hen hb
      exact ⟨⟨(b * ⟨e, he⟩ : ↥E).2, hba⟩, mem_normalizer_of_mem_normalizer hne hB hAB hba⟩

end Conj

section Two

variable {H : Type} [Group H] [Finite H]

theorem eq_of_mem_of_card_le_two {Z : Subgroup H} (h : Nat.card Z ≤ 2) {a b : H} (ha : a ∈ Z)
    (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have : Fintype Z := Fintype.ofFinite Z
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, ⟨a, ha⟩, ⟨b, hb⟩, fun h => ha1 (congrArg Subtype.val h).symm,
      fun h => hb1 (congrArg Subtype.val h).symm, fun h => hab (congrArg Subtype.val h), rfl⟩
  have h4 := Finset.card_le_univ ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem commute_of_mem_of_card_le_two {Z : Subgroup H} (h : Nat.card Z ≤ 2) {k d : H} (hk : k ∈ Z)
    (hdk : d * k * d⁻¹ ∈ Z) : d * k = k * d := by
  by_cases hk1 : k = 1
  · rw [hk1, mul_one, one_mul]
  · have hdk1 : d * k * d⁻¹ ≠ 1 := fun h => hk1 (by simpa using h)
    have h1 := eq_of_mem_of_card_le_two h hdk hk hdk1 hk1
    calc d * k = (d * k * d⁻¹) * d := by group
      _ = k * d := by rw [h1]

end Two

section Main

variable {H : Type} [Group H] [Finite H]

theorem twoNilp_inf_normalizers (L₁ L₂ : Subgroup H) (hZ₀ : Nat.card ↥(L₁ ⊓ L₂) ≤ 2)
    (hZ : ∀ c : H, (∀ a ∈ L₁, c * a = a * c) → (∀ b ∈ L₂, c * b = b * c) → c ∈ L₁ ⊓ L₂)
    (u : H) (hu₁ : u ∈ normalizer (L₁ : Set H)) (hu₂ : u ∈ normalizer (L₂ : Set H))
    (h₁ : TwoNilp ↥(centralizer ({actOnK L₁ u hu₁} : Set (MulAut ↥L₁))))
    (h₂ : TwoNilp ↥(centralizer ({actOnK L₂ u hu₂} : Set (MulAut ↥L₂)))) :
    TwoNilp ↥(centralizer ({u} : Set H) ⊓ normalizer (L₁ : Set H) ⊓ normalizer (L₂ : Set H)) := by
  set D' : Subgroup H :=
    centralizer ({u} : Set H) ⊓ normalizer (L₁ : Set H) ⊓ normalizer (L₂ : Set H)
  have hD'₁ : D' ≤ normalizer (L₁ : Set H) := fun d hd => hd.1.2
  have hD'₂ : D' ≤ normalizer (L₂ : Set H) := fun d hd => hd.2
  have huD' : u ∈ D' := ⟨⟨mem_centralizer_singleton_iff.mpr rfl, hu₁⟩, hu₂⟩
  have hcomm : ∀ d : ↥D', (⟨u, huD'⟩ : ↥D') * d = d * ⟨u, huD'⟩ := fun d =>
    Subtype.ext (mem_centralizer_singleton_iff.mp d.2.1.1).symm
  have hA₁ : ∀ d : ↥D', actOnKHom L₁ D' hD'₁ d ∈
      centralizer ({actOnK L₁ u hu₁} : Set (MulAut ↥L₁)) := by
    intro d
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have e : actOnK L₁ u hu₁ = actOnKHom L₁ D' hD'₁ ⟨u, huD'⟩ := rfl
    rw [e, ← map_mul, ← map_mul, hcomm d]
  have hA₂ : ∀ d : ↥D', actOnKHom L₂ D' hD'₂ d ∈
      centralizer ({actOnK L₂ u hu₂} : Set (MulAut ↥L₂)) := by
    intro d
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have e : actOnK L₂ u hu₂ = actOnKHom L₂ D' hD'₂ ⟨u, huD'⟩ := rfl
    rw [e, ← map_mul, ← map_mul, hcomm d]
  set K : Subgroup ↥D' := (actOnKHom L₁ D' hD'₁).ker ⊓ (actOnKHom L₂ D' hD'₂).ker
  have hker : ∀ d : ↥D', d ∈ K → (d : H) ∈ L₁ ⊓ L₂ := by
    intro d hd
    have h1 : d ∈ (actOnKHom L₁ D' hD'₁).ker := hd.1
    have h2 : d ∈ (actOnKHom L₂ D' hD'₂).ker := hd.2
    rw [actOnKHom_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff] at h1 h2
    exact hZ d (fun a ha => (h1 a ha).symm) (fun b hb => (h2 b hb).symm)
  have hcard : Nat.card ↥K ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : ↥K => (⟨((k : ↥D') : H), hker k.1 k.2⟩ : ↥(L₁ ⊓ L₂))) ?_) hZ₀
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hpg : IsPGroup 2 ↥K := by
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    rcases (by omega : Nat.card ↥K = 1 ∨ Nat.card ↥K = 2) with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  have hkc : K ≤ Subgroup.center ↥D' := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro d
    have hk' := hker k hk
    have hn₁ : (d : H) ∈ normalizer (L₁ : Set H) := d.2.1.2
    have hn₂ : (d : H) ∈ normalizer (L₂ : Set H) := d.2.2
    refine Subtype.ext ?_
    exact commute_of_mem_of_card_le_two hZ₀ hk'
      ⟨(mem_normalizer_iff.mp hn₁ _).mp hk'.1, (mem_normalizer_iff.mp hn₂ _).mp hk'.2⟩
  exact twoNilp_of_two_actions (actOnKHom L₁ D' hD'₁) (actOnKHom L₂ D' hD'₂) _ _ hA₁ hA₂ h₁ h₂
    hpg hkc

end Main

end L29Pair

theorem twoNilp_centralizer_of_components {H : Type} [Group H] [Finite H] (L₁ L₂ : Subgroup H)
    (hne : L₁ ≠ L₂) (hcomps : {K : Subgroup H | IsComponent K} = {L₁, L₂})
    (hZ₀ : Nat.card ↥(L₁ ⊓ L₂) ≤ 2)
    (hZ : ∀ c : H, (∀ a ∈ L₁, c * a = a * c) → (∀ b ∈ L₂, c * b = b * c) → c ∈ L₁ ⊓ L₂)
    (u : H) (hu₁ : u ∈ normalizer (L₁ : Set H)) (hu₂ : u ∈ normalizer (L₂ : Set H))
    (h₁ : TwoNilp ↥(centralizer ({actOnK L₁ u hu₁} : Set (MulAut ↥L₁))))
    (h₂ : TwoNilp ↥(centralizer ({actOnK L₂ u hu₂} : Set (MulAut ↥L₂)))) :
    TwoNilp ↥(centralizer ({u} : Set H)) := by
  have hc1 : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup H | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert _ _
    exact this
  have hc2 : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup H | IsComponent K} := by
      rw [hcomps]
      exact Set.mem_insert_of_mem _ rfl
    exact this
  have hall : ∀ K : Subgroup H, IsComponent K → K = L₁ ∨ K = L₂ := fun K hK => by
    have : K ∈ ({L₁, L₂} : Set (Subgroup H)) := by
      rw [← hcomps]
      exact hK
    simpa using this
  have hD' := L29Pair.twoNilp_inf_normalizers L₁ L₂ hZ₀ hZ u hu₁ hu₂ h₁ h₂
  have hle : centralizer ({u} : Set H) ⊓ normalizer (L₁ : Set H) ⊓ normalizer (L₂ : Set H) ≤
      centralizer ({u} : Set H) := inf_le_left.trans inf_le_left
  have hidx := L29Pair.index_dvd_two_of_components hne hc1 hc2 hall (centralizer ({u} : Set H))
  have hTN : TwoNilp ↥((centralizer ({u} : Set H) ⊓ normalizer (L₁ : Set H) ⊓
      normalizer (L₂ : Set H)).subgroupOf (centralizer ({u} : Set H))) :=
    twoNilp_of_injective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).injective hD'
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
  · have := normal_of_index_eq_one h
    exact twoNilp_of_normal_two_index _ hTN ⟨0, by simpa using h⟩
  · have := normal_of_index_eq_two h
    exact twoNilp_of_normal_two_index _ hTN ⟨1, by simpa using h⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

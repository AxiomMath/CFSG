module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.GroupTheory

open Subgroup

universe u

theorem isSubnormal_finset_iSup_of_pair {K : Type*} [Group K]
    (hpair : ∀ A B : Subgroup K, A.IsSubnormal → B.IsSubnormal → (A ⊔ B).IsSubnormal)
    {ι : Type*} (s : Finset ι) (f : ι → Subgroup K) (hf : ∀ i ∈ s, (f i).IsSubnormal) :
    (⨆ i ∈ s, f i).IsSubnormal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert]
    exact hpair _ _ (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isSubnormal_iSup_of_pair {K : Type*} [Group K]
    (hpair : ∀ A B : Subgroup K, A.IsSubnormal → B.IsSubnormal → (A ⊔ B).IsSubnormal)
    {ι : Type*} [Finite ι] (f : ι → Subgroup K) (hf : ∀ i, (f i).IsSubnormal) :
    (⨆ i, f i).IsSubnormal := by
  have := Fintype.ofFinite ι
  simpa using isSubnormal_finset_iSup_of_pair hpair Finset.univ f fun i _ => hf i

theorem isSubnormal_map_subtype {G : Type*} [Group G] {K : Subgroup G} {H : Subgroup K}
    (hH : H.IsSubnormal) (hK : K.IsSubnormal) : (H.map K.subtype).IsSubnormal :=
  hH.trans' hK

theorem isSubnormal_sup_of_card (n : ℕ) : ∀ {G : Type u} [Group G] [Finite G],
    Nat.card G = n → ∀ A B : Subgroup G, A.IsSubnormal → B.IsSubnormal →
      (A ⊔ B).IsSubnormal := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn A₀ B hA₀ hB
  have hsub : ∀ K : Subgroup G, K ≠ ⊤ → ∀ A' B' : Subgroup K, A'.IsSubnormal →
      B'.IsSubnormal → (A' ⊔ B').IsSubnormal := by
    intro K hK A' B'
    refine ih (Nat.card K) ?_ rfl A' B'
    rw [← hn, ← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt hK.lt_top
  suffices key : ∀ k, ∀ A : Subgroup G, Nat.card G - Nat.card A = k → A.IsSubnormal →
      (A ⊔ B).IsSubnormal from key _ A₀ rfl hA₀
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro A hk hA
  have hgood : ∀ X : Subgroup G, A < X → X.IsSubnormal → (X ⊔ B).IsSubnormal := by
    intro X hAX hX
    refine ihk (Nat.card G - Nat.card X) ?_ X rfl hX
    have h1 := Subgroup.card_lt_of_lt hAX
    have h2 : Nat.card X ≤ Nat.card G := Subgroup.card_le_card_group X
    omega
  by_contra hAB
  have hAnormal : ¬ A.Normal := by
    intro hN
    apply hAB
    have h1 := (hB.map (QuotientGroup.mk'_surjective A)).comap (QuotientGroup.mk' A)
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at h1
  obtain hAtop | ⟨X, hAX, hX, hAXn⟩ := Subgroup.IsSubnormal.iff_eq_top_or_exists.mp hA
  · apply hAnormal
    rw [hAtop]
    exact Subgroup.normal_top
  have hXnorm : X ≤ Subgroup.normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAX.le).mp hAXn
  have hXtop : X ≠ ⊤ := by
    rintro rfl
    exact hAnormal (normalizer_eq_top_iff.mp (top_le_iff.mp hXnorm))
  obtain ⟨G₁, hG₁n, hXG₁, hG₁top⟩ := hX.exists_normal_and_le_and_lt_top_of_ne hXtop
  let conjA : B → Subgroup G := fun b => A.map (MulAut.conj (b : G)).toMonoidHom
  have hconj_mem : ∀ (b : B) (a : G), a ∈ A → (b : G) * a * (b : G)⁻¹ ∈ conjA b :=
    fun b a ha => ⟨a, ha, rfl⟩
  have hconj_le : ∀ b : B, conjA b ≤ G₁ := by
    rintro b _ ⟨a, ha, rfl⟩
    exact hG₁n.conj_mem a (hXG₁ (hAX.le ha)) b
  have hconj_sn : ∀ b : B, ((conjA b).subgroupOf G₁).IsSubnormal := fun b =>
    (hA.map (f := (MulAut.conj (b : G)).toMonoidHom) (MulAut.conj (b : G)).surjective).subgroupOf
  let L : Subgroup G := ⨆ b, conjA b
  have hLmap : (⨆ b, (conjA b).subgroupOf G₁).map G₁.subtype = L := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun b => Subgroup.map_subgroupOf_eq_of_le (hconj_le b)
  have hLsn : L.IsSubnormal := by
    rw [← hLmap]
    exact isSubnormal_map_subtype
      (isSubnormal_iSup_of_pair (hsub G₁ hG₁top.ne) _ hconj_sn) hG₁n.isSubnormal
  have hAL : A ≤ L := fun a ha =>
    Subgroup.mem_iSup_of_mem (1 : B) (by simpa using hconj_mem 1 a ha)
  have hLAB : L ≤ A ⊔ B := iSup_le fun b => by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem (mem_sup_right b.2) (mem_sup_left ha)) (inv_mem (mem_sup_right b.2))
  have hLA : L = A := by
    rcases hAL.lt_or_eq with hlt | heq
    · exact absurd (by
        have h := hgood L hlt hLsn
        rwa [le_antisymm (sup_le hLAB le_sup_right) (sup_le_sup_right hAL B)] at h) hAB
    · exact heq.symm
  have hconjA : ∀ b : B, conjA b ≤ A := fun b => (le_iSup conjA b).trans hLA.le
  have hBnorm : B ≤ Subgroup.normalizer (A : Set G) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconjA ⟨b, hb⟩ (hconj_mem ⟨b, hb⟩ h hh)
    · intro hh
      have h1 := hconjA ⟨b⁻¹, inv_mem hb⟩ (hconj_mem ⟨b⁻¹, inv_mem hb⟩ _ hh)
      simpa [mul_assoc] using h1
  have hG₂ := hgood X hAX hX
  by_cases hG₂top : X ⊔ B = ⊤
  · apply hAnormal
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hG₂top]
    exact sup_le hXnorm hBnorm
  · apply hAB
    have hAle : A ≤ X ⊔ B := hAX.le.trans le_sup_left
    have hBle : B ≤ X ⊔ B := le_sup_right
    have h := isSubnormal_map_subtype (hsub (X ⊔ B) hG₂top _ _ hA.subgroupOf hB.subgroupOf)
      hG₂
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAle,
      Subgroup.map_subgroupOf_eq_of_le hBle] at h

theorem isSubnormal_sup {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (hA : A.IsSubnormal) (hB : B.IsSubnormal) : (A ⊔ B).IsSubnormal :=
  isSubnormal_sup_of_card (Nat.card G) rfl A B hA hB

theorem subnormal_subgroups_generated_join {G : Type u} [Group G] [Finite G]
    (𝒮 : Set (Subgroup G)) (h𝒮 : ∀ A ∈ 𝒮, A.IsSubnormal) :
    (Subgroup.closure (⋃ A ∈ 𝒮, (A : Set G))).IsSubnormal ∧
      Subgroup.closure (⋃ A ∈ (∅ : Set (Subgroup G)), (A : Set G)) = ⊥ := by
  refine ⟨?_, by simp⟩
  rw [Set.biUnion_eq_iUnion, ← Subgroup.iSup_eq_closure]
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Finite 𝒮 := Set.toFinite 𝒮
  exact isSubnormal_iSup_of_pair (fun A B => isSubnormal_sup) _ fun A => h𝒮 A A.2

end CFSG.GroupTheory

module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.Diagonal
public import CFSG.GroupTheory.PermSylowTwo.Alt

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)

private theorem isSylowTwoOf_of_maximal {G : Type*} [Group G] [Finite G] {A T : Subgroup G}
    (hT : IsPGroup 2 T) (hTA : T ≤ A)
    (hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ A → T ≤ Q → Q = T) : IsSylowTwoOf T A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hTA, hT, ?_⟩
  have hT' : IsPGroup 2 (T.subgroupOf A) := hT.comap_subtype
  obtain ⟨P, hP⟩ := hT'.exists_le_sylow
  have hQ : (P : Subgroup A).map A.subtype = T := by
    refine hmax _ (P.isPGroup'.map _) (map_subtype_le _) fun g hg => ?_
    exact ⟨⟨g, hTA hg⟩, hP (mem_subgroupOf.mpr hg), rfl⟩
  have hPT : T.subgroupOf A = P := by
    rw [← hQ]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  rw [hPT]
  exact P.not_dvd_index

private theorem sq_mem_alternatingGroup' {β : Type} [Fintype β] [DecidableEq β] (x : Perm β) :
    x ^ 2 ∈ alternatingGroup β :=
  mem_alternatingGroup.mpr (by rw [map_pow]; exact Int.units_sq _)

private theorem isPGroup_two_of_sq_mem {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : IsPGroup 2 (X ⊓ N : Subgroup G)) (h : ∀ x ∈ X, x ^ 2 ∈ N) : IsPGroup 2 X := by
  intro x
  obtain ⟨k, hk⟩ := hXN ⟨(x : G) ^ 2, mem_inf.mpr ⟨pow_mem x.2 2, h x x.2⟩⟩
  have h1 : ((x : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ' (2 : ℕ) k, pow_mul]
  exact h1

private theorem isPGroup_normalizer_of_maximal {β : Type} [Fintype β] [DecidableEq β]
    (h6 : 6 ≤ Fintype.card β) {T : Subgroup (Perm β)} (hT : IsPGroup 2 T)
    (hTA : T ≤ alternatingGroup β)
    (hmax : ∀ Q : Subgroup (Perm β), IsPGroup 2 Q → Q ≤ alternatingGroup β → T ≤ Q → Q = T) :
    IsPGroup 2 (normalizer (T : Set (Perm β))) := by
  refine isPGroup_two_of_sq_mem (N := alternatingGroup β) ?_ fun x _ => sq_mem_alternatingGroup' x
  exact CFSG.GroupTheory.PermSylowTwo.isPGroup_two_of_sylow_le_alt β h6
    (isSylowTwoOf_of_maximal hT hTA hmax) (le_inf le_normalizer hTA) inf_le_right
    (Or.inr inf_le_left)

private theorem exists_mem_normalizer_not_mem_alternatingGroup' {β : Type} [Fintype β]
    [DecidableEq β] [Nontrivial β] {T : Subgroup (Perm β)} (hT : IsPGroup 2 T)
    (hTA : T ≤ alternatingGroup β)
    (hmax : ∀ Q : Subgroup (Perm β), IsPGroup 2 Q → Q ≤ alternatingGroup β → T ≤ Q → Q = T) :
    ∃ g ∈ normalizer (T : Set (Perm β)), g ∉ alternatingGroup β := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hPA : (P : Subgroup (Perm β)) ⊓ alternatingGroup β = T :=
    hmax _ P.isPGroup'.to_inf_left inf_le_right (le_inf hTP hTA)
  have hodd : ¬ (P : Subgroup (Perm β)) ≤ alternatingGroup β := by
    intro hPle
    apply P.not_dvd_index
    have h := relIndex_mul_index hPle
    rw [alternatingGroup.index_eq_two] at h
    exact ⟨(P : Subgroup (Perm β)).relIndex (alternatingGroup β), by rw [← h, mul_comm]⟩
  obtain ⟨g, hgP, hgA⟩ := SetLike.not_le_iff_exists.mp hodd
  refine ⟨g, mem_normalizer_fintype fun t ht => ?_, hgA⟩
  have ht' : t ∈ (P : Subgroup (Perm β)) ⊓ alternatingGroup β := by
    rw [hPA]
    exact ht
  rw [SetLike.mem_coe, ← hPA]
  exact mem_inf.mpr ⟨mul_mem (mul_mem hgP (mem_inf.mp ht').1) (inv_mem hgP),
    (inferInstance : (alternatingGroup β).Normal).conj_mem t (mem_inf.mp ht').2 g⟩

section Transport

variable {α : Type} [Fintype α] [DecidableEq α] {O : Set α} [DecidablePred (· ∈ O)]

private theorem range_ofSubtype_eq_fixOutside :
    (ofSubtype : Perm O →* Perm α).range = fixOutside O := by
  ext g
  rw [mem_range_ofSubtype_iff]
  constructor
  · intro h z hz
    by_contra hne
    exact hz (h (mem_support.mpr hne))
  · intro h z hz
    by_contra hzO
    exact (mem_support.mp hz) (h z hzO)

private theorem le_range_ofSubtype {P : Subgroup (Perm α)} (hP : P ≤ fixOutside O) :
    P ≤ (ofSubtype : Perm O →* Perm α).range := by
  rwa [range_ofSubtype_eq_fixOutside]

private theorem comap_ofSubtype_le_alternatingGroup {S : Subgroup (Perm α)}
    (hSA : S ≤ alternatingGroup α) :
    S.comap (ofSubtype : Perm O →* Perm α) ≤ alternatingGroup O := fun g hg =>
  mem_alternatingGroup.mpr (by
    rw [← sign_ofSubtype]
    exact mem_alternatingGroup.mp (hSA (mem_comap.mp hg)))

private theorem comap_ofSubtype_maximal {S : Subgroup (Perm α)}
    (hSO : S ≤ fixOutside O ⊓ alternatingGroup α)
    (hmax : ∀ Q : Subgroup (Perm α), IsPGroup 2 Q → Q ≤ fixOutside O ⊓ alternatingGroup α →
      S ≤ Q → Q = S) (Q : Subgroup (Perm O)) (hQ : IsPGroup 2 Q) (hQA : Q ≤ alternatingGroup O)
    (hSQ : S.comap (ofSubtype : Perm O →* Perm α) ≤ Q) :
    Q = S.comap (ofSubtype : Perm O →* Perm α) := by
  have hSF : S ≤ fixOutside O := hSO.trans inf_le_left
  have hmap : Q.map (ofSubtype : Perm O →* Perm α) = S := by
    refine hmax (Q.map ofSubtype) (hQ.map _) ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      refine mem_inf.mpr ⟨fun z hz => ofSubtype_apply_of_not_mem q hz, ?_⟩
      rw [mem_alternatingGroup, sign_ofSubtype]
      exact mem_alternatingGroup.mp (hQA hq)
    · rw [← map_comap_eq_self (le_range_ofSubtype hSF)]
      exact map_mono hSQ
  rw [← hmap, comap_map_eq_self_of_injective ofSubtype_injective]

private theorem mem_normalizer_comap_ofSubtype {S : Subgroup (Perm α)} (hSF : S ≤ fixOutside O)
    {g : Perm O} :
    g ∈ normalizer ((S.comap (ofSubtype : Perm O →* Perm α) : Subgroup (Perm O)) :
      Set (Perm O)) ↔ (ofSubtype g : Perm α) ∈ normalizer (S : Set (Perm α)) := by
  rw [← comap_normalizer_eq_of_le_range (le_range_ofSubtype hSF), mem_comap]

end Transport

variable {α : Type} [Fintype α] [DecidableEq α]

theorem isPGroup_normalizer_inf_fixOutside {O : Set α} (hO : 6 ≤ O.ncard)
    {S : Subgroup (Perm α)} (hS : IsPGroup 2 S) (hSO : S ≤ fixOutside O ⊓ alternatingGroup α)
    (hmax : ∀ Q : Subgroup (Perm α), IsPGroup 2 Q → Q ≤ fixOutside O ⊓ alternatingGroup α →
      S ≤ Q → Q = S) :
    IsPGroup 2 (normalizer (S : Set (Perm α)) ⊓ fixOutside O : Subgroup (Perm α)) := by
  classical
  have hSF : S ≤ fixOutside O := hSO.trans inf_le_left
  have hcard : 6 ≤ Fintype.card O := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hO
  have hN := isPGroup_normalizer_of_maximal hcard
    (hS.comap_of_injective (ofSubtype : Perm O →* Perm α) ofSubtype_injective)
    (comap_ofSubtype_le_alternatingGroup (hSO.trans inf_le_right))
    (comap_ofSubtype_maximal hSO hmax)
  refine (hN.map (ofSubtype : Perm O →* Perm α)).to_le fun x hx => ?_
  obtain ⟨hxN, hxF⟩ := mem_inf.mp hx
  obtain ⟨g, rfl⟩ : x ∈ (ofSubtype : Perm O →* Perm α).range := by
    rwa [range_ofSubtype_eq_fixOutside]
  exact ⟨g, (mem_normalizer_comap_ofSubtype hSF).mpr hxN, rfl⟩

theorem exists_mem_normalizer_not_mem_alternatingGroup {O : Set α} (hO : 2 ≤ O.ncard)
    {S : Subgroup (Perm α)} (hS : IsPGroup 2 S) (hSO : S ≤ fixOutside O ⊓ alternatingGroup α)
    (hmax : ∀ Q : Subgroup (Perm α), IsPGroup 2 Q → Q ≤ fixOutside O ⊓ alternatingGroup α →
      S ≤ Q → Q = S) :
    ∃ g ∈ (normalizer (S : Set (Perm α)) ⊓ fixOutside O : Subgroup (Perm α)),
      g ∉ alternatingGroup α := by
  classical
  have hSF : S ≤ fixOutside O := hSO.trans inf_le_left
  have : Nontrivial O := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_coe_set_eq]
    omega
  obtain ⟨g, hgN, hgA⟩ := exists_mem_normalizer_not_mem_alternatingGroup'
    (hS.comap_of_injective (ofSubtype : Perm O →* Perm α) ofSubtype_injective)
    (comap_ofSubtype_le_alternatingGroup (hSO.trans inf_le_right))
    (comap_ofSubtype_maximal hSO hmax)
  refine ⟨ofSubtype g, mem_inf.mpr ⟨(mem_normalizer_comap_ofSubtype hSF).mp hgN,
    fun z hz => ofSubtype_apply_of_not_mem g hz⟩, ?_⟩
  rw [mem_alternatingGroup, sign_ofSubtype]
  exact fun h => hgA (mem_alternatingGroup.mpr h)

end CFSG.GroupTheory.AltCore

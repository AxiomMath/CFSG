module

public import CFSG.CGT.Timmesfeld75.JLemmaTrans

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section KernelCount

variable {G : Type} [Group G] [Finite G] {R T T' : Subgroup G}

theorem card_normIn_eq_mul_card_ker (hT : IsWC T) (hTR : T ≤ R) {x : G} (hx : x ∈ R)
    (hT' : T' = conjSubgroup x T)
    (hker : ∀ w : ↥R, w ∈ (jMap ↥R).ker → conjSubgroup (w : G) T' = T') :
    Nat.card ↥(normIn T T') =
      Nat.card ↥((T.subgroupOf R).map (jMap ↥R) ⊓
          Subgroup.normalizer (((T'.subgroupOf R).map (jMap ↥R) : Subgroup (jQuot ↥R)) :
            Set (jQuot ↥R))) *
        Nat.card ↥(T.subgroupOf R ⊓ (jMap ↥R).ker) := by
  have hT'R : T' ≤ R := hT' ▸ conjSubgroup_le_of_le_of_mem hTR hx
  have hle : normIn T T' ≤ R := (normIn_le T T').trans hTR
  set π := jMap ↥R with hπ
  set U : Subgroup ↥R := (normIn T T').subgroupOf R with hU
  have hcardU : Nat.card U = Nat.card ↥(normIn T T') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hconj : ∀ c : ↥R,
      conjSubgroup c (T'.subgroupOf R) = (conjSubgroup (c : G) T').subgroupOf R :=
    fun c => conjSubgroup_subgroupOf R T' c
  have hconjT : conjSubgroup (⟨x, hx⟩ : ↥R) (T.subgroupOf R) = T'.subgroupOf R := by
    rw [conjSubgroup_subgroupOf, hT']
  let φ : ↥U →* jQuot ↥R := π.comp U.subtype
  have hrange : φ.range = (T.subgroupOf R).map π ⊓
      Subgroup.normalizer (((T'.subgroupOf R).map π : Subgroup (jQuot ↥R)) : Set (jQuot ↥R)) := by
    have hr : φ.range = U.map π := by
      simp [φ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hr]
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have huT : (u : G) ∈ T := (mem_normIn.1 (Subgroup.mem_subgroupOf.1 hu)).1
      have huN : (u : G) ∈ Subgroup.normalizer (T' : Set G) :=
        (mem_normIn.1 (Subgroup.mem_subgroupOf.1 hu)).2
      have hyN : π u ∈ Subgroup.normalizer
          (((T'.subgroupOf R).map π : Subgroup (jQuot ↥R)) : Set (jQuot ↥R)) := by
        rw [mem_normalizer_iff_conjSubgroup_eq, ← map_conjSubgroup, hconj,
          mem_normalizer_iff_conjSubgroup_eq.1 huN]
      exact ⟨⟨u, Subgroup.mem_subgroupOf.2 huT, rfl⟩, hyN⟩
    · rintro ⟨⟨t, ht, rfl⟩, hyN⟩
      have h1 := (mem_normalizer_iff_conjSubgroup_eq.1 hyN)
      rw [← map_conjSubgroup] at h1
      have h2 : conjSubgroup (t * ⟨x, hx⟩) (T.subgroupOf R) =
          conjSubgroup (⟨x, hx⟩ : ↥R) (T.subgroupOf R) := by
        refine eq_of_map_jMap_le (isWC_subgroupOf hT R hTR) (le_of_eq ?_)
        rw [← conjSubgroup_conjSubgroup, hconjT, map_conjSubgroup, ← map_conjSubgroup, h1]
      have h3 : conjSubgroup t (T'.subgroupOf R) = T'.subgroupOf R := by
        rw [← hconjT, conjSubgroup_conjSubgroup, h2]
      have h4 : conjSubgroup (t : G) T' = T' := by
        rw [hconj] at h3
        have := Subgroup.subgroupOf_inj.1 h3
        rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem hT'R t.2), inf_of_le_left hT'R] at this
      refine ⟨t, Subgroup.mem_subgroupOf.2 (mem_normIn.2 ⟨Subgroup.mem_subgroupOf.1 ht,
        mem_normalizer_of_conjSubgroup_eq h4⟩), rfl⟩
  have hkerφ : φ.ker = (π.ker).subgroupOf U := by
    ext y
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hUker : U ⊓ π.ker = T.subgroupOf R ⊓ π.ker := by
    ext u
    constructor
    · rintro ⟨hu, hk⟩
      exact ⟨Subgroup.mem_subgroupOf.2 (mem_normIn.1 (Subgroup.mem_subgroupOf.1 hu)).1, hk⟩
    · rintro ⟨hu, hk⟩
      exact ⟨Subgroup.mem_subgroupOf.2 (mem_normIn.2 ⟨Subgroup.mem_subgroupOf.1 hu,
        mem_normalizer_of_conjSubgroup_eq (hker u hk)⟩), hk⟩
  have hcardker : Nat.card φ.ker = Nat.card ↥(T.subgroupOf R ⊓ π.ker) := by
    rw [hkerφ, ← hUker, ← inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : π.ker ⊓ U ≤ U)).toEquiv
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hcardker, hcardU] at h
  rw [← h, mul_comm]

end KernelCount

end CFSG.CGT.Timmesfeld75

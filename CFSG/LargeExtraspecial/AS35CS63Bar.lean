module

public import CFSG.LargeExtraspecial.AS35CS63Hat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

variable {G : Type} [Group G]

section Bar

variable (t : G)

@[expose] def tC : centralizer ({t} : Set G) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩

theorem tC_mem_center : tC t ∈ center (centralizer ({t} : Set G)) := by
  rw [mem_center_iff]
  intro c
  exact Subtype.ext (mem_centralizer_singleton_iff.mp c.2)

instance normal_zpowers_tC : (zpowers (tC t)).Normal :=
  normal_of_le_center (zpowers_le.mpr (tC_mem_center t))

abbrev Cbar : Type := centralizer ({t} : Set G) ⧸ zpowers (tC t)

@[expose] def piC : centralizer ({t} : Set G) →* Cbar t := QuotientGroup.mk' _

theorem piC_surjective : Function.Surjective (piC t) := QuotientGroup.mk'_surjective _

variable {t}

theorem piC_eq_iff (ht2 : t * t = 1) {a b : centralizer ({t} : Set G)} :
    piC t a = piC t b ↔ (b : G) = a ∨ (b : G) = a * t := by
  have htt : tC t * tC t = 1 := Subtype.ext ht2
  rw [piC, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Setting.mem_zpowers_iff_of_mul_self htt]
  constructor
  · rintro (h | h)
    · left
      have h1 : (a : G)⁻¹ * b = 1 := congrArg Subtype.val h
      calc (b : G) = a * ((a : G)⁻¹ * b) := by group
        _ = a := by rw [h1, mul_one]
    · right
      have h1 : (a : G)⁻¹ * b = t := congrArg Subtype.val h
      calc (b : G) = a * ((a : G)⁻¹ * b) := by group
        _ = a * t := by rw [h1]
  · rintro (h | h)
    · left
      exact Subtype.ext (by
        change (a : G)⁻¹ * b = 1
        rw [h, inv_mul_cancel])
    · right
      exact Subtype.ext (by
        change (a : G)⁻¹ * b = t
        rw [h, inv_mul_cancel_left])

theorem piC_eq_one_iff (ht2 : t * t = 1) {a : centralizer ({t} : Set G)} :
    piC t a = 1 ↔ (a : G) = 1 ∨ (a : G) = t := by
  rw [← (piC t).map_one, eq_comm, piC_eq_iff ht2]
  simp

theorem piC_tC : piC t (tC t) = 1 := by
  rw [piC, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact mem_zpowers _

end Bar

variable (S : Setting G) in
structure Six where
  t : G
  hW : WeakCl S
  htQ : t ∈ S.QG
  ht2 : t * t = 1
  ht1 : t ≠ 1
  htz : t ≠ S.z

namespace Six

variable {S : Setting G} (K : Six S)

theorem z_mem_C : S.z ∈ centralizer ({K.t} : Set G) :=
  mem_centralizer_singleton_iff.mpr (S.z_comm_QG K.htQ).symm

@[expose] def zC : centralizer ({K.t} : Set G) := ⟨S.z, K.z_mem_C⟩

@[expose] def zeta : Cbar K.t := piC K.t K.zC

theorem zeta_mul_zeta : K.zeta * K.zeta = 1 := by
  rw [zeta, ← map_mul]
  have : K.zC * K.zC = 1 := Subtype.ext S.z_mul_z
  rw [this, map_one]

theorem zeta_ne_one : K.zeta ≠ 1 := by
  rw [zeta, Ne, piC_eq_one_iff K.ht2]
  rintro (h | h)
  · exact S.z_ne_one h
  · exact K.htz h.symm

theorem orderOf_zeta : orderOf K.zeta = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact K.zeta_mul_zeta) K.zeta_ne_one

theorem mem_M_of_comm {c : centralizer ({K.t} : Set G)}
    (h : piC K.t c * K.zeta = K.zeta * piC K.t c) : (c : G) ∈ S.M := by
  rw [zeta, ← map_mul, ← map_mul, piC_eq_iff K.ht2] at h
  rcases h with h | h
  · exact S.mem_M_iff.mpr h.symm
  · exfalso
    change S.z * (c : G) = (c : G) * S.z * K.t at h
    have h1 : (c : G)⁻¹ * S.z * (c : G)⁻¹⁻¹ = S.z * K.t := by
      calc (c : G)⁻¹ * S.z * (c : G)⁻¹⁻¹ = (c : G)⁻¹ * (S.z * c) := by group
        _ = S.z * K.t := by rw [h]; group
    have h2 := K.hW _ (h1 ▸ S.QG.mul_mem S.z_mem_QG K.htQ)
    rw [h1] at h2
    exact K.ht1 (mul_eq_left.mp h2)

theorem exists_of_isConj {τ : Cbar K.t} (h : IsConj K.zeta τ) :
    ∃ c : centralizer ({K.t} : Set G), piC K.t (c * K.zC * c⁻¹) = τ := by
  obtain ⟨d, hd⟩ := isConj_iff.mp h
  obtain ⟨c, rfl⟩ := piC_surjective K.t d
  exact ⟨c, by rw [map_mul, map_mul, map_inv]; exact hd⟩

@[expose] def pair (c : centralizer ({K.t} : Set G)) (hyM : (c : G) * S.z * (c : G)⁻¹ ∈ S.M)
    (hyz : (c : G) * S.z * (c : G)⁻¹ ≠ S.z) : Pair S where
  g := c
  t := K.t
  hW := K.hW
  hxM := hyM
  hxz := hyz
  htQ := K.htQ
  hta := by
    rw [S.Qa_eq_map]
    refine ⟨K.t, K.htQ, ?_⟩
    change (c : G) * K.t * (c : G)⁻¹ = K.t
    rw [mem_centralizer_singleton_iff.mp c.2]
    group
  ht1 := K.ht1

theorem pair_x (c : centralizer ({K.t} : Set G)) (hyM) (hyz) :
    (K.pair c hyM hyz).x = (c : G) * S.z * (c : G)⁻¹ := rfl

@[expose] noncomputable def Hbar : Subgroup (Cbar K.t) :=
  ((Hhat S K.htQ K.ht2).subgroupOf (centralizer ({K.t} : Set G))).map (piC K.t)

theorem mem_Hbar_of {u : centralizer ({K.t} : Set G)} (hu : (u : G) ∈ Hhat S K.htQ K.ht2) :
    piC K.t u ∈ K.Hbar :=
  ⟨u, by rw [SetLike.mem_coe, mem_subgroupOf]; exact hu, rfl⟩

theorem lift_mem_M {c : centralizer ({K.t} : Set G)}
    (h : piC K.t (c * K.zC * c⁻¹) * K.zeta = K.zeta * piC K.t (c * K.zC * c⁻¹)) :
    (c : G) * S.z * (c : G)⁻¹ ∈ S.M :=
  K.mem_M_of_comm h

variable [Finite G]

theorem isPGroup_Hbar : IsPGroup 2 K.Hbar :=
  ((isPGroup_Hhat K.htQ K.ht2).comap_of_injective _
    (centralizer ({K.t} : Set G)).subtype_injective).map _

theorem commutator_commutator_Hbar : ⁅⁅K.Hbar, K.Hbar⁆, K.Hbar⁆ = ⊥ := by
  set H' := (Hhat S K.htQ K.ht2).subgroupOf (centralizer ({K.t} : Set G)) with hH'
  have h1 : ⁅⁅H', H'⁆, H'⁆ = ⊥ := by
    have hle : H'.map (centralizer ({K.t} : Set G)).subtype ≤ Hhat S K.htQ K.ht2 := by
      rintro _ ⟨u, hu, rfl⟩
      exact hu
    have h2 : (⁅⁅H', H'⁆, H'⁆).map (centralizer ({K.t} : Set G)).subtype = ⊥ := by
      rw [map_commutator, map_commutator, eq_bot_iff,
        ← commutator_commutator_Hhat K.htQ K.ht2]
      exact commutator_mono (commutator_mono hle hle) hle
    exact (map_eq_bot_iff_of_injective _ (centralizer ({K.t} : Set G)).subtype_injective).mp h2
  rw [Hbar, ← hH', ← map_commutator, ← map_commutator, h1, Subgroup.map_bot]

end Six

end S63

end CFSG.LargeExtraspecial

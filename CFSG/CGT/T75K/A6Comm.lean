module

public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

@[expose] def cm (t u : G) : G := t * u * t⁻¹ * u⁻¹

theorem cm_one_left (u : G) : cm 1 u = 1 := by simp [cm]

theorem cm_one_right (t : G) : cm t 1 = 1 := by simp [cm]

theorem cm_eq_one_iff {t u : G} : cm t u = 1 ↔ t * u = u * t := by
  unfold cm
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

section Generic

variable {T : Subgroup G} {u t s : G}

theorem cm_mem_T (ht : t ∈ T) (hu : u ∈ Subgroup.normalizer (T : Set G)) : cm t u ∈ T := by
  have h1 : u * t⁻¹ * u⁻¹ ∈ T := conj_mem_of_mem_normalizer hu (T.inv_mem ht)
  have e : cm t u = t * (u * t⁻¹ * u⁻¹) := by unfold cm; group
  rw [e]
  exact T.mul_mem ht h1

theorem cm_mul_left (hT : IsElemAbelian 2 T) (ht : t ∈ T) (hs : s ∈ T)
    (hu : u ∈ Subgroup.normalizer (T : Set G)) : cm (t * s) u = cm s u * cm t u := by
  have hw : cm s u ∈ T := cm_mem_T hs hu
  have hcomm : t * cm s u = cm s u * t := elemAbelian_mul_comm hT ht hw
  calc cm (t * s) u = (t * cm s u * t⁻¹) * cm t u := by unfold cm; group
    _ = cm s u * cm t u := by rw [hcomm]; group

theorem cm_comm_u (hT : IsElemAbelian 2 T) (ht : t ∈ T) (hu : u ∈ Subgroup.normalizer (T : Set G))
    (hu2 : u * u = 1) : cm t u * u = u * cm t u := by
  have hw : cm t u ∈ T := cm_mem_T ht hu
  have hww : cm t u * cm t u = 1 := elemAbelian_mul_self hT hw
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h1 : u * cm t u * u⁻¹ = (cm t u)⁻¹ := by
    have hu2' : u⁻¹ * u⁻¹ = 1 := by rw [hui]; exact hu2
    calc u * cm t u * u⁻¹ = u * t * u * t⁻¹ * (u⁻¹ * u⁻¹) := by unfold cm; group
      _ = u * t * u * t⁻¹ := by rw [hu2', mul_one]
      _ = u * t * u⁻¹ * t⁻¹ := by rw [hui]
      _ = (cm t u)⁻¹ := by unfold cm; group
  have h2 : (cm t u)⁻¹ = cm t u := inv_eq_of_mul_eq_one_right hww
  rw [h2] at h1
  calc cm t u * u = (u * cm t u * u⁻¹) * u := by rw [h1]
    _ = u * cm t u := by group

@[expose] noncomputable def thetaHom (hT : IsElemAbelian 2 T)
    (hu : u ∈ Subgroup.normalizer (T : Set G)) (hu2 : u * u = 1) :
    ↥T →* ↥(T ⊓ Subgroup.centralizer ({u} : Set G)) where
  toFun t := ⟨cm (t : G) u, cm_mem_T t.2 hu,
    Subgroup.mem_centralizer_singleton_iff.2 (cm_comm_u hT t.2 hu hu2)⟩
  map_one' := Subtype.ext (cm_one_left u)
  map_mul' a b := by
    apply Subtype.ext
    show cm ((a : G) * b) u = cm (a : G) u * cm (b : G) u
    rw [cm_mul_left hT a.2 b.2 hu]
    exact elemAbelian_mul_comm hT (cm_mem_T b.2 hu) (cm_mem_T a.2 hu)

theorem ker_thetaHom (hT : IsElemAbelian 2 T) (hu : u ∈ Subgroup.normalizer (T : Set G))
    (hu2 : u * u = 1) :
    (thetaHom hT hu hu2).ker = (T ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf T := by
  ext t
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h1 : cm (t : G) u = 1 := congrArg Subtype.val h
    exact ⟨t.2, Subgroup.mem_centralizer_singleton_iff.2 (cm_eq_one_iff.1 h1)⟩
  · rintro ⟨-, hc⟩
    apply Subtype.ext
    show cm (t : G) u = 1
    rw [cm_eq_one_iff]
    exact Subgroup.mem_centralizer_singleton_iff.1 hc

theorem card_range_thetaHom (hT : IsElemAbelian 2 T) (hu : u ∈ Subgroup.normalizer (T : Set G))
    (hu2 : u * u = 1) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G)) * Nat.card (thetaHom hT hu hu2).range =
      Nat.card T := by
  have h := Subgroup.card_ker_mul_card_range (thetaHom hT hu hu2)
  rw [ker_thetaHom] at h
  have hle : T ⊓ Subgroup.centralizer ({u} : Set G) ≤ T := inf_le_left
  have h2 : Nat.card ↥((T ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf T) =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h
  exact h

end Generic

end CFSG.CGT.T75K

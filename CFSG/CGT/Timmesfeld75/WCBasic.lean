module

public import CFSG.CGT.Timmesfeld75.Involutions
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conjSubgroup_conjSubgroup (g h : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup h T) = conjSubgroup (g * h) T := by
  ext x
  simp only [mem_conjSubgroup]
  constructor
  · intro hx
    simpa [mul_assoc] using hx
  · intro hx
    simpa [mul_assoc] using hx

theorem conjSubgroup_one (T : Subgroup G) : conjSubgroup 1 T = T := by
  ext x
  simp [mem_conjSubgroup]

theorem mem_normalizer_iff_conjSubgroup_eq {T : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (T : Set G) ↔ conjSubgroup g T = T := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

theorem conjSubgroup_le_iff {g : G} {S T : Subgroup G} :
    conjSubgroup g S ≤ T ↔ S ≤ conjSubgroup g⁻¹ T := by
  constructor
  · intro h x hx
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using h ((mem_conjSubgroup).2 (by simpa [mul_assoc] using hx))
  · intro h x hx
    have := h ((mem_conjSubgroup).1 hx)
    rw [mem_conjSubgroup] at this
    simpa [mul_assoc] using this

theorem conjSubgroup_inj {g : G} {S T : Subgroup G} :
    conjSubgroup g S = conjSubgroup g T ↔ S = T := by
  constructor
  · intro h
    ext x
    have := congrArg (fun K : Subgroup G => g * x * g⁻¹ ∈ K) h
    simp only [mem_conjSubgroup, eq_iff_iff] at this
    simpa [mul_assoc] using this
  · rintro rfl; rfl

theorem isElemAbelian_conjSubgroup {p : ℕ} {T : Subgroup G} (hT : IsElemAbelian p T) (g : G) :
    IsElemAbelian p (conjSubgroup g T) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    change (a : G) * b = b * a
    rw [← ha, ← hb]
    show g * a' * g⁻¹ * (g * b' * g⁻¹) = g * b' * g⁻¹ * (g * a' * g⁻¹)
    have := elemAbelian_mul_comm hT ha' hb'
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [this]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  · obtain ⟨y, hy, rfl⟩ := hx
    show (g * y * g⁻¹) ^ p = 1
    have := hT.2 y hy
    calc (g * y * g⁻¹) ^ p = g * y ^ p * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [this]; simp

theorem IsWC.centralizer_le_normalizer {T : Subgroup G} (hT : IsWC T) {y : G} (hy : y ∈ T)
    (hy1 : y ≠ 1) : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (T : Set G) := by
  intro z hz
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine (hT.2 y hy hy1).2 z fun x hx => Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hzy : z * h = h * z := (Subgroup.mem_centralizer_iff.1 hz h (Set.mem_singleton h)).symm
  have hyc : h ∈ conjSubgroup z T := by
    rw [mem_conjSubgroup]
    have : z⁻¹ * h * z = h := by rw [mul_assoc, ← hzy, ← mul_assoc, inv_mul_cancel, one_mul]
    rwa [this]
  exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hT.1 z) hyc hx

theorem IsWC.conj_eq_of_inf_ne_bot {T : Subgroup G} (hT : IsWC T) {g : G}
    (h : T ⊓ conjSubgroup g T ≠ ⊥) : conjSubgroup g T = T := by
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
  have htT : t ∈ T := ht.1
  have htc : t ∈ conjSubgroup g T := ht.2
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  refine (hT.2 t htT ht1').2 g fun x hx => Subgroup.mem_centralizer_iff.2 fun h' hh => ?_
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact elemAbelian_mul_comm (isElemAbelian_conjSubgroup hT.1 g) htc hx

theorem IsWC.inf_conj_eq_bot {T : Subgroup G} (hT : IsWC T) {g : G}
    (hne : conjSubgroup g T ≠ T) : T ⊓ conjSubgroup g T = ⊥ := by
  by_contra h
  exact hne (hT.conj_eq_of_inf_ne_bot h)

theorem IsWC.isTI {T : Subgroup G} (hT : IsWC T) : IsTI T := by
  intro g
  by_cases h : conjSubgroup g T = T
  · right; rw [h]; exact inf_idem T
  · left; exact hT.inf_conj_eq_bot h

end CFSG.CGT.Timmesfeld75

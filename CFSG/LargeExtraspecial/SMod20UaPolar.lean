module

public import CFSG.Fischer.Polar.PerpPerp
public import CFSG.Fischer.T46Simple

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer

section Polar


@[expose] def stabOrb (p q : Fin 693) : Set (Fin 693) := {x | ∃ g ∈ T46, g p = p ∧ g q = x}

theorem stabOrb_subset_perp {p q : Fin 693} (h : perp p q) : stabOrb p q ⊆ {x | perp p x} := by
  rintro _ ⟨g, hg, hgp, rfl⟩
  show perp p (g q)
  rw [← hgp, perp_apply_of_mem hg]
  exact h

theorem not_perp_zero_iff (x : Fin 693) : ¬ perp 0 x ↔ t46SubLab x = 1 := by
  have hset : {x : Fin 693 | t46SubLab x = 1} ⊆ {x | perp 0 x} ∨
      {x : Fin 693 | t46SubLab x = 1} ⊆ {x | ¬ perp 0 x} := by
    by_cases h01 : perp 0 (⟨1, by norm_num⟩ : Fin 693)
    · refine Or.inl fun y hy => ?_
      obtain ⟨⟨g, hg⟩, rfl⟩ := t46SubLab_eq_one.1 hy
      show perp 0 (g • (⟨1, _⟩ : Fin 693))
      rw [← t46lvl_one_fix hg, Equiv.Perm.smul_def, Equiv.Perm.smul_def,
        perp_apply_of_mem (t46lvl_one_le hg)]
      exact h01
    · refine Or.inr fun y hy => ?_
      obtain ⟨⟨g, hg⟩, rfl⟩ := t46SubLab_eq_one.1 hy
      show ¬ perp 0 (g • (⟨1, _⟩ : Fin 693))
      rw [← t46lvl_one_fix hg, Equiv.Perm.smul_def, Equiv.Perm.smul_def,
        perp_apply_of_mem (t46lvl_one_le hg)]
      exact h01
  have h512 : {x : Fin 693 | t46SubLab x = 1}.ncard = 512 := by
    rw [← card_t46SubLab_one, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp
  have hperp : {x : Fin 693 | perp 0 x}.ncard = 181 := ncard_setOf_perp 0
  have hnperp : {x : Fin 693 | ¬ perp 0 x}.ncard = 512 := by
    rw [show {x : Fin 693 | ¬ perp 0 x} = {x | perp 0 x}ᶜ from rfl, Set.ncard_compl, hperp,
      Nat.card_fin]
  rcases hset with hs | hs
  · have := Set.ncard_le_ncard hs (Set.toFinite _)
    omega
  · have heq := Set.eq_of_subset_of_ncard_le hs (by rw [h512, hnperp]) (Set.toFinite _)
    rw [Set.ext_iff] at heq
    exact (heq x).symm

theorem not_perp_subset_stabOrb {p q : Fin 693} (h : ¬ perp p q) :
    {x | ¬ perp p x} ⊆ stabOrb p q := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := exists_smul_zero p
  have ha := isPolarAut_of_mem hg
  have tr : ∀ y, ¬ perp (g 0) y → t46SubLab (g⁻¹ y) = 1 := fun y hy => by
    rw [← not_perp_zero_iff]
    intro h'
    apply hy
    rw [← perm_apply_inv_self g y, ha.map_perp]
    exact h'
  obtain ⟨k, hk, hkx⟩ := t46SubLab_orb (g⁻¹ q) (g⁻¹ x) ((tr q h).trans (tr x hx).symm)
  refine ⟨g * k * g⁻¹, T46.mul_mem (T46.mul_mem hg (t46lvl_one_le hk)) (T46.inv_mem hg), ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, perm_inv_apply_self]
    rw [← Equiv.Perm.smul_def k 0, t46lvl_one_fix hk]
  · simp only [Equiv.Perm.mul_apply]
    rw [← Equiv.Perm.smul_def k, hkx, perm_apply_inv_self]

theorem image_stabOrb {π : Equiv.Perm (Fin 693)}
    (hπ : π ∈ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693)))) (p q : Fin 693) :
    ⇑π '' stabOrb p q = stabOrb (π p) (π q) := by
  have hN := Subgroup.mem_normalizer_iff.1 hπ
  have hN' := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hπ)
  ext y
  constructor
  · rintro ⟨_, ⟨g, hg, hgp, rfl⟩, rfl⟩
    refine ⟨π * g * π⁻¹, (hN g).1 hg, ?_, ?_⟩ <;>
      simp only [Equiv.Perm.mul_apply, perm_inv_apply_self, hgp]
  · rintro ⟨h, hh, hhp, rfl⟩
    refine ⟨π⁻¹ (h (π q)), ⟨π⁻¹ * h * π⁻¹⁻¹, (hN' h).1 hh, ?_, ?_⟩, perm_apply_inv_self π _⟩ <;>
      simp only [inv_inv, Equiv.Perm.mul_apply, hhp, perm_inv_apply_self]

theorem perp_apply_of_mem_normalizer {π : Equiv.Perm (Fin 693)}
    (hπ : π ∈ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693)))) {p q : Fin 693}
    (h : perp p q) : perp (π p) (π q) := by
  by_contra h'
  have h1 := Set.ncard_le_ncard ((not_perp_subset_stabOrb h').trans
    ((image_stabOrb hπ p q).symm.subset.trans (Set.image_mono (stabOrb_subset_perp h))))
    (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ π.injective, ncard_setOf_perp] at h1
  have h2 : {x : Fin 693 | ¬ perp (π p) x}.ncard = 512 := by
    rw [show {x : Fin 693 | ¬ perp (π p) x} = {x | perp (π p) x}ᶜ from rfl, Set.ncard_compl,
      ncard_setOf_perp, Nat.card_fin]
  omega

theorem isPolarAut_of_mem_normalizer {π : Equiv.Perm (Fin 693)}
    (hπ : π ∈ Subgroup.normalizer (T46 : Set (Equiv.Perm (Fin 693)))) : IsPolarAut π := by
  have hπ' := Subgroup.inv_mem _ hπ
  have map_perp : ∀ a b, perp (π a) (π b) ↔ perp a b := fun a b =>
    ⟨fun h => by simpa only [perm_inv_apply_self] using perp_apply_of_mem_normalizer hπ' h,
      perp_apply_of_mem_normalizer hπ⟩
  refine ⟨map_perp, fun a b => ?_⟩
  by_cases hab : perp a b
  · rw [tvP_apply_eq_self_iff.2 hab, tvP_apply_eq_self_iff.2 ((map_perp a b).2 hab)]
  · have hc : ¬ perp a (tvP a b) := fun h =>
      hab (by rw [← perp_tvP a a b, tvP_self]; exact h)
    have hN : ∀ w, perp w a ∧ perp w b ↔ perp w a ∧ perp w (tvP a b) := fun w => by
      constructor
      · rintro ⟨hw, hwb⟩
        refine ⟨hw, ?_⟩
        rw [← tvP_apply_eq_self_iff.2 (perp_comm.1 hw), perp_tvP]
        exact hwb
      · rintro ⟨hw, hwc⟩
        refine ⟨hw, ?_⟩
        rw [← tvP_apply_eq_self_iff.2 (perp_comm.1 hw), perp_tvP] at hwc
        exact hwc
    have hN' : ∀ w, perp w (π a) ∧ perp w (π b) ↔ perp w (π a) ∧ perp w (π (tvP a b)) :=
      fun w => by
        rw [← perm_apply_inv_self π w, map_perp, map_perp, map_perp]
        exact hN _
    rcases eq_of_perp_perp (fun h => hab ((map_perp a b).1 h))
      (fun h => hc ((map_perp a _).1 h)) hN' with h | h
    · exact absurd (tvP_apply_eq_self_iff.1 (π.injective h)) hab
    · exact h

end Polar

end CFSG.LargeExtraspecial.SMod20

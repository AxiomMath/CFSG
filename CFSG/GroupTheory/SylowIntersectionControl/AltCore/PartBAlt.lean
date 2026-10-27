module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.AltOrbits
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.GoodY
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.AltIsolated
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.OrbitCount
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartA
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.TransitiveCase

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

variable {n : ℕ} {H : Subgroup (Perm (Fin n))}

theorem exists_goodY_alt_of_forall_not_isEvenSetAlt (hn : 7 ≤ n)
    (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hall : ∀ x, ¬ IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x)) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧ normalizer (H : Set (Perm (Fin n))) ≤ Y := by
  have hfix3 : (fixSet H).ncard ≤ 3 := by
    rcases (fixSet H).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h, Set.ncard_empty]
      omega
    · refine ncard_fixSet_le_three ?_
      rw [fixSet_eq_orbit hx]
      exact hall x
  have hdvd : 4 ∣ (fixSet H)ᶜ.ncard :=
    dvd_ncard_of_forall_dvd (P := normalizer (H : Set (Perm (Fin n))))
      (fun g hg x hx h => hx ((fixSet_mem_setStab hg x).mp h)) fun x hx => by
        rw [Nat.card_coe_set_eq, ncard_orbit_eq_four hH hrad hHL hx (hall x)]
  have hsum := Set.ncard_add_ncard_compl (fixSet H)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  have hD : ∀ x ∈ fixSet H, ∀ y,
      (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)).r x y ↔ y ∈ fixSet H :=
    fun x hx y => by
      change x ∈ orbit _ y ↔ _
      rw [fixSet_eq_orbit hx]
      exact mem_orbit_symm
  have hcls : ∀ x, x ∉ fixSet H →
      Nat.card {y // (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)).r x y} = 2 ^ 2 :=
    fun x hx => by
      rw [show Nat.card {y // (orbitRel (normalizer (H : Set (Perm (Fin n)))) (Fin n)).r x y} =
          Nat.card (orbit (normalizer (H : Set (Perm (Fin n)))) x) from
          Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_orbit_symm),
        Nat.card_coe_set_eq, ncard_orbit_eq_four hH hrad hHL hx (hall x)]
      rfl
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_of_classes hn hn2 (Or.inr rfl) hD
    (by rw [Nat.card_coe_set_eq]; show _ = n % 4; omega) hcls
    (good := (· ∈ normalizer (H : Set (Perm (Fin n)))))
    (fun a ha => mem_partStab_iff.mpr fun x y => orbitRel_apply_iff (le_normalizer ha) x y)
    fun a ha x => fixSet_mem_setStab ha x
  exact ⟨Y, hY, fun a ha => hYa a ha⟩

theorem isPIsolatedOver_alternatingGroup_fixSet [DecidablePred (· ∈ fixSet H)]
    (hH : IsPGroup 2 H) (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    (he : IsEvenSetAlt H (fixSet H)) :
    IsPIsolatedOver 2 (alternatingGroup (fixSet H)) (⊥ : Subgroup (Perm (fixSet H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : fixOutside (fixSet H) ≤ normalizer (H : Set (Perm (Fin n))) := fun g hg =>
    mem_normalizer_fintype fun h hh => by
      have hc : g * h = h * g := (Disjoint.commute fun z => by
        by_cases hz : z ∈ fixSet H
        · exact Or.inr (hz h hh)
        · exact Or.inl (hg z hz)).eq
      rw [hc, mul_inv_cancel_right]
      exact hh
  obtain ⟨x, hx, hxO, hxH, hx2⟩ := he
  have hiso' := IsPIsolatedOver.inf_of_normal_of_le hiso hH (le_inf le_normalizer hHL)
    inf_le_left (inf_le_inf_right _ hTN)
    ((le_inf (inf_le_left.trans (le_normalizer_fixOutside fixSet_mem_setStab))
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)
    (mem_inf.mpr ⟨hxO, (mem_inf.mp hx).2⟩) hxH hx2
  have hbot : fixOutside (fixSet H) ⊓ alternatingGroup (Fin n) ⊓ H = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    rw [mem_bot]
    refine Equiv.ext fun z => ?_
    by_cases hz : z ∈ fixSet H
    · exact hz g (mem_inf.mp hg).2
    · exact (mem_inf.mp (mem_inf.mp hg).1).1 z hz
  have hmap : (alternatingGroup (fixSet H)).map
      (ofSubtype : Perm (fixSet H) →* Perm (Fin n)) =
      fixOutside (fixSet H) ⊓ alternatingGroup (Fin n) := by
    ext g
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine mem_inf.mpr ⟨fun z hz => ofSubtype_apply_of_not_mem σ hz, ?_⟩
      rw [mem_alternatingGroup, sign_ofSubtype]
      exact hσ
    · intro hg
      obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff (p := (· ∈ fixSet H)) (g := g)).mpr
        fun z hz => by
        by_contra h
        exact (mem_support.mp hz) ((mem_inf.mp hg).1 z h)
      refine ⟨σ, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_alternatingGroup, ← sign_ofSubtype]
      exact (mem_inf.mp hg).2
  rwa [hbot, ← hmap, ← map_bot (ofSubtype : Perm (fixSet H) →* Perm (Fin n)),
    isPIsolatedOver_map_iff_of_injective ofSubtype_injective] at hiso'

theorem not_isEvenSetAlt_compl (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    {O : Set (Fin n)} (hO : normalizer (H : Set (Perm (Fin n))) ≤ setStab O)
    (he : IsEvenSetAlt H O) : ¬ IsEvenSetAlt H Oᶜ := fun hc =>
  not_isEvenSetAlt_of_disjoint hH hrad hHL hiso hO (by rw [setStab_compl]; exact hO)
    (by rw [compl_compl]) he hc

theorem false_of_isEvenSetAlt_fixSet (hn : 7 ≤ n) (hn9 : n ≠ 9) (hH : IsPGroup 2 H)
    (hrad : IsRadical H) (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    (he : IsEvenSetAlt H (fixSet H)) : False := by
  classical
  have hOc : normalizer (H : Set (Perm (Fin n))) ≤ setStab (fixSet H)ᶜ := by
    rw [setStab_compl]
    exact fixSet_mem_setStab
  have hR := not_isEvenSetAlt_compl hH hrad hHL hiso fixSet_mem_setStab he
  have hR5 := ncard_le_five_of_not_isEvenSetAlt hH hrad hHL hOc hR
  have hsub : ∀ x ∈ (fixSet H)ᶜ, orbit (normalizer (H : Set (Perm (Fin n)))) x ⊆ (fixSet H)ᶜ := by
    rintro x hx _ ⟨⟨g, hg⟩, rfl⟩ h
    exact hx ((fixSet_mem_setStab hg x).mp h)
  obtain ⟨c, hc⟩ : 4 ∣ (fixSet H)ᶜ.ncard :=
    dvd_ncard_of_forall_dvd (P := normalizer (H : Set (Perm (Fin n))))
      (fun g hg x hx h => hx ((fixSet_mem_setStab hg x).mp h)) fun x hx => by
        rw [Nat.card_coe_set_eq,
          ncard_orbit_eq_four hH hrad hHL hx fun hc => hR (hc.mono (hsub x hx))]
  have h5 : (fixSet H).ncard = 5 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact card_eq_five_of_isPIsolatedOver_alternatingGroup
      (isPIsolatedOver_alternatingGroup_fixSet hH hHL hiso he)
  have hsum := Set.ncard_add_ncard_compl (fixSet H)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  omega

variable {x₀ : Fin n}

theorem restrSub_section_alt (hH : IsPGroup 2 H) (hrad : IsRadical H)
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (he : IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) :
    normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ≤
      normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) ∧
    normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) ≤
      normalizer ((normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) ∧
    ∃ x ∈ normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n), x ∉ H ∧ x ^ 2 ∈ H := by
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm (Fin n))) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) :=
    fun a ha => mem_normalizer_fintype fun k hk => conj_mem_restrSub ha (hO ha) hk
  refine ⟨fun g hg => mem_inf.mpr ⟨mem_normalizer_of_mem_fixOutside hH hrad hO
      (mem_inf.mp (mem_inf.mp hg).1).2 (mem_inf.mp (mem_inf.mp hg).1).1, (mem_inf.mp hg).2⟩,
    (le_inf (inf_le_left.trans ((le_inf (hKN.trans le_normalizer)
      (le_normalizer_fixOutside hO)).trans inf_normalizer_le_normalizer_inf))
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf, ?_⟩
  obtain ⟨x, hx, hxO, hxH, hx2⟩ := he
  exact ⟨x, mem_inf.mpr ⟨mem_inf.mpr ⟨hKN (mem_inf.mp hx).1, hxO⟩, (mem_inf.mp hx).2⟩, hxH, hx2⟩

theorem isPIsolatedOver_restrSub_alt (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (he : IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)) :
    IsPIsolatedOver 2 (normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n))
      (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H) := by
  have hO := orbit_mem_setStab (H := H) x₀
  obtain ⟨hMN, hNM, x, hxM, hxH, hx2⟩ := restrSub_section_alt hH hrad he
  have hiso' := IsPIsolatedOver.inf_of_normal_of_le hiso hH (le_inf le_normalizer hHL)
    inf_le_left hMN hNM hxM hxH hx2
  have hMH : normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ⊓ H =
      restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H := by
    refine le_antisymm (fun g hg => ?_) (le_inf (le_inf (le_inf le_normalizer
      restrSub_le_fixOutside) ((restrSub_le hH hrad hO).trans hHL)) (restrSub_le hH hrad hO))
    have hgO := (mem_inf.mp (mem_inf.mp (mem_inf.mp hg).1).1).2
    rw [← restrHom_eq_self hgO (fixOutside_le_setStab _ hgO)]
    exact restrHom_mem_restrSub (mem_inf.mp hg).2
  rwa [hMH] at hiso'

theorem exists_card_orbit_omegaOneCenterOf_eq_alt (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (he : IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀))
    (hx₀ : x₀ ∉ fixSet H) :
    ∃ i, (i = 1 ∨ i = 2) ∧ ∀ x ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀,
      Nat.card (orbit (omegaOneCenterOf
        (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H)) x) = 2 ^ i := by
  have hO := orbit_mem_setStab (H := H) x₀
  have hKN : normalizer (H : Set (Perm (Fin n))) ≤
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) :=
    fun a ha => mem_normalizer_fintype fun k hk => conj_mem_restrSub ha (hO ha) hk
  refine exists_card_orbit_omegaOneCenterOf_eq_of_le hH hx₀
    (card_orbit_omegaOneCenter_le_four (isPGroup_restrSub hH) restrSub_le_fixOutside
      (le_inf (le_inf le_normalizer restrSub_le_fixOutside) ((restrSub_le hH hrad hO).trans hHL))
      (inf_le_left.trans inf_le_left) le_rfl (fun a ha b hb => ?_)
      (isPIsolatedOver_restrSub_alt hH hrad hHL hiso he) (mem_orbit_self x₀))
  obtain ⟨⟨g₁, hg₁⟩, rfl⟩ := ha
  obtain ⟨⟨g₂, hg₂⟩, rfl⟩ := hb
  refine ⟨g₂ * g₁⁻¹, hKN (mul_mem hg₂ (inv_mem hg₁)), ?_⟩
  change (g₂ * g₁⁻¹) (g₁ x₀) = g₂ x₀
  rw [Perm.mul_apply]
  exact congrArg g₂ (g₁.symm_apply_apply x₀)

end CFSG.GroupTheory.AltCore

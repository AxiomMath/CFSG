module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartBBlocks
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartASym
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.TransitiveCase
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartBAlt

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction
open CFSG.Quasithin (omegaOneCenterOf)

variable {n : ℕ} {H : Subgroup (Perm (Fin n))}

theorem exists_goodY_alt_of_not_mem_fixSet (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (hH : IsPGroup 2 H) (hrad : IsRadical H) (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    {x₀ : Fin n} [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm (Fin n)))) x₀)]
    (he : IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀))
    (hx₀ : x₀ ∉ fixSet H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      normalizer (restrSub (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) H :
        Set (Perm (Fin n))) ⊓ fixOutside (orbit (normalizer (H : Set (Perm (Fin n)))) x₀) ⊓
        alternatingGroup (Fin n) ≤ Y ∧ H ≤ Y := by
  have hO := orbit_mem_setStab (H := H) x₀
  have hR := not_isEvenSetAlt_compl hH hrad hHL hiso hO he
  have hΦ : ∀ x ∈ fixSet H, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ :=
    fun x hx hxO => hx₀ (by
      rw [fixSet_eq_orbit hx, orbit_eq_iff.mpr hxO]
      exact mem_orbit_self x₀)
  have hΦ3 : (fixSet H).ncard ≤ 3 := ncard_fixSet_le_three fun h => hR (h.mono hΦ)
  have hR4 : ∀ x, x ∉ orbit (normalizer (H : Set (Perm (Fin n)))) x₀ → x ∉ fixSet H →
      (orbit (normalizer (H : Set (Perm (Fin n)))) x).ncard = 4 := fun x hxO hxΦ =>
    ncard_orbit_eq_four hH hrad hHL hxΦ fun h => hR (h.mono (by
      rintro _ ⟨⟨g, hg⟩, rfl⟩ hz
      exact hxO ((hO hg x).mp hz)))
  obtain ⟨i, hi, hE⟩ := exists_card_orbit_omegaOneCenterOf_eq_alt hH hrad hHL hiso he hx₀
  rcases hi with rfl | rfl
  · exact exists_goodY_alt_two hn hn2 hH hE hΦ hΦ3
  · obtain ⟨Y, hY, hNY⟩ := exists_goodY_alt_four hn hn2 hE hR4 hΦ hΦ3
    obtain ⟨hMN, -, -⟩ := restrSub_section_alt hH hrad he
    exact ⟨Y, hY, (hMN.trans inf_le_left).trans hNY, le_normalizer.trans hNY⟩

theorem exists_goodY_alt_of_isRadical (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (hH : IsPGroup 2 H) (hHL : H ≤ alternatingGroup (Fin n)) (hrad : IsRadical H)
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∃ K : Subgroup (Perm (Fin n)), H ≤ K ∧
        K ≤ normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) ∧
        (K.subgroupOf
          (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n))).IsSubnormal ∧
        2 ∣ H.relIndex K ∧ K ≤ Y := by
  classical
  have hHN := le_inf (le_normalizer (H := H)) hHL
  by_cases hex : ∃ x₀, IsEvenSetAlt H (orbit (normalizer (H : Set (Perm (Fin n)))) x₀)
  · obtain ⟨x₀, he⟩ := hex
    by_cases hx₀ : x₀ ∈ fixSet H
    · refine (false_of_isEvenSetAlt_fixSet hn (fun h => hn2 3 (by omega)) hH hrad hHL hiso ?_).elim
      rw [fixSet_eq_orbit hx₀]
      exact he
    obtain ⟨Y, hY, hMY, hHY⟩ := exists_goodY_alt_of_not_mem_fixSet hn hn2 hH hrad hHL hiso he hx₀
    obtain ⟨hMN, hNM, x, hxM, hxH, hx2⟩ := restrSub_section_alt hH hrad he
    refine ⟨Y, hY, _, le_sup_right, sup_le hMN hHN, ?_, two_dvd_relIndex_of_sq_mem le_sup_right
      (sup_le (hMN.trans inf_le_left) le_normalizer) (mem_sup_left hxM) hxH hx2, sup_le hMY hHY⟩
    exact ((normal_subgroupOf_iff_le_normalizer (sup_le hMN hHN)).mpr
      (le_normalizer_sup' hNM inf_le_left)).isSubnormal
  · push Not at hex
    obtain ⟨Y, hY, hNY⟩ := exists_goodY_alt_of_forall_not_isEvenSetAlt hn hn2 hH hrad hHL hex
    obtain ⟨x, hx, -, hxH, hx2⟩ := isEvenSetAlt_univ hH hHL hiso
    refine ⟨Y, hY, _, hHN, le_rfl, ?_, two_dvd_relIndex_of_sq_mem hHN inf_le_left hx hxH hx2,
      inf_le_left.trans hNY⟩
    rw [subgroupOf_self]
    exact .top

private theorem sign_eq_neg_one {g : Perm (Fin n)} (hg : g ∉ alternatingGroup (Fin n)) :
    sign g = -1 :=
  (Int.units_eq_one_or _).resolve_left fun h => hg (mem_alternatingGroup.mpr h)

theorem mul_inv_mem_alternatingGroup {g k : Perm (Fin n)} (hg : g ∉ alternatingGroup (Fin n))
    (hk : k ∉ alternatingGroup (Fin n)) : g * k⁻¹ ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, map_mul, map_inv, sign_eq_neg_one hg, sign_eq_neg_one hk]
  decide

private theorem sup_inf_alternatingGroup_eq (hH : IsPGroup 2 H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    {P : Subgroup (Perm (Fin n))} (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (H : Set (Perm (Fin n))))
    (hNP : normalizer (H : Set (Perm (Fin n))) ≤ normalizer (P : Set (Perm (Fin n)))) :
    (P ⊔ H) ⊓ alternatingGroup (Fin n) = H ∧
      normalizer ((P ⊔ H : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) =
        normalizer (H : Set (Perm (Fin n))) := by
  have hK : IsPGroup 2 (P ⊔ H : Subgroup (Perm (Fin n))) := hP.to_sup_of_normal_right' hH hPN
  have hKN : P ⊔ H ≤ normalizer (H : Set (Perm (Fin n))) := sup_le hPN le_normalizer
  have hNK : normalizer (H : Set (Perm (Fin n))) ≤
      normalizer ((P ⊔ H : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) :=
    le_normalizer_sup' hNP le_rfl
  have hKL : (P ⊔ H) ⊓ alternatingGroup (Fin n) = H := le_antisymm
    (IsPIsolatedOver.le_of_normal hiso hH (le_inf le_normalizer hHL) inf_le_left
      (inf_le_inf_right _ hKN) (hK.to_le inf_le_left)
      ((le_inf (inf_le_left.trans hNK) le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf))
    (le_inf le_sup_right hHL)
  refine ⟨hKL, le_antisymm (fun g hg => ?_) hNK⟩
  have := ((le_inf (le_refl (normalizer ((P ⊔ H : Subgroup (Perm (Fin n))) :
    Set (Perm (Fin n))))) (le_normalizer_of_normal (H := alternatingGroup (Fin n)))).trans
    inf_normalizer_le_normalizer_inf) hg
  rwa [hKL] at this

theorem exists_goodY_alt_of_not_isRadical (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1)
    (hH : IsPGroup 2 H) (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H)
    (hnrad : ¬ IsRadical H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∀ a ∈ normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n), a ^ 2 ∈ H → a ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hPN, hNP, hPH⟩ : ∃ P : Subgroup (Perm (Fin n)), IsPGroup 2 P ∧
      P ≤ normalizer (H : Set (Perm (Fin n))) ∧
      normalizer (H : Set (Perm (Fin n))) ≤ normalizer (P : Set (Perm (Fin n))) ∧ ¬ P ≤ H := by
    by_contra h
    push Not at h
    exact hnrad h
  have hK : IsPGroup 2 (P ⊔ H : Subgroup (Perm (Fin n))) := hP.to_sup_of_normal_right' hH hPN
  have hKN : P ⊔ H ≤ normalizer (H : Set (Perm (Fin n))) := sup_le hPN le_normalizer
  obtain ⟨hKL, hNK⟩ := sup_inf_alternatingGroup_eq hH hHL hiso hP hPN hNP
  obtain ⟨k, hkK, hkL⟩ : ∃ k ∈ P ⊔ H, k ∉ alternatingGroup (Fin n) := by
    by_contra h
    push Not at h
    exact hPH (le_sup_left.trans (hKL ▸ le_inf le_rfl fun k hk => h k hk))
  have hsup : (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) ⊔ (P ⊔ H) =
      normalizer (H : Set (Perm (Fin n))) := by
    refine le_antisymm (sup_le inf_le_left hKN) fun g hg => ?_
    by_cases hgL : g ∈ alternatingGroup (Fin n)
    · exact mem_sup_left (mem_inf.mpr ⟨hg, hgL⟩)
    · have hgk : g * k⁻¹ ∈ normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) :=
        mem_inf.mpr ⟨mul_mem hg (inv_mem (hKN hkK)), mul_inv_mem_alternatingGroup hgL hkL⟩
      simpa using mul_mem (mem_sup_left hgk) (mem_sup_right hkK)
  have hinf : (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) ⊓ (P ⊔ H) = H := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hKN, hKL]
  have hiso' : IsPIsolatedOver 2 (normalizer ((P ⊔ H : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n)))) (P ⊔ H) := by
    rw [hNK, ← hsup]
    exact (isPIsolatedOver_sup_iff hK (inf_le_left.trans (hNK ▸ le_rfl))).mpr
      (by rw [hinf]; exact hiso)
  obtain ⟨Y, hY, hYa⟩ := exists_goodY_sym hn hn2 hK hiso'
  exact ⟨Y, hY, fun a ha ha2 => hYa a (hNK ▸ (mem_inf.mp ha).1) (mem_sup_right ha2)⟩

theorem exists_goodY_alt (hn : 7 ≤ n) (hn2 : ∀ m : ℕ, n ≠ 2 ^ m + 1) (hH : IsPGroup 2 H)
    (hHL : H ≤ alternatingGroup (Fin n))
    (hiso : IsPIsolatedOver 2 (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n)) H) :
    ∃ Y : Subgroup (Perm (Fin n)), GoodY Y ∧
      ∃ K : Subgroup (Perm (Fin n)), H ≤ K ∧
        K ≤ normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) ∧
        (K.subgroupOf
          (normalizer (H : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n))).IsSubnormal ∧
        2 ∣ H.relIndex K ∧ K ≤ Y := by
  by_cases hrad : IsRadical H
  · exact exists_goodY_alt_of_isRadical hn hn2 hH hHL hrad hiso
  · obtain ⟨Y, hY, hYa⟩ := exists_goodY_alt_of_not_isRadical hn hn2 hH hHL hiso hrad
    exact ⟨Y, hY, IsPIsolatedOver.exists_le_of_sq_mem_of_le hiso hH (le_inf le_normalizer hHL)
      inf_le_left hYa⟩

end CFSG.GroupTheory.AltCore

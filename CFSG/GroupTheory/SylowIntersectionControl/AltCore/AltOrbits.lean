module

public import CFSG.GroupTheory.SylowIntersectionControl.AltCore.AltEven
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.AltSylow
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.OrbitCount
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartA

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup MulAction

variable {α : Type} [Fintype α] [DecidableEq α] {H : Subgroup (Perm α)}

theorem ncard_le_five_of_not_isEvenSetAlt (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup α) {O : Set α} (hO : normalizer (H : Set (Perm α)) ≤ setStab O)
    (hne : ¬ IsEvenSetAlt H O) : O.ncard ≤ 5 := by
  classical
  by_contra h6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := isPGroup_restrSub (O := O) hH
  have hSO : restrSub O H ≤ fixOutside O ⊓ alternatingGroup α :=
    le_inf restrSub_le_fixOutside ((restrSub_le hH hrad hO).trans hHL)
  have hmax : ∀ Q : Subgroup (Perm α), IsPGroup 2 Q → Q ≤ fixOutside O ⊓ alternatingGroup α →
      restrSub O H ≤ Q → Q = restrSub O H := fun Q hQ hQO hPQ =>
    eq_restrSub_of_not_isEvenSetAlt hH hrad hO hne hQ hQO hPQ
  have hKN : normalizer (H : Set (Perm α)) ≤ normalizer (restrSub O H : Set (Perm α)) :=
    fun n hn => mem_normalizer_fintype fun k hk => conj_mem_restrSub hn (hO hn) hk
  have hT := isPGroup_normalizer_inf_fixOutside (by omega) hS hSO hmax
  have hTN : (normalizer (restrSub O H : Set (Perm α)) ⊓ fixOutside O : Subgroup (Perm α)) ≤
      normalizer (H : Set (Perm α)) := fun g hg =>
    mem_normalizer_of_mem_fixOutside hH hrad hO (mem_inf.mp hg).2 (mem_inf.mp hg).1
  have hTH := hrad _ hT hTN
    ((le_inf (hKN.trans le_normalizer) (le_normalizer_fixOutside hO)).trans
      inf_normalizer_le_normalizer_inf)
  obtain ⟨g, hg, hgL⟩ := exists_mem_normalizer_not_mem_alternatingGroup (by omega) hS hSO hmax
  exact hgL (hHL (hTH hg))

omit [DecidableEq α] in
theorem two_dvd_card_orbit_of_not_mem_fixSet (hH : IsPGroup 2 H) {x : α} (hx : x ∉ fixSet H) :
    2 ∣ Nat.card (orbit H x) := by
  obtain ⟨j, hj⟩ := exists_card_orbit_eq_two_pow' hH x
  rcases j with _ | j
  · refine absurd (fun h hh => ?_) hx
    rw [pow_zero] at hj
    obtain ⟨w, hw⟩ := Nat.card_eq_one_iff_exists.mp hj
    exact congrArg Subtype.val ((hw ⟨h x, ⟨⟨h, hh⟩, rfl⟩⟩).trans (hw ⟨x, mem_orbit_self x⟩).symm)
  · rw [hj]
    exact dvd_pow_self 2 (Nat.succ_ne_zero j)

theorem fixSet_eq_orbit {x : α} (hx : x ∈ fixSet H) :
    fixSet H = orbit (normalizer (H : Set (Perm α))) x := by
  refine (fixSet_subset_orbit hx).antisymm ?_
  rintro _ ⟨⟨n, hn⟩, rfl⟩
  exact (fixSet_mem_setStab hn x).mpr hx

omit [Fintype α] in
private theorem restrHom_eq_swap {x : α} {h : Perm α} (hh : h ∈ H) (hhx : h x ≠ x)
    (hO : normalizer (H : Set (Perm α)) ≤ setStab (orbit (normalizer (H : Set (Perm α))) x))
    [DecidablePred (· ∈ orbit (normalizer (H : Set (Perm α))) x)]
    (hOeq : orbit (normalizer (H : Set (Perm α))) x = {x, h x}) :
    restrHom (orbit (normalizer (H : Set (Perm α))) x) ⟨h, hO (le_normalizer hh)⟩ =
      swap x (h x) := by
  have hhh : h (h x) = x := by
    have hm : h (h x) ∈ orbit (normalizer (H : Set (Perm α))) x :=
      (hO (le_normalizer hh) (h x)).mpr (hOeq ▸ Or.inr rfl)
    rw [hOeq] at hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd (h.injective hm) hhx
  ext z
  by_cases hz : z ∈ orbit (normalizer (H : Set (Perm α))) x
  · rw [restrHom_apply_of_mem _ hz]
    rw [hOeq] at hz
    rcases hz with rfl | rfl
    · exact (swap_apply_left z (h z)).symm
    · exact hhh.trans (swap_apply_right x (h x)).symm
  · rw [restrHom_apply_of_not_mem _ hz]
    rw [hOeq] at hz
    exact (swap_apply_of_ne_of_ne (fun e => hz (Or.inl e)) fun e => hz (Or.inr e)).symm

theorem ncard_orbit_eq_four (hH : IsPGroup 2 H) (hrad : IsRadical H)
    (hHL : H ≤ alternatingGroup α) {x : α} (hx : x ∉ fixSet H)
    (hne : ¬ IsEvenSetAlt H (orbit (normalizer (H : Set (Perm α))) x)) :
    (orbit (normalizer (H : Set (Perm α))) x).ncard = 4 := by
  classical
  have hO := orbit_mem_setStab (H := H) x
  have h5 := ncard_le_five_of_not_isEvenSetAlt hH hrad hHL hO hne
  have hfix : ∀ y ∈ orbit (normalizer (H : Set (Perm α))) x, y ∉ fixSet H := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩ hy
    exact hx ((fixSet_mem_setStab hn x).mp hy)
  have h2 : 2 ∣ (orbit (normalizer (H : Set (Perm α))) x).ncard :=
    dvd_ncard_of_forall_dvd (P := H) (fun g hg y hy => (hO (le_normalizer hg) y).mpr hy)
      fun y hy => two_dvd_card_orbit_of_not_mem_fixSet hH (hfix y hy)
  obtain ⟨h, hh, hhx⟩ : ∃ h ∈ H, h x ≠ x := by
    by_contra hall
    push Not at hall
    exact hx hall
  have hsub : ({x, h x} : Set α) ⊆ orbit (normalizer (H : Set (Perm α))) x := by
    rintro z (rfl | rfl)
    · exact mem_orbit_self z
    · exact ⟨⟨h, le_normalizer hh⟩, rfl⟩
  have hpos : 2 ≤ (orbit (normalizer (H : Set (Perm α))) x).ncard := by
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair hhx.symm] at this
  have hne2 : (orbit (normalizer (H : Set (Perm α))) x).ncard ≠ 2 := by
    intro h2'
    have hOeq : orbit (normalizer (H : Set (Perm α))) x = {x, h x} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [h2', Set.ncard_pair hhx.symm])).symm
    have hmem := restrHom_mem hH hrad hO hh
    rw [restrHom_eq_swap hh hhx hO hOeq] at hmem
    have hs := hHL hmem
    rw [mem_alternatingGroup, sign_swap hhx.symm] at hs
    exact absurd hs (by decide)
  omega

end CFSG.GroupTheory.AltCore

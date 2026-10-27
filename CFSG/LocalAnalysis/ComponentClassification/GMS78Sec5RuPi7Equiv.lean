module

public import Certificates.Certificate15103
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPi7
public import CFSG.Sporadic.Bridge.RuSurjBase

public section

namespace CFSG.ComponentClassification.GMS78.RuPi7

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
open CFSG.CosetTable

theorem lift_mk_eq_wordProd {G : Type*} [Group G] {m : ℕ} (x : ℕ → G) (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i : Fin m => x i.val) (FreeGroup.mk w) =
      wordProd x (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, s⟩ := l
    cases s
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp [wordProd]
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp [wordProd]

noncomputable abbrev pi7Img : ℕ → J CFSG.Sporadic.Ru.Native.ruData :=
  img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)

noncomputable def pi7ToJ :
    Pi7 →* J CFSG.Sporadic.Ru.Native.ruData :=
  PresentedGroup.toGroup (f := fun i : Fin 7 => pi7Img i.val) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_eq_wordProd]
    exact Certificates.certificate15103.1 w hw

theorem pi7ToJ_of (i : Fin 7) :
    pi7ToJ (PresentedGroup.of i) = pi7Img i.val :=
  PresentedGroup.toGroup.of _

noncomputable def pi7Gen (i : ℕ) : Pi7 := if h : i < 7 then PresentedGroup.of ⟨i, h⟩ else 1

noncomputable def pi7Letter (z : ℤ) : Pi7 :=
  if 0 < z then pi7Gen (z - 1).toNat else (pi7Gen (-z - 1).toNat)⁻¹

theorem pi7ToJ_pi7Letter {z : ℤ} (hz : z.natAbs ≤ 7) :
    pi7ToJ (pi7Letter z) = imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData) z := by
  unfold pi7Letter imgG pi7Gen
  split_ifs with h h1 h2
  · exact pi7ToJ_of _
  · omega
  · rw [map_inv, pi7ToJ_of]
  · omega

theorem wordG_mem_range {w : List ℤ}
    (hw : ∀ z ∈ w, z.natAbs ≤ 7) :
    wordG (imgG pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) w ∈ pi7ToJ.range := by
  refine ⟨wordG pi7Letter w, ?_⟩
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact pi7ToJ_pi7Letter (hw z hz)

theorem pi7ToJ_surjective : Function.Surjective pi7ToJ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab CFSG.Sporadic.Ru.Native.ruData,
    Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [← Certificates.certificate15103.2.1]
    exact wordG_mem_range (by decide)
  · rw [← Certificates.certificate15103.2.2]
    exact wordG_mem_range (by decide)

theorem pi7ToJ_bijective :
    Function.Bijective pi7ToJ := by
  have := card_pi7_le.1
  exact pi7ToJ_surjective.bijective_of_nat_card_le
    (card_pi7_le.2.trans CFSG.Sporadic.Bridge.Ru.card_J.ge)

noncomputable def pi7EquivJ :
    Pi7 ≃* J CFSG.Sporadic.Ru.Native.ruData :=
  MulEquiv.ofBijective pi7ToJ pi7ToJ_bijective

end CFSG.ComponentClassification.GMS78.RuPi7

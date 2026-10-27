module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalEndData

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] def centerBar (D A : Subgroup G) : Subgroup (Bar D) :=
  bar D A ⊓ Subgroup.centralizer (bar D A : Set (Bar D))

omit [Finite G] in
theorem centerBar_le (A : Subgroup G) : centerBar D A ≤ bar D A := inf_le_left

omit [Finite G] in
theorem centerBar_comm (A : Subgroup G) {z : Bar D} (hz : z ∈ centerBar D A) :
    ∀ x ∈ bar D A, z * x = x * z := fun x hx => (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm

omit [Finite G] in
theorem core_le_factorZStar (i : Fin r) : aschbacherThm5Core D ≤ factorZStar D Abar i := by
  intro o ho
  refine ⟨core_le_preimage D _ ho, (mem_centralizing_iff (Abar i) o).mpr
    ⟨core_le D ho, fun a ha => ?_⟩⟩
  have haH : a ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer (preimage_le D _ ha)
  have h1 : a⁻¹ * o * a ∈ aschbacherThm5Core D := by
    have := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_core D (Subgroup.inv_mem _ haH)) o).mp ho
    simpa using this
  have : o⁻¹ * a⁻¹ * o * a = o⁻¹ * (a⁻¹ * o * a) := by group
  rw [this]
  exact (aschbacherThm5Core D).mul_mem ((aschbacherThm5Core D).inv_mem ho) h1

omit [Finite G] in
theorem bar_factorZStar (i : Fin r) :
    bar D (factorZStar D Abar i) = centerBar D (aschbacherThm5Preimage D (Abar i)) := by
  set A := aschbacherThm5Preimage D (Abar i)
  have hAD : A ≤ D := preimage_le D _
  apply le_antisymm
  · intro x hx
    obtain ⟨h, ⟨hhA, hhC⟩, rfl⟩ := (mem_bar_iff D _ x).mp hx
    exact ⟨toBar_mem_bar D hhA, (centralizes_iff_mem_centralizer D A hAD h).mp
      (centralizes_of_mem_centralizing hhC)⟩
  · rintro x ⟨hxA, hxC⟩
    obtain ⟨h, hhA, rfl⟩ := (mem_bar_iff D A x).mp hxA
    refine toBar_mem_bar D ⟨hhA, (mem_centralizing_iff (Abar i) h).mpr
      ⟨hAD hhA, (centralizes_iff_mem_centralizer D A hAD h).mpr hxC⟩⟩

omit [Finite G] in
theorem le_normalizer_centerBar {A : Subgroup G} {x : Bar D}
    (hx : x ∈ Subgroup.normalizer (bar D A : Set (Bar D))) :
    x ∈ Subgroup.normalizer (centerBar D A : Set (Bar D)) := by
  have key : ∀ y ∈ Subgroup.normalizer (bar D A : Set (Bar D)), ∀ z ∈ centerBar D A,
      y * z * y⁻¹ ∈ centerBar D A := by
    intro y hy z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp hy z).mp hz.1, ?_⟩
    show y * z * y⁻¹ ∈ Subgroup.centralizer (bar D A : Set (Bar D))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : y⁻¹ * w * y ∈ bar D A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) w).mp hw
      simpa using this
    have hc := centerBar_comm A hz _ hw'
    calc w * (y * z * y⁻¹) = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by rw [hc]
      _ = y * z * y⁻¹ * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key x hx z, fun hz => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hz
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] {E : Subgroup X}
    (hE : IsElemAbelian 2 E) (f : X →* Y) : IsElemAbelian 2 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

namespace EndHyp

variable {a : Fin r} {d : DeltaDatum D Abar a}

omit [Finite G] in
theorem A_le_H : aschbacherThm5Preimage D (Abar a) ≤ Subgroup.normalizer (D : Set G) :=
  (preimage_le D _).trans Subgroup.le_normalizer

omit [Finite G] in
theorem S_le_H : d.S ≤ Subgroup.normalizer (D : Set G) := d.sylowS.le.trans A_le_H

omit [Finite G] in
theorem V_le_H : AschbacherTheorem3.omegaOne d.S ≤ Subgroup.normalizer (D : Set G) :=
  V_le_S.trans S_le_H

omit [Finite G] in
theorem barU_le_normalizer :
    bar D (AschbacherTheorem3.omegaOne d.T) ≤
      Subgroup.normalizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)) :=
  bar_le_normalizer U_le_normalizer_A A_le_H

theorem barU_inf_barA (hC : Counterexample G D r Abar) :
    bar D (AschbacherTheorem3.omegaOne d.T) ⊓ bar D (aschbacherThm5Preimage D (Abar a)) = ⊥ := by
  rw [← bar_inf_of_core_le (core_le_preimage D _), U_inf_A hC, eq_bot_iff]
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (mem_bar_iff D ⊥ x).mp hx
  rw [Subgroup.mem_bot] at hh ⊢
  rw [show h = 1 from Subtype.ext hh, map_one]

theorem card_barU (hC : Counterexample G D r Abar) :
    Nat.card (bar D (AschbacherTheorem3.omegaOne d.T)) =
      Nat.card (AschbacherTheorem3.omegaOne d.T) :=
  card_bar_of_isPGroup (d.sylowT.isPGroup.to_le U_le_T) (U_le_H hC)

theorem card_barV :
    Nat.card (bar D (AschbacherTheorem3.omegaOne d.S)) =
      Nat.card (AschbacherTheorem3.omegaOne d.S) :=
  card_bar_of_isPGroup (d.sylowS.isPGroup.to_le V_le_S) V_le_H

theorem isSylowOf_barS :
    IsSylowOf 2 (bar D d.S) (bar D (aschbacherThm5Preimage D (Abar a))) :=
  isSylowOf_bar d.sylowS A_le_H

omit [Finite G] in
theorem barU_le_normalizer_S :
    bar D (AschbacherTheorem3.omegaOne d.T) ≤ Subgroup.normalizer (bar D d.S : Set (Bar D)) :=
  bar_le_normalizer U_le_normalizer_S S_le_H

theorem mem_barV {x : Bar D} (hx : x ∈ bar D d.S) (hx2 : x ^ 2 = 1) :
    x ∈ bar D (AschbacherTheorem3.omegaOne d.S) := by
  obtain ⟨s, hs, rfl⟩ := (mem_bar_iff D d.S x).mp hx
  refine toBar_mem_bar D (mem_omegaOne hs ?_)
  rw [← map_pow, toBar_eq_one_iff] at hx2
  have h1 := eq_one_of_mem_core hx2 (twoElt_of_mem d.sylowS.isPGroup (d.S.pow_mem hs 2))
  simpa using h1

theorem barU_comm_barV (hE : EndHyp d) (hC : Counterexample G D r Abar) :
    ∀ u ∈ bar D (AschbacherTheorem3.omegaOne d.T),
      ∀ v ∈ bar D (AschbacherTheorem3.omegaOne d.S), u * v = v * u := by
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := (mem_bar_iff D _ u).mp hu
  obtain ⟨v', hv', rfl⟩ := (mem_bar_iff D _ v).mp hv
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hE.U_comm_V hC u' hu' v' hv')

theorem barU_comm_mem (hE : EndHyp d) (hC : Counterexample G D r Abar) :
    ∀ u ∈ bar D (AschbacherTheorem3.omegaOne d.T), ∀ s ∈ bar D d.S,
      u⁻¹ * s⁻¹ * u * s ∈ bar D (AschbacherTheorem3.omegaOne d.S) := by
  intro u hu s hs
  obtain ⟨u', hu', rfl⟩ := (mem_bar_iff D _ u).mp hu
  obtain ⟨s', hs', rfl⟩ := (mem_bar_iff D _ s).mp hs
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact toBar_mem_bar D (hE.comm_mem_V hC u' hu' s' hs')

theorem card_inf_le :
    Nat.card (AschbacherTheorem3.omegaOne d.S ⊓ factorZStar D Abar a : Subgroup G) ≤
      Nat.card (bar D (AschbacherTheorem3.omegaOne d.S) ⊓
        centerBar D (aschbacherThm5Preimage D (Abar a)) : Subgroup (Bar D)) := by
  have hP2 : IsPGroup 2 (AschbacherTheorem3.omegaOne d.S ⊓ factorZStar D Abar a : Subgroup G) :=
    (d.sylowS.isPGroup.to_le V_le_S).to_inf_left
  rw [← card_bar_of_isPGroup hP2 (inf_le_left.trans V_le_H), ← bar_factorZStar]
  exact Subgroup.card_le_of_le (le_inf (bar_mono D inf_le_left) (bar_mono D inf_le_right))

theorem bar_conj_le (hE : EndHyp d) (hC : Counterexample G D r Abar)
    (c : Subgroup.normalizer (D : Set G)) (hc : (c : G) ∈ aschbacherThm5Preimage D (Abar a))
    (hle : rightConjugate (bar D (AschbacherTheorem3.omegaOne d.T)) (toBar D c) ≤
      bar D d.S ⊔ bar D (AschbacherTheorem3.omegaOne d.T) ⊔
        centerBar D (aschbacherThm5Preimage D (Abar a))) :
    rightConjugate (bar D (AschbacherTheorem3.omegaOne d.T)) (toBar D c) ≤
      bar D (AschbacherTheorem3.omegaOne d.T) ⊔ bar D (AschbacherTheorem3.omegaOne d.S) ⊔
        centerBar D (aschbacherThm5Preimage D (Abar a)) := by
  have hZH : factorZStar D Abar a ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans A_le_H
  rw [← bar_rightConjugate, ← bar_factorZStar, ← bar_sup S_le_H (U_le_H hC),
    ← bar_sup (sup_le S_le_H (U_le_H hC)) hZH] at hle
  rw [← bar_rightConjugate, ← bar_factorZStar, ← bar_sup (U_le_H hC) V_le_H,
    ← bar_sup (sup_le (U_le_H hC) V_le_H) hZH]
  have hUcH : rightConjugate (AschbacherTheorem3.omegaOne d.T) (c : G) ≤
      Subgroup.normalizer (D : Set G) := rightConjugate_le_normalizer (U_le_H hC) c
  have h1 := BarTools.le_sup_core_of_bar_le hUcH hle
  rw [sup_eq_left.mpr (core_le_factorZStar a |>.trans le_sup_right)] at h1
  exact bar_mono D (hE.conj_le_of_le_sup_zStar hC hc h1)

theorem barA_inf_centralizer_le (hE : EndHyp d) (hC : Counterexample G D r Abar) {u : G}
    (hu : u ∈ AschbacherTheorem3.omegaOne d.T) (hu1 : u ≠ 1) :
    bar D (aschbacherThm5Preimage D (Abar a)) ⊓
        Subgroup.centralizer ({toBar D ⟨u, U_le_H hC hu⟩} : Set (Bar D)) ≤
      bar D (aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) := by
  have hu2 : orderOf u = 2 := by
    apply orderOf_eq_prime (hE.U_elem.2 u hu) hu1
  rw [← BarTools.bar_inf_centralizer (core_le_preimage D _) (U_le_H hC hu) hu2]
  refine bar_mono D (inf_le_inf_left _ ?_)
  exact centralizer_le_conj hC a d.g (twoElt_of_mem (d.sylowT.isPGroup.to_le U_le_T) hu) hu1
    (U_le_L hu)

theorem false_of_barA_le (hC : Counterexample G D r Abar)
    (hle : bar D (aschbacherThm5Preimage D (Abar a)) ≤
      bar D (aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g)) : False := by
  have h1 := BarTools.le_sup_core_of_bar_le A_le_H hle
  exact datum_g_not_mem d (mem_normalizer_of_le_sup hC a d.g _ inf_le_right
    (inf_le_left.trans A_le_H) h1)

end EndHyp

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5

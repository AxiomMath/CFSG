module

public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

namespace S289

variable {X : Type} [Group X]

theorem not_le_of_comm {C N : Subgroup X} (hC : IsComponent C)
    (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : ¬ C ≤ N := by
  intro hle
  have : Nontrivial C := LocalCores.isQuasisimple_nontrivial hC.1
  have : Group.IsPerfect C := hC.1.1
  exact Group.IsPerfect.not_isSolvable C
    (Group.isSolvable_of_comm fun x y => Subtype.ext (hN _ (hle x.2) _ (hle y.2)))

theorem commute_of_normal_comm [Finite X] {C N : Subgroup X} (hC : IsComponent C) (hN : N.Normal)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {a : X} (ha : a ∈ N) :
    ∀ c ∈ C, a * c = c * a := by
  rcases LocalCores.component_normal_subgroup hC hN with h | h
  · exact absurd h (not_le_of_comm hC hab)
  · intro c hc
    have h1 := Subgroup.commutator_mem_commutator hc ha
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem e8_not_isComponent [Finite X] (h : ∃ E : Subgroup X, TC.Thin.E8Struct ⊤ E)
    {C : Subgroup X} (hC : IsComponent C) : False := by
  obtain ⟨E, hE⟩ := h
  have hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => TC.Thin.comm_of_sq hE.sq hx hy
  have hEn : E.Normal := ⟨fun e he g => hE.normal g (Subgroup.mem_top g) e he⟩
  apply not_le_of_comm hC hab
  intro c hc
  exact hE.cent c (Subgroup.mem_top c) fun e he =>
    (commute_of_normal_comm hC hEn hab he c hc).symm

theorem wNormal_commute [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaGen Φ)
    (hV : ∃ V : Subgroup X, WSet Φ = {V}) {C : Subgroup X} (hC : IsComponent C) {L : Subgroup X}
    (hL : L ∈ Φ) {a : X} (ha : IsUniqueInvolution L a) : ∀ c ∈ C, a * c = c * a := by
  obtain ⟨V, hV1⟩ := hV
  have hW : V ∈ WSet Φ := by rw [hV1]; rfl
  have hVn : V.Normal := ⟨fun n hn g => by
    have h1 := WSet.conj hΦ.conjInvariant hW g
    rw [hV1] at h1
    have h2 := Generic.conj_mem_conjSub (n := g) hn
    rwa [show conjSub g V = V from h1] at h2⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hP := isSylow2In_map_subtype L P
  have hD : (P : Subgroup ↥L).map L.subtype ∈ DSet Φ V := by
    refine ⟨mem_RSet_of_isSylow2In hL hP, fun x _ => Subgroup.mem_normalizer_iff.mpr fun h => ?_⟩
    refine ⟨fun hh => hVn.conj_mem h hh x, fun hh => ?_⟩
    have h1 := hVn.conj_mem _ hh x⁻¹
    rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h1
  have haV := (Q3CL.Thompson.uniqueInvolution_mem_W hΦ hW hL hD hP ha).2
  exact commute_of_normal_comm hC hVn (Q3CL.Thompson.commutes_of_mem_WSet hΦ hW) haV

theorem vecBar_normal (n : ℕ) : ((AE.vecSub n).map (AE.mkQ n)).Normal :=
  (AE.vecSub_normal).map _ (QuotientGroup.mk'_surjective _)

theorem vecBar_comm (n : ℕ) : ∀ x ∈ (AE.vecSub n).map (AE.mkQ n),
    ∀ y ∈ (AE.vecSub n).map (AE.mkQ n), x * y = y * x := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  have h1 := AE.vecSub_mul_self ((AE.vecSub n).mul_mem hv hw)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (AE.vecSub_mul_self hv)
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (AE.vecSub_mul_self hw)
  calc v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = w * v := by rw [mul_inv_rev, hvi, hwi]

theorem e64_commute [Finite X] {Φ : Set (Subgroup X)} (hgen : omegaGen Φ = ⊤)
    (h : Nonempty (TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub)) {C : Subgroup X}
    (hC : IsComponent C) {L : Subgroup X} (hL : L ∈ Φ) {a : X} (ha : IsUniqueInvolution L a) :
    ∀ c ∈ C, a * c = c * a := by
  obtain ⟨D⟩ := h
  have hsp : TC.Thin.pSpan Φ = ⊤ := hgen
  have hCP : C ≤ TC.Thin.pSpan Φ := hsp ▸ le_top
  have haP : a ∈ TC.Thin.pSpan Φ := hsp ▸ Subgroup.mem_top a
  have hC' := LocalCores.component_overgroup hC hCP
  have hNn : (((AE.vecSub 7).map (AE.mkQ 7)).comap D.φ).Normal := (vecBar_normal 7).comap _
  rcases LocalCores.component_normal_subgroup hC' hNn with hle | hcomm
  ·
    exfalso
    have hP : Group.IsPerfect ↥(C.subgroupOf (TC.Thin.pSpan Φ)) := hC'.1.1
    have hle' : commutator ↥(C.subgroupOf (TC.Thin.pSpan Φ)) ≤
        (D.φ.comp (C.subgroupOf (TC.Thin.pSpan Φ)).subtype).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro y _ z _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact vecBar_comm 7 _ (hle y.2) _ (hle z.2)
    have hZ : C.subgroupOf (TC.Thin.pSpan Φ) ≤ Subgroup.center ↥(TC.Thin.pSpan Φ) := by
      intro x hx
      have htop : (⟨x, hx⟩ : ↥(C.subgroupOf (TC.Thin.pSpan Φ))) ∈
          commutator ↥(C.subgroupOf (TC.Thin.pSpan Φ)) := by
        rw [hP.commutator_eq_top]
        exact Subgroup.mem_top _
      exact D.ker_le (hle' htop)
    exact not_le_of_comm hC' (fun x _ y hy => (Subgroup.mem_center_iff.mp hy x)) hZ
  ·
    obtain ⟨α, -, hα, b, hlab⟩ := D.label L hL
    have hmem : D.φ ⟨a, haP⟩ ∈ AE.memBar α hα b := by
      rw [← hlab]
      exact ⟨⟨a, haP⟩, Subgroup.mem_subgroupOf.mpr ha.mem, rfl⟩
    have hsq : D.φ ⟨a, haP⟩ * D.φ ⟨a, haP⟩ = 1 := by
      rw [← map_mul, ← map_one D.φ]
      exact congrArg D.φ (Subtype.ext ha.sq)
    have haN : (⟨a, haP⟩ : ↥(TC.Thin.pSpan Φ)) ∈ ((AE.vecSub 7).map (AE.mkQ 7)).comap D.φ := by
      rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hmem hsq with h1 | h1
      · rw [Subgroup.mem_comap, h1]
        exact Subgroup.one_mem _
      · rw [Subgroup.mem_comap, h1]
        exact ⟨_, AE.zOf_perm _, rfl⟩
    intro c hc
    have h1 := Subgroup.commutator_mem_commutator
      (show (⟨c, hCP hc⟩ : ↥(TC.Thin.pSpan Φ)) ∈ C.subgroupOf (TC.Thin.pSpan Φ) from
        Subgroup.mem_subgroupOf.mpr hc) haN
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact (congrArg Subtype.val h1).symm

end S289

end CFSG.ClassicalInvolution.Q3.TL4

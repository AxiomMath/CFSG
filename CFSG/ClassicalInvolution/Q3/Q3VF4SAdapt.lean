module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SShape
public import CFSG.ClassicalInvolution.Q3.Q3VF4SAdaptModel
public import CFSG.ClassicalInvolution.Q3.Q3TPSChart
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3V.Lift
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_stdPlane isHyperbolicPlane_stdPlane longBlock shortBlock)

open scoped MatrixGroups

local notation "F₃" => GaloisField 3 1


variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

theorem range_normal_of_dictR {m : ℕ} (d : ShapeCDictR m Ω z) : d.ψ.range.Normal := by
  classical
  have hmem : ∀ L ∈ centralizingMembers Ω {z},
      locImg Ω z L ≤ Subgroup.normalizer (d.ψ.range : Set (locQuot Ω z)) := by
    intro L hL
    have hLfam : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
    rcases d.fam_cases _ hLfam with h | ⟨P, hP, hPL⟩
    · intro q hq
      apply Subgroup.centralizer_le_normalizer (d.ψ.range : Set (locQuot Ω z))
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact d.commutes c hc q (h hq)
    · rw [hPL]
      exact (Subgroup.map_le_range _ _).trans Subgroup.le_normalizer
  have hlayer : locImg Ω z (locLayer Ω z) = ⊤ := by
    unfold locImg
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have h1 : locLayer Ω z = ⨆ L : ↥(centralizingMembers Ω {z}), (L : Subgroup G) := by
    simp only [locLayer, centralizingLayer, iSup_subtype']
  have hsup : locImg Ω z (locLayer Ω z) =
      ⨆ L : ↥(centralizingMembers Ω {z}), locImg Ω z (L : Subgroup G) :=
    (congrArg (locImg Ω z) h1).trans (locImg_iSup _ (fun L => le_centralizingLayer L.2))
  have hle : (⊤ : Subgroup (locQuot Ω z)) ≤
      Subgroup.normalizer (d.ψ.range : Set (locQuot Ω z)) := by
    rw [← hlayer, hsup]
    exact iSup_le fun L => hmem L L.2
  exact ⟨fun c hc g => ((Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_top g))) c).mp hc⟩

theorem commutes_of_locAut_fixed3 (hΩ : InClass3 Ω) (hP1 : LocalOddCentral Ω {z})
    (hO3 : LocalOddThreeFree3 Ω z) {t : G} (ht : t * z * t⁻¹ = z) {A : Type*} [Group A]
    (f : A →* ↥(locLayer Ω z)) (hpow : Pow3 f.range)
    (hfix : ∀ a, locAut hΩ.conjInvariant ht (locMk Ω z (f a)) = locMk Ω z (f a)) (a : A) :
    t * ((f a : ↥(locLayer Ω z)) : G) * t⁻¹ = ((f a : ↥(locLayer Ω z)) : G) := by
  classical
  have hOc : ∀ b ∈ f.range, b⁻¹ * layerAut hΩ.conjInvariant ht b ∈
      classicalInvolutionOddCore ↥(locLayer Ω z) := by
    rintro _ ⟨a', rfl⟩
    have h2 : locMk Ω z (layerAut hΩ.conjInvariant ht (f a')) = locMk Ω z (f a') := hfix a'
    exact QuotientGroup.eq.mp h2.symm
  have hcop : ∀ x ∈ classicalInvolutionOddCore ↥(locLayer Ω z), ¬ 3 ∣ orderOf x := by
    intro x hx h3
    have h1 : orderOf (⟨x, hx⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) ∣
        Nat.card (classicalInvolutionOddCore ↥(locLayer Ω z)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hO3 (h3.trans h1)
  have key := fixed_of_pow3_of_central (layerAut hΩ.conjInvariant ht).toMonoidHom
    (N := f.range) hpow hP1 hcop hOc
  have := key (f a) ⟨a, rfl⟩
  have h4 := congrArg Subtype.val this
  exact h4

theorem exists_adapted_nodes [Finite G] {K : Subgroup G}
    {c : CCoreR 3 Ω K z} (l : LayerR c) {β : Subgroup G} {t : G} (ht : IsClassicalMember3 β t)
    (hβJ : ∃ W, WeakCT.LinearBlockStandardPair F₃ W β
      ((planeGroup (stdPlane F₃ 3 2)).map l.Θ))
    (htz : t * z * t⁻¹ = z) :
    ∃ g : StatedSp 3 F₃,
      (longBlock F₃ 3 2).range.map (l.Θ.comp (MulAut.conj g).toMonoidHom) =
          (planeGroup (stdPlane F₃ 3 2)).map l.Θ ∧
        (shortBlock F₃ (by decide : (1 : Fin 3) ≠ 2)).range.map
            (l.Θ.comp (MulAut.conj g).toMonoidHom) ≤ Subgroup.centralizer ({t} : Set G) ∧
        (shortBlock F₃ (by decide : (0 : Fin 3) ≠ 1)).range.map
            (l.Θ.comp (MulAut.conj g).toMonoidHom) ≤ Subgroup.centralizer ({t} : Set G) := by
  have h3 := @CFSG.ClassicalInvolution.Q3.Q3V.F4S.f4AdaptFact3
  classical
  have hΩ := c.hΩ
  have hP2 : IsHyperbolicPlane (stdPlane F₃ 3 2) := isHyperbolicPlane_stdPlane 2
  have hJ : (planeGroup (stdPlane F₃ 3 2)).map l.Θ ≤ locLayer Ω z :=
    le_centralizingLayer (l.plane _ hP2).1
  obtain ⟨θ, hθr, hθτ⟩ := Q3TPS.exists_chart3 hΩ.conjInvariant ht hJ htz hβJ
  have hθ : θ.range = (longBlock F₃ 3 2).range.map c.d.ψ := by
    rw [hθr, (l.plane _ hP2).2, planeGroup_stdPlane]
    rfl
  have hnorm := range_normal_of_dictR c.d
  have hτ : ∀ y, locAut hΩ.conjInvariant htz (locAut hΩ.conjInvariant htz y) = y :=
    locAut_locAut hΩ.conjInvariant htz (mul_self_of_isClassicalMember3 ht)
  obtain ⟨g, hg1, hg2, hg3⟩ := h3 c.d.ψ c.d.ker_le hnorm (locAut hΩ.conjInvariant htz) hτ θ hθ hθτ
  have key : ∀ (f₀ : SL(2, F₃) →* StatedSp 3 F₃),
      (∀ x ∈ f₀.range.map (MulAut.conj g).toMonoidHom,
        locAut hΩ.conjInvariant htz (c.d.ψ x) = c.d.ψ x) →
      f₀.range.map (l.Θ.comp (MulAut.conj g).toMonoidHom) ≤
        Subgroup.centralizer ({t} : Set G) := by
    intro f₀ hfix
    let f : SL(2, F₃) →* ↥(locLayer Ω z) :=
      (l.Θ.comp ((MulAut.conj g).toMonoidHom.comp f₀)).codRestrict (locLayer Ω z)
        (fun s => l.mem _)
    have hpow : Pow3 f.range := pow3_range_sl2 card_gf3 f
    have hmk : ∀ s, locMk Ω z (f s) = c.d.ψ (g * f₀ s * g⁻¹) := fun s =>
      DFunLike.congr_fun l.comp_eq (g * f₀ s * g⁻¹)
    have hf : ∀ s, locAut hΩ.conjInvariant htz (locMk Ω z (f s)) = locMk Ω z (f s) := by
      intro s
      rw [hmk]
      exact hfix _ ⟨f₀ s, ⟨s, rfl⟩, rfl⟩
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have h := commutes_of_locAut_fixed3 hΩ c.hP1 c.hO3 htz f hpow hf s
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : t * l.Θ (g * f₀ s * g⁻¹) = l.Θ (g * f₀ s * g⁻¹) * t := mul_inv_eq_iff_eq_mul.mp h
    exact h'.symm
  refine ⟨g, ?_, key _ hg2, key _ hg3⟩
  rw [← Subgroup.map_map, hg1, planeGroup_stdPlane]
  rfl

end CFSG.ClassicalInvolution.Q3.Q3V.F4S

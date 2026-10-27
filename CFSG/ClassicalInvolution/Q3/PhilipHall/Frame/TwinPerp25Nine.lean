module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Defs
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M7

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

section Hyp

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem z_facts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    z ∈ cA S R R' ∧ z * z = 1 ∧ z ≠ 1 := by
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hzS : z ∈ (S : Subgroup G) := h.hRS h.hzR.mem
  have hzC : z ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    have : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.hzR.commute_of_mem hx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.hzR'.commute_of_mem hx).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  exact ⟨⟨hzS, hzC⟩, h.hzR.sq, h.hzR.ne_one⟩

theorem perm_R (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G} (hs : s ∈ (S : Subgroup G))
    {X : Subgroup G} (hX : X = R ∨ X = R') : conjSub s X = R ∨ conjSub s X = R' := by
  have hΩ : HypOmegaMod Ω := hyp.std.setting.stand.hyp
  have hXmem : X ∈ RSet Ω := by
    rcases hX with rfl | rfl
    exacts [hyp.hR.1, hyp.hR'.1]
  have hXS : X ≤ (S : Subgroup G) := by
    rcases hX with rfl | rfl
    exacts [hyp.hR.2.2, hyp.hR'.2.2]
  have hmem : conjSub s X ∈ RSet Ω := Q3.Q3CL.Thompson.conjSub_mem_RSet hΩ hXmem s
  have hle : conjSub s X ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hXS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact hyp.hRS _ hmem hle

theorem conj_mem_sup (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G} (hs : s ∈ (S : Subgroup G))
    {y : G} (hy : y ∈ R ⊔ R') : s * y * s⁻¹ ∈ R ⊔ R' := by
  have h : R ⊔ R' ≤ (R ⊔ R').comap (MulAut.conj s).toMonoidHom := by
    refine sup_le ?_ ?_
    · intro r hr
      rw [Subgroup.mem_comap]
      have hc : s * r * s⁻¹ ∈ conjSub s R := conj_mem_conjSub hr
      rcases perm_R hyp hs (Or.inl rfl : R = R ∨ R = R') with h | h
      · rw [h] at hc
        simpa using Subgroup.mem_sup_left hc
      · rw [h] at hc
        simpa using Subgroup.mem_sup_right hc
    · intro r hr
      rw [Subgroup.mem_comap]
      have hc : s * r * s⁻¹ ∈ conjSub s R' := conj_mem_conjSub hr
      rcases perm_R hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h | h
      · rw [h] at hc
        simpa using Subgroup.mem_sup_left hc
      · rw [h] at hc
        simpa using Subgroup.mem_sup_right hc
  have := h hy
  simpa using this

theorem cA_normal (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {s : G} (hs : s ∈ (S : Subgroup G)) :
    conjSub s (cA S R R') = cA S R R' := by
  have key : ∀ s ∈ (S : Subgroup G), ∀ x ∈ cA S R R', s * x * s⁻¹ ∈ cA S R R' := by
    intro s hs x hx
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hx.1) (Subgroup.inv_mem _ hs),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : s⁻¹ * y * s⁻¹⁻¹ ∈ R ⊔ R' := conj_mem_sup hyp (Subgroup.inv_mem _ hs) hy
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hy'
    calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s⁻¹⁻¹) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * y * s⁻¹⁻¹)) * s⁻¹ := by rw [hc]
      _ = (s * x * s⁻¹) * y := by group
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro h
    have := key s hs _ h
    simpa [mul_assoc] using this
  · intro h
    have := key s⁻¹ (Subgroup.inv_mem _ hs) x h
    simpa [mul_assoc] using this

theorem badElt_of_mem {D : Subgroup G} (hD : D ≤ cA S R R')
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hbad : BadSub z D) {a : G} (ha : a ∈ D) :
    BadElt z a := by
  intro hz
  apply hbad
  have hle : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (by simpa using ha)
  have hzC : z ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd => hyp.hzS d (hD hd).1
  exact T7T.mem_zStarOf_of_le hle hz hzC

theorem notMem_of_badSub {D : Subgroup G} (hD : D ≤ cA S R R')
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hbad : BadSub z D) : z ∉ D := by
  intro hzD
  apply hbad
  have hle : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (by simpa using hzD)
  have hzC : z ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd => hyp.hzS d (hD hd).1
  exact T7T.mem_zStarOf_of_le hle (T7T.mem_zStarOf_centralizer_self z) hzC

end Hyp

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R

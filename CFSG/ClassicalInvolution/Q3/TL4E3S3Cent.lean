module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3Pick
public import CFSG.ClassicalInvolution.Q3.TL4E3Fin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem E3.omegaNbrGen_conj (hc : ConjInvariant Ω) (K : Subgroup G) (g : G) :
    conjSub g (omegaNbrGen Ω K) = omegaNbrGen Ω (conjSub g K) := by
  have key : ∀ (a : G) (K : Subgroup G),
      conjSub a (omegaNbrGen Ω K) ≤ omegaNbrGen Ω (conjSub a K) := by
    intro a K
    show (omegaNbrGen Ω K).map (MulAut.conj a).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_omegaNbrGen (omegaNbr_conj hc hM a)
  refine le_antisymm (key g K) ?_
  have h := conjSub_mono (n := g) (key g⁻¹ (conjSub g K))
  rwa [conjSub_inv_conjSub, conjSub_conjSub_inv] at h

theorem E3.orbGen_conj (hc : ConjInvariant Ω) {K J : Subgroup G} (hK : K ∈ Ω) (g : G) :
    E3.orbGen Ω (conjSub g K) (conjSub g J) = conjSub g (E3.orbGen Ω K J) := by
  have hKg : conjSub g K ∈ Ω := hc g K hK
  have hgen : nbrGen (TC.nbrAdj Ω) (conjSub g K) = conjSub g (nbrGen (TC.nbrAdj Ω) K) := by
    rw [E3.nbrGen_eq_omegaNbrGen hKg, E3.nbrGen_eq_omegaNbrGen hK, E3.omegaNbrGen_conj hc]
  have horb : orbOf (TC.nbrAdj Ω) (conjSub g K) (conjSub g J) =
      conjSub g '' orbOf (TC.nbrAdj Ω) K J := by
    ext M
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [hgen, mem_conjSub_iff] at hl
      refine ⟨conjSub (g⁻¹ * l * g) J, ⟨_, hl, rfl⟩, ?_⟩
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨g * l * g⁻¹, ?_, ?_⟩
      · rw [hgen]
        exact conj_mem_conjSub hl
      · rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    rw [horb] at hM
    obtain ⟨M', hM', rfl⟩ := hM
    exact conjSub_mono (le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) K J) => N) M' hM')
  · show (E3.orbGen Ω K J).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hM' : conjSub g M ∈ orbOf (TC.nbrAdj Ω) (conjSub g K) (conjSub g J) := by
      rw [horb]
      exact ⟨M, hM, rfl⟩
    exact le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) (conjSub g K) (conjSub g J)) => N)
      _ hM'

end Gen

section Quot

variable {G : Type} [Group G]

@[expose] noncomputable def E3.conjQ (H : Subgroup G) (d : G) (hd : conjSub d H = H) :
    MulAut (↥H ⧸ classicalInvolutionOddCore ↥H) :=
  QuotientGroup.congr _ _ (((MulAut.conj d).subgroupMap H).trans (MulEquiv.subgroupCongr hd))
    (E3.map_oddCore_mulEquiv _)

theorem E3.conjQ_mk (H : Subgroup G) (d : G) (hd : conjSub d H = H) (x : ↥H) :
    E3.conjQ H d hd (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (((MulAut.conj d).subgroupMap H).trans (MulEquiv.subgroupCongr hd) x) := rfl

theorem E3.conjQ_val (H : Subgroup G) (d : G) (hd : conjSub d H = H) (x : ↥H) :
    ((((MulAut.conj d).subgroupMap H).trans (MulEquiv.subgroupCongr hd) x : ↥H) : G) =
      d * x * d⁻¹ := rfl

theorem E3.comm_mem_oddCoreOf {H : Subgroup G} {d e : G} (he : e ∈ H)
    (hdx : ∀ x ∈ H, d * x * d⁻¹ ∈ H)
    (h : ∀ x (hx : x ∈ H), QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
      (⟨d * x * d⁻¹, hdx x hx⟩ : ↥H) = QuotientGroup.mk' (classicalInvolutionOddCore ↥H)
        (⟨e * x * e⁻¹, H.mul_mem (H.mul_mem he hx) (H.inv_mem he)⟩ : ↥H)) :
    ∀ x ∈ H, ⁅e⁻¹ * d, x⁆ ∈ oddCoreOf H := by
  intro x hx
  set O := classicalInvolutionOddCore ↥H with hOdef
  have hOn : O.Normal := classicalInvolutionOddCore_normal ↥H
  have h1 := h x hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 := hOn.conj_mem _ (O.inv_mem h1) (⟨x, hx⟩ * (⟨e, he⟩ : ↥H)⁻¹)
  refine ⟨_, h2, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  group

end Quot

end CFSG.ClassicalInvolution.Q3.TL4

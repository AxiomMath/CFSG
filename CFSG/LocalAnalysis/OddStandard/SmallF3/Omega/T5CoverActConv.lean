module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

private theorem coverAct_normalizer {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (h : CoverAct L φ s x) : s ∈ Subgroup.normalizer (L : Set G) := by
  with_unfolding_all exact h.1

private theorem coverAct_apply {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (h : CoverAct L φ s x) {l l' : ↥L} (hl : (l' : G) = s * l * s⁻¹) :
    ((φ l' : omegaGroup hQ) : OGroup Q) = simAct Q x ((φ l : omegaGroup hQ) : OGroup Q) := by
  with_unfolding_all exact h.2 l l' hl

private theorem coverAct_intro {φ : ↥L →* omegaGroup hQ} {s : G} {x : simGroup Q}
    (h1 : s ∈ Subgroup.normalizer (L : Set G))
    (h2 : ∀ l l' : ↥L, (l' : G) = s * l * s⁻¹ →
      ((φ l' : omegaGroup hQ) : OGroup Q) = simAct Q x ((φ l : omegaGroup hQ) : OGroup Q)) :
    CoverAct L φ s x := by
  with_unfolding_all exact ⟨h1, h2⟩

private theorem t5_ffSimOmegaAct_h2_irrel {hQ : Q.Nondegenerate}
    {h2a h2b : 2 ≤ Module.finrank (ZMod 3) V} :
    ffSimOmegaAct hQ h2a = ffSimOmegaAct hQ h2b := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.ext
  intro w
  exact Subtype.ext rfl

private theorem t5_ffSimOmegaAct_injective' {hQ : Q.Nondegenerate}
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Injective (ffSimOmegaAct hQ h2) := by
  have h := ffSimOmegaAct_injective hQ h5
  rwa [← t5_ffSimOmegaAct_h2_irrel (hQ := hQ) (h2a := h2)] at h

theorem t5_coverAct_mul_left {φ : ↥L →* omegaGroup hQ} {b : G} {s : OGroup Q}
    (hb : CoverAct L φ b (orthToSim Q s)) {u : G} (hu : u ∈ L) :
    CoverAct L φ (u * b) (orthToSim Q (((φ ⟨u, hu⟩ : omegaGroup hQ) : OGroup Q) * s)) := by
  refine coverAct_intro
    (Subgroup.mul_mem _ (Subgroup.le_normalizer hu) (coverAct_normalizer hb))
    (fun l l' hl => ?_)
  let l'' : ↥L := ⟨b * (l : G) * b⁻¹,
    (Subgroup.mem_normalizer_iff.mp (coverAct_normalizer hb) (l : G)).mp l.2⟩
  have hl'' : (l'' : G) = b * (l : G) * b⁻¹ := rfl
  have hb2 : ((φ l'' : omegaGroup hQ) : OGroup Q) =
      simAct Q (orthToSim Q s) ((φ l : omegaGroup hQ) : OGroup Q) :=
    coverAct_apply hb rfl
  have hconj : l' = (⟨u, hu⟩ : ↥L) * l'' * (⟨u, hu⟩ : ↥L)⁻¹ := by
    apply Subtype.ext
    show (l' : G) = u * (l'' : G) * u⁻¹
    rw [hl, hl'']
    group
  rw [hconj, map_mul φ, map_mul φ, map_inv φ]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hb2, simAct_orthToSim, simAct_orthToSim]
  group

theorem t5_inducesViaP_of_coverAct {φ : ↥L →* omegaGroup hQ}
    {e₀ : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ}
    (he₀ : ∀ l : ↥L, e₀ (QuotientGroup.mk l) = omegaToProj hQ (φ l)) {s : G} {x : simGroup Q}
    (hx : CoverAct L φ s x) :
    InducesViaP L (Subgroup.center ↥L) hQ e₀ s (QuotientGroup.mk x) := by
  refine ⟨coverAct_normalizer hx, fun l l' hl => ?_⟩
  rw [he₀ l', he₀ l, coe_omegaToProj, coe_omegaToProj, projSimAct_mk, projActAux_toProj]
  exact congrArg (toProj Q) (coverAct_apply hx hl)

theorem t5_sq_mem_pi_of_coverAct {φ : ↥L →* omegaGroup hQ} (h : IsCoverMap L φ) {e : G}
    (he2 : e * e = 1) {g : OGroup Q} (he : CoverAct L φ e (orthToSim Q g)) :
    g * g = 1 ∨ g * g = piOrth Q := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [h.finrank_eq]; norm_num
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by rw [h.finrank_eq]; norm_num
  have hfixL : ∀ l : ↥L, simAct Q (orthToSim Q g) (simAct Q (orthToSim Q g)
      ((φ l : omegaGroup hQ) : OGroup Q)) = ((φ l : omegaGroup hQ) : OGroup Q) := by
    intro l
    let l₁ : ↥L := ⟨e * (l : G) * e⁻¹,
      (Subgroup.mem_normalizer_iff.mp (coverAct_normalizer he) (l : G)).mp l.2⟩
    let l₂ : ↥L := ⟨e * (l₁ : G) * e⁻¹,
      (Subgroup.mem_normalizer_iff.mp (coverAct_normalizer he) (l₁ : G)).mp l₁.2⟩
    have hl₂ : l₂ = l := by
      apply Subtype.ext
      show e * (l₁ : G) * e⁻¹ = (l : G)
      have hl₁ : (l₁ : G) = e * (l : G) * e⁻¹ := rfl
      rw [hl₁]
      calc e * (e * (l : G) * e⁻¹) * e⁻¹ = (e * e) * (l : G) * (e⁻¹ * e⁻¹) := by
            group
        _ = (l : G) := by
            rw [he2, one_mul, inv_eq_of_mul_eq_one_right he2, he2, mul_one]
    have h1 : ((φ l₁ : omegaGroup hQ) : OGroup Q) =
        simAct Q (orthToSim Q g) ((φ l : omegaGroup hQ) : OGroup Q) := coverAct_apply he rfl
    have h2' : ((φ l₂ : omegaGroup hQ) : OGroup Q) =
        simAct Q (orthToSim Q g) ((φ l₁ : omegaGroup hQ) : OGroup Q) := coverAct_apply he rfl
    calc simAct Q (orthToSim Q g) (simAct Q (orthToSim Q g)
          ((φ l : omegaGroup hQ) : OGroup Q))
        = simAct Q (orthToSim Q g) ((φ l₁ : omegaGroup hQ) : OGroup Q) := by rw [← h1]
      _ = ((φ l₂ : omegaGroup hQ) : OGroup Q) := h2'.symm
      _ = ((φ l : omegaGroup hQ) : OGroup Q) := by rw [hl₂]
  have key : ∀ w : OGroup Q, w ∈ omegaGroup hQ →
      simAct Q (orthToSim Q (g * g)) w = w := by
    intro w hw
    obtain ⟨l, hl⟩ := h.surjective ⟨w, hw⟩
    have hw' : simAct Q (orthToSim Q g) (simAct Q (orthToSim Q g) w) = w := by
      have hh := hfixL l
      rw [hl] at hh
      exact hh
    calc simAct Q (orthToSim Q (g * g)) w
        = (simAct Q (orthToSim Q g) * simAct Q (orthToSim Q g)) w := by
          rw [map_mul (orthToSim Q) g g,
            map_mul (simAct Q) (orthToSim Q g) (orthToSim Q g)]
      _ = simAct Q (orthToSim Q g) (simAct Q (orthToSim Q g) w) := by
          rw [MulAut.mul_apply]
      _ = w := hw'
  have hff : ffSimOmegaAct hQ h2 (QuotientGroup.mk (orthToSim Q (g * g))) = 1 :=
    (ffSimOmegaAct_eq_one_iff hQ h2 (orthToSim Q (g * g))).mpr
      (fun t ht => Or.inl (key t ht))
  have hmk : QuotientGroup.mk (orthToSim Q (g * g)) = (1 : ProjSim Q) :=
    t5_ffSimOmegaAct_injective' h5 h2 (by rw [hff, map_one])
  have hmem : orthToSim Q (g * g) ∈ piSim Q :=
    (QuotientGroup.eq_one_iff (N := piSim Q) (orthToSim Q (g * g))).mp hmk
  rcases mem_piSim_iff.mp hmem with h1 | h1
  · left
    exact orthToSim_injective (by rw [h1, map_one])
  · right
    exact orthToSim_injective h1

end CFSG.OddStandard.SmallF3.Omega

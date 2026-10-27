module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAll
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenWire

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace MuTab

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muTabCtx (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) : Ctx p f Ω W :=
  ⟨hP.1, hP.2.1, hP.2.2.1, hW, thompsonKey G Ω hP W hW, hP.2.2.2⟩

noncomputable def mkRep (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K) : Rep Ω W :=
  have h := exists_not_mem_of_mem_D hP.1 hP.2.1 hP.2.2.1 hW hR
  ⟨K, R, h.choose, hK, hR, hRK, h.choose_spec.1, h.choose_spec.2⟩

@[expose] noncomputable def muTabElt (ρ : Rep Ω W) : ↥(muGroup Ω W) :=
  ⟨ρ.img, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D ρ.hR ρ.hr))⟩

omit [Finite G] in
theorem muTabElt_coe (ρ : Rep Ω W) : (muTabElt ρ : NQuot (W ⊔ OCW W)) = piG W ρ.r := rfl

omit [Finite G] in
theorem muTabElt_mem (ρ : Rep Ω W) : muTabElt ρ ∈ muDelta Ω W :=
  ⟨ρ.R, ρ.hR, ρ.r, ρ.hr, ρ.hrW, rfl⟩

omit [Finite G] in
theorem exists_rep_of_mem_muDelta {d : ↥(muGroup Ω W)} (hd : d ∈ muDelta Ω W) :
    ∃ ρ : Rep Ω W, d = muTabElt ρ := by
  obtain ⟨R, hR, r, hr, hrW, hd⟩ := hd
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, Subtype.ext hd⟩

section Ctx

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muTabElt_eq_iff (ρ σ : Rep Ω W) : muTabElt ρ = muTabElt σ ↔ ρ.K = σ.K := by
  have c := muTabCtx hP hW
  constructor
  · intro h
    exact c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (c.img_eq_of_K_eq ρ σ h)

theorem muTab_commute_iff (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K := by
  have c := muTabCtx hP hW
  constructor
  · intro h
    exact c.omega_of_comm ρ σ hne (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (c.comm_of_omega ρ σ h)

theorem muTab_omegaStar (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) : σ.K ∈ omegaStarNbr Ω ρ.K :=
  (mem_omegaStarNbr_of_inf_W hP.1 hP.2.1 hP.2.2.1 hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK).1

end Ctx

section Realize

variable {ι : Type}

theorem exists_rep_of_member_sylow (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (K R : ι → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hR : ∀ i, IsSylow2In (R i) (K i)) (Q : Subgroup G)
    (hQ : IsPGroup 2 ↥Q) (hRQ : ∀ i, R i ≤ Q) :
    ∃ g : G, ∀ i, ∃ ρ : Rep Ω W, ρ.K = conjSub g (K i) := by
  obtain ⟨S₀, hS₀⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_DSet hP.1 hP.2.1 hP.2.2.1 hW S₀
  refine ⟨g, fun i => ?_⟩
  have hRi : R i ≤ (S₀ : Subgroup G) := (hRQ i).trans hS₀
  have hD : conjSub g (R i) ∈ DSet Ω W :=
    hg (R i) (mem_RSet_of_isSylow2In (hK i) (hR i)) hRi
  exact ⟨mkRep hP hW (hP.2.2.1.conjInvariant g (K i) (hK i)) hD ((hR i).conj g), rfl⟩

theorem exists_rep_of_member_U (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (K U : ι → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hU : ∀ i, U i ∈ USet Ω) (hUK : ∀ i, U i ≤ K i) (Q : Subgroup G)
    (hQ : IsPGroup 2 ↥Q) (hUQ : ∀ i, U i ≤ Q) :
    ∃ g : G, ∀ i, ∃ ρ : Rep Ω W, ρ.K = conjSub g (K i) := by
  obtain ⟨S₀, hS₀⟩ := hQ.exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S
  refine ⟨g, fun i => ?_⟩
  have hUi : conjSub g (U i) ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) ((hUQ i).trans hS₀)
    rwa [hg] at this
  obtain ⟨T, hT, hTK⟩ := exists_sylow_mem_DSet hP.1 hP.2.1 hP.2.2.1 hW hWS
    (hP.2.2.1.conjInvariant g (K i) (hK i)) (USet.conj hP.2.2.1.conjInvariant (hU i) g)
    (conjSub_mono (hUK i)) hUi
  exact ⟨mkRep hP hW (hP.2.2.1.conjInvariant g (K i) (hK i)) hT hTK, rfl⟩

end Realize

end MuTab

end CFSG.ClassicalInvolution.Asc77

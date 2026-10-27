module

public import CFSG.ClassicalInvolution.Q3.Q3CLSeven2
public import CFSG.ClassicalInvolution.Asc77.AscMuTabAbel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6.Mu

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt exists_sylow2In)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

section Ctx

variable (c : Q3CL.Thompson.Ctx Ω W)

include c

theorem ctx_img_eq_of_K_eq (ρ σ : Rep Ω W) (h : ρ.K = σ.K) : ρ.img = σ.img := by
  have hle : σ.R ≤ ρ.R ⊔ W ⊔ OCW W :=
    c.hkey ρ.R ρ.hR σ.R σ.hR ρ.K ρ.hK ρ.hRK.1 (h ▸ σ.hRK.1)
  exact (Q3CL.Thompson.piG_eq_of_le_sup c.hΩ c.hW ρ.hR σ.hR hle ρ.hr σ.hr ρ.hrW σ.hrW).symm

theorem ctx_omega_of_comm (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K)
    (hcomm : ρ.img * σ.img = σ.img * ρ.img) : σ.K ∈ omegaNbr Ω ρ.K := by
  by_contra hnot
  exact c.noncomm ρ σ hne hnot hcomm

theorem ctx_comm_of_omega (ρ σ : Rep Ω W) (hnbr : σ.K ∈ omegaNbr Ω ρ.K) :
    ρ.img * σ.img = σ.img * ρ.img :=
  Q3CL.Thompson.piG_comm_of_mem_omegaNbr Sec6Gen.l6_2Gen c.hΩ c.hW c.hkey ρ.hK σ.hK
    hnbr.2.1.symm ρ.hR σ.hR ρ.hRK σ.hRK hnbr ρ.hr σ.hr ρ.hrW

end Ctx

theorem exists_conj_mem_DSet (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) (S : Sylow 2 G) :
    ∃ g : G, ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → conjSub g R ∈ DSet Ω W := by
  obtain ⟨S', hWS'⟩ := exists_sylow_ge_of_mem_WSet hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S'
  refine ⟨g, fun R hR hRS => ?_⟩
  refine Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS' (RSet.conj hΩ.conjInvariant hR g) ?_
  rw [← hg]
  exact conjSub_mono hRS

section Realize

variable {ι : Type}

theorem exists_rep_of_member_sylow (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    (K R : ι → Subgroup G) (hK : ∀ i, K i ∈ Ω) (hR : ∀ i, IsSylow2In (R i) (K i))
    (Q : Subgroup G) (hQ : IsPGroup 2 ↥Q) (hRQ : ∀ i, R i ≤ Q) :
    ∃ g : G, ∀ i, ∃ ρ : Rep Ω W, ρ.K = conjSub g (K i) := by
  obtain ⟨S₀, hS₀⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_DSet hP.hyp hW S₀
  refine ⟨g, fun i => ?_⟩
  have hRi : R i ≤ (S₀ : Subgroup G) := (hRQ i).trans hS₀
  have hD : conjSub g (R i) ∈ DSet Ω W :=
    hg (R i) (mem_RSet_of_isSylow2In (hK i) (hR i)) hRi
  exact ⟨Q3CL.T8.mkRep hP hW (hP.hyp.conjInvariant g (K i) (hK i)) hD ((hR i).conj g), rfl⟩

end Realize

theorem exists_rep (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ g : G, ∃ ρ : Rep Ω W, ρ.K = conjSub g K := by
  obtain ⟨R, hR⟩ := exists_sylow2In K
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow (ι := Unit) hP hW (fun _ => K) (fun _ => R)
    (fun _ => hK) (fun _ => hR) R hR.2.1 (fun _ => le_rfl)
  obtain ⟨ρ, hρ⟩ := hg ()
  exact ⟨g, ρ, hρ⟩

section Tab

variable (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem muTabElt_eq_iff (ρ σ : Rep Ω W) : muTabElt ρ = muTabElt σ ↔ ρ.K = σ.K := by
  have c := Q3CL.T8.ctxOf hP hW
  constructor
  · intro h
    exact c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (ctx_img_eq_of_K_eq c ρ σ h)

theorem muTab_commute_iff (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    muTabElt ρ * muTabElt σ = muTabElt σ * muTabElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K := by
  have c := Q3CL.T8.ctxOf hP hW
  constructor
  · intro h
    exact ctx_omega_of_comm c ρ σ hne (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (ctx_comm_of_omega c ρ σ h)

theorem muTab_omegaStar (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) : σ.K ∈ omegaStarNbr Ω ρ.K :=
  (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hP.hyp hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK).1

end Tab

theorem muDelta_mul_self (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {a : ↥(muGroup Ω W)}
    (ha : a ∈ muDelta Ω W) : a * a = 1 := by
  obtain ⟨R, hR, r, hr, -, hra⟩ := ha
  apply Subtype.ext
  show (a : NQuot (W ⊔ OCW W)) * a = 1
  rw [hra]
  exact Q3CL.Thompson.piG_mul_self_of_mem_D hΩ hW hR hr

theorem muDelta_conj_mem (hΩ : HypOmegaGen Ω) {a : ↥(muGroup Ω W)} (ha : a ∈ muDelta Ω W)
    (g : ↥(muGroup Ω W)) : g * a * g⁻¹ ∈ muDelta Ω W := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨m, hm, hgm⟩ := mem_muGroup_iff.mp g.2
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
  refine ⟨conjSub m R, Q3CL.Thompson.conjSub_mem_D hΩ hR hmN, m * r * m⁻¹, conj_mem_conjSub hr,
    ?_, ?_⟩
  · rw [mem_normalizer_iff_of_mem hmN]
    exact hrW
  · show (g : NQuot (W ⊔ OCW W)) * a * (g : NQuot (W ⊔ OCW W))⁻¹ = piG W (m * r * m⁻¹)
    rw [hra, hgm, piG_mul (Subgroup.mul_mem _ hmN (hR.2 hr)) (Subgroup.inv_mem _ hmN),
      piG_mul hmN (hR.2 hr), piG_inv hmN]

end CFSG.ClassicalInvolution.Q3.Q3T6.Mu

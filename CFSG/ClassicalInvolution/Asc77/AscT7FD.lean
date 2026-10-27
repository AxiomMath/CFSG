module

public import CFSG.ClassicalInvolution.Asc77.AscT7FC
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem exists_mem_MGrp_piG_eq (g : ↥(muGroup Ω W)) :
    ∃ m ∈ MGrp Ω W, (g : NQuot (W ⊔ OCW W)) = piG W m := by
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  set L : Set G := {r | ∃ R ∈ DSet Ω W, r ∈ R} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro r ⟨R, hR, hr⟩
    exact hR.2 hr
  have hmem : g ∈ Subgroup.closure (muDelta Ω W) := by
    rw [hTT.closure_eq_top]
    trivial
  have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hmem
  rw [MonoidHom.map_closure] at h1
  have hq' : (g : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨q, ⟨R, hR, r, hr, hrW, hq⟩, rfl⟩
    exact ⟨r, ⟨R, hR, hr⟩, hq.symm⟩
  obtain ⟨m, hm, hmg⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  refine ⟨m, ?_, hmg.symm⟩
  have hcl : Subgroup.closure L ≤ MGrp Ω W := by
    rw [Subgroup.closure_le]
    rintro r ⟨R, hR, hr⟩
    exact le_MGrp_of_mem_D hR hr
  exact hcl hm

theorem exists_conj_of_rep (hnc : ¬ DbarConnected Ω W) (ρ σ : Rep Ω W) :
    ∃ m ∈ MGrp Ω W, conjSub m ρ.K = σ.K := by
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ :=
    exists_not_conn_of_not_connected c.hp c.hq c.hΩ c.hW hnc
  have hcls := hTT.exists_conj_of_not_conn hd₀ ha₀ hn₀
  obtain ⟨g₁, hg₁⟩ := hcls _ (T7D.imgQ_mem ρ)
  obtain ⟨g₂, hg₂⟩ := hcls _ (T7D.imgQ_mem σ)
  have hy : T7D.imgQ σ = (g₂ * g₁⁻¹) * T7D.imgQ ρ * (g₂ * g₁⁻¹)⁻¹ := by
    rw [hg₁, hg₂]
    group
  obtain ⟨m, hm, hmg⟩ := c.exists_mem_MGrp_piG_eq (g₂ * g₁⁻¹)
  refine ⟨m, hm, ?_⟩
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_le_normalizer Ω W hm
  have himg : (T7D.conjRep c.hΩ hmN ρ).img = σ.img := by
    rw [T7D.conjRep_img, ← hmg]
    exact (congrArg Subtype.val hy).symm
  exact c.K_eq_of_img_eq (T7D.conjRep c.hΩ hmN ρ) σ himg

theorem exists_conj_reps_of_mem_omegaStarNbr {K₁ J₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (hJ₁ : J₁ ∈ omegaStarNbr Ω K₁) :
    ∃ g : G, ∃ ρ σ : Rep Ω W, ρ.K = conjSub g K₁ ∧ σ.K = conjSub g J₁ := by
  obtain ⟨hJ₁Ω, -, U, hU, hUJ₁, hUN⟩ := hJ₁
  have hU2 : IsPGroup 2 U := c.hΩ.isPGroup_of_mem_USet c.hp hU
  obtain ⟨R, hRK, hRU⟩ := T3.exists_sylow_normalized hU2 hUN
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S₁, hS₁⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet c.hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S
  have hUS : conjSub g U ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_left.trans hS₁)
    rwa [hg] at this
  have hRS : conjSub g R ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_right.trans hS₁)
    rwa [hg] at this
  have hK' : conjSub g K₁ ∈ Ω := c.hΩ.conjInvariant g K₁ hK₁
  have hJ' : conjSub g J₁ ∈ Ω := c.hΩ.conjInvariant g J₁ hJ₁Ω
  have hR'K' : IsSylow2In (conjSub g R) (conjSub g K₁) := hRK.conj g
  have hR'D : conjSub g R ∈ DSet Ω W :=
    mem_DSet_of_le_sylow c.hp c.hq c.hΩ c.hW hWS (mem_RSet_of_isSylow2In hK' hR'K') hRS
  obtain ⟨T, hTD, hTJ⟩ := exists_sylow_mem_DSet c.hp c.hq c.hΩ c.hW hWS hJ'
    (USet.conj c.hΩ.conjInvariant hU g) (conjSub_mono hUJ₁) hUS
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep c.hp c.hq c.hΩ c.hW hK' hR'K' hR'D
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep c.hp c.hq c.hΩ c.hW hJ' hTJ hTD
  exact ⟨g, ρ, σ, hρK, hσK⟩

end Ctx

end Thompson

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.exists_mem_conj_of_dstarComp (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {H : Subgroup G} (hM : MGrp Ω W ≤ H)
    (hN : Subgroup.normalizer (K : Set G) ≤ H) :
    ∀ L ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = L := by
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hK : K ∈ Ω := hst.mem
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ, ρ', hρ, -, -⟩ := h.exists_reps
  have hA : ∀ J₁ ∈ omegaStarNbr Ω K, ∃ x ∈ H, conjSub x K = J₁ := by
    intro J₁ hJ₁
    obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK hJ₁
    obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hnc ρ ρ₁
    obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hnc ρ σ₁
    rw [hρ, hρ₁] at hm₁K
    rw [hρ, hσ₁] at hm₂K
    have hg' : conjSub (m₁⁻¹ * g) K = K := by
      rw [conjSub_mul, ← hm₁K, conjSub_inv_conjSub]
    have hg'N : m₁⁻¹ * g ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hg'
    refine ⟨(m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂), H.mul_mem (H.inv_mem (hN hg'N))
      (H.mul_mem (H.inv_mem (hM hm₁)) (hM hm₂)), ?_⟩
    have e : (m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂) = g⁻¹ * m₂ := by group
    rw [e, conjSub_mul, hm₂K, conjSub_inv_conjSub]
  intro L hL
  have hL' : Relation.ReflTransGen (dstarAdj Ω) K L := hL
  clear hL
  induction hL' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail b c' _ hbc ih =>
    obtain ⟨x, hxH, hx⟩ := ih
    have hbΩ : b ∈ Ω := hx ▸ hΩ.conjInvariant x K hK
    have hc'Ω : c' ∈ Ω := hbc.1
    have hnbr : c' ∈ omegaStarNbr Ω b := by
      rcases hbc.2 with h1 | h1
      · exact h1
      · exact T3.omegaStarNbr_symm (l6_2 p f) hp hq hΩ hc'Ω hbΩ h1
    have h2 := omegaStarNbr_conj hΩ.conjInvariant hnbr x⁻¹
    rw [← hx, conjSub_inv_conjSub] at h2
    obtain ⟨y, hyH, hy⟩ := hA _ h2
    refine ⟨x * y, H.mul_mem hxH hyH, ?_⟩
    rw [conjSub_mul, hy, conjSub_conjSub_inv]

theorem Hyp21.not_rLayer_le_sigmaGen (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K := by
  intro hD
  have hst := h.std.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hK : K ∈ Ω := hst.mem
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  obtain ⟨ρ, ρ', hρ, -, -⟩ := h.exists_reps
  have hMN : MGrp Ω W ≤ sigmaNorm Ω K :=
    (h.mGrp_le_rLayer_tz hne).trans (hD.trans (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK))
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := exists_boundary_of_dComp_ne hp hq hΩ hK hne
  have hK₁Ω : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁Ω hJ₁
  obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hnc ρ ρ₁
  obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hnc ρ σ₁
  rw [hρ, hρ₁] at hm₁K
  rw [hρ, hσ₁] at hm₂K
  have h1 : conjSub g K₁ ∈ dComp Ω K := by
    rw [← hm₁K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₁)
  have h2 : conjSub g J₁ ∈ dComp Ω K := by
    rw [← hm₂K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₂)
  have hgN : g ∈ sigmaNorm Ω K :=
    T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hK₁d h1
  exact hJ₁n ((hgN J₁).mpr h2)

theorem dComp_eq_dstarComp_of_rLayer_le (h : Hyp21 p f Ω K K' z u J t W)
    (hD : rLayer Ω (t * z) ≤ sigmaGen Ω K) : dComp Ω K = dstarComp Ω K := by
  by_contra hne
  exact h.not_rLayer_le_sigmaGen hne hD

end Frame

end CFSG.ClassicalInvolution.Asc77

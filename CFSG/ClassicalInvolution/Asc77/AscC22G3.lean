module

public import CFSG.ClassicalInvolution.Asc77.AscC22G2
public import CFSG.ClassicalInvolution.Asc77.AscC22G1
public import CFSG.ClassicalInvolution.Asc77.AscT7JHyp51u
public import CFSG.ClassicalInvolution.Asc77.AscT7V1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace C22G

set_option linter.unusedSectionVars false

section Setting

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem exists_conj_of_far (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) {J : Subgroup G} (hJ : J ∈ Ω) (hJt : J ∉ twinSet Ω K)
    {w : G} (hw : IsUniqueInvolution J w) (hwW : w ∈ W) :
    ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have c : Ctx p f Ω W := T7D.ctx_of_stand hs.stand hW
  obtain ⟨ρ₀, hρ₀⟩ := c.exists_rep_of_involution_mem hK hz hzW
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hK' hz' hzW
  obtain ⟨σ, hσ⟩ := c.exists_rep_of_involution_mem hJ hw hwW
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have hJK : J ≠ K := fun h => hJt (h ▸ hKtw)
  have hJK' : J ≠ K' := fun h => hJt (h ▸ hs.hK')
  have hJnot : J ∉ omegaNbr Ω K := by
    intro h
    have h1 : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h
    rw [hs.perp] at h1
    exact hJt h1
  have hKnot : K ∉ omegaNbr Ω J := fun h =>
    hJnot (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hJ hK h)
  have hz₀ : IsUniqueInvolution ρ₀.K z := hρ₀ ▸ hz
  have hz₁ : IsUniqueInvolution ρ₁.K z := hρ₁ ▸ hz'
  have hw' : IsUniqueInvolution σ.K w := hσ ▸ hw
  have hσ₀ : σ.K ≠ ρ₀.K := by rw [hσ, hρ₀]; exact hJK
  have hσ₁ : σ.K ≠ ρ₁.K := by rw [hσ, hρ₁]; exact hJK'
  have hn₀ : ρ₀.K ∉ omegaNbr Ω σ.K := by rw [hσ, hρ₀]; exact hKnot
  have hn₀' : σ.K ∉ omegaNbr Ω ρ₀.K := by rw [hσ, hρ₀]; exact hJnot
  obtain ⟨g₀, hg₀, ho₀⟩ := exists_orderOf_four_mem_inf_W c ρ₀
  obtain ⟨g₁, hg₁, ho₁⟩ := exists_orderOf_four_mem_inf_W c ρ₁
  obtain ⟨g₁', hg₁', ho₁', hRC⟩ :=
    exists_centralized_pair c ρ₀ ρ₁ σ hz₀ hz₁ hw' hσ₀ hσ₁ hn₀ hg₀ ho₀ hg₁ ho₁
  have hg₀K : g₀ ∈ K := hρ₀ ▸ hg₀.1
  have hg₁K' : g₁' ∈ K' := hρ₁ ▸ hg₁'.1
  have hcomm : g₀ * g₁' = g₁' * g₀ := c.comm_W g₀ hg₀.2 g₁' hg₁'.2
  have hKK' : K ≤ trivialOnQuot K' := T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz hz'
  have hK'K : K' ≤ trivialOnQuot K := T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c₁, hc₁, hconj⟩ := T7V.exists_conj_pair hp hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K
    hg₀K hg₁K' hs.hu₁.1 hs.hu₂.1 ho₀ ho₁' hs.hu₁.2 hs.hu₂.2 hcomm hs.comm₁₂
  have hKA : K ≤ genGroup Ω K (u₁ * u₂) := le_genGroup_of_mem_twinSet hKtw
  have hK'A : K' ≤ genGroup Ω K (u₁ * u₂) := le_genGroup_of_mem_twinSet hs.hK'
  have hc₁A : c₁ ∈ genGroup Ω K (u₁ * u₂) := (sup_le hKA hK'A) hc₁
  have hLayer : rLayer Ω (g₀ * g₁') ≤ genGroup Ω K (u₁ * u₂) :=
    rLayer_le_of_conj hΩ.conjInvariant hc₁A hconj (rLayer_le_genGroup K (u₁ * u₂))
  have hσR : σ.R ≤ rLayer Ω (g₀ * g₁') :=
    le_rLayer_of_le_centralizer (mem_RSet_of_isSylow2In σ.hK σ.hRK) hRC
  have hσrA : σ.r ∈ genGroup Ω K (u₁ * u₂) := hLayer (hσR σ.hr)
  have hρrA : ρ₀.r ∈ genGroup Ω K (u₁ * u₂) := by
    have : ρ₀.r ∈ K := hρ₀ ▸ ρ₀.hRK.1 ρ₀.hr
    exact hKA this
  refine ⟨ρ₀.r * σ.r, (genGroup Ω K (u₁ * u₂)).mul_mem hρrA hσrA, ?_⟩
  have hτz : σ.r * z * σ.r⁻¹ = w * z := c.conj_involution σ ρ₀ hσ₀ hn₀ hw' hz₀
  have hτ' : ρ₀.r * w * ρ₀.r⁻¹ = z * w :=
    c.conj_involution ρ₀ σ (Ne.symm hσ₀) hn₀' hz₀ hw'
  have hr₀z : ρ₀.r * z * ρ₀.r⁻¹ = z := by
    have hn : conjSub ρ₀.r ρ₀.K = ρ₀.K := conjSub_eq_self_of_mem (ρ₀.hRK.1 ρ₀.hr)
    exact hz₀.conj_eq hn
  have hzw : z * w = w * z := c.comm_W z hzW w hwW
  have e : (ρ₀.r * σ.r) * z * (ρ₀.r * σ.r)⁻¹ = ρ₀.r * (σ.r * z * σ.r⁻¹) * ρ₀.r⁻¹ := by group
  rw [e, hτz]
  calc ρ₀.r * (w * z) * ρ₀.r⁻¹ = (ρ₀.r * w * ρ₀.r⁻¹) * (ρ₀.r * z * ρ₀.r⁻¹) := by group
    _ = (z * w) * z := by rw [hτ', hr₀z]
    _ = w := by rw [hzw, mul_assoc, hz.sq, mul_one]

end Setting

end C22G

end CFSG.ClassicalInvolution.Asc77

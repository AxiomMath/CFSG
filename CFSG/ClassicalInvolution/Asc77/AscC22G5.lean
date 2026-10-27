module

public import CFSG.ClassicalInvolution.Asc77.AscC22G4
public import CFSG.ClassicalInvolution.Asc77.AscS22C
public import CFSG.ClassicalInvolution.Asc77.AscT7FI
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma

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


theorem hyp22_of_setting {L L' M : Subgroup G} {x y w z' : G}
    (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) (hs : Hyp22Setting p f Ω L L' M z' x y w) :
    Hyp22 p f Ω L L' M z' x y w where
  std := ⟨hs.stand, h.std.disconnected, hs.hz, hs.hK', hs.hne, h.std.cex⟩
  perp := hs.perp
  hK₃ := hs.hK₃
  hK₃K := hs.hK₃K
  hK₃K' := hs.hK₃K'
  hu₁ := hs.hu₁
  hu₂ := hs.hu₂
  hu₃ := hs.hu₃
  hB := hs.hB

theorem exists_third_twin (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (L L' : Subgroup G) :
    ∃ M ∈ twinSet Ω K, M ≠ L ∧ M ≠ L' := by
  by_contra hcon
  have hmem : ∀ M ∈ twinSet Ω K, M = L ∨ M = L' := by
    intro M hM
    by_cases h : M = L
    · exact Or.inl h
    · by_cases h' : M = L'
      · exact Or.inr h'
      · exact absurd ⟨M, hM, h, h'⟩ hcon
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hs.stand.mem hs.hz
  have hKK' : K' ≠ K := hs.hne
  have hKK₃ : K₃ ≠ K := hs.hK₃K
  have hK'K₃ : K₃ ≠ K' := hs.hK₃K'
  rcases hmem K hKtw with h1 | h1 <;> rcases hmem K' hs.hK' with h2 | h2 <;>
    rcases hmem K₃ hs.hK₃ with h3 | h3 <;>
    first
    | exact hKK' (h2.trans h1.symm)
    | exact hKK₃ (h3.trans h1.symm)
    | exact hK'K₃ (h3.trans h2.symm)

theorem exists_sylow_third (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {L L' M : Subgroup G}
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hM : M ∈ twinSet Ω K) (hML : M ≠ L)
    (hML' : M ≠ L') {R₁ R₂ : Subgroup G} (h₁ : IsSylow2In R₁ L) (h₂ : IsSylow2In R₂ L')
    (c₁₂ : Commutes R₁ R₂) :
    ∃ R₃ : Subgroup G, IsSylow2In R₃ M ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hzL := isUniqueInvolution_of_mem_twinSet hz hL
  have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
  have hzM := isUniqueInvolution_of_mem_twinSet hz hM
  have nL : L ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hL.1 hM.1 (Ne.symm hML) hzL hzM
  have nL' : L' ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hL'.1 hM.1 (Ne.symm hML') hzL' hzM
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h₁.2.1.to_sup_of_normal_right' h₂.2.1 (T7A.le_normalizer_of_commutes c₁₂.symm)
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (M : Set G) :=
    sup_le (h₁.1.trans nL) (h₂.1.trans nL')
  obtain ⟨R₃, h₃, hQ⟩ := exists_isPGroup_sup_sylow hP12 hPN
  refine ⟨R₃, h₃, ?_, ?_⟩
  · exact hΩ.commutes_of_twin_of_isPGroup hL.1 hM.1 (Ne.symm hML) hzL hzM h₁.1 h₃.1
      (hQ.to_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  · exact hΩ.commutes_of_twin_of_isPGroup hL'.1 hM.1 (Ne.symm hML') hzL' hzM h₂.1 h₃.1
      (hQ.to_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right))

end Setting

section Statement

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C22_layerStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ J ∈ tqMembers Ω (u₁ * u₂), J ∈ dstarComp Ω K

variable {p f}

theorem c22_dstarConn_of_layerStar (hE : ThmEWithSylow p f) (hLay : C22_layerStar p f) :
    C22_dstarConn p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp
  have hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ := hyp.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hz_le : Subgroup.centralizer ({z} : Set G) ≤ sigmaStarNorm Ω K := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
        _ = z := by group
    have hLt : conjSub c K ∈ twinSet Ω K := ⟨hΩ.conjInvariant c K hK, z, hz, hcz ▸ hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (AscE186.mem_dstarComp_of_twin hp hΩ hK hLt)
  have hnon : ∀ L ∈ twinSet Ω K, ∀ J ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution J z' →
      z' ≠ z → Subgroup.centralizer ({z'} : Set G) ≤ sigmaStarNorm Ω K ∧
        Subgroup.centralizer ({z * z'} : Set G) ≤ sigmaStarNorm Ω K := by
    intro L hL J hJ z' hz' hzz
    exfalso
    have h1 : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
    rw [T7S22.perp_of_twin hs hL, twinSet_eq_of_mem_twinSet hz hL] at h1
    obtain ⟨-, z₀, hz₀K, hz₀J⟩ := h1
    exact hzz ((hz₀J.eq hz').symm.trans (hz.eq hz₀K).symm)
  have htw : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          Subgroup.centralizer ({x * y} : Set G) ≤ sigmaStarNorm Ω K := by
    intro L hL L' hL' hne R₁ R₂ h₁ h₂ c₁₂ x hx y hy ox oy c hc
    obtain ⟨M, hM, hML, hML'⟩ := exists_third_twin hs L L'
    obtain ⟨R₃, h₃, c₁₃, c₂₃⟩ := exists_sylow_third hs hL hL' hM hML hML' h₁ h₂ c₁₂
    obtain ⟨u₃', hu₃', ou₃⟩ :=
      hΩ.exists_orderOf_eq_four_of_mem_RSet hp (mem_RSet_of_isSylow2In hM.1 h₃)
    have hzL := isUniqueInvolution_of_mem_twinSet hz hL
    have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
    have hzM := isUniqueInvolution_of_mem_twinSet hz hM
    have hL'L : L' ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet hz hL]; exact hL'
    have hML₀ : M ∈ twinSet Ω L := by rw [twinSet_eq_of_mem_twinSet hz hL]; exact hM
    have hs' : Hyp22Setting p f Ω L L' M z x y u₃' :=
      S22.hyp22Setting_of_sylows (hst.of_mem hL.1) hzL hL'L hne (T7S22.perp_of_twin hs hL) hML₀ hML
        hML' h₁ h₂ h₃ c₁₂ c₁₃ c₂₃ hx hy hu₃' ox oy ou₃
    have hxM : x ∈ trivialOnQuot M :=
      T7J.twin_le_trivialOnQuot hΩ hL.1 hM.1 (Ne.symm hML) hzL hzM (h₁.1 hx)
    have hyM : y ∈ trivialOnQuot M :=
      T7J.twin_le_trivialOnQuot hΩ hL'.1 hM.1 (Ne.symm hML') hzL' hzM (h₂.1 hy)
    have hMt : M ∈ tqMembers Ω (x * y) := ⟨hM.1, Subgroup.mul_mem _ hxM hyM⟩
    have hJt : conjSub c M ∈ tqMembers Ω (x * y) :=
      conjSub_mem_tqMembers hΩ.conjInvariant hc hMt
    have hJL : conjSub c M ∈ dstarComp Ω L :=
      hLay G Ω L L' M z x y u₃' (hyp22_of_setting hyp hs') _ hJt
    have hLK : dstarComp Ω L = dstarComp Ω K :=
      T7A.dstarComp_eq_of_mem hK (AscE186.mem_dstarComp_of_twin hp hΩ hK hL)
    rw [hLK] at hJL
    have hKtw : conjSub c K ∈ twinSet Ω (conjSub c M) :=
      ⟨hΩ.conjInvariant c K hK, c * z * c⁻¹, hzM.conj c, hz.conj c⟩
    have hKJ : conjSub c K ∈ dstarComp Ω (conjSub c M) :=
      AscE186.mem_dstarComp_of_twin hp hΩ hJt.1 hKtw
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hJL.trans hKJ)
  have hstd : StdCent Ω K (sigmaStarNorm Ω K) z := ⟨hz_le, hnon, htw⟩
  have htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ sigmaStarNorm Ω K, conjSub h K = J := by
    intro J hJ
    obtain ⟨g, hg⟩ := hst.trans J (T3.mem_dstarComp_symm hK hJ).1
    exact ⟨g, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK (hg ▸ hJ), hg⟩
  have htop : sigmaStarNorm Ω K = ⊤ := thmE_apply hE hst hz hs.hK' hs.hne hstd htrans
  refine T3.dstarConnected_of_pivot hK fun B hB => ?_
  obtain ⟨g, hg⟩ := hst.trans B hB
  have hgH : g ∈ sigmaStarNorm Ω K := htop ▸ Subgroup.mem_top g
  have h1 := (mem_sigmaStarNorm_iff.mp hgH K).mp Relation.ReflTransGen.refl
  rwa [hg] at h1

end Statement


end C22G

end CFSG.ClassicalInvolution.Asc77

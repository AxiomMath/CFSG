module

public import CFSG.ClassicalInvolution.Asc77.AscC22G3
public import CFSG.ClassicalInvolution.Asc77.AscT7JFrame

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


theorem exists_conj_of_mem_dstarComp (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ J ∈ dstarComp Ω K, ∃ w : G, IsUniqueInvolution J w ∧
      ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have key : ∀ J : Subgroup G, Relation.ReflTransGen (dstarAdj Ω) K J →
      ∃ w : G, IsUniqueInvolution J w ∧
        ∃ y ∈ genGroup Ω K (u₁ * u₂), y * z * y⁻¹ = w := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨z, hz, 1, (genGroup Ω K (u₁ * u₂)).one_mem, by group⟩
    | @tail b c hpre hstep ih =>
      obtain ⟨wb, hwb, y, hy, hyz⟩ := ih
      have hbΩ : b ∈ Ω := (T3.mem_dstarComp_symm hK hpre).1
      obtain ⟨hcΩ, hor⟩ := hstep
      have hcb : c ∈ omegaStarNbr Ω b := by
        rcases hor with h | h
        · exact h
        · exact T3.omegaStarNbr_symm (l6_2 p f) hp hq hΩ hcΩ hbΩ h
      have hM : conjSub y⁻¹ b ∈ twinSet Ω K :=
        conjSub_mem_twinSet hΩ.conjInvariant hz hbΩ hwb hyz
      have hMΩ : conjSub y⁻¹ b ∈ Ω := hM.1
      have hzM : IsUniqueInvolution (conjSub y⁻¹ b) z := isUniqueInvolution_of_mem_twinSet hz hM
      have hJ'' : conjSub y⁻¹ c ∈ omegaStarNbr Ω (conjSub y⁻¹ b) :=
        omegaStarNbr_conj hΩ.conjInvariant hcb y⁻¹
      have hJ''Ω : conjSub y⁻¹ c ∈ Ω := hΩ.conjInvariant y⁻¹ c hcΩ
      obtain ⟨w', hw'⟩ := hΩ.exists_uniqueInvolution hp hq hcΩ
      have hw'' : IsUniqueInvolution (conjSub y⁻¹ c) (y⁻¹ * w' * y⁻¹⁻¹) := hw'.conj y⁻¹
      refine ⟨w', hw', ?_⟩
      by_cases hJt : conjSub y⁻¹ c ∈ twinSet Ω K
      · have h1 := isUniqueInvolution_of_mem_twinSet hz hJt
        have h2 : z = y⁻¹ * w' * y⁻¹⁻¹ := h1.eq hw''
        exact ⟨y, hy, by rw [h2]; group⟩
      · obtain ⟨W₁, hW₁, R, hRD, T, hTD, hRM, hTJ⟩ :=
          exists_W_of_mem_omegaStarNbr hp hq hΩ hMΩ hJ''
        have hzW : z ∈ W₁ := (uniqueInvolution_mem_W hp hq hΩ hW₁ hMΩ hRD hRM hzM).2
        have hwW : y⁻¹ * w' * y⁻¹⁻¹ ∈ W₁ :=
          (uniqueInvolution_mem_W hp hq hΩ hW₁ hJ''Ω hTD hTJ hw'').2
        obtain ⟨y'', hy'', hy''z⟩ := exists_conj_of_far hs hW₁ hzW hJ''Ω hJt hw'' hwW
        refine ⟨y * y'', (genGroup Ω K (u₁ * u₂)).mul_mem hy hy'', ?_⟩
        calc y * y'' * z * (y * y'')⁻¹ = y * (y'' * z * y''⁻¹) * y⁻¹ := by group
          _ = y * (y⁻¹ * w' * y⁻¹⁻¹) * y⁻¹ := by rw [hy''z]
          _ = w' := by group
  intro J hJ
  exact key J hJ

theorem le_genGroup_of_mem_dstarComp (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) {J : Subgroup G}
    (hJ : J ∈ dstarComp Ω K) : J ≤ genGroup Ω K (u₁ * u₂) := by
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := (T3.mem_dstarComp_symm hK hJ).1
  obtain ⟨w, hw, y, hy, hyw⟩ := exists_conj_of_mem_dstarComp hs J hJ
  exact le_genGroup_of_conj hs.stand.hyp.conjInvariant hs.hz hJΩ hw hy hyw

theorem genGroup_eq_top_of_dstarConnected (hs : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hconn : T3.DStarConnected Ω) : genGroup Ω K (u₁ * u₂) = ⊤ := by
  have hK : K ∈ Ω := hs.stand.mem
  rw [eq_top_iff]
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := hs.stand.gen
  rw [← hgen]
  exact iSup₂_le fun J hJ => le_genGroup_of_mem_dstarComp hs (hconn K hK J hJ)

end Setting

section Statement

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C22_dstarConn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      T3.DStarConnected Ω

theorem c22_8Gen_of_dstarConn (h : C22_dstarConn p f) : C22_8Gen p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp
  exact genGroup_eq_top_of_dstarConnected hyp.setting (h G Ω K K' K₃ z u₁ u₂ u₃ hyp)

end Statement

end C22G

end CFSG.ClassicalInvolution.Asc77

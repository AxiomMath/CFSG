module

public import CFSG.ClassicalInvolution.Asc77.AscS16F
public import CFSG.ClassicalInvolution.Asc77.AscS16D
public import CFSG.ClassicalInvolution.Asc77.AscS16B
public import CFSG.ClassicalInvolution.Asc77.AscS22G
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Hall

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem z_mem_layer (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) :
    z ∈ exactLayer Ω (u₁ * u₂) := by
  have hp : p ≠ 2 := h.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) := isPGroup_zpowers_of_sq_eq_one h.sq_12
  have hK₃Ω : K₃ ∈ tqMembers Ω (u₁ * u₂) :=
    S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzc₃ : z ∈ exactCore (u₁ * u₂) K₃ :=
    (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hK₃Ω h.hzK₃).mem
  exact exactCore_le_exactLayer hK₃Ω hzc₃

theorem layer_hall (hR1 : Z2NoD8 p) (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    ∀ B ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)),
      IsUniqueInvolution B (T7H.toBar Ω (u₁ * u₂) z (z_mem_layer h)) := by
  classical
  have hp : p ≠ 2 := h.stand.odd
  have hq : 5 ≤ p ^ f := h.stand.five
  have hΩ : HypOmegaMod p f Ω := h.stand.hyp
  have hBelow : CITBelowU p f (Nat.card G) := h.stand.below f hq
  have hu1 : u₁ * u₂ ≠ 1 :=
    (T7S22.mul_ne_one_of_twins h.stand.hyp h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
      h.hu₂.1 h.hu₂.2).1
  have hu₂C' : (u₁ * u₂) * u₂ = u₂ * (u₁ * u₂) := by
    calc (u₁ * u₂) * u₂ = (u₂ * u₁) * u₂ := by rw [h.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := h.sq_12
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) := isPGroup_zpowers_of_sq_eq_one hu2
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    obtain ⟨x, -, y, -, hxy⟩ :=
      (hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.stand.mem hV)).exists_not_commute
    have hucen : u₁ * u₂ ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  obtain ⟨hS, hlt⟩ := S22.layer_section hp hq hΩ h.stand.aEmpty hu2 hnc
  have hK₃Ω : K₃ ∈ tqMembers Ω (u₁ * u₂) := S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzY : z ∈ exactLayer Ω (u₁ * u₂) := z_mem_layer h
  have hA3 : T7H.exactImg Ω (u₁ * u₂) K₃ ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)) :=
    T7H.exactImg_mem hK₃Ω
  have hzA3 : IsUniqueInvolution (T7H.exactImg Ω (u₁ * u₂) K₃) (T7H.toBar Ω (u₁ * u₂) z hzY) :=
    T7H.exactImg_isUnique hp hΩ hcpg hK₃Ω h.hzK₃ hzY
  have hstar := S22.hstar_layer hp hq hΩ hcpg hAall
  rcases transSection_or_dConnected hp hq (thm4Below_of_citBelow hBelow) hlt hS with hconn | htrans
  · exact hall_of_connected hp hS.hyp hconn hstar hA3 hzA3
  · have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω (u₁ * u₂))) := htrans.hyp
    by_cases htop : (⊤ : Subgroup (↥(exactLayer Ω (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(exactLayer Ω (u₁ * u₂)))) ∈
        oddQuotientFamily (exactPair Ω (u₁ * u₂))
    · intro B hB
      have h1 : ∀ B ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)), B = ⊤ := by
        intro B hB
        obtain ⟨g, hg⟩ := htrans.trans ⊤ htop B hB
        rw [← hg]
        exact conjSub_eq_self_of_mem (Subgroup.mem_top g)
      rw [h1 B hB, ← h1 _ hA3]
      exact hzA3
    · exfalso
      have hDE : DEdgeless (oddQuotientFamily (exactPair Ω (u₁ * u₂))) := by
        have key : ∀ B ∈ oddQuotientFamily (exactPair Ω (u₁ * u₂)),
            ∀ J ∈ omegaNbr (oddQuotientFamily (exactPair Ω (u₁ * u₂))) B, False := by
          intro B hB J hJ'
          have hJΦ := hJ'.1
          obtain ⟨w, hw1, hw2⟩ := hstar B hB J hJΦ
            (T3.omegaNbr_subset_omegaStarNbr hp hΦ B hJ')
          obtain ⟨g, hg⟩ := htrans.trans _ hA3 B hB
          have hJ'Φ := hΦ.conjInvariant g⁻¹ J hJΦ
          have hwK : IsUniqueInvolution (T7H.exactImg Ω (u₁ * u₂) K₃) (g⁻¹ * w * g⁻¹⁻¹) := by
            have := hw1.conj g⁻¹
            rwa [← hg, conjSub_inv_conjSub] at this
          have hw2' := hw2.conj g⁻¹
          rw [← hzA3.eq hwK] at hw2'
          have heq := eq_exactImg_of_twin h hV3 hJ'Φ hzY hw2'
          apply hJ'.2.1
          calc J = conjSub g (conjSub g⁻¹ J) := (conjSub_conjSub_inv g J).symm
            _ = B := by rw [heq, hg]
        intro B hB J hJ hadj
        rcases hadj with h1 | h1
        · exact key B hB J h1
        · exact key J hJ B h1
      obtain ⟨H, _, _, ι, π, hι, hconj, hπy⟩ := exists_layer_emb hΩ (u₁ * u₂)
      obtain ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, hu₁R, hu₂R, hu₃R, c12, c13, c23, hj₁, hj₂, e₁,
        e₂, s₁, s₂⟩ := exists_invert h
      have d : InvData z u₁ u₂ j₁ j₂ R R' R₃ :=
        { z2 := h.hz.sq, s₁ := h.sq₁, s₂ := h.sq₂, u₁R := hu₁R, u₂R := hu₂R, j₁R := hj₁,
          j₂R := hj₂, c₁₂ := c12, c₁₃ := c13, c₂₃ := c23, inv₁ := e₁, inv₂ := e₂, sq₁ := s₁,
          sq₂ := s₂ }
      have hu₂C : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hu₂C'.symm
      have hvC : j₁ * j₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr d.v_comm_u
      have hzC : z ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        exactLayer_le_centralizer Ω (u₁ * u₂) hzY
      set g₂ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)) := ⟨u₂, hu₂C⟩ with hg₂
      set gv : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)) := ⟨j₁ * j₂, hvC⟩ with hgv
      have hnorm : ∀ (g : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)))
          (x : ↥(exactLayer Ω (u₁ * u₂)) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω (u₁ * u₂))),
          π g * ι x * (π g)⁻¹ ∈ ι.range ∧ (π g)⁻¹ * ι x * π g ∈ ι.range := by
        intro g x
        induction x using QuotientGroup.induction_on with
        | H y =>
          refine ⟨⟨_, (hconj g y).symm⟩, ?_⟩
          have h' := hconj g⁻¹ y
          rw [map_inv, inv_inv] at h'
          exact ⟨_, h'.symm⟩
      have hK_le : K ≤ trivialOnQuot K₃ :=
        T7J.twin_le_trivialOnQuot hΩ h.stand.mem h.hK₃.1 h.hK₃K.symm h.hz h.hzK₃
      have hK'_le : K' ≤ trivialOnQuot K₃ :=
        T7J.twin_le_trivialOnQuot hΩ h.hK'.1 h.hK₃.1 h.hK₃K'.symm h.hzK' h.hzK₃
      have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ := hK'_le h.hu₂.1
      have hvK₃ : j₁ * j₂ ∈ trivialOnQuot K₃ :=
        (trivialOnQuot K₃).mul_mem (hK_le (hR.1 hj₁)) (hK'_le (hR'.1 hj₂))
      have haA := layer_act_exact hΩ hcpg hconj hK₃Ω g₂ hu₂K₃
      have hvA := layer_act_exact hΩ hcpg hconj hK₃Ω gv hvK₃
      have ha2 : π g₂ * π g₂ = ι (T7H.toBar Ω (u₁ * u₂) z hzY) := by
        rw [← map_mul]
        have : g₂ * g₂ = ⟨z, hzC⟩ := Subtype.ext h.sq₂
        rw [this]
        exact hπy ⟨z, hzY⟩
      have hv2 : π gv * π gv = 1 := by
        rw [← map_mul]
        have : gv * gv = 1 := Subtype.ext d.sq_v
        rw [this, map_one]
      have hav : π gv * π g₂ * (π gv)⁻¹ = (π g₂)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        congr 1
        refine Subtype.ext ?_
        show (j₁ * j₂) * u₂ * (j₁ * j₂)⁻¹ = u₂⁻¹
        exact d.v_inv_u₂
      exact false_of_t6_section hR1 hp hq hBelow hlt htrans htop hDE hstar ι hι (π g₂) (π gv)
        (hnorm g₂) (hnorm gv) hA3 hzA3 haA hvA ha2 hv2 hav

end Hall

end S16

end CFSG.ClassicalInvolution.Asc77

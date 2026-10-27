module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31CaseI
public import CFSG.GH74.GLS.Stage1.Main.BridgeField
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
import CFSG.GH74.GLS.Stage2.Local.P27.Leaf27DatumPlus
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cP27
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Psp4Datum
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

section Conj

variable {G : Type} [Group G] [Finite G]

theorem l31_exists_conj_sylow {K T T' : Subgroup G} (hT : IsSylowOf 2 T K)
    (hT' : IsSylowOf 2 T' K) : ∃ c ∈ K, T' = cmap c T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hT
  obtain ⟨Q', rfl⟩ := hT'
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨n, n.2, ?_⟩
  rw [← hn]
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨z, hz, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hy
    refine ⟨(z : G), ⟨_, hz, rfl⟩, ?_⟩
    change (n : G) * (z : G) * (n : G)⁻¹ = ((MulAut.conj n • z : K) : G)
    rw [MulAut.smul_def, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨MulAut.conj n • y, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
    · change ((MulAut.conj n • y : K) : G) = (n : G) * (y : G) * (n : G)⁻¹
      rw [MulAut.smul_def, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem l31_isSylowOf_cmap {K T : Subgroup G} (h : IsSylowOf 2 T K) (g : G) :
    IsSylowOf 2 (cmap g T) (cmap g K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h.card_eq

theorem l31_T1_conj {x : G} {T : Subgroup G}
    (h : ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ IsDihedral ↥T₁)
    (g : G) :
    ∃ T₁ : Subgroup G, T₁ ≤ cmap g T ∧ (cmap g T ⊓ Jx (g * x * g⁻¹)) ⊔ T₁ = cmap g T ∧
      T₁ ⊓ Jx (g * x * g⁻¹) = ⊥ ∧ IsDihedral ↥T₁ := by
  obtain ⟨T₁, h1, h2, h3, h4⟩ := h
  have hinj := (MulAut.conj g).injective
  refine ⟨cmap g T₁, Subgroup.map_mono h1, ?_, ?_, ?_⟩
  · rw [P27.Jx_conj, ← Subgroup.map_inf T (Jx x) _ hinj, ← Subgroup.map_sup, h2]
  · rw [P27.Jx_conj, ← Subgroup.map_inf _ _ _ hinj, h3, Subgroup.map_bot]
  · exact l31_isDihedral_of_equiv (Subgroup.equivMapOfInjective T₁ _ hinj).symm h4

end Conj

section Main

theorem nonCentralT1_of_ctx
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → L4TwoFieldStmt G z k S)
    (hSch : P34.GHSchreier) : NonCentralT1 := by
  intro G _ _ z k S hctx hk x hx T hT
  classical
  have hcen : IsCentralInvolution z := hctx.central
  have hncx : ¬ IsConj z x := fun hc =>
    hx.2 (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hcen hc)
  rcases kind_cases_of_data hcen hctx.data with hone | -
  · exact absurd (hone z x hctx.orderOf_z hx.1) hncx
  obtain ⟨xd, hDP⟩ : ∃ xd : G, P27.DatumPlus z xd := by
    rcases hk with hpsp | ⟨ε, hl4⟩
    · subst hpsp
      obtain ⟨xd, q, hDP⟩ := P27.datumPlusPsp4_of_ctx hctx hSch
      exact ⟨xd, hDP.toDatumPlusQ.toDatumPlus⟩
    · subst hl4
      have hcl : IsClassicalKind (Kind.l4 ε) := Or.inr ⟨ε, rfl⟩
      obtain ⟨g, hg⟩ := exists_conj_cen_of_central hcen hx.1
      have hx'nc : IsNonCentralInvolution (g * x * g⁻¹) :=
        ⟨by rw [← hx.1]; exact (MulAut.conj g).orderOf_eq x, fun hc => hx.2
          (Stage2.Local.Prop28.isCentralInvolution_of_isConj' hc (isConj_iff.mpr ⟨g, rfl⟩).symm)⟩
      obtain ⟨xd, hDP⟩ := P27.leaf_p27datumPlus_of_ctx (Ctx := Stage2Ctx) hfld
        (fun _ _ _ _ _ _ c => c.data) (fun _ _ _ _ _ _ c => c.central)
        (fun _ _ _ _ _ _ c => c.sylow) (fun _ _ _ _ _ _ c => c.std.kgh) hSch G z (Kind.l4 ε) S
        hctx hcl ⟨_, hg, hx'nc⟩
      exact ⟨xd, hDP⟩
  obtain ⟨T₀, D₁, D₂, U, T₁, q, n, t', hC, hS, hTr, hEx⟩ := hDP
  obtain ⟨T₁s, h1, h2, h3, -, -, h6⟩ := P27.fullFT1_of_extra hS hEx
  obtain ⟨g, hg⟩ := isConj_iff.mp ((hC.classes x hx.1).resolve_left hncx)
  have hT₀ : IsSylowOf 2 (cmap g T₀) (centralizer ({x} : Set G)) := by
    have hcm : cmap g (centralizer ({xd} : Set G)) = centralizer ({g * xd * g⁻¹} : Set G) :=
      Stage1.Thm2.Recip.map_centralizer_singleton_conj xd g
    have := l31_isSylowOf_cmap hC.T_syl g
    rwa [hcm, hg] at this
  obtain ⟨c, hc, hTc⟩ := l31_exists_conj_sylow hT₀ hT
  have hcx : c * x * c⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [this]
    group
  have hgc : (c * g) * xd * (c * g)⁻¹ = x := by
    rw [show (c * g) * xd * (c * g)⁻¹ = c * (g * xd * g⁻¹) * c⁻¹ by group, hg, hcx]
  have hTcg : T = cmap (c * g) T₀ := by rw [hTc, cmap_cmap]
  have := l31_T1_conj (x := xd) ⟨T₁s, h1, h2, h3, h6⟩ (c * g)
  rwa [hgc, ← hTcg] at this

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

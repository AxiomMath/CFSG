module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24H00
public import CFSG.ClassicalInvolution.Asc77.AscS24BHFrame
public import CFSG.ClassicalInvolution.Asc77.AscS24BHyp
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngH
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A05

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.exists_mem_USet_le [Finite G] (hΩ : HypOmegaModT
    Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) : ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.dstarAdj_of_le_normalizer [Finite G] (hΩ :
    HypOmegaModT Ω)
    {K J : Subgroup G} (hJ : J ∈ Ω) (hne : J ≠ K) (hN : J ≤ Subgroup.normalizer (K : Set G)) :
    dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := CFSG.ClassicalInvolution.Q3.Q3T7P24.exists_mem_USet_le hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu => hN (hUJ hu)⟩⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement MatrixGroups
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]
omit [Finite G] in

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.isClassicalMember_of_twin (hΩ : HypOmegaModT Ω)
    {M : Subgroup G} {t : G}
    (hM : M ∈ Ω) (hMt : IsUniqueInvolution M t) : Generic.IsClassicalMember M t := by
  obtain ⟨z', hz'⟩ := hΩ.classical M hM
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = t := (hMt.unique z' hz'.mem hzsq).resolve_left hzne
  exact hz'
end Finite
end Asc77

end

section

namespace Asc77.ExactLayer
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped commutatorElement MatrixGroups
section Core
variable {G : Type} [Group G] {K : Subgroup G} {z c : G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.exactCore_le [Finite G] (c : G) (K : Subgroup G)
    :
    exactCore c K ≤ K ⊓ Subgroup.centralizer ({c} : Set G) :=
  (exactCore_def c K).le

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.exactCore_le_centralizer [Finite G] (c : G) (K :
    Subgroup G) :
    exactCore c K ≤ Subgroup.centralizer ({c} : Set G) :=
  (CFSG.ClassicalInvolution.Q3.Q3T7P24.exactCore_le c K).trans inf_le_right
variable [Finite G]
variable (hK : Generic.IsClassicalMember K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
  (hcK : c ∈ trivialOnQuot K)
include hK hc2 hcK
end Core
end Asc77.ExactLayer

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7P24.mem_dstarComp_of_twin (hΩ : HypOmegaModT Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K := by
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Relation.ReflTransGen.single
    (CFSG.ClassicalInvolution.Q3.Q3T7P24.dstarAdj_of_le_normalizer hΩ hLΩ hLK
        (hΩ.le_normalizer_of_twin hLΩ hK hLK hzL hzK))
end Finite
end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Frame4
open CFSG.ClassicalInvolution.Asc77.T7E.Frame4

theorem exists_structure [Fact (Q3CL.ClassicalClause Ω)] (c : Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω
    W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    ∃ (x₁ x₂ x₃ : G) (m : ℕ), 0 < m ∧ Subgroup.zpowers x₁ = F.ρ.R ⊓ W ∧
      Subgroup.zpowers x₂ = F.ρ'.R ⊓ W ∧ Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W ∧
      orderOf x₁ = 4 * m ∧ orderOf x₂ = 4 * m ∧ orderOf x₃ = 4 * m ∧ x₁ ^ (2 * m) = F.z ∧
      x₂ ^ (2 * m) = F.z ∧ x₃ ^ (2 * m) = F.j ∧
      x₁ ∈ F.ρ.K ∧ x₂ ∈ F.ρ'.K ∧ x₃ ∈ F.ρ₃.K ∧
      (∀ a ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)),
        a = 1 ∨ a = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m) := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have k₁ : x₁ ∈ F.ρ.K := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
  have k₂ : x₂ ∈ F.ρ'.K := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
  have k₃ : x₃ ∈ F.ρ₃.K := F.ρ₃.hRK.1 (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).1
  refine ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, ?_⟩
  intro a ha
  refine A3Mod.fixed_eq_one_or (show Commute x₁ x₂ from c.comm_W _ m₁ _ m₂)
    (show Commute x₁ x₃ from c.comm_W _ m₁ _ m₃) (show Commute x₂ x₃ from c.comm_W _ m₂ _ m₃)
    o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃ (hgen ha.1) ?_ ?_ ?_
  · rw [commutes_of_mem_centerIn ha.2 F.ρ.r_mem_normalizer]; group
  · rw [commutes_of_mem_centerIn ha.2 F.ρ'.r_mem_normalizer]; group
  · rw [commutes_of_mem_centerIn ha.2 F.ρ₃.r_mem_normalizer]; group
end Frame4
end T7E
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_twin_reps [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W) :
    ∃ (S : Sylow 2 G) (ρ ρ' : Thompson.Rep Ω W), W ≤ (S : Subgroup G) ∧ ρ.K = K ∧ ρ'.K = K' ∧
      ρ.R ≤ (S : Subgroup G) ∧ ρ'.R ≤ (S : Subgroup G) ∧ ρ'.K ∈ omegaNbr Ω ρ.K ∧
      ρ.K ∈ omegaNbr Ω ρ'.K ∧ T7D.imgQ ρ ≠ T7D.imgQ ρ' ∧
      T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ := T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hΩ hW hK' hR'syl hR'D
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  refine ⟨S, ρ, ρ', hWS, hρK, hρ'K, hρR ▸ hRS, hρ'R ▸ hR'S, hρnbr,
    c.omega_of_comm ρ' ρ hne.symm hcomm.symm, fun h => hne
      (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h)), Subtype.ext hcomm⟩

theorem rep_dichotomy [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (ρ ρ' : Thompson.Rep Ω W)
    (hab : T7D.imgQ ρ ≠ T7D.imgQ ρ')
    (hcomm : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ) :
    (∀ σ : Thompson.Rep Ω W, σ.K = ρ.K ∨ σ.K = ρ'.K) ∨
      ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4),
        (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ ∃ σ : Thompson.Rep Ω W,
          T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ ∧
          T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ' := by
  obtain ⟨-, hcl⟩ := c23_1_clique_proved G Ω K K' z hs W hW
  have hst : AscStand Ω K := hs.stand
  have hP : PartIHyp Ω := ⟨hst.modU, hst.cls, hst.aEmpty⟩
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Thompson.isTT_muDelta hst.modU hW (Q3CL.thompsonCube hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Thompson.isStar_muDelta hst.modU hW (thompsonStar G Ω hP W hW)
  by_cases hall : ∀ σ : Thompson.Rep Ω W, σ.K = ρ.K ∨ σ.K = ρ'.K
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨σ, hσ1, hσ2⟩ := hall
  set Δ := Thompson.muDelta Ω W with hΔ
  set a := T7D.imgQ ρ with ha
  set b := T7D.imgQ ρ' with hb
  set x := T7D.imgQ σ with hx
  have haΔ : a ∈ Δ := T7D.imgQ_mem ρ
  have hbΔ : b ∈ Δ := T7D.imgQ_mem ρ'
  have hxΔ : x ∈ Δ := T7D.imgQ_mem σ
  have hxa : x ≠ a := fun h => hσ1 (c.K_eq_of_img_eq σ ρ (congrArg Subtype.val h))
  have hxb : x ≠ b := fun h => hσ2 (c.K_eq_of_img_eq σ ρ' (congrArg Subtype.val h))
  have hcent : ∀ d ∈ ({a, b} : Set ↥(muGroup Ω W)), Star3T.cent Δ d = {a, b} := by
    intro d hd
    have hdΔ : d ∈ Δ := by
      rcases hd with rfl | rfl
      · exact haΔ
      · exact hbΔ
    have hsub : ({a, b} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent Δ d := by
      intro y hy
      rcases hd with rfl | rfl
      · rcases hy with rfl | rfl
        · exact Star3T.self_mem_cent haΔ
        · exact ⟨hbΔ, hcomm.symm⟩
      · rcases hy with rfl | rfl
        · exact ⟨haΔ, hcomm⟩
        · exact Star3T.self_mem_cent hbΔ
    exact (Set.eq_of_subset_of_ncard_le hsub
      (by rw [hcl d hdΔ, Set.ncard_pair hab]) (Set.toFinite _)).symm
  have hreach : ∀ y, Relation.ReflTransGen (Star3T.Adj Δ) a y → y = a ∨ y = b := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail y₁ y₂ _ hadj ih =>
      obtain ⟨-, h2, hc⟩ := hadj
      have hy₁ : y₁ ∈ ({a, b} : Set ↥(muGroup Ω W)) := by
        rcases ih with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      have : y₂ ∈ Star3T.cent Δ y₁ := ⟨h2, hc.symm⟩
      rw [hcent y₁ hy₁] at this
      exact this
  have hnc : ¬ Star3T.Conn Δ a x := fun h => by
    rcases hreach x h with h | h
    · exact hxa h
    · exact hxb h
  obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_four hTT hS haΔ hxΔ hnc (hcl a haΔ)
  have hna : a * x ≠ x * a := fun h => by
    have : x ∈ Star3T.cent Δ a := ⟨hxΔ, h.symm⟩
    rw [hcent a (Or.inl rfl)] at this
    rcases this with h | h
    · exact hxa h
    · exact hxb h
  have hnb : b * x ≠ x * b := fun h => by
    have : x ∈ Star3T.cent Δ b := ⟨hxΔ, h.symm⟩
    rw [hcent b (Or.inr rfl)] at this
    rcases this with h | h
    · exact hxa h
    · exact hxb h
  exact ⟨e, he, σ, hna, hnb⟩

theorem frame4_of_twin_reps [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) {ρ ρ' σ : Thompson.Rep Ω W}
    (hρK : ρ.K = K) (hρ'K : ρ'.K = K') (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K)
    (hnbr' : ρ.K ∈ omegaNbr Ω ρ'.K)
    (hac : T7D.imgQ ρ * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ)
    (hbc : T7D.imgQ ρ' * T7D.imgQ σ ≠ T7D.imgQ σ * T7D.imgQ ρ') :
    ∃ F : Frame4 Ω W, F.ρ = ρ ∧ F.ρ' = ρ' ∧ F.ρ₃ = σ ∧ F.z = z := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne₁ : ρ.K ≠ σ.K := fun h => hac (by
    have h1 : T7D.imgQ ρ = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ σ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ σ.K := fun h => hbc (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ σ := Subtype.ext (c.img_eq_of_K_eq ρ' σ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution σ.hK
  exact ⟨⟨ρ, ρ', σ, z, j, hzρ, hzρ', hj, hnbr, hnbr', hne₁, hne₂,
    fun h => hac (Subtype.ext (c.comm_of_omega ρ σ h)),
    fun h => hbc (Subtype.ext (c.comm_of_omega ρ' σ h)),
    fun h => hac (Subtype.ext (c.comm_of_omega σ ρ h).symm),
    fun h => hbc (Subtype.ext (c.comm_of_omega σ ρ' h).symm)⟩, rfl, rfl, rfl, rfl⟩
end T7E
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem sup_le_centralizer (hs : Hyp23Setting Ω K K' z) :
    K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  refine sup_le (fun w hw => ?_) (fun w hw => ?_)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hs.hz.commute_of_mem hw).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzK'.commute_of_mem hw).symm
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W₁ : Subgroup G}

theorem exists_conj_of_frame (c : Q3CL.Thompson.Ctx Ω W₁)
    {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {H₀ : Subgroup G}
    (hr : F.ρ.r ∈ H₀) (hr' : F.ρ'.r ∈ H₀) (hs : F.ρ₃.r ∈ H₀) (σ : Thompson.Rep Ω W₁) :
    ∃ h ∈ H₀, conjSub h F.ρ.K = σ.K := by
  let Y : Subgroup ↥(muGroup Ω W₁) :=
    { carrier := {y | ∃ h ∈ H₀ ⊓ Subgroup.normalizer (W₁ : Set G),
        (y : NQuot (W₁ ⊔ OCW W₁)) = Thompson.piG W₁ h}
      one_mem' := ⟨1, ⟨H₀.one_mem, Subgroup.one_mem _⟩,
        (Thompson.piG_of_mem_sup (Subgroup.one_mem _)).symm⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
        refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
        rw [Subgroup.coe_mul, e₁, e₂, Thompson.piG_mul hh₁.2 hh₂.2]
      inv_mem' := by
        rintro y ⟨h, hh, e₁⟩
        refine ⟨h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
        rw [Subgroup.coe_inv, e₁, Thompson.piG_inv hh.2] }
  have hgen : ∀ ρ : Thompson.Rep Ω W₁, ρ.r ∈ H₀ → T7D.imgQ ρ ∈ Y := fun ρ hρ =>
    ⟨ρ.r, ⟨hρ, ρ.r_mem_normalizer⟩, rfl⟩
  have hle : Subgroup.closure ({T7D.imgQ F.ρ, T7D.imgQ F.ρ', T7D.imgQ F.ρ₃} :
      Set ↥(muGroup Ω W₁)) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    exacts [hgen _ hr, hgen _ hr', hgen _ hs]
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
  have hyY : y ∈ Y :=
    hle (by rw [closure_frame_eq_top' he F hab hcomm hac]; exact Subgroup.mem_top y)
  obtain ⟨h, hh, hyh⟩ := hyY
  have himg : Thompson.piG W₁ h * F.ρ.img * (Thompson.piG W₁ h)⁻¹ = σ.img := by
    rw [← hyh]
    exact congrArg Subtype.val hy
  exact ⟨h, hh.1, c.K_eq_of_img_eq (T7D.conjRep c.hΩ hh.2 F.ρ) σ (by rw [T7D.conjRep_img, himg])⟩
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem centralizer_eq_sup_mul (hs : Hyp23Setting Ω K K' z) {u : G} (hu : u ∈ K ⊔ K')
    (hu1 : u ≠ 1) (huz : u ≠ z) (hu2 : u * u = 1) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ q ∈ K ⊔ K', ∃ c₀ ∈ Subgroup.centralizer ({z} : Set G),
      c₀ * u = u * c₀ ∧ c = q * c₀ := by
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hu' : c * u * c⁻¹ ∈ K ⊔ K' := conj_mem_sup hs hc hu
  have hu'1 : c * u * c⁻¹ ≠ 1 := by
    intro h
    apply hu1
    have := congrArg (fun t => c⁻¹ * t * c) h
    simpa [mul_assoc] using this
  have hu'z : c * u * c⁻¹ ≠ z := by
    intro h
    apply huz
    have := congrArg (fun t => c⁻¹ * t * c) h
    have e1 : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
        _ = z := by group
    simpa [mul_assoc, e1] using this
  have hu'2 : (c * u * c⁻¹) * (c * u * c⁻¹) = 1 := by
    calc (c * u * c⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  obtain ⟨q, hq, hqu⟩ := exists_conj_of_involution hs hu hu1 huz hu2 hu' hu'1 hu'z hu'2
  have hqz : q ∈ Subgroup.centralizer ({z} : Set G) := sup_le_centralizer hs hq
  refine ⟨q, hq, q⁻¹ * c, ?_, ?_, by group⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hqz) hc
  ·
    calc q⁻¹ * c * u = q⁻¹ * (c * u * c⁻¹) * c := by group
      _ = q⁻¹ * (q * u * q⁻¹) * c := by rw [← hqu]
      _ = u * (q⁻¹ * c) := by group
end T7K
end Asc77

end

section

namespace Asc77.S24
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S24
open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
    CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian)
set_option linter.unusedSectionVars false
section Gamma
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCore_le_gamma2_of {z : G} {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hBC : B ≤ Subgroup.centralizer ({z} : Set G)) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 B (Subgroup.centralizer ({z} : Set G)) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B (oddCoreOf (Subgroup.centralizer ({z} : Set G))) hB (by rw [hB8]; norm_num)
    (fun b hb => CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ (hBC hb))
    (Nat.coprime_two_left.mpr
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))))
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)).trans
    (T7K.le_gamma2 hE.1 hE2)

theorem le_gamma2_of_trivial (hΩ : HypOmegaModT Ω) {z e : G} {B : Subgroup G}
    (hzB : z ∈ B) (heB : e ∈ B) (he2 : e * e = 1) (he1 : e ≠ 1) (hze : z ≠ e)
    (hcomm : z * e = e * z) (hO : oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 B (Subgroup.centralizer ({z} : Set G))) {L : Subgroup G} (hLΩ : L ∈ Ω)
    (hzL : IsUniqueInvolution L z) (hetq : e ∈ trivialOnQuot L) :
    L ≤ gamma2 B (Subgroup.centralizer ({z} : Set G)) := by
  have hcl : Generic.IsClassicalMember L z :=
      CFSG.ClassicalInvolution.Q3.Q3T7P24.isClassicalMember_of_twin hΩ hLΩ hzL
  have he2' : IsPGroup 2 (Subgroup.zpowers e) := Asc77.isPGroup_zpowers_of_mul_self_eq_one he2 he1
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hzL.sq he2 hzL.ne_one he1 hze hcomm
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  intro ℓ hℓ
  obtain ⟨i, hi, n, hn, rfl⟩ := ExactLayer.exactCore_cover hcl he2' hetq ℓ hℓ
  refine Subgroup.mul_mem _ ?_ ?_
  · have hiL : i ∈ L := ExactLayer.exactCore_le_left e L hi
    have hiC : i ∈ Subgroup.centralizer ({e} : Set G) :=
        CFSG.ClassicalInvolution.Q3.Q3T7P24.exactCore_le_centralizer e L hi
    have hzi : z * i = i * z := hzL.commute_of_mem hiL
    have hiz : i ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzi.symm
    have hie : e * i = i * e := (Subgroup.mem_centralizer_singleton_iff.mp hiC).symm
    exact T7K.le_gamma2 hAB hA ⟨hiz, T7B.mem_centralizer_closure_pair hzi hie⟩
  · exact hO (CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal
      (T7A.isSubnormal_centralizer hΩ hLΩ hzL) hn)
end Gamma
end Asc77.S24

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)

theorem r_conj_j : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]

theorem comm_jz : C.D.F.j * z = z * C.D.F.j :=
  Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW _
    (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2) z C.hd.hzW

end Ctx8

structure HCtx (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  C : Ctx8 Ω K K' W S R R' z u
  a : G
  T₃ : Subgroup G
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haR : R ≤ Subgroup.centralizer ({a} : Set G)
  haR' : R' ≤ Subgroup.centralizer ({a} : Set G)
  hT : IsSylow2In T₃ C.D.F.ρ₃.K
  hTN : T₃ ≤ Subgroup.normalizer (W : Set G)
  hTa : T₃ ≤ Subgroup.centralizer ({a} : Set G)
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

private def toHFrame : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame Ω K K' W S R R' z u where
  C := H.C.toFrame
  a := H.a
  T₃ := H.T₃
  ha2 := H.ha2
  ha1 := H.ha1
  haR := H.haR
  haR' := H.haR'
  hT := H.hT
  hTN := H.hTN
  hTa := H.hTa

theorem comm_R {x : G} (hx : x ∈ R) : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR hx)

theorem comm_R' {x : G} (hx : x ∈ R') : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR' hx)

theorem x₃_mem_T : H.C.D.x₃ ∈ H.T₃ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.x₃_mem_T (toHFrame H)

theorem comm_W {w : G} (hw : w ∈ W) : w * H.a = H.a * w := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.comm_W (toHFrame H) hw

theorem comm_z : z * H.a = H.a * z := H.comm_W H.C.hd.hzW

theorem comm_j : H.C.D.F.j * H.a = H.a * H.C.D.F.j :=
  H.comm_W (H.C.x₃_sq ▸ W.pow_mem H.C.D.x₃_mem 2)

theorem comm_r : H.C.D.F.ρ.r * H.a = H.a * H.C.D.F.ρ.r := H.comm_R H.C.r_mem_R

theorem comm_t : H.C.D.F.ρ'.r * H.a = H.a * H.C.D.F.ρ'.r := H.comm_R' H.C.t_mem_R'

theorem a_ne_z : H.a ≠ z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_ne_z (toHFrame H)

theorem a_ne_j : H.a ≠ H.C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_ne_j (toHFrame H)

theorem a_not_mem : H.a ∉ Subgroup.closure ({H.C.D.F.j, z} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_not_mem (toHFrame H)

@[expose] def B : Subgroup G := Subgroup.closure ({H.C.D.F.j * H.a, H.C.D.F.j, z} : Set G)

theorem B_isElemAbelian : IsElemAbelian 2 H.B :=
  S24.B_isElemAbelian_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz H.comm_j H.comm_z

theorem B_card : Nat.card ↥H.B = 8 :=
  S24.B_natCard_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.hjJ.ne_one H.C.hzK.ne_one H.C.z_ne_j.symm
    H.C.comm_jz H.comm_j H.comm_z H.a_not_mem

theorem ja_mem_B : H.C.D.F.j * H.a ∈ H.B := Subgroup.subset_closure (by simp)

theorem j_mem_B : H.C.D.F.j ∈ H.B := Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ H.B := Subgroup.subset_closure (by simp)

theorem a_mem_B : H.a ∈ H.B := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_mem_B (toHFrame H)
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_exactCore {K₀ M V : Subgroup G} (hst : AscStand Ω K₀) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : V ≤ ExactLayer.exactCore c M := by
  have hc : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hcM : c ∈ trivialOnQuot M :=
    (ExactLayer.mem_trivialOnQuot_iff_exists_sylow hst.modU hc hM).mpr ⟨V, hV, hVc⟩
  exact ((ExactLayer.isSylow2In_exactCore_iff hst.modU hc hM hcM).mpr ⟨hV, hVc⟩).1

theorem mem_tq {K₀ M V : Subgroup G} (hst : AscStand Ω K₀) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : M ∈ ExactLayer.tqMembers Ω c :=
  (ExactLayer.mem_tqMembers_iff_exists_sylow hst.modU (isPGroup_zpowers_of_sq_eq_one hc2)).mpr
    ⟨hM, V, hV, hVc⟩
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

@[expose] def rt : G := H.C.D.F.ρ.r * H.C.D.F.ρ'.r

@[expose] def Js : Subgroup G := conjSub H.rt H.C.D.F.ρ₃.K

@[expose] def Ts : Subgroup G := conjSub H.rt H.T₃

theorem Js_mem : H.Js ∈ Ω :=
  H.C.hs.stand.modU.conjInvariant _ _ H.C.D.F.ρ₃.hK

theorem hjJs : IsUniqueInvolution H.Js H.C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.hjJs (toHFrame H)

theorem Ts_syl : IsSylow2In H.Ts H.Js := H.hT.conj H.rt

theorem Ts_le : H.Ts ≤ Subgroup.centralizer ({H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.Ts_le (toHFrame H)

theorem zx₃_mem_Ts : z * H.C.D.x₃⁻¹ ∈ H.Ts := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.zx₃_mem_Ts (toHFrame H)

theorem Js_ne : H.Js ≠ H.C.D.F.ρ₃.K := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.Js_ne (toHFrame H)

theorem za_sq : z * H.a * (z * H.a) = 1 := mul_mul_self H.C.hzK.sq H.ha2 H.comm_z

theorem ja_sq : H.C.D.F.j * H.a * (H.C.D.F.j * H.a) = 1 :=
  mul_mul_self H.C.hjJ.sq H.ha2 H.comm_j

theorem R_le_za : R ≤ Subgroup.centralizer ({z * H.a} : Set G) :=
  le_centralizer_mul ((H.C.hd.hR.2.1).trans (le_centralizer_of_unique H.C.hzK)) H.haR

theorem R'_le_za : R' ≤ Subgroup.centralizer ({z * H.a} : Set G) :=
  le_centralizer_mul ((H.C.hd.hR'.2.1).trans (le_centralizer_of_unique H.C.hzK')) H.haR'

theorem T_le_ja : H.T₃ ≤ Subgroup.centralizer ({H.C.D.F.j * H.a} : Set G) :=
  le_centralizer_mul (H.hT.1.trans (le_centralizer_of_unique H.C.hjJ)) H.hTa

theorem Ts_le_ja : H.Ts ≤ Subgroup.centralizer ({H.C.D.F.j * H.a} : Set G) :=
  le_centralizer_mul (H.Ts_syl.1.trans (le_centralizer_of_unique H.hjJs)) H.Ts_le
include H in

theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le H.C.hs.stand.modU H.C.hs.hK'.1 H.C.hd.hR'.1
    H.C.hd.hR'.2.1
include H in

theorem K_tq (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G)) :
    K ∈ ExactLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hs.stand.mem H.C.hRsyl hc2 hc
include H in

theorem K'_tq (c : G) (hc2 : c * c = 1) (hc : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    K' ∈ ExactLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hs.hK'.1 H.hR'syl hc2 hc

theorem J_tq (c : G) (hc2 : c * c = 1) (hc : H.T₃ ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.ρ₃.K ∈ ExactLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.D.F.ρ₃.hK H.hT hc2 hc

theorem Js_tq (c : G) (hc2 : c * c = 1) (hc : H.Ts ≤ Subgroup.centralizer ({c} : Set G)) :
    H.Js ∈ ExactLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.Js_mem H.Ts_syl hc2 hc

theorem j_mem_exact (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hc' : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.j ∈ ExactLayer.exactCore c K ⊔ ExactLayer.exactCore c K' := by
  rw [H.C.j_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.hs.stand.mem H.C.hRsyl hc2 hc
      (R.inv_mem H.C.x₁_mem_R)))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.C.hs.hK'.1 H.hR'syl hc2 hc'
      H.C.x₂_mem_R'))

theorem z_mem_exact :
    z ∈ ExactLayer.exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔ ExactLayer.exactCore (H.C.D.F.j *
        H.a) H.Js := by
  have e : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
    have hc : z * H.C.D.x₃⁻¹ = H.C.D.x₃⁻¹ * z :=
      Q3CL.Thompson.commutes_of_mem_WSet H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
        (W.inv_mem H.C.D.x₃_mem)
    rw [hc]; group
  have h := Subgroup.mul_mem (ExactLayer.exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔
      ExactLayer.exactCore (H.C.D.F.j * H.a) H.Js)
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.D.F.ρ₃.hK H.hT H.ja_sq H.T_le_ja
      H.x₃_mem_T))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.Js_mem H.Ts_syl H.ja_sq H.Ts_le_ja
      H.zx₃_mem_Ts))
  rwa [e] at h
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

theorem x₃_mul : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.x₃_mul (toHFrame H)

theorem B_le {L : Subgroup G} (h1 : H.C.D.F.j * H.a ∈ L) (h2 : H.C.D.F.j ∈ L) (h3 : z ∈ L) :
    H.B ≤ L := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_le (toHFrame H) h1 h2 h3

theorem closure_le_B {x y w : G} (hx : x ∈ H.B) (hy : y ∈ H.B) (hw : w ∈ H.B) :
    Subgroup.closure ({x, y, w} : Set G) ≤ H.B := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.closure_le_B (toHFrame H) hx hy hw

theorem B_eq_zja : H.B = Subgroup.closure ({z, H.C.D.F.j, H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_eq_zja (toHFrame H)

theorem B_eq_zjza : H.B = Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_eq_zjza (toHFrame H)

theorem B_eq_jzja : H.B = Subgroup.closure ({H.C.D.F.j, z, H.C.D.F.j * H.a} : Set G) :=
  le_antisymm (H.B_le mem_closure₃ mem_closure₁ mem_closure₂)
    (H.closure_le_B H.j_mem_B H.z_mem_B H.ja_mem_B)

theorem hyp51At_z [h51v : Fact Q3T7P24.Hyp51VertexThree] [IsSimpleGroup G] : Hyp51At H.B z := by
  have hxy : H.C.D.x₁⁻¹ * H.C.D.x₂ = H.C.D.F.j := H.C.j_eq.symm
  refine h51v.out H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hzK
    H.C.hzK' H.B_isElemAbelian H.z_mem_B (K.inv_mem H.C.x₁_mem_K) H.C.x₂_mem_K'
    (by rw [hxy]; exact H.j_mem_B) (by rw [hxy]; exact H.C.hjJ.ne_one)
    (by rw [hxy]; exact H.C.z_ne_j.symm) H.a_mem_B H.ha1 H.a_ne_z
    (H.K_tq H.a H.ha2 H.haR).2 H.a_mem_B H.ha1 H.a_ne_z (H.K'_tq H.a H.ha2 H.haR').2

theorem hyp51At_j [h51v : Fact Q3T7P24.Hyp51VertexThree] [IsSimpleGroup G] : Hyp51At H.B H.C.D.F.j
    := by
  refine h51v.out H.C.hs.stand H.C.D.F.ρ₃.hK H.Js_mem H.C.hjJ H.hjJs
    H.B_isElemAbelian H.j_mem_B H.C.x₃_mem_J (H.Ts_syl.1 H.zx₃_mem_Ts)
    (by rw [H.x₃_mul]; exact H.z_mem_B) (by rw [H.x₃_mul]; exact H.C.hzK.ne_one)
    (by rw [H.x₃_mul]; exact H.C.z_ne_j) H.a_mem_B H.ha1 H.a_ne_j
    (H.J_tq H.a H.ha2 H.hTa).2 H.a_mem_B H.ha1 H.a_ne_j (H.Js_tq H.a H.ha2 H.Ts_le).2

theorem hyp51At_a [h51i : Fact Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : Hyp51At H.B H.a :=
  h51i.out
    H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq H.a H.ha2 H.haR) (H.K'_tq H.a H.ha2 H.haR') H.B_isElemAbelian H.z_mem_B H.j_mem_B
    H.a_mem_B H.B_eq_zja H.ha1 H.a_ne_z.symm H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact H.a H.ha2 H.haR H.haR')

theorem za_ne_one : z * H.a ≠ 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.za_ne_one (toHFrame H)

theorem ja_ne_one : H.C.D.F.j * H.a ≠ 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.ja_ne_one (toHFrame H)

theorem hyp51At_za [h51i : Fact Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : Hyp51At H.B (z *
    H.a) :=
  h51i.out
    H.C.hs.stand H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq (z * H.a) H.za_sq H.R_le_za) (H.K'_tq (z * H.a) H.za_sq H.R'_le_za)
    H.B_isElemAbelian H.z_mem_B H.j_mem_B (H.B.mul_mem H.z_mem_B H.a_mem_B) H.B_eq_zjza
    H.za_ne_one (fun h => H.ha1 (left_eq_mul.mp h)) H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact (z * H.a) H.za_sq H.R_le_za H.R'_le_za)

theorem hyp51At_ja [h51i : Fact Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G] : Hyp51At H.B
    (H.C.D.F.j * H.a) :=
  h51i.out
    H.C.hs.stand H.C.D.F.ρ₃.hK H.Js_mem H.Js_ne H.C.hjJ H.hjJs
    (H.J_tq _ H.ja_sq H.T_le_ja) (H.Js_tq _ H.ja_sq H.Ts_le_ja) H.B_isElemAbelian H.j_mem_B
    H.z_mem_B H.ja_mem_B H.B_eq_jzja H.ja_ne_one (fun h => H.ha1 (left_eq_mul.mp h))
    H.C.hzK.ne_one H.C.z_ne_j H.C.hzK.sq H.z_mem_exact

theorem r_mem_normalizer_B : H.C.D.F.ρ.r ∈ Subgroup.normalizer (H.B : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.r_mem_normalizer_B (toHFrame H)

theorem hyp51 [Fact Q3T7P24.Hyp51VertexThree] [Fact Q3T7P24.Hyp51TwinInnerThree] [IsSimpleGroup G]
    : Hyp51 H.B := by
  refine hyp51_of_orbitReps H.B_isElemAbelian H.B_card
    (R := {z, H.C.D.F.j, H.a, z * H.a, H.C.D.F.j * H.a}) ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    exacts [H.hyp51At_z, H.hyp51At_j, H.hyp51At_a, H.hyp51At_za, H.hyp51At_ja]
  · intro c hc hc1
    have hrN := H.r_mem_normalizer_B
    have hrj := H.C.r_conj_j
    have hra : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
    rcases T7K.mem_cases_of_commuting_involutions H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz
        H.comm_j H.comm_z hc with h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, H.C.D.F.ρ.r, hrN, by rw [h, hrj]⟩
    · exact ⟨H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · refine ⟨H.C.D.F.j * H.a, by simp, H.C.D.F.ρ.r, hrN, ?_⟩
      have e : H.C.D.F.ρ.r * (H.C.D.F.j * H.a) * H.C.D.F.ρ.r⁻¹ =
          (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹) := by
        group
      rw [h, e, hrj, hra]
end HCtx
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

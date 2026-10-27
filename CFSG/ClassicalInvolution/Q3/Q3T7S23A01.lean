module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2207
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H03

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp23bData
    :=
  @CFSG.ClassicalInvolution.Asc77.Hyp23bData

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C23_2
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 → u ≠ z →
      u * u = 1 →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤

@[expose] def C23_3
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoS4 Ω W →
      W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥ ∨ ConcOrTF4
          G

structure Hyp23b {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (z u e g : G) : Prop where
  std : Q3T8.Asc77.Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hS4 : MuIsoS4 Ω W
  hzW : z ∈ W
  hu : u ∈ K ⊔ K'
  huW : u ∈ W
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  he : Subgroup.closure {e} = W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W :
      Set G))
  he1 : e ≠ 1
  he2 : e * e = 1
  hg : g ∈ ⨆ R ∈ DSet Ω W, R
  hgt : g * z * g⁻¹ = u * e

@[expose] def C23_7
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      ¬ ExactLayer.exactLayer Ω e ≤ oddCoreOf (ExactLayer.exactLayer Ω e) ⊔ (ExactLayer.exactLayer
          Ω e ⊓ Subgroup.normalizer (W : Set G))

@[expose] def C23_10
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g → ConcOrTF4 G

@[expose] def C23_setup
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, MuIsoS4 Ω W →
      W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥ → z ∈ W →
        ∃ (u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g

theorem c23_3_of_steps
    (hsetup : Q3T8.Asc77.C23_setup) (h10 : Q3T8.Asc77.C23_10) : Q3T8.Asc77.C23_3
    := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4
  by_cases h : W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥
  · exact Or.inl h
  · obtain ⟨u, e, g, hyp⟩ := hsetup G Ω K K' z hs W hW hS4 h hzW
    exact Or.inr (h10 G Ω K K' W z u e g hyp)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank
section Omega
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_omegaNbr_of_sylow_le_centralizer
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K J R : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : J ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) (hR : IsSylow2In R J) (hRset : R ∈ RSet Ω)
    (hRc : R ≤ Subgroup.centralizer ({z} : Set G)) : J ∈ omegaNbr Ω K := by
  have h8 := hΩ.eight_le_of_mem_RSet hRset
  exact ⟨hJ, hne, R, hRset, hR.1, hΩ.le_normalizer_of_le_centralizer hK hJ hne.symm hz hR.1
    hR.2.1 (by omega) hRc⟩
end Omega
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23b.data
    (h : Q3T8.Asc77.Hyp23b Ω K K' W z u e g) : Q3T8.Asc77.Hyp23bData Ω K K' W z u e
    g where
  hW := h.hW
  hS4 := h.hS4
  hzW := h.hzW
  hu := h.hu
  huW := h.huW
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  he := h.he
  he1 := h.he1
  he2 := h.he2
  hg := h.hg
  hgt := h.hgt

theorem Hyp23bData.hyp23b
    (h : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hs : Q3T8.Asc77.Hyp23 Ω K
    K' z) :
    Q3T8.Asc77.Hyp23b Ω K K' W z u e g where
  std := hs
  hW := h.hW
  hS4 := h.hS4
  hzW := h.hzW
  hu := h.hu
  huW := h.huW
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  he := h.he
  he1 := h.he1
  he2 := h.he2
  hg := h.hg
  hgt := h.hgt
end Basic
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C23_setupSetting
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Hyp23Setting Ω K K' z → ∀ W ∈ WSet Ω, MuIsoS4 Ω W →
      W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥ → z ∈ W →
        ∃ (u e g : G), Q3T8.Asc77.Hyp23bData Ω K K' W z u e g

theorem c23_setup_of
    (h : Q3T8.Asc77.C23_setupSetting) : Q3T8.Asc77.C23_setup := by
  intro G _ _ _ Ω K K' z hs W hW hS4 hne hzW
  obtain ⟨u, e, g, hd⟩ := h G Ω K K' z hs.setting W hW hS4 hne hzW
  exact ⟨u, e, g, hd.hyp23b hs⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

theorem c23_2_of
    (hE : Q3T7E.ThmEWithSylow3) (htr : Q3T8.Asc77.C23_2_trans) (hfuse :
    Q3T8.Asc77.C23_2_fuse) :
    Q3T8.Asc77.C23_2 := by
  intro G _ _ _ Ω K K' z h W hW hzW u hu huW hu1 huz hu2
  have hs := h.setting
  have hstd : StdCent Ω K
      (Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) z :=
    hs.stdCent_of_twin le_sup_right fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨c, hcz, hcu⟩ := hfuse G Ω K K' z hs W hW hzW u hu huW hu1 huz hu2 L hL L' hL' hne
        R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      intro a ha
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact Q3T8.Asc77.thmE_apply hE hs.stand hs.hz hs.hK' hs.hne hstd
    (htr G Ω K K' z hs W hW hzW u hu huW hu1 huz hu2)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_frame4
    [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (hzW : z ∈ W) (hS4 : MuIsoS4 Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.z = z ∧
      T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := Q3T8.Asc77.T7D.exists_swap_equiv hs hW hS4
  obtain ⟨S, R, R', hWS, hRsyl, hR'syl, hRS, hR'S⟩ := Q3T8.Asc77.T7D.exists_sylow_frame hs hW hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS (mem_RSet_of_isSylow2In hK' hR'syl) hR'S
  obtain ⟨ρ, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, -⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK' hR'syl
      hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
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
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)
end T7E
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD

theorem c23_2_of_trans
    (hE : Q3T7E.ThmEWithSylow3) (htr : Q3T8.Asc77.C23_2_trans) :
    Q3T8.Asc77.C23_2 :=
  Q3T8.Asc77.c23_2_of hE htr Q3T8.Asc77.c23_2_fuse
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
theorem c23_setupSetting_proved
    : Q3T8.Asc77.C23_setupSetting := by
  intro G _ _ _ Ω K K' z hs W hW hS4 hE hzW
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hst hW
  obtain ⟨e, F, he, hρK, hρ'K, hFz, hab, hcomm, hac, -⟩ := Q3T8.Asc77.T7E.exists_frame4 hs hW hzW
      hS4
  obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, hfix⟩ :=
    F.exists_structure c he hab hcomm hac
  rw [hρK] at k₁
  rw [hρ'K] at k₂
  rw [hFz] at z₁ z₂
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have c12 : Commute x₁ x₂ := c.comm_W _ m₁ _ m₂
  have c13 : Commute x₁ x₃ := c.comm_W _ m₁ _ m₃
  have c23 : Commute x₂ x₃ := c.comm_W _ m₂ _ m₃
  have o₃' : x₃ ^ (4 * m) = 1 := by rw [← o₃]; exact pow_orderOf_eq_one x₃
  obtain ⟨hsq_e, hsq_u, hue⟩ := A3Mod.triple_facts c12 c13 c23 o₃' (z₁.trans z₂.symm)

  set e₄ := (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m with he₄
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W
      : Set G)), a ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hE (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hno a ha))
  have hae : a = e₄ := (hfix a haE).resolve_left ha1
  have he₄E : e₄ ∈ W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
      hae ▸ haE
  have he₄1 : e₄ ≠ 1 := hae ▸ ha1

  set u := x₁ ^ m * (x₂ ^ m)⁻¹ with hu
  have hu4 : orderOf (x₁ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega) (by rw [o₁]; exact dvd_mul_left m 4)
    rwa [o₁, Nat.mul_div_cancel _ hm] at this
  have hu4' : orderOf (x₂ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega) (by rw [o₂]; exact dvd_mul_left m 4)
    rwa [o₂, Nat.mul_div_cancel _ hm] at this
  have hmem₁ : x₁ ^ m ∈ K := K.pow_mem k₁ m
  have hmem₂ : (x₂ ^ m)⁻¹ ∈ K' := K'.inv_mem (K'.pow_mem k₂ m)
  have huK : u ∈ K ⊔ K' := Subgroup.mul_mem_sup hmem₁ hmem₂
  have huW : u ∈ W := W.mul_mem (W.pow_mem m₁ m) (W.inv_mem (W.pow_mem m₂ m))
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hsq_u
  have hu1 : u ≠ 1 := by
    intro h
    have : x₁ ^ m = x₂ ^ m := mul_inv_eq_one.mp h
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK' hKK'
        hu4' (this ▸ hmem₁) (K'.pow_mem k₂ m)
  have huz : u ≠ z := by
    intro h
    have h1 : (x₂ ^ m)⁻¹ = (x₁ ^ m)⁻¹ * z := by rw [← h, hu]; group
    have h2 : (x₂ ^ m)⁻¹ ∈ K := by
      rw [h1]
      exact K.mul_mem (K.inv_mem hmem₁) hz.mem
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK' hKK'
      (by rw [orderOf_inv]; exact hu4') h2 hmem₂

  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ₃)
  obtain ⟨g, hgM, hyg⟩ := T7E.exists_mem_MGrp_of_mem_muGroup y
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := Thompson.MGrp_le_normalizer Ω W hgM
  have himg : Thompson.piG W g * F.ρ.img * (Thompson.piG W g)⁻¹ = F.ρ₃.img := by
    rw [← hyg]
    exact congrArg Subtype.val hy
  have hKg : conjSub g F.ρ.K = F.ρ₃.K :=
    c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ hgN F.ρ) F.ρ₃ (by rw [Q3T8.Asc77.T7D.conjRep_img,
        himg])
  have hzg : g * z * g⁻¹ = F.j := by
    have := F.hz.conj g
    rw [hKg] at this
    rw [hFz] at this
    exact (F.hj.eq this).symm
  have hj : u * e₄ = F.j := by rw [hue, z₃]
  refine ⟨u, e₄, g, ⟨hW, hS4, hzW, huK, huW, hu2, hu1, huz, ?_, he₄1, ?_, hgM, ?_⟩⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact he₄E
    · intro b hb
      rcases hfix b hb with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.subset_closure (Set.mem_singleton _)
  · rw [← pow_two]; exact hsq_e
  · rw [hzg, hj]
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

@[expose] def C23_4X
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      ExactLayer.exactLayer Ω e ≤ oddCoreOf (ExactLayer.exactLayer Ω e) ⊔ (ExactLayer.exactLayer Ω
          e ⊓ Subgroup.normalizer (W : Set G)) ∨
        Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1)

@[expose] def C23_9X
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧ ExactLayer.exactLayer Ω e ⊔ ExactLayer.exactLayer Ω
          u = ⊤) ∧
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) ∧
      (Q3T8.Asc77.LayerOrthType Ω u 5 true ∨ Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1))

@[expose] def C23_9_noZX
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23Setting Ω K K' z →
      Q3T8.Asc77.Hyp23bData Ω K K' W z u e g →
        Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) → u * e ∉ zStarOf (ExactLayer.exactLayer Ω u)

@[expose] def C23_9_genX
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23Setting Ω K K' z →
      Q3T8.Asc77.Hyp23bData Ω K K' W z u e g → Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) →
        (Q3T8.Asc77.LayerOrthType Ω u 5 true ∨ Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1)) →
          ExactLayer.exactLayer Ω e ⊔ ExactLayer.exactLayer Ω u = ⊤
end Asc77

end

section

namespace Asc77.T7H
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7H
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem toBar_mul
    {x y : G} (hx : x ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c) (hy : y ∈
    Q3T8.Asc77.ExactLayer.exactLayer Ω c) :
    Q3T8.Asc77.T7H.toBar Ω c (x * y) ((Q3T8.Asc77.ExactLayer.exactLayer Ω c).mul_mem hx hy) =
        Q3T8.Asc77.T7H.toBar Ω c x hx * Q3T8.Asc77.T7H.toBar Ω c y hy := rfl

theorem layer_orth_six
    (hTSF : Q3T8.Asc77.TwinSquareFact3) (hΩ : Q3T7M.HM Ω) (hBelow : Q3T8.Generic.CITBelowU
    (Nat.card G))
    (hc2 : c * c = 1) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {K K' L : Subgroup G} {z t b b' : G}
    (hK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
        (hL : L ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : KPerp Ω K = {K, K'}) (hperp' : KPerp Ω K' = {K', K})
    (htL : IsUniqueInvolution L t) (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K)) (hR' : IsSylow2In
        R' (Q3T8.Asc77.ExactLayer.exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ Q3T8.Asc77.ExactLayer.exactCore c K) (hb' : b' ∈ Q3T8.Asc77.ExactLayer.exactCore c
        K') (ob : b * b = z) (ob' : b' * b' = z)
    (hrel : t = b * b' * c) :
    Q3T8.Asc77.LayerOrthType Ω c 6 (piSign 3 1) := Q3T8.Asc77.T7J.layer_orth_six_weak hTSF hΩ
        hBelow hc2 hnc hK hK' hL hz hz'
    (fun J _ hJ => by rw [hperp] at hJ; exact hJ) (fun J _ hJ => by rw [hperp'] at hJ; exact hJ)
    htL hzt htz hR hR' hRR' hb hb' ob ob' hrel
end Asc77.T7H

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace T7K
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7K
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem exists_sylow_D
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W
    z u e g) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      R ≤ Subgroup.normalizer (W : Set G) ∧ R' ≤ Subgroup.normalizer (W : Set G) := by
  have hst := hs.stand
  have hΩ : Q3T8.Asc77.HypOmegaMod Ω := hst.hyp
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := Q3T8.Asc77.T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD := Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS
    (mem_RSet_of_isSylow2In hst.mem hR) hRS
  have hR'D := Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS
    (mem_RSet_of_isSylow2In hs.hK'.1 hR') hR'S
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have h2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  exact ⟨R, R', hR, hR', hΩ.commutes_of_twin_of_isPGroup hst.mem hs.hK'.1 hs.hne.symm hs.hz hzK'
    hR.1 hR'.1 h2, hRD.2, hR'D.2⟩

theorem e_not_mem_sup
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W
    z u e g) :
    e ∉ K ⊔ K' := by
  intro he
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', hc, hRN, hR'N⟩ := Q3T8.Asc77.T7K.exists_sylow_D hs hd
  have hQ : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Q3T8.Asc77.T7A.isSylow2In_sup_of_twin (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hs.hne hs.hz hzK'
        hR hR' hc
  have he2 : e * e = 1 := hd.he2
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hr))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hR'N hr))
  have hcz : Subgroup.centralizer (Subgroup.zpowers e : Set G) = Subgroup.centralizer {e} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have heN : R ⊔ R' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine hle.trans ?_
    rw [← hcz]
    exact Subgroup.centralizer_le_normalizer _
  have hpe : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one he2 hd.he1
  have hpg : IsPGroup 2 ↥((R ⊔ R') ⊔ Subgroup.zpowers e) := hQ.2.1.to_sup_of_normal_right' hpe heN
  have heQ : e ∈ R ⊔ R' := by
    have := hQ.2.2 _ (sup_le hQ.1 (Subgroup.zpowers_le.mpr he)) hpg le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commutes hc heQ
  have hbr : ∀ r ∈ R, b * r = r * b := fun r hr => (hc r hr b hb).symm
  have hac : ∀ r ∈ R, a * r = r * a := by
    intro r hr
    have h1 : r * e = e * r := comm_e hd (hRN hr)
    rw [hab] at h1
    have h2 : r * a * b = a * r * b := by
      calc r * a * b = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
        _ = a * (r * b) := by rw [hbr r hr]
        _ = a * r * b := by group
    exact (mul_right_cancel h2).symm
  have hbc : ∀ r ∈ R', b * r = r * b := by
    intro r hr
    have h1 : r * e = e * r := comm_e hd (hR'N hr)
    rw [hab] at h1
    have har : a * r = r * a := hc a ha r hr
    have h2 : a * (r * b) = a * (b * r) := by
      calc a * (r * b) = (a * r) * b := by group
        _ = (r * a) * b := by rw [har]
        _ = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
    exact (mul_left_cancel h2).symm
  have hapg : IsPGroup 2 (Subgroup.zpowers a) := hR.2.1.to_le (Subgroup.zpowers_le.mpr ha)
  have hbpg : IsPGroup 2 (Subgroup.zpowers b) := hR'.2.1.to_le (Subgroup.zpowers_le.mpr hb)
  have haK : a ∈ K := hR.1 ha
  have hbK' : b ∈ K' := hR'.1 hb
  have hatq : a ∈ trivialOnQuot K := (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ
      hapg hK).mpr
    ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hac r hr).symm⟩
  have hbtq : b ∈ trivialOnQuot K' := (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ
      hbpg hK'Ω).mpr
    ⟨R', hR', fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hbc r hr).symm⟩
  have ha1z : a = 1 ∨ a = z := hΩ.center_two hK hs.hz a haK hapg
    (fun y hy => (mem_trivialOnQuot_iff.mp hatq).2 y hy)
  have hb1z : b = 1 ∨ b = z := hΩ.center_two hK'Ω hzK' b hbK' hbpg
    (fun y hy => (mem_trivialOnQuot_iff.mp hbtq).2 y hy)
  have hez : e = z := by
    have hz2 : z * z = 1 := hs.hz.sq
    rcases ha1z with h1 | h1 <;> rcases hb1z with h2 | h2
    · exact absurd (by rw [hab, h1, h2]; simp) hd.he1
    · rw [hab, h1, h2]; simp
    · rw [hab, h1, h2]; simp
    · exact absurd (by rw [hab, h1, h2]; exact hz2) hd.he1

  have hgz : g * z * g⁻¹ = z := by
    have := comm_e hd (g_mem_normalizer hd)
    rw [hez] at this
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have h3 := hd.hgt
  rw [hgz, hez] at h3
  have : u = 1 := by
    have h4 : u * z = 1 * z := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h4
  exact hd.hu1 this

theorem comm_uz
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e
    g) :
    u * z = z * u :=
  Subgroup.mem_centralizer_singleton_iff.mp (Q3T8.Asc77.T7K.sup_le_centralizer hs hd.hu)

theorem comm_gen
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e
    g) :
    ∀ a ∈ ({u * e, u, z} : Set G), ∀ b ∈ ({u * e, u, z} : Set G), a * b = b * a := by
  have c1 : Commute u e := comm_e_of_mem_W hd hd.huW
  have c2 : Commute u z := Q3T8.Asc77.T7K.comm_uz hs hd
  have c3 : Commute z e := comm_e_of_mem_W hd hd.hzW
  have c4 : Commute (u * e) u := Commute.mul_left (Commute.refl u) c1.symm
  have c5 : Commute (u * e) z := Commute.mul_left c2 c3.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (Commute.refl _).eq
  · exact c4.eq
  · exact c5.eq
  · exact c4.symm.eq
  · exact (Commute.refl _).eq
  · exact c2.eq
  · exact c5.symm.eq
  · exact c2.symm.eq
  · exact (Commute.refl _).eq

theorem B_isElemAbelian
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K'
    W z u e g) :
    IsElemAbelian 2 (Subgroup.closure ({u * e, u, z} : Set G)) := by
  have hcomm := T7A.commutes_closure (Q3T8.Asc77.T7K.comm_gen hs hd)
  have hue : u * e = e * u := comm_e_of_mem_W hd hd.huW
  have hsq : ∀ a ∈ ({u * e, u, z} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · calc u * e * (u * e) = u * (e * u) * e := by group
        _ = u * (u * e) * e := by rw [← hue]
        _ = (u * u) * (e * e) := by group
        _ = 1 := by rw [hd.hu2, hd.he2]; group
    · exact hd.hu2
    · exact hs.hz.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (Q3T8.Asc77.T7K.comm_gen hs hd) x hx

theorem B_natCard
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u
    e g) :
    Nat.card ↥(Subgroup.closure ({u * e, u, z} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz
    (Q3T8.Asc77.T7K.comm_uz hs hd)
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd.he2) hd.he1
  have hsub : ∀ x ∈ ({u * e, u, z} : Set G), x ∈ Subgroup.closure ({u, z} : Set G) ⊔
      Subgroup.zpowers e := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcl : Subgroup.closure ({u * e, u, z} : Set G) =
      Subgroup.closure ({u, z} : Set G) ⊔ Subgroup.zpowers e := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr hsub
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · have : e = u⁻¹ * (u * e) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))
  have hcomm : Commutes (Subgroup.closure ({u, z} : Set G)) (Subgroup.zpowers e) := by
    have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e_of_mem_W hd hd.huW)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e_of_mem_W hd hd.hzW)
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, z} : Set G) ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases T7A.eq_one_or_eq_of_mem_zpowers he2 hx.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      refine Q3T8.Asc77.T7K.e_not_mem_sup hs hd ?_
      have hle : Subgroup.closure ({u, z} : Set G) ≤ K ⊔ K' := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact hd.hu
        · exact Subgroup.mem_sup_left hs.hz.mem
      rw [← h1]
      exact hle hx.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, he2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num
end T7K
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace T7H
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7H
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem layer_frame
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z
    u e g) :
    ∃ (R R' : Subgroup G) (b b' : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧ R ∈ DSet Ω W ∧
      R' ∈ DSet Ω W ∧ Commutes R R' ∧ b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧ orderOf b' = 4 ∧
      (u = b * b' ∨ u = z * (b * b')) := by
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := Q3T8.Asc77.T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD : R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK' hR') hR'S
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hs.hne.symm hz hz' hR.1 hR'.1
    (S.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨b, hbRW, hb4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
      hd.hW hRD
  obtain ⟨b', hb'RW, hb'4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod
      Ω) hd.hW hR'D
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hu := Q3T8.Asc77.T7E.involution_cases hs hR hR' hRS hR'S hbRW.1 hb'RW.1 hb4 hb'4 hd.hu
    (hWS hd.huW) hd.hu2 hd.hu1 hd.huz (hWab u hd.huW b hbRW.2) (hWab u hd.huW b' hb'RW.2)
  exact ⟨R, R', b, b', hR, hR', hRD, hR'D, hc, hbRW.1, hb'RW.1, hb4, hb'4, hu⟩
end T7H
open CFSG.ClassicalInvolution.Asc77.T7H in

theorem c23_4X_of_tsf
    (hTSF : Q3T8.Asc77.TwinSquareFact3) : Q3T8.Asc77.C23_4X := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := h.std.setting
  have hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g := h.data
  have hst : Q3T8.Asc77.AscStand Ω K := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hst.below
  have hcpg : IsPGroup 2 (Subgroup.zpowers e) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨R, R', b, b', hR, hR', hRD, hR'D, hRR', hbR, hb'R', hb4, hb'4, hu⟩ :=
      Q3T8.Asc77.T7H.layer_frame hs hd

  have heW : e ∈ W ⊓ CFSG.ClassicalInvolution.Asc77.centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← hd.he]
    exact Subgroup.mem_closure_singleton_self e
  have hec : ∀ x ∈ Subgroup.normalizer (W : Set G), e * x = x * e := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := heW.2
    have := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
    have h2 : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val this
    rw [← hye]
    exact h2.symm
  have hRc : R ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hRD.2 hr)).symm
  have hR'c : R' ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hR'D.2 hr)).symm
  have hKt : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcpg).mpr ⟨hK, R, hR, hRc⟩
  have hK't : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcpg).mpr ⟨hK', R', hR', hR'c⟩
  have hRe : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore e K) :=
    ((Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hcpg hK hKt.2).mpr ⟨hR, hRc⟩)
  have hR'e : IsSylow2In R' (Q3T8.Asc77.ExactLayer.exactCore e K') :=
    ((Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hcpg hK' hK't.2).mpr ⟨hR', hR'c⟩)

  have hgN : g ∈ Subgroup.normalizer (W : Set G) := by
    have : (⨆ R ∈ DSet Ω W, R) ≤ Subgroup.normalizer (W : Set G) := iSup₂_le fun R hR => hR.2
    exact this hd.hg
  have hgc : g ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hec g hgN).symm
  have hLt : conjSub g K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω e :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hgc hKt
  have htL : IsUniqueInvolution (conjSub g K) (u * e) := by
    rw [← hd.hgt]
    exact hz.conj g

  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hzt : z * (u * e) = (u * e) * z :=
    hWab z hd.hzW (u * e) (W.mul_mem hd.huW heW.1)

  have hbK : b ∈ K := hR.1 hbR
  have hb'K' : b' ∈ K' := hR'.1 hb'R'
  have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hbK hb4
  have hb'b' : b' * b' = z := T7A.sq_eq_of_orderOf_four hz' hb'K' hb'4
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => hz.commute_of_mem hx
  have hzKe : z ∈ Q3T8.Asc77.ExactLayer.exactCore e K :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hKt hz).mem
  obtain ⟨b₁, hb₁, ob₁, hub₁, hbc⟩ : ∃ b₁ ∈ Q3T8.Asc77.ExactLayer.exactCore e K, b₁ * b₁ = z ∧ u =
      b₁ * b' ∧
      ∀ r ∈ R, r * b₁ = b₁ * r → r * b = b * r := by
    rcases hu with hu | hu
    · exact ⟨b, hRe.1 hbR, hbb, hu, fun r _ h => h⟩
    · refine ⟨z * b, (Q3T8.Asc77.ExactLayer.exactCore e K).mul_mem hzKe (hRe.1 hbR), ?_,
        by rw [hu]; group, ?_⟩
      · have hzb : z * b = b * z := hzc b hbK
        calc z * b * (z * b) = z * (b * z) * b := by group
          _ = z * (z * b) * b := by rw [← hzb]
          _ = (z * z) * (b * b) := by group
          _ = z := by rw [hz.sq, hbb, one_mul]
      · intro r hr h
        have hzr : z * r = r * z := hzc r (hR.1 hr)
        have h1 : z * (r * b) = z * (b * r) := by
          calc z * (r * b) = r * z * b := by rw [← mul_assoc, ← hzr, mul_assoc]
            _ = r * (z * b) := by group
            _ = z * b * r := h
            _ = z * (b * r) := by group
        exact mul_left_cancel h1

  have hQ : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hK hR)
  have htz : u * e ≠ z := by
    intro hte
    have hez : e = u * z := by
      have h1 : u * (u * e) = e := by rw [← mul_assoc, hd.hu2, one_mul]
      rw [← h1, hte]
    have hbc' : ∀ r ∈ R, r * b = b * r := by
      intro r hr
      refine hbc r hr ?_
      have hre : r * e = e * r := (hec r (hRD.2 hr)).symm
      have hzr : r * z = z * r := (hzc r (hR.1 hr)).symm
      have hrb' : r * b' = b' * r := hRR' r hr b' hb'R'
      have huz : u = e * z := by
        rw [hez, mul_assoc, hz.sq, mul_one]
      have hru : r * u = u * r := by
        rw [huz]
        calc r * (e * z) = (r * e) * z := by group
          _ = (e * r) * z := by rw [hre]
          _ = e * (r * z) := by group
          _ = e * (z * r) := by rw [hzr]
          _ = (e * z) * r := by group
      rw [hub₁] at hru
      have h2 : (r * b₁) * b' = (b₁ * r) * b' := by
        calc (r * b₁) * b' = r * (b₁ * b') := by group
          _ = (b₁ * b') * r := hru
          _ = b₁ * (b' * r) := by group
          _ = b₁ * (r * b') := by rw [hrb']
          _ = (b₁ * r) * b' := by group
      exact mul_right_cancel h2
    have := hQ.sq_eq_one_of_central hbR (fun y hy => (hbc' y hy).symm)
    rw [hbb] at this
    exact hz.ne_one this

  have hnc : ¬ ({e} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨x, -, y, -, hxy⟩ := hQ.exists_not_commute
    have hecen : e ∈ Subgroup.center G := hsub (Set.mem_singleton e)
    exact hd.he1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hecen g'))
  have hperp : KPerp Ω K = {K, K'} := hs.perp
  have hperp' : KPerp Ω K' = {K', K} := by
    rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  refine Or.inr (Q3T8.Asc77.T7H.layer_orth_six hTSF hΩ hBelow hd.he2 hnc hKt hK't hLt hz hz' hperp
      hperp'
    htL hzt htz hRe hR'e hRR' hb₁ (hR'e.1 hb'R') ob₁ hb'b' ?_)
  rw [← hub₁]
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

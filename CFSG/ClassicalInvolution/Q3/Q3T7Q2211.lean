module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RLayer
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22SecC
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2210
public import CFSG.ClassicalInvolution.Asc77.AscC22P11
public import CFSG.ClassicalInvolution.Asc77.AscC22P2

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.AscE184Sect
open scoped commutatorElement
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Conn
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem sectionConnected_of_layer
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h : T3.DStarConnected (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))) :
        Q3T8.Asc77.SectionConnected Ω c := h
end Conn
section Main

theorem third_mem_tqMembers {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω
        (u₁ * u₂) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK₃Ω hs.hK₃K.symm hs.hz hs.hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hK₃Ω hs.hK₃K'.symm hs.hzK' hs.hzK₃ hs.hu₂.1
  exact ⟨hK₃Ω, Subgroup.mul_mem _ hu₁K₃ hu₂K₃⟩

theorem sectionConnected_of_hyp22 (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF : Q3T8.Asc77.Hyp22Fuse)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Q3T8.Asc77.SectionConnected Ω (u₁ * u₂) := by
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hMz : Q3T8.Generic.IsClassicalMember K₃ z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hK₃Ω
      hzK₃
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (Q3T8.Asc77.exists_noncomm_of_isClassicalMember hMz) hc1
  have hcA : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hL : Q3T8.Asc77.LayerOrthType Ω (u₁ * u₂) 6 (piSign 3 1) :=
      Q3T8.Asc77.c22_8X_layer_of_inputs h4 hF h
  exact Q3T8.Asc77.C22G.sectionConnected_of_layer hΩ hcA
    (Q3T8.Asc77.C22G.layer_dstarConnected hΩ hs.stand.aEmpty hc2 hnc hL)

theorem layerStar_of_alpha (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF : Q3T8.Asc77.Hyp22Fuse)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) :
    ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂), J ∈ dstarComp Ω K := by
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hconn : Q3T8.Asc77.SectionConnected Ω (u₁ * u₂) := Q3T8.Asc77.C22G.sectionConnected_of_hyp22
      h4 hF h
  have hK₃t : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
      Q3T8.Asc77.C22G.third_mem_tqMembers hs
  have hK₃d : K₃ ∈ dstarComp Ω K := Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hKΩ hs.hK₃
  have hdK : dstarComp Ω K₃ = dstarComp Ω K := T7A.dstarComp_eq_of_mem hKΩ hK₃d
  intro M hM
  obtain ⟨n, hn, J', hJ't, hJ'd, rfl⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ hc2 hK₃t hconn M hM
  rw [hdK] at hJ'd
  
  have hzA : z ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u₁ * u₂ ∈ Subgroup.closure ({u₁ * u₂, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hle := commutator_oddCore_le_alphaOf hc1 (Subgroup.closure ({u₁ * u₂, z} : Set G)) huA
  rw [hα] at hle
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
      Subgroup.closure ({u₁ * u₂, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hnz : n * z = z * n :=
    commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))
  have hnzn : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  have hKn : conjSub n K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant n K hKΩ, z, hz, hnzn ▸ hz.conj n⟩
  have hnN : n ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hKΩ
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hKΩ hKn)
  exact ((mem_sigmaStarNorm_iff.mp hnN) J').mp hJ'd

theorem c22_layerStar_of_alpha (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF : Q3T8.Asc77.Hyp22Fuse) (h7 :
    Q3T8.Asc77.C22_7) :
    Q3T8.Asc77.C22G.C22_layerStar := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  exact Q3T8.Asc77.C22G.layerStar_of_alpha h4 hF h (h7 G Ω K K' K₃ z u₁ u₂ u₃ h)
end Main
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z g₀ g₁ g₂ : G}

theorem mem_normalizer_alpha_of_frame [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z]
    [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (hs : Q3T8.Asc77.Hyp22Setting Ω K K'
    K₃ z g₀ g₁ g₂)
    (hb : S22.Big Ω K) {y t : G} (hyu : y * (g₀ * g₁) = (g₀ * g₁) * y)
    (hyz : y * z * y⁻¹ = t) (hzt : z * t = t * z) (ht2 : t * t = 1)
    (htw : t * (g₁ * g₂) = (g₁ * g₂) * t)
    (hw : y * (g₁ * g₂) * y⁻¹ = g₁ * g₂ ∨ y * (g₁ * g₂) * y⁻¹ = (t * z) * (g₁ * g₂)) :
    y ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({g₀ * g₁, z} : Set G)) : Set G) := by
  classical
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz2 : z * z = 1 := hz.sq
  have h2 := Q3T8.Asc77.S22.c22_2S G Ω K K' K₃ z g₀ g₁ g₂ hs hb
  have hcg := Q3T8.Asc77.S22.comm_gen hs
  set u : G := g₀ * g₁ with hu
  set w : G := g₁ * g₂ with hwdef
  have huB : u ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_fst
  have hzB : z ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_snd
  have hwB : w ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := T7B.mem_closure_thd
  have cuz : u * z = z * u := hcg u (by simp [hu]) z (by simp)
  have cuw : u * w = w * u := hcg u (by simp [hu, hwdef]) w (by simp [hwdef])
  have czw : z * w = w * z := hcg z (by simp) w (by simp [hwdef])
  have hu2 : u * u = 1 := hs.sq_12
  have hw2 : w * w = 1 := hs.sq_23
  obtain ⟨hu1, huz⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK hK' hs.hne.symm hz hs.hu₁.1
      hs.hu₂.1
    hs.hu₂.2
  obtain ⟨hw1, hwz⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK' hK₃Ω hs.hK₃K'.symm hzK' hs.hu₂.1
    hs.hu₃.1 hs.hu₃.2
  have hg12 : g₁ * g₂ = g₂ * g₁ := hs.comm₂₃
  have huw : u ≠ w := by
    intro h
    have e : g₀ = g₂ := by
      have h' : g₀ * g₁ = g₂ * g₁ := by rw [← hg12]; exact h
      exact mul_right_cancel h'
    exact Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK₃Ω
        hs.hK₃K hs.hu₃.2 (e ▸ hs.hu₁.1) hs.hu₃.1
  have huwz : u ≠ w * z := by
    intro h
    have e : g₀ = g₂ * z := by
      have hzg₁ : z * g₁ = g₁ * z := hs.comm_z₂
      have h' : g₀ * g₁ = (g₂ * z) * g₁ := by
        calc g₀ * g₁ = g₁ * g₂ * z := h
          _ = g₂ * g₁ * z := by rw [hg12]
          _ = g₂ * (g₁ * z) := by rw [mul_assoc]
          _ = g₂ * (z * g₁) := by rw [hzg₁]
          _ = (g₂ * z) * g₁ := by rw [mul_assoc]
      exact mul_right_cancel h'
    exact Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK₃Ω
        hs.hK₃K hs.hu₁.2 hs.hu₁.1
      (e ▸ K₃.mul_mem hs.hu₃.1 hzK₃.mem)
  have key : ∀ w' ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G), w' ≠ 1 → u ≠ w' →
      w' * w' = 1 → u * w' = w' * u → y * w' = w' * y →
      y ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({g₀ * g₁, z} : Set G)) : Set G) := by
    intro w' hw'B hw'1 huw' hw'2 hcomm hyw'
    have hA2 : IsElemAbelian2 (Subgroup.closure ({u, w'} : Set G)) 2 :=
      T7A.isElemAbelian2_closure_pair hu2 hw'2 hu1 hw'1 huw' hcomm
    have hAB : Subgroup.closure ({u, w'} : Set G) ≤
        Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huB
      · exact hw'B
    have hα := (h2.2 _ hAB hA2)
    have hyu' : y * u * y⁻¹ = u := by rw [hyu]; group
    have hyw'' : y * w' * y⁻¹ = w' := by rw [hyw']; group
    have hconj : conjSub y (Subgroup.closure ({u, w'} : Set G)) =
        Subgroup.closure ({u, w'} : Set G) := by
      rw [T7A.conjSub_closure_pair, hyu', hyw'']
    have := mem_normalizer_alphaOf_of_conjSub_eq hconj
    rwa [hα] at this
  rcases hw with h1 | h1
  · refine key w hwB hw1 huw hw2 cuw ?_
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [h1]
  · have hww : (w * z) * (w * z) = 1 := by
      calc (w * z) * (w * z) = (w * w) * (z * z) := by
            calc (w * z) * (w * z) = w * (z * w) * z := by group
              _ = w * (w * z) * z := by rw [czw]
              _ = (w * w) * (z * z) := by group
        _ = 1 := by rw [hw2, hz2]; group
    have hwzB : w * z ∈ Subgroup.closure ({g₀ * g₁, z, g₁ * g₂} : Set G) := mul_mem hwB hzB
    have hwz1 : w * z ≠ 1 := by
      intro h
      apply hwz
      have : w = z⁻¹ := eq_inv_of_mul_eq_one_left h
      exact this.trans (inv_eq_of_mul_eq_one_right hz2)
    have hcomm : u * (w * z) = (w * z) * u := by
      calc u * (w * z) = (u * w) * z := by group
        _ = (w * u) * z := by rw [cuw]
        _ = w * (u * z) := by group
        _ = w * (z * u) := by rw [cuz]
        _ = (w * z) * u := by group
    refine key (w * z) hwzB hwz1 huwz hww hcomm ?_
    have hyz' : y * z = t * y := by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = t * y := by rw [hyz]
    have hyw : y * w = (t * z) * w * y := by
      calc y * w = (y * w * y⁻¹) * y := by group
        _ = (t * z) * w * y := by rw [h1]
    calc y * (w * z) = (y * w) * z := by group
      _ = (t * z) * w * y * z := by rw [hyw]
      _ = (t * z) * w * (y * z) := by group
      _ = (t * z) * w * (t * y) := by rw [hyz']
      _ = ((t * z) * (w * t)) * y := by group
      _ = ((t * z) * (t * w)) * y := by rw [← htw]
      _ = (t * (z * t) * w) * y := by group
      _ = (t * (t * z) * w) * y := by rw [hzt]
      _ = ((t * t) * (z * w)) * y := by group
      _ = (w * z) * y := by rw [ht2, czw]; group

theorem oddCore_centralizer_le_normalizer_alpha [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u]
    {u₁ u₂ u₃ : G} (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : S22.Big Ω K) :
    oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) ≤
      Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  classical
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hz2 : z * z = 1 := hs.hz.sq
  have h2 := Q3T8.Asc77.S22.c22_2S G Ω K K' K₃ z u₁ u₂ u₃ hs hb
  have hCz := Q3T8.Asc77.S22.centralizer_le_normalizer_alpha (Q3T8.Asc77.S22.c22_2S) hs hb
  set α₀ := alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) with hα₀
  obtain ⟨hu1, -⟩ := Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hs.stand.mem hs.hK'.1 hs.hne.symm hs.hz
    hs.hu₁.1 hs.hu₂.1 hs.hu₂.2
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)),
      Subgroup.closure ({u₁ * u₂, z} : Set G)⁆ ≤ α₀ := by
    refine le_trans ?_ le_sup_left
    exact le_iSup₂_of_le (u₁ * u₂) (Subgroup.subset_closure (by simp))
      (le_iSup_of_le hu1 le_rfl)
  have hodd : ∀ x ∈ α₀, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat h2.1 (Subgroup.orderOf_dvd_natCard α₀ hx)
  intro n hn
  have hmα : ⁅n⁻¹, z⁆ ∈ α₀ :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hn)
      (Subgroup.subset_closure (by simp)))
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨m, hmdef⟩ : ∃ m : G, m = ⁅n⁻¹, z⁆ := ⟨_, rfl⟩
  rw [← hmdef] at hmα
  have hm : m = n⁻¹ * z * n * z := by
    rw [hmdef, commutatorElement_def, hzi]
    group
  have hzm : z * m * z⁻¹ = m⁻¹ := by
    rw [hm, hzi]
    calc z * (n⁻¹ * z * n * z) * z = z * n⁻¹ * z * n * (z * z) := by group
      _ = z * n⁻¹ * z * n := by rw [hz2]; group
      _ = (n⁻¹ * z * n * z)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]
  obtain ⟨s, hsm, hss⟩ := T7J.exists_sq_mem_zpowers (hodd m hmα)
  have hzs : z * s * z⁻¹ = s⁻¹ := T7J.conj_inv_of_mem_zpowers hzm hsm
  have hsα : s ∈ α₀ := (Subgroup.zpowers_le.mpr hmα) hsm
  have hzn : z * n * z⁻¹ = n * m := by
    rw [hm, hzi]
    group
  have hc : n * s ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : z * (n * s) * z⁻¹ = n * s := by
      calc z * (n * s) * z⁻¹ = (z * n * z⁻¹) * (z * s * z⁻¹) := by group
        _ = (n * m) * s⁻¹ := by rw [hzn, hzs]
        _ = n * (s * s) * s⁻¹ := by rw [hss]
        _ = n * s := by group
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hnn : n = (n * s) * s⁻¹ := by group
  rw [hnn]
  exact Subgroup.mul_mem _ (hCz hc) (Subgroup.inv_mem _ (Subgroup.le_normalizer hsα))
end Alpha
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Final

theorem hyp22SigmaNeX4_proved [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] : Q3T8.Asc77.T7V.Hyp22SigmaNeX4 := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h1 h2 h3 heq
  have hb : Big Ω K := Q3T8.Asc77.S22.Big.of_four h hK₄ h1 h2 h3
  have hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K := fun J hJ =>
    Q3T8.Asc77.T7S22.dComp_subset_twinSet h (by rw [heq]; exact hJ)
  have hAall := Q3T8.Asc77.S22.hAall_of_dstarComp h hsig
  have hNT : CFSG.ClassicalInvolution.G2D4Models.G2NonToralGenerate 3 :=
    CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all
  have hE : Q3T7E.ThmEWithSylow3 := Q3T8.Asc77.thmEWithSylow_of_nonToral hNT
  refine Q3T8.Asc77.S22.false_of_abelian hE (Q3T8.Asc77.S22.c22_2S) h hb hsig ?_
  intro L L' L₃ x y w hd
  have hLV : L ∈ twinSet Ω K := ⟨hd.stand.mem, z, h.hz, hd.hz⟩
  obtain ⟨L₄, hL₄, e1, e2, e3⟩ := (hb.of_twin h.hz hLV).fourth L L' L₃
  exact Q3T8.Asc77.S22.cent_of_zstar hd (Q3T8.Asc77.S22.layer_zStar hd hL₄ e1 e2 e3 hAall)

theorem hyp22SettingWyl_of_fourthTwin [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h3 : Q3T8.Asc77.Hyp22FourthTwin) :
    Q3T8.Asc77.T7V.Hyp22SettingWyl :=
  Q3T8.Asc77.T7V.hyp22SettingWyl_of_sigmaNe (Q3T8.Asc77.T7V.hyp22SigmaNe_of_split h3
      (Q3T8.Asc77.S22.hyp22SigmaNeX4_proved))
end Final
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Named

@[expose] def C22_layerNormAlpha
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      rLayer Ω (u₁ * u₂) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)
end Named
section Reduction

theorem c22_7_trans_of_layerNormAlpha (h2 : Q3T8.Asc77.C22_2) (hY :
    Q3T8.Asc77.C22G.C22_layerNormAlpha) :
    Q3T8.Asc77.C22_7_trans := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h _ J hJ
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hCz := h.centralizer_le_normalizer_alpha h2
  have hVK : ∀ M ∈ twinSet Ω K,
      M ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    fun M hM m hm => hCz (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((isUniqueInvolution_of_mem_twinSet hz hM).commute_of_mem hm).symm)
  have hgen : genGroup Ω K (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    sup_le (iSup₂_le hVK) (hY G Ω K K' K₃ z u₁ u₂ u₃ h)
  obtain ⟨w, hw, y, hy, hyw⟩ := Q3T8.Asc77.C22G.exists_conj_of_mem_dstarComp hs J hJ
  have hJΩ : J ∈ Ω := (T3.mem_dstarComp_symm hKΩ hJ).1
  have hM₀ : conjSub y⁻¹ J ∈ twinSet Ω K := conjSub_mem_twinSet hΩ.conjInvariant hz hJΩ hw hyw
  obtain ⟨g, hg⟩ := hs.stand.trans (conjSub y⁻¹ J) hM₀.1
  have hgz : g * z * g⁻¹ = z := by
    have h1 := hz.conj g
    rw [hg] at h1
    exact (isUniqueInvolution_of_mem_twinSet hz hM₀).eq h1 |>.symm
  have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  refine ⟨y * g, Subgroup.mul_mem _ (hgen hy) (hCz hgC), ?_⟩
  rw [conjSub_mul, hg, conjSub_conjSub_inv]

theorem c22_7_cent_of_layerNormAlpha (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF : Q3T8.Asc77.Hyp22Fuse)
    (h2 : Q3T8.Asc77.C22_2) (hY : Q3T8.Asc77.C22G.C22_layerNormAlpha) : Q3T8.Asc77.C22_7_cent := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hμ c hc
  have hs := h.setting
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hc2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hc1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hCz := h.centralizer_le_normalizer_alpha h2
  have htrK := Q3T8.Asc77.C22G.c22_7_trans_of_layerNormAlpha h2 hY G Ω K K' K₃ z u₁ u₂ u₃ h hμ
  have hconn : Q3T8.Asc77.SectionConnected Ω (u₁ * u₂) := Q3T8.Asc77.C22G.sectionConnected_of_hyp22
      h4 hF h
  have hK₃t : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
      Q3T8.Asc77.C22G.third_mem_tqMembers hs
  have hK₃d : K₃ ∈ dstarComp Ω K := Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hKΩ hs.hK₃
  have hdK : dstarComp Ω K₃ = dstarComp Ω K := T7A.dstarComp_eq_of_mem hKΩ hK₃d
  have hcK₃ : conjSub c K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc hK₃t
  obtain ⟨n, hn, J', hJ't, hJ'd, hJ'eq⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ hc2 hK₃t hconn _ hcK₃
  rw [hdK] at hJ'd
  obtain ⟨x₁, hx₁, hx₁eq⟩ := htrK J' hJ'd
  
  have hu₁z : u₁ * z = z * u₁ := (hz.commute_of_mem hs.hu₁.1).symm
  have hu₂z : u₂ * z = z * u₂ := (hzK'.commute_of_mem hs.hu₂.1).symm
  have huz : (u₁ * u₂) * z = z * (u₁ * u₂) := by
    calc (u₁ * u₂) * z = u₁ * (u₂ * z) := by group
      _ = u₁ * (z * u₂) := by rw [hu₂z]
      _ = (u₁ * z) * u₂ := by group
      _ = (z * u₁) * u₂ := by rw [hu₁z]
      _ = z * (u₁ * u₂) := by group
  have hnN := oddCoreOf_centralizer_le_normalizer_alphaOf hz.sq hc1 huz hn
  
  obtain ⟨c₃, hc₃⟩ := hs.stand.trans K₃ hs.hK₃.1
  have hc₃z : c₃ * z * c₃⁻¹ = z := by
    have h1 := hz.conj c₃
    rw [hc₃] at h1
    exact (hs.hzK₃.eq h1).symm
  have hc₃C : c₃ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c₃ * z = (c₃ * z * c₃⁻¹) * c₃ := by group
      _ = z * c₃ := by rw [hc₃z]
  
  have hcK : conjSub (c * c₃) K = conjSub (n * x₁) K := by
    rw [conjSub_mul, hc₃, hJ'eq, conjSub_mul, hx₁eq]
  have hdK' : conjSub ((n * x₁)⁻¹ * (c * c₃)) K = K := by
    rw [conjSub_mul, hcK, conjSub_inv_conjSub]
  have hdz : ((n * x₁)⁻¹ * (c * c₃)) * z * ((n * x₁)⁻¹ * (c * c₃))⁻¹ = z := hz.conj_eq hdK'
  have hdC : (n * x₁)⁻¹ * (c * c₃) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((n * x₁)⁻¹ * (c * c₃)) * z
        = (((n * x₁)⁻¹ * (c * c₃)) * z * ((n * x₁)⁻¹ * (c * c₃))⁻¹) *
            ((n * x₁)⁻¹ * (c * c₃)) := by group
      _ = z * ((n * x₁)⁻¹ * (c * c₃)) := by rw [hdz]
  have hce : c = (n * x₁) * ((n * x₁)⁻¹ * (c * c₃)) * c₃⁻¹ := by group
  rw [hce]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hx₁) (hCz hdC))
    (Subgroup.inv_mem _ (hCz hc₃C))

theorem c22_7_of_layerNormAlpha (hE : Q3T7E.ThmEWithSylow3) (h4 : Q3T8.Asc77.Hyp22FourTwins)
    (hF : Q3T8.Asc77.Hyp22Fuse) (h2 : Q3T8.Asc77.C22_2) (hμ : Q3T8.Asc77.C22_4) (hY :
        Q3T8.Asc77.C22G.C22_layerNormAlpha) :
    Q3T8.Asc77.C22_7 :=
  Q3T8.Asc77.c22_7_of hE h2 hμ (Q3T8.Asc77.C22G.c22_7_trans_of_layerNormAlpha h2 hY)
    (Q3T8.Asc77.C22G.c22_7_cent_of_layerNormAlpha h4 hF h2 hY)
end Reduction
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem fuseFrame_alpha [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁
    u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a a' : G, a ∈ K ∧ a' ∈ K' ∧ orderOf a = 4 ∧ orderOf a' = 4 ∧ a * a' = a' * a ∧
      ∃ (R R' : Subgroup G) (b b' y : G), IsSylow2In R K₃ ∧ IsSylow2In R' K₄ ∧ Commutes R R' ∧
        R ≤ Subgroup.centralizer ({a * a'} : Set G) ∧
        R' ≤ Subgroup.centralizer ({a * a'} : Set G) ∧ b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧
        orderOf b' = 4 ∧ b * b = z ∧ b' * b' = z ∧ y ∈ rLayer Ω (a * a') ∧
        y * z * y⁻¹ = b * b' * (a * a') ∧ b * b' * (a * a') ≠ z ∧
        z * (b * b' * (a * a')) = (b * b' * (a * a')) * z ∧
        y ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({a * a', z} : Set G)) : Set G) := by
  classical
  have hs := h
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    Q3T8.Asc77.C22P.exists_sylow_quad_S h hK₄ h41 h42 h43
  
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup (Q3T7.modU_toGen3 hΩ) hP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := Q3T8.Asc77.T7D.exists_rep (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hW hK₄Ω h4
      hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hs.hK'
    · exact hs.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact Q3T8.Asc77.T7V.adj_of_twins hs (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    Q3T8.Asc77.T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3T8.Asc77.T7D.ctx_of_stand hs.stand hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hR⟩ := c.fuse_frame h.stand.cls hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hρ0R : (ρ 0).R = R₁ := hρ₀R
  have hρ1R : (ρ 1).R = R₂ := hρ₁R
  have hρ2R : (ρ 2).R = R₃ := hρ₂R
  have hρ3R : (ρ 3).R = R₄ := hρ₃R
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hzρ i) (hg i).1.1 (hg i).2
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hzρ 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hu0W : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hu2 : (g 0 * g 1) * (g 0 * g 1) = 1 := by
    calc (g 0 * g 1) * (g 0 * g 1) = (g 0 * g 0) * (g 1 * g 1) := by
          rw [mul_assoc, ← mul_assoc (g 1), ← hcomm _ (hgW 0) _ (hgW 1)]; group
      _ = 1 := by rw [hgsq 0, hgsq 1]; exact (hzρ 0).sq
  have hc2 : IsPGroup 2 (Subgroup.zpowers (g 0 * g 1)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hg0R₁ : g 0 ∈ R₁ := by simpa [hρ0R] using hgR 0
  have hg1R₂ : g 1 ∈ R₂ := by simpa [hρ1R] using hgR 1
  have hR₃C : R₃ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c13 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c23 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hR₄C : R₄ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c14 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c24 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hcK₃ : g 0 * g 1 ∈ trivialOnQuot K₃ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₃).mpr ⟨R₃, h3, hR₃C⟩
  have hcK₄ : g 0 * g 1 ∈ trivialOnQuot K₄ :=
    (Q3T8.Asc77.ExactLayer.mem_trivialOnQuot_iff_exists_sylow hΩ hc2 hK₄Ω).mpr ⟨R₄, h4, hR₄C⟩
  have hex₃ : IsSylow2In R₃ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₃) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₃ hcK₃).mpr ⟨h3, hR₃C⟩
  have hex₄ : IsSylow2In R₄ (Q3T8.Asc77.ExactLayer.exactCore (g 0 * g 1) K₄) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2 hK₄Ω hcK₄).mpr ⟨h4, hR₄C⟩
  have hg2R₃ : g 2 ∈ R₃ := by simpa [hρ2R] using hgR 2
  have hg3R₄ : g 3 ∈ R₄ := by simpa [hρ3R] using hgR 3
  
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hr₂R : (ρ 2).r ∈ R₃ := by simpa [hρ2R] using (ρ 2).hr
  have hyC : y ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR₃C hr₂R) (hR σ.hr))
      (Subgroup.inv_mem _ (hR₃C hr₂R))
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid h.stand.cls (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have htz : t ≠ z := by
    intro h'
    have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
    have hperp : σ.K ∈ KPerp Ω K := by rw [hs.perp]; exact hσK
    rcases hperp with h'' | h''
    · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
    · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm
  have hperm : g 0 * g 1 * g 2 * g 3 = g 2 * g 3 * (g 0 * g 1) := by
    calc g 0 * g 1 * g 2 * g 3 = (g 0 * g 1) * (g 2 * g 3) := by group
      _ = (g 2 * g 3) * (g 0 * g 1) := hcomm _ hu0W _ (W.mul_mem (hgW 2) (hgW 3))
  have hRL₃ : R₃ ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le R₃ (mem_RSet_of_isSylow2In hK₃ h3) (le_iSup_of_le hR₃C le_rfl)
  have hRLσ : σ.R ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le σ.R σ.hR.1 (le_iSup_of_le hR le_rfl)
  have hyL : y ∈ rLayer Ω (g 0 * g 1) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRL₃ hr₂R) (hRLσ σ.hr))
      (Subgroup.inv_mem _ (hRL₃ hr₂R))
  
  have hKne : ∀ i, σ.K ≠ (ρ i).K := fun i h =>
    hfar i (by rw [c.img_eq_of_K_eq σ (ρ i) h])
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
  have hcomm_sq : ∀ (e x : G), e ∈ W → x ∈ W → σ.r * x * σ.r⁻¹ = e * x →
      σ.r * (x * x) * σ.r⁻¹ = e * e * (x * x) := by
    intro e x heW hxW hex
    have hcx : e * x = x * e := hcomm _ heW _ hxW
    calc σ.r * (x * x) * σ.r⁻¹ = (σ.r * x * σ.r⁻¹) * (σ.r * x * σ.r⁻¹) := by group
      _ = (e * x) * (e * x) := by rw [hex]
      _ = e * (x * e) * x := by group
      _ = e * (e * x) * x := by rw [hcx]
      _ = e * e * (x * x) := by group
  obtain ⟨e₁, he₁def⟩ : ∃ e : G, e = σ.r * g 1 * σ.r⁻¹ * (g 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e : G, e = σ.r * g 2 * σ.r⁻¹ * (g 2)⁻¹ := ⟨_, rfl⟩
  have he₁ : e₁ ∈ σ.K ⊓ W := he₁def ▸ c.comm_mem σ (ρ 1) (hKne 1) (hg 1).1
  have he₂ : e₂ ∈ σ.K ⊓ W := he₂def ▸ c.comm_mem σ (ρ 2) (hKne 2) (hg 2).1
  have hs₁ : σ.r * g 1 * σ.r⁻¹ = e₁ * g 1 := by rw [he₁def]; group
  have hs₂ : σ.r * g 2 * σ.r⁻¹ = e₂ * g 2 := by rw [he₂def]; group
  have hsz₁ : σ.r * z * σ.r⁻¹ = e₁ * e₁ * z := by
    have := hcomm_sq e₁ (g 1) he₁.2 (hgW 1) hs₁
    rwa [hgsq 1] at this
  have hsz₂ : σ.r * z * σ.r⁻¹ = e₂ * e₂ * z := by
    have := hcomm_sq e₂ (g 2) he₂.2 (hgW 2) hs₂
    rwa [hgsq 2] at this
  have hee : e₁ * e₁ = e₂ * e₂ := mul_right_cancel (hsz₁.symm.trans hsz₂)
  
  have hcσ : e₁ * e₂⁻¹ ∈ σ.K := σ.K.mul_mem he₁.1 (σ.K.inv_mem he₂.1)
  have hcc : (e₁ * e₂⁻¹) * (e₁ * e₂⁻¹) = 1 := by
    have h12 : e₂⁻¹ * e₁ = e₁ * e₂⁻¹ := hcomm _ (W.inv_mem he₂.2) _ he₁.2
    calc (e₁ * e₂⁻¹) * (e₁ * e₂⁻¹) = e₁ * (e₂⁻¹ * e₁) * e₂⁻¹ := by group
      _ = e₁ * (e₁ * e₂⁻¹) * e₂⁻¹ := by rw [h12]
      _ = (e₁ * e₁) * (e₂⁻¹ * e₂⁻¹) := by group
      _ = (e₂ * e₂) * (e₂⁻¹ * e₂⁻¹) := by rw [hee]
      _ = 1 := by group
  have hc01 := ht.unique _ hcσ hcc
  
  have hr₂ : ∀ i : Fin 4, i ≠ 2 → (ρ 2).r * g i = g i * (ρ 2).r := fun i hi =>
    c.centralizes (ρ 2) (ρ i) (hnbrρ 2 i (Ne.symm hi)) (hg i).1
  have hr₂fix : ∀ i : Fin 4, i ≠ 2 → (ρ 2).r * g i * (ρ 2).r⁻¹ = g i := fun i hi => by
    rw [hr₂ i hi]; group
  have hr₂g2 : (ρ 2).r * g 2 * (ρ 2).r⁻¹ = (g 2)⁻¹ := c.conj_inv (ρ 2) (hg 2).1
  have hA1 : (ρ 2).r⁻¹ * g 1 * (ρ 2).r = g 1 := by
    have h1' := hr₂ 1 (by decide)
    calc (ρ 2).r⁻¹ * g 1 * (ρ 2).r = (ρ 2).r⁻¹ * (g 1 * (ρ 2).r) := by group
      _ = (ρ 2).r⁻¹ * ((ρ 2).r * g 1) := by rw [h1']
      _ = g 1 := by group
  have hB2 : (ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r = g 2 := by
    calc (ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r
        = (ρ 2).r⁻¹ * ((ρ 2).r * g 2 * (ρ 2).r⁻¹) * (ρ 2).r := by rw [hr₂g2]
      _ = g 2 := by group
  have hA2 : (ρ 2).r⁻¹ * g 2 * (ρ 2).r = (g 2)⁻¹ := by
    calc (ρ 2).r⁻¹ * g 2 * (ρ 2).r = ((ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r)⁻¹ := by group
      _ = (g 2)⁻¹ := by rw [hB2]
  have hA : (ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r = g 1 * (g 2)⁻¹ := by
    calc (ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r
        = ((ρ 2).r⁻¹ * g 1 * (ρ 2).r) * ((ρ 2).r⁻¹ * g 2 * (ρ 2).r) := by group
      _ = g 1 * (g 2)⁻¹ := by rw [hA1, hA2]
  have hB' : σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹ = (e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹) := by
    have hx : (g 2)⁻¹ * e₂⁻¹ = e₂⁻¹ * (g 2)⁻¹ :=
      hcomm _ (W.inv_mem (hgW 2)) _ (W.inv_mem he₂.2)
    have hy' : g 1 * e₂⁻¹ = e₂⁻¹ * g 1 := hcomm _ (hgW 1) _ (W.inv_mem he₂.2)
    calc σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹
        = (σ.r * g 1 * σ.r⁻¹) * (σ.r * g 2 * σ.r⁻¹)⁻¹ := by group
      _ = (e₁ * g 1) * (e₂ * g 2)⁻¹ := by rw [hs₁, hs₂]
      _ = e₁ * g 1 * ((g 2)⁻¹ * e₂⁻¹) := by group
      _ = e₁ * g 1 * (e₂⁻¹ * (g 2)⁻¹) := by rw [hx]
      _ = e₁ * (g 1 * e₂⁻¹) * (g 2)⁻¹ := by group
      _ = e₁ * (e₂⁻¹ * g 1) * (g 2)⁻¹ := by rw [hy']
      _ = (e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹) := by group
  have hrfix : (ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹ = g 1 * g 2 := by
    calc (ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹
        = ((ρ 2).r * g 1 * (ρ 2).r⁻¹) * ((ρ 2).r * g 2 * (ρ 2).r⁻¹)⁻¹ := by group
      _ = g 1 * g 2 := by rw [hr₂fix 1 (by decide), hr₂g2, inv_inv]
  have hyw : y * (g 1 * g 2) * y⁻¹ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * (g 1 * g 2) := by
    rw [hy]
    calc ((ρ 2).r * σ.r * (ρ 2).r⁻¹) * (g 1 * g 2) * ((ρ 2).r * σ.r * (ρ 2).r⁻¹)⁻¹
        = (ρ 2).r * (σ.r * ((ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r) * σ.r⁻¹) * (ρ 2).r⁻¹ := by group
      _ = (ρ 2).r * (σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹) * (ρ 2).r⁻¹ := by rw [hA]
      _ = (ρ 2).r * ((e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹)) * (ρ 2).r⁻¹ := by rw [hB']
      _ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * ((ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹) := by
          group
      _ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * (g 1 * g 2) := by rw [hrfix]
  have hg2inv : (g 2)⁻¹ = g 2 * z := by
    have h1' : (g 2)⁻¹ = z⁻¹ * g 2 := by
      have : z = g 2 * g 2 := (hgsq 2).symm
      rw [this]; group
    rw [h1', hzi]
    exact hcomm _ hzW _ (hgW 2)
  have hrt : (ρ 2).r * t * (ρ 2).r⁻¹ = t * z := by
    rw [hrel]
    calc (ρ 2).r * (g 0 * g 1 * g 2 * g 3) * (ρ 2).r⁻¹
        = ((ρ 2).r * g 0 * (ρ 2).r⁻¹) * ((ρ 2).r * g 1 * (ρ 2).r⁻¹) *
            ((ρ 2).r * g 2 * (ρ 2).r⁻¹) * ((ρ 2).r * g 3 * (ρ 2).r⁻¹) := by group
      _ = g 0 * g 1 * (g 2)⁻¹ * g 3 := by
          rw [hr₂fix 0 (by decide), hr₂fix 1 (by decide), hr₂g2, hr₂fix 3 (by decide)]
      _ = g 0 * g 1 * (g 2 * z) * g 3 := by rw [hg2inv]
      _ = g 0 * g 1 * g 2 * (z * g 3) := by group
      _ = g 0 * g 1 * g 2 * (g 3 * z) := by rw [hcomm z hzW (g 3) (hgW 3)]
      _ = (g 0 * g 1 * g 2 * g 3) * z := by group
  have hw : y * (g 1 * g 2) * y⁻¹ = g 1 * g 2 ∨
      y * (g 1 * g 2) * y⁻¹ = (t * z) * (g 1 * g 2) := by
    rcases hc01 with h0 | h0
    · left
      rw [hyw, h0]
      group
    · right
      rw [hyw, h0, hrt]
  
  have hKdat : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z (g 0) (g 1) (g 2) :=
    Q3T8.Asc77.S22.hyp22Setting_of_sylows hs.stand hz hs.hK' hs.hne hs.perp hs.hK₃ hs.hK₃K hs.hK₃K'
        h1 h2
      h3 c12 c13 c23 hg0R₁ hg1R₂ hg2R₃ (hg 0).2 (hg 1).2 (hg 2).2
  have hbig : S22.Big Ω K := Q3T8.Asc77.S22.Big.of_four hs hK₄ h41 h42 h43
  have hyα : y ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({g 0 * g 1, z} : Set G)) : Set G) :=
    Q3T8.Asc77.C22P.mem_normalizer_alpha_of_frame hKdat hbig
        (Subgroup.mem_centralizer_singleton_iff.mp hyC) hyz
      (hcomm z hzW t htW) ht.sq (hcomm t htW _ (W.mul_mem (hgW 1) (hgW 2))) hw
  refine ⟨g 0, g 1, by simpa [hρ0K] using (hg 0).1.1, by simpa [hρ1K] using (hg 1).1.1,
    (hg 0).2, (hg 1).2, hcomm _ (hgW 0) _ (hgW 1), ?_⟩
  refine ⟨R₃, R₄, g 2, g 3, y, h3, h4, c34, hR₃C, hR₄C, hg2R₃, hg3R₄, (hg 2).2, (hg 3).2,
    hgsq 2, hgsq 3, hyL, ?_, ?_, ?_, hyα⟩
  · rw [hyz, hrel, hperm]
  · rw [← hperm, ← hrel]
    exact htz
  · exact hcomm _ hzW _ (W.mul_mem (W.mul_mem (hgW 2) (hgW 3)) hu0W)
end Frame
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Datum
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem exists_invert
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    ∃ (R R' R₃ : Subgroup G) (j₁ j₂ : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧
      IsSylow2In R₃ K₃ ∧ u₁ ∈ R ∧ u₂ ∈ R' ∧ u₃ ∈ R₃ ∧ Commutes R R' ∧ Commutes R R₃ ∧
      Commutes R' R₃ ∧ j₁ ∈ R ∧ j₂ ∈ R' ∧ j₁ * u₁ * j₁⁻¹ = u₁⁻¹ ∧ j₂ * u₂ * j₂⁻¹ = u₂⁻¹ ∧
      j₁ * j₁ = z ∧ j₂ * j₂ = z := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hqR : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In h.stand.mem hR)
  have hqR' : IsQuatSub R' :=
    hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In h.hK'.1 hR')
  obtain ⟨j₁, hj₁, e₁, n₁, s₁⟩ := isQuatSub_exists_inv hqR h₁
  obtain ⟨j₂, hj₂, e₂, n₂, s₂⟩ := isQuatSub_exists_inv hqR' h₂
  have hz₁ : j₁ * j₁ = z := by
    rcases h.hz.unique (j₁ * j₁) (K.mul_mem (hR.1 hj₁) (hR.1 hj₁)) s₁ with h1 | h1
    · exact absurd h1 n₁
    · exact h1
  have hz₂ : j₂ * j₂ = z := by
    rcases h.hzK'.unique (j₂ * j₂) (K'.mul_mem (hR'.1 hj₂) (hR'.1 hj₂)) s₂ with h1 | h1
    · exact absurd h1 n₂
    · exact h1
  exact ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23, hj₁, hj₂, e₁, e₂, hz₁, hz₂⟩
end Datum
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Ab

@[expose] def Hyp22FourthTwinAb
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      dComp Ω K = dstarComp Ω K →
        ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃

theorem hyp22FourthTwin_of_ab
    (h : Q3T8.Asc77.S22.Hyp22FourthTwinAb) : Q3T8.Asc77.Hyp22FourthTwin
    := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hd
  by_cases heq : dComp Ω K = dstarComp Ω K
  · exact h G Ω K K' K₃ z u₁ u₂ u₃ hd heq
  · have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hd.stand.modU, hd.stand.cls, hd.stand.aEmpty⟩
    exact Q3T8.Asc77.T7V.exists_fourth_twin hd
      (fun W hW _ => Q3T8.Asc77.thompsonGraphAll G Ω hP hd.stand.mem heq hW)
end Ab
section Wire

theorem hyp22SettingWyl_of_ab [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h : Q3T8.Asc77.S22.Hyp22FourthTwinAb) :
    Q3T8.Asc77.T7V.Hyp22SettingWyl :=
  Q3T8.Asc77.S22.hyp22SettingWyl_of_fourthTwin (Q3T8.Asc77.S22.hyp22FourthTwin_of_ab h)
end Wire
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Conj
variable {G : Type} [Group G] [Finite G]

theorem FrameData.conj
    {Ω : Set (Subgroup G)} {K₃ K₄ : Subgroup G} {z c : G} {R R' : Subgroup G}
    {b b' y : G} (hΩ : ConjInvariant Ω) (hF : Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z c R R' b b' y) {n
        : G}
    (hn₃ : conjSub n K₃ = K₃) (hn₄ : conjSub n K₄ = K₄) (hnz : n * z * n⁻¹ = z) :
    Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (n * c * n⁻¹) (conjSub n R) (conjSub n R') (n * b * n⁻¹) (n
        * b' * n⁻¹)
      (n * y * n⁻¹) := by
  have hnz' : n⁻¹ * z * n = z := by
    have := congrArg (fun x => n⁻¹ * x * n) hnz
    simpa [mul_assoc] using this.symm
  have ho : ∀ x : G, orderOf (n * x * n⁻¹) = orderOf x := fun x =>
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  refine ⟨?_, ?_, hF.hRR'.conjSub n, conjSub_le_centralizer_conj n hF.hRc,
    conjSub_le_centralizer_conj n hF.hR'c, conj_mem_conjSub hF.hbR, conj_mem_conjSub hF.hb'R',
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn₃]; exact hF.hR.conj n
  · rw [← hn₄]; exact hF.hR'.conj n
  · rw [ho, hF.hb4]
  · rw [ho, hF.hb'4]
  · calc n * b * n⁻¹ * (n * b * n⁻¹) = n * (b * b) * n⁻¹ := by group
      _ = z := by rw [hF.hbz, hnz]
  · calc n * b' * n⁻¹ * (n * b' * n⁻¹) = n * (b' * b') * n⁻¹ := by group
      _ = z := by rw [hF.hb'z, hnz]
  · rw [Q3T8.Asc77.ExactLayer.exactLayer_conj hΩ n c]
    exact conj_mem_conjSub hF.hy
  · calc n * y * n⁻¹ * z * (n * y * n⁻¹)⁻¹ = n * y * (n⁻¹ * z * n) * y⁻¹ * n⁻¹ := by group
      _ = n * (y * z * y⁻¹) * n⁻¹ := by rw [hnz']; group
      _ = n * (b * b' * c) * n⁻¹ := by rw [hF.hyz]
      _ = n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹) := by group
  · intro h
    apply hF.htz
    have h2 : b * b' * c = n⁻¹ * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * n := by group
    rw [h2, h, hnz']
  · calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) =
        n * (z * (b * b' * c)) * n⁻¹ := by
          calc z * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹))
              = (n * z * n⁻¹) * (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) := by rw [hnz]
            _ = n * (z * (b * b' * c)) * n⁻¹ := by group
      _ = n * ((b * b' * c) * z) * n⁻¹ := by rw [hF.hzt]
      _ = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * z := by
          calc n * ((b * b' * c) * z) * n⁻¹
              = (n * b * n⁻¹ * (n * b' * n⁻¹) * (n * c * n⁻¹)) * (n * z * n⁻¹) := by group
            _ = _ := by rw [hnz]
end Conj
section Frame
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem frame_at_alpha [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z
    u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ (R R' : Subgroup G) (b b' y : G), Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b' y ∧
      y ∈ Subgroup.normalizer
        (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨a, a', ha, ha', ha4, ha'4, haa', R, R', b, b', y, hR, hR', hRR', hRc, hR'c, hbR, hb'R',
    hb4, hb'4, hbz, hb'z, hy, hyz, htz, hzt, hyα⟩ := Q3T8.Asc77.C22P.fuseFrame_alpha hs hK₄ h41 h42
        h43 hμ
  have haz : a * a = z := sq_eq_involution_of_orderOf_four hz ha ha4
  have ha'z : a' * a' = z := sq_eq_involution_of_orderOf_four hz' ha' ha'4
  have haa2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a' a a', ← haa']; group
      _ = 1 := by rw [haz, ha'z]; exact hz.sq
  have hy' : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (a * a') := by
    exact Q3T8.Asc77.rLayer_le_exactLayer hΩ haa2 hy
  have hF : Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (a * a') R R' b b' y :=
    ⟨hR, hR', hRR', hRc, hR'c, hbR, hb'R', hb4, hb'4, hbz, hb'z, hy', hyz, htz, hzt⟩
  have hKK' : K ≤ trivialOnQuot K' := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK' hs.hne.symm hz
      hz'
  have hK'K : K' ≤ trivialOnQuot K := Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK hs.hne hz' hz
  obtain ⟨c, hc, hconj⟩ := Q3T8.Asc77.T7V.exists_conj_pair hΩ hK hK' hs.hne.symm hz hz' hKK' hK'K
      ha ha'
    hs.hu₁.1 hs.hu₂.1 ha4 ha'4 hs.hu₁.2 hs.hu₂.2 haa' hs.comm₁₂
  have nK₃ : K ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₃ hs.hK₃K.symm hz hz₃
  have nK₃' : K' ≤ Subgroup.normalizer (K₃ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₃ hs.hK₃K'.symm hz' hz₃
  have nK₄ : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK hK₄Ω h41.symm hz hz₄
  have nK₄' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK₄Ω h42.symm hz' hz₄
  have hc₃ : conjSub c K₃ = K₃ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₃ nK₃' hc)
  have hc₄ : conjSub c K₄ = K₄ := mem_normalizer_iff_conjSub_eq.mp (sup_le nK₄ nK₄' hc)
  have hcz : c * z * c⁻¹ = z := by
    have hle : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem hx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz'.commute_of_mem hx).symm
    have h1 : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
    rw [h1]
    group
  have hF' := hF.conj hΩ.conjInvariant hc₃ hc₄ hcz
  rw [hconj] at hF'
  refine ⟨conjSub c R, conjSub c R', c * b * c⁻¹, c * b' * c⁻¹, c * y * c⁻¹, hF', ?_⟩
  
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))) := by
    have e := T7A.conjSub_closure_pair c (a * a') z
    rw [hcz, hconj] at e
    rw [← e, alphaOf_conjSub]
  rw [hα, mem_normalizer_iff_conjSub_eq]
  have h1 := mem_normalizer_iff_conjSub_eq.mp hyα
  calc conjSub (c * y * c⁻¹) (conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))))
      = conjSub c (conjSub y (conjSub c⁻¹ (conjSub c
          (alphaOf (Subgroup.closure ({a * a', z} : Set G)))))) := by
        rw [conjSub_mul, conjSub_mul]
    _ = conjSub c (alphaOf (Subgroup.closure ({a * a', z} : Set G))) := by
        rw [conjSub_inv_conjSub, h1]
end Frame
end C22P
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

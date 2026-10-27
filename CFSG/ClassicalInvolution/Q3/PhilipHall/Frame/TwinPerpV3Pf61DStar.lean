module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu
public import CFSG.ClassicalInvolution.Asc77.AscC22G2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2208
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.C22G

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section DStar



variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_conj_of_far' (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {H : Subgroup G} (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hY : ∀ (L₃ : Subgroup G) (x₁ x₂ x₃ : G), A7T22.Hyp22G Ω K K' L₃ z x₁ x₂ x₃ →
      rLayer Ω (x₁ * x₂) ≤ H)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hzW : z ∈ W) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {w : G} (hw : IsUniqueInvolution J w) (hwW : w ∈ W) :
    ∃ y ∈ H, y * z * y⁻¹ = w := by
  have hΩ : HypOmegaGen Ω := hd.hyp
  have hK : K ∈ Ω := hd.mem
  have hK' : K' ∈ Ω := hd.hK'.1
  have hz : IsUniqueInvolution K z := hd.hz
  have hz' : IsUniqueInvolution K' z := hd.hzK'
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ₀, hρ₀⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP.cls hK hz hzW
  obtain ⟨ρ₁, hρ₁⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP.cls hK' hz' hzW
  obtain ⟨σ, hσ⟩ := Q3.TL4.exists_rep_of_involution_mem_gen c hP.cls hJ hw hwW
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hK hz
  have hJK : J ≠ K := fun h => hJt (h ▸ hKtw)
  have hJK' : J ≠ K' := fun h => hJt (h ▸ hd.hK')
  have hJnot : J ∉ omegaNbr Ω K := by
    intro h
    have h1 : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h
    rw [hperp] at h1
    exact hJt h1
  have hKnot : K ∉ omegaNbr Ω J := fun h =>
    hJnot (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hK h)
  have hz₀ : IsUniqueInvolution ρ₀.K z := hρ₀ ▸ hz
  have hz₁ : IsUniqueInvolution ρ₁.K z := hρ₁ ▸ hz'
  have hw' : IsUniqueInvolution σ.K w := hσ ▸ hw
  have hσ₀ : σ.K ≠ ρ₀.K := by rw [hσ, hρ₀]; exact hJK
  have hσ₁ : σ.K ≠ ρ₁.K := by rw [hσ, hρ₁]; exact hJK'
  have hn₀ : ρ₀.K ∉ omegaNbr Ω σ.K := by rw [hσ, hρ₀]; exact hKnot
  have hn₀' : σ.K ∉ omegaNbr Ω ρ₀.K := by rw [hσ, hρ₀]; exact hJnot
  obtain ⟨g₀, hg₀, ho₀⟩ := Q3T8.Asc77.C22G.exists_orderOf_four_mem_inf_W c ρ₀
  obtain ⟨g₁, hg₁, ho₁⟩ := Q3T8.Asc77.C22G.exists_orderOf_four_mem_inf_W c ρ₁
  obtain ⟨g₁', hg₁', ho₁', hRC⟩ :=
    Q3T8.Asc77.C22G.exists_centralized_pair c ρ₀ ρ₁ σ hz₀ hz₁ hw' hσ₀ hσ₁ hn₀ hg₀ ho₀ hg₁ ho₁
  have hg₀K : g₀ ∈ K := hρ₀ ▸ hg₀.1
  have hg₁K' : g₁' ∈ K' := hρ₁ ▸ hg₁'.1
  have hcomm : g₀ * g₁' = g₁' * g₀ := c.comm_W g₀ hg₀.2 g₁' hg₁'.2
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK' hd.hne.symm hz hz'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK' hK hd.hne hz' hz
  have hAW : Subgroup.closure ({g₀, g₁'} : Set G) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hg₀.2
    · exact hg₁'.2
  have hA2 : IsPGroup 2 (Subgroup.closure ({g₀, g₁'} : Set G)) :=
    (Thompson.isPGroup_of_mem_WSet hW).to_le hAW
  have hAK : Subgroup.closure ({g₀, g₁'} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.le_normalizer hg₀K
    · exact hK'N hg₁K'
  have hAK' : Subgroup.closure ({g₀, g₁'} : Set G) ≤ Subgroup.normalizer (K' : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hKN' hg₀K
    · exact Subgroup.le_normalizer hg₁K'
  obtain ⟨R₁, R₂, hR₁, hR₂, hc12, -, -, h2grp⟩ := TwinFrameTgt.exists_twinSylow_normalized_gen hΩ hK hz hd.hK'
    hd.hne hA2 hAK hAK'
  have hg₀A : g₀ ∈ Subgroup.closure ({g₀, g₁'} : Set G) := Subgroup.subset_closure (by simp)
  have hg₁A : g₁' ∈ Subgroup.closure ({g₀, g₁'} : Set G) := Subgroup.subset_closure (by simp)
  have hg₀R₁ : g₀ ∈ R₁ := by
    have hQ2 : IsPGroup 2 ↥(R₁ ⊔ Subgroup.zpowers g₀) :=
      h2grp.to_le (sup_le (le_sup_right.trans le_sup_left)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg₀A))))
    have := hR₁.2.2 _ (sup_le hR₁.1 (Subgroup.zpowers_le.mpr hg₀K)) hQ2 le_sup_left
    have h := (Subgroup.mem_sup_right (Subgroup.mem_zpowers g₀) : g₀ ∈ R₁ ⊔ Subgroup.zpowers g₀)
    rwa [this] at h
  have hg₁R₂ : g₁' ∈ R₂ := by
    have hQ2 : IsPGroup 2 ↥(R₂ ⊔ Subgroup.zpowers g₁') :=
      h2grp.to_le (sup_le le_sup_right
        (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg₁A))))
    have := hR₂.2.2 _ (sup_le hR₂.1 (Subgroup.zpowers_le.mpr hg₁K')) hQ2 le_sup_left
    have h := (Subgroup.mem_sup_right (Subgroup.mem_zpowers g₁') : g₁' ∈ R₂ ⊔ Subgroup.zpowers g₁')
    rwa [this] at h
  obtain ⟨L₃, w₃, hd'⟩ := hd.exists_datum_of_pair hKtw hd.hK' hd.hne hR₁ hR₂ hc12 hg₀R₁ hg₁R₂
    ho₀ ho₁'
  have hLayer : rLayer Ω (g₀ * g₁') ≤ H := hY L₃ g₀ g₁' w₃ hd'
  have hσR : σ.R ≤ rLayer Ω (g₀ * g₁') :=
    le_rLayer_of_le_centralizer (mem_RSet_of_isSylow2In σ.hK σ.hRK) hRC
  have hσrA : σ.r ∈ H := hLayer (hσR σ.hr)
  have hρrA : ρ₀.r ∈ H := by
    have : ρ₀.r ∈ K := hρ₀ ▸ ρ₀.hRK.1 ρ₀.hr
    refine hCz ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz.commute_of_mem this).symm
  refine ⟨ρ₀.r * σ.r, H.mul_mem hρrA hσrA, ?_⟩
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

theorem exists_conj_of_dstarComp' (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {H : Subgroup G} (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hY : ∀ (L₃ : Subgroup G) (x₁ x₂ x₃ : G), A7T22.Hyp22G Ω K K' L₃ z x₁ x₂ x₃ →
      rLayer Ω (x₁ * x₂) ≤ H) :
    ∀ J ∈ dstarComp Ω K, ∃ w : G, IsUniqueInvolution J w ∧ ∃ y ∈ H, y * z * y⁻¹ = w := by
  have hΩ : HypOmegaGen Ω := hd.hyp
  have hK : K ∈ Ω := hd.mem
  have hz : IsUniqueInvolution K z := hd.hz
  have key : ∀ J : Subgroup G, Relation.ReflTransGen (dstarAdj Ω) K J →
      ∃ w : G, IsUniqueInvolution J w ∧ ∃ y ∈ H, y * z * y⁻¹ = w := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨z, hz, 1, H.one_mem, by group⟩
    | @tail b c hpre hstep ih =>
      obtain ⟨wb, hwb, y, hy, hyz⟩ := ih
      have hbΩ : b ∈ Ω := (T3.mem_dstarComp_symm hK hpre).1
      obtain ⟨hcΩ, hor⟩ := hstep
      have hcb : c ∈ omegaStarNbr Ω b := by
        rcases hor with h | h
        · exact h
        · exact Q3.Q3T6.Mu.omegaStarNbr_symm hΩ hcΩ hbΩ h
      have hM : conjSub y⁻¹ b ∈ twinSet Ω K :=
        conjSub_mem_twinSet hΩ.conjInvariant hz hbΩ hwb hyz
      have hMΩ : conjSub y⁻¹ b ∈ Ω := hM.1
      have hzM : IsUniqueInvolution (conjSub y⁻¹ b) z := isUniqueInvolution_of_mem_twinSet hz hM
      have hJ'' : conjSub y⁻¹ c ∈ omegaStarNbr Ω (conjSub y⁻¹ b) :=
        omegaStarNbr_conj hΩ.conjInvariant hcb y⁻¹
      have hJ''Ω : conjSub y⁻¹ c ∈ Ω := hΩ.conjInvariant y⁻¹ c hcΩ
      obtain ⟨w', hw'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hcΩ
      have hw'' : IsUniqueInvolution (conjSub y⁻¹ c) (y⁻¹ * w' * y⁻¹⁻¹) := hw'.conj y⁻¹
      refine ⟨w', hw', ?_⟩
      by_cases hJt : conjSub y⁻¹ c ∈ twinSet Ω K
      · have h1 := isUniqueInvolution_of_mem_twinSet hz hJt
        have h2 : z = y⁻¹ * w' * y⁻¹⁻¹ := h1.eq hw''
        exact ⟨y, hy, by rw [h2]; group⟩
      · obtain ⟨W₁, hW₁, R, hRD, T, hTD, hRM, hTJ⟩ :=
          Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hMΩ hJ''
        have hzW : z ∈ W₁ := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hMΩ hRD hRM hzM).2
        have hwW : y⁻¹ * w' * y⁻¹⁻¹ ∈ W₁ :=
          (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hJ''Ω hTD hTJ hw'').2
        obtain ⟨y'', hy'', hy''z⟩ := exists_conj_of_far' hP hd hperp hCz hY hW₁ hzW hJ''Ω hJt hw''
          hwW
        refine ⟨y * y'', H.mul_mem hy hy'', ?_⟩
        calc y * y'' * z * (y * y'')⁻¹ = y * (y'' * z * y''⁻¹) * y⁻¹ := by group
          _ = y * (y⁻¹ * w' * y⁻¹⁻¹) * y⁻¹ := by rw [hy''z]
          _ = w' := by group
  intro J hJ
  exact key J hJ

end DStar

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

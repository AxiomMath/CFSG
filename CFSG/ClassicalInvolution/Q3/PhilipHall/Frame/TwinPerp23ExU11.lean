module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU10
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf17Perp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf12Vertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1c
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Fin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



open CFSG.ClassicalInvolution.Balance

section U11

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem gug_mem_B (hc : P23Cfg n Y R S t K' W u e g) :
    g * u * g⁻¹ ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
  have hB : ∀ {a : Y}, a ∈ ({u * e, u, t} : Set Y) → a ∈ Subgroup.closure ({u * e, u, t} : Set Y) :=
    fun h => Subgroup.subset_closure h
  have hue : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := hB (by simp)
  have hu : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := hB (by simp)
  have ht : t ∈ Subgroup.closure ({u * e, u, t} : Set Y) := hB (by simp)
  obtain ⟨v', hv', hzt⟩ := z_cases hc
  have hv'B : v' ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rcases hzt with h | h
    · rw [← h]; exact ht
    · have : v' = u⁻¹ * t := by rw [h]; group
      rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) ht
  rcases hv' with h | h
  · rw [← h]; exact hv'B
  · have : g * u * g⁻¹ = v' * (u * e)⁻¹ := by rw [h]; group
    rw [this]; exact Subgroup.mul_mem _ hv'B (Subgroup.inv_mem _ hue)

theorem t_mem_closure_gug (hc : P23Cfg n Y R S t K' W u e g) :
    t ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := by
  have hB : ∀ {a : Y}, a ∈ ({u * e, g * u * g⁻¹, u} : Set Y) →
      a ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := fun h => Subgroup.subset_closure h
  have hue : u * e ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := hB (by simp)
  have hg : g * u * g⁻¹ ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := hB (by simp)
  have hu : u ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := hB (by simp)
  obtain ⟨v', hv', hzt⟩ := z_cases hc
  have hv'B : v' ∈ Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := by
    rcases hv' with h | h
    · rw [h]; exact hg
    · rw [h]; exact Subgroup.mul_mem _ hg hue
  rcases hzt with h | h
  · rw [h]; exact hv'B
  · rw [h]; exact Subgroup.mul_mem _ hu hv'B

theorem p23_hyp51_vertices (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hT : TwinThmE.T4Supply) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) :
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) t ∧
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) (u * e) ∧
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) e ∧
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) (e * t) ∧
    Hyp51At (Subgroup.closure ({u * e, u, t} : Set Y)) u := by
  classical
  set B := Subgroup.closure ({u * e, u, t} : Set Y) with hBdef
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hsolv : ∀ M ∈ Om R, Group.IsSolvable ↥M :=
    fun M hM => CFSG.ClassicalInvolution.Q8P.P24.isSolvable_of_quot2 (h2 M hM)
  have hBab := B_isElemAbelian hc
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hBm : ∀ {a : Y}, a ∈ ({u * e, u, t} : Set Y) → a ∈ B := fun h => Subgroup.subset_closure h
  have hueB : u * e ∈ B := hBm (by simp)
  have huB : u ∈ B := hBm (by simp)
  have htB : t ∈ B := hBm (by simp)
  have heB : e ∈ B := by
    have : e = u⁻¹ * (u * e) := by group
    rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huB) hueB
  have hguB := gug_mem_B hc
  have he1 := hd.he1
  have hu1 := hd.hu1
  have hut : u ≠ t := hd.huz
  have het : e ≠ t := fun h => e_not_mem_sup hc (h ▸ Subgroup.mem_sup_left hz.mem)
  have ht1 := hz.ne_one
  have hEIH : TwinThmE.EIHAll (Nat.card Y) := by
    rw [hC.card]; intros; exact ⟨hcit, hP⟩
  have H : CFSG.ClassicalInvolution.Q8P.P24.Hyp51TwinInnerAt (Om R) :=
    CFSG.ClassicalInvolution.Q8P.P24.hyp51TwinInnerPerp_of_model
    TwinCentRes.modelFactSp62 hD4 hM12 (hT n hcit hP) Y R S t hc.std.perp
  have hst := CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC
  have hne' : K' ≠ tightCore R := hc.std.hne
  have hR₁t : ∀ x ∈ R₁, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₁.1 hx))
  have hR₁'t : ∀ x ∈ R₁', x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' (hR₁'.1 hx))
  have hR₁et : R₁ ≤ Subgroup.centralizer ({e * t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hx)
    calc x * (e * t) = (x * e) * t := by group
      _ = (e * x) * t := by rw [h1]
      _ = e * (x * t) := by group
      _ = e * (t * x) := by rw [hR₁t x hx]
      _ = (e * t) * x := by group
  have hR₁'et : R₁' ≤ Subgroup.centralizer ({e * t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hR₁'e hx)
    calc x * (e * t) = (x * e) * t := by group
      _ = (e * x) * t := by rw [h1]
      _ = e * (x * t) := by group
      _ = e * (t * x) := by rw [hR₁'t x hx]
      _ = (e * t) * x := by group
  have hb₁K : b₁ ∈ tightCore R := hR₁.1 hb₁R
  have hb'K : b' ∈ K' := hR₁'.1 hb'R'
  have hb₁R2 : IsPGroup 2 R₁ := hR₁.2.1
  have hb'R2 : IsPGroup 2 R₁' := hR₁'.2.1
  have v1 : Hyp51At B t :=
    hyp51At_of_twin_product hΩ hsolv hBab hK hK'Ω hz hz' htB huB ht1 hu1 hut hb₁K hb'K hub
  have hgcu := conj_cent_u hc hR₁e hR₁t
  have hgcu' := conj_cent_u hc hR₁'e hR₁'t
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hK'Ω
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hgug : g * u * g⁻¹ = (g * b₁ * g⁻¹) * (g * b' * g⁻¹) := by
    rw [hub]; group
  have hgb₁ : g * b₁ * g⁻¹ ∈ conjSub g (tightCore R) := conj_mem_conjSub hb₁K
  have hgb' : g * b' * g⁻¹ ∈ conjSub g K' := conj_mem_conjSub hb'K
  have hgu1 : g * u * g⁻¹ ≠ 1 := fun h => hu1 (by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group)
  have hgue : g * u * g⁻¹ ≠ u * e := by
    intro h
    apply hut
    rw [← hd.hgt] at h
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  have v2 : Hyp51At B (u * e) :=
    hyp51At_of_twin_product hΩ hsolv hBab hJ₁ hJ₂ hτ₁ hτ₂ hueB hguB (hτ₁.ne_one) hgu1 hgue
      hgb₁ hgb' hgug
  have hKe : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hK'e : K' ∈ tqMembers3 (Om R) e :=
    ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R₁', hR₁', hR₁'e⟩⟩
  have hKet : tightCore R ∈ tqMembers3 (Om R) (e * t) :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁et⟩⟩
  have hK'et : K' ∈ tqMembers3 (Om R) (e * t) :=
    ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R₁', hR₁', hR₁'et⟩⟩
  have hJ₁u : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hgcu⟩⟩
  have hJ₂u : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hgcu'⟩⟩
  have hBt : B = Subgroup.closure ({t, u, e} : Set Y) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact htB
      · exact huB
      · exact heB
  have hBet : B = Subgroup.closure ({t, u, e * t} : Set Y) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · have : e = (e * t) * t⁻¹ := by group
        have hh : e ∈ Subgroup.closure ({t, u, e * t} : Set Y) := by
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) hh
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact htB
      · exact huB
      · exact Subgroup.mul_mem _ heB htB
  have hBu : B = Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact t_mem_closure_gug hc
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact hueB
      · exact hguB
      · exact huB
  have hb₁e : b₁ ∈ TwinLayer.exactCore e (tightCore R) :=
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁e) hb₁R2 hb₁R
  have hb'e : b' ∈ TwinLayer.exactCore e K' := le_tightCore_of_isPGroup (le_inf hR₁'.1 hR₁'e) hb'R2 hb'R'
  have hb₁et : b₁ ∈ TwinLayer.exactCore (e * t) (tightCore R) :=
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁et) hb₁R2 hb₁R
  have hb'et : b' ∈ TwinLayer.exactCore (e * t) K' :=
    le_tightCore_of_isPGroup (le_inf hR₁'.1 hR₁'et) hb'R2 hb'R'
  have hgb₁u : g * b₁ * g⁻¹ ∈ TwinLayer.exactCore u (conjSub g (tightCore R)) :=
    le_tightCore_of_isPGroup (le_inf hR₃.1 hgcu) hR₃.2.1 (conj_mem_conjSub hb₁R)
  have hgb'u : g * b' * g⁻¹ ∈ TwinLayer.exactCore u (conjSub g K') :=
    le_tightCore_of_isPGroup (le_inf hR₃'.1 hgcu') hR₃'.2.1 (conj_mem_conjSub hb'R')
  have v3 : Hyp51At B e :=
    H hst hEIH h2 hK hK'Ω hne' hz hz' hKe hK'e hBab htB huB heB hBt he1 het.symm hu1 hut hd.hu2
      (by rw [hub]; exact Subgroup.mul_mem_sup hb₁e hb'e)
  have v4 : Hyp51At B (e * t) :=
    H hst hEIH h2 hK hK'Ω hne' hz hz' hKet hK'et hBab htB huB (Subgroup.mul_mem _ heB htB) hBet
      (fun h => het (by
        have h1 : e = t⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [h1, inv_eq_of_mul_eq_one_right hz.sq]))
      (fun h => he1 (by simpa using h.symm)) hu1 hut hd.hu2
      (by rw [hub]; exact Subgroup.mul_mem_sup hb₁et hb'et)
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hne'
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hgg : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  have v5 : Hyp51At B u :=
    H hst hEIH h2 hJ₁ hJ₂ hne₂ hτ₁ hτ₂ hJ₁u hJ₂u hBab hueB hguB huB hBu hu1
      (fun h => he1 (by simpa using h)) hgu1 hgue hgg
      (by rw [hgug]; exact Subgroup.mul_mem_sup hgb₁u hgb'u)
  exact ⟨v1, v2, v3, v4, v5⟩

end U11

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

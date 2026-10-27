module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf29ExitCases
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Alpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf53Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf66Class
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf67Print
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section LayerW

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem sigmaCentU_of_layer (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (h2g : ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKW : K ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)))
    (hlayer : ∀ J ∈ CoreAssembly.conjClass (tightCore R),
      J ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
        J ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R))) :
    Subgroup.centralizer ({u₁ * u₂} : Set Y) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hperp3 := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have hKtw : K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K₃ := by
    obtain ⟨-, z, hz, hz'⟩ := hd.hK₃
    exact ⟨hd.mem, z, hz', hz⟩
  have hKK₃ : K ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K₃ := by
    have hLp : K ∈ KPerp (CoreAssembly.conjClass (tightCore R)) K₃ := by rw [hperp3]; exact hKtw
    rcases Set.mem_insert_iff.mp hLp with h | h
    · rw [h]; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hd.mem, Or.inl
        (Q3.Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K₃ h)⟩
  have hcommTw : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J ≠ J' →
        ∀ a ∈ J', ∀ b ∈ J, a * b = b * a := by
    intro J hJ J' hJ' hne a ha b hb
    have hz1 : IsUniqueInvolution J t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ
    have hz2 : IsUniqueInvolution J' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hJ'
    have := A7T22.le_trivialOnQuot_of_twin hΩ hJ'.1 hJ.1 (Ne.symm hne) hz2 hz1 ha
    exact commute_of_trivialOnQuot (h2g J hJ.1) this hb
  have hK₃u : ∀ k ∈ K₃, k * (u₁ * u₂) = (u₁ * u₂) * k := by
    intro k hk
    have h1 : k * u₁ = u₁ * k :=
      (hcommTw K₃ hd.hK₃ K (mem_twinSet_self hd.mem hd.hz) hd.hK₃K u₁ hd.hu₁.1 k hk).symm
    have h2 : k * u₂ = u₂ * k :=
      (hcommTw K₃ hd.hK₃ K' hd.hK' hd.hK₃K' u₂ hd.hu₂.1 k hk).symm
    calc k * (u₁ * u₂) = (k * u₁) * u₂ := by group
      _ = (u₁ * k) * u₂ := by rw [h1]
      _ = u₁ * (k * u₂) := by group
      _ = u₁ * (u₂ * k) := by rw [h2]
      _ = (u₁ * u₂) * k := by group
  intro c hc
  have hcu : c * (u₁ * u₂) = (u₁ * u₂) * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hM : conjSub c K₃ ∈ CoreAssembly.conjClass (tightCore R) :=
    hΩ.conjInvariant c K₃ hd.hK₃.1
  have hMle : conjSub c K₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro m hm
    rw [mem_conjSub_iff] at hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hK₃u _ hm
    have hmk : m = c * (c⁻¹ * m * c) * c⁻¹ := by group
    have hcu' : c⁻¹ * (u₁ * u₂) = (u₁ * u₂) * c⁻¹ := by
      calc c⁻¹ * (u₁ * u₂) = c⁻¹ * (u₁ * u₂) * c * c⁻¹ := by group
        _ = c⁻¹ * (c * (u₁ * u₂)) * c⁻¹ := by rw [hcu]; group
        _ = (u₁ * u₂) * c⁻¹ := by group
    symm
    calc (u₁ * u₂) * m = (u₁ * u₂) * (c * (c⁻¹ * m * c) * c⁻¹) := by rw [← hmk]
      _ = c * ((u₁ * u₂) * (c⁻¹ * m * c)) * c⁻¹ := by
          calc (u₁ * u₂) * (c * (c⁻¹ * m * c) * c⁻¹)
              = ((u₁ * u₂) * c) * (c⁻¹ * m * c) * c⁻¹ := by group
            _ = (c * (u₁ * u₂)) * (c⁻¹ * m * c) * c⁻¹ := by rw [hcu]
            _ = c * ((u₁ * u₂) * (c⁻¹ * m * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * m * c) * (u₁ * u₂)) * c⁻¹ := by rw [← h1]
      _ = (c * (c⁻¹ * m * c) * c⁻¹) * ((c * (u₁ * u₂)) * c⁻¹) := by group
      _ = m * ((u₁ * u₂) * c * c⁻¹) := by rw [← hmk, hcu]
      _ = m * (u₁ * u₂) := by group
  have hMW := hlayer _ hM hMle
  have hMK : conjSub c K₃ ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    TwinThmEW.mem_dstarComp_of_inf_W hΩ hW hd.mem hM hKW hMW
  have hKc : conjSub c K ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K :=
    hMK.trans (dstarComp_conj hΩ.conjInvariant hKK₃ c)
  exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hd.mem hKc

theorem dstarConn_of_centAdapted (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n)
    (hStd : V3Std n Y R S t K K' K₃ u₁ u₂ u₃)
    (hCent : ∀ (J' L₃ : Subgroup Y) (x₁ x₂ x₃ : Y),
      A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K J' L₃ t x₁ x₂ x₃ →
      (∃ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)), x₁ ∈ W' ∧ x₂ ∈ W') →
      Subgroup.centralizer ({x₁ * x₂} : Set Y) ≤
        sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := by
  intro J hJ
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hCore.hyp
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  have hq8 := q8_all_of_core hCore
  have htw : ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
      L ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K := by
    intro L hL
    have hLp : L ∈ KPerp (CoreAssembly.conjClass (tightCore R)) K := by rw [hperp]; exact hL
    rcases Set.mem_insert_iff.mp hLp with h | h
    · rw [h]; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨hL.1, Or.inl
        (Q3.Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K h)⟩
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤
      sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
    intro c hc
    have hcz : c * t * c⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [this]
        _ = t := by group
    have hL : conjSub c K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K :=
      ⟨hΩ.conjInvariant c K hd.mem, t, hd.hz, hcz ▸ hd.hz.conj c⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hd.mem (htw _ hL)
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have htrans : ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K,
      ∃ h' ∈ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K, conjSub h' K = J := by
    intro J hJ
    obtain ⟨g, hg⟩ := htr J (T3.mem_dstarComp_symm hd.mem hJ).1
    exact ⟨g, T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hd.mem (hg ▸ hJ), hg⟩
  obtain ⟨W, hWP, hKW⟩ := exists_printedWT hΩ hd.mem hd.hK' hd.hne
  obtain ⟨S₀, hWP'⟩ := hWP
  have hcentAll : TwinThmEW.CentAll (CoreAssembly.conjClass (tightCore R)) W
      (sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K) := by
    obtain ⟨R₀, -, -, hWΩ, -⟩ := id hWP'
    refine TwinThmEW.centAll_of_centAllK hΩ hd.mem hWΩ hKW htrans ?_
    intro x hx hU
    exact centralizersPrinted_of_adapted hCore.partIHypG hd hperp hq8 hCt hCent
      (WSet.conj hΩ.conjInvariant hWΩ x) hU
  have htop := TwinThmEW.twinThmEPrintedAllT_of_thmEQ8 hEW hcit hP Y R S t
    hStd.perp.core.toHyp K _ W S₀ hd.mem hWP' ⟨htrans, hcentAll.toPairs _⟩
  obtain ⟨g, hg⟩ := htr J hJ
  have hgH : g ∈ sigmaStarNorm (CoreAssembly.conjClass (tightCore R)) K := by
    rw [htop]; exact Subgroup.mem_top g
  have h1 := (mem_sigmaStarNorm_iff.mp hgH K).mp Relation.ReflTransGen.refl
  rwa [hg] at h1

@[expose] def V3LayerDW (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      (∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 ↥J) →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        K ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R)) → u₁ ∈ W → u₂ ∈ W →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        ∀ J ∈ CoreAssembly.conjClass (tightCore R),
          J ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) → J ⊓ W ∈ USet (CoreAssembly.conjClass (tightCore R))

@[expose] def V3DStarConnXu (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        ∀ L ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K,
        ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, L ≠ L' →
        ∀ a ∈ L ⊓ W', ∀ a' ∈ L' ⊓ W', orderOf a = 4 → orderOf a' = 4 →
          ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (a * a')),
            WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) = {V}) →
        ∀ J ∈ CoreAssembly.conjClass (tightCore R),
          J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K

theorem v3DStarConnXu_of_layerDW (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hL : V3LayerDW n) :
    V3DStarConnXu n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hUniq J hJ
  have hStd := hin.1
  have h2g := hin.2.2.2.1
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := (CoreData.of_S hStd.perp.core).hyp
  refine dstarConn_of_centAdapted hEW hcit hP hStd ?_ J hJ
  intro J' L₃ x₁ x₂ x₃ hd'' ⟨W', hW', hx₁, hx₂⟩
  have hStd'' : V3Std n Y R S t K J' L₃ x₁ x₂ x₃ :=
    ⟨hStd.perp, hStd.two, hStd.exit, hd'', hStd.wyl⟩
  have hKW' : K ⊓ W' ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
    obtain ⟨S₁, hS₁⟩ := (Thompson.isPGroup_of_mem_WSet hW').exists_le_sylow
    refine TwinThmEW.inf_W_mem_USet_of_card hΩ hW' hS₁ hd.mem ?_
    have h4 : Nat.card ↥(Subgroup.zpowers x₁) = 4 := by rw [Nat.card_zpowers, hd''.hu₁.2]
    have hle : Subgroup.zpowers x₁ ≤ K ⊓ (S₁ : Subgroup Y) :=
      le_inf (Subgroup.zpowers_le.mpr hd''.hu₁.1) (Subgroup.zpowers_le.mpr (hS₁ hx₁))
    have := Subgroup.card_le_of_le hle
    omega
  have hW'' := hUniq W' hW' K (mem_twinSet_self hd.mem hd.hz) J' hd''.hK' (Ne.symm hd''.hne)
    x₁ ⟨hd''.hu₁.1, hx₁⟩ x₂ ⟨hd''.hu₂.1, hx₂⟩ hd''.hu₁.2 hd''.hu₂.2
  exact sigmaCentU_of_layer hStd'' h2g hW' hKW'
    (hL Y R S t K J' L₃ x₁ x₂ x₃ hStd'' h2g W' hW' hKW' hx₁ hx₂ hW'')

end LayerW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

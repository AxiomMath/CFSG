module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf49Split
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf48ZStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf46WO2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement


section WeakData

variable {Y : Type} [Group Y] [Finite Y]

theorem weak_data_of_eta {Ω : Set (Subgroup Y)} {S₀ : Sylow 2 Y} {η : Set (Subgroup Y)}
    (hη : η ∈ etaSet Ω (S₀ : Subgroup Y))
    (hinv : ∀ s ∈ (S₀ : Subgroup Y), ∀ U ∈ η, conjSub s U ∈ η)
    (hwc : ∀ g : Y, (∀ U ∈ η, conjSub g U ≤ (S₀ : Subgroup Y)) → ∀ U ∈ η, conjSub g U ∈ η)
    (S₁ : Sylow 2 Y) (hWS₁ : (⨆ U ∈ η, U) ≤ (S₁ : Subgroup Y)) :
    (∀ s ∈ (S₁ : Subgroup Y), ∀ a ∈ (⨆ U ∈ η, U : Subgroup Y), s * a * s⁻¹ ∈ (⨆ U ∈ η, U : Subgroup Y)) ∧
      ∀ n : Y, (∀ a ∈ (⨆ U ∈ η, U : Subgroup Y), n * a * n⁻¹ ∈ (S₁ : Subgroup Y)) →
        ∀ a ∈ (⨆ U ∈ η, U : Subgroup Y), n * a * n⁻¹ ∈ (⨆ U ∈ η, U : Subgroup Y) := by
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  set W : Subgroup Y := ⨆ U ∈ η, U with hW
  have hUW : ∀ U ∈ η, U ≤ W := fun U hU => le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl
  have hx1 : ∀ U ∈ η, conjSub x⁻¹ U ∈ η := by
    refine hwc x⁻¹ fun U hU => ?_
    rw [conjSub_le_iff, inv_inv, hx]
    exact (hUW U hU).trans hWS₁
  have e2 : conjSub x⁻¹ W = W := Disconnected.AschTight.Sec7.conjSub_iSup_eq_of_forall_mem hx1
  have e3 : conjSub x W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv x W
  have hmemconj : ∀ (g : Y) (a : Y), a ∈ W → conjSub g W = W → g * a * g⁻¹ ∈ W := fun g a ha e => by
    rw [← e]; exact conj_mem_conjSub ha
  refine ⟨fun s hs a ha => ?_, fun n hn a ha => ?_⟩
  · have hs₀ : x⁻¹ * s * x ∈ (S₀ : Subgroup Y) := by
      rw [← hx] at hs
      exact mem_conjSub_iff.mp hs
    have e4 : conjSub (x⁻¹ * s * x) W = W := Disconnected.AschTight.Sec7.conjSub_iSup_eq_of_forall_mem (hinv _ hs₀)
    have e5 : conjSub s W = W := by
      have : s = x * (x⁻¹ * s * x) * x⁻¹ := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, conjSub_mul, e2, e4, e3]
    exact hmemconj s a ha e5
  · have key : ∀ U ∈ η, conjSub (x⁻¹ * n) U ≤ (S₀ : Subgroup Y) := by
      intro U hU y hy
      obtain ⟨a', ha', rfl⟩ := hy
      have h1 := hn a' (hUW U hU ha')
      rw [← hx] at h1
      have h2 := mem_conjSub_iff.mp h1
      simpa [MulAut.conj_apply, mul_assoc] using h2
    have e6 : conjSub (x⁻¹ * n) W = W := Disconnected.AschTight.Sec7.conjSub_iSup_eq_of_forall_mem (hwc _ key)
    have e7 : conjSub n W = W := by
      have : n = x * (x⁻¹ * n) := by group
      conv_lhs => rw [this]
      rw [conjSub_mul, e6, e3]
    exact hmemconj n a ha e7

end WeakData

section WDatum




variable {n : ℕ}

@[expose] def V3WDatum (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      (∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
        WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V}) →
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥ →
          ∀ U ∈ USet (CoreAssembly.conjClass (tightCore R)), U ≤ Subgroup.centralizer ({t} : Set Y) →
            (¬ ∃ P : Subgroup Y, P ≤ Subgroup.centralizer ({t} : Set Y) ∧
              (P.subgroupOf (Subgroup.centralizer ({t} : Set Y))).Normal ∧ IsPGroup 2 P ∧ U ≤ P) →
            ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), ∃ c ∈ Subgroup.centralizer ({t} : Set Y),
              ∃ w ∈ W, W ≤ Subgroup.centralizer ({t} : Set Y) ∧ conjSub c U ≤ W ∧
                W ≤ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) ⊔ Subgroup.zpowers w ∧
                w * w ∈ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M)

@[expose] def V3WAlt2 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ : Subgroup Y),
    V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄ →
      ∀ S₀ : Sylow 2 Y, (∃ η ∈ etaSet (CoreAssembly.conjClass (tightCore R)) (S₀ : Subgroup Y),
          ∀ s ∈ (S₀ : Subgroup Y), ∀ U ∈ η, conjSub s U ∈ η) →
        ∃ J ∈ CoreAssembly.conjClass (tightCore R), 2 < Nat.card ↥(J ⊓ (S₀ : Subgroup Y)) ∧
          J ⊓ (S₀ : Subgroup Y) ∉ RSet (CoreAssembly.conjClass (tightCore R))


theorem v3WZStar'_of_datum (hD : V3WDatum n) (hA : V3WAlt2 n) : V3WZStar' n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  obtain ⟨W, hWΩ, c, hcC, w, hwW, hWC, hcU, hWw, hw2⟩ :=
    hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW hO U hU hUC hUP
  have hin' := hin
  obtain ⟨hStd, hF, hα, h2g, hno⟩ := hin
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set P : Subgroup Y := ⨆ M ∈ twinSet Ω K, M with hPdef
  have hd := hStd.datum
  have hCore := CoreData.of_S hStd.perp.core
  have hPI : Q3CL.PartIHypG Ω := hCore.partIHypG
  have hPn : TC.IsNormalTwoIn P t := v3_P_normalTwo hStd h2g
  have htr0 : ∀ J ∈ Ω, ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : Y, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := htr0 K₁ hK₁
    obtain ⟨g₂, rfl⟩ := htr0 J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  obtain ⟨η, ⟨S₀, hη, hinv⟩, hWη⟩ := hWΩ
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup Y) := fun U hU => (hη.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup Y) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have h612 := Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod Y Ω hPI htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  swap
  · obtain ⟨J, hJ, hJc, hJR⟩ := hA Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin' S₀ ⟨η, hη, hinv⟩
    exact absurd (h2 J hJ hJc) hJR
  have hMS₀ : (⨆ U ∈ {U : Subgroup Y | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup Y)}, U) ≤
      (S₀ : Subgroup Y) := iSup₂_le fun U hU => hU.2
  have hηeq : η = η₀ := huniq η ⟨S₀, hη, hinv⟩ fun m hm U hU => hinv m (hMS₀ hm) U hU
  subst hηeq
  have hW2 : IsPGroup 2 W := S₀.isPGroup'.to_le hWS₀
  have hW'2 : IsPGroup 2 (W.subgroupOf C) := hW2.comap_subtype
  obtain ⟨S_C, hS_C⟩ := hW'2.exists_le_sylow
  have hQ2 : IsPGroup 2 ((S_C : Subgroup ↥C).map C.subtype) := S_C.isPGroup'.map C.subtype
  obtain ⟨S₁, hS₁⟩ := hQ2.exists_le_sylow
  have hSC₁ : ∀ s ∈ (S_C : Subgroup ↥C), (s : Y) ∈ (S₁ : Subgroup Y) := fun s hs =>
    hS₁ ⟨s, hs, rfl⟩
  have hWS₁ : W ≤ (S₁ : Subgroup Y) := fun a ha =>
    hSC₁ ⟨a, hWC ha⟩ (hS_C (Subgroup.mem_subgroupOf.mpr ha))
  obtain ⟨hWn₁, hweak₁⟩ := weak_data_of_eta hη hinv hwc S₁ (hWη ▸ hWS₁)
  rw [← hWη] at hWn₁ hweak₁
  have hPC : P ≤ C := hPn.1
  have hwC : w ∈ C := hWC hwW
  have hP'n : (P.subgroupOf C).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hPn.2.2 g g.2 a ha
  have hP'2 : IsPGroup 2 (P.subgroupOf C) := hPn.2.1.comap_subtype
  have hWw' : W.subgroupOf C ≤ P.subgroupOf C ⊔ Subgroup.zpowers (⟨w, hwC⟩ : ↥C) := by
    intro a ha
    have h1 : (a : Y) ∈ P ⊔ Subgroup.zpowers w := hWw (Subgroup.mem_subgroupOf.mp ha)
    have h2 : (P.subgroupOf C ⊔ Subgroup.zpowers (⟨w, hwC⟩ : ↥C)).map C.subtype =
        P ⊔ Subgroup.zpowers w := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPC,
        MonoidHom.map_zpowers]
      rfl
    rw [← h2] at h1
    obtain ⟨b, hb, hba⟩ := h1
    have : b = a := Subtype.ext hba
    rwa [this] at hb
  have hw2' : (⟨w, hwC⟩ : ↥C) * ⟨w, hwC⟩ ∈ P.subgroupOf C := Subgroup.mem_subgroupOf.mpr hw2
  have hno' : ¬ ∃ Q : Subgroup ↥C, Q.Normal ∧ IsPGroup 2 Q ∧ (conjSub c U).subgroupOf C ≤ Q := by
    rintro ⟨Q, hQn, hQ2', hUQ⟩
    have hsub : (Q.map C.subtype).subgroupOf C = Q :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective Q
    refine hUP ⟨Q.map C.subtype, Subgroup.map_subtype_le Q, by rw [hsub]; exact hQn,
      hQ2'.map C.subtype, fun u hu => ?_⟩
    let c' : ↥C := ⟨c, hcC⟩
    let u' : ↥C := ⟨u, hUC hu⟩
    have hq : c' * u' * c'⁻¹ ∈ Q :=
      hUQ (Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub hu))
    have hu'Q : u' ∈ Q := by
      have := hQn.conj_mem _ hq c'⁻¹
      simpa [mul_assoc] using this
    exact ⟨u', hu'Q, rfl⟩
  have hWn : ∀ s ∈ (S_C : Subgroup ↥C), ∀ a ∈ W.subgroupOf C, s * a * s⁻¹ ∈ W.subgroupOf C :=
    fun s hs a ha => Subgroup.mem_subgroupOf.mpr
      (hWn₁ s (hSC₁ s hs) a (Subgroup.mem_subgroupOf.mp ha))
  have hweak : ∀ g : ↥C, (∀ a ∈ W.subgroupOf C, g⁻¹ * a * g ∈ (S_C : Subgroup ↥C)) →
      ∀ a ∈ W.subgroupOf C, g⁻¹ * a * g ∈ W.subgroupOf C := by
    intro g hg a ha
    have := hweak₁ (g : Y)⁻¹ (fun b hb => by
      have := hSC₁ _ (hg ⟨b, hWC hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
      simpa using this) a (Subgroup.mem_subgroupOf.mp ha)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  obtain ⟨x, hxL, hxodd, p, hp, hne⟩ := exists_odd_moving hO (P.subgroupOf C) hP'2 S_C
    (W.subgroupOf C) ((conjSub c U).subgroupOf C) ⟨w, hwC⟩ (Subgroup.mem_subgroupOf.mpr hwW)
    hS_C hWn hWw' hw2' hweak
    (fun a ha => Subgroup.mem_subgroupOf.mpr (hcU (Subgroup.mem_subgroupOf.mp ha))) hno'
  have hUC' : U ≤ C := hUC
  have hsub : ((conjSub c U).subgroupOf C : Subgroup ↥C) ≤
      (Balance.normalClosureIn C U).subgroupOf C := by
    intro y hy
    have hy' := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hu : c⁻¹ * (y : Y) * c ∈ Balance.normalClosureIn C U := Balance.le_normalClosureIn C U hy'
    have := Balance.conj_mem_normalClosureIn hcC hu
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using this
  haveI hTn : ((Balance.normalClosureIn C U).subgroupOf C).Normal :=
    Balance.normal_subgroupOf_normalClosureIn hUC'
  have hxT : x ∈ (Balance.normalClosureIn C U).subgroupOf C :=
    Subgroup.normalClosure_le_normal hsub hxL
  refine ⟨(x : Y), ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hxodd
  · exact Subgroup.mem_subgroupOf.mp hxT
  · intro hx
    have h1 := Subgroup.mem_centralizer_iff.mp hx (p : Y) hp
    exact hne (Subtype.ext h1.symm)

end WDatum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

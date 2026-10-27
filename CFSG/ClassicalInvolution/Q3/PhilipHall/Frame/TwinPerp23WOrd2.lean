module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf5Trans
public import CFSG.ClassicalInvolution.Q3.TL4SepRestr

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

section O2

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem layer_pair_two_group {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : HypOmegaGen Ω)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (TwinDisc.secFam Ω c)) {J₁ J₂ : Subgroup G}
    (hJ₁ : J₁ ∈ tqMembers3 Ω c) (hJ₂ : J₂ ∈ tqMembers3 Ω c) {w : G}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ : Subgroup G}
    (hT₁ : IsSylow2In T₁ J₁) (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set G))
    (hpair : ∀ M ∈ TwinDisc.secFam Ω c, M = TwinDisc.secImg Ω c J₁ ∨ M = TwinDisc.secImg Ω c J₂)
    (hedge : TwinDisc.secImg Ω c J₂ ∈ omegaNbr (TwinDisc.secFam Ω c) (TwinDisc.secImg Ω c J₁)) :
    ∃ k : ℕ, Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = 2 ^ k := by
  classical
  set H := coreHull Ω c with hH
  set N := classicalInvolutionOddCore ↥H with hN
  obtain ⟨htC, htY, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₁ hw₁
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ hw₂
  set zb : ↥H ⧸ N := QuotientGroup.mk (⟨⟨w, htC⟩, htY⟩ : ↥H) with hzb
  have hcentTop : Subgroup.centralizer ({zb} : Set (↥H ⧸ N)) = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    refine iSup₂_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hpair M hM with h | h
    · rw [h] at hx
      exact (hz₁.commute_of_mem hx).symm
    · rw [h] at hx
      exact (hz₂.commute_of_mem hx).symm
  have hodd : oddCoreImg (Subgroup.centralizer ({zb} : Set (↥H ⧸ N))) = ⊥ := by
    rw [hcentTop]
    exact TwinExitPf12.oddCoreIn_top_eq_bot' hS.oddFree
  have hA₁ : IsPGroup 2 ↥(TwinDisc.secImg Ω c J₁) :=
    isPGroup_of_oddCent hS.hyp (secImg_mem_secFam hJ₁) hz₁ hodd
      (hS.two _ (secImg_mem_secFam hJ₁))
  have hA₂ : IsPGroup 2 ↥(TwinDisc.secImg Ω c J₂) :=
    isPGroup_of_oddCent hS.hyp (secImg_mem_secFam hJ₂) hz₂ hodd
      (hS.two _ (secImg_mem_secFam hJ₂))
  have h2' : ∀ M ∈ TwinDisc.secFam Ω c, IsPGroup 2 ↥M := fun M hM => by
    rcases hpair M hM with h | h
    · rw [h]; exact hA₁
    · rw [h]; exact hA₂
  have hcomm := TL4.commutes_of_mem_omegaNbr hS.hyp h2' (secImg_mem_secFam hJ₁) hedge
  have hnorm : TwinDisc.secImg Ω c J₂ ≤ Subgroup.normalizer
      ((TwinDisc.secImg Ω c J₁ : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := fun x hx =>
    Subgroup.centralizer_le_normalizer
      ((TwinDisc.secImg Ω c J₁ : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N))
      (Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := hcomm k hk x hx
        exact this)
  have hP : IsPGroup 2 ↥(TwinDisc.secImg Ω c J₂ ⊔ TwinDisc.secImg Ω c J₁) :=
    hA₂.to_sup_of_normal_right' hA₁ hnorm
  have htop : TwinDisc.secImg Ω c J₂ ⊔ TwinDisc.secImg Ω c J₁ = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    refine iSup₂_le fun M hM => ?_
    rcases hpair M hM with h | h
    · rw [h]; exact le_sup_right
    · rw [h]; exact le_sup_left
  rw [htop] at hP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  exact ⟨k, by rw [← Subgroup.card_top (G := ↥H ⧸ N)]; exact hk⟩

theorem e_exit_frame4 (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) :
    (∃ M ∈ TwinDisc.secFam (Om R) e, ∃ N : Subgroup (SecQ R e),
      N ∈ omegaNbr (TwinDisc.secFam (Om R) e) M) ∧
    (∃ A ∈ TwinDisc.secFam (Om R) e, ∃ B ∈ twinSet (TwinDisc.secFam (Om R) e) A, B ≠ A) ∧
    ((∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
        ∃ x : SecQ R e, conjSub x K = L) ∨ ∃ k : ℕ, Nat.card (SecQ R e) = 2 ^ k) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  obtain ⟨hedge, hdich⟩ := layer_exit_frame hT hc.std.perp hd.he2 hd.he1 hK hc.std.hK'.1
    hc.std.hne hz hz' hR₁ hR₁' hR₁e hR₁'e hcomm hp₁ hp₂
  have hJ₁ : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hJ₂ : K' ∈ tqMembers3 (Om R) e :=
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hc.std.hK'.1 ⟨R₁', hR₁', hR₁'e⟩⟩
  obtain ⟨hC₁, hY₁, hzz₁⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₁ hz
  obtain ⟨hC₂, hY₂, hzz₂⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₂ hz'
  refine ⟨⟨_, secImg_mem_secFam hJ₁, _, hedge⟩,
    ⟨_, secImg_mem_secFam hJ₁, _, ⟨secImg_mem_secFam hJ₂, _, hzz₁, hzz₂⟩,
      (secImg_ne_of_twins hΩ hc2' hJ₁ hJ₂ hc.std.hne hz hz').symm⟩, ?_⟩
  rcases hdich with h | h
  · exact Or.inl h
  · exact Or.inr (layer_pair_two_group hΩ h2 hc2' (p23_q8Section hc.std.perp hd.he2) hJ₁ hJ₂ hz hz'
      hR₁ hR₁e h hedge)

end O2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

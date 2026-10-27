module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22O

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Fam

theorem q8Fam_of_isPGroup {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hS : Q8Section X Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K : Subgroup X} (hK : K ∈ Φ) {z : X}
    (hz : IsUniqueInvolution K z) (hO2 : TightInO2 z) : ExitO2.Q8Fam X Φ where
  hyp := hS.hyp
  two := h2
  q8 := fun J hJ => hS.q8 J hJ J ⟨le_rfl, h2 J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  aEmpty := hS.aEmpty
  gen := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  trans := htrans
  oddFree := hS.oddFree
  inO2 := by
    intro L hL u hu
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    obtain ⟨P, hPn, hP2, hzP⟩ := hO2
    refine ⟨P, hPn, hP2, ?_⟩
    have hgu : g * z * g⁻¹ = u := (hz.conj g).eq hu
    rw [← hgu]
    exact hPn.conj_mem z hzP g

end Fam

section Sec


variable {n : ℕ}

theorem v3_secFam_dstarConnected (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (hOpen : V3SecOpenW n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    {K₄ : Subgroup Y} (hin : V3ExitIn n R S t K K' K₃ u₁ u₂ u₃ K₄) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hKD : K ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK'D : K' ∈ DSet (CoreAssembly.conjClass (tightCore R)) W)
    (hK₃D : K₃ ∈ DSet (CoreAssembly.conjClass (tightCore R)) W) (hu₁ : u₁ ∈ W) (hu₂ : u₂ ∈ W) :
    T3.DStarConnected (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) := by
  obtain ⟨hStd, hF, -, h2g, -⟩ := id hin
  have hd := hStd.datum
  have hS := layer_q8Section hStd.perp hd.sq_12
  have hlt := card_layer_lt hStd.perp hd.mul_ne_one
  obtain ⟨hmem, -⟩ := v3_tq_members hStd hF
  have hBs := secImg_mem_secFam hmem
  rcases dichotomy_of_thm4RTwin h4 hlt hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree hBs with
    hconn | horb
  · intro A hA B hB
    exact (T3.mem_dstarComp_symm hBs (hconn A hA)).2.trans (hconn B hB)
  · have htrans : ∀ K₁ ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        ∀ L ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
          ∃ g : LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), conjSub g K₁ = L := by
      intro K₁ hK₁ L hL
      obtain ⟨y₁, hy₁⟩ := horb K₁ hK₁
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    have h2 : ∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
        IsPGroup 2 J := by
      intro J hJ
      obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hJ
      exact secImg_isPGroup' (h2g J₀ hJ₀.1)
    obtain ⟨⟨M, hM, zb, hzb, hO2⟩, hWu | ⟨m, hm, ⟨I⟩⟩⟩ :=
      v3ExitTrichotomyAd_of_open hcit hP h4 hOpen Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D
        hK₃D hu₁ hu₂
    · obtain ⟨V, hV⟩ := hWu
      exact ExitO2.fam_dstarConnected_of_wSet (q8Fam_of_isPGroup hS h2 htrans hM hzb hO2) hV
    · rcases hm with rfl | rfl
      · exact (v3ExitAE5W_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂
          ⟨I⟩).elim
      · exact ExitO2.fam_dstarConnected_of_aeIdent
          (AE5.q8Fam_of_aeIdent_n (by norm_num) hS I) le_rfl I

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

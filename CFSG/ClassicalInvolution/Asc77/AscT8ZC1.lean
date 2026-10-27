module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabD4
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8ZB1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open CFSG.ClassicalInvolution.RouteD.Gaps (InvOf)

namespace T8ZZ

theorem three_cover {α : Type*} {x y w a b c s : α} (ha : a = x ∨ a = y ∨ a = w)
    (hb : b = x ∨ b = y ∨ b = w) (hc : c = x ∨ c = y ∨ c = w) (hs : s = x ∨ s = y ∨ s = w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : s = a ∨ s = b ∨ s = c := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp_all

variable {p f : ℕ} [Fact p.Prime]


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_layerDatum [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hnconn : ¬ DConnected (T8.layerFamQ Ω (z * t))) (F : FrameData Ω W K J z t) :
    ∃ e : ℕ, ∃ M : Ih8Model p f (T8.layerFamQ Ω (z * t))
        CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 e, e = f ∧
      ∃ Rs : Fin 4 → Subgroup (modelUniv CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus 4 p e
          Fact.out).K,
        (∀ i, Rs i ∈ M.cls) ∧
          (∀ i, T8.layerImg Ω (z * t) (F.ρ i).K = (Rs i).map M.ψ) ∧
            ∀ i j, i ≠ j → Commutes (Rs i) (Rs j) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
  have hlt := T8.card_layerQuot_lt (Ω := Ω) (T8.zt_not_central hs)
  have hΨ := T8.hypOmegaMod_layerQuot hp hq hΩ hx
  have hinj : Function.Injective
      (fun i : Fin 3 => T8.layerImg Ω (z * t) (F.ρ i.castSucc).K) := by
    intro i j h
    by_contra hij
    exact frame_layerImg_ne hs F (fun h' => hij (Fin.castSucc_injective _ h')) h
  obtain ⟨e, ⟨M⟩⟩ := T8X.exists_spin8_datum_of_triangle hn hlt hp hq hΨ
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (T8.omegaGen_layerFamQ Ω _)
    (T8.noTwins_layerQuot hp hq hΩ hnt hx)
    (fun i : Fin 3 => T8.layerImg Ω (z * t) (F.ρ i.castSucc).K)
    (fun i => T8.layerImg_mem (frame_xMem hs F _)) hinj
    (fun i j hij => frame_layerImg_nbr hs F (fun h' => hij (Fin.castSucc_injective _ h')))
    hnconn
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have he : e = f := M.exp_eq_f hD4
  have hrep : ∀ i : Fin 4, ∃ Ri ∈ M.cls, T8.layerImg Ω (z * t) (F.ρ i).K = Ri.map M.ψ :=
    fun i => (M.mem_iff _).mp (T8.layerImg_mem (frame_xMem hs F i))
  choose Rs hRs hRsψ using hrep
  refine ⟨e, M, he, Rs, hRs, hRsψ, fun i j hij => ?_⟩
  have hadj : (Rs j).map M.ψ ∈
      omegaNbr (T8.layerFamQ Ω (z * t)) ((Rs i).map M.ψ) := by
    rw [← hRsψ i, ← hRsψ j]
    exact frame_layerImg_nbr hs F hij
  exact ((M.muTab_omegaNbr_iff hΨ hp hq hG2 hD4 (hRs i) (hRs j)).mp hadj).2

theorem layerImg_nbr_eq_frame [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hnconn : ¬ DConnected (T8.layerFamQ Ω (z * t))) (F : FrameData Ω W K J z t)
    {L : Subgroup G} (hL : T8.XMem Ω (z * t) L)
    (hadj : T8.layerImg Ω (z * t) L ∈
      omegaNbr (T8.layerFamQ Ω (z * t)) (T8.layerImg Ω (z * t) K)) :
    ∃ j : Fin 4, j ≠ 0 ∧ T8.layerImg Ω (z * t) L = T8.layerImg Ω (z * t) (F.ρ j).K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  have hΨ := T8.hypOmegaMod_layerQuot hp hq hΩ hx
  obtain ⟨e, M, he, Rs, hRs, hRsψ, hcomm⟩ := exists_layerDatum hs hnconn F
  have hD4 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .trialityD4 := by decide
  have hG2 : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaPlus ≠ .G2 := by decide
  have hq' : 5 ≤ p ^ e := he ▸ hq
  obtain ⟨S₀, hS₀, hLS⟩ := (M.mem_iff _).mp (T8.layerImg_mem hL)
  have hK0 : T8.layerImg Ω (z * t) K = (Rs 0).map M.ψ := by
    rw [← hRsψ 0, F.h0]
  rw [hLS, hK0] at hadj
  obtain ⟨hne0, hc0⟩ := (M.muTab_omegaNbr_iff hΨ hp hq hG2 hD4 (hRs 0) hS₀).mp hadj
  obtain ⟨R₂, h₂, R₃, h₃, R₄, h₄, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
    MuTab.clique_plus hp hq' M.admissible (M.cls_sub (hRs 0))
  have hfr : ∀ i : Fin 4, i ≠ 0 → Rs i = R₂ ∨ Rs i = R₃ ∨ Rs i = R₄ := by
    intro i hi
    have hne : Rs 0 ≠ Rs i := by
      intro h
      have := congrArg (fun A => A.map M.ψ) h
      beta_reduce at this
      rw [← hRsψ 0, ← hRsψ i] at this
      exact frame_layerImg_ne hs F (Ne.symm hi) this
    exact hall (Rs i) (M.cls_sub (hRs i)) (Ne.symm hne) (hcomm 0 i (Ne.symm hi))
  have hSc : S₀ = R₂ ∨ S₀ = R₃ ∨ S₀ = R₄ :=
    hall S₀ (M.cls_sub hS₀) (Ne.symm hne0) hc0
  have hdist : ∀ i j : Fin 4, i ≠ j → Rs i ≠ Rs j := by
    intro i j hij h
    have := congrArg (fun A => A.map M.ψ) h
    beta_reduce at this
    rw [← hRsψ i, ← hRsψ j] at this
    exact frame_layerImg_ne hs F hij this
  have hcov := three_cover (hfr 1 (by decide)) (hfr 2 (by decide)) (hfr 3 (by decide)) hSc
    (hdist 1 2 (by decide)) (hdist 1 3 (by decide)) (hdist 2 3 (by decide))
  rcases hcov with h | h | h
  · exact ⟨1, by decide, by rw [hLS, h, ← hRsψ 1]⟩
  · exact ⟨2, by decide, by rw [hLS, h, ← hRsψ 2]⟩
  · exact ⟨3, by decide, by rw [hLS, h, ← hRsψ 3]⟩

end T8ZZ

end CFSG.ClassicalInvolution.Asc77

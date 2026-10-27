module

public import CFSG.ClassicalInvolution.Q3.Q3TY33

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups commutatorElement


section Quot

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3W.CentralQuot3.orthCross
    (h : CentralQuot3 π 𝓕 𝓕' Z') (hG : OrthCross Z' 𝓕') : OrthCross (Subgroup.center KY) 𝓕 := by
  refine ⟨?_⟩
  intro K' hK β' hβ J' hJ N' hN a1 a2 kKJ kNK kNJ hKJ hKN hJN nKJ nKN nJN
  have := hG.cross (K'.map π) (h.map_mem K' hK) (β'.map π) (h.map_mem β' hβ) (J'.map π)
    (h.map_mem J' hJ) (N'.map π) (h.map_mem N' hN) (h.modelAdj hK hβ a1) (h.modelAdj hβ hJ a2)
    ((h.commutes_iff hK).mpr kKJ) ((h.commutes_iff hN).mpr kNK) ((h.commutes_iff hN).mpr kNJ)
    (fun e => hKJ (h.map_inj hK hJ e)) (fun e => hKN (h.map_inj hK hN e))
    (fun e => hJN (h.map_inj hJ hN e))
    (fun hi => nKJ (h.modelIndist hK hJ hKJ hi)) (fun hi => nKN (h.modelIndist hK hN hKN hi))
    (fun hi => nJN (h.modelIndist hJ hN hJN hi))
  exact (h.commutes_iff hN).mp this

end Quot

section Minus

theorem orthCross_minus3 {m : ℕ} (hm : 5 ≤ m) :
    OrthCross (Subgroup.center (spinGroup (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))) (fundamentalSubgroups .POmegaMinus
        (minusDatum m (minusCoeffs_irr 3 1))) := by
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 m (by omega)]
    omega
  have hadm : StatedLieAdmissible .POmegaMinus m 3 1 := ⟨Nat.prime_three, le_rfl, by omega⟩
  exact (centralQuot3_minus hadm).orthCross (orthCross_model odd_gf3 hdim)

end Minus

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {W : Subgroup G} {x : G}

@[expose] def SeparatesAt3 (Ω : Set (Subgroup G)) (x : G) (l l' : Subgroup G) (wl wl' : G) : Prop :=
  ∃ d v, d ∈ centralizingMembers Ω {x} ∧ IsClassicalMember3 d v ∧ d ≠ l ∧ d ≠ l' ∧
    Commute v wl ∧ Commute v wl' ∧ Commutes d l ∧ ¬ Commutes d l'

theorem IsLayerMember3.of_distinguish (cx : Q3TC.TCtx3 tY nY Ω W x) {d l l' : Subgroup G}
    (hd : d ∈ centralizingMembers Ω {x}) (hl : l ∈ centralizingMembers Ω {x})
    (hl' : l' ∈ centralizingMembers Ω {x}) (hdl : d ≠ l) (hdl' : d ≠ l')
    (h : ¬ (Commutes d l ↔ Commutes d l')) : IsLayerMember3 cx d := by
  by_cases hc : Commutes d l
  · exact IsLayerMember3.of_not_commutes cx hd hl' hdl' (fun hc' => h ⟨fun _ => hc', fun _ => hc⟩)
  · exact IsLayerMember3.of_not_commutes cx hd hl hdl hc

theorem commutes_iff_of_indist3 (cx : Q3TC.TCtx3 tY nY Ω W x) {l l' d : Subgroup G}
    (hl : l ∈ centralizingMembers Ω {x}) (hl' : l' ∈ centralizingMembers Ω {x})
    (hd : IsLayerMember3 cx d) {Rl Rl' Rd : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hRl : Rl ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hRl' : Rl' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hRd : Rd ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hlR : locImg Ω x l = Rl.map cx.d.ψ) (hlR' : locImg Ω x l' = Rl'.map cx.d.ψ)
    (hdR : locImg Ω x d = Rd.map cx.d.ψ) {wl wl' wd : G} (hwl : IsClassicalMember3 l wl)
    (hwl' : IsClassicalMember3 l' wl') (hwd : IsClassicalMember3 d wd) (hdl : d ≠ l)
    (hdl' : d ≠ l') (hc : Commute wd wl) (hc' : Commute wd wl')
    (hind : ModelIndist (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) Rl Rl') :
    Commutes d l ↔ Commutes d l' := by
  have h1 : Rd ≠ Rl := fun h => hdl (cx.eq_of_locImg_eq hd.1 hl (by rw [hdR, hlR, h]))
  have h2 : Rd ≠ Rl' := fun h => hdl' (cx.eq_of_locImg_eq hd.1 hl' (by rw [hdR, hlR', h]))
  obtain ⟨r₁, r₁', hr₁, hr₁', hcen₁, -, -⟩ := cx.modelInvComm3 hd.1 hl hRd hRl hdR hlR hwd hwl hc
  obtain ⟨r₂, r₂', hr₂, hr₂', hcen₂, -, -⟩ :=
    cx.modelInvComm3 hd.1 hl' hRd hRl' hdR hlR' hwd hwl' hc'
  have := hind.2 Rd hRd h1 h2 ⟨r₁, r₁', hr₁, hr₁', hcen₁⟩ ⟨r₂, r₂', hr₂, hr₂', hcen₂⟩
  rw [cx.commutes_iff_fund hd.1 hl hRd hdR hlR, cx.commutes_iff_fund hd.1 hl' hRd hdR hlR']
  exact this

theorem cross_config3 (cx : Q3TC.TCtx3 tY nY Ω W x)
    (hF : OrthCross (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D))
    {K β J N : Subgroup G} {wK wβ wJ wN : G}
    (hK : K ∈ centralizingMembers Ω {x}) (hβ : β ∈ centralizingMembers Ω {x})
    (hJ : J ∈ centralizingMembers Ω {x}) (hN : N ∈ centralizingMembers Ω {x})
    (hwK : IsClassicalMember3 K wK) (hwβ : IsClassicalMember3 β wβ)
    (hwJ : IsClassicalMember3 J wJ) (hwN : IsClassicalMember3 N wN)
    (hKβ : K ≠ β ∧ ¬ Commutes K β ∧ Commute wK wβ ∧ conjSub wβ K = K)
    (hβJ : β ≠ J ∧ ¬ Commutes β J ∧ Commute wβ wJ ∧ conjSub wJ β = β)
    (hKJ : K ≠ J) (kKJ : Commutes K J) (hKN : K ≠ N) (kNK : Commutes N K) (hJN : J ≠ N)
    (kNJ : Commutes N J) (sKJ : SeparatesAt3 Ω x K J wK wJ)
    (sKN : SeparatesAt3 Ω x K N wK wN) (sJN : SeparatesAt3 Ω x J N wJ wN) :
    Commutes N β := by
  classical
  obtain ⟨hKβ1, hKβ2, hKβ3, hKβ4⟩ := hKβ
  obtain ⟨hβJ1, hβJ2, hβJ3, hβJ4⟩ := hβJ
  have hKL : IsLayerMember3 cx K := IsLayerMember3.of_not_commutes cx hK hβ hKβ1 hKβ2
  have hβL : IsLayerMember3 cx β :=
    IsLayerMember3.of_not_commutes cx hβ hK hKβ1.symm (fun h => hKβ2 (commutes_symm h))
  have hJL : IsLayerMember3 cx J :=
    IsLayerMember3.of_not_commutes cx hJ hβ hβJ1.symm (fun h => hβJ2 (commutes_symm h))
  have hNL : IsLayerMember3 cx N := by
    obtain ⟨d, v, hd, hvd, hdK, hdN, -, -, -, hdn⟩ := sKN
    exact IsLayerMember3.of_not_commutes cx hN hd hdN.symm (fun h => hdn (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  obtain ⟨RJ, hRJ, hJR⟩ := hJL.exists_fund
  obtain ⟨RN, hRN, hNR⟩ := hNL.exists_fund
  have nind : ∀ {l l' : Subgroup G} {wl wl' : G}
      {Rl Rl' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      l ∈ centralizingMembers Ω {x} → l' ∈ centralizingMembers Ω {x} →
      Rl ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D →
      Rl' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D →
      locImg Ω x l = Rl.map cx.d.ψ → locImg Ω x l' = Rl'.map cx.d.ψ →
      IsClassicalMember3 l wl → IsClassicalMember3 l' wl' →
      SeparatesAt3 Ω x l l' wl wl' →
      ¬ ModelIndist (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
        (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) Rl Rl' := by
    intro l l' wl wl' Rl Rl' hl hl' hRl hRl' hlR hlR' hwl hwl' ⟨d, v, hd, hvd, hdl, hdl', hv1, hv2,
      hdc, hdn⟩ hind
    have hdL : IsLayerMember3 cx d :=
      IsLayerMember3.of_distinguish cx hd hl hl' hdl hdl' (fun h => hdn (h.mp hdc))
    obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
    exact hdn ((commutes_iff_of_indist3 cx hl hl' hdL hRl hRl' hRd hlR hlR' hdR hwl hwl' hvd hdl
      hdl' hv1 hv2 hind).mp hdc)
  have hadj1 := cx.modelAdj_of_adj3 hK hβ hRK hRβ hKR hβR hwK hwβ hKβ1 hKβ2 hKβ3 hKβ4
  have hadj2 := cx.modelAdj_of_adj3 hβ hJ hRβ hRJ hβR hJR hwβ hwJ hβJ1 hβJ2 hβJ3 hβJ4
  have hne : ∀ {l l' : Subgroup G} {Rl Rl' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K},
      l ∈ centralizingMembers Ω {x} → l' ∈ centralizingMembers Ω {x} → l ≠ l' →
      locImg Ω x l = Rl.map cx.d.ψ → locImg Ω x l' = Rl'.map cx.d.ψ → Rl ≠ Rl' :=
    fun hl hl' h hlR hlR' e => h (cx.eq_of_locImg_eq hl hl' (by rw [hlR, hlR', e]))
  have := hF.cross RK hRK Rβ hRβ RJ hRJ RN hRN hadj1 hadj2
    ((cx.commutes_iff_fund hK hJ hRK hKR hJR).mp kKJ)
    ((cx.commutes_iff_fund hN hK hRN hNR hKR).mp kNK)
    ((cx.commutes_iff_fund hN hJ hRN hNR hJR).mp kNJ)
    (hne hK hJ hKJ hKR hJR) (hne hK hN hKN hKR hNR) (hne hJ hN hJN hJR hNR)
    (nind hK hJ hRK hRJ hKR hJR hwK hwJ sKJ) (nind hK hN hRK hRN hKR hNR hwK hwN sKN)
    (nind hJ hN hRJ hRN hJR hNR hwJ hwN sJN)
  exact (cx.commutes_iff_fund hN hβ hRN hNR hβR).mpr this

end Witness

end CFSG.ClassicalInvolution.Q3.Q3TY

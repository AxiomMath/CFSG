module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

section Abstract

variable {KY : Type} [Group KY]

structure OrthCross (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) : Prop where
  cross : ∀ K' ∈ 𝓕, ∀ β' ∈ 𝓕, ∀ J' ∈ 𝓕, ∀ N' ∈ 𝓕, ModelAdj Z K' β' → ModelAdj Z β' J' →
    Commutes K' J' → Commutes N' K' → Commutes N' J' → K' ≠ J' → K' ≠ N' → J' ≠ N' →
    ¬ ModelIndist Z 𝓕 K' J' → ¬ ModelIndist Z 𝓕 K' N' → ¬ ModelIndist Z 𝓕 J' N' →
    Commutes N' β'

end Abstract

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
private theorem commutes_of_orth' (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i')
    (horth : ∀ x ∈ negSpace i, ∀ y ∈ negSpace i', polar Q x y = 0) : Commutes L L' := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨F', rfl, rfl⟩ := h'
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at horth
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact Frame.La_comm_of_orth (fun X Y => horth _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩) A B

theorem orthCross_model (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) :
    OrthCross (scalars K V) (fundSet Q) := by
  refine ⟨?_⟩
  rintro K' ⟨iK, hK⟩ β' ⟨iβ, hβ⟩ J' ⟨iJ, hJ⟩ N' ⟨iN, hN⟩ a1 a2 kKJ kNK kNJ hKJ hKN hJN nKJ nKN nJN
  have oKJ : ∀ x ∈ negSpace iK, ∀ y ∈ negSpace iJ, polar Q x y = 0 := by
    rcases orth_or_twin hodd hK hJ kKJ with h | h
    · exact h
    · exact absurd (indist_of_eq hodd hdim hK hJ hKJ h) nKJ
  have oKN : ∀ x ∈ negSpace iK, ∀ y ∈ negSpace iN, polar Q x y = 0 := by
    rcases orth_or_twin hodd hK hN (commutes_symm kNK) with h | h
    · exact h
    · exact absurd (indist_of_eq hodd hdim hK hN hKN h) nKN
  have oJN : ∀ x ∈ negSpace iJ, ∀ y ∈ negSpace iN, polar Q x y = 0 := by
    rcases orth_or_twin hodd hJ hN (commutes_symm kNJ) with h | h
    · exact h
    · exact absurd (indist_of_eq hodd hdim hJ hN hJN h) nJN
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data hodd hdim hK hβ a1
  obtain ⟨cm₂, N₂, C₂⟩ := adj_data hodd hdim hβ hJ a2
  have pd₁ := (lemma_6_10 hodd hK hβ cm₁ N₁ C₁).1
  have pd₂ := (lemma_6_10 hodd hβ hJ cm₂ N₂ C₂).1
  set P₁ := negSpace iK ⊓ negSpace iβ with hP₁
  set P₂ := negSpace iβ ⊓ negSpace iJ with hP₂
  have hdis : Disjoint P₁ P₂ := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    refine pd₁.nondeg₂ x hx1 fun y hy => ?_
    rw [polar_comm]
    exact oKJ y (Submodule.mem_inf.mp hy).1 x (Submodule.mem_inf.mp hx2).2
  have hsup := Frame.finrank_sup_of_disjoint hdis
  have hle : P₁ ⊔ P₂ ≤ negSpace iβ := sup_le inf_le_right inf_le_left
  have heq : P₁ ⊔ P₂ = negSpace iβ := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [hsup, pd₁.finrank_U₂, pd₂.finrank_U₂, finrank_negSpace hodd hβ]
  refine commutes_of_orth' hodd hN hβ fun x hx y hy => ?_
  rw [← heq] at hy
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [polar_add_right]
  have h1 : polar Q x u = 0 := by
    rw [polar_comm]
    exact oKN u (Submodule.mem_inf.mp hu).1 x hx
  have h2 : polar Q x w = 0 := by
    rw [polar_comm]
    exact oJN w (Submodule.mem_inf.mp hw).2 x hx
  rw [h1, h2, add_zero]

end Model

section Quot

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot.orthCross (h : CentralQuot π 𝓕 𝓕' Z') (hG : OrthCross Z' 𝓕') :
    OrthCross (Subgroup.center KY) 𝓕 := by
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

variable {p f : ℕ} [Fact p.Prime]

theorem orthCross_minusDatum {m : ℕ} (hp2 : p ≠ 2) (hm : 5 ≤ m) (hq : 5 ≤ p ^ f) :
    OrthCross (Subgroup.center (spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))) (fundamentalSubgroups .POmegaMinus
        (minusDatum m (minusCoeffs_irr p f))) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f m (by omega)]
    omega
  have hf1 : 1 ≤ f := by omega
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf1, by omega⟩
  exact (Exotic.centralQuot_minus hp2 hq hadm).orthCross (orthCross_model hodd hdim)

end Minus

section Witness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {W : Subgroup G} {x : G}

variable (p f) in
@[expose] def SeparatesAt (Ω : Set (Subgroup G)) (x : G) (l l' : Subgroup G) (wl wl' : G) : Prop :=
  ∃ d v, d ∈ centralizingMembers Ω {x} ∧ IsClassicalMember p f d v ∧ d ≠ l ∧ d ≠ l' ∧
    Commute v wl ∧ Commute v wl' ∧ Commutes d l ∧ ¬ Commutes d l'

theorem cross_config (cx : TCtx p f tY nY Ω W x)
    (hF : OrthCross (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D))
    {K β J N : Subgroup G} {wK wβ wJ wN : G}
    (hK : K ∈ centralizingMembers Ω {x}) (hβ : β ∈ centralizingMembers Ω {x})
    (hJ : J ∈ centralizingMembers Ω {x}) (hN : N ∈ centralizingMembers Ω {x})
    (hwK : IsClassicalMember p f K wK) (hwβ : IsClassicalMember p f β wβ)
    (hwJ : IsClassicalMember p f J wJ) (hwN : IsClassicalMember p f N wN)
    (hKβ : K ≠ β ∧ ¬ Commutes K β ∧ Commute wK wβ ∧ conjSub wβ K = K)
    (hβJ : β ≠ J ∧ ¬ Commutes β J ∧ Commute wβ wJ ∧ conjSub wJ β = β)
    (hKJ : K ≠ J) (kKJ : Commutes K J) (hKN : K ≠ N) (kNK : Commutes N K) (hJN : J ≠ N)
    (kNJ : Commutes N J) (sKJ : SeparatesAt p f Ω x K J wK wJ)
    (sKN : SeparatesAt p f Ω x K N wK wN) (sJN : SeparatesAt p f Ω x J N wJ wN) :
    Commutes N β := by
  classical
  obtain ⟨hKβ1, hKβ2, hKβ3, hKβ4⟩ := hKβ
  obtain ⟨hβJ1, hβJ2, hβJ3, hβJ4⟩ := hβJ
  have hKL : IsLayerMember cx K := IsLayerMember.of_not_commutes cx hK hβ hKβ1 hKβ2
  have hβL : IsLayerMember cx β :=
    IsLayerMember.of_not_commutes cx hβ hK hKβ1.symm (fun h => hKβ2 (commutes_symm h))
  have hJL : IsLayerMember cx J :=
    IsLayerMember.of_not_commutes cx hJ hβ hβJ1.symm (fun h => hβJ2 (commutes_symm h))
  have hNL : IsLayerMember cx N := by
    obtain ⟨d, v, hd, hvd, hdK, hdN, -, -, -, hdn⟩ := sKN
    exact IsLayerMember.of_not_commutes cx hN hd hdN.symm (fun h => hdn (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  obtain ⟨RJ, hRJ, hJR⟩ := hJL.exists_fund
  obtain ⟨RN, hRN, hNR⟩ := hNL.exists_fund
  have nind : ∀ {l l' : Subgroup G} {wl wl' : G}
      {Rl Rl' : Subgroup (modelUniv tY nY p f Fact.out).K},
      l ∈ centralizingMembers Ω {x} → l' ∈ centralizingMembers Ω {x} →
      Rl ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D →
      Rl' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D →
      locImg Ω x l = Rl.map cx.d.ψ → locImg Ω x l' = Rl'.map cx.d.ψ →
      IsClassicalMember p f l wl → IsClassicalMember p f l' wl' →
      SeparatesAt p f Ω x l l' wl wl' →
      ¬ ModelIndist (Subgroup.center (modelUniv tY nY p f Fact.out).K)
        (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) Rl Rl' := by
    intro l l' wl wl' Rl Rl' hl hl' hRl hRl' hlR hlR' hwl hwl' ⟨d, v, hd, hvd, hdl, hdl', hv1, hv2,
      hdc, hdn⟩ hind
    have hdL : IsLayerMember cx d :=
      IsLayerMember.of_distinguish cx hd hl hl' hdl hdl' (fun h => hdn (h.mp hdc))
    obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
    exact hdn ((commutes_iff_of_indist cx hl hl' hdL hRl hRl' hRd hlR hlR' hdR hwl hwl' hvd hdl
      hdl' hv1 hv2 hind).mp hdc)
  have hadj1 := modelAdj_of_adj cx hK hβ hRK hRβ hKR hβR hwK hwβ hKβ1 hKβ2 hKβ3 hKβ4
  have hadj2 := modelAdj_of_adj cx hβ hJ hRβ hRJ hβR hJR hwβ hwJ hβJ1 hβJ2 hβJ3 hβJ4
  have hne : ∀ {l l' : Subgroup G} {Rl Rl' : Subgroup (modelUniv tY nY p f Fact.out).K},
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

end CFSG.ClassicalInvolution.RouteD.Gaps

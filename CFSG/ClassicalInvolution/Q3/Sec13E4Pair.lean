module

public import CFSG.ClassicalInvolution.Q3.TL3T26
public import CFSG.ClassicalInvolution.Q3.TL4Conn264T

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure E4Hyp (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop where
  thmD : ThmDHyp 3 Ω
  center : Subgroup.center G = ⊥
  hW : W ∈ WSet Ω
  hE : MuIsoE4 Ω W

@[expose] def Paired (Ω : Set (Subgroup G)) (A B : Subgroup G) : Prop :=
  A ∈ Ω ∧ B ∈ Ω ∧ A ≠ B ∧ Commutes A B

theorem Paired.symm {Ω : Set (Subgroup G)} {A B : Subgroup G} (h : Paired Ω A B) :
    Paired Ω B A :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

theorem Paired.conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {A B : Subgroup G}
    (h : Paired Ω A B) (g : G) : Paired Ω (conjSub g A) (conjSub g B) := by
  refine ⟨hΩ g A h.1, hΩ g B h.2.1, ?_, h.2.2.2.conjSub g⟩
  intro he
  apply h.2.2.1
  have := congrArg (conjSub g⁻¹) he
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem partIHypG : Q3CL.PartIHypG Ω :=
  ⟨h.thmD.hyp, classicalClause_of_two h.thmD.hyp h.thmD.two, h.thmD.aEmpty⟩

theorem card_eq {L : Subgroup G} (hL : L ∈ Ω) : Nat.card L = 8 := by
  have := h.thmD.card L hL
  norm_num at this
  exact this

theorem isPGroup {L : Subgroup G} (hL : L ∈ Ω) : IsPGroup 2 L := h.thmD.two L hL

theorem exists_uniqueInvolution {L : Subgroup G} (hL : L ∈ Ω) : ∃ z : G, IsUniqueInvolution L z :=
  (h.thmD.hyp.omega1 L hL).1

theorem mem_pCore {L : Subgroup G} (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z) :
    z ∈ pCore 2 G := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := h.thmD.inO2 L hL z hz
  exact (le_sSup ⟨hQn, hQ2⟩ : Q ≤ pCore 2 G) hzQ

theorem false_of_three (S : Sylow 2 G) {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ Ω) (h₂ : L₂ ∈ Ω)
    (h₃ : L₃ ∈ Ω) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (hc₁ : 2 < Nat.card ↥(L₁ ⊓ (S : Subgroup G))) (hc₂ : 2 < Nat.card ↥(L₂ ⊓ (S : Subgroup G)))
    (hc₃ : 2 < Nat.card ↥(L₃ ⊓ (S : Subgroup G))) : False :=
  TL4.false_of_three_meet_sylow_E4 h.partIHypG h.hW h.hE S h₁ h₂ h₃ h12 h13 h23 hc₁ hc₂ hc₃

theorem two_lt_card_inf_of_le {L : Subgroup G} (hL : L ∈ Ω) {S : Subgroup G} (hLS : L ≤ S) :
    2 < Nat.card ↥(L ⊓ S) := by
  rw [inf_eq_left.mpr hLS, h.card_eq hL]
  norm_num

theorem exists_paired : ∃ A B : Subgroup G, Paired Ω A B := by
  have hcard : Nat.card ↥(muGroup Ω W) = 4 := by
    obtain ⟨φ⟩ := h.hE
    rw [Nat.card_congr φ.toEquiv]
    simp
  have hne : (Thompson.muDelta Ω W).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hcl := Thompson.closure_muDelta_eq_top Ω W
    rw [hemp, Subgroup.closure_empty] at hcl
    have h1 : Nat.card ↥(muGroup Ω W) = 1 := by
      rw [← Subgroup.card_top (G := ↥(muGroup Ω W)), ← hcl, Subgroup.card_bot]
    omega
  obtain ⟨d, hd⟩ := hne
  obtain ⟨ρ, -⟩ := MuTab.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, hσ⟩ := TL4.exists_rep_ne_E4_gen h.partIHypG h.hW h.hE ρ
  have hcomm : MuTab.muTabElt ρ * MuTab.muTabElt σ = MuTab.muTabElt σ * MuTab.muTabElt ρ := by
    obtain ⟨φ⟩ := h.hE
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hnbr : σ.K ∈ omegaNbr Ω ρ.K :=
    (Q3T6.Mu.muTab_commute_iff h.partIHypG h.hW ρ σ hσ.symm).mp hcomm
  exact ⟨ρ.K, σ.K, ρ.hK, σ.hK, hσ.symm,
    comm_of_mem_omegaNbr h.thmD.hyp h.thmD.two ρ.hK hnbr⟩

theorem exists_sylow_of_paired {A B : Subgroup G} (hp : Paired Ω A B) :
    ∃ S : Sylow 2 G, A ≤ (S : Subgroup G) ∧ B ≤ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hp.2.2.2 x hx y hy).symm
  have hP2 : IsPGroup 2 ↥(A ⊔ B) :=
    (h.isPGroup hp.1).to_sup_of_normal_right' (h.isPGroup hp.2.1) hAN
  obtain ⟨S, hS⟩ := hP2.exists_le_sylow
  exact ⟨S, le_sup_left.trans hS, le_sup_right.trans hS⟩

theorem eq_or_eq_of_paired {A B : Subgroup G} (hp : Paired Ω A B) {S : Sylow 2 G}
    (hA : A ≤ (S : Subgroup G)) (hB : B ≤ (S : Subgroup G)) {L : Subgroup G} (hL : L ∈ Ω)
    (hc : 2 < Nat.card ↥(L ⊓ (S : Subgroup G))) : L = A ∨ L = B := by
  by_contra hne
  push Not at hne
  exact h.false_of_three S hp.1 hp.2.1 hL hp.2.2.1 (Ne.symm hne.1) (Ne.symm hne.2)
    (h.two_lt_card_inf_of_le hp.1 hA) (h.two_lt_card_inf_of_le hp.2.1 hB) hc

theorem exists_third {A B : Subgroup G} (hp : Paired Ω A B) :
    ∃ L ∈ Ω, L ≠ A ∧ L ≠ B := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ L ∈ Ω, L = A ∨ L = B := fun L hL => by
    by_cases hLA : L = A
    · exact Or.inl hLA
    · exact Or.inr (hcon L hL hLA)
  have hB : B ≤ Subgroup.normalizer (A : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => hp.2.2.2 x hx y hy
  have hle : pSpan Ω ≤ Subgroup.normalizer (A : Set G) :=
    pSpan_le fun L hL => by
      rcases hmem L hL with rfl | rfl
      · exact Subgroup.le_normalizer
      · exact hB
  rw [h.thmD.gen, top_le_iff] at hle
  obtain ⟨g, hg⟩ := h.thmD.trans A hp.1 B hp.2.1
  have hgN : g ∈ Subgroup.normalizer (A : Set G) := by
    rw [hle]
    exact Subgroup.mem_top g
  exact hp.2.2.1 (by rw [← hg, conjSub_eq_of_mem_normalizer hgN])

theorem card_inf_pCore_le {L : Subgroup G} (hL : L ∈ Ω) :
    Nat.card ↥(L ⊓ pCore 2 G) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hall : ∀ M ∈ Ω, 2 < Nat.card ↥(M ⊓ pCore 2 G) := by
    intro M hM
    obtain ⟨g, rfl⟩ := h.thmD.trans L hL M hM
    have hpc : conjSub g (pCore 2 G) = pCore 2 G :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance (MulAut.conj g)
    have hinf : conjSub g L ⊓ pCore 2 G = conjSub g (L ⊓ pCore 2 G) := by
      conv_lhs => rw [← hpc]
      exact (Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective).symm
    have hcard : Nat.card ↥(conjSub g (L ⊓ pCore 2 G)) = Nat.card ↥(L ⊓ pCore 2 G) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hinf, hcard]
    exact hlt
  obtain ⟨S, -⟩ := (IsPGroup.of_bot : IsPGroup 2 ↥(⊥ : Subgroup G)).exists_le_sylow
  have hQS : pCore 2 G ≤ (S : Subgroup G) := IsPGroup.le_sylow_of_normal pCore_isPGroup S
  have hS : ∀ M ∈ Ω, 2 < Nat.card ↥(M ⊓ (S : Subgroup G)) := fun M hM =>
    lt_of_lt_of_le (hall M hM) (Subgroup.card_le_of_le (inf_le_inf_left M hQS))
  obtain ⟨A, B, hp⟩ := h.exists_paired
  obtain ⟨L', hL', hLA, hLB⟩ := h.exists_third hp
  exact h.false_of_three S hp.1 hp.2.1 hL' hp.2.2.1 hLA.symm hLB.symm (hS _ hp.1) (hS _ hp.2.1)
    (hS _ hL')

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13

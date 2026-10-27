module

public import CFSG.GH74.Generic.BProg.B3.S1FinalJ4
public import CFSG.GH74.Generic.BProg.B3.S1FinalK2
public import CFSG.GH74.Generic.BProg.B3.S1IdentCenter
public import CFSG.GH74.Generic.BProg.B3.S1Lemma282
public import CFSG.GH74.Generic.BProg.B3.S1Lemma283b
public import CFSG.GH74.Generic.BProg.B3.S1Lemma285

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalMain

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs CFSG.GH74.Generic.BProg.B3.S1FinalJ1
  CFSG.GH74.Generic.BProg.B3.S1FinalJ2 CFSG.GH74.Generic.BProg.B3.S1FinalJ3
  CFSG.GH74.Generic.BProg.B3.S1FinalJ4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_core {L : Subgroup G} {c : G} (hc : c ∈ normalizer (L : Set G)) :
    c ∈ normalizer ((pPrimeCoreOf 2 L : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hL : L.map (MulAut.conj c).toMonoidHom = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
  have := pPrimeCoreOf_map_conj c L
  rw [hL] at this
  exact this.symm

omit [Finite G] in
theorem mem_cSec_of_commute {L : Subgroup G} {c : G} (hc : ∀ k ∈ L, k * c = c * k) :
    c ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  have hN : c ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have : c * k * c⁻¹ = k := by rw [← hc k hk]; group
      rw [this]; exact hk
    · intro hk
      have h2 : c * k * c⁻¹ * c = c * (c * k * c⁻¹) := hc _ hk
      have h4 : c * k = c * (c * k * c⁻¹) := by
        rw [← h2]
        group
      have : k = c * k * c⁻¹ := mul_left_cancel h4
      rw [this]; exact hk
  refine ⟨hN, mem_normalizer_core hN, fun k hk => ?_⟩
  have : ⁅k, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc k hk)
  rw [this]
  exact one_mem _

section Final


theorem s1_final (H : JSetup x K A a D J J₁ J₂)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  classical
  have hL : B1.QShape3SD (J0 a J) := qShape3SD_J0 H
  have hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J))) :=
    S1IdentCenter.odd_center_of_qShape3SD H.bar_quasisimple hL
  by_cases hin : ∀ e : ↥A, rhoA H e ∈ (MulAut.conj : J0 a J →* MulAut (J0 a J)).range
  · exact false_of_inner H hL hin
  push Not at hin
  obtain ⟨⟨c, hcA⟩, hcout⟩ := hin
  obtain ⟨d, δ, hd2, hdδ, hδ2, hδβ, hdA⟩ := exists_d H hL hodd hcA hcout
  have hle := card_Theta_le_four H hL hodd hcA hcout hd2 hdδ hδ2 hδβ hdA
  have hδ1 : δ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hδ2
    omega
  have hdnA : (d : G) ∉ A := d_not_mem_A H hcA hcout hdδ hδ1 hδβ
  have hdd : (d : G) * d = 1 := congrArg Subtype.val hd2
  have hdA' : ∀ e ∈ A, (d : G) * e = e * d := fun e he => (hdA e he).symm
  have hdJ₁ : ∀ j ∈ J₁, ⁅(d : G), j⁆ ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)) := by
    intro j hj
    have h := (H.hJ₁c hj).2.2 (d : G) d.2
    exact Th2.Bal.pPrimeCoreOf_le_of_pCompIn H.hc.obs.comp h
  obtain ⟨e, heA, he⟩ := S1FinalK2.s1_K_side H.hc h1 H.hax H.hS hdd hdA' hdJ₁
  have haT : a ∈ Theta A (d : G) J₂ := by
    refine ⟨Subgroup.mem_sup_left H.haA, (H.hS.A_norm H.haA).2,
      mem_normalizer_core (H.hS.A_norm H.haA).2, fun k hk => ?_⟩
    have h := (H.hS.commute a H.hS.u_mem k hk).2
    have hinv : ⁅k, a⁆ = ⁅a, k⁆⁻¹ := (commutatorElement_inv a k).symm
    rw [hinv]
    exact inv_mem h
  have hxT : x ∈ Theta A (d : G) J₂ :=
    ⟨Subgroup.mem_sup_left H.hxA, mem_cSec_of_commute (fun k hk => H.hJ₂comm_x k hk)⟩
  have heT : e⁻¹ * (d : G) ∈ Theta A (d : G) J₂ :=
    ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem heA))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), he⟩
  have hA2 : closure ({a, x} : Set G) ≤ Theta A (d : G) J₂ := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact haT
    · rw [Set.mem_singleton_iff.1 hg]; exact hxT
  have h4 := four_le_card_A2 H
  have heq : closure ({a, x} : Set G) = Theta A (d : G) J₂ :=
    Subgroup.eq_of_le_of_card_ge hA2 (by omega)
  have hA2A : closure ({a, x} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact H.haA
    · rw [Set.mem_singleton_iff.1 hg]; exact H.hxA
  have heA' : e⁻¹ * (d : G) ∈ A := hA2A (heq ▸ heT)
  apply hdnA
  have : (d : G) = e * (e⁻¹ * (d : G)) := by group
  rw [this]
  exact A.mul_mem heA heA'

end Final

section Setup


theorem jSetup_of_ctx (hB : KG531BPair) (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ J₁ J₂ : Subgroup G, JSetup x K A a D J J₁ J₂ := by
  have hQ1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) := B1.PilotS1.QShape1Big.qShape1 h1
  obtain ⟨-, -, hxA, -⟩ := s1_basic hc hQ1
  have hax : a ≠ x := s1_a_ne_x hc hQ1
  have ha1 : a ≠ 1 := fun h => by
    have := hc.obs.y_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨J₁, J₂, hS⟩ := s1_split_mod hc h1 hc.a_mem ha1 hax
  obtain ⟨-, hxS, hJ₂, hAJ⟩ := s1_lemma282 hc h1 hS
  have hJ₁ : ¬ J₁ ≤ J := s1_lemma283b_of_pair hB hc h1 hS hJ₂
  obtain ⟨J', -, hJ₁J', -, -, hJ'c⟩ := s1_lemma285 hc h1 hS hJ₂ hJ₁
  exact ⟨J₁, J₂, ⟨hc, hax, hxA, hxS, hAJ, hS, hJ₂, hJ₁J'.trans hJ'c⟩⟩

end Setup

section Big


theorem false_of_ctx_s1_big (hB : KG531BPair) (hc : Ctx21 G x K A a D J)
    (h1 : B1.PilotS1.QShape1Big (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  obtain ⟨J₁, J₂, H⟩ := jSetup_of_ctx hB hc h1
  exact s1_final H h1

end Big

end S1FinalMain

end CFSG.GH74.Generic.BProg.B3

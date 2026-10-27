module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.OutTrivial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.NormMax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocalEq
public import CFSG.Sporadic.Bridge.J4Surj

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

open CFSG.Sporadic.J4 CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_top_of_card_outer_eq_one {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (hout : Nat.card (Outer K) = 1) : K = ⊤ := by
  have hinner : inner K = ⊤ := by
    have h1 : (inner K).index = 1 := hout
    exact Subgroup.index_eq_one.1 h1
  rw [eq_top_iff]
  intro x _
  have hx : MulAut.conjNormal (H := K) x ∈ inner K := by rw [hinner]; exact Subgroup.mem_top _
  obtain ⟨k₀, hk₀⟩ := hx
  have hmem : (k₀ : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 := congrArg (fun φ : MulAut K => (φ ⟨k, hk⟩ : X)) hk₀
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv] at h2
    calc k * ((k₀ : X)⁻¹ * x) = (k₀ : X)⁻¹ * (k₀ * k * (k₀ : X)⁻¹) * x := by group
      _ = (k₀ : X)⁻¹ * (x * k * x⁻¹) * x := by rw [h2]
      _ = ((k₀ : X)⁻¹ * x) * k := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact k₀.2

theorem heisLocal_of_normMax_of_eq {p : ℕ} {X : Type*} [Group X] {R : Subgroup X}
    (hmax : NormMax R) (hEq : HeisLocalEq p R) : HeisLocal p R := by
  obtain ⟨hcard, hrest⟩ := hEq
  exact ⟨hcard, hmax, hrest⟩

theorem d2HeisLocalAt_J4_of_local
    (R₀ : Sylow 11 J) (hmax : NormMax (R₀ : Subgroup J))
    (hEq : HeisLocalEq 11 (R₀ : Subgroup J)) :
    D2HeisLocalAt (.sporadic .J4) fun p => p = 11 := by
  intro X _ _ K hKn hC ⟨e⟩ p hp R
  subst hp
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  have hout1 : Nat.card (Outer K) = 1 := by
    have h := @CFSG.Sporadic.J4Schreier.card_outer_congr K J _ (Subgroup.toGroup J) eKJ
    rw [h]
    exact card_outer_J_eq_one
  have hKtop : K = ⊤ := by
    have : K.Normal := hKn
    exact eq_top_of_card_outer_eq_one hC hout1
  have hfinJ : Finite J := Finite.of_equiv K eKJ.toEquiv
  have eXK : X ≃* K := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm)
  have eXJ : X ≃* J := eXK.trans eKJ
  refine ⟨by rw [hout1]; norm_num, ?_⟩
  have hsyl : Nat.card (R₀ : Subgroup J) = 11 ^ (Nat.card J).factorization 11 :=
    Sylow.card_eq_multiplicity R₀
  have hEqR : HeisLocalEq 11 (R : Subgroup X) := @heisLocalEq_sylow X J _ (Subgroup.toGroup J) _ hfinJ 11 _ eXJ _ hEq hsyl R
  exact heisLocal_of_normMax_of_eq (@NormMax.sylow_of_equiv X J _ (Subgroup.toGroup J) 11 _ _ hfinJ eXJ R₀ hmax R) hEqR

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

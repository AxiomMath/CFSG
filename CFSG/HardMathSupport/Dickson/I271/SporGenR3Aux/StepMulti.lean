module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Inner
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

section Perm

theorem perm_eq_one_of_card_lt {α : Type*} [Finite α] {p : ℕ} (hp : p.Prime)
    (hα : Nat.card α < p) {σ : Equiv.Perm α} (hσ : σ ^ p = 1) : σ = 1 := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact p.Prime := ⟨hp⟩
  have h : σ.supportᶜ.card ≡ Fintype.card α [MOD p] :=
    Equiv.Perm.card_compl_support_modEq (n := 1) (by simpa using hσ)
  have hα' : Fintype.card α < p := by rwa [Nat.card_eq_fintype_card] at hα
  have h1 : σ.supportᶜ.card ≤ Fintype.card α := Finset.card_le_univ _
  have h2 : σ.supportᶜ.card = Fintype.card α := Nat.ModEq.eq_of_lt_of_lt h (by omega) hα'
  have h3 : σ.support.card = 0 := by
    have h4 := Finset.card_compl σ.support
    have h5 : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
    omega
  exact Equiv.Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 h3)

end Perm

section Multi

variable {X : Type} [Group X] [Finite X]

theorem card_comp_le_of_list {p : ℕ} {N : Subgroup X} {L : List (Subgroup X)}
    (h : ∀ J : Subgroup X, GLAPComponent p N J → J ∈ L) :
    Nat.card {I : Subgroup X // GLAPComponent p N I} ≤ L.length := by
  classical
  have hsub : {I : Subgroup X | GLAPComponent p N I} ⊆ ↑L.toFinset := fun I hI => by
    simpa using h I hI
  calc Nat.card {I : Subgroup X // GLAPComponent p N I}
      = Set.ncard {I : Subgroup X | GLAPComponent p N I} := (Nat.card_coe_set_eq _)
    _ ≤ Set.ncard (↑L.toFinset : Set (Subgroup X)) := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le L

theorem le_normalizer_of_card_lt {p : ℕ} (hp : p.Prime) {K B J : Subgroup X} {a : X}
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B) (haB : a ∈ B)
    (hcard : Nat.card {I : Subgroup X //
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I} < p)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    B ≤ Subgroup.normalizer (J : Set X) := by
  classical
  set N : Subgroup X := K ⊓ Subgroup.centralizer ({a} : Set X) with hNdef
  have hBN : ∀ c ∈ B, c ∈ Subgroup.normalizer (N : Set X) := fun c hc =>
    mem_normalizer_inf (hBK hc) (Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.2 (CFSG.Open.IsElemAbelian.comm hBel hc haB)))
  have hconj : ∀ c ∈ B, ∀ I : Subgroup X, GLAPComponent p N I → GLAPComponent p N (GLBConj c I) := by
    intro c hc I hI
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hI c
    rwa [(mem_normalizer_iff_gLBConj_eq).1 (hBN c hc)] at h1
  intro b hb
  let Ω : Type := {I : Subgroup X // GLAPComponent p N I}
  let σ : Equiv.Perm Ω :=
    { toFun := fun I => ⟨GLBConj b I.1, hconj b hb I.1 I.2⟩
      invFun := fun I => ⟨GLBConj b⁻¹ I.1, hconj b⁻¹ (inv_mem hb) I.1 I.2⟩
      left_inv := fun I => Subtype.ext (gLBConj_inv_gLBConj b I.1)
      right_inv := fun I => Subtype.ext (gLBConj_gLBConj_inv b I.1) }
  have hpow : ∀ (n : ℕ) (I : Ω), ((σ ^ n) I).1 = GLBConj (b ^ n) I.1 := by
    intro n
    induction n with
    | zero => intro I; simp [gLBConj_one]
    | succ n ih =>
      intro I
      rw [pow_succ', Equiv.Perm.mul_apply]
      show GLBConj b ((σ ^ n) I).1 = _
      rw [ih, gLBConj_gLBConj, pow_succ]
  have hσp : σ ^ p = 1 := by
    ext I
    rw [hpow, hBel.2 b hb, gLBConj_one]
    rfl
  have hσ1 : σ = 1 := perm_eq_one_of_card_lt hp hcard hσp
  have hfix : GLBConj b J = J :=
    congrArg (fun τ : Equiv.Perm Ω => (τ ⟨J, hJ⟩).1) hσ1
  exact (mem_normalizer_iff_gLBConj_eq).2 hfix

theorem strong_of_dichotomy_multi {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hH : CompHyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : ∀ (a k : X) (hk : k ∈ K), a ∈ B → k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) →
      a ∉ Subgroup.centralizer (K : Set X) →
        ∃ L : List (Subgroup X), L.length < p ∧
          (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            J ∈ L) ∧
          ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            Good (PSimple p (J.subgroupOf K)) ∧ Rk (PQuot p (J.subgroupOf K)))
    (hE : ∀ A : Subgroup X, A ≤ B → ¬ IsCyclic ↥A → A ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
      (∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) →
        ∃ a ∈ A, a ≠ 1 ∧ ∀ I J : Subgroup X,
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J) :
    IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hH.quasi
  have hO : GLAPPrimeCore p ↥K = ⊥ := hH.primeCore
  have hdvd : p ∣ Nat.card K := hH.dvd
  have hBel : IsElemAbelian p B := hH.elem
  obtain ⟨hBN, h2⟩ := hN
  have hSC : IsSCp p (K ⊔ B) B := hH.sc
  obtain ⟨A, hAB, hAnc, hAf⟩ := exists_faithful_noncyclic hp hBel hBN h2
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAB.trans hBN
  have hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := fun a ha =>
    exists_inner_of_spor hp hp2 hOut hq hS hBN hBel (hAB ha)
  have hloc' : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_inner_loc hp hq hO hloc hAN hin
  have hdich : ∀ a ∈ A, a ≠ 1 → ∃ L : List (Subgroup X), L.length < p ∧
      (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J ∈ L) ∧
      ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        Good (PSimple p (J.subgroupOf K)) ∧ Rk (PQuot p (J.subgroupOf K)) := by
    intro a ha ha1
    obtain ⟨k, hk, hc⟩ := hin a ha
    exact hD a k hk (hAB ha) hc (not_mem_centralizer_of_faithful hAf ha ha1)
  have hcomp : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J := by
    intro a ha ha1 J hJ
    obtain ⟨L, hL, hmem, hgood⟩ := hdich a ha ha1
    have hcard := lt_of_le_of_lt (card_comp_le_of_list hmem) hL
    have hBN' : B ≤ Subgroup.normalizer (J : Set X) :=
      le_normalizer_of_card_lt hp hBN hBel (hAB ha) hcard hJ
    refine ⟨hBN', ?_⟩
    set C := Subgroup.centralizer ({a} : Set X) with hC
    have hBC : B ≤ C := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.2
        (CFSG.Open.IsElemAbelian.comm hBel (hAB ha) hb).symm
    have hJK : J ≤ K := hJ.1.trans inf_le_left
    have hJC : J ≤ C := hJ.1.trans inf_le_right
    have hJcomp : GLAPComponent p C J := glaPComponent_centralizer hp hH.comp.2.1 hJ
    have hsn : IsSubnormal J C := hJcomp.2.1
    obtain ⟨hcoreC, hcompC, hSCC, hBNC⟩ := recursionData hp hJcomp hBC hBN' hH.scp
    obtain ⟨hgoodJ, hrkJ⟩ := hgood J hJ
    let pS : PSimple p (J.subgroupOf K) ≃*
        (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J)) :=
      (pSimpleEquiv p (Subgroup.subgroupOfEquivOfLe hJK)).trans (pSimpleBarEquiv hp hJC hsn)
    let fQ : PQuot p (J.subgroupOf K) ≃* ↥(barX p C J) :=
      (pQuotEquiv p (Subgroup.subgroupOfEquivOfLe hJK)).trans (quotEquivBarX hp hJC hsn)
    have hbal := hIH (↥C ⧸ GLAPPrimeCore p ↥C) (barX p C J) (barX p C B)
      ⟨hp, hp2, hcoreC, hcompC, hSCC, hBNC⟩ (hGood _ _ pS hgoodJ) (hRk _ _ fQ hrkJ)
    exact stronglyLocallyOneBalanced_of_bar hp hsn hBN' hbal
  obtain ⟨a₀, ha₀A, ha₀1, huniq'⟩ := hE A hAB hAnc hAf hin
  have hc : ∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
      (∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨a₀, ha₀A, ha₀1, fun w hw _ hwB J hJ => ?_⟩
    have hwC := mem_normalizer_inf_centralizer_of_comm hw (hwB a₀ (hAB ha₀A))
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ w
    rw [(mem_normalizer_iff_gLBConj_eq).1 hwC] at h1
    exact (mem_normalizer_iff_gLBConj_eq).2 (huniq' _ J h1 hJ)
  exact engine_full ⟨hp, hp2, hq, hdvd, hBN, hBel, hSC, hAB, hAnc, hloc', hcomp⟩ hc

end Multi

end CFSG.HardMathSupport.Dickson.I271

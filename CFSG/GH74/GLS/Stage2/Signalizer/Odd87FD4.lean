module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87InvMax
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Arith
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem fd4_iso {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FD4 Y) : FD4 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  exact ⟨p, f, hp, hf, hp2, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem involved_qdSL_of_sl2_subgroup {T : Type} [Group T] (I : Subgroup T) {F : Type} [Field F] {p : ℕ}
    [Fact p.Prime] [CharP F p] (e : ↥I ≃* SL(2, F)) :
    CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) T := by
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hf : Function.Injective f := f.injective
  let φ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map f
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
    exact Matrix.map_injective hf this
  let ψ : CFSG.Glauberman.qdSL p →* T := I.subtype.comp (e.symm.toMonoidHom.comp φ)
  have hψ : Function.Injective ψ := I.subtype_injective.comp (e.symm.injective.comp hφ)
  exact ⟨ψ.range, ⊥, Subgroup.normal_bot,
    ⟨(QuotientGroup.quotientBot).trans (MonoidHom.ofInjective hψ).symm⟩⟩

section Certs

theorem fd4_outAbel {Y : Type} [Group Y] [Finite Y] (h : FD4 Y) : OutAbelian Y := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := h
  have htw : TwistedChevalleyModel Y .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
    CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form hp hp2 hf M hM σ hσ
  exact outAbelian_of_mulEquiv e.symm (outAbelian_of_hom Θ (comm_of_isCyclic_group hcyc) hker)

theorem td4_bad_of_model {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hT : LieModel T .trialityD4 0 p e) : ∀ k : Kind, ¬ KindFactor k T := by
  intro k
  have : Fact p.Prime := ⟨hp⟩
  have heven : 2 ∣ Nat.card T := by
    by_contra hnd
    have hodd : Odd (Nat.card T) := Nat.odd_iff.2 (by omega)
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (hcomm a b)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 heven
  obtain ⟨F₁, F₂, _, _, _, _, S, hc₁, hc₂, hSz⟩ := CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hT z hz
  have : Fintype F₁ := Fintype.ofFinite F₁
  have hchar : CharP F₁ p := by
    refine charP_of_card_eq_prime_pow (f := 3 * e) ?_
    rw [← Nat.card_eq_fintype_card, hc₁, ← pow_mul, mul_comm]
  let I₁ : Subgroup T := S.I₁.map (centralizer ({z} : Set T)).subtype
  let eI : ↥I₁ ≃* SL(2, F₁) :=
    ((S.I₁.equivMapOfInjective (centralizer ({z} : Set T)).subtype
      (centralizer ({z} : Set T)).subtype_injective).symm).trans S.e₁
  have hinv : CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) T :=
    involved_qdSL_of_sl2_subgroup I₁ eI
  have hcardI : Nat.card ↥I₁ = (p ^ e) ^ 3 * (((p ^ e) ^ 3) ^ 2 - 1) := by
    rw [Nat.card_congr eI.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hc₁]
  have hc3 : 3 ≤ p ^ e := by
    calc 3 ≤ p := by
          have := hp.two_le
          omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  have hord : ¬ Nat.card T ∣ Nat.factorial 11 := fun hd =>
    not_card_sl2_dvd_factorial_cube hc3
      (hcardI ▸ (Subgroup.card_subgroup_dvd_card I₁).trans hd)
  exact not_kindFactor hp2 hinv hord

theorem equiv_modelUniv_d4 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hY : LieModel Y .trialityD4 0 p f) : Nonempty (Y ≃* (modelUniv .trialityD4 0 p f hp).K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have hσq : ∀ c : GaloisField p (3 * f), iterateFrobenius (GaloisField p (3 * f)) p f c = c ^ p ^ f :=
    fun c => iterateFrobenius_def p f c
  have hYq := CFSG.Timmesfeld.lieModel_twistedD4_quotient hp hf hK _ hσq
  obtain ⟨E⟩ := Upgrade.lieModel_unique hp2 (by trivial) hY hYq
  have hZ : Subgroup.center (modelUniv .trialityD4 0 p f hp).K = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0 hf
  exact ⟨E.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem fd4_mult (hMult : D4Mult) {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hZ2 : IsPGroup 2 ↥(center L)) (hF : FD4 (L ⧸ center L)) : center L = ⊥ := by
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  exact hMult L hL hZ2 p f hp hf hp2 hm

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

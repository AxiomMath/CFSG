module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIn

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def InnerOneBalanceAt (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ d ∈ innerAut K, d ^ p = 1 → d ≠ 1 → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut K))) = ⊥

theorem exists_ne_one_of_card_eq_prime {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    {D : Subgroup M} (hcard : Nat.card D = p ^ 1) : ∃ d ∈ D, d ≠ 1 := by
  have hnt : 1 < Nat.card D := by rw [hcard, pow_one]; exact hp.one_lt
  have : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hnt
  obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
  exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩

theorem isLocallyBalancedAbs_one_of_inner_outer_at {p : ℕ} (hp : p.Prime) {S : Type*} [Group S]
    (hin : InnerOneBalanceAt p S)
    (hout : ∀ δ : MulAut S, δ ^ p = 1 → δ ∉ innerAut S →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H → δ ∈ Subgroup.normalizer (H : Set (MulAut S)) →
        GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({δ} : Set (MulAut S))) = ⊥) :
    IsLocallyBalancedAbs p 1 S := by
  intro D hD hcard H hH hDH
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_card_eq_prime hp hcard
  have hdp : d ^ p = 1 := hD.2 d hdD
  refine localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 ?_
  by_cases hdin : d ∈ innerAut S
  · exact hin d hdin hdp hd1 H hH
  · exact hout d hdp hdin H hH (hDH hdD)

theorem glaPPrimeCore_eq_top_of_not_dvd {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card Y) : GLAPPrimeCore p Y = ⊤ := by
  refine top_le_iff.1 (le_sSup ⟨inferInstance, ?_⟩)
  rw [Subgroup.card_top]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 h

theorem isLocallyBalancedAbs_of_subsingleton {p k : ℕ} {T : Type*} [Group T] [Subsingleton T] :
    IsLocallyBalancedAbs p k T := by
  intro D _ _ H _ _
  have : Subsingleton (MulAut T) := ⟨fun a b => MulEquiv.ext fun _ => Subsingleton.elim _ _⟩
  exact eq_bot_iff.2 fun x _ => Subgroup.mem_bot.2 (Subsingleton.elim x 1)

theorem subsingleton_barOf_of_not_dvd {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    {K : Subgroup X} (h : ¬ p ∣ Nat.card K) : Subsingleton (barOf p K) := by
  have htop := glaPPrimeCore_eq_top_of_not_dvd hp h
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y => exact QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _)

theorem isCompLocallyBalanced_of_abs {P : ℕ → TauCeti.LieTypeIndex → Prop}
    (h : ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), P p d.1 →
      IsLocallyBalancedAbs p 1 (TauCeti.CFSGIndex.lie d).Group)
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) {K : Subgroup X} (A : Subgroup X)
    (hq : CFSG.Open.IsQuasisimple ↥K) (hK : IsLieQuot ↥K (P p)) :
    IsCompLocallyBalanced p 1 A K := by
  by_cases hdvd : p ∣ Nat.card ↥K
  · have hNZ : GLAPPrimeCore p ↥K ≤ Subgroup.center ↥K :=
      Bal209TwoInAux.pPrimeCore_le_center_of_quasisimple hq hp hdvd
    obtain ⟨d, hd, ⟨e⟩⟩ := hK
    have hS : IsLocallyBalancedAbs p 1 (↥K ⧸ Subgroup.center ↥K) :=
      IsLocallyBalancedAbs.of_mulEquiv e (h p d hd)
    exact (Bal209TwoInAux.isLocallyBalancedAbs_quotient_of_central hq.1 hNZ hS).isLocallyBalanced _
  · have := subsingleton_barOf_of_not_dvd hp hdvd
    exact isLocallyBalancedAbs_of_subsingleton.isLocallyBalanced _

@[expose] def Bal207LocalBalAbs : Prop :=
  ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), Bal207Index p d.1 →
    IsLocallyBalancedAbs p 1 (TauCeti.CFSGIndex.lie d).Group

theorem bal207LocalBal_of_abs (h : Bal207LocalBalAbs) : Bal207LocalBal := by
  intro X _ _ _ p K A hp _ hK hLie _ _
  exact isCompLocallyBalanced_of_abs h hp A hK.2.2 hLie

end CFSG.HardMathSupport.Dickson.Bal207

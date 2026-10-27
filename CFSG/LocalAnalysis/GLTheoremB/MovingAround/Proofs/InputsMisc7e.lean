module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7d
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
import CFSG.RankThree.PartOne.KLC.D4OutCentral
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7e

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem mem_inner_of_congr {K C : Type*} [Group K] [Group C] (e : K ≃* C) {α : MulAut K}
    (h : MulAut.congr e α ∈ inner C) : α ∈ inner K := by
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at h
  obtain ⟨β, hβ, hβα⟩ := h
  have hβα' : β = α := (MulAut.congr e).injective hβα
  rwa [← hβα']

@[expose] def E6InndiagSylowThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ∀ (S : Sylow 3 (adjointGroup Tag.E6 K)) (α : MulAut (adjointGroup Tag.E6 K)),
      α ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag K → (∃ k : ℕ, α ^ 3 ^ k = 1) →
      (∀ x ∈ (S : Subgroup (adjointGroup Tag.E6 K)), α x = x) → α ∈ inner (adjointGroup Tag.E6 K)

@[expose] def TwistedE6InndiagSylowThree :
    Prop :=
  ∀ (p f : ℕ), p.Prime → 1 ≤ f → 3 ∣ p ^ f + 1 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (p ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ (S : Sylow 3 (twistedE6RootGroup K σ)) (α : MulAut (twistedE6RootGroup K σ)),
      α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ → (∃ k : ℕ, α ^ 3 ^ k = 1) →
      (∀ x ∈ (S : Subgroup (twistedE6RootGroup K σ)), α x = x) → α ∈ twistedE6Inn K σ

theorem ordE6_sq_eq_mul {q : ℕ} (hq : 1 ≤ q) (h3 : 3 ∣ q + 1) :
    ∃ I : ℕ, CFSG.Open.ordE6 (q ^ 2) = CFSG.Open.ordTwistedE6 q * I ∧ ¬ 3 ∣ I := by
  have hsq : ∀ d : ℕ, (q ^ 2) ^ d - 1 = (q ^ d - 1) * (q ^ d + 1) := by
    intro d
    rw [← pow_mul, mul_comm 2 d, pow_mul, show (q ^ d) ^ 2 - 1 = (q ^ d) ^ 2 - 1 ^ 2 by rw [one_pow],
      Nat.sq_sub_sq, mul_comm]
  have h3sq : 3 ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h3.mul_right _
  refine ⟨q ^ 36 * (q ^ 12 + 1) * (q ^ 9 - 1) * (q ^ 8 + 1) * (q ^ 6 + 1) * (q ^ 5 - 1) *
    (q ^ 2 + 1), ?_, ?_⟩
  · rw [CFSG.Open.ordE6, CFSG.Open.ordTwistedE6, Nat.gcd_eq_left h3, Nat.gcd_eq_left h3sq, hsq 12,
      hsq 9, hsq 8, hsq 6, hsq 5, hsq 2]
    obtain ⟨t, ht⟩ : 3 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
        (q ^ 5 + 1) * (q ^ 2 - 1) := Dvd.dvd.mul_left h3sq _
    have e : (q ^ 2) ^ 36 * ((q ^ 12 - 1) * (q ^ 12 + 1)) * ((q ^ 9 - 1) * (q ^ 9 + 1)) *
        ((q ^ 8 - 1) * (q ^ 8 + 1)) * ((q ^ 6 - 1) * (q ^ 6 + 1)) * ((q ^ 5 - 1) * (q ^ 5 + 1)) *
          ((q ^ 2 - 1) * (q ^ 2 + 1)) = (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
            (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) * (q ^ 36 * (q ^ 12 + 1) * (q ^ 9 - 1) *
              (q ^ 8 + 1) * (q ^ 6 + 1) * (q ^ 5 - 1) * (q ^ 2 + 1)) := by
      generalize q ^ 12 - 1 = a12
      generalize q ^ 9 - 1 = a9
      generalize q ^ 8 - 1 = a8
      generalize q ^ 6 - 1 = a6
      generalize q ^ 5 - 1 = a5
      generalize q ^ 2 - 1 = a2
      ring
    rw [e, ht, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3),
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  · intro hdvd
    have h0 := (ZMod.natCast_eq_zero_iff _ 3).2 hdvd
    have hq3 : (q : ZMod 3) = 2 := by
      have h1 := (ZMod.natCast_eq_zero_iff (q + 1) 3).2 h3
      push_cast at h1
      have h2 : (q : ZMod 3) = -1 := eq_neg_of_add_eq_zero_left h1
      rw [h2]
      decide
    have h9 : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ hq
    have h5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
    push_cast [Nat.cast_sub h9, Nat.cast_sub h5] at h0
    rw [hq3] at h0
    revert h0
    decide

section Reductions


theorem resOddE6_of_inndiag (h : E6InndiagSylowThree) : InputsMisc7.ResOddE6 := by
  intro K _ _ hs hnab ℓ f hch h3 P hP _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hm⟩ := hch
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6 hm
  obtain ⟨Θ, -, -, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) F
  have hZ := InputsMisc5.center_eq_bot_of_simple hs hnab
  let S : Sylow 3 K := ⟨P, hP.2.1, fun {Q} hQ hle => hP.2.2 Q le_top hQ hle⟩
  haveI : Finite (RingAut F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  haveI : NeZero (exactE Tag.E6) := ⟨(exactE_pos Tag.E6).ne'⟩
  have hG' : CFSG.HasNormalPComplement 3 (RingAut F × Multiplicative (ZMod (exactE Tag.E6))) :=
    InputsMisc7.hasNormalPComplement_of_isMulCommutative
      ⟨⟨fun x y => Prod.ext (CFSG.RankThree.PartOne.OutStructure.ringAut_comm F _ _)
        (mul_comm _ _)⟩⟩
  refine InputsMisc7.hasNormalPComplement_fixerAut_of_hom hZ S
    (Θ.comp (MulAut.congr e).toMonoidHom) hG' fun α hαp hα1 hαfix => ?_
  set α' := MulAut.congr e α with hα'
  obtain ⟨g, a, hga⟩ := (hker α').1 hα1
  have hα'eq : α' = MulAut.conj g * rootDiagAut Tag.E6 F a := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hga x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_rootDiagAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  have hmem : α' ∈ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag F := by
    rw [hα'eq]
    exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hp' : ∃ k : ℕ, α' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hαp
    exact ⟨k, by rw [hα', ← map_pow, hk, map_one]⟩
  let S' : Sylow 3 (adjointGroup Tag.E6 F) :=
    S.mapSurjective (f := (e : K →* adjointGroup Tag.E6 F)) e.surjective
  have hfix' : ∀ x ∈ (S' : Subgroup (adjointGroup Tag.E6 F)), α' x = x := by
    rintro _ ⟨y, hy, rfl⟩
    show e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hαfix y hy]
  exact mem_inner_of_congr e (h F (by rw [hF]; exact h3) S' α' hmem hp' hfix')

theorem resOddTwE6_of_inndiag (h : TwistedE6InndiagSylowThree) : InputsMisc7.ResOddTwE6 := by
  intro X _ _ hs hnab r f hch h3 P hP _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := hch
  have hm' : TwistedChevalleyModel X .E6 (r ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hrp hf1 K hcard σ' hσ'
  have hZ := InputsMisc5.center_eq_bot_of_simple hs hnab
  let S : Sylow 3 X := ⟨P, hP.2.1, fun {Q} hQ hle => hP.2.2 Q le_top hQ hle⟩
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) DFunLike.coe_injective
  have hG' : CFSG.HasNormalPComplement 3 (RingAut K) :=
    InputsMisc7.hasNormalPComplement_of_isMulCommutative
      ⟨⟨fun x y => CFSG.RankThree.PartOne.OutStructure.ringAut_comm K x y⟩⟩
  let e' : X ≃* twistedE6RootGroup K σ' := e.trans E
  refine InputsMisc7.hasNormalPComplement_fixerAut_of_hom hZ S
    (Θ.comp (MulAut.congr e').toMonoidHom) hG' fun α hαp hα1 hαfix => ?_
  set α' := MulAut.congr e' α with hα'
  have hmem : α' ∈ twistedE6Inn K σ' ⊔ twistedE6Diag K σ' := by
    rw [← hker]
    exact hα1
  have hp' : ∃ k : ℕ, α' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hαp
    exact ⟨k, by rw [hα', ← map_pow, hk, map_one]⟩
  let S' : Sylow 3 (twistedE6RootGroup K σ') :=
    S.mapSurjective (f := (e' : X →* twistedE6RootGroup K σ')) e'.surjective
  have hfix' : ∀ x ∈ (S' : Subgroup (twistedE6RootGroup K σ')), α' x = x := by
    rintro _ ⟨y, hy, rfl⟩
    show e' (α (e'.symm (e' y))) = e' y
    rw [e'.symm_apply_apply, hαfix y hy]
  exact mem_inner_of_congr e' (h r f hrp hf1 h3 K hcard σ' hσ' S' α' hmem hp' hfix')

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem twistedE6InndiagSylowThree_of_E6 (h : E6InndiagSylowThree) : TwistedE6InndiagSylowThree := by
  intro p f hp hf h3 K _ _ hK σ hσ S₀ α hα hα3 hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  haveI : Finite (ModGL Tag.E6 K) := finite_modGL
  have hle : twistedE6RootGroup K σ ≤ adjointGroup Tag.E6 K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans inf_le_left
  set ι : twistedE6RootGroup K σ →* adjointGroup Tag.E6 K := Subgroup.inclusion hle with hιdef
  have hι : Function.Injective ι := Subgroup.inclusion_injective hle
  obtain ⟨-, -, -, -, -, hcoe, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  obtain ⟨_, ⟨g₀, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hα
  set α' := MulAut.conj g₀ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u with hα'
  set ĝ : ModGL TwistTag.E6.tag K := (g₀ : ModGL TwistTag.E6.tag K) *
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
      (compatDiag TwistTag.E6 σ.toRingHom u) with hĝdef
  have hĝ : ĝ ∈ e6InndiagGL K :=
    mul_mem (adjointGroup_le_e6InndiagGL K (hle g₀.2)) (rootDiagUnit_mem_e6InndiagGL _)
  set ĝA : ↥(e6InndiagGL K) := ⟨ĝ, hĝ⟩ with hĝA
  have hαx : ∀ x : twistedE6RootGroup K σ,
      ((α' x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = ĝ * x * ĝ⁻¹ := by
    intro x
    rw [hα', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hcoe, hĝdef, mul_inv_rev]
    simp only [mul_assoc]
  have hαxn : ∀ (n : ℕ) (x : twistedE6RootGroup K σ),
      (((α' ^ n) x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        ĝ ^ n * x * (ĝ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hαx, pow_succ]
      group
  have hfixn : ∀ (n : ℕ), ∀ x ∈ (S₀ : Subgroup (twistedE6RootGroup K σ)), (α' ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  set αs := e6InndiagConj K ĝA with hαs
  have hαsn : ∀ (n : ℕ) (y : adjointGroup Tag.E6 K),
      (((αs ^ n) y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((ĝA ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) * y *
          ((ĝA ^ n : ↥(e6InndiagGL K)) : ModGL Tag.E6 K)⁻¹ := by
    intro n y
    rw [hαs, ← map_pow, e6InndiagConj_apply]
  obtain ⟨a, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos αs).ne' 3 (by norm_num)
  have hβmem : αs ^ m ∈ e6Inndiag K := by
    rw [← range_e6InndiagConj]
    exact ⟨ĝA ^ m, by rw [map_pow]⟩
  have hβ3 : (αs ^ m) ^ 3 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  obtain ⟨I, hI, hI3⟩ := ordE6_sq_eq_mul hq1 h3
  have hcardC : Nat.card (adjointGroup Tag.E6 K) = CFSG.Open.ordE6 ((p ^ f) ^ 2) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK]
  have hcardC₀ : Nat.card (twistedE6RootGroup K σ) = CFSG.Open.ordTwistedE6 (p ^ f) :=
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 hp hf hK σ.toRingHom hσ
  have hS₀p : IsPGroup 3 (S₀.map ι) := S₀.isPGroup'.map ι
  have hidx : ¬ 3 ∣ (S₀.map ι).index := by
    have e1 := Subgroup.index_mul_card (S₀.map ι)
    have e2 := Subgroup.index_mul_card (S₀ : Subgroup (twistedE6RootGroup K σ))
    rw [Subgroup.card_map_of_injective hι, hcardC, hI, ← hcardC₀, ← e2] at e1
    have hpos : 0 < Nat.card (S₀ : Subgroup (twistedE6RootGroup K σ)) := Nat.card_pos
    have e3 : (S₀.map ι).index = (S₀ : Subgroup (twistedE6RootGroup K σ)).index * I := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [e1]
      ring
    rw [e3]
    intro h3d
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3d with h' | h'
    · exact Sylow.not_dvd_index S₀ h'
    · exact hI3 h'
  let S : Sylow 3 (adjointGroup Tag.E6 K) := hS₀p.toSylow hidx
  have hS : (S : Subgroup (adjointGroup Tag.E6 K)) = S₀.map ι := IsPGroup.toSylow_coe hS₀p hidx
  have hβfix : ∀ y ∈ (S : Subgroup (adjointGroup Tag.E6 K)), (αs ^ m) y = y := by
    rw [hS]
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [hαsn]
    have hT : ĝ ^ m * (x : ModGL TwistTag.E6.tag K) * (ĝ ^ m)⁻¹ = (x : ModGL TwistTag.E6.tag K) := by
      rw [← hαxn m x, hfixn m x hx]
    exact hT
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK, show (p ^ f) ^ 2 - 1 = (p ^ f) ^ 2 - 1 ^ 2 by rw [one_pow], Nat.sq_sub_sq]
    exact h3.mul_right _
  obtain ⟨c, hc⟩ := h K h3K S (αs ^ m) hβmem ⟨a, hβ3⟩ hβfix
  have hZ : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hca : c ^ 3 ^ a = 1 := by
    apply InputsMisc5.conj_injective_of_center hZ
    rw [map_pow, hc, hβ3, map_one]
  have hcS : c ∈ (S : Subgroup (adjointGroup Tag.E6 K)) := by
    refine GL83.I710.mem_sylow_of_commute S ⟨a, hca⟩ fun y hy => ?_
    have := hβfix y hy
    rw [← hc, MulAut.conj_apply] at this
    calc c * y = c * y * c⁻¹ * c := by group
      _ = y * c := by rw [this]
  rw [hS] at hcS
  obtain ⟨x₀, -, rfl⟩ := hcS
  have hgm : ((ĝA ^ m : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) =
      ((ι x₀ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) := by
    have hinj := e6InndiagConj_injective K (by rw [hK]; nlinarith)
    have hx₀ : ((ι x₀ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) ∈ e6InndiagGL K :=
      adjointGroup_le_e6InndiagGL K (ι x₀).2
    have e : e6InndiagConj K (ĝA ^ m) = e6InndiagConj K ⟨_, hx₀⟩ := by
      rw [map_pow, ← hαs, ← hc]
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [e6InndiagConj_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
    exact congrArg Subtype.val (hinj e)
  have hgmT : ĝ ^ m = (x₀ : ModGL TwistTag.E6.tag K) := by
    have h1 : ((ĝA ^ m : ↥(e6InndiagGL K)) : ModGL Tag.E6 K) = ĝ ^ m := by
      rw [Subgroup.coe_pow]
      rfl
    rw [← h1, hgm]
    rfl
  have hαm : α' ^ m ∈ twistedE6Inn K σ := by
    refine ⟨x₀, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [MulAut.conj_apply, hαxn, hgmT, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨b, hb⟩ := hα3
  have hcop : Nat.Coprime m (orderOf α') := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hb) ?_
    exact Nat.Coprime.pow_right b
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj]
  exact Subgroup.pow_mem _ hαm j

end Reductions

section Cycle

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem exists_three_pow_not_fix [Finite A] {F y z : X} {c : A} (hcF : c • F = y) (hcy : c • y = z)
    (hcz : c • z = F) (hyF : y ≠ F) (hzF : z ≠ F) :
    ∃ n : ℕ, (∃ k : ℕ, (c ^ n) ^ 3 ^ k = 1) ∧ (c ^ n) • F ≠ F := by
  obtain ⟨a, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3 (by norm_num)
  refine ⟨m, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · have h3 : c ^ 3 ∈ MulAction.stabilizer A F := by
      rw [MulAction.mem_stabilizer_iff, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, hcF, hcy,
        hcz]
    have hj : (c ^ 3) ^ (m / 3) • F = F := (Subgroup.pow_mem _ h3 _)
    have hm : c ^ m = c ^ (m % 3) * (c ^ 3) ^ (m / 3) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hm, mul_smul, hj]
    have hm0 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm0 with h1 | h2
    · rw [h1, pow_one, hcF]
      exact hyF
    · rw [h2, pow_two, mul_smul, hcF, hcy]
      exact hzF

theorem not_cycle_of_three_elements [Finite A] {F y z : X} (C : Subgroup A)
    (hT : ∀ c ∈ C, (∃ k : ℕ, c ^ 3 ^ k = 1) → c • F = F) (hyF : y ≠ F) (hzF : z ≠ F) {c : A}
    (hc : c ∈ C) (hcF : c • F = y) (hcy : c • y = z) (hcz : c • z = F) : False := by
  obtain ⟨n, hn3, hnF⟩ := exists_three_pow_not_fix hcF hcy hcz hyF hzF
  exact hnF (hT _ (C.pow_mem hc n) hn3)

theorem fix_third [Finite A] {F y z : X} (hOF : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    (hOy : ∀ a : A, a • y = F ∨ a • y = y ∨ a • y = z)
    (hOz : ∀ a : A, a • z = F ∨ a • z = y ∨ a • z = z) (hyz : y ≠ z) (hyF : y ≠ F) (hzF : z ≠ F)
    (C : Subgroup A) (hT : ∀ c ∈ C, (∃ k : ℕ, c ^ 3 ^ k = 1) → c • F = F) {c₀ : A} (hc₀ : c₀ ∈ C)
    (hc₀F : c₀ • F = y) : ∀ d ∈ C, d • z = z := by
  have hcyc : ∀ {c : A}, c ∈ C → c • F = y → c • y = z → c • z = F → False :=
    fun hc => not_cycle_of_three_elements C hT hyF hzF hc
  have hcyc' : ∀ {c : A}, c ∈ C → c • F = z → c • z = y → c • y = F → False :=
    fun hc => not_cycle_of_three_elements (y := z) (z := y) C hT hzF hyF hc
  have hinj : ∀ (a : A) {u v : X}, u ≠ v → a • u ≠ a • v := fun a u v h e => h (smul_left_cancel a e)
  have hc₀y : c₀ • y = F := by
    rcases hOy c₀ with h | h | h
    · exact h
    · exact absurd (h.trans hc₀F.symm) (hinj c₀ hyF)
    · exfalso
      rcases hOz c₀ with h' | h' | h'
      · exact hcyc hc₀ hc₀F h h'
      · exact hinj c₀ hzF (h'.trans hc₀F.symm)
      · exact hinj c₀ hyz (h.trans h'.symm)
  have hc₀z : c₀ • z = z := by
    rcases hOz c₀ with h | h | h
    · exact absurd (h.trans hc₀y.symm) (hinj c₀ hyz.symm)
    · exact absurd (h.trans hc₀F.symm) (hinj c₀ hzF)
    · exact h
  intro d hd
  by_contra hdz
  have he : c₀ * d ∈ C := C.mul_mem hc₀ hd
  rcases hOz d with h | h | h
  ·
    rcases hOF d with h' | h' | h'
    · exact hinj d hzF.symm (h'.trans h.symm)
    ·
      rcases hOy d with h'' | h'' | h''
      · exact hinj d hyz (h''.trans h.symm)
      · exact hinj d hyF (h''.trans h'.symm)
      · exact hcyc hd h' h'' h
    ·
      rcases hOy d with h'' | h'' | h''
      · exact hinj d hyz (h''.trans h.symm)
      · exact hcyc' he (by rw [mul_smul, h', hc₀z]) (by rw [mul_smul, h, hc₀F])
          (by rw [mul_smul, h'', hc₀y])
      · exact hinj d hyF (h''.trans h'.symm)
  ·
    rcases hOF d with h' | h' | h'
    ·
      rcases hOy d with h'' | h'' | h''
      · exact hinj d hyF (h''.trans h'.symm)
      · exact hinj d hyz (h''.trans h.symm)
      · exact hcyc he (by rw [mul_smul, h', hc₀F]) (by rw [mul_smul, h'', hc₀z])
          (by rw [mul_smul, h, hc₀y])
    · exact hinj d hzF.symm (h'.trans h.symm)
    ·
      rcases hOy d with h'' | h'' | h''
      · exact hcyc' hd h' h h''
      · exact hinj d hyz (h''.trans h.symm)
      · exact hinj d hyF (h''.trans h'.symm)
  · exact hdz h

theorem exists_fix_of_three_elements [Finite A] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z) {κ : A} (hκF : κ • F = F) (hκy : κ • y = z)
    (hκz : κ • z = y) (hyz : y ≠ z) (C : Subgroup A)
    (hT : ∀ c ∈ C, (∃ k : ℕ, c ^ 3 ^ k = 1) → c • F = F) : ∃ g : A, ∀ c ∈ C, c • (g • F) = g • F := by
  by_cases hall : ∀ c ∈ C, c • F = F
  · exact ⟨1, fun c hc => by rw [one_smul]; exact hall c hc⟩
  push Not at hall
  obtain ⟨c₀, hc₀, hc₀F⟩ := hall
  have hFy : y ≠ F := by
    intro h
    apply hyz
    rw [← hκy, h, hκF]
  have hFz : z ≠ F := by
    intro h
    apply hFy
    have : κ • y = κ • F := by rw [hκy, hκF, h]
    exact smul_left_cancel κ this
  have hOw : ∀ g : A, ∀ a : A, a • (g • F) = F ∨ a • (g • F) = y ∨ a • (g • F) = z := fun g a => by
    rw [← mul_smul]
    exact hO (a * g)
  rcases hO c₀ with h | h | h
  · exact absurd h hc₀F
  ·
    have hz : (κ * c₀) • F = z := by rw [mul_smul, h, hκy]
    refine ⟨κ * c₀, fun c hc => ?_⟩
    rw [hz]
    exact fix_third hO (fun a => by have := hOw c₀ a; rwa [h] at this)
      (fun a => by have := hOw (κ * c₀) a; rwa [hz] at this) hyz hFy hFz C hT hc₀ h c hc
  ·
    have hy : (κ * c₀) • F = y := by rw [mul_smul, h, hκz]
    have hO' : ∀ a : A, a • F = F ∨ a • F = z ∨ a • F = y := fun a => by
      rcases hO a with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
      · exact Or.inr (Or.inl h')
    refine ⟨κ * c₀, fun c hc => ?_⟩
    rw [hy]
    exact fix_third hO' (fun a => by have := hOw c₀ a; rw [h] at this; tauto)
      (fun a => by have := hOw (κ * c₀) a; rw [hy] at this; tauto) hyz.symm hFz hFy C hT hc₀ h c hc

end Cycle

section NoCycle

variable {p : ℕ}

theorem hasNormalPComplement_of_quotient_central {G : Type*} [Group G] [Finite G] [hp : Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hq : CFSG.HasNormalPComplement p (G ⧸ N))
    (hN : ∀ n ∈ N, (∃ k : ℕ, n ^ p ^ k = 1) → n ∈ Subgroup.center G) :
    CFSG.HasNormalPComplement p G := by
  obtain ⟨M, hMn, hMc, hMq⟩ := hq
  haveI := hMn
  haveI : (M.comap (QuotientGroup.mk' N)).Normal := Subgroup.Normal.comap hMn _
  refine InputsMisc5.hasNormalPComplement_of_normal (N := M.comap (QuotientGroup.mk' N)) ?_ ?_
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hMq (QuotientGroup.mk (QuotientGroup.mk' N g))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_comap, map_pow]
    exact hk
  · refine InputsMisc5.hasNormalPComplement_of_pElements_central fun r hr => ?_
    obtain ⟨k, hk⟩ := hr
    have hrk : (r : G) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : QuotientGroup.mk' N (r : G) = 1 :=
      InputsMisc5.eq_one_of_pow_of_coprime hMc r.2 (by rw [← map_pow, hrk, map_one])
    have hcen := hN _ ((QuotientGroup.eq_one_iff _).1 h1) ⟨k, hrk⟩
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hcen (x : G)

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185 (fixerAut mem_fixerAut)

theorem hasNormalPComplement_fixerAut_of_no_cycle {K : Type} [Group K] [Finite K]
    (hZ : Subgroup.center K = ⊥) {X : Type*} [MulAction (MulAut K) X] {F y z : X}
    (hO : ∀ a : MulAut K, a • F = F ∨ a • F = y ∨ a • F = z) {κ : MulAut K} (hκF : κ • F = F)
    (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z) {D : Subgroup (MulAut K)}
    (hD : ∀ δ ∈ D, ∀ k : ℕ, δ ^ 3 ^ k ∈ inner K → δ ∈ inner K)
    (hE : ∀ a b : MulAut K, a • F = F → b • F = F → ⁅a, b⁆ ∈ D) (P : Sylow 3 K)
    (hT : ∀ α : MulAut K, (∃ k : ℕ, α ^ 3 ^ k = 1) → (∀ x ∈ (P : Subgroup K), α x = x) →
      α • F = F) :
    CFSG.HasNormalPComplement 3 ↥(fixerAut (P : Subgroup K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_fix_of_three_elements hO hκF hκy hκz hyz (fixerAut (P : Subgroup K))
    (fun c hc hc3 => hT c hc3 (mem_fixerAut.1 hc))
  set C := fixerAut (P : Subgroup K) with hC
  set D' : Subgroup (MulAut K) := D.comap (MulAut.conj g⁻¹).toMonoidHom with hD'
  have hmemD' : ∀ x, x ∈ D' ↔ g⁻¹ * x * g ∈ D := by
    intro x
    rw [hD', Subgroup.mem_comap]
    simp [MulAut.conj_apply]
  have hstab : ∀ c ∈ C, (g⁻¹ * c * g) • F = F := by
    intro c hc
    rw [mul_smul, mul_smul, hg c hc, inv_smul_smul]
  have hCD : ∀ c ∈ C, ∀ d ∈ C, ⁅c, d⁆ ∈ D' := by
    intro c hc d hd
    rw [hmemD']
    have e : g⁻¹ * ⁅c, d⁆ * g = ⁅g⁻¹ * c * g, g⁻¹ * d * g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hE _ _ (hstab c hc) (hstab d hd)
  haveI : (D'.subgroupOf C).Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have e : ((c * n * c⁻¹ : C) : MulAut K) = ⁅(c : MulAut K), (n : MulAut K)⁆ * n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact D'.mul_mem (hCD c c.2 n n.2) hn⟩
  have hq : CFSG.HasNormalPComplement 3 (C ⧸ D'.subgroupOf C) := by
    refine InputsMisc7.hasNormalPComplement_of_isMulCommutative ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : ((⁅a, b⁆ : C) : C ⧸ D'.subgroupOf C) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hCD a a.2 b b.2
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  refine hasNormalPComplement_of_quotient_central hq fun n hn hnp => ?_
  obtain ⟨k, hk⟩ := hnp
  rw [Subgroup.mem_subgroupOf, hmemD'] at hn
  have hnk : ((n : C) : MulAut K) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hδ : g⁻¹ * (n : MulAut K) * g ∈ inner K := by
    refine hD _ hn k ?_
    have e := conj_pow (a := g⁻¹) (b := (n : MulAut K)) (i := 3 ^ k)
    rw [inv_inv] at e
    rw [e, hnk, mul_one, inv_mul_cancel]
    exact (inner K).one_mem
  have hinner : (n : MulAut K) ∈ inner K := by
    have := (CFSG.ComponentClassification.OuterAutomorphisms.innerNormal K).conj_mem _ hδ g
    simpa [mul_assoc] using this
  exact InputsMisc5.mem_center_fixerAut_of_inner hZ P n ⟨k, hk⟩ hinner

end NoCycle

section D4

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Automorphisms
  CFSG.RankThree.PartOne.OutStructure
open scoped Pointwise

@[expose] def D4NoTrialitySylowThree : Prop :=
  ∀ (K : Type) [Field K] [Finite K]
    (S : Sylow 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
    (∃ k : ℕ, α ^ 3 ^ k = 1) →
    (∀ x ∈ (S : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))), α x = x) →
      α • projectivePointFamily (coordinateQuadPlus 4 K) = projectivePointFamily (coordinateQuadPlus 4 K)

theorem resOddD4_of_noTriality (h : D4NoTrialitySylowThree) : InputsMisc7.ResOddD4 := by
  intro X _ _ hs hnab r m hcl P hP _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h0 := hcl
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hcl K hK e
  have hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 r m hcl K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hab2 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_abelianization_two_pow_of_bound
    (plusIndexEquiv 4) (quadPlus 4 K) hab
  have hEA := (orthogonal_geometry_plus_model_stabilizer_preserving_image hcl K hK e).1
  have hsub := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  obtain ⟨κ, hκF, hκy, hκz, hyz⟩ := CFSG.RankThree.PartOne.KLC.swap_data_coordinate K
  set e' := coordinatePlusWitnessEquiv K e with he'
  have hZ' : Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus 4 K)) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e',
      InputsMisc5.center_eq_bot_of_simple hs hnab, Subgroup.map_bot]
  have hP' := InputsMisc5.fusionIsSylowIn_map_of_surjective
    (f := (e' : X →* matrixProjectiveDerived (coordinateQuadPlus 4 K))) e'.surjective hP
  let S : Sylow 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    ⟨P.map (e' : X →* matrixProjectiveDerived (coordinateQuadPlus 4 K)), hP'.2.1,
      fun {Q} hQ hle => hP'.2.2 Q le_top hQ hle⟩
  refine InputsMisc7.hasNormalPComplement_fixerAut_of_mulEquiv e' P ?_
  exact hasNormalPComplement_fixerAut_of_no_cycle hZ'
    (F := projectivePointFamily (coordinateQuadPlus 4 K)) (y := plusCX 4 K)
    (z := plusCXstar 4 K (by omega))
    (fun a => by
      have := hsub (MulAction.mem_orbit _ a)
      simpa using this)
    hκF hκy hκz hyz (D := orthD (coordinateQuadPlus 4 K))
    (fun δ hδ k hk => CFSG.HardMathSupport.Timmesfeld.Tables.T1b.orthD_D2_of_bound' _ hQ hab2
      Nat.prime_three (by norm_num) hδ hk)
    (fun a b ha hb => by
      have ha' : a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
        rw [← hEA]
        exact (mem_projectivePointFamilyAut_iff _ _).2 ha
      have hb' : b ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
        rw [← hEA]
        exact (mem_projectivePointFamilyAut_iff _ _).2 hb
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 ha'
      obtain ⟨g', rfl⟩ := MonoidHom.mem_range.1 hb'
      exact comm_mem_orthD _ g g')
    S (fun α hα hfix => h K S α hα hfix)

end D4

section Assembly


theorem input7_10_1Rest_of_narrowed (hE6 : E6InndiagSylowThree)
    (hTwE6 : TwistedE6InndiagSylowThree) (hD4 : D4NoTrialitySylowThree) :
    InputsMisc7c.Input7_10_1Rest :=
  InputsMisc7d.input7_10_1Rest_of_residues (resOddE6_of_inndiag hE6) (resOddTwE6_of_inndiag hTwE6)
    (resOddD4_of_noTriality hD4)

theorem input7_10_1Rest_of_E6_D4 (hE6 : E6InndiagSylowThree) (hD4 : D4NoTrialitySylowThree) :
    InputsMisc7c.Input7_10_1Rest :=
  input7_10_1Rest_of_narrowed hE6 (twistedE6InndiagSylowThree_of_E6 hE6) hD4

end Assembly

@[expose] def Input7_10_1Rest2 : Prop :=
  E6InndiagSylowThree ∧ D4NoTrialitySylowThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7e

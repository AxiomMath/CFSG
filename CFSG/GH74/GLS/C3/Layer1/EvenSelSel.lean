module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic
public import CFSG.GH74.GLS.C3.Layer1.St1RigTop
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.EvenSelP

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.C3.Layer1 CFSG.ComponentClassification CFSG.Blueprint
open CFSG.Open (ordA)
open scoped commutatorElement

section Violations

variable {G : Type} [Group G] [Finite G]

@[expose] def KViol (K : Subgroup G) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥K .PSL 2 p f ∧
      ¬ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 17)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥K .PSL 2 p f ∧
      ¬ ((p ^ f = 5 ∧ HasElemAbelianSylowTwo (normalizer (K : Set G)) 4) ∨
        (p ^ f = 9 ∧ pRank 2 ↥(centralizer (K : Set G)) = 1)))

theorem KViol.evenViolates {K : Subgroup G} (h : KViol K) (x : G) : EvenViolates x K := by
  rcases h with h | ⟨p, f, hp, hp2, hL, hb3⟩
  · exact Or.inl h
  · exact Or.inr (fun hB => hb3 (hB p f hp hp2 hL).2.2)

theorem violation_cases {x : G} {K : Subgroup G} (hb1 : 4 ≤ pRank 2 ↥(centralizer ({x} : Set G)))
    (h : EvenViolates x K) : KViol K ∨ IsCentralInvolution x := by
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · unfold EvenBCond at h
    push Not at h
    obtain ⟨p, f, hp, hp2, hL, hn⟩ := h
    by_cases hc : IsCentralInvolution x
    · exact Or.inr hc
    · refine Or.inl (Or.inr ⟨p, f, hp, hp2, hL, ?_⟩)
      rintro (⟨h5, hh⟩ | ⟨h9, hr⟩)
      · exact (hn hb1 hc).1 h5 hh
      · exact (hn hb1 hc).2 h9 hr

omit [Finite G] in
theorem mem_centralizer_of_le {x : G} {K : Subgroup G} (hK : K ≤ centralizer ({x} : Set G)) :
    x ∈ centralizer (K : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun _ hk =>
    mem_centralizer_singleton_iff.1 (hK hk)

namespace TermK

variable {K : Subgroup G}

omit [Finite G] in
theorem lieModel_kBar (hK : TermK K) {p f : ℕ} (hL : LieModel ↥K .PSL 2 p f) :
    LieModel (kBar K) .PSL 2 p f :=
  CFSG.GH74.lieModel_of_mulEquiv (kBarEquiv hK.pPrimeCore_eq_bot).symm hL

omit [Finite G] in
theorem lieModel_of_kBar (hK : TermK K) {p f : ℕ} (hL : LieModel (kBar K) .PSL 2 p f) :
    LieModel ↥K .PSL 2 p f :=
  CFSG.GH74.lieModel_of_mulEquiv (kBarEquiv hK.pPrimeCore_eq_bot) hL

end TermK

theorem goodK_of_lieModel {K : Subgroup G} (hK : TermK K) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel ↥K .PSL 2 p f) : GoodK K := by
  refine ⟨hK, isSimpleGroup_of_lieModel' hp hp2 hL, ?_⟩
  obtain ⟨E, hEK, hEel, hErk⟩ := Th2.exists_elemAbelian_pRank K
  refine ⟨E, hEK, hEel, ?_⟩
  rw [hErk]
  exact C3.Layer1.Thm1.two_le_pRank_of_shape
    (Or.inl (hasL2Model_of_lieModel' hp hp2 (hp.odd_of_ne_two hp2).pow (hK.lieModel_kBar hL)))

theorem exists_twoTerminal_violating (hG : C3Hyp G) {K : Subgroup G} (hK : GoodK K) {x₀ : G}
    (hx₀ : orderOf x₀ = 2) (hx₀K : x₀ ∈ centralizer (K : Set G))
    (hd : KViol K ∨ (IsCentralInvolution x₀ ∧ EvenViolates x₀ K)) :
    ∃ x : G, IsTwoTerminal x K ∧ EvenViolates x K := by
  have h3 : 3 ≤ pRank 2 G := by have := hG.pRank_eq_four; omega
  have hr4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  rcases hd with hv | ⟨hc, hv⟩
  · obtain ⟨T', hT'⟩ := exists_isSylowOf 2 (normalizer (K : Set G))
    obtain ⟨x, hxT, hxK, hx2, hxc⟩ := exists_good_x hT' ⟨x₀, hx₀, hx₀K⟩
    exact ⟨x, (hK.good_pair hG.kproper h3 hr4 hT' hx2 hxK hxT hxc).1, hv.evenViolates x⟩
  · obtain ⟨-, S, hxS, hxc⟩ := hc
    have hSC : (S : Subgroup G) ≤ centralizer ({x₀} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.2 (hxc s hs)
    have hnorm := hK.normal_of_involution hr4 hx₀ hx₀K
    have hSN : (S : Subgroup G) ≤ normalizer (K : Set G) := fun s hs =>
      C3.Layer1.U1a.mem_normalizer_of_norm hnorm (hSC hs)
    have hT' : IsSylowOf 2 (S : Subgroup G) (normalizer (K : Set G)) :=
      (isSylowOf_top' S).of_le hSN le_top
    exact ⟨x₀, (hK.good_pair hG.kproper h3 hr4 hT' hx₀ hx₀K hxS hxc).1, hv⟩

end Violations

section Existence

variable {G : Type} [Group G] [Finite G]

theorem exists_violating_pair
    (hClass : FM9Class) (h79 : B_ivk_7_9_pump) (h14 : B_prop14) (hG : C3Hyp G)
    (hE : IsEvenType G) : ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ EvenViolates x K := by
  by_contra hno
  push Not at hno
  have h3 : 3 ≤ pRank 2 G := by have := hG.pRank_eq_four; omega
  apply hG.notRE
  refine ⟨hE, ?_, ?_, ?_⟩
  ·
    intro x hx K' hK' p f hp hp2 hL
    refine ⟨?_, hG.lt2o.1⟩
    by_contra hbad
    obtain ⟨J, hJ, hJK⟩ := Th2.Bal.exists_pCompIn_over hK'
    obtain ⟨e⟩ := Th2.Bal.kBar_equiv_of_over hJ hJK
    have hLJ : LieModel (kBar J) .PSL 2 p f := CFSG.GH74.lieModel_of_mulEquiv e.symm hL
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hU2 : InU2 (kBar J) :=
      ⟨TwoThin.isQuasisimple_hat hJ, Or.inl (hasL2Model_of_lieModel' hp hp2 hodd hLJ)⟩
    have hrk : 4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := h14 G hG x J ⟨hx, hJ⟩ hU2
    have hILo : IsILo 2 x J :=
      ⟨hx, by simpa [oBound] using (show 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) by omega), hJ⟩
    obtain ⟨x₂, K₂, hlong, h2t⟩ := b_ig_6_10_proved G hG.kproper h3 x J hILo
    obtain ⟨p₂, f₂, hp₂, hf₂, hq₂, hL₂⟩ := hasL2Model_fm9 hClass hG hE hx hJ hp hp2 hLJ
    have hp₂2 : p₂ ≠ 2 := by
      rintro rfl
      have : Even (2 ^ f₂) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact (Nat.not_even_iff_odd.mpr (isFM9_odd hq₂)) this
    have hpf : p ^ f = p₂ ^ f₂ := pow_eq_of_lieModel hp hp2 hp₂ hp₂2 hLJ hL₂
    have hfm : IsFM9 (p ^ f) := hpf ▸ hq₂
    obtain ⟨e₂⟩ := h79 G hG hE x J x₂ K₂ hILo
      (hasL2Model_of_lieModel' hp hp2 ⟨hfm, hbad⟩ hLJ) hlong
    have hTerm : TermK K₂ := termK_of_twoTerminal hG.kproper h3 hE.2.1 h2t
    have hL₃ : LieModel ↥K₂ .PSL 2 p f :=
      CFSG.GH74.lieModel_of_mulEquiv
        ((kBarEquiv hTerm.pPrimeCore_eq_bot).symm.trans e₂).symm hLJ
    exact hno x₂ K₂ h2t (Or.inl ⟨p, f, hp, hp2, hL₃, hbad⟩)
  ·
    intro x K hterm p f hp hp2 hL
    have hK : TermK K := termK_of_terminalPair hE.2.1 hterm
    have hKc := isPCompIn_of_terminalPair hterm
    have hx : orderOf x = 2 := hterm.1
    have hxK : x ∈ centralizer (K : Set G) := mem_centralizer_of_le hKc.1
    have hgood : GoodK K := goodK_of_lieModel hK hp hp2 hL
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hL' : LieModel (kBar K) .PSL 2 p f := hK.lieModel_kBar hL
    have hU2 : InU2 (kBar K) :=
      ⟨TwoThin.isQuasisimple_hat hKc, Or.inl (hasL2Model_of_lieModel' hp hp2 hodd hL')⟩
    have hb1 : 4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := h14 G hG x K ⟨hx, hKc⟩ hU2
    by_contra hbad
    have hv : EvenViolates x K := Or.inr (fun hB => hbad (hB p f hp hp2 hL))
    have hd : KViol K ∨ (IsCentralInvolution x ∧ EvenViolates x K) := by
      by_cases hc : IsCentralInvolution x
      · exact Or.inr ⟨hc, hv⟩
      · exact Or.inl (Or.inr ⟨p, f, hp, hp2, hL, fun hb3 => hbad ⟨hb1, hc, hb3⟩⟩)
    obtain ⟨x₂, h2t, hv₂⟩ := exists_twoTerminal_violating hG hgood hx hxK hd
    exact hno x₂ K h2t hv₂
  ·
    intro x y K hx hy hxy hterm hL34 hu
    exact (false_of_terminal_l34 hG hE hterm hL34).elim

theorem exists_max_violating (hex : ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ EvenViolates x K) :
    ∃ (x₁ : G) (K₁ T₁ : Subgroup G), IsTwoTerminal x₁ K₁ ∧ EvenViolates x₁ K₁ ∧
      IsSylowOf 2 T₁ (centralizer ({x₁} : Set G)) ∧
      ∀ (x' : G) (K' T' : Subgroup G), IsTwoTerminal x' K' → EvenViolates x' K' →
        IsSylowOf 2 T' (centralizer ({x'} : Set G)) → Nat.card ↥T' ≤ Nat.card ↥T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set ℕ := {n | ∃ (x : G) (K T : Subgroup G), IsTwoTerminal x K ∧ EvenViolates x K ∧
    IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ Nat.card ↥T = n} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, K, h1, h2⟩ := hex
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (centralizer ({x} : Set G))
    exact ⟨_, x, K, T, h1, h2, hT, rfl⟩
  have hbdd : BddAbove S := ⟨Nat.card G, by
    rintro n ⟨x, K, T, -, -, -, rfl⟩
    exact Subgroup.card_le_card_group T⟩
  obtain ⟨x₁, K₁, T₁, h1, h2, h3, h4⟩ := Nat.sSup_mem hne hbdd
  refine ⟨x₁, K₁, T₁, h1, h2, h3, fun x' K' T' ha hb hc => ?_⟩
  rw [h4]
  exact le_csSup hbdd ⟨x', K', T', ha, hb, hc, rfl⟩

end Existence

end CFSG.GH74.GLS.EvenSelP

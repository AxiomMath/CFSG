module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelSel
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.EvenSelP

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.C3.Layer1 CFSG.ComponentClassification CFSG.Blueprint
open CFSG.Open (ordA)
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G]

theorem ne_two_of_isFM9 {p f : ℕ} (hf : 1 ≤ f) (hq : IsFM9 (p ^ f)) : p ≠ 2 := by
  rintro rfl
  have : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact (Nat.not_even_iff_odd.mpr (isFM9_odd hq)) this

theorem two_le_pRank_cent_of_kviol {K : Subgroup G} {x : G} (hx2 : orderOf x = 2)
    (hxK : x ∈ centralizer (K : Set G)) (hv : KViol K) {p₂ f₂ : ℕ} (hp₂ : p₂.Prime)
    (hp₂2 : p₂ ≠ 2) (hL₂ : LieModel ↥K .PSL 2 p₂ f₂) (h9 : p₂ ^ f₂ = 9) :
    2 ≤ pRank 2 ↥(centralizer (K : Set G)) := by
  have h1 : 1 ≤ pRank 2 ↥(centralizer (K : Set G)) := by
    have := Back.pRank_mono' (zpowers_le.2 hxK)
    rw [Th2.pRank_zpowers_of_orderOf_two hx2] at this
    exact this
  rcases hv with ⟨p, f, hp, hp2, hL, hbad⟩ | ⟨p, f, hp, hp2, hL, hbad⟩
  · exfalso
    have := pow_eq_of_lieModel hp hp2 hp₂ hp₂2 hL hL₂
    exact hbad (Or.inr (Or.inr (Or.inl (this.trans h9))))
  · have h9' : p ^ f = 9 := (pow_eq_of_lieModel hp hp2 hp₂ hp₂2 hL hL₂).trans h9
    by_contra hlt
    have : pRank 2 ↥(centralizer (K : Set G)) = 1 := by omega
    exact hbad (Or.inr ⟨h9', this⟩)

theorem rankQ_of_good
    (hG : C3Hyp G) {K : Subgroup G} {x : G}
    (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hnorm : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4)
    {p₂ f₂ : ℕ} (hp₂ : p₂.Prime) (hf₂ : 1 ≤ f₂) (hq₂ : IsFM9 (p₂ ^ f₂))
    (hL₂ : LieModel (kBar K) .PSL 2 p₂ f₂)
    (hcase : IsCentralInvolution x ∨ (p₂ ^ f₂ = 9 → 2 ≤ pRank 2 ↥(CxK x K))) :
    2 ≤ pRank 2 ↥(CxK x K) := by
  have hp₂2 : p₂ ≠ 2 := ne_two_of_isFM9 hf₂ hq₂
  by_cases h9 : p₂ ^ f₂ = 9
  · by_contra hlt
    push Not at hlt
    rcases two_le_pRank_CxK_or_fAut hG4 hnorm ⟨p₂, f₂, hp₂, hf₂, hq₂, hL₂⟩ with h | ⟨f, hfC, hf2, hind⟩
    · omega
    · rcases hcase with hc | hr
      · have hQ2 : ∀ A : Subgroup G, A ≤ CMK (centralizer ({x} : Set G)) K →
            IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2 := by
          intro A hA hAel
          have h1 := Back.card_eq_two_pow_pRank hAel
          have h2 : pRank 2 ↥A ≤ pRank 2 ↥(CxK x K) := Back.pRank_mono' hA
          have h3 : pRank 2 ↥A ≤ 1 := by omega
          calc Nat.card ↥A = 2 ^ pRank 2 ↥A := h1
            _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h3
        have hyp : Bk.Prop34HypN G x K :=
          { simple := hG.kproper.1
            nonab := hG.kproper.2.1
            central := hc
            comp := hKc
            normal := hnorm
            shape := Or.inl (hasL2Model_of_lieModel' hp₂ hp₂2 (hp₂.odd_of_ne_two hp₂2).pow hL₂)
            sylowQ := C3.Layer1.Thm1.exists_Q_of_card_le_two hQ2 }
        exact Bk.prop34N_false hyp hfC hf2 hind
      · exact absurd (hr h9) (by omega)
  · exact two_le_pRank_CxK_of_prime hG4 hnorm ⟨p₂, f₂, hp₂, hf₂, ⟨hq₂, h9⟩, hL₂⟩

theorem evenSelPre_of_max
    (hClass : FM9Class) (h14 : B_prop14) (hG : C3Hyp G) (hE : IsEvenType G)
    {x : G} {K T : Subgroup G} (h2t : IsTwoTerminal x K) (hviol : EvenViolates x K)
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hmax : ∀ (x' : G) (K' T' : Subgroup G), IsTwoTerminal x' K' → EvenViolates x' K' →
      IsSylowOf 2 T' (centralizer ({x'} : Set G)) → Nat.card ↥T' ≤ Nat.card ↥T) :
    EvenSelPre x K T (T ⊓ CxK x K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ≤ pRank 2 G := by have := hG.pRank_eq_four; omega
  have hr4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  obtain ⟨p, f, hp, hp2, hL⟩ := lieModel_of_violates hviol
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hx2 : orderOf x = 2 := h2t.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := h2t.1.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hKc.1
  have hxK : x ∈ centralizer (K : Set G) := mem_centralizer_of_le hKC
  have hK : TermK K := termK_of_twoTerminal hG.kproper h3 hE.2.1 h2t
  have hgood : GoodK K := goodK_of_lieModel hK hp hp2 hL
  have hL' : LieModel (kBar K) .PSL 2 p f := hK.lieModel_kBar hL
  have hfm : HasL2Model (kBar K) IsFM9 := hasL2Model_fm9 hClass hG hE hx2 hKc hp hp2 hL'
  have hnorm := hgood.normal_of_involution hr4 hx2 hxK
  have hU2 : InU2 (kBar K) :=
    ⟨TwoThin.isQuasisimple_hat hKc, Or.inl (hasL2Model_of_lieModel' hp hp2 hodd hL')⟩
  have hb1 : 4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := h14 G hG x K ⟨hx2, hKc⟩ hU2
  have hG4 : pRank 2 ↥(centralizer ({x} : Set G)) = 4 :=
    le_antisymm ((pRank_le_top' _).trans hr4) hb1
  have hxT : x ∈ T := mem_of_isSylowOf_centralizer hx2 hT
  have hTC : T ≤ centralizer ({x} : Set G) := hT.le
  have hTcomm : ∀ t ∈ T, t * x = x * t := fun t ht => mem_centralizer_singleton_iff.1 (hTC ht)
  have hTN : T ≤ normalizer (K : Set G) := fun t ht =>
    C3.Layer1.U1a.mem_normalizer_of_norm hnorm (hTC ht)
  have hTM : IsSylowOf 2 T (normalizer (K : Set G)) := by
    by_cases hc : IsCentralInvolution x
    · obtain ⟨-, S, hxS, hxc⟩ := hc
      have hS := isSylowOf_top' S
      have hSC : (S : Subgroup G) ≤ centralizer ({x} : Set G) := fun s hs =>
        mem_centralizer_singleton_iff.2 (hxc s hs)
      have hSC' : IsSylowOf 2 (S : Subgroup G) (centralizer ({x} : Set G)) := hS.of_le hSC le_top
      have hcard : Nat.card ↥T = Nat.card ↥(S : Subgroup G) := hT.card_eq.trans hSC'.card_eq.symm
      have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_of_card le_top (by rw [hcard, hS.card_eq])
      exact hTtop.of_le hTN le_top
    · have hKv : KViol K := (violation_cases hb1 hviol).resolve_right hc
      obtain ⟨T', hT', hTT'⟩ := exists_isSylowOf_ge' hT.isPGroup hTN
      obtain ⟨x', hx'T', hx'K, hx'2, hx'c⟩ := exists_good_x hT' ⟨x, hx2, hxK⟩
      obtain ⟨h2t', hT'C, -, -, -⟩ :=
        hgood.good_pair hG.kproper h3 hr4 hT' hx'2 hx'K hx'T' hx'c
      have hle := hmax x' K T' h2t' (hKv.evenViolates x') hT'C
      have heq : T = T' := Subgroup.eq_of_le_of_card_ge hTT' hle
      rw [heq]
      exact hT'
  obtain ⟨-, -, hQsyl, hCx, hcent5⟩ := hgood.good_pair hG.kproper h3 hr4 hTM hx2 hxK hxT hTcomm
  have hCN : centralizer ({x} : Set G) ≤
      normalizer ((CMK (centralizer ({x} : Set G)) K : Subgroup G) : Set G) := by
    intro g hg
    refine P34.mem_normalizer_of_conj_le (fun a ha => ?_)
    have := P34Real.CMK_conj hnorm (Subgroup.inv_mem _ hg) ha
    simpa using this
  have hQCx : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) :=
    hT.inf_of_le_normalizer inf_le_left hCN
  have hrk1 : pRank 2 ↥(T ⊓ CxK x K) = pRank 2 ↥(CxK x K) := Th2.pRank_eq_of_isSylowOf hQCx
  have hQC : IsSylowOf 2 (T ⊓ CxK x K) (centralizer (K : Set G)) := by
    rw [hCx]
    exact hQsyl
  have hrk2 : pRank 2 ↥(T ⊓ CxK x K) = pRank 2 ↥(centralizer (K : Set G)) :=
    Th2.pRank_eq_of_isSylowOf hQC
  obtain ⟨p₂, f₂, hp₂, hf₂, hq₂, hL₂⟩ := hfm
  have hp₂2 : p₂ ≠ 2 := ne_two_of_isFM9 hf₂ hq₂
  have hcase : IsCentralInvolution x ∨ (p₂ ^ f₂ = 9 → 2 ≤ pRank 2 ↥(CxK x K)) := by
    by_cases hc : IsCentralInvolution x
    · exact Or.inl hc
    · right
      intro h9
      have hKv : KViol K := (violation_cases hb1 hviol).resolve_right hc
      have := two_le_pRank_cent_of_kviol hx2 hxK hKv hp₂ hp₂2 (hK.lieModel_of_kBar hL₂) h9
      rw [← hrk1, hrk2]
      exact this
  have hrank : 2 ≤ pRank 2 ↥(CxK x K) :=
    rankQ_of_good hG hKc hnorm hG4 hp₂ hf₂ hq₂ hL₂ hcase
  exact
    { twoTerminal := h2t
      terminal := ⟨hx2, hK.comp x hx2 hxK, hK.even, fun y hy2 hyK => hK.comp y hy2 hyK⟩
      isL2 := TwoThin.hasL2Model_of_mulEquiv (kBarEquiv hK.pPrimeCore_eq_bot)
        ⟨p₂, f₂, hp₂, hf₂, hq₂, hL₂⟩
      sylowT := hT
      hQ := rfl
      sylowQ := hQC
      rankQ := by rw [hrk1]; exact hrank
      sylowTM := hTM
      cent5 := hcent5
      violation := hviol }

theorem exists_evenSelPre
    (hClass : FM9Class) (h79 : B_ivk_7_9_pump) (h14 : B_prop14) (hG : C3Hyp G)
    (hE : IsEvenType G) :
    ∃ (x : G) (K T Q : Subgroup G), EvenSelPre x K T Q ∧
      ∀ (x' : G) (K' T' : Subgroup G), IsTwoTerminal x' K' → EvenViolates x' K' →
        IsSylowOf 2 T' (centralizer ({x'} : Set G)) → Nat.card ↥T' ≤ Nat.card ↥T := by
  obtain ⟨x₁, K₁, T₁, h2t, hv, hT, hmax⟩ :=
    exists_max_violating (exists_violating_pair hClass h79 h14 hG hE)
  exact ⟨x₁, K₁, T₁, _, evenSelPre_of_max hClass h14 hG hE h2t hv hT hmax, hmax⟩

end Final

end CFSG.GH74.GLS.EvenSelP

module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltTr
public import CFSG.GH74.KGroups.TwoM12Fixed
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.CompNormal
public import CFSG.GH74.GLS.TwoThin.G.C2Vertical

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace S3SL2Pump

theorem hasL2Model_gt_three {K : Type} [Group K] (h : HasL2Model K Odd) :
    HasL2Model K (fun q => Odd q ∧ 3 < q) := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  refine ⟨p, f, hp, hf, ⟨hq, ?_⟩, hL⟩
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
    have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
    have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hq
    omega
  all_goals exact absurd h0 (by norm_num)

end S3SL2Pump

@[expose] def C2CoverInput : Prop :=
  ∀ (L : Type) [Group L] [Finite L], InC2 L → Gen4 L → center L = ⊥ ∨ E2.Shape2M12 L ∨ E2.Shape2Sz8 L

theorem kg_sl2_pumpup_of_cases
    (hC2 : C2CoverInput)
    {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y) (_hO : pPrimeCore 2 Y = ⊥)
    {H Lb : Subgroup Y} (hH : IsComponent H) (_hHZ : IsPGroup 2 ↥(center ↥H)) (hHZ1 : center ↥H ≠ ⊥)
    (_hGH : GHList (↥H ⧸ center ↥H)) (hcases : InC2 ↥H ∨ InT2 ↥H) {s : Y} (hs : orderOf s = 2)
    (hsN : s ∈ normalizer (H : Set Y))
    (hLb : IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb)
    (hLlay : pLayerOf 2 (centralizer ({s} : Set Y) ⊓ H) = Lb)
    (hLsl2 : HasSL2Model ↥Lb (fun q => Odd q ∧ 5 ≤ q)) (hne : Lb ≠ H) :
    HasSL2Model ↥H Odd ∨ IsDoubleCoverOfAlt ↥H 7 ∨ IsDoubleCoverOfAlt ↥H 8 ∨ IsL34Quotient ↥H := by
  classical
  have hgenH : Gen4 ↥H := Gen4.subgroup H hY
  have hss : s * s = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  obtain ⟨q, hqodd, hq5, hLbcard⟩ := S3SL2Basic.sl2_card_data hLsl2
  have hLbH : Lb ≤ H := hLb.1.trans inf_le_right
  have hperf : ⁅Lb, Lb⁆ = Lb := GLS.C3.Layer1.Bk.perfect_of_isPCompIn hLb
  have hncLb : ∃ a ∈ Lb, ∃ b ∈ Lb, a * b ≠ b * a :=
    S3SL2Basic.exists_noncomm_of_perfect hperf (by rw [hLbcard]; have := S3SL2Basic.sl2_card_ge hq5; omega)
  set σ : MulAut ↥H := S3SL2Basic.actH H hsN with hσdef
  have hσ2 : σ * σ = 1 := S3SL2Basic.actH_mul_self H hsN hss
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hcen : ∀ h ∈ H, s * h = h * s := fun h hh =>
      (S3SL2Basic.actH_eq_iff H hsN ⟨h, hh⟩).1 (by rw [hσdef] at h1; simp [h1])
    exact hne (S3SL2Basic.eq_of_centralizes hH.1 hcen hLb hncLb)
  have hLbfix : ∀ x ∈ Lb.subgroupOf H, σ x = x := fun x hx =>
    (S3SL2Basic.actH_eq_iff H hsN x).2 (by
      have : (x : Y) ∈ centralizer ({s} : Set Y) := (hLb.1 hx).1
      exact (mem_centralizer_iff.1 this s rfl))
  have hcardP : Nat.card (Lb.subgroupOf H) = Nat.card Lb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLbH).toEquiv
  rcases hcases with hC | hT
  ·
    exfalso
    rcases hC2 ↥H hC hgenH with hz | h2M | h2S
    · exact hHZ1 hz
    · have h60 := KGroups.TwoM12.card_le_sixty_of_fixed h2M σ hσ2 hσ1
        (S3SL2Basic.perfect_subgroupOf hLb) hLbfix
      have h120 := S3SL2Basic.sl2_card_ge hq5
      omega
    · obtain ⟨-, hc2, hSz⟩ := h2S
      have hcard : Nat.card ↥H = 58240 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥H), hc2,
          card_of_lieModel_twistedB2 hSz, TwoThin.ordSuzuki_eight]
      have h3 : 3 ∣ Nat.card Lb := hLbcard ▸ TwoThin.three_dvd_mul_sq_sub_one q
      have hdvd : Nat.card Lb ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hLbH
      have h4 : 3 ∣ 58240 := hcard ▸ h3.trans hdvd
      omega
  ·
    obtain ⟨-, hT⟩ := hT
    rcases hT with hL2 | hS | hA7 | ⟨n, h7, h11, hn⟩ | ⟨hl, hexp⟩
    · exfalso
      obtain ⟨p, f, hp, hf, ⟨hqodd, -⟩, hL⟩ := hL2
      exact hHZ1 (Stage1.Thm6.Glue.center_eq_bot_of_isL2Model
        (Stage1.Thm6.Glue.isL2Model_of_hasL2Model
          (S3SL2Pump.hasL2Model_gt_three ⟨p, f, hp, hf, hqodd, hL⟩)))
    · exact Or.inl hS
    · exact absurd (Stage1.Thm6.Glue.center_eq_bot_of_isA7Model hA7) hHZ1
    · by_cases h7' : n = 7
      · subst h7'
        exact Or.inr (Or.inl hn)
      by_cases h8' : n = 8
      · subst h8'
        exact Or.inr (Or.inr (Or.inl hn))
      exact (false_of_bigAlt transpExcl hY hH (by omega) h11 hn hs hsN hLb hLlay hLsl2 hne).elim
    · exact Or.inr (Or.inr (Or.inr hl))

theorem kg_sl2_pumpup_of_input
    (hC2 : C2CoverInput)
    {Y : Type} [Group Y] [Finite Y] (hY : Gen4 Y) (_hO : pPrimeCore 2 Y = ⊥)
    {H Lb : Subgroup Y} (hH : IsComponent H) (_hHZ : IsPGroup 2 ↥(center ↥H)) (hHZ1 : center ↥H ≠ ⊥)
    (_hGH : GHList (↥H ⧸ center ↥H)) (hCal : InCalK2 ↥H) (hHG2 : ¬ InG2 ↥H) {s : Y} (hs : orderOf s = 2)
    (hsN : s ∈ normalizer (H : Set Y))
    (hLb : IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb)
    (hLlay : pLayerOf 2 (centralizer ({s} : Set Y) ⊓ H) = Lb)
    (hLsl2 : HasSL2Model ↥Lb (fun q => Odd q ∧ 5 ≤ q)) (hne : Lb ≠ H) :
    HasSL2Model ↥H Odd ∨ IsDoubleCoverOfAlt ↥H 7 ∨ IsDoubleCoverOfAlt ↥H 8 ∨ IsL34Quotient ↥H := by
  have hcases : InC2 ↥H ∨ InT2 ↥H := by
    by_contra hcon
    push Not at hcon
    exact hHG2 ⟨hCal, hcon.1, hcon.2⟩
  exact kg_sl2_pumpup_of_cases hC2 hY _hO hH _hHZ hHZ1 _hGH hcases hs hsN hLb hLlay hLsl2 hne

theorem c2CoverInput_of_facts
    (hG : GenericKnownFacts) (hF : E2.E2ComponentFacts) : C2CoverInput :=
  fun _ _ _ hC hgen => TwoThin.c2ShapeG_of_inC2 hG hF hC hgen

end CFSG.GH74.Generic.BProg.B3

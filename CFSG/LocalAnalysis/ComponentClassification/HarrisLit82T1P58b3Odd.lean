module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCl

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace P58b3

theorem setting_facts {G : Type} [Group G] [Finite G] {z₁ z₂ : G} (hz₁ : orderOf z₁ = 2)
    (hz₂ : orderOf z₂ = 2) {L₁ K : Subgroup G} (hz₁L : z₁ ∈ L₁)
    (hKc : IsTwoComponentIn K (centralizer {z₁})) (hO₁ : GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K)
    (hz₂K : z₂ ∈ K)
    (hz₂Z : (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K))
    {τ : StatedLieTag} {n f : ℕ} (hm : LieModel (↥K ⧸ Open.fusionZStar ↥K) τ n 3 f) :
    IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ ∧
      LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) τ n 3 f ∧
      ∃ c t : ↥K ⧸ pPrimeCore 2 ↥K, orderOf c = 2 ∧ c ∈ center (↥K ⧸ pPrimeCore 2 ↥K) ∧
        orderOf t = 2 ∧ t ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  have hz₁Z := mem_center_of_le_centralizer hKc.1 hz₁K
  obtain ⟨e⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K
  refine ⟨hKc.2.2.2, CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot _ 2,
    GSThmB.OddQuot.lieModel_of_equiv e hm,
    QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩, QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩,
    P58b.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hz₁), ?_,
    P58b.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hz₂), hz₂Z⟩
  rw [mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) g
  rw [← map_mul, ← map_mul, mem_center_iff.mp hz₁Z g]

theorem odd_exceptionalOrders_three (t : StatedLieTag) (n f : ℕ) :
    Odd ((Multiplier.exceptionalOrders t n 3 f).1 *
      (Multiplier.exceptionalOrders t n 3 f).2) := by
  unfold Multiplier.exceptionalOrders
  split <;> first | decide | simp_all

theorem models_lieModel_of_lieModel (hTB : CFSG.TauCetiBridge.TypewiseBridges) {S : Type}
    [Group S] {τ : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel S τ n p f) : CFSG.Models.LieModel S τ n p f := by
  rcases hm with ⟨-, hc⟩ | ⟨hn, ht, hce⟩ | ⟨hn, ht, hr⟩ | ⟨-, -, hsz⟩
  · exact ⟨hc.1, .inl hc⟩
  · subst hn
    exact ⟨hce.1, .inr ⟨rfl, CFSG.TauCetiBridge.exists_index_of_exceptional hTB hp hp2
      (.inl ⟨ht, hce⟩)⟩⟩
  · subst hn
    exact ⟨hr.1, .inr ⟨rfl, CFSG.TauCetiBridge.exists_index_of_exceptional hTB hp hp2
      (.inr ⟨ht, hr⟩)⟩⟩
  · exact absurd hsz.1 hp2

theorem false_of_odd_generic (hGA : TBLit.GriessMultipliersAllModels)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) {c : X} (hc2 : orderOf c = 2) (hcZ : c ∈ center X)
    {τ : StatedLieTag} {n f : ℕ} (hm : LieModel (X ⧸ center X) τ n 3 f)
    (hodd : Odd ((Multiplier.genericOrders τ n 3 f).1 * (Multiplier.genericOrders τ n 3 f).2)) :
    False := by
  have hcard := card_griessHopfMultiplier_eq hGA
    (models_lieModel_of_lieModel hTB Nat.prime_three (by norm_num) hm)
  have hodd' : Odd (Nat.card (Open.griessHopfMultiplier (X ⧸ center X))) := by
    rw [hcard]
    exact hodd.mul (odd_exceptionalOrders_three τ n f)
  exact P58b.not_odd_card_center hc2 hcZ (P58b.odd_card_center_of_odd_multiplier hX hodd')

theorem false_of_PSL_two {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hO : pPrimeCore 2 X = ⊥) {f : ℕ} (hm : LieModel (X ⧸ center X) .PSL 2 3 f) {c t : X}
    (hc2 : orderOf c = 2) (hcZ : c ∈ center X) (ht2 : orderOf t = 2) (htZ : t ∉ center X) :
    False := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨-, hf, -, -, h23⟩ := P58b.admissible_of_lieModel hm
  obtain ⟨F, _, _, hFc, ⟨θ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hm
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hF : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hq2 : Nat.card F ≠ 2 := by
    intro h
    rw [hFc] at h
    have h3 : 3 ∣ 2 := h ▸ dvd_pow_self 3 (by omega)
    omega
  have hq3 : Nat.card F ≠ 3 := by
    intro h
    rw [hFc] at h
    exact h23 (by rw [h])
  have hG := CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl (Or.inr hq2)
    (Or.inr hq3)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(2, F)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(2, F) →* E, ∀ x, π (s x) = x := fun E _ _ π hπ hker h2 => by
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.sl_central_two_extension_splitting 1 hF hπ hker h2
    exact ⟨s, hs⟩
  set β : SL(2, F) →* X ⧸ center X := θ.symm.toMonoidHom.comp (LinearFlag.proj 2 F)
  have hβ : Function.Surjective β := θ.symm.surjective.comp (LinearFlag.proj_surjective 2 F)
  have hη : (QuotientGroup.mk' (center X)).ker = center X := QuotientGroup.ker_mk' _
  obtain ⟨α, hαβ, hαs, hker⟩ := CFSG.LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ
    (QuotientGroup.mk'_surjective (center X)) hη.le
    (by rw [hη]; exact Sol78.center_isPGroup_two hO)
  have hnt : ∃ g, β g ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hX.2.2
    by_contra hall
    have hall' : ∀ g, β g = 1 := fun g => by
      by_contra h
      exact hall ⟨g, h⟩
    apply hab
    obtain ⟨a, rfl⟩ := hβ a
    obtain ⟨b, rfl⟩ := hβ b
    rw [hall' a, hall' b]
  have hβZ := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hG hnt
  have hpm : ∀ z ∈ β.ker, z = 1 ∨ z = -1 := fun z hz =>
    Burgoyne.C.eq_one_or_eq_neg_one hF2 z (by
      rw [← pow_two]; exact Burgoyne.C.sq_eq_one_of_mem_center_SL (hβZ hz))
  have hc : c ∈ β.ker.map α := by rw [← hker, hη]; exact hcZ
  obtain ⟨z, hz, hzc⟩ := hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hneg : α (-1) = c := by
    rcases hpm z hz with rfl | rfl
    · rw [map_one] at hzc
      exact absurd hzc.symm hc1
    · exact hzc
  obtain ⟨g, rfl⟩ := hαs t
  have hg2 : g * g = 1 := by
    have hα2 := pow_orderOf_eq_one (α g)
    rw [ht2] at hα2
    have h1 : α (g * g) = 1 := by
      rw [map_mul, ← pow_two, hα2]
    have h2 : g * g ∈ β.ker := by
      rw [MonoidHom.mem_ker, ← hαβ, h1, map_one]
    rcases hpm _ h2 with h3 | h3
    · exact h3
    · exfalso
      rw [h3, hneg] at h1
      exact hc1 h1
  rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 g hg2 with rfl | rfl
  · rw [map_one] at htZ
    exact htZ (one_mem _)
  · rw [hneg] at htZ
    exact htZ hcZ

end P58b3

open P58b3

theorem harris82Lemma58bThreeRow_of_odd_generic (hGA : TBLit.GriessMultipliersAllModels)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {τ : StatedLieTag} {n : ℕ}
    (hodd : ∀ f : ℕ, Odd ((Multiplier.genericOrders τ n 3 f).1 *
      (Multiplier.genericOrders τ n 3 f).2)) : Harris82Lemma58bThreeRow τ n := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ _ K _ _ hz₁L _ _ hKc hO₁ _ _ hz₂K hz₂Z f hm
  obtain ⟨hX, -, hmX, c, -, hc2, hcZ, -⟩ := setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  exact (false_of_odd_generic hGA hTB hX hc2 hcZ hmX (hodd f)).elim

theorem harris82Lemma58bThreeRow_exc (hGA : TBLit.GriessMultipliersAllModels)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {τ : StatedLieTag}
    (hτ : τ ∈ ({.G2, .F4, .E6, .E8, .twistedE6, .trialityD4, .twistedG2} : Finset StatedLieTag))
    (n : ℕ) : Harris82Lemma58bThreeRow τ n := by
  refine harris82Lemma58bThreeRow_of_odd_generic hGA hTB fun f => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  have h3 : Odd 3 := by decide
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact odd_one
  · exact odd_one
  · simp only [Multiplier.genericOrders, mul_one]
    exact h3.of_dvd_nat (Nat.gcd_dvd_left 3 _)
  · exact odd_one
  · simp only [Multiplier.genericOrders, mul_one]
    exact h3.of_dvd_nat (Nat.gcd_dvd_left 3 _)
  · exact odd_one
  · exact odd_one

theorem harris82Lemma58bThreeRow_PSL_odd (hGA : TBLit.GriessMultipliersAllModels)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {n : ℕ} (hn : Odd n) :
    Harris82Lemma58bThreeRow .PSL n :=
  harris82Lemma58bThreeRow_of_odd_generic hGA hTB fun _ => by
    simp only [Multiplier.genericOrders, mul_one]
    exact hn.of_dvd_nat (Nat.gcd_dvd_left n _)

theorem harris82Lemma58bThreeRow_PSU_odd (hGA : TBLit.GriessMultipliersAllModels)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {n : ℕ} (hn : Odd n) :
    Harris82Lemma58bThreeRow .PSU n :=
  harris82Lemma58bThreeRow_of_odd_generic hGA hTB fun _ => by
    simp only [Multiplier.genericOrders, mul_one]
    exact hn.of_dvd_nat (Nat.gcd_dvd_left n _)

theorem harris82Lemma58bThreeRow_PSL_two : Harris82Lemma58bThreeRow .PSL 2 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ _ K _ _ hz₁L _ _ hKc hO₁ _ _ hz₂K hz₂Z f hm
  obtain ⟨hX, hO, hmX, c, t, hc2, hcZ, ht2, htZ⟩ :=
    setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  exact (false_of_PSL_two hX hO hmX hc2 hcZ ht2 htZ).elim

theorem harris82Lemma58bThreeRow_char_two {τ : StatedLieTag}
    (hτ : τ = .twistedB2 ∨ τ = .twistedF4 ∨ τ = .Tits) (n : ℕ) :
    Harris82Lemma58bThreeRow τ n := by
  intro G _ _ z₁ z₂ _ _ _ _ L₁ _ K _ _ _ _ _ _ _ _ _ _ _ f hm
  exfalso
  obtain ⟨-, -, h⟩ := P58b.admissible_of_lieModel hm
  rcases hτ with rfl | rfl | rfl
  · exact absurd h.2.1 (by norm_num)
  · exact absurd h.2.1 (by norm_num)
  · exact absurd h.2.1 (by norm_num)

end CFSG.ComponentClassification.HarrisLit.T1

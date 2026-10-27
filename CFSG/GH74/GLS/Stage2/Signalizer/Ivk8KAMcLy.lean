module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.SmallOddCore.HSMcL

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
open scoped commutatorElement

theorem kaAll_of_McL
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .McL) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 898128000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL
  have hna : ∃ a b : Y, a * b ≠ b * a :=
    exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num)
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact
      CFSG.Sporadic.SmallOddCore.ctuc_hs_mcl_almost_simple_involution_centralizer_odd_core_trivial
        S (Or.inr ⟨ψ.trans e⟩) hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.McL_outer_card_le_two
  have hfinC : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs hna hY hOutCyc hOut hα2 hα1

theorem kaNoP_of_quasisimple_cent {Y : Type} [Group Y] [Finite Y] {t : Y}
    (hq : IsQuasisimple ↥(centralizer ({t} : Set Y)))
    (hZ : Nat.card ↥(Subgroup.center ↥(centralizer ({t} : Set Y))) = 2) :
    KANoP (MulAut.conj t) := by
  intro p hp hp2 N hN hNn hNp
  rw [kn_fixSub_conj] at hN hNn
  have hcentral := ka_central_of_quasisimple_image (centralizer ({t} : Set Y)).subtype hq hp N
    (by rwa [Subgroup.range_subtype]) hNp (by
      intro l hl
      rw [Subgroup.range_subtype] at hl
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨fun hn => hNn l hl n hn, fun hn => ?_⟩
      have h1 := hNn l⁻¹ (Subgroup.inv_mem _ hl) _ hn
      simpa [mul_assoc] using h1)
  rw [eq_bot_iff]
  intro m hm
  have hmC : m ∈ centralizer ({t} : Set Y) := hN hm
  have hmc : (⟨m, hmC⟩ : ↥(centralizer ({t} : Set Y))) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := hcentral m hm g (by rw [Subgroup.range_subtype]; exact g.2)
    exact h1.symm
  have hd : orderOf (⟨⟨m, hmC⟩, hmc⟩ : ↥(Subgroup.center ↥(centralizer ({t} : Set Y)))) ∣ 2 :=
    hZ ▸ orderOf_dvd_natCard _
  have hmsq := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 hd)
  have hm2 : m ^ 2 = 1 := by
    have h2 := congrArg Subtype.val hmsq
    simpa using h2
  obtain ⟨k, hk⟩ := hNp ⟨m, hm⟩
  have hmk : m ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  have h2 : orderOf m ∣ p ^ k := orderOf_dvd_of_pow_eq_one hmk
  have h3 : orderOf m = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h3)

theorem kaAll_of_Ly
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .Ly) {α : MulAut Y} (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 51765179004000000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  have hna : ∃ a b : Y, a * b ≠ b * a :=
    exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num)
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot
      (CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.center_eq_bot_of_simple hs hna)
  have hinnerT : ∀ φ : MulAut NativeSporadic.Ly, ∃ g : NativeSporadic.Ly, φ = MulAut.conj g :=
    fun φ => by
      obtain ⟨g, hg⟩ := (Subgroup.eq_top_iff' _).mp
        CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput φ
      exact ⟨g, hg.symm⟩
  have hinner : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g := fun φ =>
    exists_conj_of_equiv e hinnerT φ
  refine kaAll_of_allInner hinj hinner (fun t ht2 ht1 => ?_) hα2 hα1
  have hto : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨hq, hZ, -⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t hto
  exact kaNoP_of_quasisimple_cent hq hZ

theorem kay_McLy :
    KAY FMcLy := by
  refine kay_of_kaAll ?_
  intro Y _ _ hF hs α hα2 hα1
  rcases hF with hMcL | hLy
  · exact kaAll_of_McL hs hMcL hα2 hα1
  · exact kaAll_of_Ly hs hLy hα2 hα1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

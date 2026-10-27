module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryParabThreeRankSix
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryParabThreeRankTorus
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviTransfer
import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIV
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThreeCoreUniqueness.Helpers

section Lift

variable {Y X : Type*} [Group Y] [Group X] [Finite Y] {ρ : Y →* X}

omit [Finite Y] in
theorem eq_one_of_mem_of_isPGroup_three_of_coprime (hker : Nat.Coprime 3 (Nat.card ρ.ker))
    {U : Subgroup Y} (hU : IsPGroup 3 U) {x : Y} (hx : x ∈ U) (h1 : ρ x = 1) : x = 1 := by
  obtain ⟨e, he⟩ := hU ⟨x, hx⟩
  exact eq_one_of_mem_of_coprime_three hker h1 (by simpa using congrArg Subtype.val he)

omit [Finite Y] in
theorem card_map_eq_of_isPGroup_three_of_coprime (hker : Nat.Coprime 3 (Nat.card ρ.ker))
    {U : Subgroup Y} (hU : IsPGroup 3 U) : Nat.card (U.map ρ) = Nat.card U := by
  have hinj : Function.Injective (ρ.comp U.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2
      (Subtype.ext (eq_one_of_mem_of_isPGroup_three_of_coprime hker hU x.2 hx))
  have e := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at e
  exact e.symm

theorem exists_elemAbelian_le_of_map_of_coprime (hρ : Function.Surjective ρ)
    (hker : Nat.Coprime 3 (Nat.card ρ.ker)) {J : Subgroup Y} (hkJ : ρ.ker ≤ J)
    {E : Subgroup X} (hEJ : E ≤ J.map ρ) (hE : IsElemAbelian 3 E) :
    ∃ E' : Subgroup Y, E' ≤ J ∧ IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E := by
  obtain ⟨U, hUE, hU, hUm⟩ :=
    exists_isPGroup_three_map_eq hρ (isPGroup_three_of_isElemAbelian_three hE)
  have hUJ : U ≤ J := hUE.trans ((Subgroup.comap_mono hEJ).trans
    (by rw [Subgroup.comap_map_eq, sup_eq_left.2 hkJ]))
  have hinj : ∀ x ∈ U, ρ x = 1 → x = 1 := fun x hx h1 =>
    eq_one_of_mem_of_isPGroup_three_of_coprime hker hU hx h1
  have hU1 : IsElemAbelian 3 (U.map ρ) := hUm ▸ hE
  refine ⟨U, hUJ, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hc := hU1.1.is_comm.comm ⟨ρ a, a, a.2, rfl⟩ ⟨ρ b, b, b.2, rfl⟩
    have hc' : ρ ((a : Y) * (b : Y) * ((b : Y) * (a : Y))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · exact hinj _ (pow_mem hx 3) (by rw [map_pow]; exact hU1.2 _ ⟨x, hx, rfl⟩)
  · rw [← hUm, card_map_eq_of_isPGroup_three_of_coprime hker hU]

end Lift

theorem kFactUnitaryParabolicThreeRank : KFactUnitaryParabolicThreeRank := by
  intro Y _ _ hY hZ d hd he T J hT hNJ hJ hperf hO3 hrank E hEJ hE hE27
  obtain ⟨e⟩ := he
  obtain ⟨r, q, hq, h3r, hdr⟩ := hd
  obtain ⟨d, hv⟩ := d
  simp only at hdr
  subst hdr
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two hq
  rw [hp, hf] at hc
  set ρ : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y) with hρdef
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hkerρ : ρ.ker = Subgroup.center Y := QuotientGroup.ker_mk' _
  have hcop : Nat.Coprime 3 (Nat.card ρ.ker) := by rw [hkerρ]; exact hZ
  have hkJ : ρ.ker ≤ J := by
    rw [hkerρ]
    exact (Subgroup.center_le_normalizer _).trans hNJ
  obtain ⟨S, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  obtain ⟨hT₁, hN₁, hJ₁, hperf₁⟩ := map_overgroup_of_central hρ hkerρ.le S hNJ hJ hperf
  obtain ⟨S₁, hS₁⟩ := exists_sylow_of_isSylowTwoOf_top hT₁
  rw [← hS₁] at hN₁ hJ₁
  have hX : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_centerQuotient_eq_bot hY
  obtain ⟨⟨-, -, hn, hne⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hc
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have hB := borelQuotient_su hcard (by omega) ζ hζ e'
  obtain ⟨α, hαs, hαk⟩ : ∃ α : SU (unitaryInvolution F 2 1) (r + 1) →* Y ⧸ Subgroup.center Y,
      Function.Surjective α ∧ α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) (r + 1)) :=
    ⟨_, hB.surj, fun z hz => hB.ker_central z hz⟩
  have hn6 : 6 ≤ r + 1 := by
    have h3 : r + 1 ≠ 3 := fun h => hne (by rw [h]; rfl)
    omega
  rcases Nat.even_or_odd (r + 1) with heven | hodd
  · by_cases h6 : r + 1 = 6
    ·
      obtain rfl : r = 5 := by omega
      have hEm : Nat.card (E.map ρ) = 27 := by
        rw [card_map_eq_of_isPGroup_three_of_coprime hcop
          (isPGroup_three_of_isElemAbelian_three hE), hE27]
        norm_num
      have h27 : 27 ∣ Nat.card (J.map ρ) :=
        hEm ▸ Subgroup.card_dvd_of_le (Subgroup.map_mono hEJ)
      exact not_dvd_card_of_su_six hcard hX α hαs hαk S₁ (J.map ρ) hN₁ hJ₁ hperf₁ h27
    ·
      have hn12 : 12 ≤ r + 1 := by
        obtain ⟨m, hm⟩ := heven
        omega
      set k : Fin ((r + 1) / 2) := ⟨(r + 1) / 2 - 1, by omega⟩ with hkdef
      have hk : ¬k.val + 1 < (r + 1) / 2 := by simp only [hkdef]; omega
      obtain ⟨ζ', π', hQ, -, hTJ, -, -⟩ :=
        exists_lastNode_decomposition_su hcard (by omega) hk α hαs hαk S₁ (J.map ρ) hN₁ hJ₁
          hperf₁
      have hT0 : IsElemAbelian 3 (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := r + 1) i) := by
        refine ⟨⟨⟨fun a b => Subtype.ext (commute_of_mem_sup_tori hQ.extras a.2 b.2).eq⟩⟩,
          fun t ht => ?_⟩
        have h3 := hQ.pow_eq_one_of_mem_iSup ht
        rwa [hcard] at h3
      have hTe := isElemAbelian_map_of_isElemAbelian π' hT0
      have hTc := pow_four_le_card_map_torus_su hcard hn12 hQ.ker_central
      obtain ⟨E', hE'J, hE', hE'c⟩ := exists_elemAbelian_le_of_map_of_coprime hρ hcop hkJ hTJ hTe
      obtain ⟨j, hj⟩ := (isPGroup_three_of_isElemAbelian_three hTe).exists_card_eq
      have h4 : 4 ≤ j := by
        rw [hj] at hTc
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hTc
      have := le_pRank_of_elemAbelian_le (by norm_num) hE'J hE' (hE'c.trans hj)
      omega
  ·
    have hodd' : ¬Even (r + 1) := Nat.not_even_iff_odd.2 hodd
    have hexc := isThreeExceptional_of_su_odd hcard (by omega) hodd' α hαs hαk S₁ (J.map ρ) hN₁
      hJ₁ hperf₁
    have hall := (ThreeDichotomy.clauses (ThreeDichotomy.of_map hρ hkJ hcop (Or.inr hexc))).2.2.2
      hO3
    obtain ⟨-, -, R₁, V₁, N₁, hRN, -, hNJ', -, -, -, -, hR3, a₁, ha₁, b₁, hb₁, hab⟩ := hexc
    obtain ⟨R, hRle, hR, hRm⟩ := exists_isPGroup_three_map_eq hρ hR3
    have hRJ : R ≤ J := hRle.trans ((Subgroup.comap_mono (hRN.trans hNJ')).trans
      (by rw [Subgroup.comap_map_eq, sup_eq_left.2 hkJ]))
    have hRe := hall R hRJ hR
    rw [← hRm] at ha₁ hb₁
    obtain ⟨a, ha, rfl⟩ := ha₁
    obtain ⟨b, hb, rfl⟩ := hb₁
    apply hab
    have hc := congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← map_mul, ← map_mul, hc]

end CFSG.AGLEmbedding

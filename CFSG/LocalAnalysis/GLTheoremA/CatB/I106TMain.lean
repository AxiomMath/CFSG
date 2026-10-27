module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I106TGroup
open scoped commutatorElement

theorem I106T1430At_of_facts (G : Type) [Group G] [Finite G]
    (hE27 : I106TE27Fact) (hSp48 : I106TSp48Fact) : I106T1430At G := by
  unfold I106T1430At
  intro X J hJ hcat
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hZ : ∀ z ∈ Subgroup.center (PQuot 3 J), ∃ n : ℕ, z ^ 3 ^ n = 1 :=
    center_pQuot_three_pow J
  have hNcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNcop
  refine ⟨fun hnot => ?_, fun hsp y hy hy3 hni => ?_⟩
  ·
    obtain ⟨i, hi, ⟨e⟩⟩ := hcat
    have hi' : ¬ isSp48 i := fun h => hnot ⟨i, h, ⟨e⟩⟩
    obtain ⟨E, hE, hcard, hcap⟩ := hE27 i (PQuot 3 J) hi hi' hQ hZ ⟨e⟩
    obtain ⟨F, hFM, hFN, hFmap, hFab, hFcard⟩ :=
      exists_lift_elemAb (GLAPPrimeCore 3 ↥J) hNcop
        (E.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)))
        E (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E) hE
    refine ⟨F.map J.subtype, Subgroup.map_subtype_le F, isElemAbelian_map_of_hom hFab, ?_,
      eq_one_of_centMod F E hFN hFmap hcap⟩
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hFcard, hcard]
  ·
    obtain ⟨i, hi, ⟨e⟩⟩ := hsp
    have hφN : (GLAPPrimeCore 3 ↥J).map (conjJ J y hy).toMonoidHom = GLAPPrimeCore 3 ↥J :=
      CFSG.pPrimeCore_map_iso 3 (conjJ J y hy)
    let α : PQuot 3 J ≃* PQuot 3 J :=
      QuotientGroup.congr (GLAPPrimeCore 3 ↥J) (GLAPPrimeCore 3 ↥J) (conjJ J y hy) hφN
    have hα_mk : ∀ x : ↥J, α (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) x) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (conjJ J y hy x) :=
      fun x => QuotientGroup.congr_mk _ _ _ _ x
    have hφ3 : ∀ z : ↥J, conjJ J y hy (conjJ J y hy (conjJ J y hy z)) = z := by
      intro z
      apply Subtype.ext
      show y⁻¹ * (y⁻¹ * (y⁻¹ * (z : G) * y) * y) * y = z
      have h2 : y⁻¹ * (y⁻¹ * (y⁻¹ * (z : G) * y) * y) * y = (y ^ 3)⁻¹ * (z : G) * y ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_rev, inv_mul_cancel_left,
          mul_inv_cancel_left, inv_inv]
      rw [h2, hy3, inv_one, one_mul, mul_one]
    have hα3 : ∀ z, α (α (α z)) = z := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) z
      rw [hα_mk, hα_mk, hα_mk, hφ3]
    have hnon : ¬ ∃ h : PQuot 3 J, ∀ x : PQuot 3 J, α x = h * x * h⁻¹ := by
      rintro ⟨h, hh⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) h
      apply hni
      refine ⟨((u⁻¹ : ↥J) : G), (u⁻¹ : ↥J).2, fun w hw => ?_⟩
      have hw1 := hh (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) ⟨w, hw⟩)
      rw [hα_mk, ← map_inv, ← map_mul, ← map_mul] at hw1
      have hw2 := QuotientGroup.eq.1 hw1
      have hz : (u * ⟨w, hw⟩ * u⁻¹)⁻¹ * conjJ J y hy ⟨w, hw⟩ ∈ GLAPPrimeCore 3 ↥J := by
        have e' : (u * ⟨w, hw⟩ * u⁻¹)⁻¹ * conjJ J y hy ⟨w, hw⟩ =
            ((conjJ J y hy ⟨w, hw⟩)⁻¹ * (u * ⟨w, hw⟩ * u⁻¹))⁻¹ := by group
        rw [e']
        exact (GLAPPrimeCore 3 ↥J).inv_mem hw2
      have hz' := (mem_glaPPrimeCoreOf_iff' _).2 hz
      convert hz' using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ_val]
      group
    obtain ⟨E, hE, hcard, hfix, hcap⟩ := hSp48 i (PQuot 3 J) hi hQ hZ ⟨e⟩ α hα3 hnon
    have hlift : ∀ e' : E, ∃ c : ↥J, QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) c = (e' : PQuot 3 J) ∧
        conjJ J y hy c = c := by
      intro e'
      obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) (e' : PQuot 3 J)
      have hf := hfix (e' : PQuot 3 J) e'.2
      rw [← hx0, hα_mk] at hf
      obtain ⟨c, hc1, hc2⟩ := exists_fixed_lift hN3 (conjJ J y hy) hφN hφ3 x0 hf
      exact ⟨c, hc1.trans hx0, hc2⟩
    choose c hc1 hc2 using hlift
    have hMmap : (Subgroup.closure (Set.range c)).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = E := by
      rw [MonoidHom.map_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨_, ⟨e', rfl⟩, rfl⟩
        rw [hc1 e']
        exact e'.2
      · intro q hq
        have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (c ⟨q, hq⟩) ∈
            Subgroup.closure (⇑(QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) '' Set.range c) :=
          Subgroup.subset_closure ⟨c ⟨q, hq⟩, Set.mem_range_self _, rfl⟩
        rwa [hc1 ⟨q, hq⟩] at hmem
    have hCy : Subgroup.closure (Set.range c) ≤
        (Subgroup.centralizer ({y} : Set G)).subgroupOf J := by
      rw [Subgroup.closure_le]
      rintro _ ⟨e', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun z : ↥J => (z : G)) (hc2 e')
      simp only [conjJ_val] at h
      calc (c e' : G) * y = y * (y⁻¹ * (c e' : G) * y) := by group
        _ = y * (c e' : G) := by rw [h]
    obtain ⟨F, hFM, hFN, hFmap, hFab, hFcard⟩ :=
      exists_lift_elemAb (GLAPPrimeCore 3 ↥J) hNcop (Subgroup.closure (Set.range c)) E hMmap hE
    refine ⟨F.map J.subtype, ?_, isElemAbelian_map_of_hom hFab, ?_,
      eq_one_of_centMod F E hFN hFmap hcap⟩
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨m.2, Subgroup.mem_subgroupOf.1 (hCy (hFM hm))⟩
    · rw [Subgroup.card_map_of_injective Subtype.val_injective, hFcard, hcard]

end CFSG.LocalAnalysis.GLTheoremA.S8.L84

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42T2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43 (card_subgroupOf_of_le card_PSp43_eq factorization_two_25920)

section Rows

variable {G : Type} [Group G] [Finite G]

theorem i2811TAt_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : I2811TAt G := by
  intro X K E z hK hcat hodd hzc hz2 hz1 hEc hEel hEcard
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hZ := center_pQuot_eq_bot_u4two hGA hq hcat
  obtain ⟨e⟩ := bridge_u4two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk3 : ¬ 3 ∣ Nat.card π.ker := not_three_dvd_card_ker K hkc hZ
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker K hkc hodd
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top_of_surjective π hπs
  have hKcard : Nat.card K = Nat.card π.ker * 25920 := by
    have h1 := π.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, card_PSp43_eq] at h1
    exact h1.symm
  have hKfac : (Nat.card K).factorization 2 = 6 := by
    have hpos : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    rw [hKcard, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hk2, factorization_two_25920, zero_add]
  obtain ⟨hzK, P', hP'K, hP'2, hzP', hP'c, hmax⟩ := hzc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 (P'.subgroupOf K) :=
    hP'2.of_equiv (Subgroup.subgroupOfEquivOfLe hP'K).symm
  have hP'card : Nat.card P' = 64 := by
    obtain ⟨R, hR⟩ := hW2.exists_le_sylow
    have hRK : (R : Subgroup K).map K.subtype = P' := by
      refine hmax _ ?_ (Subgroup.map_subtype_le _) (R.2.map K.subtype)
      intro x hx
      exact ⟨⟨x, hP'K hx⟩, hR (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have hc : Nat.card (R : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
      Sylow.card_eq_multiplicity R
    rw [← hRK, Subgroup.card_map_of_injective K.subtype_injective, hc, hKfac]
    norm_num
  set W := P'.subgroupOf K with hWdef
  have hWinj : Function.Injective (π.comp W.subtype) := injective_comp_subtype Nat.prime_two π hk2 hW2
  have hWcard : Nat.card (W.map π) = 64 := by
    rw [← card_eq_of_injective_comp_subtype π hWinj, hWdef, card_subgroupOf_of_le hP'K, hP'card]
  have hcomm_K : ∀ w ∈ W, (⟨z, hzK⟩ : K) * w = w * ⟨z, hzK⟩ := by
    intro w hw
    have hwP : (w : G) ∈ P' := Subgroup.mem_subgroupOf.1 hw
    have hwz := Subgroup.mem_centralizer_singleton_iff.1 (hP'c hwP)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hwz.symm
  have hSbc : ∀ s ∈ W.map π, π ⟨z, hzK⟩ * s = s * π ⟨z, hzK⟩ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hcomm_K w hw]
  have hzbS : π ⟨z, hzK⟩ ∈ W.map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hzP')
  have hzb2 : π ⟨z, hzK⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨z, hzK⟩ : K) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [this, map_one]
  have hzb1 : π ⟨z, hzK⟩ ≠ 1 := by
    intro h
    have hmem : (⟨z, hzK⟩ : K) ∈ π.ker := h
    have hne : (⟨⟨z, hzK⟩, hmem⟩ : π.ker) ≠ 1 := by
      intro h1
      apply hz1
      exact congrArg Subtype.val (congrArg Subtype.val h1)
    have hsq : (⟨⟨z, hzK⟩, hmem⟩ : π.ker) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hz2
    have hord := orderOf_eq_prime hsq hne
    have hdvd := orderOf_dvd_natCard (⟨⟨z, hzK⟩, hmem⟩ : π.ker)
    rw [hord] at hdvd
    exact hk2 hdvd
  have hEK : E ≤ K := fun x hx => (Subgroup.mem_inf.1 (hEc hx)).1
  set W3 := E.subgroupOf K with hW3def
  have hW3 : IsPGroup 3 W3 :=
    (isPGroup_of_isElemAbelian hEel).of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  have hW3inj : Function.Injective (π.comp W3.subtype) :=
    injective_comp_subtype Nat.prime_three π hk3 hW3
  have hEbcard : Nat.card (W3.map π) = 9 := by
    rw [← card_eq_of_injective_comp_subtype π hW3inj, hW3def, card_subgroupOf_of_le hEK, hEcard]
    norm_num
  have hEbc : ∀ f ∈ W3.map π, π ⟨z, hzK⟩ * f = f * π ⟨z, hzK⟩ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (hEc (Subgroup.mem_subgroupOf.1 ha))).2
    exact h1.symm
  obtain ⟨Tb, hTb2, hTbcard, hTbn, xb, hxb, yb, hyb, hxy⟩ :=
    YS09U42T2.finite_psp43_part hzb2 hzb1 (hW2.map π) hWcard hzbS hSbc hEbc hEbcard
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup K, M = Tb.comap π := ⟨_, rfl⟩
  have hMmem : ∀ x : K, x ∈ M ↔ π x ∈ Tb := fun x => by rw [hMdef]; exact Iff.rfl
  have hMcard : Nat.card M = Nat.card π.ker * 32 := by
    have h1 := M.card_mul_index
    have h2 := Tb.card_mul_index
    have hidx : M.index = Tb.index := by
      rw [hMdef]; exact Subgroup.index_comap_of_surjective Tb hπs
    rw [hidx, hKcard] at h1
    rw [hTbcard, card_PSp43_eq] at h2
    have hi : Tb.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
    rw [h1]
    calc Nat.card π.ker * 25920 = Nat.card π.ker * (32 * Tb.index) := by rw [h2]
      _ = Nat.card π.ker * 32 * Tb.index := by ring
  have hMcop : ¬ 3 ∣ Nat.card M := by
    rw [hMcard]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · exact hk3 h1
    · norm_num at h1
  have hMnorm : ∀ a : K, a ∈ W3 → ∀ x : K, π x ∈ Tb → π (a * x * a⁻¹) ∈ Tb := by
    intro a ha x hx
    rw [map_mul, map_mul, map_inv]
    exact hTbn (π a) (Subgroup.mem_map_of_mem π ha) (π x) hx
  let conjK : W3 →* MulAut K := (MulAut.conj : K →* MulAut K).comp W3.subtype
  have hinv : ∀ a : W3, M.map (conjK a).toMonoidHom = M := by
    intro a
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      show (a : K) * m * (a : K)⁻¹ ∈ M
      rw [hMmem]
      exact hMnorm (a : K) a.2 m ((hMmem m).1 hm)
    · intro x hx
      refine ⟨(a : K)⁻¹ * x * (a : K), ?_, ?_⟩
      · show (a : K)⁻¹ * x * (a : K) ∈ M
        rw [hMmem]
        have h1 := hMnorm ((a : K)⁻¹) (W3.inv_mem a.2) x ((hMmem x).1 hx)
        simpa only [inv_inv] using h1
      · show (a : K) * ((a : K)⁻¹ * x * (a : K)) * (a : K)⁻¹ = x
        group
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨sylow, hsyl⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 2
    hW3 hMcop (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism conjK M hinv)
  obtain ⟨S, hS⟩ : ∃ S : Subgroup M, (sylow : Subgroup M) = S := ⟨_, rfl⟩
  rw [hS] at hsyl
  have hS2 : IsPGroup 2 S := hS ▸ sylow.2
  have hS_card : Nat.card S = 32 := by
    have h1 := sylow.card_eq_multiplicity
    rw [hS] at h1
    have hfac : (Nat.card M).factorization 2 = 5 := by
      rw [hMcard, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hk2, zero_add,
        show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
    rw [hfac] at h1
    simpa using h1
  obtain ⟨TK, hTKdef⟩ : ∃ TK : Subgroup K, TK = S.map M.subtype := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup G, T = TK.map K.subtype := ⟨_, rfl⟩
  have hTK_card : Nat.card TK = 32 := by
    rw [hTKdef, Subgroup.card_map_of_injective M.subtype_injective, hS_card]
  have hT_card : Nat.card T = 32 := by
    rw [hTdef, Subgroup.card_map_of_injective K.subtype_injective, hTK_card]
  have hTK2 : IsPGroup 2 TK := by rw [hTKdef]; exact hS2.map M.subtype
  have hT2 : IsPGroup 2 T := by rw [hTdef]; exact hTK2.map K.subtype
  have hTKn : ∀ a : W3, ∀ k ∈ TK, (a : K) * k * (a : K)⁻¹ ∈ TK := by
    intro a k hk
    rw [hTKdef] at hk ⊢
    obtain ⟨m, hm, rfl⟩ := hk
    have h1 : (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism conjK M hinv a) m ∈ S := by
      rw [← hsyl a]
      exact Subgroup.mem_map_of_mem _ hm
    exact ⟨(CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism conjK M hinv a) m, h1, rfl⟩
  have hTn_G : ∀ a : W3, ∀ t ∈ T, (a : G) * t * (a : G)⁻¹ ∈ T := by
    intro a t ht
    rw [hTdef] at ht ⊢
    obtain ⟨k, hk, rfl⟩ := ht
    refine ⟨(a : K) * k * (a : K)⁻¹, hTKn a k hk, ?_⟩
    simp
  have hEnorm : E ≤ Subgroup.normalizer (T : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact hTn_G ⟨⟨e, hEK he⟩, Subgroup.mem_subgroupOf.2 he⟩ t ht
    · intro ht
      have h2 := hTn_G ⟨⟨e⁻¹, hEK (E.inv_mem he)⟩, Subgroup.mem_subgroupOf.2 (E.inv_mem he)⟩ _ ht
      simpa [mul_assoc] using h2
  have hπTK : TK.map π = Tb := by
    have hinj : Function.Injective (π.comp TK.subtype) :=
      injective_comp_subtype Nat.prime_two π hk2 hTK2
    have hc1 := card_eq_of_injective_comp_subtype π hinj
    have hle : TK.map π ≤ Tb := by
      rintro _ ⟨k, hk, rfl⟩
      rw [hTKdef] at hk
      obtain ⟨m, hm, rfl⟩ := hk
      exact (hMmem (M.subtype m)).1 m.2
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [← hc1, hTK_card, hTbcard]))
  obtain ⟨a, ha, rfl⟩ := hyb
  have hxb' : xb ∈ TK.map π := by rw [hπTK]; exact hxb
  obtain ⟨k, hk, hkx⟩ := hxb'
  have hkne : (k : K) * a ≠ a * (k : K) := by
    intro h
    apply hxy
    rw [← hkx, ← map_mul, ← map_mul, h]
  refine ⟨T, ?_, hT2, hEnorm, ?_, ?_, ?_⟩
  · rw [hTdef]; exact Subgroup.map_subtype_le _
  · intro hbot
    have hkT : K.subtype k ∈ T := by rw [hTdef]; exact ⟨k, hk, rfl⟩
    have hmem := Subgroup.commutator_mem_commutator hkT (Subgroup.mem_subgroupOf.1 ha)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    apply hkne
    apply Subtype.ext
    simpa using hmem
  · intro hTO
    have h1 := Subgroup.card_dvd_of_le hTO
    rw [hT_card] at h1
    have h2 : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := (by norm_num : (2:ℕ) ∣ 32).trans h1
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  · constructor
    intro φ
    have h1 := Nat.card_congr φ.toEquiv
    rw [hT_card, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
    norm_num at h1

end Rows

section Holds


theorem i2811TAt_holds (G : Type) [Group G] [Finite G] : I2811TAt G :=
  i2811TAt_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB

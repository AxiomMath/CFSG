module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarHN
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarAlt

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Sets

abbrev fiveSupp : Finset (Fin 16) := Finset.univ.filter fun i => 4 ≤ (i : ℕ) ∧ (i : ℕ) < 9

abbrev nineSet : Finset (Fin 16) :=
  Finset.univ.filter fun i => (i : ℕ) < 4 ∨ (9 ≤ (i : ℕ) ∧ (i : ℕ) < 14)

theorem fiveCyc_mem_fixSub : fiveCyc ∈ fixSub fiveSuppᶜ := fun i hi => by revert i; decide

theorem zpowers_fiveCyc_le : zpowers fiveCyc ≤ fixSub fiveSuppᶜ :=
  (zpowers_le).2 fiveCyc_mem_fixSub

theorem zpowers_fiveCyc_comm : ∀ r ∈ zpowers fiveCyc, ∀ s ∈ zpowers fiveCyc, r * s = s * r := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact (Commute.zpow_zpow_self fiveCyc a b).eq

theorem fiveCyc_transitive :
    ∀ i ∈ fiveSupp, ∀ j ∈ fiveSupp, ∃ r ∈ zpowers fiveCyc, r i = j := by
  have h : ∀ i ∈ fiveSupp, ∀ j ∈ fiveSupp, ∃ k ∈ Finset.range 5, (fiveCyc ^ k) i = j := by
    decide
  intro i hi j hj
  obtain ⟨k, -, hk⟩ := h i hi j hj
  exact ⟨fiveCyc ^ k, pow_mem (mem_zpowers _) k, hk⟩

theorem altSub_nineSet_le : altSub nineSet ≤ fixSub fiveSupp := by
  intro σ hσ i hi
  exact (mem_altSub.1 hσ).2 i (by revert i; decide)

theorem altSub_fiveCompl_le : altSub fiveSuppᶜ ≤ fixSub fiveSupp := by
  intro σ hσ i hi
  exact (mem_altSub.1 hσ).2 i (by simpa using hi)

theorem nineSet_subset : nineSet ⊆ fiveSuppᶜ := by decide

theorem mem_nineSet_iff (i : Fin 16) :
    i ∈ nineSet ↔ i ∉ fiveCyc.support ∧ i ∉ (OverData.tau 13).support := by
  revert i; decide

abbrev threeCyc : Perm (Fin 16) := OverData.tau 13 * swap 13 14 * (OverData.tau 13)⁻¹ * (swap 13 14)⁻¹

theorem threeCyc_mem : threeCyc ∈ altSub fiveSuppᶜ := mem_altSub.2 ⟨by decide, by decide⟩

theorem orderOf_threeCyc : orderOf threeCyc = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (by decide)
  rw [show threeCyc ^ 3 = threeCyc * threeCyc * threeCyc by
    simp only [pow_succ, pow_zero, one_mul]]
  decide

end Sets

section Five

variable {G : Type} [Group G] [Finite G] {z : G} (O : OverData G z 13)

abbrev fiveC : Subgroup G := centralizer ({O.φ fiveCyc} : Set G)

omit [Finite G] in
theorem fixSub_comm_five {s : Perm (Fin 16)} (hs : s ∈ fixSub fiveSupp) :
    O.φ s ∈ fiveC O := by
  rw [fiveC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact congrArg O.φ (comm_fixSub_compl fiveCyc_mem_fixSub hs).symm

@[expose] noncomputable def fiveIncl (K : Subgroup (Perm (Fin 16))) (hK : K ≤ fixSub fiveSupp) :
    K →* fiveC O :=
  (O.φ.comp K.subtype).codRestrict _ (fun σ => fixSub_comm_five O (hK σ.2))

omit [Finite G] in
theorem fiveIncl_apply (K : Subgroup (Perm (Fin 16))) (hK : K ≤ fixSub fiveSupp) (σ : K) :
    ((fiveIncl O K hK σ : fiveC O) : G) = O.φ σ := rfl

omit [Finite G] in
theorem fiveIncl_injective (K : Subgroup (Perm (Fin 16))) (hK : K ≤ fixSub fiveSupp) :
    Function.Injective (fiveIncl O K hK) := by
  intro a b hab
  have := congrArg Subtype.val hab
  exact Subtype.ext (O.φ_injective this)

@[expose] noncomputable def fiveT : fiveC O :=
  ⟨z, by
    rw [fiveC, mem_centralizer_singleton_iff]
    have h : O.φ (OverData.tau 13) * O.φ fiveCyc = O.φ fiveCyc * O.φ (OverData.tau 13) := by
      rw [← map_mul, ← map_mul]
      exact congrArg O.φ fiveCyc_comm_tau.symm
    rwa [O.φ_tau] at h⟩

@[expose] noncomputable def fiveB : Subgroup (fiveC O) :=
  (fiveIncl O _ altSub_nineSet_le).range

@[expose] noncomputable def fiveL : Subgroup (fiveC O) :=
  (fiveIncl O _ altSub_fiveCompl_le).range

theorem card_nineSet : nineSet.card = 9 := by decide

theorem card_fiveCompl : (fiveSuppᶜ).card = 11 := by decide

@[expose] noncomputable def fiveBEquiv : fiveB O ≃* alternatingGroup (Fin 9) :=
  (MonoidHom.ofInjective (fiveIncl_injective O _ altSub_nineSet_le)).symm.trans
    ((altSubEquiv _).trans (Equiv.altCongrHom (finCongr card_nineSet)))

@[expose] noncomputable def fiveLEquiv : fiveL O ≃* alternatingGroup (Fin 11) :=
  (MonoidHom.ofInjective (fiveIncl_injective O _ altSub_fiveCompl_le)).symm.trans
    ((altSubEquiv _).trans (Equiv.altCongrHom (finCongr card_fiveCompl)))

theorem fiveL_inf_oddCore : fiveL O ⊓ CFSG.oddCore (fiveC O) = ⊥ :=
  inf_oddCore_eq_bot_of_alt (by norm_num) (fiveLEquiv O)

omit [Finite G] in
theorem orderOf_fiveT : orderOf (fiveT O) = 2 := by
  have h := orderOf_injective O.φ O.φ_injective (OverData.tau 13)
  rw [O.φ_tau] at h
  rw [fiveT, Subgroup.orderOf_mk, h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

omit [Finite G] in
theorem zpowers_five_le_oddCore :
    zpowers (⟨O.φ fiveCyc, mem_centralizer_singleton_iff.2 rfl⟩ : fiveC O) ≤
      CFSG.oddCore (fiveC O) := by
  set ff : fiveC O := ⟨O.φ fiveCyc, mem_centralizer_singleton_iff.2 rfl⟩ with hff
  have hcen : ∀ c : fiveC O, c * ff = ff * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
  have hN : (zpowers ff).Normal := by
    refine ⟨fun x hx c => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have : c * ff ^ k * c⁻¹ = ff ^ k := by
      rw [(Commute.zpow_right (show Commute c ff from hcen c) k).eq]
      group
    rw [this]
    exact zpow_mem (mem_zpowers ff) k
  have hodd : Odd (Nat.card (zpowers ff)) := by
    rw [Nat.card_zpowers, hff, Subgroup.orderOf_mk,
      orderOf_injective O.φ O.φ_injective, orderOf_fiveCyc]
    decide
  exact le_sSup ⟨hN, hodd⟩

omit [Finite G] in
theorem fiveB_le_cent : fiveB O ≤ centralizer ({fiveT O} : Set (fiveC O)) := by
  rintro _ ⟨σ, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  change O.φ σ * z = z * O.φ σ
  have h : O.φ σ * O.φ (OverData.tau 13) = O.φ (OverData.tau 13) * O.φ σ := by
    rw [← map_mul, ← map_mul]
    refine congrArg O.φ (swap_comm_of_fixed ?_ ?_).symm
    · exact (mem_altSub.1 σ.2).2 _ (by decide)
    · exact (mem_altSub.1 σ.2).2 _ (by decide)
  rwa [O.φ_tau] at h

omit [Finite G] in
theorem exists_of_cent_fiveT {c : fiveC O} (hc : c * fiveT O = fiveT O * c) :
    ∃ x : Perm (Fin 16), O.φ x = c ∧ x * OverData.tau 13 = OverData.tau 13 * x ∧
      x * fiveCyc = fiveCyc * x := by
  have hcz : (c : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hc
  obtain ⟨x, hx, hxτ⟩ := O.exists_of_mem_centralizer_z hcz
  refine ⟨x, hx, hxτ, ?_⟩
  have h1 : (c : G) * O.φ fiveCyc = O.φ fiveCyc * c := mem_centralizer_singleton_iff.1 c.2
  rw [← hx] at h1
  exact O.φ_comm_iff.1 h1

omit [Finite G] in
theorem cent_fiveT_le_normalizer :
    centralizer ({fiveT O} : Set (fiveC O)) ≤ normalizer (fiveB O : Set (fiveC O)) := by
  intro c hc
  obtain ⟨x, hx, hxτ, hxf⟩ := exists_of_cent_fiveT O (mem_centralizer_singleton_iff.1 hc)
  have hpres : ∀ i, i ∈ nineSet ↔ x i ∈ nineSet := by
    intro i
    rw [mem_nineSet_iff, mem_nineSet_iff, ← mem_support_iff_of_comm hxf i,
      ← mem_support_iff_of_comm hxτ i]
  have hpres' : ∀ i, i ∈ nineSet ↔ x⁻¹ i ∈ nineSet := by
    intro i
    rw [hpres (x⁻¹ i)]
    simp
  have hxN := mem_normalizer_altSub hpres
  have hxN' := mem_normalizer_altSub hpres'
  rw [mem_normalizer_iff]
  intro b
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨⟨x * σ * x⁻¹, (mem_normalizer_iff.1 hxN σ).1 σ.2⟩, ?_⟩
    apply Subtype.ext
    rw [fiveIncl_apply]
    change O.φ (x * σ * x⁻¹) = (c : G) * O.φ σ * (c : G)⁻¹
    rw [map_mul, map_mul, map_inv, hx]
  · rintro ⟨σ, hσ⟩
    have hb : (b : G) = (c : G)⁻¹ * O.φ σ * c := by
      have := congrArg Subtype.val hσ
      rw [fiveIncl_apply] at this
      change O.φ σ = (c : G) * b * (c : G)⁻¹ at this
      rw [this]; group
    refine ⟨⟨x⁻¹ * σ * x⁻¹⁻¹, (mem_normalizer_iff.1 hxN' σ).1 σ.2⟩, ?_⟩
    apply Subtype.ext
    rw [fiveIncl_apply, hb]
    change O.φ (x⁻¹ * σ * x⁻¹⁻¹) = _
    simp only [map_mul, map_inv, inv_inv, hx]

omit [Finite G] in
theorem cent_fiveB_inf_le :
    centralizer (fiveB O : Set (fiveC O)) ⊓ centralizer ({fiveT O} : Set (fiveC O)) ≤
      zpowers (fiveT O) ⊔ CFSG.oddCore (fiveC O) := by
  intro c hc
  obtain ⟨hcB, hct⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨x, hx, hxτ, hxf⟩ := exists_of_cent_fiveT O (mem_centralizer_singleton_iff.1 hct)
  have hxA : ∀ σ ∈ altSub nineSet, σ * x = x * σ := by
    intro σ hσ
    have h1 := mem_centralizer_iff.1 hcB (fiveIncl O _ altSub_nineSet_le ⟨σ, hσ⟩) ⟨⟨σ, hσ⟩, rfl⟩
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, fiveIncl_apply, ← hx, ← map_mul, ← map_mul] at h2
    exact O.φ_injective h2
  have hxfix : ∀ i ∈ nineSet, x i = i :=
    (mem_centralizer_altSub_iff (by rw [card_nineSet]; norm_num)).1
      (mem_centralizer_iff.2 hxA)
  obtain ⟨r, hr, s, hs, hrs⟩ := exists_mul_of_mem_centralizer zpowers_fiveCyc_le
    zpowers_fiveCyc_comm fiveCyc_transitive (by decide) (x := x) (fun r hr => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
      exact ((Commute.zpow_right (show Commute x fiveCyc from hxf) k)).eq)
  have hrfix : ∀ i ∉ fiveSupp, r i = i := fun i hi => zpowers_fiveCyc_le hr i (by simpa using hi)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hr
  have hsfix : ∀ i : Fin 16, (i : ℕ) < 13 + 1 → s i = i := by
    intro i hi
    by_cases h5 : i ∈ fiveSupp
    · exact hs i h5
    · have hi9 : i ∈ nineSet := by revert i; decide
      have h1 : x i = i := hxfix i hi9
      rw [hrs, Perm.mul_apply] at h1
      rcases em (s i ∈ fiveSupp) with h2 | h2
      · exfalso
        have h3 : s (s i) = s i := hs _ h2
        have h4 := s.injective h3
        rw [h4] at h2
        exact h5 h2
      · rw [hrfix _ h2] at h1
        exact h1
  set ff : fiveC O := ⟨O.φ fiveCyc, mem_centralizer_singleton_iff.2 rfl⟩ with hff
  have hffk : ((ff ^ k : fiveC O) : G) = O.φ (fiveCyc ^ k) := by
    rw [map_zpow]
    rfl
  have hk : ff ^ k ∈ CFSG.oddCore (fiveC O) :=
    zpowers_five_le_oddCore O (zpow_mem (mem_zpowers _) _)
  rcases eq_one_or_eq_tau hsfix with hs1 | hs1
  ·
    have hc' : c = ff ^ k := by
      apply Subtype.ext
      rw [hffk, ← hx, hrs, hs1, mul_one]
    rw [hc']
    exact mem_sup_right hk
  ·
    have hc' : c = ff ^ k * fiveT O := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hffk, ← hx, hrs, hs1, map_mul, O.φ_tau]
      rfl
    rw [hc']
    exact mul_mem (mem_sup_right hk) (mem_sup_left (mem_zpowers _))

theorem exactShape_five :
    ExactShape (QuotientGroup.mk (fiveT O) : fiveC O ⧸ CFSG.oddCore (fiveC O))
      ((fiveB O).map (QuotientGroup.mk' (CFSG.oddCore (fiveC O)))) 9 :=
  exactShape_quotient_oddCore (orderOf_fiveT O) (by norm_num) (fiveBEquiv O)
    (fiveB_le_cent O) (cent_fiveT_le_normalizer O) (cent_fiveB_inf_le O)

end Five

section Card

variable {G : Type} [Group G] [Finite G] {z : G} (O : OverData G z 13)

omit [Finite G] in
theorem fiveB_le_fiveL : fiveB O ≤ fiveL O := by
  rintro _ ⟨σ, rfl⟩
  exact ⟨⟨σ, altSub_mono nineSet_subset σ.2⟩, Subtype.ext rfl⟩

theorem fiveLq_injective :
    Function.Injective ((QuotientGroup.mk' (CFSG.oddCore (fiveC O))).comp
      (fiveIncl O _ altSub_fiveCompl_le)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : fiveIncl O _ altSub_fiveCompl_le y ∈ CFSG.oddCore (fiveC O) :=
    (QuotientGroup.eq_one_iff _).1 hy
  have h2 : fiveIncl O _ altSub_fiveCompl_le y ∈ fiveL O ⊓ CFSG.oddCore (fiveC O) :=
    Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, h1⟩
  rw [fiveL_inf_oddCore O, mem_bot] at h2
  exact fiveIncl_injective O _ _ (h2.trans (map_one _).symm)

theorem fiveT_notMem_center :
    (QuotientGroup.mk (fiveT O) : fiveC O ⧸ CFSG.oddCore (fiveC O)) ∉
      center (fiveC O ⧸ CFSG.oddCore (fiveC O)) := by
  intro hc
  have hsw : swap (13 : Fin 16) 14 ∈ fixSub fiveSupp := fun i hi => by revert i; decide
  set w := fiveIncl O _ le_rfl ⟨swap 13 14, hsw⟩ with hw
  have h1 := (mem_center_iff.1 hc) (QuotientGroup.mk w)
  have h2 : fiveT O * w * (fiveT O)⁻¹ * w⁻¹ ∈ CFSG.oddCore (fiveC O) := by
    apply (QuotientGroup.eq_one_iff _).1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← h1]
    group
  have h3 : fiveT O * w * (fiveT O)⁻¹ * w⁻¹ =
      fiveIncl O _ altSub_fiveCompl_le ⟨threeCyc, threeCyc_mem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, fiveIncl_apply, hw]
    rw [show threeCyc = OverData.tau 13 * swap 13 14 * (OverData.tau 13)⁻¹ * (swap 13 14)⁻¹ from rfl]
    simp only [map_mul, map_inv, O.φ_tau]
    rfl
  rw [h3] at h2
  have h4 : fiveIncl O _ altSub_fiveCompl_le ⟨threeCyc, threeCyc_mem⟩ ∈
      fiveL O ⊓ CFSG.oddCore (fiveC O) := Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, h2⟩
  rw [fiveL_inf_oddCore O, mem_bot] at h4
  have h5 := fiveIncl_injective O _ _ (h4.trans (map_one _).symm)
  have h6 : threeCyc = 1 := congrArg Subtype.val h5
  exact absurd h6 (by decide)

theorem not_wreath_five :
    ¬ WreathOutcome (QuotientGroup.mk (fiveT O) : fiveC O ⧸ CFSG.oddCore (fiveC O))
      ((fiveB O).map (QuotientGroup.mk' (CFSG.oddCore (fiveC O)))) 9 := by
  intro hW
  set π := QuotientGroup.mk' (CFSG.oddCore (fiveC O)) with hπ
  set ψ := π.comp (fiveIncl O _ altSub_fiveCompl_le) with hψ
  have hψi : Function.Injective ψ := fiveLq_injective O
  set L := ψ.range with hL
  have eL : L ≃* alternatingGroup (Fin 11) :=
    (MonoidHom.ofInjective hψi).symm.trans
      ((altSubEquiv _).trans (Equiv.altCongrHom (finCongr card_fiveCompl)))
  have : IsSimpleGroup L := isSimpleGroup_of_alt (by norm_num) eL
  obtain ⟨eA⟩ := (exactShape_five O).iso
  refine false_of_wreath_of_big (by norm_num : 7 ≤ 9) hW (L := L) ?_ ?_ ?_
    (exists_not_comm_of_alt (by norm_num) eA)
  · apply closure_eq_top_of_simple
    · intro a x hx
      change Odd (orderOf (a * x * a⁻¹))
      rw [orderOf_conj']
      exact hx
    · set c : ↥(altSub fiveSuppᶜ) := ⟨threeCyc, threeCyc_mem⟩ with hc
      have hcL : ψ c ∈ L := MonoidHom.mem_range.2 ⟨c, rfl⟩
      have hox : orderOf (⟨ψ c, hcL⟩ : L) = 3 := by
        rw [Subgroup.orderOf_mk, orderOf_injective ψ hψi c, hc, Subgroup.orderOf_mk,
          orderOf_threeCyc]
      refine ⟨⟨ψ c, hcL⟩, ?_, ?_⟩
      · change Odd (orderOf (⟨ψ c, hcL⟩ : L))
        rw [hox]
        decide
      · intro h
        rw [h, orderOf_one] at hox
        omega
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨σ, rfl⟩ := fiveB_le_fiveL O hb
    exact ⟨σ, rfl⟩
  · rw [Nat.card_congr eL.toEquiv]
    have : Nontrivial (Fin 11) := Fin.nontrivial_iff_two_le.2 (by norm_num)
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 11)
    rw [Nat.card_perm, Nat.card_fin] at h2
    have h3 : Nat.factorial 9 = 362880 := by decide
    have h4 : Nat.factorial 11 = 39916800 := by decide
    omega

theorem card_secFive (htri : ExactShapeTrichotomy)
    (hK : CFSG.SectionRank.IsKGroupCat (fiveC O)) :
    Nat.card (fiveC O ⧸ CFSG.oddCore (fiveC O)) = Nat.factorial 11 := by
  have hKX : CFSG.SectionRank.IsKGroupCat (fiveC O ⧸ CFSG.oddCore (fiveC O)) := hK.quotient _
  have hOX : CFSG.oddCore (fiveC O ⧸ CFSG.oddCore (fiveC O)) = ⊥ :=
    ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _
  rcases htri _ _ _ 9 le_rfl hKX hOX (exactShape_five O) with h1 | h2 | h3 | h4
  · exact absurd h1 (fiveT_notMem_center O)
  · exact absurd h2 (not_wreath_five O)
  · obtain ⟨e, -⟩ := h3
    rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  · omega

theorem card_fixSub_fiveSupp : Nat.card (fixSub fiveSupp) = Nat.factorial 11 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _ (fixSubHom_bijective fiveSupp)).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, card_fiveCompl]

theorem card_sevenCompl : ((fourSet 16 ∪ fiveSupp)ᶜ).card = 7 := by decide

theorem card_fixSub_seven : Nat.card (fixSub (fourSet 16 ∪ fiveSupp)) = Nat.factorial 7 := by
  rw [← Nat.card_congr (MulEquiv.ofBijective _ (fixSubHom_bijective _)).toEquiv,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, card_sevenCompl]

theorem card_dvd_of_two_subgroup
    (hcard : Nat.card (fiveC O ⧸ CFSG.oddCore (fiveC O)) = Nat.factorial 11)
    {R : Subgroup (Perm (Fin (13 + 3)))} (hR : SecR 13 R) (T : Subgroup G) (hT2 : IsPGroup 2 T)
    (hTP : T ≤ centralizer (secP O R : Set G)) (hTf : T ≤ fiveC O) : Nat.card T ∣ 20160 := by
  classical
  set π := QuotientGroup.mk' (CFSG.oddCore (fiveC O)) with hπ
  set ι := fiveIncl O (fixSub fiveSupp) le_rfl with hι
  set ψS := π.comp ι with hψS
  have hψSi : Function.Injective ψS := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkO : ι k ∈ CFSG.oddCore (fiveC O) := (QuotientGroup.eq_one_iff _).1 hk
    have hk2 : (k : Perm (Fin 16)) * k ∈ altSub fiveSuppᶜ := by
      rw [mem_altSub]
      refine ⟨by rw [map_mul]; exact Int.units_mul_self _, fun i hi => ?_⟩
      have hi' : i ∈ fiveSupp := by simpa using hi
      rw [Perm.mul_apply, k.2 i hi', k.2 i hi']
    have hk2O : fiveIncl O _ altSub_fiveCompl_le ⟨_, hk2⟩ ∈ fiveL O ⊓ CFSG.oddCore (fiveC O) := by
      refine Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩
      have e : fiveIncl O _ altSub_fiveCompl_le ⟨_, hk2⟩ = ι k * ι k := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, fiveIncl_apply, hι, map_mul]
      rw [e]
      exact mul_mem hkO hkO
    rw [fiveL_inf_oddCore O, mem_bot] at hk2O
    have hk2' : (k : Perm (Fin 16)) * k = 1 :=
      congrArg Subtype.val (fiveIncl_injective O _ _ (hk2O.trans (map_one _).symm))
    have hodd : Odd (orderOf k) := by
      have := orderOf_odd_of_mem_oddCore hkO
      rwa [orderOf_injective ι (fiveIncl_injective O _ le_rfl)] at this
    exact eq_one_of_odd_of_sq hodd (by rw [pow_two]; exact Subtype.ext hk2')
  have hrange : ψS.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (MonoidHom.ofInjective hψSi).toEquiv, card_fixSub_fiveSupp, hcard]
  have hsurj : Function.Surjective ψS := MonoidHom.range_eq_top.1 hrange
  set eS := MulEquiv.ofBijective ψS ⟨hψSi, hsurj⟩ with heS
  set incl : T →* fiveC O := Subgroup.inclusion hTf with hincl
  set φT : T →* fixSub fiveSupp := eS.symm.toMonoidHom.comp (π.comp incl) with hφT
  have heφ : ∀ t : T, ψS (φT t) = π (incl t) := fun t => by
    change eS (eS.symm (π (incl t))) = _
    exact eS.apply_symm_apply _
  have hφTi : Function.Injective φT := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : π (incl t) = 1 := by rw [← heφ t, ht, map_one]
    have h2 : incl t ∈ CFSG.oddCore (fiveC O) := (QuotientGroup.eq_one_iff _).1 h1
    have h3 := orderOf_odd_of_mem_oddCore h2
    rw [orderOf_injective incl (Subgroup.inclusion_injective hTf)] at h3
    obtain ⟨k, hk⟩ := hT2 t
    have h4 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h5 : orderOf t = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 h3)) h4
    exact orderOf_eq_one_iff.1 h5
  have hRS : ∀ r ∈ R, r ∈ fixSub fiveSupp := fun r hr i hi =>
    hR.le hr i (by revert i; decide)
  have hW' : fixSub (fourSet 16 ∪ fiveSupp) ≤ fixSub fiveSupp := fun w hw i hi =>
    hw i (Finset.mem_union_right _ hi)
  have hWF : fixSub (fourSet 16 ∪ fiveSupp) ≤ fixSub (fourSet (13 + 3)) := fun w hw i hi =>
    hw i (Finset.mem_union_left _ hi)
  have hcommRW : ∀ r ∈ R, ∀ w ∈ fixSub (fourSet 16 ∪ fiveSupp), r * w = w * r := fun r hr w hw =>
    comm_fixSub_compl (hR.le hr) (hWF hw)
  let μ : R × ↥(fixSub (fourSet 16 ∪ fiveSupp)) →* fixSub fiveSupp :=
    { toFun := fun p => ⟨(p.1 : Perm (Fin 16)) * p.2, mul_mem (hRS _ p.1.2) (hW' p.2.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun p q => by
        apply Subtype.ext
        change ((p.1 : Perm (Fin 16)) * q.1) * ((p.2 : Perm (Fin 16)) * q.2) =
          ((p.1 : Perm (Fin 16)) * p.2) * ((q.1 : Perm (Fin 16)) * q.2)
        have := hcommRW q.1 q.1.2 p.2 p.2.2
        calc ((p.1 : Perm (Fin 16)) * q.1) * ((p.2 : Perm (Fin 16)) * q.2) =
            (p.1 : Perm (Fin 16)) * ((q.1 : Perm (Fin 16)) * p.2) * q.2 := by group
          _ = (p.1 : Perm (Fin 16)) * ((p.2 : Perm (Fin 16)) * q.1) * q.2 := by rw [this]
          _ = ((p.1 : Perm (Fin 16)) * p.2) * ((q.1 : Perm (Fin 16)) * q.2) := by group }
  have hμi : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨r, w⟩ h
    have h1 : (r : Perm (Fin 16)) * w = 1 := congrArg Subtype.val h
    have h2 : (r : Perm (Fin 16)) = (w : Perm (Fin 16))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (r : Perm (Fin 16)) ∈ fixSub (fourSet (13 + 3)) := by
      rw [h2]; exact inv_mem (hWF w.2)
    have hr1 : (r : Perm (Fin 16)) = 1 := eq_one_of_mem_R_of_mem_fixSub hR r.2 h3
    have hw1 : (w : Perm (Fin 16)) = 1 := by rw [hr1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hr1) (Subtype.ext hw1)
  have hle : φT.range ≤ μ.range := by
    rintro _ ⟨t, rfl⟩
    set σ : fixSub fiveSupp := φT t with hσ
    have hσR : ∀ r ∈ R, (σ : Perm (Fin 16)) * r = r * σ := by
      intro r hr
      have key : ψS (σ * ⟨r, hRS r hr⟩) = ψS (⟨r, hRS r hr⟩ * σ) := by
        rw [map_mul, map_mul, hσ, heφ]
        change π (incl t) * π (ι ⟨r, hRS r hr⟩) = π (ι ⟨r, hRS r hr⟩) * π (incl t)
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        change (t : G) * O.φ r = O.φ r * t
        exact (mem_centralizer_iff.1 (hTP t.2) (O.φ r) ⟨r, hr, rfl⟩).symm
      exact congrArg Subtype.val (hψSi key)
    obtain ⟨r, hr, s, hs, hrs⟩ := exists_mul_of_mem_centralizer hR.le hR.comm hR.trans
      (by rw [card_fourSet (by norm_num)]; norm_num) (x := (σ : Perm (Fin 16))) hσR
    have hsW : s ∈ fixSub (fourSet 16 ∪ fiveSupp) := by
      intro i hi
      rcases Finset.mem_union.1 hi with hi | hi
      · exact hs i hi
      · have h1 : (σ : Perm (Fin 16)) i = i := σ.2 i hi
        have h2 : r i = i := hRS r hr i hi
        rw [hrs, Perm.mul_apply] at h1
        have h3 : r (s i) = r i := by rw [h1, h2]
        exact r.injective h3
    exact ⟨(⟨r, hr⟩, ⟨s, hsW⟩), Subtype.ext hrs.symm⟩
  have h1 : Nat.card T = Nat.card φT.range := Nat.card_congr (MonoidHom.ofInjective hφTi).toEquiv
  have h2 : Nat.card μ.range = Nat.card R * Nat.card ↥(fixSub (fourSet 16 ∪ fiveSupp)) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hμi).toEquiv, Nat.card_prod]
  rw [card_secR hR, card_fixSub_seven] at h2
  have h3 : (4 : ℕ) * Nat.factorial 7 = 20160 := by decide
  rw [h1, ← h3, ← h2]
  exact Subgroup.card_dvd_of_le hle

end Card

end CFSG.OddStandard.AltStdSec

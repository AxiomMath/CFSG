module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisA2
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisA1
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisMb2
public import CFSG.Quasithin.Background.E1Defs

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem exists_psi_A (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hA : pCore 2 D.Xt ≠ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    ∃ ψ : ↥D.Y1 →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
      ψ.ker = D.E.subgroupOf D.Y1 ∧ Nat.card ↥D.Y1 = 3840 := by
  obtain ⟨hpE, -, ⟨α⟩, -⟩ := D.prop38A_of hC hO hz hA
  refine ⟨α.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 D.Xt)).comp D.piX), ?_, ?_, ?_⟩
  · exact α.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hpE,
      D.piX_mem_Et_iff, mem_subgroupOf]
  · have h1 := (zpowers D.lY).card_eq_card_quotient_mul_card_subgroup
    have h2 := (pCore 2 D.Xt).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr α.toEquiv, nat_card_alternatingGroup, hpE, (D.card_Et_Ft hO hz).1,
      Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h2
    rw [h1, Nat.card_zpowers, D.orderOf_lY]
    change Nat.card D.Xt * 2 ^ 2 = 3840
    rw [h2]
    decide


theorem exists_S5_A (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hA : pCore 2 D.Xt ≠ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) :
    ∃ φ : Y →* Equiv.Perm (Fin 5), Function.Surjective φ ∧ φ.ker = D.E ∧
      ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P ≤ D.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨ψ, hψ, hψker, hY1⟩ := D.exists_psi_A hC hO hz hA
  have hidx := D.index_centralizer_l hO hz
  have hY1n : D.Y1.Normal := normal_of_index_eq_two hidx
  set φ₀ := sylowConj D.Y1 2 with hφ₀
  have hY : Nat.card Y = 7680 := by rw [← D.Y1.card_mul_index, hidx, hY1]
  have hE : Nat.card D.E = 64 := by rw [card_map_of_injective D.toG_injective, SE.card_Esub]
  have hE2 : IsPGroup 2 D.E := D.S.isPGroup'.to_le D.E_le_S
  set E' := D.E.subgroupOf D.Y1 with hE'
  have hE'n : E'.Normal := hψker ▸ ψ.normal_ker
  have hE'2 : IsPGroup 2 E' := hE2.comap_of_injective D.Y1.subtype D.Y1.subtype_injective
  have hE'T : ∀ T : Sylow 2 ↥D.Y1, E' ≤ T := fun T => hE'2.le_sylow_of_normal T
  have h1 : D.E ≤ φ₀.ker := fun e he => mem_ker_sylowConj_of_mem D.Y1 2 (D.E_le_Y1 he)
    fun T => hE'T T (mem_subgroupOf.mpr he)
  have h2 : ∀ y ∈ φ₀.ker, y ∈ D.Y1 → y ∈ D.E := by
    intro y hy hyY
    have hKn : ((φ₀.ker.subgroupOf D.Y1).map ψ).Normal :=
      ((φ₀.normal_ker).subgroupOf D.Y1).map ψ hψ
    rcases hs.eq_bot_or_eq_top_of_normal ((φ₀.ker.subgroupOf D.Y1).map ψ) with hb | ht
    · have hle := (Subgroup.map_eq_bot_iff _).mp hb
      have hm : (⟨y, hyY⟩ : ↥D.Y1) ∈ ψ.ker := hle (mem_subgroupOf.mpr hy)
      rw [hψker, mem_subgroupOf] at hm
      exact hm
    · exfalso
      have hall : ∀ w : ↥D.Y1, (w : Y) ∈ φ₀.ker := by
        intro w
        obtain ⟨k, hk, hkw⟩ : ψ w ∈ (φ₀.ker.subgroupOf D.Y1).map ψ := ht ▸ mem_top _
        have he : k⁻¹ * w ∈ E' := by
          rw [← hψker, MonoidHom.mem_ker, map_mul, map_inv, hkw, inv_mul_cancel]
        have e : (w : Y) = (k : Y) * ((k⁻¹ * w : ↥D.Y1) : Y) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
        rw [e]
        exact mul_mem (mem_subgroupOf.mp hk) (h1 (mem_subgroupOf.mp he))
      obtain ⟨T₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥D.Y1))
      have hTn : (T₀ : Subgroup ↥D.Y1).Normal := ⟨fun t ht w => by
        have h := (mem_ker_sylowConj D.Y1 2).mp (hall w) T₀ t ht
        have e : MulAut.conjNormal (H := D.Y1) (w : Y) t = w * t * w⁻¹ := Subtype.ext rfl
        rwa [e] at h⟩
      have hψT : ((T₀ : Subgroup ↥D.Y1).map ψ).Normal := hTn.map ψ hψ
      rcases hs.eq_bot_or_eq_top_of_normal ((T₀ : Subgroup ↥D.Y1).map ψ) with hb' | ht'
      · have hle : (T₀ : Subgroup ↥D.Y1) ≤ E' := hψker ▸ (Subgroup.map_eq_bot_iff _).mp hb'
        have hc := card_le_of_le hle
        rw [T₀.card_eq_multiplicity, hY1, show (3840 : ℕ) = 2 ^ 8 * 15 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15), hE',
          Nat.card_congr (subgroupOfEquivOfLe D.E_le_Y1).toEquiv, hE] at hc
        exact absurd hc (by norm_num)
      · have hp : IsPGroup 2 ((T₀ : Subgroup ↥D.Y1).map ψ) := T₀.isPGroup'.map ψ
        rw [ht'] at hp
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
        rw [card_top, hA5] at hk
        have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 60)
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have h3 : φ₀.ker ≤ D.E := by
    have hK2 : IsPGroup 2 φ₀.ker := by
      intro g
      have hgE := h2 _ (mul_mem g.2 g.2) (mul_self_mem_of_index_two hidx (g : Y))
      obtain ⟨n, hn⟩ := hE2 ⟨_, hgE⟩
      refine ⟨n + 1, Subtype.ext ?_⟩
      have hn' : ((g : Y) * g) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul, pow_two]
      exact hn'
    have hKS : φ₀.ker ≤ (D.S : Subgroup Y) := hK2.le_sylow_of_normal D.S
    intro k hk
    by_cases hkY : k ∈ D.Y1
    · exact h2 k hk hkY
    · exfalso
      obtain ⟨k₀, rfl⟩ := D.exists_toG (hKS hk)
      have hd : 4 ≤ k₀.d.val := by
        by_contra hd
        exact hkY (D.S1_le_Y1 (D.toG_mem_S1 (by omega)))
      have hcomm : ∀ i : Fin 9, (SE.gen i).d.val < 4 →
          SE.predE (k₀⁻¹ * (SE.gen i)⁻¹ * k₀ * SE.gen i) := by
        intro i hi
        have hsY : D.toG (SE.gen i) ∈ D.Y1 := D.S1_le_Y1 (D.toG_mem_S1 hi)
        have hc1 : (D.toG k₀)⁻¹ * ((D.toG (SE.gen i))⁻¹ * D.toG k₀ * D.toG (SE.gen i)) ∈
            φ₀.ker := by
          refine mul_mem (inv_mem hk) ?_
          have h := (φ₀.normal_ker).conj_mem _ hk (D.toG (SE.gen i))⁻¹
          rwa [inv_inv] at h
        have hc2 : (D.toG k₀)⁻¹ * ((D.toG (SE.gen i))⁻¹ * D.toG k₀ * D.toG (SE.gen i)) ∈
            D.Y1 := by
          rw [show (D.toG k₀)⁻¹ * ((D.toG (SE.gen i))⁻¹ * D.toG k₀ * D.toG (SE.gen i)) =
            (D.toG k₀)⁻¹ * (D.toG (SE.gen i))⁻¹ * (D.toG k₀)⁻¹⁻¹ * D.toG (SE.gen i) by group]
          exact mul_mem (hY1n.conj_mem _ (inv_mem hsY) _) hsY
        have h := h2 _ hc1 hc2
        rw [show (D.toG k₀)⁻¹ * ((D.toG (SE.gen i))⁻¹ * D.toG k₀ * D.toG (SE.gen i)) =
          D.toG (k₀⁻¹ * (SE.gen i)⁻¹ * k₀ * SE.gen i) by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]; group] at h
        exact D.toG_mem_E_iff.mp h
      rcases SE.not_comm_mod_E k₀ hd with h | h
      · exact h (hcomm 6 (by decide))
      · exact h (hcomm 7 (by decide))
  have hker : φ₀.ker = D.E := le_antisymm h3 h1
  have hrange : Nat.card φ₀.range = 120 := by
    rw [← index_ker, hker]
    have h := D.E.card_mul_index
    rw [hE, hY] at h
    omega
  obtain ⟨T₀, hT₀⟩ := (D.isSylowOf_S1_Y1 hO hz).exists_sylow_eq_subgroupOf
  have hT₀card : Nat.card (T₀ : Subgroup ↥D.Y1) = 256 := by
    rw [hT₀, Nat.card_congr (subgroupOfEquivOfLe D.S1_le_Y1).toEquiv, D.card_S1]
  have hT₀idx : (T₀ : Subgroup ↥D.Y1).index = 15 := by
    have h := (T₀ : Subgroup ↥D.Y1).card_mul_index
    rw [hT₀card, hY1] at h
    omega
  have hn := T₀.card_eq_index_normalizer
  have hdvd : (normalizer (T₀ : Set ↥D.Y1)).index ∣ 15 :=
    hT₀idx ▸ index_dvd_of_le le_normalizer
  have hfact : 120 ∣ (Nat.card (Sylow 2 ↥D.Y1)).factorial := by
    rw [← Nat.card_perm, ← hrange]
    exact card_subgroup_dvd_card _
  have hne : Nat.card (Sylow 2 ↥D.Y1) ≠ 15 := by
    intro h15
    obtain ⟨g, hgN, hgP⟩ := exists_mem_normalizer_not_mem_A5 (T₀.mapSurjective hψ)
    rw [← Sylow.coe_coe, Sylow.coe_mapSurjective] at hgN
    rw [Sylow.coe_mapSurjective] at hgP
    obtain ⟨y, rfl⟩ := hψ g
    have key : ∀ w : ↥D.Y1, w ∈ (T₀ : Subgroup ↥D.Y1) ↔
        ψ w ∈ (T₀ : Subgroup ↥D.Y1).map ψ := by
      intro w
      refine ⟨fun hw => ⟨w, hw, rfl⟩, ?_⟩
      rintro ⟨w', hw', he⟩
      have hm : w'⁻¹ * w ∈ E' := by
        rw [← hψker, MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
      have h := mul_mem hw' (hE'T T₀ hm)
      rwa [mul_inv_cancel_left] at h
    have hyN : y ∈ normalizer ((T₀ : Subgroup ↥D.Y1) : Set ↥D.Y1) := by
      rw [mem_normalizer_iff]
      intro h
      rw [key, key, map_mul, map_mul, map_inv]
      exact mem_normalizer_iff.mp hgN (ψ h)
    have hrel := relIndex_mul_index (le_normalizer : (T₀ : Subgroup ↥D.Y1) ≤
      normalizer ((T₀ : Subgroup ↥D.Y1) : Set ↥D.Y1))
    rw [T₀.coe_coe, ← hn, h15, hT₀idx] at hrel
    have hNT : normalizer ((T₀ : Subgroup ↥D.Y1) : Set ↥D.Y1) ≤ T₀ :=
      relIndex_eq_one.mp (by rw [T₀.coe_coe]; omega)
    exact hgP ⟨y, hNT hyN, rfl⟩
  have h5 : Nat.card (Sylow 2 ↥D.Y1) = 5 := by
    rw [hn] at hfact hne ⊢
    have hmem : (normalizer (T₀ : Set ↥D.Y1)).index ∈ Nat.divisors 15 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at hfact
      exact absurd hfact (by decide)
    · rw [h] at hfact
      exact absurd hfact (by decide)
    · exact h
    · exact absurd h hne
  set e : Sylow 2 ↥D.Y1 ≃ Fin 5 := (Finite.equivFin _).trans (finCongr h5)
  refine ⟨(Equiv.permCongrHom e).toMonoidHom.comp φ₀, ?_, ?_, fun P hPn hP2 => ?_⟩
  · rw [← MonoidHom.range_eq_top]
    refine eq_top_of_card_eq _ ?_
    rw [MonoidHom.range_comp, card_map_of_injective (Equiv.permCongrHom e).injective, hrange,
      Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · rw [← hker]
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · rw [← hker]
    exact le_ker_sylowConj_of_normal D.Y1 2 hP2

end GHSylow

end Ybar

end CFSG.ComponentClassification.GHarris

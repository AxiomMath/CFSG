module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23MX
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23ME16
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23MK4

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem mem_M_of_mem_normalizer_k4Sub_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) (m : ↥M2)
    (hm : π m ∈ Subgroup.normalizer (k4Sub : Set (Perm (Fin 7)))) : (m : G) ∈ M := by
  obtain ⟨hbl, -, h16, hUQ, -⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hUle, hVle, -⟩ := inf_L_facts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hVsq := hbl.1.2.2.1
  rw [hUQ] at hVsq
  have hmN := mem_normalizer_inf_L_of_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS m hm
  set W := (pCoreOf 2 L).map (MulAut.conj (m : G) : G →* G) with hWdef
  have hmemW : ∀ w ∈ W, ∃ v ∈ pCoreOf 2 L, w = (m : G) * v * (m : G)⁻¹ := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have hWle : W ≤ T ⊓ L := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hmemW w hw
    exact (Subgroup.mem_normalizer_iff.mp hmN v).mp (hVle hv)
  have hW2 : ∀ g ∈ W, g * g = 1 := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := hmemW g hg
    have h2 : v * v = 1 := by rw [← sq]; exact hVsq.2 v hv
    calc (m : G) * v * (m : G)⁻¹ * ((m : G) * v * (m : G)⁻¹) = (m : G) * (v * v) * (m : G)⁻¹ := by
          group
      _ = 1 := by rw [h2]; group
  have hWc : ∀ g ∈ W, ∀ h ∈ W, g * h = h * g := by
    intro g hg h hh
    obtain ⟨v, hv, rfl⟩ := hmemW g hg
    obtain ⟨w, hw, rfl⟩ := hmemW h hh
    have hvw : v * w = w * v := (Subgroup.mem_centralizer_iff.mp (hVsq.1 hw).2) v hv
    calc (m : G) * v * (m : G)⁻¹ * ((m : G) * w * (m : G)⁻¹) = (m : G) * (v * w) * (m : G)⁻¹ := by
          group
      _ = (m : G) * (w * v) * (m : G)⁻¹ := by rw [hvw]
      _ = (m : G) * w * (m : G)⁻¹ * ((m : G) * v * (m : G)⁻¹) := by group
  have hW16 : Nat.card W = 16 := by
    rw [hWdef, Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective, h16]
  rcases eq_or_eq_of_isElemAbelian_of_le_inf_L_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS hWle
    hW2 hWc hW16 with hWU | hWV
  · exfalso

    have hUN : (m : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 M2 : Set G) :=
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M2)) (M2.inv_mem m.2)
    have hle : pCoreOf 2 L ≤ pCoreOf 2 M2 := by
      intro v hv
      have h1 : (m : G) * v * (m : G)⁻¹ ∈ pCoreOf 2 M2 := hWU ▸ ⟨v, hv, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hUN _).mp h1
      simpa [mul_assoc] using h2
    exact pCoreOf_M2_ne_pCoreOf_L hyp hS h16
      (Subgroup.eq_of_le_of_card_ge hle (by rw [hU16, h16])).symm
  · have hmV : (m : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hWV
    rwa [normalizer_pCoreOf_L_eq hyp h16] at hmV

theorem preE9_le_M_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : preE9 M2 π ≤ M := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_M_of_mem_normalizer_k4Sub_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS m
    (E9Sub_le_normalizer_k4Sub hm)

theorem card_preE9_F4 (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : Nat.card (preE9 M2 π) = 144 := by
  obtain ⟨-, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hle : preE9 M2 π ≤ M2 := Subgroup.map_subtype_le _
  have hUle : pCoreOf 2 M2 ≤ preE9 M2 π := by
    intro u hu
    have huM2 : u ∈ M2 := CFSG.LieType.BorelTits.pCoreOf_le 2 M2 hu
    refine ⟨⟨u, huM2⟩, ?_, rfl⟩
    have hk : (⟨u, huM2⟩ : ↥M2) ∈ π.ker := by
      rw [hS.ker_eq]
      exact hu
    show (⟨u, huM2⟩ : ↥M2) ∈ E9Sub.comap π
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact E9Sub.one_mem
  have hmap : ((preE9 M2 π).subgroupOf M2).map π = E9Sub := by
    show (((E9Sub.comap π).map M2.subtype).comap M2.subtype).map π = E9Sub
    rw [Subgroup.comap_map_eq_self_of_injective M2.subtype_injective, Subgroup.map_comap_eq,
      hS.range_eq]
    exact inf_of_le_right E9Sub_le_alternatingGroup
  have h1 := card_map_mul_card_inf hS.ker_eq hle
  rw [hmap, card_E9Sub, inf_of_le_right hUle, hU16] at h1
  omega

theorem exists_mem_centralizerModO2_of_setting_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) :
    ∃ (x : G) (hx : x ∈ M2), x ∈ M ⊓ centralizerModO2 L ∧ orderOf x = 3 ∧
      π ⟨x, hx⟩ ∈ E9Sub := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn2, -, -, -, -⟩ := setting_K_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  subst hn2
  obtain ⟨-, -, h16, -, -⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hEM := preE9_le_M_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hcard := card_preE9_F4 hQ hyp hM23 hS
  set Φ : ↥(preE9 M2 π) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (actLmodO2 hyp.normal).comp (Subgroup.inclusion hEM) with hΦ
  have hkr := Subgroup.card_ker_mul_card_range Φ
  rw [hcard] at hkr
  have hrange : Nat.card Φ.range ∣ 120 :=
    card_mulAut_LmodO2 hyp.lie ▸ Subgroup.card_subgroup_dvd_card Φ.range
  have h3ker : 3 ∣ Nat.card Φ.ker := by
    by_contra hn
    have hcop : Nat.Coprime 9 (Nat.card Φ.ker) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
    have h9 : 9 ∣ Nat.card Φ.range :=
      hcop.dvd_of_dvd_mul_left ⟨16, by rw [hkr]⟩
    have := h9.trans hrange
    norm_num at this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3ker
  have hyE : ((y : ↥(preE9 M2 π)) : G) ∈ preE9 M2 π := (y : ↥(preE9 M2 π)).2
  obtain ⟨m, hm, hmy⟩ := id hyE
  refine ⟨((y : ↥(preE9 M2 π)) : G), hmy ▸ m.2, ⟨hEM hyE, ?_⟩, ?_, ?_⟩
  · have h1 : actLmodO2 hyp.normal (Subgroup.inclusion hEM y) = 1 := MonoidHom.mem_ker.mp y.2
    have hMV : M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      hyp.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    exact mem_centralizerModO2_of_actLmodO2 hyp.normal hMV h1
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  · have e : (⟨((y : ↥(preE9 M2 π)) : G), hmy ▸ m.2⟩ : ↥M2) = m := Subtype.ext hmy.symm
    rw [e]
    exact hm

end CFSG.Quasithin.H13

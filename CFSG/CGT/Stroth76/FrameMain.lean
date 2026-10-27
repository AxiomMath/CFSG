module

public import CFSG.CGT.Stroth76.PassageLemma1
public import CFSG.CGT.Stroth76.Lemma2Ne
public import CFSG.CGT.Stroth76.Lemma2Frame
public import CFSG.CGT.Stroth76.FrameLemma7
public import CFSG.CGT.Stroth76.Lemma3Final

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76 CFSG.CGT.Stroth77.L4Sylow
  CFSG.OddStandard.HigherRank.YamadaG23

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_S_eq_inf_of_normalizer_le
    (hch : Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (F.A : Set G)) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) = F.S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) < F.S :=
    lt_of_le_of_ne inf_le_left hne
  have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup F.S.isPGroup' hlt
  obtain ⟨g, hg, hgP⟩ := SetLike.exists_of_lt h
  exact hgP ⟨hg.1, hch hg.2⟩

theorem frame_dElt_mem_centralizer_inf {d : Dc}
    (h : dElt F.dA.toConfig d ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) :
    d = 0 :=
  dElt_mem_centralizer_eq_zero F.dA.toConfig h.1

theorem card_eq_of_dvd_of_ne {X : Type*} [Group X] [Finite X] {A C : Subgroup X} (hAC : A ≤ C)
    (hA : Nat.card A = 32) (hC : Nat.card C ∣ 2 ^ 7) (hne : C ≠ A) :
    Nat.card C = 2 ^ 6 ∨ Nat.card C = 2 ^ 7 := by
  have hdvd : Nat.card A ∣ Nat.card C := Subgroup.card_dvd_of_le hAC
  rw [hA] at hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hC
  have hne' : Nat.card C ≠ 32 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hAC (by rw [h, hA])).symm
  rw [hk'] at hdvd hne' ⊢
  interval_cases k <;> simp_all <;> omega

theorem frame_arch76Lemma2_of_ne (h11 : ¬ 2 ^ 11 ∣ Nat.card G)
    (hne : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) ≠ F.A) :
    (F.S : Subgroup G) = (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G)) ⊔
      Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  obtain ⟨O, hON, -, hOodd, hZ⟩ := frame_exists_oddComplement F h11
  haveI := hON
  have hinj := frame_injOn_configN_A F O hOodd
  haveI := frame_configX_normal F O hinj
  have hX := arch76Lemma2_of_ne (F.configN.map (QuotientGroup.mk' O) hinj)
    (frame_odd_orderOf_configX_ρ F O hinj) (frame_centralizer_configX F O hOodd hZ hinj)
    (frame_card_map_centralizerN_dvd F O h11 hOodd) (frame_map_centralizerN_ne F O hOodd hne hinj)
    ((frameSylowN F).mapSurjective (QuotientGroup.mk'_surjective O)) (frame_T_le_sylowX F O hinj)
    (frame_card_sylowX_dvd F O h11 hOodd) (frame_hE_sylowX F O hOodd hinj)
  have hN := frame_sylowN_eq_of_sylowX_eq F O hOodd hinj hX
  set C := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hCdef
  have hAC : F.A ≤ C := frame_A_le_centralizer_inf F
  obtain ⟨hCc, hshape⟩ := frame_arch76Lemma1 F h11 hne
  haveI := hCc
  rcases card_eq_of_dvd_of_ne hAC F.dA.card_eq_32 (frame_card_centralizer_inf_dvd F h11) hne with
    h64 | h128
  ·
    rw [← hN]
    refine (frame_S_eq_inf_of_normalizer_le F ?_).symm
    rcases hshape with ⟨a, b, hCab, ha, hb, -⟩ | ⟨a, b, hCab, ha, hb, -⟩ |
      ⟨c, hCc', hc2, h1, h2, h3⟩ | ⟨c, hCc', hc2, h1, h2, h3⟩
    · exact (false_of_card_of_sq F.dA.toConfig hAC hCc h64
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp))
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp)) ha hb).elim
    · exact (false_of_card_of_sq F.dA.toConfig hAC hCc h64
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp))
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp)) ha hb).elim
    all_goals
      have hcC : c ∈ C := by rw [hCdef, hCc']; exact Subgroup.subset_closure (by simp)
      have hcx : c⁻¹ * F.dA.toConfig.x * c = F.dA.toConfig.x := by
        rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
          (hAC F.dA.toConfig.x_mem), mul_assoc, inv_mul_cancel, mul_one]
      have hcy : c⁻¹ * F.dA.toConfig.y * c = F.dA.toConfig.y := by
        rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
          (hAC F.dA.toConfig.y_mem), mul_assoc, inv_mul_cancel, mul_one]
      rw [hN, hCdef, hCc']
    · exact normalizer_le_normalizer_A_of_shape F.dA.toConfig hcx hcy hc2 (Or.inl ⟨h1, h2, h3⟩)
    · exact normalizer_le_normalizer_A_of_shape F.dA.toConfig hcx hcy hc2 (Or.inr ⟨h1, h2, h3⟩)
  ·
    have hS := frame_card_S_dvd F h11
    have hge := card_sup_dElt_ge F.dA.toConfig (B := C)
      (fun d hd => frame_dElt_mem_centralizer_inf F hd)
    rw [h128] at hge
    have hle : C ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤ (F.S : Subgroup G) :=
      sup_le inf_le_right (le_sup_right.trans F.T_le_S)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    calc Nat.card (F.S : Subgroup G) ≤ 2 ^ 10 := Nat.le_of_dvd (by positivity) hS
      _ = 8 * 2 ^ 7 := by norm_num
      _ ≤ _ := hge

theorem frame_arch76Lemma7 (h11 : ¬ 2 ^ 11 ∣ Nat.card G)
    (hAnn1 : ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    Nat.card (Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) : Subgroup G) = 2 ^ 7 := by
  have hne := frame_centralizer_inf_ne_A F hAnn1
  set C := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hCdef
  have hAC : F.A ≤ C := frame_A_le_centralizer_inf F
  rcases card_eq_of_dvd_of_ne hAC F.dA.card_eq_32 (frame_card_centralizer_inf_dvd F h11) hne with
    h64 | h128
  · exfalso
    obtain ⟨hCc, hshape⟩ := frame_arch76Lemma1 F h11 hne
    haveI := hCc
    have hS := frame_arch76Lemma2_of_ne F h11 hne
    rcases hshape with ⟨a, b, hCab, ha, hb, -⟩ | ⟨a, b, hCab, ha, hb, -⟩ |
      ⟨c, hCc', hc2, h1, h2, h3⟩ | ⟨c, hCc', hc2, h1, h2, h3⟩
    · exact false_of_card_of_sq F.dA.toConfig hAC hCc h64
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp))
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp)) ha hb
    · exact false_of_card_of_sq F.dA.toConfig hAC hCc h64
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp))
        (by rw [hCdef, hCab]; exact Subgroup.subset_closure (by simp)) ha hb
    all_goals
      have hcC : c ∈ C := by rw [hCdef, hCc']; exact Subgroup.subset_closure (by simp)
      have hcx : c⁻¹ * F.dA.toConfig.x * c = F.dA.toConfig.x := by
        rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
          (hAC F.dA.toConfig.x_mem), mul_assoc, inv_mul_cancel, mul_one]
      have hcy : c⁻¹ * F.dA.toConfig.y * c = F.dA.toConfig.y := by
        rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
          (hAC F.dA.toConfig.y_mem), mul_assoc, inv_mul_cancel, mul_one]
      have hS' : (F.S : Subgroup G) = Tsub F.dA.toConfig ⊔ Subgroup.closure {c} := by
        rw [hS, hCc']
        exact closure_cxy_sup_eq F.dA.toConfig hc2
    · exact frame_arch76Lemma7_index_two F hAnn1 hS' hcx hcy hc2 (Or.inl ⟨h1, h2, h3⟩)
    · exact frame_arch76Lemma7_index_two F hAnn1 hS' hcx hcy hc2 (Or.inr ⟨h1, h2, h3⟩)
  · exact h128

theorem frame_arch76Lemma3 (h11 : ¬ 2 ^ 11 ∣ Nat.card G)
    (hAnn1 : ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2))
    (hMason : ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G, Nonempty (↥P ≃* L4Model n) → LitPSLU4S G) :
    LitPSLU4S G := by
  have h7 := frame_arch76Lemma7 F h11 hAnn1
  have hne := frame_centralizer_inf_ne_A F hAnn1
  obtain ⟨hCc, hshape⟩ := frame_arch76Lemma1 F h11 hne
  haveI := hCc
  have hS := frame_arch76Lemma2_of_ne F h11 hne
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := frame_fusion F
  refine arch76Lemma3 F.dA.toConfig hfusE huw hwu hAnn1 F.S hS hCc h7 ?_ hMason
  set C := Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) with hCdef
  have hAC : F.A ≤ C := frame_A_le_centralizer_inf F
  rcases hshape with h | h | ⟨c, hCc', hc2, h1, h2, h3⟩ | ⟨c, hCc', hc2, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr h
  all_goals
    exfalso
    have hcC : c ∈ C := by rw [hCc']; exact Subgroup.subset_closure (by simp)
    have hcx : c⁻¹ * F.dA.toConfig.x * c = F.dA.toConfig.x := by
      rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
        (hAC F.dA.toConfig.x_mem), mul_assoc, inv_mul_cancel, mul_one]
    have hcy : c⁻¹ * F.dA.toConfig.y * c = F.dA.toConfig.y := by
      rw [Subgroup.mul_comm_of_mem_isMulCommutative C (Subgroup.inv_mem _ hcC)
        (hAC F.dA.toConfig.y_mem), mul_assoc, inv_mul_cancel, mul_one]
    have hge := card_sup_dElt_ge F.dA.toConfig (B := C)
      (fun d hd => frame_dElt_mem_centralizer_inf F hd)
    rw [h7] at hge
  · have h9 := card_closure_cxy_sup F.dA.toConfig hcx hcy hc2 (Or.inl ⟨h1, h2, h3⟩)
    rw [← hCc'] at h9
    have : 8 * 2 ^ 7 ≤ 2 ^ 9 := h9 ▸ hge
    norm_num at this
  · have h9 := card_closure_cxy_sup F.dA.toConfig hcx hcy hc2 (Or.inr ⟨h1, h2, h3⟩)
    rw [← hCc'] at h9
    have : 8 * 2 ^ 7 ≤ 2 ^ 9 := h9 ▸ hge
    norm_num at this

end CFSG.CGT.Stroth76

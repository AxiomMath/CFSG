module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_A_le_gen (hm : Sec11Model t L S z K1 K2 T Alt φ) {U : Subgroup G}
    (hQU : secQ K1 K2 ≤ U) (htU : t ∈ U) (haU : φ (Pi.single 2 1) ∈ U) : secA t S L ≤ U := by
  intro y hy
  obtain ⟨v, rfl⟩ := hm.perm.surj y hy
  obtain ⟨w, ⟨hs, h01⟩, h⟩ := sec113_decomp v
  have hwU : φ w ∈ U := hQU ((hm.mem_Q w).2 ⟨hs, h01⟩)
  have he0 : φ (Pi.single 0 1) ∈ U := by
    rw [← hm.t_eq]
    exact htU
  rcases h with h | h | h | h
  · rw [h]
    exact hwU
  · rw [h, hm.perm.mul]
    exact U.mul_mem hwU he0
  · rw [h, hm.perm.mul]
    exact U.mul_mem hwU haU
  · rw [h, hm.perm.mul, hm.perm.mul]
    exact U.mul_mem hwU (U.mul_mem he0 haU)

theorem sec113_eq_of_card {H K : Subgroup (Perm (Fin 6))} (hHK : H ≤ K) {n N : ℕ}
    (hK : Nat.card K = N) (hn : n ≤ Nat.card H) (hN : ∀ d, n ≤ d → d ∣ N → d = N) : H = K := by
  have hdvd : Nat.card H ∣ N := hK ▸ Subgroup.card_dvd_of_le hHK
  have h := hN _ hn hdvd
  exact Subgroup.eq_of_le_of_card_ge hHK (by rw [hK, h])

theorem sec113_gen [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ) {x : G}
    (hxT : x ∈ T) (htC : t ∈ secCTQ K1 K2 T)
    (hcase : (Alt = alternatingGroup (Fin 6) ∧ Sec113TypeA (hm.perm.rho x)) ∨
      (Alt = ⊤ ∧ Sec113TypeS (hm.perm.rho x) ∧
        ∃ r ∈ secCTQ K1 K2 T, hm.perm.rho r = swap 0 1)) :
    T = Subgroup.closure ((secCTQ K1 K2 T : Set G) ∪ (secQ K1 K2 : Set G) ∪
      ({φ (Pi.single 2 1), x} : Set G)) := by
  have hTM := sec113_T_le_M hctx
  have hQT := sec113_Q_le_T hp hctx
  have hAT := sec113_A_le_T hp hctx
  have haT : φ (Pi.single 2 1) ∈ T := hAT (hm.perm.mem _)
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G, U = Subgroup.closure ((secCTQ K1 K2 T : Set G) ∪
      (secQ K1 K2 : Set G) ∪ ({φ (Pi.single 2 1), x} : Set G)) := ⟨_, rfl⟩
  rw [← hU]
  have hCU : ∀ c ∈ secCTQ K1 K2 T, c ∈ U := fun c hc => by
    rw [hU]
    exact Subgroup.subset_closure (Or.inl (Or.inl hc))
  have hQU : secQ K1 K2 ≤ U := fun q hq => by
    rw [hU]
    exact Subgroup.subset_closure (Or.inl (Or.inr hq))
  have haU : φ (Pi.single 2 1) ∈ U := by
    rw [hU]
    exact Subgroup.subset_closure (Or.inr (Set.mem_insert _ _))
  have hxU : x ∈ U := by
    rw [hU]
    exact Subgroup.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hUT : U ≤ T := by
    rw [hU, Subgroup.closure_le]
    intro g hg
    rcases hg with (hg | hg) | hg
    · exact (inf_le_right : secCTQ K1 K2 T ≤ T) hg
    · exact hQT hg
    · rcases hg with rfl | hg
      · exact haT
      · rw [Set.mem_singleton_iff.mp hg]
        exact hxT
  have hAU : secA t S L ≤ U := sec113_A_le_gen hm hQU (hCU t htC) haU
  have hmemH : ∀ σ, σ ∈ (U.subgroupOf T).map (sec113RhoT hm hTM) ↔
      ∃ u ∈ T, u ∈ U ∧ hm.perm.rho u = σ := by
    intro σ
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, u.2, hu, rfl⟩
    · rintro ⟨u, huT, huU, rfl⟩
      exact ⟨⟨u, huT⟩, huU, rfl⟩
  have hHle : (U.subgroupOf T).map (sec113RhoT hm hTM) ≤ sec113Tstar hm hTM :=
    Subgroup.map_le_range _ _
  have hV4 : ∀ s ∈ sec11V4, s ∈ (U.subgroupOf T).map (sec113RhoT hm hTM) := by
    intro s hs
    obtain ⟨q, hq, hact⟩ := hm.Q_act_surj s hs
    exact (hmemH s).2 ⟨q, hQT hq, hQU hq, hm.perm.rho_eq (hTM (hQT hq)) s hact⟩
  have hxH : hm.perm.rho x ∈ (U.subgroupOf T).map (sec113RhoT hm hTM) :=
    (hmemH _).2 ⟨x, hxT, hxU, rfl⟩
  have hHT : (U.subgroupOf T).map (sec113RhoT hm hTM) = sec113Tstar hm hTM := by
    rcases hcase with ⟨hAlt, hty⟩ | ⟨hAlt, hty, r, hrC, hρr⟩
    · have hcard : Nat.card (sec113Tstar hm hTM) = 8 :=
        (sec113_card_Tstar' hm hTM hAT).2 (by rw [hAlt]; exact sec113_alt_ne_top)
      have h5 : (insert (hm.perm.rho x) sec11V4).card ≤
          Nat.card ((U.subgroupOf T).map (sec113RhoT hm hTM)) := by
        refine sec113_card_le _ _ fun σ hσ => ?_
        rcases Finset.mem_insert.1 hσ with rfl | hσ
        · exact hxH
        · exact hV4 σ hσ
      rw [Finset.card_insert_of_notMem (sec113_typeA_not_V4 hty), sec113_cardV4] at h5
      refine sec113_eq_of_card hHle hcard h5 fun d h1 h2 => ?_
      have := Nat.le_of_dvd (by norm_num) h2
      interval_cases d <;> omega
    · have hcard : Nat.card (sec113Tstar hm hTM) = 16 := (sec113_card_Tstar' hm hTM hAT).1 hAlt
      have hr01 : swap (0 : Fin 6) 1 ∈ (U.subgroupOf T).map (sec113RhoT hm hTM) :=
        (hmemH _).2 ⟨r, (inf_le_right : secCTQ K1 K2 T ≤ T) hrC, hCU r hrC, hρr⟩
      have h9 : (insert (hm.perm.rho x)
          (sec11V4 ∪ sec11V4.image (fun s => swap 0 1 * s))).card ≤
          Nat.card ((U.subgroupOf T).map (sec113RhoT hm hTM)) := by
        refine sec113_card_le _ _ fun σ hσ => ?_
        rcases Finset.mem_insert.1 hσ with rfl | hσ
        · exact hxH
        · rcases Finset.mem_union.1 hσ with h | h
          · exact hV4 σ h
          · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 h
            exact Subgroup.mul_mem _ hr01 (hV4 s hs)
      rw [Finset.card_insert_of_notMem (sec113_typeS_not_F8 hty), sec113_cardF8] at h9
      refine sec113_eq_of_card hHle hcard h9 fun d h1 h2 => ?_
      have := Nat.le_of_dvd (by norm_num) h2
      interval_cases d <;> omega
  refine le_antisymm (fun m hmT => ?_) hUT
  have hmem : hm.perm.rho m ∈ (U.subgroupOf T).map (sec113RhoT hm hTM) := by
    rw [hHT]
    exact (mem_sec113Tstar hm hTM).2 ⟨m, hmT, rfl⟩
  obtain ⟨u, huT, huU, hρu⟩ := (hmemH _).1 hmem
  have huM := hTM huT
  have hcT : m * u⁻¹ ∈ T := T.mul_mem hmT (T.inv_mem huT)
  have hρc : hm.perm.rho (m * u⁻¹) = 1 := by
    rw [hm.perm.rho_mul (hTM hmT) ((secM t S L).inv_mem huM), sec113_rho_inv hm huM, hρu]
    exact mul_inv_cancel _
  have hcA : m * u⁻¹ ∈ secA t S L := by
    refine hm.cenTA _ hcT fun a ha => ?_
    have h := (hm.perm.rho_eq_one_iff (hTM hcT)).1 hρc a ha
    calc m * u⁻¹ * a = (m * u⁻¹ * a * (m * u⁻¹)⁻¹) * (m * u⁻¹) := by group
      _ = a * (m * u⁻¹) := by rw [h]
  have hm' : m = (m * u⁻¹) * u := by group
  rw [hm']
  exact U.mul_mem (hAU hcA) huU

end CFSG.OddStandard.SmallF3.Omega

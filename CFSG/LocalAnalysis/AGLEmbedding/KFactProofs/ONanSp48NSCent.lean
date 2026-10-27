module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSLoc
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentData

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin KFactProofs.Sp48 CFSG.PreuniquenessRankFour.Helpers

namespace KFactProofs.Sp48

section Cent

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8} {T : Subgroup Y}
  {y : Y} {ψ : Sp8 ≃* Sp8} {Y₀ : Subgroup Y}

theorem zpowers_slZ_cases {x : Sl28} (hx : x ∈ Subgroup.zpowers slZ) :
    x = 1 ∨ x = slZ ∨ x = slZ⁻¹ := by
  have hT : x ∈ slT := Subgroup.zpowers_le.2 slZ_mem_slT hx
  have h3 : x ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, slZ_pow3, one_zpow]
  exact slT_cube hT h3

omit [K.Normal] in
theorem diag_conj (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8} (hs : s ∈ spE)
    (h1 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk0 slZ)))
    (h2 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk1 slZ))) :
    ∃ n ∈ wrp slD, ψ.symm s = n * spZ12 * n⁻¹ := by
  have hs' : ψ.symm s ∈ spE := psi_symm_spE hψ hs
  obtain ⟨x, hx, y', hy, hxy⟩ := (mem_spE_iff _).1 hs'
  have hemb : emb e s = fpsi e ψ (blk0 x * blk1 y') := by
    rw [← hxy, fpsi_apply, MulEquiv.apply_symm_apply]
  have hx1 : x ≠ 1 := by
    intro hx1
    apply h2
    rw [hemb, hx1, map_one, one_mul]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [map_zpow, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have hy1 : y' ≠ 1 := by
    intro hy1
    apply h1
    rw [hemb, hy1, map_one, mul_one]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
  have hfpf : SpFPF (blk0 x * blk1 y') :=
    SpFPF_blk ((zpowers_slZ_cases hx).resolve_left hx1) ((zpowers_slZ_cases hy).resolve_left hy1)
  have hT0 : blk0 x * blk1 y' ∈ spT0 := hxy ▸ spE_le_spT0 hs'
  have h3 : (blk0 x * blk1 y') ^ 3 = 1 := hxy ▸ ((mem_spE_iff_cube _).1 hs').2
  have hne : blk0 x * blk1 y' ≠ 1 := by
    intro h
    exact hx1 (blk_inj (by rw [h, map_one, map_one, mul_one])).1
  rcases spE_cases hT0 h3 hne with ⟨n, hn, hnz⟩ | ⟨n, hn, hnz⟩
  · exfalso
    rw [hnz] at hfpf
    exact not_SpFPF_spZ1 ((SpFPF_conj n spZ1).1 hfpf)
  · exact ⟨n, hn, hxy.trans hnz⟩

omit [K.Normal] in
theorem outside_aux
    (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8} (hs : s ∈ spE)
    (h1 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk0 slZ)))
    (h2 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk1 slZ))) :
    ¬ Subgroup.centralizer ({emb e s} : Set Y) ≤ Y₀ := by
  intro hle
  obtain ⟨n, hn, hnz⟩ := diag_conj hψ hs h1 h2
  set c : Sp8 := n * spWit * n⁻¹ with hc
  have hcomm : c * (n * spZ12 * n⁻¹) = (n * spZ12 * n⁻¹) * c := by
    calc c * (n * spZ12 * n⁻¹) = n * (spWit * spZ12) * n⁻¹ := by rw [hc]; group
      _ = n * (spZ12 * spWit) * n⁻¹ := by rw [spWit_comm]
      _ = (n * spZ12 * n⁻¹) * c := by rw [hc]; group
  have hsc : s = ψ (n * spZ12 * n⁻¹) := by rw [← hnz, MulEquiv.apply_symm_apply]
  have hcent : emb e (ψ c) ∈ Subgroup.centralizer ({emb e s} : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    rw [hsc, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hcomm]
  have hY₀ : ψ c ∈ Y₀.comap (emb e) := hle hcent
  rw [hcl] at hY₀
  obtain ⟨m, hm, hmc⟩ := hY₀
  have hmc' : m = c := ψ.injective hmc
  have hnM : n ∈ wrp (⊤ : Subgroup Sl28) := wrp_mono le_top hn
  have hcM : c ∈ wrp (⊤ : Subgroup Sl28) := hmc' ▸ hm
  have : spWit ∈ wrp (⊤ : Subgroup Sl28) := by
    have : spWit = n⁻¹ * c * n := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnM) hcM) hnM
  exact spWit_not_mem this

omit [K.Normal] in
theorem involve_aux {θ : Sp8 ≃* Sp8} (hθz : θ spZ1 = spZ12)
    (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8} (hs : s ∈ spE)
    (h1 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk0 slZ)))
    (h2 : emb e s ∉ Subgroup.zpowers (fpsi e ψ (blk1 slZ))) :
    ∃ L : Subgroup Y, L ≤ Subgroup.centralizer ({emb e s} : Set Y) ∧ IsSimpleGroup L ∧
      ⁅L, L⁆ = L ∧ CFSG.AGLEmbedding.IsCaseTwoGroup 3 L ∧ ∃ x ∈ L, x ≠ 1 ∧ x ^ 3 = 1 := by
  obtain ⟨n, hn, hnz⟩ := diag_conj hψ hs h1 h2
  let G : Sl28 →* Y := (fpsi e ψ).comp ((MulAut.conj n).toMonoidHom.comp
    (θ.toMonoidHom.comp blk1))
  have hG : Function.Injective G :=
    (fpsi_injective e ψ).comp ((MulAut.conj n).injective.comp (θ.injective.comp blk1_injective))
  have hsc : emb e s = fpsi e ψ (n * spZ12 * n⁻¹) := by
    rw [← hnz, fpsi_apply, MulEquiv.apply_symm_apply]
  refine ⟨G.range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    have hGx : G x = fpsi e ψ (n * θ (blk1 x) * n⁻¹) := rfl
    rw [hGx, hsc, ← map_mul, ← map_mul]
    congr 1
    calc n * spZ12 * n⁻¹ * (n * θ (blk1 x) * n⁻¹) = n * (spZ12 * θ (blk1 x)) * n⁻¹ := by group
      _ = n * θ (spZ1 * blk1 x) * n⁻¹ := by rw [map_mul, hθz]
      _ = n * θ (blk1 x * spZ1) * n⁻¹ := by
          have hcm : spZ1 * blk1 x = blk1 x * spZ1 := (blk_commute slZ x).eq
          rw [hcm]
      _ = n * (θ (blk1 x) * spZ12) * n⁻¹ := by rw [map_mul, hθz]
      _ = n * θ (blk1 x) * n⁻¹ * (n * spZ12 * n⁻¹) := by group
  · have := sl28_isSimpleGroup
    exact (MonoidHom.ofInjective hG).symm.isSimpleGroup
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, sl28_commutator_top]
  · obtain ⟨d', hd', ⟨eL⟩⟩ := sl28_isCaseTwoGroup
    exact ⟨d', hd', ⟨(MonoidHom.ofInjective hG).symm.trans eL⟩⟩
  · exact ⟨G slZ, ⟨slZ, rfl⟩, fun h => slZ_ne_one (hG (h.trans (map_one G).symm)), by
      rw [← map_pow, slZ_pow3, map_one]⟩

end Cent

section P

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {e : K ≃* Sp8} {T : Subgroup Y} {y : Y}

theorem Sp48Setup.pRank_T_le (S : Sp48Setup e T y) : Open.pRank 3 T ≤ 3 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) (fun F hFT hF => ?_)
  have hHT : T ⊓ K ≤ T := inf_le_left
  have hidxT : (T ⊓ K).relIndex T = 3 := by
    have h1 := Subgroup.card_mul_index ((T ⊓ K).subgroupOf T)
    have h2 : Nat.card ((T ⊓ K).subgroupOf T) = 3 ^ 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv, S.card_inf_K]
    rw [h2, S.card_T] at h1
    show ((T ⊓ K).subgroupOf T).index = 3
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 4)
      (h1.trans (by norm_num : 3 ^ 5 = 3 ^ 4 * 3))
  have hFcard := Subgroup.card_mul_index ((T ⊓ K).subgroupOf F)
  have hc1 : Nat.card ((T ⊓ K).subgroupOf F) = Nat.card (T ⊓ K ⊓ F : Subgroup Y) := by
    rw [← Subgroup.subgroupOf_map_subtype (T ⊓ K) F,
      Subgroup.card_map_of_injective F.subtype_injective]
  have hle : T ⊓ K ⊓ F ≤ spE.map (emb e) := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := S.inf_K ht.1.1 ht.1.2
    refine ⟨k, (mem_spE_iff_cube k).2 ⟨hk, ?_⟩, rfl⟩
    apply emb_injective e
    rw [map_pow, map_one]
    exact hF.2 _ ht.2
  have hc2 : Nat.card (T ⊓ K ⊓ F : Subgroup Y) ≤ 9 := by
    calc Nat.card (T ⊓ K ⊓ F : Subgroup Y) ≤ Nat.card (spE.map (emb e)) :=
          Subgroup.card_le_of_le hle
      _ = 9 := by rw [Subgroup.card_map_of_injective (emb_injective e), card_spE]
  have hidx : ((T ⊓ K).subgroupOf F).index ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right hFT (by rw [hidxT]; norm_num :
      (T ⊓ K).relIndex T ≠ 0)
    rwa [hidxT] at this
  rw [hc1] at hFcard
  calc Nat.card F = Nat.card (T ⊓ K ⊓ F : Subgroup Y) * ((T ⊓ K).subgroupOf F).index :=
        hFcard.symm
    _ ≤ 9 * 3 := Nat.mul_le_mul hc2 hidx
    _ = 3 ^ 3 := by norm_num

end P

end KFactProofs.Sp48

theorem kFactSp48NonsolvCent : KFactSp48NonsolvCent := by
  intro Y _ _ K d hd hKn he hC T Y₀ h3 hW hY₀ hns
  obtain ⟨e⟩ := he
  obtain ⟨⟨eK⟩, hcardK⟩ := exists_equiv_sp8 hd e
  have hcardS : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardK]
    exact Nat.card_congr eK.symm.toEquiv
  have hsimple : IsSimpleGroup Sp8 := isSimple_sp8_of_index hd e eK
  have : K.Normal := hKn
  obtain ⟨e', y, S⟩ := exists_setup K eK hC hcardS T h3
  have hNE := S.normalizer_E_le h3 hW
  obtain ⟨θ, ψ, hθT, hθz, hψ, hcl⟩ := nonsolv_classify S hC hcardS hsimple hNE hY₀ hns
  have hoz : orderOf slZ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime slZ_pow3 slZ_ne_one
  refine ⟨fpsi e' ψ (blk0 slZ), fpsi e' ψ (blk1 slZ), fpsi e' ψ swp, ?_⟩
  refine
  { z₁_mem := ?_
    z₂_mem := ?_
    order₁ := ?_
    order₂ := ?_
    inf_eq_bot := ?_
    σ_mem := fpsi_mem_Y₀ hcl swp_mem_wrp_top
    σ_norm := S.emb_mem_normalizer_T (psi_wrp_slD hψ (swp_mem_wrp slD))
    σ₁ := ?_
    σ₂ := ?_
    outside := fun d hd h1 h2 => ?_
    involve := fun d hd h1 h2 => ?_
    pRank_le := S.pRank_T_le }
  · rw [S.center_T]
    exact ⟨ψ (blk0 slZ), psi_spE hψ blk0_slZ_mem_spE, rfl⟩
  · rw [S.center_T]
    exact ⟨ψ (blk1 slZ), psi_spE hψ blk1_slZ_mem_spE, rfl⟩
  · rw [orderOf_injective (fpsi e' ψ) (fpsi_injective e' ψ),
      orderOf_injective blk0 blk0_injective, hoz]
  · rw [orderOf_injective (fpsi e' ψ) (fpsi_injective e' ψ),
      orderOf_injective blk1 blk1_injective, hoz]
  · rw [eq_bot_iff]
    rintro t ⟨ht1, ht2⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht2
    rw [Subgroup.mem_bot]
    have h1 : fpsi e' ψ (blk0 (slZ ^ m)) = fpsi e' ψ (blk1 (slZ ^ n)) := by
      rw [map_zpow, map_zpow, map_zpow, map_zpow]
      exact hn.symm
    have h2 := fpsi_injective e' ψ h1
    have h3 : blk0 (slZ ^ m) * blk1 1 = blk0 1 * blk1 (slZ ^ n) := by simpa using h2
    have h4 := (blk_inj h3).1
    rw [← map_zpow, ← map_zpow, h4]
    simp
  · rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk0]
    exact Subgroup.mem_zpowers _
  · rw [← map_inv, ← map_mul, ← map_mul, swp_conj_blk1]
    exact Subgroup.mem_zpowers _
  · rw [S.center_T] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    exact outside_aux hcl hψ hs h1 h2
  · rw [S.center_T] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    exact involve_aux hθz hψ hs h1 h2

end CFSG.AGLEmbedding

module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Bar
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Q8Prod

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm6.M12Facts

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem asc03Data_of_stage1M12 (hz : IsCentralInvolution z) (h : Stage1M12 G z S)
    (hO : pPrimeCore 2 ↥(Cen z) = ⊥) : Stage12.Asc03Data G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, B, hAB, hAq, hBq, hAn⟩ := h.W_shape
  obtain ⟨A₃, hA₃, -, hOres, hFst, hcomm, hfix⟩ := h.L_shape
  obtain ⟨hWn, ⟨eq⟩⟩ := h.quot
  obtain ⟨U, hUS, hU4, hUn, hzU, hUW, huniq, hAut⟩ := h.four_group
  have hz2 : orderOf z = 2 := hz.1
  have hz1 : z ≠ 1 := by
    intro e; rw [e, orderOf_one] at hz2; omega
  have hinj : Function.Injective (toBar z) := by
    rw [← MonoidHom.ker_eq_bot_iff, show (toBar z).ker = pPrimeCore 2 ↥(Cen z) from
      QuotientGroup.ker_mk' _, hO]
  let e : ↥(Cen z) ≃* CentralizerBar z := MulEquiv.ofBijective (toBar z) ⟨hinj, toBar_surj z⟩
  have he : ∀ c : ↥(Cen z), e c = toBar z c := fun c => rfl
  obtain ⟨cA, hA8'⟩ := q8Like_of_equiv hAq.some
  obtain ⟨cB, hB8'⟩ := q8Like_of_equiv hBq.some
  have hAcard : Nat.card ↥A = 8 := by rw [Nat.card_congr hAq.some.toEquiv]; exact card_Q8
  have hBcard : Nat.card ↥B = 8 := by rw [Nat.card_congr hBq.some.toEquiv]; exact card_Q8
  have hext := isExtraspecial_sup_q8 hA8' hB8' hAB.2.1 hAB.2.2 hAcard
  have hWcard : Nat.card ↥(WBar z) = 32 := by
    have := card_sup_mul_card_inf hAB.2.1
    rw [hAB.1, hAB.2.2, hAcard, hBcard] at this
    omega
  have hWpg : IsPGroup 2 ↥(WBar z) := IsPGroup.of_card (n := 5) (by rw [hWcard]; norm_num)
  have hpc : pCore 2 (CentralizerBar z) = WBar z := by
    apply le_antisymm
    · calc pCore 2 (CentralizerBar z) ≤ fittingSubgroup (CentralizerBar z) := pCore_le_fitting _ 2
        _ ≤ generalizedFitting (CentralizerBar z) := le_sup_left
        _ = WBar z := hFst
    · exact le_sSup ⟨hWn, hWpg⟩
  have hQ : (pCore 2 ↥(Cen z)).map e.toMonoidHom = WBar z := by
    rw [pCore_map_iso 2 e, hpc]
  have hQcard : Nat.card ↥(pCore 2 ↥(Cen z)) = 32 := by
    have hQ' : (pCore 2 ↥(Cen z)).map (e : ↥(Cen z) →* CentralizerBar z) = WBar z := hQ
    rw [Nat.card_congr (MulEquiv.subgroupMap e (pCore 2 ↥(Cen z))).toEquiv, hQ', hWcard]
  let eQ : ↥(pCore 2 ↥(Cen z)) ≃* ↥(A ⊔ B) :=
    ((MulEquiv.subgroupMap e (pCore 2 ↥(Cen z))).trans (MulEquiv.subgroupCongr hQ)).trans
      (MulEquiv.subgroupCongr hAB.1.symm)
  have hext' : CFSG.IsExtraspecial 2 ↥(pCore 2 ↥(Cen z)) :=
    CFSG.GH74.M12.Hyp.isExtraspecial_of_mulEquiv eQ.symm hext
  have hquot : Nonempty (↥(Cen z) ⧸ pCore 2 ↥(Cen z) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.congr (pCore 2 ↥(Cen z)) (WBar z) e hQ).trans eq⟩
  have hnwc : ∃ g : G, g * z * g⁻¹ ≠ z ∧ ∃ q ∈ pCore 2 ↥(Cen z), (q : G) = g * z * g⁻¹ := by
    obtain ⟨g, hgN, hgz⟩ := exists_move_of_autOrd hU4 hzU hz1 hAut
    have hgU : g * z * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hgN z).1 hzU
    have hgW : g * z * g⁻¹ ∈ WC z := hUW hgU
    obtain ⟨c, -, hcg⟩ := hgW
    have hcW : (c : G) ∈ WC z := by rw [show (c : G) = g * z * g⁻¹ from hcg]; exact hUW hgU
    have h1 : toBar z c ∈ WBar z := (mem_WC_iff z c).1 hcW
    rw [← hQ] at h1
    obtain ⟨q, hq, hqc⟩ := h1
    have : q = c := e.injective hqc
    exact ⟨g, hgz, c, this ▸ hq, hcg⟩
  have hcard_C : Nat.card ↥(Cen z) = 192 := by
    have h1 : Nat.card (CentralizerBar z) = 192 := by
      have := Subgroup.card_mul_index (WBar z)
      rw [hWcard, Subgroup.index_eq_card, Nat.card_congr eq.toEquiv] at this
      rw [← this]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [Nat.card_congr e.toEquiv]; exact h1
  have hcentX : ∀ X : Sylow 3 ↥(Cen z), ∀ q ∈ pCore 2 ↥(Cen z), (∀ x ∈ X, x * q = q * x) →
      (q : G) ∈ zpowers z := by
    intro X q hq hXq
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨A₃c, hA₃cdef⟩ : ∃ K : Subgroup ↥(Cen z),
        K = A₃.map (e.symm : CentralizerBar z →* ↥(Cen z)) := ⟨_, rfl⟩
    have hA₃card : Nat.card ↥A₃ = 3 := by
      rw [Nat.card_congr hA₃.some.toEquiv]; simp [Nat.card_eq_fintype_card]
    have hA₃c : Nat.card ↥A₃c = 3 := by
      rw [hA₃cdef, ← Nat.card_congr (MulEquiv.subgroupMap e.symm A₃).toEquiv]; exact hA₃card
    have hmemA : ∀ a : ↥(Cen z), a ∈ A₃c ↔ e a ∈ A₃ := by
      intro a
      rw [hA₃cdef, Subgroup.mem_map]
      constructor
      · rintro ⟨a', ha', rfl⟩; simpa using ha'
      · intro hh; exact ⟨e a, hh, by simp⟩
    have hidx : ¬ 3 ∣ A₃c.index := by
      have := Subgroup.card_mul_index A₃c
      rw [hA₃c, hcard_C] at this
      omega
    have hP3 : IsPGroup 3 ↥A₃c := IsPGroup.of_card (n := 1) (by rw [hA₃c]; norm_num)
    let Y : Sylow 3 ↥(Cen z) := hP3.toSylow hidx
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Cen z) Y X
    have hXY : ∀ a ∈ A₃c, g * a * g⁻¹ ∈ X := by
      intro a ha
      have hmem : g * a * g⁻¹ ∈ ((g • Y : Sylow 3 ↥(Cen z)) : Subgroup ↥(Cen z)) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) _ ha
      rw [hg] at hmem
      exact hmem
    have hq' : g⁻¹ * q * g ∈ pCore 2 ↥(Cen z) := by
      have := (pCore_normal (p := 2) (G := ↥(Cen z))).conj_mem q hq g⁻¹
      simpa using this
    have hq'W : e (g⁻¹ * q * g) ∈ WBar z := by
      rw [← hQ]; exact ⟨_, hq', rfl⟩
    have hq'c : ∀ a ∈ A₃, a * e (g⁻¹ * q * g) = e (g⁻¹ * q * g) * a := by
      intro a ha
      have ha0 : e.symm a ∈ A₃c := (hmemA _).2 (by simpa using ha)
      have h1 := hXq _ (hXY _ ha0)
      have h2 : e.symm a * (g⁻¹ * q * g) = (g⁻¹ * q * g) * e.symm a := by
        have h3 : g * (e.symm a) * g⁻¹ * q = q * (g * (e.symm a) * g⁻¹) := h1
        calc e.symm a * (g⁻¹ * q * g) = g⁻¹ * (g * (e.symm a) * g⁻¹ * q) * g := by group
          _ = g⁻¹ * (q * (g * (e.symm a) * g⁻¹)) * g := by rw [h3]
          _ = (g⁻¹ * q * g) * e.symm a := by group
      have h4 := congrArg e h2
      rw [map_mul, map_mul] at h4
      simpa using h4
    have hfx := hfix _ hq'W hq'c
    rw [barOf_zpowers z] at hfx
    obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).1 hfx
    have hzt : ∀ c : ↥(Cen z), c * (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) = ⟨z, z_mem_Cen z⟩ * c := fun c =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 c.2 z (Set.mem_singleton z)).symm
    have hq'eq : g⁻¹ * q * g = (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) ^ n := by
      apply e.injective
      rw [← hn, map_zpow, he]
    have hqeq : q = (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) ^ n := by
      have h5 : q = g * (g⁻¹ * q * g) * g⁻¹ := by group
      rw [h5, hq'eq]
      have hcomm' : g * (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) = (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) * g :=
        hzt g
      have : g * ((⟨z, z_mem_Cen z⟩ : ↥(Cen z)) ^ n) * g⁻¹ = (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) ^ n := by
        have hc : Commute g (⟨z, z_mem_Cen z⟩ : ↥(Cen z)) := hcomm'
        exact (hc.zpow_right n).mul_inv_cancel
      exact this
    rw [hqeq]
    refine ⟨n, ?_⟩
    simp
  let K : Subgroup ↥(Cen z) := A.comap (e : ↥(Cen z) →* CentralizerBar z)
  have hKle : K ≤ pCore 2 ↥(Cen z) := by
    intro k hk
    have h1 : e k ∈ WBar z := by rw [← hAB.1]; exact Subgroup.mem_sup_left hk
    rw [← hQ] at h1
    obtain ⟨q, hq, hqk⟩ := h1
    have : q = k := e.injective hqk
    exact this ▸ hq
  have hKmap : K.map (e : ↥(Cen z) →* CentralizerBar z) = A :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective A
  have hKq : Nonempty (↥K ≃* QuaternionGroup 2) :=
    ⟨((MulEquiv.subgroupMap e K).trans (MulEquiv.subgroupCongr hKmap)).trans hAq.some⟩
  have hKn : K.Normal := hAn.comap (e : ↥(Cen z) →* CentralizerBar z)
  exact ⟨z, hz, ⟨hz2, hQcard, hext', hquot, hcentX, hnwc⟩, K, ⟨hKle, hKq⟩, hKn⟩

end CFSG.GH74.GLS.Stage1.Thm6.Prod

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Frat24
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Fusion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Good

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

theorem lemma2524 : Lemma2524 := by
  intro G _ _ T M hs N t zK h hfr
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have h254 := h.facts254
  have h258 := h.facts258
  have hsimple := h258.simple
  obtain ⟨D⟩ := exists_a6Datum N hKH h258 h.concl2521
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have : Fact (IsPGroup 2 ↥N.SC) := ⟨hS2.to_le N.SC_le_S⟩
  have hSC2 : ∀ a ∈ N.SC, a * a = 1 := fun a ha =>
    congrArg Subtype.val (sq_eq_one_of_frattini_eq_bot hfr ⟨a, ha⟩)
  have hΦz : D.Φ N.z = zb := D.Φ_z hK0 h254 hzS
  have hΦzK : D.Φ zK = zb := (D.Φ_zK hK0 hf).trans hΦz
  have hxzK : N.x⁻¹ * zK * N.x = zK := D.x_zK hK0 hKH h254 hsimple hf hΦzK hSC2
  have hzKz : N.z = zK := (h.concl2513.2.1 hxzK).1
  have hSKx : N.SK ⊓ CFSG.conjugate N.SC N.x = ⊥ :=
    N.SK_inf_conjugate_SC hK0 hKH h254 h258 hf hzKz
  obtain ⟨E₁, E₂, hE₁K, hE₂K, hE₁4, hE₂4, hne12, hall12, hUsets, hstars⟩ := h.concl2523
  have hstar₁ := (hstars E₁ (Set.mem_insert _ _)).1
  obtain ⟨hzKE, e, heE, he1, hezK, hrefl, he2, hEel⟩ :=
    D.four_subgroup_data hK0 hsimple hf hΦzK hE₁K hE₁4
  have heSK : e ∈ N.SK := hE₁K heE
  have heS : e ∈ N.S := N.SK_le_S heSK
  have heH : e ∈ N.H := N.S_le_H heS
  have hzKS : zK ∈ N.S := N.SK_le_S (hE₁K hzKE)
  have hzKcent : ∀ a ∈ N.S, a * zK = zK * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hf.zK_mem_center.2 a ha
  set ε : G := N.x⁻¹ * e * N.x with hε
  have hεS : ε ∈ N.S := N.x_conj_S' heS
  have hεH : ε ∈ N.H := N.S_le_H hεS
  have hε2 : ε * ε = 1 := by
    have : ε * ε = N.x⁻¹ * (e * e) * N.x := by rw [hε]; group
    rw [this, he2]; group
  obtain ⟨k, hkK, hke⟩ := D.exists_conj_zK hK0 hsimple hf hΦzK heSK he1 he2
  have hgood : D.Φ ε ≠ 1 ∧ (D.Φ ε ∈ A6Models.psl29 ∨ D.Φ ε ∈ s6) := by
    have hg : (k⁻¹ * N.x)⁻¹ * N.z * (k⁻¹ * N.x) ∈ N.S := by
      have : (k⁻¹ * N.x)⁻¹ * N.z * (k⁻¹ * N.x) = ε := by
        rw [hzKz, hε, ← hke]; group
      rw [this]; exact hεS
    have h' := D.good_of_conj h.toLv2522.toLv2521 hg
    have : (k⁻¹ * N.x)⁻¹ * N.z * (k⁻¹ * N.x) = ε := by
      rw [hzKz, hε, ← hke]; group
    rwa [this] at h'
  have hgP : D.Φ ε ∈ P0 := D.S_mem ε hεS
  have hg2 : D.Φ ε * D.Φ ε = 1 := by
    rw [← D.mul ε hεH ε hεH, hε2, D.Φ_one]
  have hzKH : zK ∈ N.H := N.S_le_H hzKS
  have hxxS : ∀ s ∈ N.S, N.x⁻¹ * s * N.x ∈ N.S := fun s hs' => N.x_conj_S' hs'
  by_cases hgE4 : InE4 (D.Φ ε)
  ·
    exfalso
    have hεcomm : ∀ a ∈ N.SK, ε * a = a * ε := by
      intro a ha
      have haK : a ∈ N.K := ha.2
      have hεa : ε * a * ε⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp (hKH hεH) a).mp haK
      have hΦ : D.Φ (ε * a * ε⁻¹) = D.Φ a := by
        rw [D.Φ_conj hεH (N.K_le_H haK)]
        have hc : D.Φ ε * D.Φ a = D.Φ a * D.Φ ε :=
          hgE4.2 (D.Φ a) (D.S_mem a (N.SK_le_S ha)) (D.K_mem a haK)
        rw [hc]
        group
      have h1 : ε * a * ε⁻¹ = a := D.inj_K hsimple hεa haK hΦ
      calc ε * a = (ε * a * ε⁻¹) * ε := by group
        _ = a * ε := by rw [h1]
    have hzKcomm : ∀ a ∈ N.SK, zK * a = a * zK := fun a ha => (hzKcent a (N.SK_le_S ha)).symm
    have hEx : ∀ e' ∈ E₁, ∀ a ∈ N.SK,
        (N.x⁻¹ * e' * N.x) * a = a * (N.x⁻¹ * e' * N.x) := by
      intro e' he' a ha
      rcases hEel e' he' with h1 | h1 | h1 | h1
      · rw [h1]
        simp
      · rw [h1, hxzK]
        exact hzKcomm a ha
      · rw [h1]
        exact hεcomm a ha
      · have e1 : N.x⁻¹ * e' * N.x = ε * zK := by
          rw [h1, hε]
          calc N.x⁻¹ * (e * zK) * N.x = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * zK * N.x) := by group
            _ = (N.x⁻¹ * e * N.x) * zK := by rw [hxzK]
        rw [e1]
        calc ε * zK * a = ε * (zK * a) := by group
          _ = ε * (a * zK) := by rw [hzKcomm a ha]
          _ = (ε * a) * zK := by group
          _ = (a * ε) * zK := by rw [hεcomm a ha]
          _ = a * (ε * zK) := by group
    have hqcs : ∀ a ∈ N.SK, N.x * a * N.x⁻¹ ∈ N.CS E₁ := by
      intro a ha
      rw [Notation25.mem_CS_iff]
      refine ⟨N.x_conj_S (N.SK_le_S ha), fun e' he' => ?_⟩
      have h1 := hEx e' he' a ha
      calc e' * (N.x * a * N.x⁻¹) = N.x * ((N.x⁻¹ * e' * N.x) * a) * N.x⁻¹ := by group
        _ = N.x * (a * (N.x⁻¹ * e' * N.x)) * N.x⁻¹ := by rw [h1]
        _ = (N.x * a * N.x⁻¹) * e' := by group
    have hkey : ∀ q ∈ N.CS E₁, D.Φ q * D.Φ e = D.Φ e * D.Φ q ∧ D.Φ q * zb = zb * D.Φ q := by
      intro q hq
      obtain ⟨hqS, hqE⟩ := Notation25.mem_CS_iff.mp hq
      have hqH := N.S_le_H hqS
      constructor
      · rw [← D.mul q hqH e heH, ← D.mul e heH q hqH, hqE e heE]
      · rw [← hΦzK, ← D.mul q hqH zK hzKH, ← D.mul zK hzKH q hqH, hqE zK hzKE]
    have hcommΦ : ∀ a ∈ N.SK, ∀ b ∈ N.SK, D.Φ (N.x * a * N.x⁻¹) * D.Φ (N.x * b * N.x⁻¹) =
        D.Φ (N.x * b * N.x⁻¹) * D.Φ (N.x * a * N.x⁻¹) := by
      intro a ha b hb
      have hqa := hqcs a ha
      have hqb := hqcs b hb
      exact klein_cent_comm_mem hrefl (D.S_mem _ (Notation25.mem_CS_iff.mp hqa).1)
        (hkey _ hqa).1 (hkey _ hqa).2 (D.S_mem _ (Notation25.mem_CS_iff.mp hqb).1)
        (hkey _ hqb).1 (hkey _ hqb).2
    obtain ⟨d, d', hdP, hdpsl, hd'P, hd'psl, hdd'⟩ := exists_noncomm_D
    obtain ⟨a, haSK, haΦ⟩ := D.exists_mem_SK hKH h254 hsimple hdP hdpsl
    obtain ⟨b, hbSK, hbΦ⟩ := D.exists_mem_SK hKH h254 hsimple hd'P hd'psl
    apply hdd'
    have habcomm : a * b = b * a := by
      have hqaS : N.x * a * N.x⁻¹ ∈ N.S := N.x_conj_S (N.SK_le_S haSK)
      have hqbS : N.x * b * N.x⁻¹ ∈ N.S := N.x_conj_S (N.SK_le_S hbSK)
      have hΦeq : D.Φ ((N.x * a * N.x⁻¹) * (N.x * b * N.x⁻¹)) =
          D.Φ ((N.x * b * N.x⁻¹) * (N.x * a * N.x⁻¹)) := by
        rw [D.mul _ (N.S_le_H hqaS) _ (N.S_le_H hqbS), D.mul _ (N.S_le_H hqbS) _ (N.S_le_H hqaS)]
        exact hcommΦ a haSK b hbSK
      have hmem := D.inv_mul_mem_SC hK0 (N.S.mul_mem hqaS hqbS) (N.S.mul_mem hqbS hqaS) hΦeq
      have hw : (a * b)⁻¹ * (b * a) ∈ N.SK ⊓ CFSG.conjugate N.SC N.x := by
        refine ⟨N.SK.mul_mem (N.SK.inv_mem (N.SK.mul_mem haSK hbSK)) (N.SK.mul_mem hbSK haSK),
          mem_conjugate_iff.mpr ?_⟩
        have e : N.x * ((a * b)⁻¹ * (b * a)) * N.x⁻¹ =
            ((N.x * a * N.x⁻¹) * (N.x * b * N.x⁻¹))⁻¹ *
              ((N.x * b * N.x⁻¹) * (N.x * a * N.x⁻¹)) := by group
        rw [e]
        exact hmem
      rw [hSKx, Subgroup.mem_bot] at hw
      calc a * b = a * b * ((a * b)⁻¹ * (b * a)) := by rw [hw, mul_one]
        _ = b * a := by group
    have := congrArg D.Φ habcomm
    rw [D.mul a (N.K_le_H haSK.2) b (N.K_le_H hbSK.2), D.mul b (N.K_le_H hbSK.2) a (N.K_le_H haSK.2),
      haΦ, hbΦ] at this
    exact this
  ·
    obtain ⟨r', hr', hr'c⟩ := refl_of_good hgP hgood.1 hg2 hgood.2 hgE4
    obtain ⟨k', hk'SK, hk'Φ⟩ := D.exists_mem_SK hKH h254 hsimple hr'.1 hr'.2.1
    have hk'K : k' ∈ N.K := hk'SK.2
    have hk'H : k' ∈ N.H := N.K_le_H hk'K
    have hk'1 : k' ≠ 1 := by
      intro h1
      apply hr'.2.2.1
      rw [← hk'Φ, h1, D.Φ_one]
    have hk'zK : zK ≠ k' := by
      intro h1
      apply hr'.2.2.2.1
      rw [← hk'Φ, ← h1, hΦzK]
    have hk'2 : k' * k' = 1 := by
      apply D.inj_K hsimple (N.K.mul_mem hk'K hk'K) N.K.one_mem
      rw [D.mul k' hk'H k' hk'H, hk'Φ, hr'.2.2.2.2, D.Φ_one]
    obtain ⟨E', hE'mem, hE'4⟩ := exists_four_subgroup (D.zK_ne_one hΦzK) hk'1 hk'zK hf.zK_sq hk'2
      (hzKcent k' (N.SK_le_S hk'SK)).symm
    have hE'SK : E' ≤ N.SK := by
      intro x hx
      rcases (hE'mem x).1 hx with h1 | h1 | h1 | h1
      · rw [h1]; exact N.SK.one_mem
      · rw [h1]; exact hf.zK_mem_SK hK0
      · rw [h1]; exact hk'SK
      · rw [h1]; exact N.SK.mul_mem (hf.zK_mem_SK hK0) hk'SK
    obtain ⟨s, hsS, hEs⟩ := a6FourSubgroupFusion G T M hs N hKH h.concl2521 E₁ E' hE₁K hE₁4
      hE'SK hE'4
    have hQs : CFSG.conjugate (N.CS E₁) s = N.CS E' := by
      ext b
      rw [mem_conjugate_iff, Notation25.mem_CS_iff, Notation25.mem_CS_iff]
      constructor
      · rintro ⟨hsb, hcomm⟩
        refine ⟨?_, fun c hc => ?_⟩
        · have := N.S.mul_mem (N.S.mul_mem (N.S.inv_mem hsS) hsb) hsS
          simpa [mul_assoc] using this
        · rw [hEs, mem_conjugate_iff] at hc
          have := hcomm _ hc
          calc c * b = s⁻¹ * ((s * c * s⁻¹) * (s * b * s⁻¹)) * s := by group
            _ = s⁻¹ * ((s * b * s⁻¹) * (s * c * s⁻¹)) * s := by rw [this]
            _ = b * c := by group
      · rintro ⟨hbS, hcomm⟩
        refine ⟨N.S.mul_mem (N.S.mul_mem hsS hbS) (N.S.inv_mem hsS), fun c hc => ?_⟩
        have hc' : s⁻¹ * c * s ∈ E' := by
          rw [hEs, mem_conjugate_iff]
          have : s * (s⁻¹ * c * s) * s⁻¹ = c := by group
          rw [this]
          exact hc
        have := hcomm _ hc'
        calc c * (s * b * s⁻¹) = s * ((s⁻¹ * c * s) * b) * s⁻¹ := by group
          _ = s * (b * (s⁻¹ * c * s)) * s⁻¹ := by rw [this]
          _ = (s * b * s⁻¹) * c := by group
    have hQx : CFSG.conjugate (N.CS E₁) N.x ≤ N.CS E' := by
      intro b hb
      rw [mem_conjugate_iff, Notation25.mem_CS_iff] at hb
      obtain ⟨hxbS, hxbE⟩ := hb
      have hbS : b ∈ N.S := by
        have := N.x_conj_S' hxbS
        simpa [mul_assoc] using this
      have hbH : b ∈ N.H := N.S_le_H hbS
      have hbε : ε * b = b * ε := by
        have := hxbE e heE
        calc ε * b = N.x⁻¹ * (e * (N.x * b * N.x⁻¹)) * N.x := by rw [hε]; group
          _ = N.x⁻¹ * ((N.x * b * N.x⁻¹) * e) * N.x := by rw [this]
          _ = b * ε := by rw [hε]; group
      have hΦb : D.Φ b * D.Φ ε = D.Φ ε * D.Φ b := by
        rw [← D.mul b hbH ε hεH, ← D.mul ε hεH b hbH, hbε]
      have hΦr' : D.Φ b * r' = r' * D.Φ b := hr'c (D.Φ b) (D.S_mem b hbS) hΦb
      rw [Notation25.mem_CS_iff]
      refine ⟨hbS, fun c hc => ?_⟩
      have hbzK : zK * b = b * zK := (hzKcent b hbS).symm
      have hbk' : k' * b = b * k' := by
        have hbk'K : b * k' * b⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp (hKH hbH) k').mp hk'K
        have : b * k' * b⁻¹ = k' := by
          apply D.inj_K hsimple hbk'K hk'K
          rw [D.Φ_conj hbH hk'H, hk'Φ, hΦr']
          group
        calc k' * b = (b * k' * b⁻¹) * b := by rw [this]
          _ = b * k' := by group
      rcases (hE'mem c).1 hc with h1 | h1 | h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hbzK
      · rw [h1]; exact hbk'
      · rw [h1]
        calc zK * k' * b = zK * (k' * b) := by group
          _ = zK * (b * k') := by rw [hbk']
          _ = (zK * b) * k' := by group
          _ = (b * zK) * k' := by rw [hbzK]
          _ = b * (zK * k') := by group
    have hcardx : Nat.card (CFSG.conjugate (N.CS E₁) N.x) = Nat.card (N.CS E₁) :=
      card_conjugate _ _
    have hcards : Nat.card (CFSG.conjugate (N.CS E₁) s) = Nat.card (N.CS E₁) :=
      card_conjugate _ _
    have hQeq : CFSG.conjugate (N.CS E₁) N.x = CFSG.conjugate (N.CS E₁) s := by
      have h1 : CFSG.conjugate (N.CS E₁) N.x = N.CS E' :=
        Subgroup.eq_of_le_of_card_ge hQx (by rw [← hQs, hcards, hcardx])
      rw [h1, hQs]
    have hnorm := mem_normalizer_of_conjugate_eq hQeq
    have hxS : N.x * s⁻¹ ∈ N.S :=
      cp_contra hs.setting.sylow.isPGroup inf_le_left N.S_le_T
        (D.sylow_CS h hK0 hKH hΦzK hE₁K hE₁4 hstar₁)
        (T.mul_mem N.x_mem.1 (T.inv_mem (N.S_le_T hsS))) hnorm
    apply N.x_not_mem
    have := N.S.mul_mem hxS hsS
    simpa using this

end CFSG.QuasithinUnique

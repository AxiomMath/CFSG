module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4f
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4d

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable (s : Setting X)

theorem sylow_eq_Dbar {g : X} (hg : g ∈ normalizer (s.h.S : Set X))
    (T : Sylow 2 (Jbar s.h)) (hT : innOf (T : Subgroup (Jbar s.h)) ≤
      rhoImg s.h.J (conjugate s.h.P g)) : (T : Subgroup (Jbar s.h)) = Dbar s.h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := s.exists_sylow_Dbar
  have hinj := conj_injective_of_center_eq_bot s.hZJ
  have hS2 : IsPGroup 2 (rhoImg s.h.J s.h.S) :=
    (s.h.isPGroup_S.of_equiv (subgroupOfEquivOfLe s.h.S_le_normalizer).symm).map _
  have hDS : innOf (Dbar s.h) ≤ rhoImg s.h.J s.h.S := by
    rw [← rhoImg_eq_innOf s.h.D_le_J]
    exact map_mono (fun w hw => s.h.D_le_S hw)
  have hTS : innOf (T : Subgroup (Jbar s.h)) ≤ rhoImg s.h.J s.h.S :=
    hT.trans (map_mono fun w hw => s.conjugate_P_le_S hg hw)
  have hsup2 : IsPGroup 2 ↥((T : Subgroup (Jbar s.h)) ⊔ Dbar s.h) := by
    have h1 : ((T : Subgroup (Jbar s.h)) ⊔ Dbar s.h).map
        (MulAut.conj : Jbar s.h →* MulAut (Jbar s.h)) ≤ rhoImg s.h.J s.h.S := by
      rw [Subgroup.map_sup]
      exact sup_le hTS hDS
    have h3 := (hS2.to_le h1).comap_of_injective _ hinj
    rwa [comap_map_eq_self_of_injective hinj] at h3
  have hle : (T₀ : Subgroup (Jbar s.h)) ≤ (T : Subgroup (Jbar s.h)) ⊔ Dbar s.h :=
    hT₀ ▸ le_sup_right
  have h4 := T₀.is_maximal' hsup2 hle
  have h5 : (T₀ : Subgroup (Jbar s.h)) = T := T.is_maximal' T₀.isPGroup' (h4 ▸ le_sup_left)
  rw [← h5, hT₀]

theorem exists_ctx4 (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C) (hRank : CFL2Rank)
    (hSyl : CFL2Sylow) (hJ : CFL2J)
    (hNS : ¬ normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) :
    ∃ c : Ctx4 X, c.s = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨u, hSw⟩ := s.exists_u hConj hComp hOut hCent hD hA hC hNS
  have hza : d.z ≠ s.h.a := fun h => d.z_not_mem_P (h ▸ s.h.a_mem_P)
  have hga : u⁻¹ * s.h.a * u ≠ s.h.a := by
    rw [hSw.hua]
    exact hza
  obtain ⟨hB2, h8, T, hTinn, hTe⟩ := s.cfl2A_apply hConj hComp hOut hCent hD hA hSw.hu hga
  have hTD := s.sylow_eq_Dbar hSw.hu T hTinn
  obtain ⟨⟨b, hbB0⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp s.hB0
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hB0 : ∀ c ∈ B0 s.h s.y, c = 1 ∨ c = b := fun c hc =>
    eq_one_or_of_card_two hB2 hbB0 hc hb1'
  have hbb : b * b = 1 := by
    rcases hB0 (b * b) (mul_mem hbB0 hbB0) with h | h
    · exact h
    · exfalso
      apply hb1'
      calc b = b * b * b⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
  have hba : b ≠ s.h.a := by
    intro h
    have h1 : s.h.a ∈ s.h.B ⊓ zpowers s.h.a := mem_inf.mpr ⟨h ▸ s.B0_le_B hbB0, mem_zpowers _⟩
    rw [show s.h.B ⊓ zpowers s.h.a = ⊥ from d.B_inf_zpowers_a, mem_bot] at h1
    exact d.a_ne_one h1
  obtain ⟨c0, hc0, hcc, hacL⟩ := s.exists_c hConj hComp hOut hCent
  obtain ⟨r, hrL, -, hr⟩ := d.hconj c0 hc0 hcc hacL
  have hrb : r * b = b * r := ((mem_centralizer_iff.mp (s.L_le_centralizer hrL)) b hbB0).symm
  have hrb' : r⁻¹ * b * r = b := by rw [mul_assoc, ← hrb, inv_mul_cancel_left]
  have hrab : r⁻¹ * (s.h.a * b) * r = d.z ∨ r⁻¹ * (s.h.a * b) * r = d.z * b := by
    rcases hB0 c0 hc0 with rfl | rfl
    · right
      have hr' : r⁻¹ * s.h.a * r = d.z := by
        have := hr
        rw [mul_one] at this
        exact this
      calc r⁻¹ * (s.h.a * b) * r = (r⁻¹ * s.h.a * r) * (r⁻¹ * b * r) := by group
        _ = d.z * b := by rw [hr', hrb']
    · exact Or.inl hr
  obtain ⟨T₀, hT₀⟩ := s.exists_sylow_Dbar
  have hT₀8 : 8 ≤ Nat.card T₀ := h8 T₀
  obtain ⟨hZ2, hsq, hprod⟩ := hSyl _ s.p s.f s.hp s.hp2 s.hf s.hJLie T₀ hT₀8
  rw [hT₀] at hZ2 hsq hprod
  have hC4 := hC _ s.p s.f s.hp s.hp2 s.hf s.hJLie T₀ hT₀8
  rw [hT₀] at hC4
  have hJ8 := hJ _ s.p s.f s.hp s.hp2 s.hf s.hJLie T₀ hT₀8
  rw [hT₀] at hJ8
  have hRk := hRank _ s.p s.f s.hp s.hp2 s.hf s.hJLie
  set zbar : Jbar s.h := ((⟨d.z, s.h.D_le_J d.hzD⟩ : ↥s.h.J) : Jbar s.h) with hzbar
  have hrz : rhoE s.h.J d.z = MulAut.conj zbar := rhoE_of_mem_J _
  have hzbarZ : zbar ∈ Dbar s.h ⊓ centralizer (Dbar s.h : Set (Jbar s.h)) := by
    refine mem_inf.mpr ⟨mem_map_of_mem _ (mem_subgroupOf.mpr d.hzD), ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨t, htJ⟩, ht, rfl⟩
    change QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J) ⟨t, htJ⟩ *
        QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J) ⟨d.z, s.h.D_le_J d.hzD⟩ =
      QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J) ⟨d.z, s.h.D_le_J d.hzD⟩ *
        QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J) ⟨t, htJ⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.hzS t (s.h.D_le_S (mem_subgroupOf.mp ht)))
  have hzbar1 : zbar ≠ 1 := by
    intro h
    apply d.z_not_mem_P
    have h1 : rhoE s.h.J d.z = 1 := by rw [hrz, h, map_one]
    rw [rhoE_eq_one_iff (s.h.S_le_normalizer d.z_mem_S)] at h1
    exact mem_inf.mpr ⟨d.z_mem_S, h1⟩
  have hZD : ∀ t ∈ Dbar s.h, t ∈ centralizer (Dbar s.h : Set (Jbar s.h)) →
      MulAut.conj t = 1 ∨ MulAut.conj t = rhoE s.h.J d.z := by
    intro t ht htC
    rcases eq_one_or_of_card_two hZ2 hzbarZ (mem_inf.mpr ⟨ht, htC⟩) hzbar1 with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, hrz]
  have hB0u : conjugate (B0 s.h s.y) u ≤ normalizer (s.h.J : Set X) :=
    (map_mono (s.B0_le_B.trans s.h.B_le_P)).trans (s.conjugate_P_le_normalizer hSw.hu)
  have hbu : u⁻¹ * b * u ∈ conjugate (B0 s.h s.y) u := by
    rw [mem_conjugate_iff, show u * (u⁻¹ * b * u) * u⁻¹ = b by group]
    exact hbB0
  have he : ∀ σ ∈ innOf (Dbar s.h),
      σ * rhoE s.h.J (u⁻¹ * b * u) = rhoE s.h.J (u⁻¹ * b * u) * σ := by
    intro σ hσ
    have h1 := hTe (rhoE_mem_rhoImg hB0u hbu)
    rw [mem_centralizer_iff] at h1
    exact h1 σ (hTD ▸ hσ)
  refine ⟨
    { s := s
      z := d.z
      u := u
      b := b
      r := r
      hzD := d.hzD
      hzS := d.hzS
      hzz := d.z_mul_z
      hz1 := d.z_ne_one
      hzP := d.z_not_mem_P
      hu := hSw.hu
      hua := hSw.hua
      huz := hSw.huz
      huu := hSw.huu
      hbB0 := hbB0
      hbb := hbb
      hb1 := hb1'
      hba := hba
      hnaz := s.not_conj_a_az hConj hComp hOut hCent hD hA hC
      hrb := hrb
      hrab := hrab
      hInn := hTD ▸ hTinn
      he := he
      hZD := hZD
      hsq := hsq
      hprod := hprod
      hC4 := hC4
      hJ8 := hJ8
      hRk := hRk }, rfl⟩

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB

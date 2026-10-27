module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6p_cent_B (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
        (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
          ∃ b ∈ B, (∃ α : ℤˣ, InducesTypeSome L (x * b⁻¹) 6 1 1 α) ∧
            ∀ n ∈ L ⊓ normalizer (B : Set G), (x * b⁻¹) * n = n * (x * b⁻¹) := by
  intro G _ _ L hL P hP B hB x hxN hx
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ := ff6p_exists_model_PB hL hP hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  have hBL : B ≤ L := hB.1.trans hP.1
  have hzB : ∀ w ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ w =
        ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
    have h := (ff6p_commute_img_iff hQ hdim hsgn hz e hxN hBL).mp hx
    rwa [hBφ] at h
  rcases ff6p_cent_sim_cases hQ h2 fr hzB with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩
  · rw [← hBφ] at hb
    obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb
    refine Or.inl ⟨(b₀ : G), hb₀B, ?_⟩
    have hbmN : x * (b₀ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem hxN (Subgroup.le_normalizer (L.inv_mem b₀.2))
    have hm : (⟨x * (b₀ : G)⁻¹, hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hxN⟩ * ⟨(b₀ : G), Subgroup.le_normalizer b₀.2⟩⁻¹ := Subtype.ext rfl
    have hθ : ffTheta6P hQ hdim hsgn e ⟨x * (b₀ : G)⁻¹, hbmN⟩ = 1 := by
      rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
      change ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * (ffOmegaToSim hQ b)⁻¹ = 1
      rw [hzb, mul_inv_cancel]
    exact (ff6p_theta_eq_one_iff hL hQ hdim hsgn e hbmN).mp hθ
  · rw [← hBφ] at hb
    obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb
    have hbmN : x * (b₀ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem hxN (Subgroup.le_normalizer (L.inv_mem b₀.2))
    have hm : (⟨x * (b₀ : G)⁻¹, hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hxN⟩ * ⟨(b₀ : G), Subgroup.le_normalizer b₀.2⟩⁻¹ := Subtype.ext rfl
    have hθ : ffTheta6P hQ hdim hsgn e ⟨x * (b₀ : G)⁻¹, hbmN⟩ = ffTs fr := by
      rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
      change ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * (ffOmegaToSim hQ b)⁻¹ = ffTs fr
      rw [hzb]
      group
    refine Or.inr ⟨(b₀ : G), hb₀B, ⟨-1, ?_⟩, ?_⟩
    · exact ff6p_induces_type hQ hdim hsgn e hbmN (by rw [hθ]; exact ffTs_hasType hQ fr)
    · refine (ff6p_commute_normalizer_iff hQ hdim hsgn hz e hbmN hBL).mpr ?_
      rw [hBφ]
      intro w hw
      rw [hθ]
      exact ffTs_comm_normalizer hQ h2 hπ fr hw

theorem ff6p_cent_B_opp (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B B' : Subgroup G, IsNormalE16In P B →
      IsNormalE16In P B' → B ≠ B' → ∀ z : G, z ∈ centerIn P → IsI4PlusIn L z →
        ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
          (∀ n ∈ L ⊓ normalizer (B : Set G), x * n = n * x) →
          (∃ α : ℤˣ, InducesTypeSome L x 6 1 1 α) →
            (∀ n ∈ L ⊓ normalizer (B' : Set G), (x * z) * n = n * (x * z)) ∧
              ∃ α : ℤˣ, TypesInModel L 6 1 1 α 1 (-α) x (x * z) := by
  intro G _ _ L hL P hP B B' hB hB' hBne zz hzP hzI x hxN hxB hxnorm hxType
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ := ff6p_exists_model_PB hL hP hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hzcl : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  have hBL : B ≤ L := hB.1.trans hP.1
  have hB'L : B' ≤ L := hB'.1.trans hP.1
  have hcover : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6p_odd_center hL)
  have hz0norm : ∀ w ∈ Subgroup.normalizer (ffB1p hQ fr : Set ↥(omegaProj hQ)),
      ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ w =
        ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
    have h := (ff6p_commute_normalizer_iff hQ hdim hsgn hzcl e hxN hBL).mp hxnorm
    rwa [hBφ] at h
  have hz0 : ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ = ffTs fr := by
    rcases ff6p_cent_normalizer hQ h2 hπ fr hz0norm with h1 | h1
    · exfalso
      obtain ⟨α, hα⟩ := hxType
      exact ff6p_not_centralizer_of_type hzcl hα
        ((ff6p_theta_eq_one_iff hL hQ hdim hsgn e hxN).mp h1)
    · exact h1
  unfold centerIn at hzP
  obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hzP
  have hzPmem : zz ∈ P := haz ▸ a.2
  have hzL : zz ∈ L := hP.1 hzPmem
  have hz2 : orderOf zz = 2 := hzI.1
  have hzcen : ∀ p ∈ P, zz * p = p * zz := by
    intro p hp
    have h := (Subgroup.mem_center_iff.mp ha) (⟨p, hp⟩ : ↥P)
    have h' : p * (a : G) = (a : G) * p := congrArg Subtype.val h
    rw [show (a : G) = zz from haz] at h'
    exact h'.symm
  have hφl_mem : ff6mPhi e ⟨zz, hzL⟩ ∈ ffP1p hQ fr := by
    rw [← hPφ]
    exact mem_ffImg_iff.mpr ⟨⟨zz, hzL⟩, hzPmem, rfl⟩
  have hφl_cent : ∀ p ∈ ffP1p hQ fr, p * ff6mPhi e ⟨zz, hzL⟩ =
      ff6mPhi e ⟨zz, hzL⟩ * p := by
    intro p hp
    rw [← hPφ] at hp
    obtain ⟨p₀, hp₀P, hp₀φ⟩ := mem_ffImg_iff.mp hp
    have hcomm : p₀ * (⟨zz, hzL⟩ : ↥L) = (⟨zz, hzL⟩ : ↥L) * p₀ :=
      Subtype.ext ((hzcen (p₀ : G) hp₀P).symm)
    have h := congrArg (ff6mPhi e) hcomm
    simp only [map_mul] at h
    rw [← hp₀φ]
    exact h
  have hφz : ff6mPhi e ⟨zz, hzL⟩ = ffZ0s hQ fr := by
    rcases ffP1p_center hQ hπ fr hφl_mem hφl_cent with h1 | h1
    · exfalso
      have hl1 : (⟨zz, hzL⟩ : ↥L) = 1 :=
        ff_cover_eq_of_pGroup hcover hP.2.1 hzPmem P.one_mem (by rw [h1, map_one])
      have hzz1 : zz = 1 := congrArg Subtype.val hl1
      have h1o : orderOf (1 : G) = 1 := orderOf_one
      rw [hzz1] at hz2
      omega
    · exact h1
  have hθz : ffTheta6P hQ hdim hsgn e ⟨zz, Subgroup.le_normalizer hzL⟩ =
      ffOmegaToSim hQ (ffZ0s hQ fr) := by
    rw [show (⟨zz, Subgroup.le_normalizer hzL⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨((⟨zz, hzL⟩ : ↥L) : G), Subgroup.le_normalizer (⟨zz, hzL⟩ : ↥L).2⟩
        from Subtype.ext rfl]
    rw [ffTheta6P_of_mem, hφz]
  have hxzzN : x * zz ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem hxN (Subgroup.le_normalizer hzL)
  have hθxz : ffTheta6P hQ hdim hsgn e ⟨x * zz, hxzzN⟩ =
      ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr) := by
    rw [show (⟨x * zz, hxzzN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨x, hxN⟩ * ⟨zz, Subgroup.le_normalizer hzL⟩ from Subtype.ext rfl]
    rw [map_mul, hz0, hθz]
  have hIndx : InducesViaP L (Subgroup.center ↥L) hQ e x (ffTs fr) :=
    hz0 ▸ ffTheta6P_induces hQ hdim hsgn e ⟨x, hxN⟩
  have hIndxz : InducesViaP L (Subgroup.center ↥L) hQ e (x * zz)
      (ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr)) :=
    hθxz ▸ ffTheta6P_induces hQ hdim hsgn e ⟨x * zz, hxzzN⟩
  have hTypes : ∃ α : ℤˣ, TypesInModel L 6 1 1 α 1 (-α) x (x * zz) := by
    refine ⟨-1, V, inferInstance, inferInstance, inferInstance, Q, hQ, e, ffTs fr,
      ffTs fr * ffOmegaToSim hQ (ffZ0s hQ fr), hdim, hsgn, hIndx, ffTs_hasType hQ fr,
      hIndxz, ?_⟩
    simpa using ff6p_tsz0_hasType hQ fr
  have hxz_norm : ∀ n ∈ L ⊓ normalizer (B' : Set G), (x * zz) * n = n * (x * zz) := by
    obtain ⟨y0, hy0G, hy0⟩ := ff6p_exists_y0 hQ hdim hsgn h2 fr
    have hcase := ff6p_img_normalE16_cases hQ hdim hsgn h2 e (ff6p_odd_center hL) fr
      hP hPφ hB' hy0G hy0
    rcases hcase with hB'1 | hB'2
    · exfalso
      have heq : ffImg (ff6mPhi e) B' = ffImg (ff6mPhi e) B := hB'1.trans hBφ.symm
      exact hBne ((ff_cover_img_injective hcover hP.1 hP.2.1 hB'.1 hB.1 heq).symm)
    · refine (ff6p_commute_normalizer_iff hQ hdim hsgn hzcl e hxzzN hB'L).mpr ?_
      rw [hB'2]
      intro w hw
      rw [hθxz]
      exact ff6p_tsz0_comm_normalizer_B2 hQ hdim hsgn h2 fr hy0G hy0 hw
  exact ⟨hxz_norm, hTypes⟩

theorem ff6p_cent_B_index (hc : FF6PCls) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ x y : G, x ∈ normalizer (L : Set G) → y ∈ normalizer (L : Set G) →
        (∀ b ∈ B, x * b = b * x) → (∀ b ∈ B, y * b = b * y) →
        (∀ b ∈ B, x * b⁻¹ ∉ centralizer (L : Set G)) →
        (∀ b ∈ B, y * b⁻¹ ∉ centralizer (L : Set G)) →
          ∃ b ∈ B, x * y⁻¹ * b⁻¹ ∈ centralizer (L : Set G) := by
  intro G _ _ L hL P hP B hB x y hxN hyN hx hy hxn hyn
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hPφ, hBφ⟩ := ff6p_exists_model_PB hL hP hB
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hz : Subgroup.center ↥L = ⊥ := ff6p_center_bot hc hL
  have hBL : B ≤ L := hB.1.trans hP.1
  have hzxB : ∀ w ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * ffOmegaToSim hQ w =
        ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ := by
    have h := (ff6p_commute_img_iff hQ hdim hsgn hz e hxN hBL).mp hx
    rwa [hBφ] at h
  have hzyB : ∀ w ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩ * ffOmegaToSim hQ w =
        ffOmegaToSim hQ w * ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩ := by
    have h := (ff6p_commute_img_iff hQ hdim hsgn hz e hyN hBL).mp hy
    rwa [hBφ] at h
  have hxcase : ∃ b ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ = ffTs fr * ffOmegaToSim hQ b := by
    rcases ff6p_cent_sim_cases hQ h2 fr hzxB with h1 | h1
    · exfalso
      obtain ⟨b, hb, hzb⟩ := h1
      rw [← hBφ] at hb
      obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb
      have hbmN : x * (b₀ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        mul_mem hxN (Subgroup.le_normalizer (L.inv_mem b₀.2))
      have hm : (⟨x * (b₀ : G)⁻¹, hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨x, hxN⟩ * ⟨(b₀ : G), Subgroup.le_normalizer b₀.2⟩⁻¹ := Subtype.ext rfl
      have hθ : ffTheta6P hQ hdim hsgn e ⟨x * (b₀ : G)⁻¹, hbmN⟩ = 1 := by
        rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
        change ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ * (ffOmegaToSim hQ b)⁻¹ = 1
        rw [hzb, mul_inv_cancel]
      exact hxn (b₀ : G) hb₀B
        ((ff6p_theta_eq_one_iff hL hQ hdim hsgn e hbmN).mp hθ)
    · exact h1
  have hycase : ∃ b ∈ ffB1p hQ fr,
      ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩ = ffTs fr * ffOmegaToSim hQ b := by
    rcases ff6p_cent_sim_cases hQ h2 fr hzyB with h1 | h1
    · exfalso
      obtain ⟨b, hb, hzb⟩ := h1
      rw [← hBφ] at hb
      obtain ⟨b₀, hb₀B, hb₀φ⟩ := mem_ffImg_iff.mp hb
      have hbmN : y * (b₀ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        mul_mem hyN (Subgroup.le_normalizer (L.inv_mem b₀.2))
      have hm : (⟨y * (b₀ : G)⁻¹, hbmN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨y, hyN⟩ * ⟨(b₀ : G), Subgroup.le_normalizer b₀.2⟩⁻¹ := Subtype.ext rfl
      have hθ : ffTheta6P hQ hdim hsgn e ⟨y * (b₀ : G)⁻¹, hbmN⟩ = 1 := by
        rw [hm, map_mul, map_inv, ffTheta6P_of_mem, hb₀φ]
        change ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩ * (ffOmegaToSim hQ b)⁻¹ = 1
        rw [hzb, mul_inv_cancel]
      exact hyn (b₀ : G) hb₀B
        ((ff6p_theta_eq_one_iff hL hQ hdim hsgn e hbmN).mp hθ)
    · exact h1
  obtain ⟨b₁, hb₁, hzb₁⟩ := hxcase
  obtain ⟨b₂, hb₂, hzb₂⟩ := hycase
  have hc1 : ffTs fr * ffOmegaToSim hQ b₁ = ffOmegaToSim hQ b₁ * ffTs fr :=
    ffTs_comm_normalizer hQ h2 hπ fr (Subgroup.le_normalizer hb₁)
  have hc2 : ffTs fr * ffOmegaToSim hQ b₂ = ffOmegaToSim hQ b₂ * ffTs fr :=
    ffTs_comm_normalizer hQ h2 hπ fr (Subgroup.le_normalizer hb₂)
  have hzb₁' : ffTheta6P hQ hdim hsgn e ⟨x, hxN⟩ = ffOmegaToSim hQ b₁ * ffTs fr := by
    rw [hzb₁, hc1]
  have hzb₂' : ffTheta6P hQ hdim hsgn e ⟨y, hyN⟩ = ffOmegaToSim hQ b₂ * ffTs fr := by
    rw [hzb₂, hc2]
  have hb12 : b₁ * b₂⁻¹ ∈ ffB1p hQ fr :=
    (ffB1p hQ fr).mul_mem hb₁ ((ffB1p hQ fr).inv_mem hb₂)
  rw [← hBφ] at hb12
  obtain ⟨c₀, hc₀B, hc₀φ⟩ := mem_ffImg_iff.mp hb12
  refine ⟨(c₀ : G), hc₀B, ?_⟩
  have hmN : x * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem hxN ((Subgroup.normalizer (L : Set G)).inv_mem hyN)
  have hmcN : x * y⁻¹ * (c₀ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem hmN (Subgroup.le_normalizer (L.inv_mem c₀.2))
  have hm : (⟨x * y⁻¹ * (c₀ : G)⁻¹, hmcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      (⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹) * ⟨(c₀ : G), Subgroup.le_normalizer c₀.2⟩⁻¹ :=
    Subtype.ext rfl
  have hts_inv : (ffTs fr)⁻¹ = ffTs fr := inv_eq_of_mul_eq_one_left (ffTs_mul_self fr)
  have hprod : (ffOmegaToSim hQ b₁ * ffTs fr) * (ffOmegaToSim hQ b₂ * ffTs fr)⁻¹ =
      ffOmegaToSim hQ (b₁ * b₂⁻¹) := by
    rw [mul_inv_rev, hts_inv, map_mul, map_inv]
    calc (ffOmegaToSim hQ b₁ * ffTs fr) * (ffTs fr * (ffOmegaToSim hQ b₂)⁻¹)
        = ffOmegaToSim hQ b₁ * (ffTs fr * ffTs fr) * (ffOmegaToSim hQ b₂)⁻¹ := by group
      _ = ffOmegaToSim hQ b₁ * (ffOmegaToSim hQ b₂)⁻¹ := by rw [ffTs_mul_self fr, mul_one]
  have hθ : ffTheta6P hQ hdim hsgn e ⟨x * y⁻¹ * (c₀ : G)⁻¹, hmcN⟩ = 1 := by
    rw [hm]
    simp only [map_mul, map_inv]
    rw [hzb₁', hzb₂', ffTheta6P_of_mem, hc₀φ]
    rw [← hprod, mul_inv_cancel]
  exact (ff6p_theta_eq_one_iff hL hQ hdim hsgn e hmcN).mp hθ

end CFSG.OddStandard.SmallF3.Omega

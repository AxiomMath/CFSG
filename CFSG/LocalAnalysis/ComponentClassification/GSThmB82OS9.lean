module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem sylow_eq_Dbar_of_le_rhoImg {h : Hyp52 X} (hZJ : center (Jbar h) = ⊥)
    {T₀ : Sylow 2 (Jbar h)} (hT₀ : (T₀ : Subgroup (Jbar h)) = Dbar h) (T : Sylow 2 (Jbar h))
    (hT : innOf (T : Subgroup (Jbar h)) ≤ rhoImg h.J h.S) :
    (T : Subgroup (Jbar h)) = Dbar h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := conj_injective_of_center_eq_bot hZJ
  have hS2 : IsPGroup 2 (rhoImg h.J h.S) :=
    (h.isPGroup_S.of_equiv (subgroupOfEquivOfLe h.S_le_normalizer).symm).map _
  have hDS : innOf (Dbar h) ≤ rhoImg h.J h.S := by
    rw [← rhoImg_eq_innOf h.D_le_J]
    exact map_mono (fun w hw => h.D_le_S hw)
  have hsup2 : IsPGroup 2 ↥((T : Subgroup (Jbar h)) ⊔ Dbar h) := by
    have h1 : ((T : Subgroup (Jbar h)) ⊔ Dbar h).map
        (MulAut.conj : Jbar h →* MulAut (Jbar h)) ≤ rhoImg h.J h.S := by
      rw [Subgroup.map_sup]
      exact sup_le hT hDS
    have h3 := (hS2.to_le h1).comap_of_injective _ hinj
    rwa [comap_map_eq_self_of_injective hinj] at h3
  have hle : (T₀ : Subgroup (Jbar h)) ≤ (T : Subgroup (Jbar h)) ⊔ Dbar h :=
    hT₀ ▸ le_sup_right
  have h4 := T₀.is_maximal' hsup2 hle
  have h5 : (T₀ : Subgroup (Jbar h)) = T := T.is_maximal' T₀.isPGroup' (h4 ▸ le_sup_left)
  rw [← h5, hT₀]

namespace Setting3

variable (s : Setting3 X)

theorem conj_mem_center_D {d : X} (hc : ∀ x ∈ s.Dt, x * d = d * x) :
    ∀ y ∈ s.h.D, s.t * d * s.t⁻¹ * y = y * (s.t * d * s.t⁻¹) := by
  intro y hy
  have hy' : s.t⁻¹ * y * s.t ∈ s.Dt := by
    rw [mem_conjugate_iff, show s.t * (s.t⁻¹ * y * s.t) * s.t⁻¹ = y by group]
    exact hy
  have h1 := hc _ hy'
  calc s.t * d * s.t⁻¹ * y = s.t * (d * (s.t⁻¹ * y * s.t)) * s.t⁻¹ := by group
    _ = s.t * ((s.t⁻¹ * y * s.t) * d) * s.t⁻¹ := by rw [h1]
    _ = y * (s.t * d * s.t⁻¹) := by group

theorem eq_one_or_of_mem_center_Dt (Z : ZData s.h) {d : X} (hd : d ∈ s.Dt)
    (hc : ∀ x ∈ s.Dt, x * d = d * x) : d = 1 ∨ d = s.t⁻¹ * Z.z * s.t := by
  have hd' : s.t * d * s.t⁻¹ ∈ s.h.D := mem_conjugate_iff.mp hd
  rcases Z.hZDz _ hd' (s.conj_mem_center_D hc) with h1 | h1
  · left
    calc d = s.t⁻¹ * (s.t * d * s.t⁻¹) * s.t := by group
      _ = 1 := by rw [h1]; group
  · right
    calc d = s.t⁻¹ * (s.t * d * s.t⁻¹) * s.t := by group
      _ = s.t⁻¹ * Z.z * s.t := by rw [h1]

theorem conj_z_mem_Ct (Z : ZData s.h) : s.t⁻¹ * Z.z * s.t ∈ s.Ct := by
  have hCt1 : s.Ct ≠ ⊥ := by
    intro hbot
    have h1 := s.a_mem_Dt
    rw [← s.map_Ct_eq, hbot, bot_subgroupOf, Subgroup.map_bot, mem_bot] at h1
    have h2 := s.sec.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal s.isPGroup_Dt inf_le_left
    (fun d hd c hc => mem_inf.mpr ⟨mul_mem (mul_mem hd (mem_inf.mp hc).1) (inv_mem hd),
      s.h.conj_mem_P (s.Dt_le_S hd) (mem_inf.mp hc).2⟩) hCt1
  rcases s.eq_one_or_of_mem_center_Dt Z (mem_inf.mp hw).1 hwZ with h1 | h1
  · exact absurd h1 hw1
  · exact h1 ▸ hw

theorem sup_B0_inf_conjugate_P (Z : ZData s.h) {u : X}
    (hu : u ∈ normalizer (s.h.S : Set X)) (hua : u⁻¹ * s.h.a * u ≠ s.h.a) :
    (s.Dt ⊔ s.h.secB0 s.y) ⊓ conjugate s.h.P u = ⊥ := by
  have hVS : s.Dt ⊔ s.h.secB0 s.y ≤ s.h.S := sup_le s.Dt_le_S (s.B0_le_P.trans s.h.P_le_S)
  have hV2 : IsPGroup 2 ↥(s.Dt ⊔ s.h.secB0 s.y) := s.h.isPGroup_S.to_le hVS
  by_contra hne
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal hV2 inf_le_left
    (fun v hv x hx => by
      refine mem_inf.mpr ⟨mul_mem (mul_mem hv (mem_inf.mp hx).1) (inv_mem hv), ?_⟩
      have hx' : u * x * u⁻¹ ∈ s.h.P := mem_conjugate_iff.mp (mem_inf.mp hx).2
      have hvu : u * v * u⁻¹ ∈ s.h.S := (mem_normalizer_iff.mp hu v).mp (hVS hv)
      rw [mem_conjugate_iff, show u * (v * x * v⁻¹) * u⁻¹ =
        (u * v * u⁻¹) * (u * x * u⁻¹) * (u * v * u⁻¹)⁻¹ by group]
      exact s.h.conj_mem_P hvu hx') hne
  obtain ⟨hwV, hwP'⟩ := mem_inf.mp hw
  obtain ⟨d, hd, b', hb', rfl⟩ := exists_mul_of_mem_sup (fun x hx y hy => s.Dt_comm_B0 hx hy) hwV
  have hdc : ∀ x ∈ s.Dt, x * d = d * x := by
    intro x hx
    have h1 := hwZ x (mem_sup_left hx)
    have h2 := s.Dt_comm_B0 hx hb'
    apply mul_right_cancel (b := b')
    calc x * d * b' = x * (d * b') := by group
      _ = d * b' * x := h1
      _ = d * (b' * x) := by group
      _ = d * (x * b') := by rw [h2]
      _ = d * x * b' := by group
  have hdP : d ∈ s.h.P := by
    rcases s.eq_one_or_of_mem_center_Dt Z hd hdc with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact (mem_inf.mp (s.conj_z_mem_Ct Z)).2
  have hwP : d * b' ∈ s.h.P := mul_mem hdP (s.B0_le_P hb')
  have h3 := P_inf_conjugate_eq_bot' s.C_eq hu hua ▸ mem_inf.mpr ⟨hwP, hwP'⟩
  exact hw1 (mem_bot.mp h3)

theorem conjugate_sup_B0_inf_kernel (Z : ZData s.h) {u : X}
    (hu : u ∈ normalizer (s.h.S : Set X)) (hua : u⁻¹ * s.h.a * u ≠ s.h.a)
    (huu : u * u ∈ s.h.S) :
    conjugate (s.Dt ⊔ s.h.secB0 s.y) u ⊓ coreActionKernel s.h.J = ⊥ := by
  have hVS : s.Dt ⊔ s.h.secB0 s.y ≤ s.h.S := sup_le s.Dt_le_S (s.B0_le_P.trans s.h.P_le_S)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxK⟩ := mem_inf.mp hx
  have hxS : x ∈ s.h.S := ((map_mono hVS).trans (conjugate_le_of_mem_normalizer' hu)) hxV
  have hxP : x ∈ s.h.P := mem_inf.mpr ⟨hxS, hxK⟩
  rw [mem_conjugate_iff] at hxV
  have h1 : u * x * u⁻¹ ∈ conjugate s.h.P u := by
    rw [mem_conjugate_iff, show u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u * u)⁻¹ by group]
    exact s.h.conj_mem_P huu hxP
  have h2 := s.sup_B0_inf_conjugate_P Z hu hua ▸ mem_inf.mpr ⟨hxV, h1⟩
  rw [mem_bot] at h2 ⊢
  calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
    _ = 1 := by rw [h2]; group

theorem conj_B0_comm_D (hA : CFL2A) (Z : ZData s.h) {u : X}
    (hu : u ∈ normalizer (s.h.S : Set X)) (hua : u⁻¹ * s.h.a * u ≠ s.h.a) (huu : u * u ∈ s.h.S)
    {b : X} (hb : b ∈ s.h.secB0 s.y) {d : X} (hd : d ∈ s.h.D) :
    u⁻¹ * b * u * d = d * (u⁻¹ * b * u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVS : s.Dt ⊔ s.h.secB0 s.y ≤ s.h.S := sup_le s.Dt_le_S (s.B0_le_P.trans s.h.P_le_S)
  set W := conjugate (s.Dt ⊔ s.h.secB0 s.y) u with hWdef
  have hWS : W ≤ s.h.S := (map_mono hVS).trans (conjugate_le_of_mem_normalizer' hu)
  have hWN : W ≤ normalizer (s.h.J : Set X) := hWS.trans s.h.S_le_normalizer
  have hW := s.conjugate_sup_B0_inf_kernel Z hu hua huu
  have hDtW : conjugate s.Dt u ≤ W := map_mono le_sup_left
  have hBW : conjugate (s.h.secB0 s.y) u ≤ W := map_mono le_sup_right
  set D₁ := rhoImg s.h.J (conjugate s.Dt u) with hD₁def
  set E := rhoImg s.h.J (conjugate (s.h.secB0 s.y) u) with hEdef
  have hR2 : IsPGroup 2 (rhoImg s.h.J s.h.S) :=
    (s.h.isPGroup_S.of_equiv (subgroupOfEquivOfLe s.h.S_le_normalizer).symm).map _
  have hD₁R : D₁ ≤ rhoImg s.h.J s.h.S := map_mono (fun w hw => hWS (hDtW hw))
  have hER : E ≤ rhoImg s.h.J s.h.S := map_mono (fun w hw => hWS (hBW hw))
  have hcomm : E ≤ centralizer (D₁ : Set (MulAut (Jbar s.h))) := by
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨c, hcN⟩, hc, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change c * e = e * c
    have he' := mem_subgroupOf.mp he
    have hc' := mem_subgroupOf.mp hc
    rw [mem_conjugate_iff] at he' hc'
    have h1 : (u * c * u⁻¹) * (u * e * u⁻¹) = (u * e * u⁻¹) * (u * c * u⁻¹) :=
      s.Dt_comm_B0 hc' he'
    calc c * e = u⁻¹ * ((u * c * u⁻¹) * (u * e * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * e * u⁻¹) * (u * c * u⁻¹)) * u := by rw [h1]
      _ = e * c := by group
  have hdisj : D₁ ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨⟨⟨c, hcN⟩, hc, rfl⟩, ⟨⟨e, heN⟩, he, he'⟩⟩
    have hce : (⟨e, heN⟩ : ↥(normalizer (s.h.J : Set X))) = ⟨c, hcN⟩ :=
      rho_injOn hW (show _ ∈ W.subgroupOf _ from hBW (mem_subgroupOf.mp he))
        (show _ ∈ W.subgroupOf _ from hDtW (mem_subgroupOf.mp hc)) he'
    have hec : e = c := congrArg Subtype.val hce
    have hc1 : c ∈ conjugate s.Dt u := mem_subgroupOf.mp hc
    have he1 : e ∈ conjugate (s.h.secB0 s.y) u := mem_subgroupOf.mp he
    rw [hec, mem_conjugate_iff] at he1
    rw [mem_conjugate_iff] at hc1
    have h0 : u * c * u⁻¹ = 1 := mem_bot.mp (s.Dt_inf_B0 ▸ mem_inf.mpr ⟨hc1, he1⟩)
    have hc0 : c = 1 := by
      calc c = u⁻¹ * (u * c * u⁻¹) * u := by group
        _ = 1 := by rw [h0]; group
    rw [mem_bot]
    change Eight.oddBarAction s.h.J ⟨c, hcN⟩ = 1
    rw [show (⟨c, hcN⟩ : ↥(normalizer (s.h.J : Set X))) = 1 from Subtype.ext hc0, map_one]
  have hne : E ≠ ⊥ := by
    intro hbot
    apply s.B0_ne_bot
    rw [eq_bot_iff]
    intro b' hb'
    have hb'u : u⁻¹ * b' * u ∈ conjugate (s.h.secB0 s.y) u := by
      rw [mem_conjugate_iff, show u * (u⁻¹ * b' * u) * u⁻¹ = b' by group]
      exact hb'
    have h1 : Eight.oddBarAction s.h.J ⟨u⁻¹ * b' * u, hWN (hBW hb'u)⟩ ∈ E :=
      mem_map_of_mem _ (mem_subgroupOf.mpr hb'u)
    rw [hbot, mem_bot] at h1
    have h2 := rho_injOn hW (show _ ∈ W.subgroupOf _ from hBW hb'u)
      (show (1 : ↥(normalizer (s.h.J : Set X))) ∈ W.subgroupOf _ from one_mem _)
      (by rw [h1, map_one])
    have h3 : u⁻¹ * b' * u = 1 := congrArg Subtype.val h2
    rw [mem_bot]
    calc b' = u * (u⁻¹ * b' * u) * u⁻¹ := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨T₀, hT₀⟩ := Z.sylow
  obtain ⟨p, f, hp, hp2, hf, hLie⟩ := Z.lie
  have hinj := conj_injective_of_center_eq_bot s.center_J
  have hDN : s.h.D ≤ normalizer (s.h.J : Set X) := s.h.D_le_S.trans s.h.S_le_normalizer
  have hDK : s.h.D ⊓ coreActionKernel s.h.J = ⊥ := by
    rw [eq_bot_iff, ← s.h.D_inf_P_eq_bot s.center_J]
    intro x hx
    exact mem_inf.mpr ⟨(mem_inf.mp hx).1,
      mem_inf.mpr ⟨s.h.D_le_S (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩⟩
  let e₁ : ↥D₁ ≃* ↥(T₀ : Subgroup (Jbar s.h)) :=
    (rhoEquiv hWN hW hDtW).symm.trans ((conjugateEquiv s.Dt u).symm.trans
      ((conjugateEquiv s.h.D s.t).symm.trans ((rhoEquiv hDN hDK le_rfl).trans
        ((MulEquiv.subgroupCongr (rhoImg_eq_innOf s.h.D_le_J)).trans
          (((Dbar s.h).equivMapOfInjective _ hinj).symm.trans
            (MulEquiv.subgroupCongr hT₀.symm))))))
  obtain ⟨hE2, -, T, hT⟩ := hA _ p f hp hp2 hf hLie (rhoImg s.h.J s.h.S) D₁ E hR2 hD₁R hER
    hcomm hdisj hne ⟨T₀, ⟨e₁⟩⟩
  have hTD := sylow_eq_Dbar_of_le_rhoImg s.center_J hT₀ T (hT.trans (sup_le hD₁R hER))
  have hcent : innOf (Dbar s.h) ≤ centralizer (E : Set (MulAut (Jbar s.h))) := by
    rw [← hTD]
    exact hT.trans (sup_le (le_centralizer_iff.mp hcomm) (le_centralizer_self_of_card_two hE2))
  have hbuB : u⁻¹ * b * u ∈ conjugate (s.h.secB0 s.y) u := by
    rw [mem_conjugate_iff, show u * (u⁻¹ * b * u) * u⁻¹ = b by group]
    exact hb
  have hbuN := hWN (hBW hbuB)
  have hdS := s.h.D_le_S hd
  have hdN := s.h.S_le_normalizer hdS
  have hρd : rhoE s.h.J d ∈ innOf (Dbar s.h) := by
    rw [← rhoImg_eq_innOf s.h.D_le_J]
    exact rhoE_mem_rhoImg hDN hd
  have hρ : rhoE s.h.J (u⁻¹ * b * u) * rhoE s.h.J d =
      rhoE s.h.J d * rhoE s.h.J (u⁻¹ * b * u) :=
    mem_centralizer_iff.mp (hcent hρd) _ (rhoE_mem_rhoImg (hBW.trans hWN) hbuB)
  have hbuP : u⁻¹ * b * u ∈ conjugate s.h.P u := by
    rw [mem_conjugate_iff, show u * (u⁻¹ * b * u) * u⁻¹ = b by group]
    exact s.B0_le_P hb
  have hdbu : d * (u⁻¹ * b * u) * d⁻¹ ∈ conjugate s.h.P u := by
    have hdu : u * d * u⁻¹ ∈ s.h.S := (mem_normalizer_iff.mp hu d).mp hdS
    rw [mem_conjugate_iff, show u * (d * (u⁻¹ * b * u) * d⁻¹) * u⁻¹ =
      (u * d * u⁻¹) * (u * (u⁻¹ * b * u) * u⁻¹) * (u * d * u⁻¹)⁻¹ by group]
    exact s.h.conj_mem_P hdu (mem_conjugate_iff.mp hbuP)
  have hx : d * (u⁻¹ * b * u) * d⁻¹ * (u⁻¹ * b * u)⁻¹ ∈
      conjugate s.h.P u ⊓ coreActionKernel s.h.J := by
    refine mem_inf.mpr ⟨mul_mem hdbu (inv_mem hbuP), ?_⟩
    rw [← rhoE_eq_one_iff (mul_mem (mul_mem (mul_mem hdN hbuN) (inv_mem hdN)) (inv_mem hbuN)),
      rhoE_mul (mul_mem (mul_mem hdN hbuN) (inv_mem hdN)) (inv_mem hbuN),
      rhoE_mul (mul_mem hdN hbuN) (inv_mem hdN), rhoE_mul hdN hbuN, rhoE_inv hdN,
      rhoE_inv hbuN, ← hρ]
    group
  rw [conjugate_P_inf_kernel' s.C_eq hu hua, mem_bot] at hx
  have h1 : d * (u⁻¹ * b * u) * d⁻¹ = u⁻¹ * b * u := mul_inv_eq_one.mp hx
  calc u⁻¹ * b * u * d = d * (u⁻¹ * b * u) * d⁻¹ * d := by rw [h1]
    _ = d * (u⁻¹ * b * u) := by group

end Setting3

theorem gs82OS9Input (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) (hA : CFL2A) :
    ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
      ¬ normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      Nat.card (s.h.secB0 s.y) = 2 →
      ∀ u ∈ normalizer (s.h.S : Set X), u * u ∈ s.h.S → u⁻¹ * s.h.a * u ∈ s.h.D →
        ∀ b ∈ s.h.secB0 s.y, ∀ d ∈ s.h.D, u⁻¹ * b * u * d = d * (u⁻¹ * b * u) := by
  intro X _ _ s _ _ u hu huu huaD b hb d hd
  obtain ⟨Z⟩ := exists_zData hSy hC hJ hRank hJo s.case8 s.center_J
  have hua : u⁻¹ * s.h.a * u ≠ s.h.a := by
    intro h
    have h1 : s.h.a ∈ s.h.D ⊓ s.h.P := mem_inf.mpr ⟨h ▸ huaD, s.h.a_mem_P⟩
    rw [s.h.D_inf_P_eq_bot s.center_J, mem_bot] at h1
    have h2 := s.h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact s.conj_B0_comm_D hA Z hu hua huu hb hd

end Eight2

end CFSG.ComponentClassification.GSThmB

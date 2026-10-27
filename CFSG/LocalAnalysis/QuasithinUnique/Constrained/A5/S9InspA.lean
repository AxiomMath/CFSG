module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspKit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Main

public section

namespace CFSG.QuasithinUnique.A5.Insp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519

section Basic

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

omit [Finite G] in
theorem ne_bot_of_isQuasisimple (hq : CFSG.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hx : x = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall K).mp h x x.2)
  have hy : y = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall K).mp h y y.2)
  rw [hx, hy]

theorem Tu_isPGroup (cfg : A5Cfg G T M H S L) : IsPGroup 2 ↥(T ⊓ centralizerElem u) :=
  cfg.cs.setting.isPGroup.to_le inf_le_left

omit [Finite G] in
theorem mem_Tu_of_commute (D : U9Data T M H S L z u A V) {g : G} (hg : g ∈ centralizerElem u)
    (hz : z * g = g * z) : g ∈ T ⊓ centralizerElem u := by
  have hgM : g ∈ M := D.mem_M_of_commute hz
  have : g ∈ M ⊓ centralizerElem u := ⟨hgM, hg⟩
  rw [← D.s7.Tu_eq] at this
  exact this

omit [Finite G] in
theorem mem_Tu_of_commute_uz (D : U9Data T M H S L z u A V) {g : G} (hg : g ∈ centralizerElem u)
    (hz : g * (u * z) = (u * z) * g) : g ∈ T ⊓ centralizerElem u := by
  have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  refine mem_Tu_of_commute D hg ?_
  have h1 : u * (g * z) = u * (z * g) := by
    calc u * (g * z) = (u * g) * z := by group
      _ = (g * u) * z := by rw [hgu]
      _ = g * (u * z) := by group
      _ = (u * z) * g := hz
      _ = u * (z * g) := by group
  exact (mul_left_cancel h1).symm

omit [Finite G] in
theorem uz_sq (D : U9Data T M H S L z u A V) : (u * z) * (u * z) = 1 := by
  have hc : u * z = z * u := D.uz_comm
  calc (u * z) * (u * z) = u * (z * u) * z := by group
    _ = u * (u * z) * z := by rw [← hc]
    _ = (u * u) * (z * z) := by group
    _ = 1 := by rw [D.u_sq', D.z_sq', one_mul]

end Basic

section Index

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

theorem relIndex_N_le_two (hP : Prop121Three) (cfg : A5Cfg G T M H S L)
    (D : U9Data T M H S L z u A V) (hK : IsComponentIn K (centralizerElem u)) :
    (centralizerElem u ⊓ Subgroup.normalizer (K : Set G)).relIndex (centralizerElem u) ≤ 2 := by
  have hs := cfg.cs.setting
  have huG : u ∈ centralizerElem u := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hpc : pCoreOf 2 (centralizerElem u) ≠ ⊥ :=
    pCore_ne_bot_of_central huG D.u_ne_one D.u_sq' le_rfl
  rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K (mem_cComp_of_isComponentIn hK) with
    hn | ⟨hcard, -⟩
  · have : centralizerElem u ⊓ Subgroup.normalizer (K : Set G) = centralizerElem u :=
      inf_eq_left.mpr hn
    rw [this, Subgroup.relIndex_eq_one.mpr le_rfl]
    norm_num
  · have h2 : (centralizerElem u ⊓ Subgroup.normalizer (K : Set G)).relIndex
        (centralizerElem u) = 2 := by
      rw [← card_conj_orbit_eq_relIndex]
      exact hcard
    exact h2.le

theorem A_le_of_relIndex (D : U9Data T M H S L z u A V) {N : Subgroup G}
    (hNG : N ≤ centralizerElem u) (hN2 : N.relIndex (centralizerElem u) ≤ 2) : A ≤ N := by
  obtain ⟨c, hcA, hc3, hcN, hcfp, hAc⟩ := D.hA.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcG : c ∈ centralizerElem u := (D.A_le_Hu hcA).2
  have hcN' : c ∈ N := mem_of_pow_three hNG hN2 hcG hc3'
  have hnorm : centralizerElem u ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_relIndex_le_two hNG hN2
  have hv₁V : u * z ∈ V := D.uz_mem
  have hv₁1 : u * z ≠ 1 := D.uz_ne_one
  have hv₁G : u * z ∈ centralizerElem u := (D.A_le_Hu (D.V_le_A hv₁V)).2
  have hwN : (u * z) * c * (u * z)⁻¹ * c⁻¹ ∈ N := by
    have h1 : (u * z) * c * (u * z)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hv₁G) c).mp hcN'
    exact N.mul_mem h1 (N.inv_mem hcN')
  have hwV : (u * z) * c * (u * z)⁻¹ * c⁻¹ ∈ V := by
    have h1 : c * (u * z)⁻¹ * c⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp (V.inv_mem hv₁V)
    have e : (u * z) * c * (u * z)⁻¹ * c⁻¹ = (u * z) * (c * (u * z)⁻¹ * c⁻¹) := by group
    rw [e]
    exact V.mul_mem hv₁V h1
  have hw1 : (u * z) * c * (u * z)⁻¹ * c⁻¹ ≠ 1 := by
    intro h
    apply hcfp (u * z) hv₁V hv₁1
    have h2 : (u * z) * c = c * (u * z) := by
      calc (u * z) * c = ((u * z) * c * (u * z)⁻¹ * c⁻¹) * (c * (u * z)) := by group
        _ = c * (u * z) := by rw [h, one_mul]
    calc c * (u * z) * c⁻¹ = (u * z) * c * c⁻¹ := by rw [← h2]
      _ = u * z := by group
  have hVN : V ≤ N :=
    D.hA.le_of_mem (fun a ha => hnorm (D.A_le_Hu ha).2) hwN hwV hw1
  rw [hAc]
  exact sup_le hVN (Subgroup.zpowers_le.mpr hcN')

theorem A_inf_centralizer_eq_bot (D : U9Data T M H S L z u A V)
    (hK : IsComponentIn K (centralizerElem u)) (hcomm : ⁅K, Subgroup.zpowers z⁆ = K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  by_contra hne
  have hV := k32_le_of_normal_ne_bot D.hA inf_le_left (k32_le_normalizer_inf_centralizer hAK) hne
  have huzC : u * z ∈ Subgroup.centralizer (K : Set G) := (hV D.uz_mem).2
  have hKG : K ≤ centralizerElem u := hK.1
  have hzc : ∀ k ∈ K, z * k = k * z := by
    intro k hk
    have h1 : k * (u * z) = (u * z) * k := Subgroup.mem_centralizer_iff.mp huzC k hk
    have hku : k * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp (hKG hk)
    have h2 : u * (k * z) = u * (z * k) := by
      calc u * (k * z) = (u * k) * z := by group
        _ = (k * u) * z := by rw [hku]
        _ = k * (u * z) := by group
        _ = (u * z) * k := h1
        _ = u * (z * k) := by group
    exact (mul_left_cancel h2).symm
  have hKz : K ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left (show Commute z k from hzc k hk) n)).eq
  have hbot : ⁅K, Subgroup.zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKz
  rw [hcomm] at hbot
  exact ne_bot_of_isQuasisimple (BenderBranch.isQuasisimple_of_isComponentIn hK) hbot

theorem V_not_le_centerR (D : U9Data T M H S L z u A V) : ¬ V ≤ centerOf (baum S) := by
  intro hVc
  rw [D.s7.ZR_eq] at hVc
  have hcomm : Commute u z := D.uz_comm
  have hzC : z ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left hcomm n).eq
  have hnorm : Subgroup.zpowers z ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hzC).trans (Subgroup.centralizer_le_normalizer _)
  have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  have hu2 : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two u).trans D.u_sq') D.u_ne_one
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((pow_two z).trans D.z_sq') D.z_facts.1
  rw [hu2, hz2] at hmul
  have hpos' : 0 < Nat.card ↥(Subgroup.zpowers z ⊓ Subgroup.zpowers u) := Nat.card_pos
  have hW : Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers z) ≤ 4 := by
    rw [sup_comm]
    have h1 := Nat.le_mul_of_pos_right (Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u)) hpos'
    omega
  have hVcard : Nat.card V = 4 := D.hA.card_U
  have hVW : V = Subgroup.zpowers u ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hVc (by rw [hVcard]; exact hW)
  apply D.u_not_mem_V
  rw [hVW]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)

theorem relIndex_baum_Tu (D : U9Data T M H S L z u A V) (cfg : A5Cfg G T M H S L) :
    (baum S).relIndex (T ⊓ centralizerElem u) = 2 := by
  have hRS : baum S ≤ S := baum_le_S
  have hRG : baum S ≤ centralizerElem u := by
    rw [← D.s7.Su]
    exact inf_le_right
  have hRTu : baum S ≤ T ⊓ centralizerElem u := le_inf (hRS.trans cfg.cs.le_T) hRG
  have h1 := Subgroup.relIndex_mul_relIndex (baum S) S T hRS cfg.cs.le_T
  have h2 := Subgroup.relIndex_mul_relIndex (baum S) (T ⊓ centralizerElem u) T hRTu inf_le_left
  rw [D.s7.R_index, D.s7.index_two] at h1
  rw [D.s7.Tu_index] at h2
  omega

theorem eq_of_le_of_relIndex_le_two {Rn C R : Subgroup G} (h1 : Rn ≤ C) (h2 : C ≤ R)
    (h : Rn.relIndex R ≤ 2) (hne : C ≠ R) : Rn = C := by
  by_contra hne'
  have hmul := Subgroup.relIndex_mul_relIndex Rn C R h1 h2
  have hfin : ∀ {X Y : Subgroup G}, X.relIndex Y ≠ 0 := by
    intro X Y
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have ha : Rn.relIndex C ≠ 1 := fun h' => hne' (le_antisymm h1 (Subgroup.relIndex_eq_one.mp h'))
  have hb : C.relIndex R ≠ 1 := fun h' => hne (le_antisymm h2 (Subgroup.relIndex_eq_one.mp h'))
  have ha2 : 2 ≤ Rn.relIndex C := by
    have := hfin (X := Rn) (Y := C)
    omega
  have hb2 : 2 ≤ C.relIndex R := by
    have := hfin (X := C) (Y := R)
    omega
  have := Nat.mul_le_mul ha2 hb2
  omega

theorem not_forall_comm_Rn (D : U9Data T M H S L z u A V) (cfg : A5Cfg G T M H S L)
    {N : Subgroup G} (hNG : N ≤ centralizerElem u) (hN2 : N.relIndex (centralizerElem u) ≤ 2) :
    ¬ ∀ r ∈ baum S ⊓ N, ∀ v ∈ V, r * v = v * r := by
  intro h
  have hGuN : centralizerElem u ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_relIndex_le_two hNG hN2
  obtain ⟨x, hxT, hxS, hxG⟩ := D.s7.x_exists
  have hR := D.R_eq x hxT hxS
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    k32_le_normalizer_of_index_two cfg.cs.le_T D.s7.index_two
  have hxR : x ∈ Subgroup.normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (hTS hxT)
  have hxN : x ∈ Subgroup.normalizer (N : Set G) := hGuN hxG
  have hRG : baum S ≤ centralizerElem u := by
    rw [← D.s7.Su]
    exact inf_le_right
  have hconj : ∀ r ∈ baum S ⊓ N, x * r * x⁻¹ ∈ baum S ⊓ N := fun r hr =>
    ⟨(Subgroup.mem_normalizer_iff.mp hxR r).mp hr.1, (Subgroup.mem_normalizer_iff.mp hxN r).mp hr.2⟩
  have hconjR : ∀ r ∈ baum S, x⁻¹ * r * x ∈ baum S := by
    intro r hr
    have hxR' : x⁻¹ ∈ Subgroup.normalizer (baum S : Set G) :=
      (Subgroup.normalizer (baum S : Set G)).inv_mem hxR
    have := (Subgroup.mem_normalizer_iff.mp hxR' r).mp hr
    simpa using this
  obtain ⟨C1, hC1⟩ : ∃ C1 : Subgroup G, C1 = baum S ⊓ Subgroup.centralizer (V : Set G) := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2 : Subgroup G,
      C2 = baum S ⊓ Subgroup.centralizer (conjR V x : Set G) := ⟨_, rfl⟩
  have hmem1 : ∀ r, r ∈ C1 ↔ r ∈ baum S ∧ ∀ v ∈ V, v * r = r * v := by
    intro r
    rw [hC1, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hmem2 : ∀ r, r ∈ C2 ↔ r ∈ baum S ∧ ∀ w ∈ conjR V x, w * r = r * w := by
    intro r
    rw [hC2, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hC1R : C1 ≤ baum S := fun r hr => ((hmem1 r).mp hr).1
  have hC2R : C2 ≤ baum S := fun r hr => ((hmem2 r).mp hr).1
  have hRnC1 : baum S ⊓ N ≤ C1 := fun r hr =>
    (hmem1 r).mpr ⟨hr.1, fun v hv => (h r hr v hv).symm⟩
  have hRnC2 : baum S ⊓ N ≤ C2 := by
    intro r hr
    refine (hmem2 r).mpr ⟨hr.1, fun w hw => ?_⟩
    have hw' : x * w * x⁻¹ ∈ V := mem_conjR_iff.mp hw
    have hc := h _ (hconj r hr) _ hw'
    have : x * (r * w) * x⁻¹ = x * (w * r) * x⁻¹ := by
      calc x * (r * w) * x⁻¹ = (x * r * x⁻¹) * (x * w * x⁻¹) := by group
        _ = (x * w * x⁻¹) * (x * r * x⁻¹) := hc
        _ = x * (w * r) * x⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel this)).symm
  have hC1not : ¬ baum S ≤ C1 := by
    intro hle
    apply V_not_le_centerR D
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨D.U_le_R (D.V_le hy),
      Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact ((hmem1 r).mp (hle hr)).2 y hy |>.symm
  have hC2not : ¬ baum S ≤ C2 := by
    intro hle
    apply hC1not
    intro r hr
    refine (hmem1 r).mpr ⟨hr, fun v hv => ?_⟩
    have hw : x⁻¹ * v * x ∈ conjR V x := by
      rw [mem_conjR_iff]
      have e : x * (x⁻¹ * v * x) * x⁻¹ = v := by group
      rw [e]
      exact hv
    have hc := ((hmem2 _).mp (hle (hconjR r hr))).2 _ hw
    have : x⁻¹ * (v * r) * x = x⁻¹ * (r * v) * x := by
      calc x⁻¹ * (v * r) * x = (x⁻¹ * v * x) * (x⁻¹ * r * x) := by group
        _ = (x⁻¹ * r * x) * (x⁻¹ * v * x) := hc
        _ = x⁻¹ * (r * v) * x := by group
    exact mul_left_cancel (mul_right_cancel this)
  have hidx : (baum S ⊓ N).relIndex (baum S) ≤ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    have hne : N.relIndex (centralizerElem u) ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    exact (Subgroup.relIndex_le_of_le_right hRG hne).trans hN2
  have hE1 : baum S ⊓ N = C1 :=
    eq_of_le_of_relIndex_le_two hRnC1 hC1R hidx (fun h' => hC1not h'.ge)
  have hE2 : baum S ⊓ N = C2 :=
    eq_of_le_of_relIndex_le_two hRnC2 hC2R hidx (fun h' => hC2not h'.ge)
  have hU1 : blockU L ≤ C1 := fun a ha =>
    (hmem1 a).mpr ⟨D.U_le_R ha, fun v hv => D.U_comm v (D.V_le hv) a ha⟩
  have hU2 : conjR (blockU L) x ≤ C2 := by
    intro a ha
    refine (hmem2 a).mpr ⟨?_, fun w hw => ?_⟩
    · rw [hR]
      exact Subgroup.mem_sup_right ha
    · have ha' : x * a * x⁻¹ ∈ blockU L := mem_conjR_iff.mp ha
      have hw' : x * w * x⁻¹ ∈ blockU L := D.V_le (mem_conjR_iff.mp hw)
      have hc := D.U_comm _ hw' _ ha'
      have : x * (w * a) * x⁻¹ = x * (a * w) * x⁻¹ := by
        calc x * (w * a) * x⁻¹ = (x * w * x⁻¹) * (x * a * x⁻¹) := by group
          _ = (x * a * x⁻¹) * (x * w * x⁻¹) := hc
          _ = x * (a * w) * x⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel this)
  apply hC1not
  rw [hR]
  refine sup_le hU1 ?_
  intro a ha
  have := hU2 ha
  rw [← hE2, hE1] at this
  exact this

theorem baum_le_normalizer_A (D : U9Data T M H S L z u A V) (cfg : A5Cfg G T M H S L) :
    baum S ≤ Subgroup.normalizer (A : Set G) := by
  have hRG : baum S ≤ centralizerElem u := by
    rw [← D.s7.Su]
    exact inf_le_right
  have hRH : baum S ≤ H ⊓ centralizerElem u :=
    le_inf (baum_le_S.trans cfg.cs.sylow.1) hRG
  have hnorm : H ⊓ centralizerElem u ≤ Subgroup.normalizer (A : Set G) := by
    rw [D.A_eq, pResidualOf_eq_opResidual]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 _)).mp
      (opResidual_normal 2 _)
  exact hRH.trans hnorm

end Index

section Datum

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

theorem a5_datum (cfg : A5Cfg G T M H S L) (D : U9Data T M H S L z u A V)
    (hK : IsComponentIn K (centralizerElem u)) (hcomm : ⁅K, Subgroup.zpowers z⁆ = K)
    (hN2 : (centralizerElem u ⊓ Subgroup.normalizer (K : Set G)).relIndex (centralizerElem u) ≤ 2) :
    ∃ X P R A' V' : Subgroup (MulAut ↥K), K32Datum ↥K X P R A' V' := by
  classical
  set Gu : Subgroup G := centralizerElem u with hGu
  set N : Subgroup G := Gu ⊓ Subgroup.normalizer (K : Set G) with hNdef
  have hNG : N ≤ Gu := inf_le_left
  have hKN : N ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hGuN : Gu ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_relIndex_le_two hNG hN2
  have hKG : K ≤ Gu := hK.1
  have hKN' : K ≤ N := le_inf hKG Subgroup.le_normalizer
  have hAN : A ≤ N := A_le_of_relIndex D hNG hN2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAN.trans hKN
  have hCK : A ⊓ Subgroup.centralizer (K : Set G) = ⊥ := A_inf_centralizer_eq_bot D hK hcomm hAK
  have hVR : V ≤ baum S := D.V_le.trans D.U_le_R
  have hRG : baum S ≤ Gu := by
    rw [← D.s7.Su]
    exact inf_le_right
  have hRle : baum S ≤ T ⊓ Gu := le_inf (baum_le_S.trans cfg.cs.le_T) hRG
  have hRA : baum S ≤ Subgroup.normalizer (A : Set G) := baum_le_normalizer_A D cfg
  have hTn : IsSylowTwoOf ((T ⊓ Gu) ⊓ N) N := A4.isSylowTwoOf_inf_normal D.s7.Tu_sylow hNG hGuN
  set φ := k32ActHom K N hKN with hφ
  let f₀ : ↥A →* MulAut ↥K := φ.comp (Subgroup.inclusion hAN)
  have hf₀inj : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : (a : G) ∈ Subgroup.centralizer (K : Set G) :=
      (k32ActHom_eq_one_iff K N hKN (Subgroup.inclusion hAN a)).mp ha
    have hmem : (a : G) ∈ A ⊓ Subgroup.centralizer (K : Set G) := ⟨a.2, hc⟩
    rw [hCK] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hA' : IsA4Block f₀.range ((V.subgroupOf A).map f₀) := k32_isA4Block_range D.hA f₀ hf₀inj
  have key : ∀ ρ' : ↥N, (ρ' : G) ∈ baum S → ∀ a ∈ f₀.range, φ ρ' * a * (φ ρ')⁻¹ ∈ f₀.range := by
    intro ρ' hρ' a ha
    obtain ⟨l, rfl⟩ := ha
    have hl' : (ρ' : G) * l * (ρ' : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hRA hρ') l).mp l.2
    refine ⟨⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩, ?_⟩
    have e : (Subgroup.inclusion hAN ⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩ : ↥N) =
        ρ' * Subgroup.inclusion hAN l * ρ'⁻¹ := Subtype.ext rfl
    show φ (Subgroup.inclusion hAN ⟨(ρ' : G) * l * (ρ' : G)⁻¹, hl'⟩) =
      φ ρ' * φ (Subgroup.inclusion hAN l) * (φ ρ')⁻¹
    rw [e, map_mul, map_mul, map_inv]
  have keyV : ∀ ρ' : ↥N, (ρ' : G) ∈ baum S → ∀ a ∈ (V.subgroupOf A).map f₀,
      φ ρ' * a * (φ ρ')⁻¹ ∈ (V.subgroupOf A).map f₀ := by
    intro ρ' hρ' a ha
    obtain ⟨v, hv, rfl⟩ := ha
    have hv' : (v : G) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have hvl' : (ρ' : G) * v * (ρ' : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hRA hρ') v).mp v.2
    have hV' : (ρ' : G) * v * (ρ' : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (D.hA.mem_normalizer_U (hRA hρ')) v).mp hv'
    refine ⟨⟨(ρ' : G) * v * (ρ' : G)⁻¹, hvl'⟩, Subgroup.mem_subgroupOf.mpr hV', ?_⟩
    have e : (Subgroup.inclusion hAN ⟨(ρ' : G) * v * (ρ' : G)⁻¹, hvl'⟩ : ↥N) =
        ρ' * Subgroup.inclusion hAN v * ρ'⁻¹ := Subtype.ext rfl
    show φ (Subgroup.inclusion hAN ⟨(ρ' : G) * v * (ρ' : G)⁻¹, hvl'⟩) =
      φ ρ' * φ (Subgroup.inclusion hAN v) * (φ ρ')⁻¹
    rw [e, map_mul, map_mul, map_inv]
  refine ⟨φ.range, (((T ⊓ Gu) ⊓ N).subgroupOf N).map φ, ((baum S ⊓ N).subgroupOf N).map φ,
    f₀.range, (V.subgroupOf A).map f₀, ?_⟩
  refine ⟨?_, k32_isSylowTwoOf_map φ hTn, hA', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨(k : G), hKN' k.2⟩, k32ActHom_of_mem K N hKN _ k.2⟩
  ·
    rintro _ ⟨l, rfl⟩
    exact ⟨Subgroup.inclusion hAN l, rfl⟩
  ·
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨Subgroup.inclusion hAN v, Subgroup.mem_subgroupOf.mpr
      ⟨hVR (Subgroup.mem_subgroupOf.mp hv), hAN v.2⟩, rfl⟩
  ·
    exact Subgroup.map_mono fun a ha => Subgroup.mem_subgroupOf.mpr
      ⟨hRle (Subgroup.mem_subgroupOf.mp ha).1, (Subgroup.mem_subgroupOf.mp ha).2⟩
  ·
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρR : (ρ : G) ∈ baum S := (Subgroup.mem_subgroupOf.mp hρ).1
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact key ρ hρR a
    · intro h
      have h1 := key ρ⁻¹ (by simpa using (baum S).inv_mem hρR) _ h
      have e : (φ ρ⁻¹) * (φ ρ * a * (φ ρ)⁻¹) * (φ ρ⁻¹)⁻¹ = a := by
        rw [map_inv]; group
      rwa [e] at h1
  ·
    rintro _ ⟨ρ, hρ, rfl⟩
    have hρR : (ρ : G) ∈ baum S := (Subgroup.mem_subgroupOf.mp hρ).1
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact keyV ρ hρR a
    · intro h
      have h1 := keyV ρ⁻¹ (by simpa using (baum S).inv_mem hρR) _ h
      have e : (φ ρ⁻¹) * (φ ρ * a * (φ ρ)⁻¹) * (φ ρ⁻¹)⁻¹ = a := by
        rw [map_inv]; group
      rwa [e] at h1
  ·
    have hsub : (baum S ⊓ N).subgroupOf N ≤ ((T ⊓ Gu) ⊓ N).subgroupOf N := fun a ha =>
      Subgroup.mem_subgroupOf.mpr
        ⟨hRle (Subgroup.mem_subgroupOf.mp ha).1, (Subgroup.mem_subgroupOf.mp ha).2⟩
    have h1 := k32_relIndex_map_dvd φ hsub
    have h2 : ((baum S ⊓ N).subgroupOf N).relIndex (((T ⊓ Gu) ⊓ N).subgroupOf N) =
        (baum S ⊓ N).relIndex ((T ⊓ Gu) ⊓ N) := Subgroup.relIndex_subgroupOf inf_le_right
    rw [h2] at h1
    have h3 : (baum S ⊓ N).relIndex ((T ⊓ Gu) ⊓ N) ≤ 2 := by
      have e : baum S ⊓ ((T ⊓ Gu) ⊓ N) = baum S ⊓ N := by
        rw [← inf_assoc, inf_eq_left.mpr hRle]
      have h4 := Subgroup.inf_relIndex_right (baum S) ((T ⊓ Gu) ⊓ N)
      rw [e] at h4
      rw [h4]
      have hne : (baum S).relIndex (T ⊓ Gu) ≠ 0 := by
        unfold Subgroup.relIndex
        exact Subgroup.index_ne_zero_of_finite
      have := Subgroup.relIndex_le_of_le_right (H := baum S)
        (inf_le_left : (T ⊓ Gu) ⊓ N ≤ T ⊓ Gu) hne
      rw [relIndex_baum_Tu D cfg] at this
      exact this
    have hpos : 0 < (baum S ⊓ N).relIndex ((T ⊓ Gu) ⊓ N) := by
      apply Nat.pos_of_ne_zero
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos h1).trans h3
  ·
    intro hcon
    apply not_forall_comm_Rn D cfg hNG hN2
    intro r hr v hv
    let ρ' : ↥N := ⟨r, hr.2⟩
    let v' : ↥A := ⟨v, D.V_le_A hv⟩
    have hρ'R : φ ρ' ∈ ((baum S ⊓ N).subgroupOf N).map φ :=
      ⟨ρ', Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    have hv'V : f₀ v' ∈ (V.subgroupOf A).map f₀ := ⟨v', Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    have hcomm' : f₀ v' * φ ρ' = φ ρ' * f₀ v' :=
      Subgroup.mem_centralizer_iff.mp (hcon hρ'R) (f₀ v') hv'V
    have hl' : r * v * r⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hRA hr.1) v).mp (D.V_le_A hv)
    have hconj : f₀ ⟨r * v * r⁻¹, hl'⟩ = f₀ v' := by
      have e : (Subgroup.inclusion hAN ⟨r * v * r⁻¹, hl'⟩ : ↥N) =
          ρ' * Subgroup.inclusion hAN v' * ρ'⁻¹ := Subtype.ext rfl
      show φ (Subgroup.inclusion hAN ⟨r * v * r⁻¹, hl'⟩) = φ (Subgroup.inclusion hAN v')
      rw [e, map_mul, map_mul, map_inv]
      have hcomm'' : φ (Subgroup.inclusion hAN v') * φ ρ' = φ ρ' * φ (Subgroup.inclusion hAN v') :=
        hcomm'
      calc φ ρ' * φ (Subgroup.inclusion hAN v') * (φ ρ')⁻¹
          = (φ (Subgroup.inclusion hAN v') * φ ρ') * (φ ρ')⁻¹ := by rw [hcomm'']
        _ = φ (Subgroup.inclusion hAN v') := by group
    have hrv : r * v * r⁻¹ = v := congrArg Subtype.val (hf₀inj hconj)
    calc r * v = (r * v * r⁻¹) * r := by group
      _ = v * r := by rw [hrv]

end Datum

end CFSG.QuasithinUnique.A5.Insp
